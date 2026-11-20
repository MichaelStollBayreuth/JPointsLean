/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.SolveByElim

import Std.WP

/-!
# The simplification and the dispatch of the verification conditions

The contracts of the components with a loop are proved by `vcgen`, whose verification conditions
encode the weakest preconditions in the order of `Prop`: meets, propositions of the order, the
measures that end the loops and the applied invariants of the `while` loops. The tactic `vc_simp`
rewrites these encodings into plain propositions in all the hypotheses and the goal, with further
lemmas of each contract (the invariants to unfold and propositional clean-up), before the dispatch
of the conditions.

`vcgen` splits a postcondition, and a precondition that it passes on to a call, at its
conjunctions, one verification condition per leaf. The tactic `vc_leaf t` closes such a condition
by the component of the term `t` that matches it, so that one lemma in the shape of the whole
condition serves all its leaves.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts that use the tactics do.

## References

The tactic `vc_simp` is adapted from `Ratpoints/Proof/VCSimp.lean` of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

public meta section

open Lean.Parser.Tactic in
/-- `vc_simp [l₁, …]` rewrites, in all the hypotheses and the goal, the encodings of the weakest
preconditions that the verification conditions of `vcgen` contain into plain propositions: meets and
propositions of the order (`Lean.Order.meet_prop_eq_and`,
`Lean.Order.CompleteLattice.ofProp_prop_eq`), the measures that end the loops
(`Std.WP.Variant.evalsTo_ofMeasure`, `Std.WP.Variant.evalsBelow_ofMeasure_nat`,
`Std.WP.Assertion.NondetFun.evalsTo_pure`) and the applied invariants of `while` loops
(`Std.WP.WhileInvariant.mk_apply`), with the further simp lemmas `l₁, …`. It is
`simp only [these lemmas, l₁, …] at *`. -/
syntax (name := vcSimp) "vc_simp" (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? :
  tactic

macro_rules
  | `(tactic| vc_simp $[[$args,*]]?) => do
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Variant.evalsBelow_ofMeasure_nat,
      Std.WP.Assertion.NondetFun.evalsTo_pure, Lean.Order.meet_prop_eq_and,
      Lean.Order.CompleteLattice.ofProp_prop_eq, Std.WP.WhileInvariant.mk_apply, $args,*] at *)

open Lean Meta in
/-- The components of the proof `e` of a conjunction, recursively, also under universal statements
and implications: `And.left e` and `And.right e` split further while their types are conjunctions,
and for `e : ∀ x, A x ∧ B x` the components are those of `fun x ↦ (e x).1` and `fun x ↦ (e x).2`. -/
private partial def andLeaves (e : Expr) : MetaM (List Expr) := do
  withReducible <| forallTelescopeReducing (← instantiateMVars (← inferType e)) fun xs ty ↦ do
    unless (← whnfR ty).isAppOfArity ``And 2 do return [e]
    let ex := mkAppN e xs
    let ls := (← andLeaves (← mkAppM ``And.left #[ex])) ++
      (← andLeaves (← mkAppM ``And.right #[ex]))
    ls.mapM (mkLambdaFVars xs)

/-- `vc_leaf t` closes a verification condition of `vcgen` that is a leaf of the proposition that
the term `t` proves. `vcgen` splits a postcondition, and a precondition that it passes on to a
call, at its conjunctions and introduces the variables and the premises of its universal
statements, one verification condition per leaf, so that a lemma in the shape of the whole
condition matches none of them. The tactic tries the components of `t` (`And.left` and
`And.right`, recursively, also under universal statements and implications) in turn: it applies the
component to the goal, which fixes the arguments that the goal determines, then elaborates the
instances and the tactic blocks of `t`, and closes the premises of the component and the
propositional holes `_` of `t` together by `solve_by_elim*` from the hypotheses, which backtracks
over their choice (with a depth of six steps beyond one per goal, at the transparency of the
context, as `assumption` does), or, if that fails, closes the holes first; last it tries `t`
itself, for a condition that `vcgen` does not split. It fails if no component closes the goal.
`vc_leaf t using l₁, …` passes the further lemmas `l₁, …` to `solve_by_elim*`. -/
syntax (name := vcLeaf) "vc_leaf " term (" using " term,+)? : tactic

open Lean Meta Elab Tactic Lean.Parser.Tactic.SolveByElim in
elab_rules : tactic
  | `(tactic| vc_leaf $t $[using $ls,*]?) => withMainContext do
    let ls := #[← `(arg| *)] ++
      (← (ls.map (·.getElems) |>.getD #[]).mapM fun l ↦ `(arg| $l:term))
    let goal ← getMainGoal
    let rest := (← getGoals).tail
    let s ← saveState
    -- the instances and the tactic blocks of `t` wait until the component is applied
    let elab_ : TacticM (Expr × List MVarId) := do
      let (e, holes) ← withCollectingNewGoalsFrom (elabTerm t none (mayPostpone := true))
        (← getMainTag) `vc_leaf (allowNaturalHoles := true)
      return (e, ← holes.filterM fun g ↦ return (← Term.getSyntheticMVarDecl? g).isNone)
    let mut msgs := m!""
    let close (gs : List MVarId) : TacticM Unit := do
      let gs ← gs.filterM fun g ↦ return !(← g.isAssigned) && (← isProp (← g.getType))
      unless gs.isEmpty do
        setGoals gs
        let depth := Syntax.mkNumLit (toString (gs.length + 6))
        let tr ← match ← getTransparency with
          | .reducible => `(term| .reducible)
          | .instances => `(term| .instances)
          | _ => `(term| .default)
        evalTactic (← `(tactic| solve_by_elim* (maxDepth := $depth) (transparency := $tr)
          (symm := false) (exfalso := false) only [$ls,*]))
    -- the holes can fix a predicate whose values are conjunctions, with further components;
    -- the whole term comes last, for a condition that `vcgen` does not split
    let leaves (holesFirst : Bool) : TacticM (List Expr × List MVarId) := do
      let (e, holes) ← elab_
      if holesFirst then close holes
      let cs ← andLeaves e
      return (if cs.length > 1 then cs ++ [e] else cs, holes)
    let n ← [false, true].foldlM (init := 0) fun n holesFirst ↦ do
      let m ← (return (← leaves holesFirst).1.length) <|> pure 0
      s.restore
      return max n m
    for i in [:n] do
      for holesFirst in [false, true] do
        try
          let (cs, holes) ← leaves holesFirst
          let some leaf := cs[i]? | throwError "there are only {cs.length} components"
          -- the holes `_` of `t` are synthetic opaque, but the goal may fix them
          let gs ← withAssignableSyntheticOpaque <| goal.apply leaf
          Term.synthesizeSyntheticMVarsNoPostponing
          close (gs ++ holes)
          if (← instantiateMVars (mkMVar goal)).hasExprMVar then
            throwError "the proof has metavariables"
          setGoals rest
          return
        catch ex =>
          msgs := msgs ++ m!"\ncomponent {i}{if holesFirst then " (holes first)" else ""}: \
            {ex.toMessageData}"
          s.restore
    throwError m!"vc_leaf: no component of the term closes the goal{msgs}"

end
