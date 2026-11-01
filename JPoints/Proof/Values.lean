/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Program
public import Std.WP

/-!
# The values of the components without a contract

A composition proved by `vcgen` needs a contract of every component that it calls. A component
whose output the composition passes on without reasoning about it, such as the text of a message,
has the contract that it returns its value (`Std.WP.Id.triple_eq_run`): the messages
(`JPoints.message_spec`), the messages of the refusals of the command line
(`JPoints.Cli.Failure.message_spec`), the integers of the coefficients
(`JPoints.Cli.scanMpz_spec`), the index of a constant of the cost model by its name
(`JPoints.Cli.costIndex_spec`), the format of `-f` (`JPoints.Cli.unescape_spec`), the constants of
the cost model under `-c list` (`JPoints.Program.mainCostList_spec`), the head of the report
(`JPoints.Program.mainHead_spec`) and the text of a point on GMP integers
(`JPoints.Printf.printfMpz_spec`).

## Main statements

* `Std.WP.Id.triple_eq_run`: a program in `Id` returns its value.
* `Std.WP.Id.triple_of_run`: a contract of a program in `Id` from its value.
* `JPoints.message_spec`, `JPoints.Cli.Failure.message_spec`, `JPoints.Cli.scanMpz_spec`,
  `JPoints.Cli.costIndex_spec`, `JPoints.Cli.unescape_spec`, `JPoints.Program.mainCostList_spec`,
  `JPoints.Program.mainHead_spec`, `JPoints.Printf.printfMpz_spec`: the components that return
  their values.

## Implementation notes

`Std.WP.Id.triple_eq_run` and `Std.WP.Id.triple_of_run` are candidates for `Std.WP`, next to
`Std.WP.Id.of_run_eq_wp`. The contracts by value keep the components opaque in the verification
conditions of their callers, which name their values by `Id.run`.
-/

@[expose] public section

universe u

open scoped Std.WP

/-- A program `x` in `Id` returns its value `x.run`: the contract of a component that a
composition by `vcgen` calls without reasoning about its result. -/
theorem Std.WP.Id.triple_eq_run {α : Type u} (x : Id α) : ⦃ True ⦄ x ⦃ fun r ↦ r = x.run ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- A program `x` in `Id` meets a contract when its value `x.run` meets the postcondition wherever
the precondition holds: the contract of a component whose value is computed outside the program
logic. -/
theorem Std.WP.Id.triple_of_run {α : Type u} {P : Prop} {Q : α → Prop} {x : Id α}
    (h : P → Q x.run) : ⦃ P ⦄ x ⦃ Q ⦄ :=
  ⟨h⟩

namespace JPoints

@[spec]
theorem message_spec (g : MessageGlobals) (n total : Int) :
    ⦃ True ⦄ message g n total ⦃ fun r ↦ r = (message g n total).run ⦄ :=
  Std.WP.Id.triple_eq_run _

@[spec]
theorem Printf.printfMpz_spec (reversed negated : Bool) (format : String) (a b c d : Int) :
    ⦃ True ⦄ printfMpz reversed negated format a b c d
    ⦃ fun r ↦ r = (printfMpz reversed negated format a b c d).run ⦄ :=
  Std.WP.Id.triple_eq_run _

@[spec]
theorem Cli.Failure.message_spec (f : Cli.Failure) :
    ⦃ True ⦄ f.message ⦃ fun r ↦ r = f.message.run ⦄ :=
  Std.WP.Id.triple_eq_run _

@[spec]
theorem Cli.scanMpz_spec (s : Option (List Char)) :
    ⦃ True ⦄ Cli.scanMpz s ⦃ fun r ↦ r = (Cli.scanMpz s).run ⦄ :=
  Std.WP.Id.triple_eq_run _

@[spec]
theorem Cli.costIndex_spec (name : List Char) :
    ⦃ True ⦄ Cli.costIndex name ⦃ fun r ↦ r = (Cli.costIndex name).run ⦄ :=
  Std.WP.Id.triple_eq_run _

@[spec]
theorem Cli.unescape_spec (s : List Char) :
    ⦃ True ⦄ Cli.unescape s ⦃ fun r ↦ r = (Cli.unescape s).run ⦄ :=
  Std.WP.Id.triple_eq_run _

namespace Program

@[spec]
theorem mainCostList_spec (costs : Cli.Costs) :
    ⦃ True ⦄ mainCostList costs ⦃ fun r ↦ r = (mainCostList costs).run ⦄ :=
  Std.WP.Id.triple_eq_run _

@[spec]
theorem mainHead_spec (input : Cli.Input) :
    ⦃ True ⦄ mainHead input ⦃ fun r ↦ r = (mainHead input).run ⦄ :=
  Std.WP.Id.triple_eq_run _

end Program

end JPoints

end
