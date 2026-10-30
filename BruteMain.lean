/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import JPoints.Model.BruteForce

/-!
# The executable `j-points-brute`

The root of the Lake target `j-points-brute`, which prints the points of the brute-force reference
`JPoints.bruteForce` of a curve, one per line, as `j-points` prints them with its default format, so
that `scripts/brutetest.py` can compare them with the reference lists of the C repository and with
the output of `j-points`. Its command line is `j-points-brute 'a_0 a_1 ... a_d' H [-a] [-w W]`, the
coefficients separated by spaces. It imports only the model.
-/

/-- The options after the height bound: `-a`, and `-w` with the bound on the fourth coordinate. -/
private def parseOptions : List String → Option (Bool × Option Nat)
  | [] => some (false, none)
  | "-a" :: rest => (parseOptions rest).map fun (_, w) ↦ (true, w)
  | "-w" :: w :: rest => do
    let (a, _) ← parseOptions rest
    return (a, some (← w.toNat?))
  | _ => none

/-- The coefficient list, the height bound and the options of the command line. -/
private def parseArgs : List String → Option (List Int × Nat × Bool × Option Nat)
  | cs :: h :: rest => do
    let coeffs ← ((cs.splitOn " ").filter (· ≠ "")).mapM String.toInt?
    return (coeffs, ← h.toNat?, ← parseOptions rest)
  | _ => none

/-- The program `j-points-brute`: the points of `JPoints.bruteForce`, or a usage message and the
exit status 2. -/
public def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | some (cs, H, all, W) =>
    let out ← IO.getStdout
    for (a, b, c, d) in JPoints.bruteForce cs H all W do
      out.putStrLn s!"({a}, {b}, {c}, {d})"
    return 0
  | none =>
    IO.eprintln "Usage: j-points-brute 'a_0 a_1 ... a_d' H [-a] [-w W]"
    return 2
