/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import JPoints.Model.Program

/-!
# The executable `j-points-model`

The root of the Lake target `j-points-model`, the program of the faithful model of `j-points`
(`JPoints.Program.main`), with the command line of `j-points` and its options, against which
`scripts/difftest.py` runs. It imports only the model.
-/

/-- The command-line program `j-points-model`, `JPoints.Program.main`. -/
public def main (args : List String) : IO UInt32 := JPoints.Program.main args
