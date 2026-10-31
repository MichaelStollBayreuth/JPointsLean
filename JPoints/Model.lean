/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.BruteForce
public import JPoints.Model.CliNumbers
public import JPoints.Model.Constants
public import JPoints.Model.Double
public import JPoints.Model.DoubleArith
public import JPoints.Model.Input
public import JPoints.Model.Printf

/-!
# The model

The executable model of `j-points`, on Lean core and `Std` only:

* `JPoints.Model.Constants`: the compile-time constants of `j-points`.
* `JPoints.Model.Double`, `JPoints.Model.DoubleArith`: the doubles of the C code by their bits,
  and the operations of the C language, the C library and GMP on them.
* `JPoints.Model.Printf`: what `printf` and `gmp_printf` print for the conversions that `j-points`
  uses, and the printing of a point.
* `JPoints.Model.CliNumbers`, `JPoints.Model.Input`: the numbers of the command line, and the
  command line as `read_input` reads it.
* `JPoints.Model.BruteForce`: the brute-force reference of the specification.
-/
