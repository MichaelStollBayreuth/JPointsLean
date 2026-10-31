/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.BruteForce
public import JPoints.Model.Check
public import JPoints.Model.Choice
public import JPoints.Model.CliNumbers
public import JPoints.Model.Constants
public import JPoints.Model.Double
public import JPoints.Model.DoubleArith
public import JPoints.Model.Input
public import JPoints.Model.Kummer
public import JPoints.Model.Printf
public import JPoints.Model.Qsort
public import JPoints.Model.Rates
public import JPoints.Model.Region
public import JPoints.Model.Rows
public import JPoints.Model.Sample
public import JPoints.Model.Sift
public import JPoints.Model.Sturm
public import JPoints.Model.Tables
public import JPoints.Model.Tube
public import JPoints.Model.TwoAdic
public import JPoints.Model.Walk

/-!
# The model

The executable model of `j-points`, on Lean core and `Std` only:

* `JPoints.Model.Constants`: the compile-time constants of `j-points`.
* `JPoints.Model.Double`, `JPoints.Model.DoubleArith`: the doubles of the C code by their bits,
  and the operations of the C language, the C library and GMP on them.
* `JPoints.Model.Printf`: what `printf` and `gmp_printf` print for the conversions that `j-points`
  uses, the printing of a point and of a polynomial.
* `JPoints.Model.CliNumbers`, `JPoints.Model.Input`: the numbers of the command line, and the
  command line as `read_input` reads it.
* `JPoints.Model.Kummer`: the curve searched, the Kummer surface and the exact lifting test.
* `JPoints.Model.Check`: the exact check of a triple that the sieve leaves, and the output of the
  points.
* `JPoints.Model.Sturm`: the real roots of the polynomial of the curve by Sturm's theorem, and the
  intervals on which it is negative.
* `JPoints.Model.Tables`, `JPoints.Model.TwoAdic`: the tables of residues modulo the primes, and
  the condition at 2.
* `JPoints.Model.Qsort`, `JPoints.Model.Rates`: the sort of the C library, and the rates of the
  primes, sorted.
* `JPoints.Model.Choice`: the choice of the sieving primes by the cost model, the messages of the
  choice, and the end of `init_fmodpsquare`.
* `JPoints.Model.Rows`: the sieve tables of the primes of the first two stages of the sieve.
* `JPoints.Model.Sift`: the second and third stages of the sieve, its static data and the state
  of the thread.
* `JPoints.Model.Walk`: the first stage of the sieve, the rows of the sieve tables for a row, and
  the sieve of a row and of a range of words.
* `JPoints.Model.Tube`: the analysis of the tube, which drops the cells of rows by words where no
  fourth coordinate within its bound solves the Kummer equation, and keeps the words of the others.
* `JPoints.Model.Region`: the real region of a row, and the sieve of the rows of a first coordinate
  by bands, in the tube or in the real region.
* `JPoints.Model.Sample`: the start of the analysis of the plane of `(b, c)`, and its sample of
  the rows for the cost model.
* `JPoints.Model.BruteForce`: the brute-force reference of the specification.
-/
