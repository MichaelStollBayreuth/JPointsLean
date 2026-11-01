/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Admits
public import JPoints.Proof.Bits
public import JPoints.Proof.BruteForce
public import JPoints.Proof.Check
public import JPoints.Proof.Constants
public import JPoints.Proof.Containers
public import JPoints.Proof.Double
public import JPoints.Proof.Filters
public import JPoints.Proof.Globals
public import JPoints.Proof.Input
public import JPoints.Proof.Kummer
public import JPoints.Proof.Order
public import JPoints.Proof.Printf
public import JPoints.Proof.Reference
public import JPoints.Proof.Rounding
public import JPoints.Proof.Transform
public import JPoints.Proof.Values
public import JPoints.Proof.VCSimp

/-!
# The proofs

The proofs that the model meets the specification: the algebra of the Kummer surface
(`JPoints.Proof.Kummer`), the enumeration of the order of the specification (`JPoints.Proof.Order`),
the brute-force reference (`JPoints.Proof.BruteForce`) and the curve searched with the points taken
back to the curve given (`JPoints.Proof.Transform`); the reference layer of the contracts:
the points over a triple, the text of the points found and the parts of the enumeration
(`JPoints.Proof.Reference`), the classes that the tables of a prime admit (`JPoints.Proof.Admits`),
the tests of the main search (`JPoints.Proof.Filters`) and what the globals of the search hold
(`JPoints.Proof.Globals`); the contracts of the components: the exact check (`JPoints.Proof.Check`),
the text of a point and the format that `printf_mpz` gives `gmp_printf` (`JPoints.Proof.Printf`),
`read_input` (`JPoints.Proof.Input`), and the values of the components without a contract
(`JPoints.Proof.Values`); and the lemmas the contracts need: the facts about the compile-time
constants (`JPoints.Proof.Constants`), on 64-bit words (`JPoints.Proof.Bits`), on vectors, arrays,
lists and numbers (`JPoints.Proof.Containers`), the values and the rounding of the doubles of the
model (`JPoints.Proof.Double`, `JPoints.Proof.Rounding`), and the simplification of the
verification conditions (`JPoints.Proof.VCSimp`).
-/
