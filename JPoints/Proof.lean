/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Bits
public import JPoints.Proof.Containers
public import JPoints.Proof.Double
public import JPoints.Proof.Rounding
public import JPoints.Proof.VCSimp

/-!
# The proofs

The proofs that the model meets the specification; so far the lemmas the contracts need: on 64-bit
words (`JPoints.Proof.Bits`), on vectors, arrays, lists and numbers (`JPoints.Proof.Containers`),
the values and the rounding of the doubles of the model (`JPoints.Proof.Double`,
`JPoints.Proof.Rounding`), and the simplification of the verification conditions
(`JPoints.Proof.VCSimp`).
-/
