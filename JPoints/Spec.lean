/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Spec.Basic
public import JPoints.Spec.Sturm

/-!
# The specification

The specification of `j-points`, on Mathlib only, so that it can be read without the model: the
points of the Kummer surface that the program finds, their list in the order in which it finds them
and the polynomial whose squarefreeness it checks (`JPoints.Spec.Basic`), and Sturm's theorem, which
the theorems on the real region assume (`JPoints.Spec.Sturm`).
-/
