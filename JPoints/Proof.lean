/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Admits
public import JPoints.Proof.BandRange
public import JPoints.Proof.BandRanges
public import JPoints.Proof.Bits
public import JPoints.Proof.BruteForce
public import JPoints.Proof.CellSizes
public import JPoints.Proof.Check
public import JPoints.Proof.CheckPoint
public import JPoints.Proof.Choice
public import JPoints.Proof.Constants
public import JPoints.Proof.Containers
public import JPoints.Proof.Double
public import JPoints.Proof.DoubleArith
public import JPoints.Proof.DoubleError
public import JPoints.Proof.DoublePoints
public import JPoints.Proof.DoubleSieve
public import JPoints.Proof.Filters
public import JPoints.Proof.Globals
public import JPoints.Proof.Input
public import JPoints.Proof.Kummer
public import JPoints.Proof.Loops
public import JPoints.Proof.Main
public import JPoints.Proof.Order
public import JPoints.Proof.Poly
public import JPoints.Proof.Printf
public import JPoints.Proof.Program
public import JPoints.Proof.Qsort
public import JPoints.Proof.Quintic
public import JPoints.Proof.Rates
public import JPoints.Proof.RealRegion
public import JPoints.Proof.Reduction
public import JPoints.Proof.Reference
public import JPoints.Proof.Region
public import JPoints.Proof.Rounding
public import JPoints.Proof.RowRegion
public import JPoints.Proof.RowRegionEnds
public import JPoints.Proof.RowSetup
public import JPoints.Proof.RowWords
public import JPoints.Proof.Rows
public import JPoints.Proof.Sample
public import JPoints.Proof.Scan
public import JPoints.Proof.Search
public import JPoints.Proof.Setup
public import JPoints.Proof.Sift
public import JPoints.Proof.SiftData
public import JPoints.Proof.SiftRange
public import JPoints.Proof.Sound
public import JPoints.Proof.Sturm
public import JPoints.Proof.SturmChain
public import JPoints.Proof.Tables
public import JPoints.Proof.TaylorShift
public import JPoints.Proof.Transform
public import JPoints.Proof.Truncation
public import JPoints.Proof.Tube
public import JPoints.Proof.TubeApprox
public import JPoints.Proof.TubeBands
public import JPoints.Proof.TubeCell
public import JPoints.Proof.TubeCoeffs
public import JPoints.Proof.TubeCover
public import JPoints.Proof.TubeRun
public import JPoints.Proof.TubeSign
public import JPoints.Proof.TwoAdic
public import JPoints.Proof.UnitPoints
public import JPoints.Proof.Values
public import JPoints.Proof.VCSimp
public import JPoints.Proof.Walk

/-!
# The proofs

The proofs that the model meets the specification: the polynomial of a list of coefficients
(`JPoints.Proof.Poly`), the algebra of the Kummer surface (`JPoints.Proof.Kummer`), the first
coordinates of the points of a monic quintic (`JPoints.Proof.Quintic`), the enumeration of the order
of the specification (`JPoints.Proof.Order`), the brute-force reference (`JPoints.Proof.BruteForce`)
and the curve searched with the points taken back to the curve given (`JPoints.Proof.Transform`);
the reference layer of the contracts: the points over a triple, the text of the points found and the
parts of the enumeration (`JPoints.Proof.Reference`), the classes that the tables of a prime admit
(`JPoints.Proof.Admits`), and those of the points, at every odd prime (`JPoints.Proof.Reduction`),
the tests of the main search (`JPoints.Proof.Filters`) and what the globals of the search hold
(`JPoints.Proof.Globals`); the contracts of the components: the exact check (`JPoints.Proof.Check`),
the text of a point and the format that `printf_mpz` gives `gmp_printf` (`JPoints.Proof.Printf`),
`read_input` (`JPoints.Proof.Input`), the tables of residues of `init_main` and of the third stage
(`JPoints.Proof.Tables`), the tables of the curve at a prime and the rates of the primes
(`JPoints.Proof.Rates`), the choice of the sieving primes (`JPoints.Proof.Choice`), the sieve tables
of the first two stages, from the patterns of their rows and their words (`JPoints.Proof.Rows`,
`JPoints.Proof.RowWords`), the static data of the sieve (`JPoints.Proof.SiftData`), the set-up of
the search (`JPoints.Proof.Setup`), its condition at 2 (`JPoints.Proof.TwoAdic`), the Sturm chain of
`real_roots_init` (`JPoints.Proof.SturmChain`) and its intervals on which `f` is negative
(`JPoints.Proof.Sturm`), the double points and the step of the rows (`JPoints.Proof.Search`), with
the sieve of the pairs of the double points and their test for common factors
(`JPoints.Proof.DoubleSieve`) and the loops of the double points (`JPoints.Proof.DoublePoints`), the
tests for common factors and the third stage (`JPoints.Proof.Sift`), the second stage of a word
(`JPoints.Proof.CheckPoint`), the rows of the sieve tables for a row (`JPoints.Proof.RowSetup`), the
words of a row past the first stage (`JPoints.Proof.Scan`), the first stage and the sieve of a row
in the box (`JPoints.Proof.Walk`), the sieve of a range of words of a chunk
(`JPoints.Proof.SiftRange`), the analysis of the tube (`JPoints.Proof.Tube`) with the ranges that it
collects in the bands (`JPoints.Proof.TubeBands`), the half-sizes of its cells
(`JPoints.Proof.CellSizes`), the values of its loops (`JPoints.Proof.TubeRun`), the rounding errors
of the analysis of a cell (`JPoints.Proof.TubeApprox`), the polynomials of a first coordinate in
doubles (`JPoints.Proof.TubeCoeffs`), the sign of a polynomial over a cell
(`JPoints.Proof.TubeSign`), the verdict of a cell (`JPoints.Proof.TubeCell`) and the words that the
analysis collects (`JPoints.Proof.TubeCover`), the sample of the tube (`JPoints.Proof.Sample`), the
sieve of a range of words of a row of a band (`JPoints.Proof.BandRange`), the ranges of the rows of
a band (`JPoints.Proof.BandRanges`), the sieve by bands (`JPoints.Proof.Region`), the words that the
real region of a row keeps (`JPoints.Proof.RowRegion`), the ends of its excluded intervals in
doubles (`JPoints.Proof.RowRegionEnds`) and the points of the curve in the real region
(`JPoints.Proof.RealRegion`), the rows and the units of work, which hold the points
(`JPoints.Proof.UnitPoints`), the search of `find_points` and of `main` (`JPoints.Proof.Program`),
the soundness of the tests of the main search (`JPoints.Proof.Sound`), and the values of the
components without a contract (`JPoints.Proof.Values`); the main theorems, on what the program
prints, from the contracts (`JPoints.Proof.Main`); and the lemmas the contracts need: the facts
about the compile-time constants (`JPoints.Proof.Constants`), on 64-bit words
(`JPoints.Proof.Bits`), on arrays, lists, ranges and numbers (`JPoints.Proof.Containers`), the
invariants of the loops that fill arrays (`JPoints.Proof.Loops`), the sort of the C library
(`JPoints.Proof.Qsort`), the values and the rounding of the doubles of the model
(`JPoints.Proof.Double`, `JPoints.Proof.Rounding`), the truncation of rational numbers to doubles
(`JPoints.Proof.Truncation`), the arithmetic of the doubles and the integers that the search
computes in them (`JPoints.Proof.DoubleArith`), the error bounds of computations in doubles
(`JPoints.Proof.DoubleError`), the Taylor shifts of the tube (`JPoints.Proof.TaylorShift`), and the
simplification of the verification conditions (`JPoints.Proof.VCSimp`).
-/
