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
public import JPoints.Proof.DoublePoints
public import JPoints.Proof.DoubleSieve
public import JPoints.Proof.Filters
public import JPoints.Proof.Globals
public import JPoints.Proof.Input
public import JPoints.Proof.Kummer
public import JPoints.Proof.Order
public import JPoints.Proof.Printf
public import JPoints.Proof.Qsort
public import JPoints.Proof.Quintic
public import JPoints.Proof.Rates
public import JPoints.Proof.Reduction
public import JPoints.Proof.Reference
public import JPoints.Proof.Region
public import JPoints.Proof.Rounding
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
public import JPoints.Proof.Sturm
public import JPoints.Proof.SturmChain
public import JPoints.Proof.Tables
public import JPoints.Proof.Transform
public import JPoints.Proof.Truncation
public import JPoints.Proof.Tube
public import JPoints.Proof.TubeBands
public import JPoints.Proof.TwoAdic
public import JPoints.Proof.Values
public import JPoints.Proof.VCSimp
public import JPoints.Proof.Walk

/-!
# The proofs

The proofs that the model meets the specification: the algebra of the Kummer surface
(`JPoints.Proof.Kummer`), the first coordinates of the points of a monic quintic
(`JPoints.Proof.Quintic`), the enumeration of the order of the specification
(`JPoints.Proof.Order`), the brute-force reference (`JPoints.Proof.BruteForce`) and the curve
searched with the points taken back to the curve given (`JPoints.Proof.Transform`); the reference
layer of the contracts: the points over a triple, the text of the points found and the parts of the
enumeration (`JPoints.Proof.Reference`), the classes that the tables of a prime admit
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
collects in the bands (`JPoints.Proof.TubeBands`) and the half-sizes of its cells
(`JPoints.Proof.CellSizes`), the sample of the tube (`JPoints.Proof.Sample`), the sieve of a range
of words of a row of a band (`JPoints.Proof.BandRange`), the ranges of the rows of a band
(`JPoints.Proof.BandRanges`), the sieve by bands (`JPoints.Proof.Region`), and the values of the
components without a contract (`JPoints.Proof.Values`); and the lemmas the contracts need: the facts
about the compile-time constants (`JPoints.Proof.Constants`), on 64-bit words
(`JPoints.Proof.Bits`), on vectors, arrays, lists and numbers (`JPoints.Proof.Containers`), the sort
of the C library (`JPoints.Proof.Qsort`), the values and the rounding of the doubles of the model
(`JPoints.Proof.Double`, `JPoints.Proof.Rounding`), the truncation of rational numbers to doubles
(`JPoints.Proof.Truncation`), the integers that the search computes in doubles
(`JPoints.Proof.DoubleArith`), and the simplification of the verification conditions
(`JPoints.Proof.VCSimp`).
-/
