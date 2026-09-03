/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.Core

/-!
Range-distance layer for permute-and-flip.

This module packages the score-difference normalization used to state privacy directly in terms of
the range metric on score vectors.
-/

noncomputable section

open scoped Classical

namespace SLang
namespace PermuteAndFlip

/--
Coordinatewise score difference between two score vectors.
-/
def scoreDiff {n : CandidateCount} (q q' : Scores n) : Fin n.succ → ℤ :=
  fun i => (q' i : ℤ) - q i

namespace RangePrivacy

def diffSet {n : CandidateCount} (q q' : Scores n) : Finset ℤ :=
  Finset.univ.image (scoreDiff q q')

theorem diffSet_nonempty {n : CandidateCount} (q q' : Scores n) : (diffSet q q').Nonempty := by
  exact ⟨scoreDiff q q' 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩

def diffMin {n : CandidateCount} (q q' : Scores n) : ℤ :=
  (diffSet q q').min' (diffSet_nonempty q q')

def diffMax {n : CandidateCount} (q q' : Scores n) : ℤ :=
  (diffSet q q').max' (diffSet_nonempty q q')

/--
The range distance on score vectors: the width of the set of coordinatewise score differences.

Equivalently, this is `max_i (q' i - q i) - min_i (q' i - q i)`.
-/
def rangeDistance {n : CandidateCount} (q q' : Scores n) : ℕ :=
  Int.toNat (diffMax q q' - diffMin q q')

/--
Shift amount that moves the minimum score difference to `0`. This is the
normalization that lets the privacy proof compare two natural-valued score
vectors without leaving `ℕ`.
-/
def diffShift {n : CandidateCount} (q q' : Scores n) : ℕ :=
  Int.toNat (- diffMin q q')

/-- The shifted coordinatewise differences, now normalized to lie in `[0, rangeDistance]`. -/
def shiftedDiff {n : CandidateCount} (q q' : Scores n) : Fin n.succ → ℕ :=
  fun i => Int.toNat (scoreDiff q q' i + diffShift q q')

/-- Lower endpoint of the normalized interval of score differences. -/
def lowerEndpoint {n : CandidateCount} (q q' : Scores n) : ℕ :=
  Int.toNat (diffMin q q' + diffShift q q')

/-- Upper endpoint of the normalized interval of score differences. -/
def upperEndpoint {n : CandidateCount} (q q' : Scores n) : ℕ :=
  Int.toNat (diffMax q q' + diffShift q q')

theorem scoreDiff_mem_interval
    {n : CandidateCount} (q q' : Scores n) (i : Fin n.succ) :
    diffMin q q' ≤ scoreDiff q q' i ∧ scoreDiff q q' i ≤ diffMax q q' := by
  constructor
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)

theorem diffMin_add_diffShift_nonneg
    {n : CandidateCount} (q q' : Scores n) :
    0 ≤ diffMin q q' + diffShift q q' := by
  by_cases hmin : 0 ≤ diffMin q q'
  · have hnonpos : -diffMin q q' ≤ 0 := by linarith
    rw [diffShift, Int.toNat_of_nonpos hnonpos]
    omega
  · have hnonneg : 0 ≤ -diffMin q q' := by linarith
    rw [diffShift, Int.toNat_of_nonneg hnonneg]
    omega

theorem shiftedDiff_eq_targetShift
    {n : CandidateCount} (q q' : Scores n) :
    (fun i => q i + shiftedDiff q q' i) = (fun i => q' i + diffShift q q') := by
  funext i
  have hmem := scoreDiff_mem_interval q q' i
  have hnonneg : 0 ≤ scoreDiff q q' i + diffShift q q' := by
    have hbase : 0 ≤ diffMin q q' + diffShift q q' := diffMin_add_diffShift_nonneg q q'
    omega
  have hcast :
      ((q i + shiftedDiff q q' i : ℕ) : ℤ) = (q' i + diffShift q q' : ℕ) := by
    dsimp [shiftedDiff]
    rw [Int.toNat_of_nonneg hnonneg]
    simp [scoreDiff]
    omega
  exact Int.ofNat.inj hcast

/-!
The next three lemmas are the core normalization facts used in `Privacy.lean`:
every normalized coordinate lies between the common endpoints, and the width of
that interval is exactly the range distance.
-/

theorem lowerEndpoint_le_shiftedDiff
    {n : CandidateCount} (q q' : Scores n) (i : Fin n.succ) :
    lowerEndpoint q q' ≤ shiftedDiff q q' i := by
  have hmem := scoreDiff_mem_interval q q' i
  have _ : 0 ≤ diffMin q q' + diffShift q q' := diffMin_add_diffShift_nonneg q q'
  have _ : 0 ≤ scoreDiff q q' i + diffShift q q' := by
    omega
  refine Int.toNat_le_toNat ?_
  omega

theorem shiftedDiff_le_upperEndpoint
    {n : CandidateCount} (q q' : Scores n) (i : Fin n.succ) :
    shiftedDiff q q' i ≤ upperEndpoint q q' := by
  have hmem := scoreDiff_mem_interval q q' i
  have _ : 0 ≤ scoreDiff q q' i + diffShift q q' := by
    have _ : 0 ≤ diffMin q q' + diffShift q q' := diffMin_add_diffShift_nonneg q q'
    omega
  refine Int.toNat_le_toNat ?_
  omega

theorem upperEndpoint_eq_lowerEndpoint_add_rangeDistance
    {n : CandidateCount} (q q' : Scores n) :
    upperEndpoint q q' = lowerEndpoint q q' + rangeDistance q q' := by
  have hleft_nonneg : 0 ≤ diffMin q q' + diffShift q q' := diffMin_add_diffShift_nonneg q q'
  have hwidth_nonneg : 0 ≤ diffMax q q' - diffMin q q' := by
    have hmem := scoreDiff_mem_interval q q' 0
    omega
  have hsum_nonneg : 0 ≤ diffMax q q' + diffShift q q' := by
    omega
  apply Int.ofNat.inj
  simp [upperEndpoint, lowerEndpoint, rangeDistance,
    Int.toNat_of_nonneg hleft_nonneg, Int.toNat_of_nonneg hwidth_nonneg,
    Int.toNat_of_nonneg hsum_nonneg]
  omega

end RangePrivacy

abbrev rangeDistance {n : CandidateCount} (q q' : Scores n) : ℕ :=
  RangePrivacy.rangeDistance q q'

end PermuteAndFlip
end SLang
