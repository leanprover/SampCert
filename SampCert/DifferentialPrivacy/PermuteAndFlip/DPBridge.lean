/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Privacy
import SampCert.DifferentialPrivacy.Pure.DP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Real

noncomputable section

open Classical

namespace SLang
namespace PermuteAndFlip

/-- Dataset-level wrapper around the verified PMF implementation of permute-and-flip. -/
def scoreMechanismPMF {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    SLang.Mechanism T (Fin n.succ) :=
  fun l => permuteAndFlipPMF n (score l) ε₁ ε₂

/-- The score map has range sensitivity `Δ` when neighbouring datasets induce
score vectors whose range distance is at most `Δ`. -/
def rangeSensitive {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
    rangeDistance (score l₁) (score l₂) ≤ Δ

/--
A helper inequality for turning the pointwise `rangeDistance` privacy theorem into
SampCert's ratio-style DP bound.
-/
lemma privacy_multiplier_ge_one
    (ε₁ : ℕ) (ε₂ : ℕ+) {d Δ : ℕ} (hd : d ≤ Δ) :
    1 ≤
      ENNReal.ofReal
        (Real.exp ((((Δ : ℕ) : NNReal) * (((ε₁ : ℕ) : NNReal) / ε₂) : NNReal))) *
        (privacyBase ε₁ ε₂) ^ d := by
  let η : ℝ := ((((ε₁ : ℕ) : NNReal) / ε₂ : NNReal) : ℝ)
  have _hη : 0 ≤ η := by
    positivity
  have hrewrite :
      ENNReal.ofReal (Real.exp ((Δ : ℝ) * η)) * (privacyBase ε₁ ε₂) ^ d =
        ENNReal.ofReal (Real.exp ((Δ - d : ℕ) * η)) := by
    calc
      ENNReal.ofReal (Real.exp ((Δ : ℝ) * η)) * (privacyBase ε₁ ε₂) ^ d
          = ENNReal.ofReal (Real.exp ((Δ : ℝ) * η)) * ENNReal.ofReal ((Real.exp (-η)) ^ d) := by
              simp [privacyBase, η, ENNReal.ofReal_pow, Real.exp_nonneg]
      _ = ENNReal.ofReal (Real.exp ((Δ : ℝ) * η) * (Real.exp (-η)) ^ d) := by
            rw [← ENNReal.ofReal_mul]
            positivity
      _ = ENNReal.ofReal (Real.exp ((Δ : ℝ) * η) * Real.exp ((d : ℝ) * (-η))) := by
            rw [← Real.exp_nat_mul]
      _ = ENNReal.ofReal (Real.exp (((Δ : ℝ) * η) + ((d : ℝ) * (-η)))) := by
            rw [← Real.exp_add]
      _ = ENNReal.ofReal (Real.exp ((Δ - d : ℕ) * η)) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            calc
              ((Δ : ℝ) * η) + ((d : ℝ) * (-η)) = (((Δ : ℝ) - d) * η) := by ring
              _ = ((Δ - d : ℕ) : ℝ) * η := by rw [Nat.cast_sub hd]
  have hreal : 1 ≤ Real.exp ((Δ - d : ℕ) * η) := by
    calc
      1 = Real.exp 0 := by simp
      _ ≤ Real.exp ((Δ - d : ℕ) * η) := by
            apply Real.exp_le_exp.mpr
            positivity
  rw [show ENNReal.ofReal
      (Real.exp ((((Δ : ℕ) : NNReal) * (((ε₁ : ℕ) : NNReal) / ε₂) : NNReal)))
      = ENNReal.ofReal (Real.exp ((Δ : ℝ) * η)) by rfl]
  rw [hrewrite]
  exact ENNReal.one_le_ofReal.mpr hreal

/--
The permute-and-flip PMF wrapper satisfies SampCert's event-based `DP` definition
whenever the score function is range-sensitive on neighbouring datasets.
-/
theorem permuteAndFlipPMF_DP_bound_of_rangeSensitive
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    SLang.DP (scoreMechanismPMF score ε₁ ε₂)
      (((Δ : ℕ) : NNReal) * (((ε₁ : ℕ) : NNReal) / ε₂)) := by
  apply (SLang.event_eq_singleton _ _).mpr
  intro l₁ l₂ hneigh r
  let d := rangeDistance (score l₁) (score l₂)
  let E : ENNReal :=
    ENNReal.ofReal
      (Real.exp ((((Δ : ℕ) : NNReal) * (((ε₁ : ℕ) : NNReal) / ε₂) : NNReal)))
  have hbase :
      (privacyBase ε₁ ε₂) ^ d * scoreMechanismPMF score ε₁ ε₂ l₁ r
        ≤ scoreMechanismPMF score ε₁ ε₂ l₂ r := by
    simpa [scoreMechanismPMF, d] using
      permuteAndFlipPMF_range_privacy
        (q := score l₁) (q' := score l₂) (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
  have hd : d ≤ Δ := hΔ l₁ l₂ hneigh
  have hscale : 1 ≤ E * (privacyBase ε₁ ε₂) ^ d := by
    simpa [E, d] using privacy_multiplier_ge_one ε₁ ε₂ hd
  have hmul :
      scoreMechanismPMF score ε₁ ε₂ l₁ r
        ≤ E * scoreMechanismPMF score ε₁ ε₂ l₂ r := by
    calc
      scoreMechanismPMF score ε₁ ε₂ l₁ r
          = 1 * scoreMechanismPMF score ε₁ ε₂ l₁ r := by simp
      _ ≤ (E * (privacyBase ε₁ ε₂) ^ d) * scoreMechanismPMF score ε₁ ε₂ l₁ r := by
            exact mul_le_mul_left hscale _
      _ = E * ((privacyBase ε₁ ε₂) ^ d * scoreMechanismPMF score ε₁ ε₂ l₁ r) := by
            ac_rfl
      _ ≤ E * scoreMechanismPMF score ε₁ ε₂ l₂ r := by
            exact mul_le_mul_right hbase E
  exact ENNReal.div_le_of_le_mul hmul

/--
Pure-DP version of the range-sensitive bridge theorem for permute-and-flip.

Since SampCert's neighboring definition is hardcoded,
this specializes the result to SampCert's definition of DP.
-/
theorem permuteAndFlipPMF_PureDP_of_rangeSensitive
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    SLang.PureDP (scoreMechanismPMF score ε₁ ε₂)
      (((Δ : ℕ) : NNReal) * (((ε₁ : ℕ) : NNReal) / ε₂)) := by
  exact permuteAndFlipPMF_DP_bound_of_rangeSensitive score Δ ε₁ ε₂ hΔ

end PermuteAndFlip
end SLang
