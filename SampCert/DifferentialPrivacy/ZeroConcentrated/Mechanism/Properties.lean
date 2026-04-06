/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code

/-!
# ``privNoisedQuery`` Implementation

This file proves differential privacy for ``privNoisedQuery``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang


/--
The zCDP mechanism with bounded sensitivity satisfies the bound for ``(Δε₂/ε₁)^2``-zCDP.
-/
theorem privNoisedQuery_zCDPBound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDPBound (privNoisedQuery query Δ ε₁ ε₂) ((1/2) * ((ε₁ : NNReal) / ε₂) ^ 2) := by
  simp [zCDPBound, privNoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @discrete_GaussianGenSample_ZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A

  -- Turn it into an equality ASAP
  rw [sensitivity] at bounded_sensitivity
  have bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  have X :
    (ENNReal.ofReal α *
      (ENNReal.ofReal ((query l₁ - query l₂).cast ^ OfNat.ofNat 2) /
        (OfNat.ofNat 2 * (ofNNReal (NNReal.ofPNat (Δ * ε₂)) / ofNNReal (NNReal.ofPNat ε₁)) ^ OfNat.ofNat 2))) ≤
  (ENNReal.ofReal α *
      (ENNReal.ofReal (Δ ^ OfNat.ofNat 2) /
        (OfNat.ofNat 2 * (ofNNReal (NNReal.ofPNat (Δ * ε₂)) / ofNNReal (NNReal.ofPNat ε₁)) ^ OfNat.ofNat 2))) := by
      refine (ENNReal.mul_le_mul_iff_right ?G1 ?G2).mpr ?G3
      case G1 =>
        intro HK
        simp_all
        linarith
      case G2 => exact ofReal_ne_top
      refine ENNReal.div_le_div ?G4 ?G5
      case G5 => rfl
      apply ofReal_le_ofReal
      refine sq_le_sq.mpr ?G4.h.a
      simp only [NNReal.ofPNat, Nonneg.mk_natCast]
      rw [NNReal.abs_eq]
      rw [← Int.cast_abs]
      have X1 : |query l₁ - query l₂| ≤ (Δ.val : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast bounded_sensitivity
      have : (|query l₁ - query l₂| : ℝ) ≤ ((Δ.val : ℤ) : ℝ) := by exact_mod_cast X1
      simpa using this
  apply le_trans
  · apply X
  clear X
  apply Eq.le
  -- Block 1: Rewrite NNReal.ofPNat everywhere as ↑n (defeq)
  simp only [show ∀ (n : ℕ+), (NNReal.ofPNat n : NNReal) = ((n.val : ℕ) : NNReal) from fun _ => rfl]
  -- Block 2: The ↑↑↑(Δ * ε₂) on the LHS is ℝ≥0∞-coerced; on RHS ↑↑↑ε₁, ↑↑↑ε₂ are ℝ-coerced.
  -- Rewrite LHS to match: ↑↑↑(Δ*ε₂)/↑↑↑ε₁ is ENNReal. We want to wrap everything in ENNReal.ofReal.
  -- Key: ENNReal.ofReal ↑n = ↑n (when n : ℕ, reading ↑n : ℝ≥0∞ via natCast)
  have hcoeℝ : ∀ (n : ℕ+), ((((n : ℕ+) : ℕ) : NNReal) : ℝ≥0∞) =
                          ENNReal.ofReal ((((n : ℕ+) : ℕ) : NNReal) : ℝ) := by
    intro n
    rw [ENNReal.ofReal_coe_nnreal]
  rw [hcoeℝ ε₁, hcoeℝ (Δ * ε₂)]
  -- Block 3: Consolidate LHS into single ENNReal.ofReal
  have hε₁pos : (0 : ℝ) < ((((ε₁ : ℕ+) : ℕ) : NNReal) : ℝ) := by
    exact_mod_cast ε₁.pos
  rw [← ENNReal.ofReal_div_of_pos hε₁pos]
  have hdivnn : (0 : ℝ) ≤ (((((Δ * ε₂) : ℕ+) : ℕ) : NNReal) : ℝ) / ((((ε₁ : ℕ+) : ℕ) : NNReal) : ℝ) := by
    apply div_nonneg <;> simp
  rw [← ENNReal.ofReal_pow hdivnn]
  -- Convert `2 : ℝ≥0∞` to `ENNReal.ofReal 2`
  rw [show (OfNat.ofNat 2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]; rfl]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * _)]
  rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ α)]
  -- Block 4: Pure Real equality
  congr 1
  have hε₁r : (0 : ℝ) < (((ε₁ : ℕ+) : ℕ) : ℝ) := by exact_mod_cast ε₁.pos
  have hε₂r : (0 : ℝ) < (((ε₂ : ℕ+) : ℕ) : ℝ) := by exact_mod_cast ε₂.pos
  push_cast
  -- Normalize NNReal-mediated casts on RHS to direct ℕ→ℝ
  change α * ((((Δ : ℕ+) : ℕ) : ℝ) ^ 2 /
    (2 * ((((Δ : ℕ+) : ℕ) : ℝ) * (((ε₂ : ℕ+) : ℕ) : ℝ) / (((ε₁ : ℕ+) : ℕ) : ℝ)) ^ 2))
    = 2⁻¹ * ((((ε₁ : ℕ+) : ℕ) : ℝ) / (((ε₂ : ℕ+) : ℕ) : ℝ)) ^ 2 * α
  field_simp

lemma discrete_gaussian_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ x : ℤ) :
  discrete_gaussian σ μ (x - τ) = discrete_gaussian σ (μ + τ) (x) := by
  simp [discrete_gaussian]
  congr 1
  · simp [gauss_term_ℝ]
    congr 3
    ring_nf
  · rw [shifted_gauss_sum h]

/--
privNoisedQuery preserves absolute continuity between neighbours
-/
def privNoisedQuery_AC (query : List T -> ℤ) (Δ ε₁ ε₂ : ℕ+) : ACNeighbour (privNoisedQuery query Δ ε₁ ε₂) := by
  rw [ACNeighbour]
  intro l₁ l₂ _
  rw [AbsCts]
  intro n Hk
  exfalso
  simp [privNoisedQuery, DiscreteGaussianGenPMF, DiscreteGaussianGenSample, DFunLike.coe] at Hk
  have Hk := Hk (n - query l₂)
  simp at Hk
  have X := @discrete_gaussian_pos (Δ.val.cast * ε₂.val.cast / ε₁.val.cast) ?G1 0 (n - query l₂)
  case G1 =>
    cases Δ
    cases ε₁
    cases ε₂
    aesop
  simp at *
  linarith

/--
The zCDP mechanism is ``(Δε₂/ε₁)^2``-zCDP.
-/
theorem privNoisedQuery_zCDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDP (privNoisedQuery query Δ ε₁ ε₂) ((1/2) * ((ε₁ : NNReal) / ε₂) ^ 2) := by
  simp only [zCDP]
  apply And.intro
  · exact privNoisedQuery_AC query Δ ε₁ ε₂
  · apply privNoisedQuery_zCDPBound
    exact bounded_sensitivity

end SLang
