/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Properties
import SampCert.DifferentialPrivacy.Pure.System

noncomputable section

open Classical

namespace SLang

variable {sv_Ta: Type} (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+)
variable (Hqs_sens : ∀ i, sensitivity (qs i) 1)

def cov_τ_def (v0 : ℤ) (vs : List ℤ) (l₁ l₂ : List sv_T) : ℤ := (sv8_G qs l₁ [] v0 vs) - (sv8_G qs l₂ [] v0 vs)

lemma cov_τ_def_neg (v0 : ℤ) (vs : List ℤ) (l₁ l₂ : List sv_T) : cov_τ_def qs v0 vs l₁ l₂ = -cov_τ_def qs v0 vs l₂ l₁ := by
  simp [cov_τ_def]

def cov_vk_def (v0 : ℤ) (vs : List ℤ) (l₁ l₂ : List sv_T) (point : ℕ) : ℤ :=
  -- exactDiffSum (point + 1) l₂ - exactDiffSum (point + 1) l₁ + cov_τ_def qs v0 vs l₁ l₂
  qs (point + 1) l₂ - qs (point + 1) l₁ + cov_τ_def qs v0 vs l₁ l₂

lemma cov_vk_def_neg (v0 : ℤ) (vs : List ℤ) (l₁ l₂ : List sv_T) : cov_vk_def qs v0 vs l₁ l₂ point = -cov_vk_def qs v0 vs l₂ l₁ point := by
  simp [cov_τ_def, cov_vk_def]
  linarith

-- FIXME: Move
lemma tsum_shift (Δ : ℤ) (f : ℤ → ENNReal) : (∑'(x : ℤ), f x = ∑'(x : ℤ), f (x + Δ)) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i => exact (fun x => x.1 + Δ)
  · simp [Function.Injective]
  · simp
    intro x Hx
    exists (x - Δ)
    simp
    trivial
  · intro
    rfl

lemma laplace_inequality' (τ τ' : ℤ) (Δ : ℕ+) :
      ((ENNReal.ofReal (Real.exp (-abs τ' / (Δ * ε₂ / ε₁)))) * ((DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0 τ))) ≤
      (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0) (τ + τ') := by
  simp [DiscreteLaplaceGenSamplePMF, PMF.instFunLike]
  generalize HA : (Real.exp (↑↑ε₁ / (↑↑Δ * ↑↑ε₂)) - 1) = A
  generalize HB : (Real.exp (↑↑ε₁ / (↑↑Δ * ↑↑ε₂)) + 1) = B
  generalize HC : ((Δ : Real) * ε₂ / ε₁) = C
  rw [<- ENNReal.ofReal_mul ?G1]
  case G1 => apply Real.exp_nonneg
  apply ENNReal.ofReal_le_ofReal
  conv =>
    lhs
    rw [mul_comm]
    repeat rw [mul_assoc]
  apply mul_le_mul_of_nonneg
  · rfl
  · rw [← Real.exp_add]
    apply Real.exp_monotone
    repeat rw [<- neg_div]
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · simp
      have H := @abs_add_le ℝ _ _ _ τ τ'
      linarith
    · rw [<- HC]
      simp [div_nonneg_iff]
  · rw [<- HA]
    rw [<- HB]
    simp [div_nonneg_iff]
    left
    conv =>
      lhs
      rw [<- add_zero 0]
    apply add_le_add
    · apply Real.exp_nonneg
    · simp
  · apply Real.exp_nonneg

lemma laplace_inequality (τ τ' : ℤ) (Δ : ℕ+) :
      ((DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0 τ)) ≤
      ((ENNReal.ofReal (Real.exp (abs τ' / (Δ * ε₂ / ε₁)))) *
      (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0) (τ + τ')) := by
    apply le_trans _ ?G1
    case G1 =>
      apply mul_le_mul_right
      apply laplace_inequality'
    repeat rw [<- mul_assoc]
    conv =>
      lhs
      rw [<- one_mul (DiscreteLaplaceGenSamplePMF _ _ _  _)]
    apply mul_le_mul
    · apply Eq.le
      rw [<- ENNReal.ofReal_mul ?G1]
      case G1 => apply Real.exp_nonneg
      rw [<- Real.exp_add]
      symm
      simp
      rw [← add_div]
      rw [div_eq_zero_iff]
      left
      simp
    · rfl
    · apply zero_le
    · apply zero_le


lemma laplace_inequality_sub (τ τ' : ℤ) (Δ : ℕ+) :
      ((DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0 (τ + τ'))) ≤
      ((ENNReal.ofReal (Real.exp (abs τ' / (Δ * ε₂ / ε₁)))) *
      (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0) τ) := by
    apply le_trans
    · apply laplace_inequality ε₁ ε₂ (τ + τ') (-τ') Δ
    apply Eq.le
    simp

include Hqs_sens in
lemma DSN (N : ℕ) (H : Neighbour L1 L2) : ((qs N L1) : ℝ) - (qs N L2) ≤ 1 := by
  let Hqs_sens' := Hqs_sens N L1 L2 H
  rw [← Int.cast_sub]
  rw [<- Int.cast_one]
  apply Int.cast_le.mpr
  let X1 := Int.ofNat_le_ofNat_of_le Hqs_sens'
  simp only [Int.natCast_natAbs, Nat.cast_one] at X1
  apply le_trans _ X1
  apply le_abs_self

include Hqs_sens in
lemma Hsens_cov_τ_lemma (HN : Neighbour l₁ l₂) : sv8_sum qs l₁ H v0 - sv8_sum qs l₂ H v0 ≤ OfNat.ofNat 1 := by
  simp only [sv8_sum]
  rw [add_tsub_add_eq_tsub_right]
  have X := @DSN sv_T qs Hqs_sens l₁ l₂ H.length HN
  rw [← Int.cast_sub] at X
  have Y : (@OfNat.ofNat.{0} Real 1 (@One.toOfNat1.{0} Real Real.instOne)) = (@OfNat.ofNat.{0} Int (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (@instOfNat (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) :=
    by simp
  rw [Y] at X
  apply Int.cast_le.mp at X
  apply le_trans X
  simp

include Hqs_sens in
lemma Hsens_cov_τ (v0 : ℤ) (vs : List ℤ) (l₁ l₂ : List sv_T) (Hneighbour : Neighbour l₁ l₂) : cov_τ_def qs v0 vs l₁ l₂ ≤ sens_cov_τ := by
  dsimp [cov_τ_def, sens_cov_τ]

  suffices (∀ H v0, sv8_G qs l₁ H v0 vs - sv8_G qs l₂ H v0 vs ≤ sens_cov_τ.val.cast) by
    apply this

  induction vs
  · intro H v0
    dsimp [sens_cov_τ]
    simp only [sv8_G]
    apply Hsens_cov_τ_lemma <;> trivial
  · rename_i next fut IH
    intro H v0
    simp only [sv8_G]
    apply le_trans (max_sub_max_le_max _ _ _ _)
    -- Do both cases separately
    apply Int.max_le.mpr
    apply And.intro
    · apply Hsens_cov_τ_lemma <;> trivial
    · apply IH

-- Prove sensitivity bound
include Hqs_sens in
lemma Hsens_cov_vk (v0 : ℤ) (vs : List ℤ) (l₁ l₂ : List sv_T) (point : ℕ) (Hneighbour : Neighbour l₁ l₂) : cov_vk_def qs v0 vs l₁ l₂ point ≤ sens_cov_vk := by
  dsimp [cov_vk_def]
  have X := Hsens_cov_τ qs Hqs_sens v0 vs l₁ l₂ Hneighbour
  simp_all [sens_cov_vk, sens_cov_τ]
  rw [<- one_add_one_eq_two]
  apply Int.add_le_add _ X

  let Hqs_sens' := Hqs_sens (point + 1) l₂ l₁ (Neighbour_symm _ _ Hneighbour)
  let X1 := Int.ofNat_le_ofNat_of_le Hqs_sens'
  simp only [Int.natCast_natAbs, Nat.cast_one] at X1
  apply le_trans _ X1
  apply le_abs_self

include Hqs_sens in
lemma sv9_aboveThresh_pmf_DP HL (ε : NNReal) (Hε : ε = ε₁ / ε₂) :
    PureDPSystem.prop (@sv9_aboveThresh_SPMF sv_T qs T HL ε₁ ε₂) ε := by
  -- Unfold DP definitions
  simp [DPSystem.prop]
  apply singleton_to_event
  unfold DP_singleton
  intro l₁ l₂ Hneighbour point

  apply ENNReal.div_le_of_le_mul
  simp [sv9_aboveThresh_SPMF, DFunLike.coe, PMF.instFunLike]

  cases point
  · -- point = 0
    simp [sv9_aboveThresh]

    -- Put sums on outside
    conv =>
      enter [2]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i]
      rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i_1]
      repeat rw [<- mul_assoc]
      enter [1]
      rw [mul_comm (ENNReal.ofReal _)]
      repeat rw [mul_assoc]
      rw [mul_comm (ENNReal.ofReal _)]
    conv =>
      enter [2, 1, i, 1, i_1]
      repeat rw [mul_assoc]
    conv =>
      enter [1, 1, i]
      rw [← ENNReal.tsum_mul_left]

    -- Change of variables
    let cov_τ : ℤ := 0
    -- let cov_vk : ℤ := exactDiffSum 0 l₂ - exactDiffSum 0 l₁ + cov_τ
    let cov_vk : ℤ := qs 0 l₂ - qs 0 l₁ + cov_τ
    conv =>
      lhs
      rw [tsum_shift cov_τ]
      enter [1, τ]
      rw [tsum_shift cov_vk]
      enter [1, vk]
    conv =>
      rhs
      enter [1, τ, 1, vk]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply ENNReal.tsum_le_tsum
    intro vk

    rw [<- mul_assoc]
    rw [<- mul_assoc]
    rw [<- mul_assoc]
    apply mul_le_mul
    · -- Laplace bound
      simp [cov_τ]
      rw [mul_assoc]
      apply mul_le_mul_right
      simp [privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure]
      apply le_trans
      · apply laplace_inequality_sub
      rw  [mul_comm]
      apply mul_le_mul_right
      rw [Hε]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_monotone
      simp [sens_cov_vk, sens_cov_τ]

      have X : |((qs 0 l₂) : ℝ) - (qs 0 l₁)| ≤ 1 := by
        rw [abs_le]
        apply And.intro
        · apply neg_le.mp
          simp only [neg_sub]
          exact DSN qs Hqs_sens 0 Hneighbour
        · exact DSN qs Hqs_sens 0 (Neighbour_symm _ _ Hneighbour)

      ring_nf
      rw [InvolutiveInv.inv_inv]
      conv =>
        lhs
        rw [mul_comm]
        rw [<- mul_assoc]
        rw [<- mul_assoc]
        rw [mul_comm]
        enter [2]
        rw [mul_comm]
      simp
      apply le_trans _ X
      conv =>
        rhs
        rw [<- one_mul (abs _)]
      apply mul_le_mul
      · apply inv_le_one_of_one_le₀
        simp
      · dsimp only [cov_vk, cov_τ]
        push_cast
        simp
      · apply abs_nonneg
      · simp


    · -- Conditionals should be equal
      suffices (τ + T + cov_τ ≤ sv8_sum qs l₁ [] (vk + cov_vk)) = (τ + T ≤ sv8_sum qs l₂ [] vk) by
        split <;> simp_all
        split <;> simp_all
        linarith
      apply propext
      simp [sv8_sum, cov_vk]
      apply Iff.intro
      · intro _
        linarith
      · intro _
        linarith

    · apply zero_le
    · apply zero_le


  · rename_i point
    -- point > 0
    -- proceed with the proof in the paper
    simp [sv9_aboveThresh]

    -- Cancel out the deterministic parts
    conv =>
      enter [2]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i]
      rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i_1]
      repeat rw [<- mul_assoc]
      enter [1]
      rw [mul_comm (ENNReal.ofReal _)]
      repeat rw [mul_assoc]
      rw [mul_comm (ENNReal.ofReal _)]
    conv =>
      enter [2, 1, i, 1, i_1]
      repeat rw [mul_assoc]
    conv =>
      enter [1, 1, i]
      rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro v0
    apply ENNReal.tsum_le_tsum
    intro vs
    apply mul_le_mul_right
    apply mul_le_mul_right

    -- Rearrange to put sums on the outside
    conv =>
      lhs
      enter [1, τ]
      rw [← ENNReal.tsum_mul_left]
      enter [1, vk]
    conv =>
      rhs
      rw [← ENNReal.tsum_mul_left]
      enter [1, τ]
      rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_mul_left]
      enter [1, vk]

    simp [sv8_cond, sv8_sum]

    -- Perform the changes of variables, so that the sums are pointwise le
    let cov_τ : ℤ := cov_τ_def qs v0 vs l₁ l₂
    let cov_vk : ℤ := cov_vk_def qs v0 vs l₁ l₂ point

    conv =>
      lhs
      rw [tsum_shift cov_τ]
      enter [1, τ]
      rw [tsum_shift cov_vk]
      enter [1, vk]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply ENNReal.tsum_le_tsum
    intro vk

    -- The change of variables make the conditional equal
    repeat rw [<- mul_assoc]
    apply mul_le_mul' _ ?G2
    case G2 =>
      apply Eq.le
      suffices ((sv8_G qs l₁ [] v0 ↑vs < τ + cov_τ + T) = (sv8_G qs l₂ [] v0 ↑vs < τ + T)) ∧
               ((τ + cov_τ + T ≤ qs (point + 1) l₁ + (vk + cov_vk)) = (τ + T ≤ qs (point + 1) l₂ + vk)) by
        simp_all
      apply And.intro
      · -- cov_τ
        apply propext
        dsimp [cov_τ, cov_τ_def]
        apply Iff.intro <;> intro _ <;> linarith
      · -- cov_vk
        apply propext
        dsimp [cov_vk, cov_vk_def]
        apply Iff.intro <;> intro _ <;> linarith

    simp [privNoiseThresh, privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure]

    -- Apply the Laplace inequalities
    apply le_trans
    · apply mul_le_mul
      · apply laplace_inequality_sub
      · apply laplace_inequality_sub
      · apply zero_le
      · apply zero_le

    -- Cancel the Laplace samples
    conv =>
      lhs
      rw [mul_assoc]
      rw [mul_comm]
    conv =>
      rhs
      rw [mul_assoc]
      rw [mul_comm]
    repeat rw [mul_assoc]
    apply mul_le_mul_right
    conv =>
      lhs
      rw [mul_comm]
    repeat rw [mul_assoc]
    apply mul_le_mul_right

    -- Apply the ineuqalities
    rw [<- ENNReal.ofReal_mul ?G1]
    case G1 => apply Real.exp_nonneg
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_monotone
    apply @le_trans _ _ _ ((|sens_cov_τ| : ℝ) / (↑↑(2 * sens_cov_τ) * ↑↑ε₂ / ↑↑ε₁) + (|sens_cov_vk| : ℝ) / (↑↑(2 * sens_cov_vk) * ↑↑ε₂ / ↑↑ε₁))
    · have W : |cov_τ.cast| ≤ (sens_cov_τ.val : ℝ) := by
        apply abs_le'.mpr
        apply And.intro
        · dsimp only [cov_τ]
          apply Int.cast_le.mpr
          apply Hsens_cov_τ _ Hqs_sens <;> trivial
        · dsimp only [cov_τ]
          rw [cov_τ_def_neg]
          simp
          apply Int.cast_le.mpr
          apply Hsens_cov_τ _ Hqs_sens
          apply Neighbour_symm
          apply Hneighbour

      have X : |cov_vk.cast| ≤ (sens_cov_vk.val : ℝ) := by
        apply abs_le'.mpr
        apply And.intro
        · dsimp only [cov_vk]
          apply Int.cast_le.mpr
          apply Hsens_cov_vk _ Hqs_sens
          trivial
        · dsimp only [cov_vk]
          rw [cov_vk_def_neg]
          simp
          apply Int.cast_le.mpr
          apply Hsens_cov_vk _ Hqs_sens
          apply Neighbour_symm
          trivial

      apply add_le_add
      · simp
        apply div_le_div_of_nonneg_right
        · apply W
        · apply mul_nonneg <;> simp
      · apply div_le_div_of_nonneg_right
        · simp
          apply X
        · apply div_nonneg <;> simp
    simp [sens_cov_τ, sens_cov_vk]
    ring_nf
    rw [InvolutiveInv.inv_inv]
    rw [Hε]
    conv =>
      lhs
      enter [2, 1]
      rw [mul_comm]
    rw [<- add_mul]
    rw [<- add_mul]
    conv =>
      lhs
      enter [1, 1]
      rw [<- (one_mul (ε₁.val.cast))]
    rw [<- add_mul]
    repeat rw [div_eq_mul_inv]
    simp
    rw [one_add_one_eq_two]
    ring_nf
    rfl
