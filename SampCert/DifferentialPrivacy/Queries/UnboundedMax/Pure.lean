/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Properties
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` pure DP

This file proves pure DP for privMax.

Follows the proof given for Algorithm 1 pp. 57 "The Sparse Vector Technique"
in "The Algorithmic Foundations of Differential Privacy", Dwork & Roth.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

-- Enables the change of variables in privMax_reduct_PureDP
/--
Sums over ℤ can be shifted by any any amount
-/
lemma tsum_shift_lemma (f : ℤ -> ENNReal) (Δ : ℤ) : ∑'(t : ℤ), f t = ∑'(t : ℤ), f (t + Δ) := by
  apply tsum_eq_tsum_of_bij (fun z => z + Δ) <;> simp [Function.Injective]
  intro x Hf
  exists (x - Δ)
  simp
  trivial


/--
Reduced, history-aware, presampled, separated program  is (ε₁/ε₂)-DP
-/
lemma privMax_reduct_PureDP {ε₁ ε₂ : ℕ+} : PureDP (@privMax_presample_PMF PureDPSystem ε₁ ε₂) (ε₁ / ε₂) := by
  -- Transform into inequality
  simp [PureDP]
  apply singleton_to_event
  simp [DP_singleton]
  intro l₁ l₂ HN n
  apply (ENNReal.div_le_iff_le_mul ?G1 ?G2).mpr
  case G1 =>
    right
    exact ENNReal.ofReal_ne_top
  case G2 =>
    left
    apply PMF.apply_ne_top
  unfold privMax_presample_PMF
  simp [DFunLike.coe, PMF.instFunLike]

  -- Eliminate the deterministic part by cancellation
  simp [privMax_presample, gen_sv_presampled]
  conv =>
    enter [1, 1, τ]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, vk]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
  conv =>
    enter [1]
    rw [ENNReal.tsum_comm]
    enter [1, vk]
    rw [ENNReal.tsum_mul_left]
  conv =>
    enter [2, 2, 1, τ]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, vk]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
  conv =>
    enter [2, 2]
    rw [ENNReal.tsum_comm]
    enter [1, vk]
    rw [ENNReal.tsum_mul_left]
  conv =>
    enter [2]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, τ]
    rw [<- mul_assoc]
    rw [mul_comm (ENNReal.ofReal _)]
    rw [mul_assoc]
  apply ENNReal.tsum_le_tsum
  intro history
  apply mul_le_mul'
  · rfl

  -- Change of variables will not work for empty history as it uses G explicitly
  cases history
  · simp [privMax_eval_alt_cond]
    unfold G

    -- Cancel τ (could be a mistake)
    conv =>
      enter [2]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, vk]
      rw [mul_comm]
      rw [mul_assoc]
      enter [2]
      rw [mul_comm]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply mul_le_mul'
    · rfl

    -- Unfold defs,
    simp [privNoiseZero, DPSystem.noise]
    have Hsens : @sensitivity ℕ (fun x => 0) ↑1 := by
      unfold sensitivity
      simp
    let noise_dp := @privNoisedQueryPure_DP_bound ℕ (fun _ => 0) 1 ε₁ (4 * ε₂) Hsens
    apply (event_eq_singleton  _ _).mp at noise_dp
    unfold DP_singleton at noise_dp
    have noise_dp' := noise_dp _ _ HN
    clear noise_dp



    -- Change of variables
    let cov_Δvk : ℤ := exactDiffSum 0 l₁ - exactDiffSum 0 l₂
    conv =>
      enter [2, 2]
      rw [tsum_shift_lemma _ cov_Δvk]
      dsimp [cov_Δvk]

    -- Simplify COV and all these coercions
    have Hite_eq1 (a : ℤ) D :
      (@ite _
        (WithBot.some τ ≤
          (WithBot.some (SLang.exactDiffSum 0 l₂) +
          ((WithBot.some a) + (WithBot.some ((SLang.exactDiffSum 0 l₁) - (SLang.exactDiffSum 0 l₂))))))
        D (probPure n) 0) n =
        (if (τ ≤ SLang.exactDiffSum 0 l₁ + a) then (probPure n) else 0) n := by
      sorry
    have Hite_eq2 (a : ℤ) D :
      (@ite _
        (WithBot.some τ ≤
          (WithBot.some (SLang.exactDiffSum 0 l₁) + (WithBot.some a)))
        D (probPure n) 0) n =
        (if (τ ≤ SLang.exactDiffSum 0 l₁ + a) then (probPure n) else 0) n := by
      sorry
    conv =>
      enter [2, 2, 1, a, 2]
      rw [Hite_eq1]
    clear Hite_eq1
    conv =>
      enter [1, 1, a]
      rw [Hite_eq2]
    clear Hite_eq2

    -- Simplify the inequalities and split on the conditional
    conv =>
      enter [2]
      rw [<- ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro v
    split <;> try simp

    -- Seems like noise_dp is not what I want actually.
    -- Probably can derive the inequality directly from the Laplace distribution
    clear noise_dp'


    simp [privNoisedQueryPure]
    simp [DiscreteLaplaceGenSamplePMF]
    simp only [DFunLike.coe, PMF.instFunLike]
    simp [DiscreteLaplaceGenSample_apply]

    -- Coalesce the ENNReal.ofReals
    rw [<- ENNReal.ofReal_mul ?G1]
    case G1 => sorry
    apply ENNReal.ofReal_le_ofReal

    -- Cancel constant factor terms
    conv =>
      enter [2]
      rw [mul_comm]
      rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ ?G1
    case G1 => sorry
    skip
    rw [← exp_add]
    apply Real.exp_le_exp.mpr
    simp only [le_neg_add_iff_add_le, add_neg_le_iff_le_add]

    -- Move factor to other side
    apply div_le_of_nonneg_of_le_mul ?G1 ?G2
    case G1 => sorry
    case G2 => sorry

    -- Transitivity with triangle inequality on LHS
    apply le_trans (abs_add _ _)

    -- Simplify fractions on RHS
    simp [add_mul]
    conv =>
      enter [2, 1]
      rw [mul_comm]
      rw [division_def]
      rw [division_def]
      repeat rw [mul_assoc]
      enter [2]
      rw [mul_comm]
      repeat rw [<- mul_assoc]
      simp
    simp
    rw [add_comm]
    apply _root_.add_le_add _ (by rfl)

    -- Suffices to show that ExactDiffSum is le 1 on neighbours

    sorry


  sorry
    -- rw [<- ENNReal.tsum_mul_left]
    -- apply ENNReal.tsum_le_tsum
    -- intro τ
    -- conv =>
    --   rhs
    --   rw [mul_comm]
    --   rw [mul_assoc]
    -- apply (ENNReal.mul_le_mul_left ?G1 ?G2).mpr
    -- case G1 => sorry
    -- case G2 => sorry
    -- conv =>
    --   rhs
    --   rw [mul_comm]
    -- rw [<- ENNReal.tsum_mul_left]
    -- apply ENNReal.tsum_le_tsum
    -- intro v0
    -- conv =>
    --   rhs
    --   rw [mul_comm]
    --   rw [mul_assoc]
    -- apply (ENNReal.mul_le_mul_left ?G1 ?G2).mpr
    -- case G1 => sorry
    -- case G2 => sorry
    -- simp [privMax_eval_alt_cond]
  -- rename_i N

  -- -- Define the shift for the change of variables
  -- -- Might have these backwards
  -- let cov_Δτ : ℤ := G l₂ ⟨ history, by linarith ⟩ - G l₁ ⟨ history, by linarith ⟩
  -- let cov_Δvk  : ℤ := G l₂ ⟨ history, by linarith ⟩ - G l₁ ⟨ history, by linarith ⟩ + exactDiffSum N l₁ - exactDiffSum N l₂
  -- conv =>
  --   lhs
  --   rw [tsum_shift_lemma _ cov_Δτ]
  --   enter [1, t]
  --   rw [tsum_shift_lemma _ cov_Δvk]

  -- sorry



/--
privMax is (ε₁/ε₂)-DP
-/
lemma privMax_PureDP {ε₁ ε₂ : ℕ+} : PureDP (@privMaxPMF PureDPSystem ε₁ ε₂) (ε₁ / ε₂) := by
  -- apply DPSystem_mech_prop_ext _ _ _ privMax_reduct_PureDP
  -- apply funext
  -- intro l
  -- unfold privMax_presample_sep_PMF
  -- unfold privMaxPMF
  -- congr
  sorry
  -- rw [privMax_reduction_0]
  -- rw [privMax_reduction_1]
  -- rw [privMax_reduction_2]
  -- rw [privMax_reduction_3]

end SLang
