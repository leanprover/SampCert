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


lemma exactDiffSum_neighbours {l₁ l₂ : List ℕ} (i : ℕ) (HN : Neighbour l₁ l₂) :
    (exactDiffSum i l₁ - exactDiffSum i l₂).natAbs ≤ 1 := by
  cases HN
  · rename_i A B v H1 H2
    subst H1 H2
    unfold exactDiffSum
    unfold exactClippedSum
    rw [Int.sub_sub]
    repeat rw [List.map_append]
    generalize HV1 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n i)) A) = V1
    generalize HV2 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n i)) B) = V2
    generalize HV3 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n (i + 1))) A) = V3
    generalize HV4 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n (i + 1))) B) = V4
    simp
    -- Doable
    sorry
  · sorry
  · sorry


set_option pp.coercions false

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

  -- Eliminate the first n-1 random choices by cancellation
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

    -- Unfold defs
    simp [privNoiseZero, DPSystem.noise]

    -- Change of variables
    let cov_Δvk : ℤ := exactDiffSum 0 l₁ - exactDiffSum 0 l₂
    conv =>
      enter [2, 2]
      rw [tsum_shift_lemma _ cov_Δvk]
      dsimp [cov_Δvk]

    -- Simplify COV and all the coercions
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

    -- Simplify noise expression
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
    rw [← natAbs_to_abs]
    suffices ((exactDiffSum (OfNat.ofNat 0) l₁ - exactDiffSum (OfNat.ofNat 0) l₂).natAbs ≤ 1) by
      cases Classical.em ((exactDiffSum (OfNat.ofNat 0) l₁ - exactDiffSum (OfNat.ofNat 0) l₂) = 0)
      · simp_all
      apply (Real.natCast_le_toNNReal ?G1).mp
      case G1 =>
        simp_all only [ne_eq, natAbs_eq_zero, not_false_eq_true]
      simp
      apply le_trans this
      simp
    apply (exactDiffSum_neighbours _ HN)



  sorry
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
