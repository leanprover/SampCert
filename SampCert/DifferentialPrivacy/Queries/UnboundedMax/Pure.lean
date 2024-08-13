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

  -- -- Execute the deterministic part
  -- simp [privMax_presample_sep]
  -- rw [<- ENNReal.tsum_mul_left]
  -- apply ENNReal.tsum_le_tsum
  -- intro history
  -- conv =>
  --   enter [2]
  --   rw [<- mul_assoc]
  --   enter [1]
  --   rw [mul_comm]
  -- conv =>
  --   enter [2]
  --   rw [mul_assoc]
  -- apply (ENNReal.mul_le_mul_left ?G1 ?G2).mpr
  -- case G1 =>
  --   -- privMax_presample_sep_det can sample all n-length histories
  --   -- Could also reduce this away by conditioning if an issue
  --   sorry
  -- case G2 =>
  --   -- wf
  --   sorry
  -- rcases history with ⟨ history, Hhistory ⟩
  -- simp only []


  -- -- The n = 0 case is special
  -- -- We can't define G when n = 0 (there is nothing to take the max over)
  -- -- So we need a different change of variables, I think
  -- cases n
  -- · simp_all
  --   conv =>
  --     congr
  --     · enter [1, a, 2, 1, b]
  --       simp [privMax_eval_alt_cond]
  --       simp [G]
  --     · enter [2, 1, a, 2, 1, b]
  --       simp [privMax_eval_alt_cond]
  --       simp [G]

  --   -- Can get away with no COV for τ, I think



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
