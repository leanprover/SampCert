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

/--
Reduced, history-aware, presampled, separated program  is (ε₁/ε₂)-DP
-/
lemma privMax_reduct_PureDP {ε₁ ε₂ : ℕ+} : PureDP (@privMax_presample_sep_PMF PureDPSystem ε₁ ε₂) (ε₁ / ε₂) := by
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
  unfold privMax_presample_sep_PMF
  simp [DFunLike.coe, PMF.instFunLike]

  -- Execute the deterministic part
  simp [privMax_presample_sep]
  rw [<- ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro history
  conv =>
    enter [2]
    rw [<- mul_assoc]
    enter [1]
    rw [mul_comm]
  conv =>
    enter [2]
    rw [mul_assoc]
  apply (ENNReal.mul_le_mul_left ?G1 ?G2).mpr
  case G1 =>
    -- privMax_presample_sep_det can sample all n-length histories
    -- Could also reduce this away by conditioning if an issue
    sorry
  case G2 =>
    -- wf
    sorry
  rcases history with ⟨ history, Hhistory ⟩
  simp only []

  -- Now, history is determined, and the system involves the remaining two random events

  -- Do the change of variables (on the LHS)
  -- Either change n+1 -> n in reduct or postprocess with -1 (hard to tell which is right)






  -- I wonder if I could get away without the separation lemmas. Seems hard, but I
  -- might be able to do this cancellation (N-1) times right here.
  --
  -- Work on the separation proof some more. If it's way too hard for some reason,
  -- can explore this instead. My intuition says it'll be roughly the same difficulty.
  sorry



/--
privMax is (ε₁/ε₂)-DP
-/
lemma privMax_PureDP {ε₁ ε₂ : ℕ+} : PureDP (@privMaxPMF PureDPSystem ε₁ ε₂) (ε₁ / ε₂) := by
  apply DPSystem_mech_prop_ext _ _ _ privMax_reduct_PureDP
  apply funext
  intro l
  unfold privMax_presample_sep_PMF
  unfold privMaxPMF
  congr
  rw [privMax_reduction_0]
  rw [privMax_reduction_1]
  rw [privMax_reduction_2]
  rw [privMax_reduction_3]

end SLang
