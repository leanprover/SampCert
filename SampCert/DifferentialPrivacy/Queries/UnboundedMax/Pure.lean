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
