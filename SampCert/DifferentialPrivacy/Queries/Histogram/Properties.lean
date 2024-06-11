/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.Histogram.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privHistogram`` Properties

This file proves abstract differential privacy for the noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

variable (num_bins : ℕ)
variable (B : Bins T num_bins)

-- def exactBinCount (b : Fin num_bins) (l : List T) : ℤ :=
--   List.length (List.filter (fun v => B.bin v = b) l)

/-
exactBinCount is 1-sensitive
-/
theorem exactBinCount_sensitivity (b : Fin num_bins) : sensitivity (exactBinCount num_bins B b) 1 := by
  rw [sensitivity]
  intros l₁ l₂ HN
  cases HN
  · rename_i l₁' l₂' v' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v' l₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v₁' l₂' v₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    -- There has to be a better way
    cases (Classical.em (B.bin v₁' = b)) <;> cases (Classical.em (B.bin v₂' = b))
    all_goals (rename_i Hrw1 Hrw2)
    all_goals (simp [Hrw1, Hrw2])


/-
The histogram satisfies the DP property.
-/

-- Proof: It's a composition of B independent, 1-sensitive, ε/B-DP queries


/-
Getting the max threhsoldeded bin satisfies the DP property
-/

-- Proof: Postcomposition

end SLang
