/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Algebra.Group.Defs
import Init.Data.Int.Order
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Code

/-!
# ``privNoisedBoundedSum`` Properties

This file proves abstract differential privacy for ``privNoisedBoundedSum``.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

/--
Sensitivity of the bounded sum is equal to the bound.
-/
theorem exactBoundedSum_sensitivity (U : ℕ+) : sensitivity (exactBoundedSum U) U := by
  simp [sensitivity, exactBoundedSum]
  intros l₁ l₂ H
  have A : ∀ n : ℕ, (@min ℤ instMin (n : ℤ) (U : ℤ) = n) ∨ (@min ℤ instMin n U = U) := by
    intro n
    simp
    exact Nat.le_total n ↑U
  cases H
  · rename_i l l' n h1 h2
    subst h1 h2
    simp
    cases A n
    · rename_i h
      rw [h]
      simp at *
      trivial
    · rename_i h
      rw [h]
      simp
  · rename_i l n l' h1 h2
    subst h1 h2
    simp
    cases A n
    · rename_i h
      rw [h]
      simp at *
      trivial
    · rename_i h
      rw [h]
      simp

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

/--
The noised bounded sum satisfies the DP property of the DP system.
-/
@[simp]
theorem privNoisedBoundedSum_DP (U : ℕ+) (ε₁ ε₂ : ℕ+) (ε : NNReal) (HP : dpn.noise_priv ε₁ ε₂ ε) :
    dps.prop (privNoisedBoundedSum U ε₁ ε₂) ε := by
  apply dpn.noise_prop HP
  apply exactBoundedSum_sensitivity

end SLang
