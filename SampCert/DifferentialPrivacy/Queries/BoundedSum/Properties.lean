/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Code

open Classical Nat Int Real

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

theorem BoundedSumQuerySensitivity (U : ℕ+) : sensitivity (BoundedSumQuery U) U := by
  simp [sensitivity, BoundedSumQuery]
  intros l₁ l₂ H
  have A : ∀ n : ℕ, (@min ℤ instMin (n : ℤ) (U : ℤ) = n) ∨ (@min ℤ instMin n U = U) := by
    intro n
    simp
    exact Nat.le_total n ↑U
  cases H
  . rename_i l l' n h1 h2
    subst h1 h2
    simp
    cases A n
    . rename_i h
      rw [h]
      simp at *
      trivial
    . rename_i h
      rw [h]
      simp
  . rename_i l n l' h1 h2
    subst h1 h2
    simp
    cases A n
    . rename_i h
      rw [h]
      simp at *
      trivial
    . rename_i h
      rw [h]
      simp
  . rename_i l n l' m h1 h2
    subst h1 h2
    simp
    cases A n
    . rename_i h
      cases A m
      . rename_i h'
        rw [h, h']
        simp at *
        apply Int.natAbs_coe_sub_coe_le_of_le h h'
      . rename_i h'
        rw [h, h']
        simp at *
        apply Int.natAbs_coe_sub_coe_le_of_le h le_rfl
    . rename_i h
      cases A m
      . rename_i h'
        rw [h, h']
        simp at *
        apply Int.natAbs_coe_sub_coe_le_of_le le_rfl h'
      . rename_i h'
        rw [h, h']
        simp at *

theorem NoisedBoundedSumQueryDP (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (NoisedBoundedSumQuery U ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  apply dps.noise_prop
  apply BoundedSumQuerySensitivity

end SLang
