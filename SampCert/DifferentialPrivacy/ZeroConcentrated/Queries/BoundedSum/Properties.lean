/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Mechanism.Mechanism
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order
import SampCert.DifferentialPrivacy.ZeroConcentrated.Queries.BoundedSum.Code

open Classical Nat Int Real

noncomputable section

namespace SLang

theorem BoundedSumQuerySensitivity (U : ℕ+) : sensitivity (BoundedSumQuery U) U := by
  simp [sensitivity, BoundedSumQuery]
  intros l₁ l₂ H
  have A : ∀ n : ℕ, (@min ℤ instMinInt (n : ℤ) (U : ℤ) = n) ∨ (@min ℤ instMinInt n U = U) := by
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

def NoisedBoundedSumQuery (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℤ := do
  NoisedQuery (BoundedSumQuery U) U ε₁ ε₂ l

theorem NoisedBoundedSumQueryDP (U : ℕ+) (ε₁ ε₂ : ℕ+) : DP (NoisedBoundedSumQuery U ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  apply NoisedQueryDP
  apply BoundedSumQuerySensitivity

theorem NoisedBoundedSumQuery_NonZeroNQ (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  @NonZeroNQ ℕ ℤ (NoisedBoundedSumQuery U ε₁ ε₂) := by
  apply NoisedQuery_NonZeroNQ

theorem NoisedBoundedSumQuery_NonTopNQ (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  @NonTopNQ ℕ ℤ (NoisedBoundedSumQuery U ε₁ ε₂) := by
  apply NoisedQuery_NonTopNQ

theorem NoisedBoundedSumQuery_NonTopRDNQ (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  @NonTopRDNQ ℕ ℤ (NoisedBoundedSumQuery U ε₁ ε₂) := by
  apply NoisedQuery_NonTopRDNQ

theorem NoisedBoundedSumQuery_NonTopSum (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  @NonTopSum ℕ ℤ (NoisedBoundedSumQuery U ε₁ ε₂) := by
  apply NoisedQuery_NonTopSum

end SLang
