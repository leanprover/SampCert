/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DiffPrivacy.DP
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order

open Classical Nat Int Real

noncomputable section

namespace SLang

def BoundedSumQuery (U : ℕ+) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n U)) l)

-- theorem natAbs1 {n : ℕ} {x : ℤ} (h : n ≤ x) :
--   n ≤ natAbs x := by
--   cases x
--   . rename_i m
--     simp
--     exact Int.ofNat_le.mp h
--   . rename_i m
--     simp
--     have A : -[m+1] < 0 := negSucc_lt_zero m
--     have B : n < (0 : ℤ) := by
--       apply Int.lt_of_le_of_lt h A
--     contradiction

-- def maxBoundPos (L U : ℤ) (h : L < U) :
--   0 < max (Int.natAbs L) (Int.natAbs U) := by
--   have A : ¬ (L = 0 ∧ U = 0) := by
--     by_contra h'
--     cases h'
--     rename_i h1 h2
--     subst h1 h2
--     contradiction
--   simp at A
--   have B : L = 0 ∨ L ≠ 0 := by exact eq_or_ne L 0
--   cases B
--   . rename_i h'
--     subst h'
--     simp at A
--     simp
--     trivial
--   . rename_i h'
--     simp
--     left
--     trivial

-- def maxBound (L U : ℤ) (h : L < U) : ℕ+ :=
--   ⟨ max (Int.natAbs L) (Int.natAbs U) , maxBoundPos L U h ⟩

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
