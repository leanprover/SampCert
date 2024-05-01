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

def BoundedSumQuery (L U : ℤ) (l : List ℤ) : ℤ :=
  let center := |U - L| / 2
  let L := L - center
  let U := U - center
  let S := List.sum (List.map (fun n : ℤ => max (min (n - center) U) L) l)
  S + center * List.length l

theorem natAbs1 {n : ℕ} {x : ℤ} (h : n ≤ x) :
  n ≤ natAbs x := by
  cases x
  . rename_i m
    simp
    exact Int.ofNat_le.mp h
  . rename_i m
    simp
    have A : -[m+1] < 0 := negSucc_lt_zero m
    have B : n < (0 : ℤ) := by
      apply Int.lt_of_le_of_lt h A
    contradiction

def maxBoundPos (L U : ℤ) (h : L < U) :
  0 < max (Int.natAbs L) (Int.natAbs U) := by
  have A : ¬ (L = 0 ∧ U = 0) := by
    by_contra h'
    cases h'
    rename_i h1 h2
    subst h1 h2
    contradiction
  simp at A
  have B : L = 0 ∨ L ≠ 0 := by exact eq_or_ne L 0
  cases B
  . rename_i h'
    subst h'
    simp at A
    simp
    trivial
  . rename_i h'
    simp
    left
    trivial

def maxBound (L U : ℤ) (h : L < U) : ℕ+ :=
  ⟨ max (Int.natAbs L) (Int.natAbs U) , maxBoundPos L U h ⟩

theorem BoundedSumQuerySensitivity (L U : ℤ) (h : L < U) : sensitivity (BoundedSumQuery L U) (maxBound L U h) := by
  sorry

def NoisedBoundedSumQuery (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) (l : List ℤ) : SLang ℤ := do
  NoisedQuery (BoundedSumQuery L U) (maxBound L U h) ε₁ ε₂ l

theorem NoisedBoundedSumQueryDP (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) : DP (NoisedBoundedSumQuery L U h ε₁ ε₂) ε₁ ε₂ := by
  apply NoisedQueryDP
  apply BoundedSumQuerySensitivity

end SLang
