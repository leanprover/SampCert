/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

-- Data : sorted list of integers
-- integer can be added, removed, modified

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import SampCert.DiffPrivacy.ConcentratedBound
import SampCert.SLang
import SampCert.Samplers.GaussianGen.Basic

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}

inductive Neighbour (l₁ l₂ : List ℕ) : Prop where
  | Addition : l₁ = a ++ b → l₂ = a ++ [n] ++ b → Neighbour l₁ l₂
  | Deletion : l₁ = a ++ [n] ++ b → l₂ = a ++ b → Neighbour l₁ l₂
  | Update : l₁ = a ++ [n] ++ b → l₂ = a ++ [m] ++ b -> Neighbour l₁ l₂

def sensitivity (q : List ℕ → ℤ) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂ : List ℕ, Neighbour l₁ l₂ → Int.natAbs (q l₁ - q l₂) ≤ Δ

def DP (q : List ℕ → SLang ℤ) (ε₁ ε₂ : ℕ+) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List ℕ, Neighbour l₁ l₂ →
  RenyiDivergence
    (fun x : ℤ => (q l₁ x).toReal)
    (fun x : ℤ => (q l₂ x).toReal) α
    ≤ (1/2) * (ε₁ / ε₂)^2 * α

def NoisedQuery (query : List ℕ → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℤ := do
  DiscreteGaussianGenSample (Δ * ε₂) ε₁ (query l)

theorem NoisedQueryDP (query : List ℕ → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (NoisedQuery query Δ ε₁ ε₂) ε₁ ε₂ := by
  simp [DP, NoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @DiscreteGaussianGenSampleZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A
  replace bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  ring_nf
  simp
  conv =>
    left
    left
    right
    rw [mul_pow]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [← mul_assoc]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [← mul_assoc]
  simp only [inv_pow]
  rw [mul_inv_le_iff']
  . have A : (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) ≤ (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) := le_refl (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹)
    have B : 0 ≤ (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) := by
      simp
      apply @le_trans ℝ _ 0 1 α (instStrictOrderedCommRingReal.proof_3) (le_of_lt h1)
    apply mul_le_mul A _ _ B
    . apply sq_le_sq.mpr
      simp only [abs_cast]
      rw [← Int.cast_sub]
      rw [← Int.cast_abs]
      apply Int.cast_le.mpr
      rw [← Int.natCast_natAbs]
      apply Int.ofNat_le.mpr
      trivial
    . apply sq_nonneg
  . rw [pow_two]
    rw [mul_pos_iff]
    left
    simp

def CountingQuery (l : List ℕ) : ℤ := List.length l

theorem CountingQuery1Sensitive :
  sensitivity CountingQuery 1 := by
  simp [CountingQuery, sensitivity]
  intros l₁ l₂ H
  cases H
  . rename_i a b n h1 h2
    subst h1 h2
    simp
  . rename_i a b n h1 h2
    subst h1 h2
    simp
  . rename_i a n b m h1 h2
    subst h1 h2
    simp

example (ε₁ ε₂ : ℕ+) : DP (NoisedQuery CountingQuery 1 ε₁ ε₂) ε₁ ε₂ := by
  apply NoisedQueryDP
  apply CountingQuery1Sensitive

example (clip : ℕ+) : sensitivity (fun l : List ℕ => List.sum (List.map (fun n : ℕ => if n > clip then clip else n) l)) clip := by
  simp [sensitivity]
  intros l₁ l₂ H
  cases H
  . rename_i a b n h1 h2
    subst h1 h2
    simp
    split
    . rename_i h3
      simp
    . rename_i h3
      simp at h3
      simpa
  . rename_i a b n h1 h2
    subst h1 h2
    simp
    split
    . rename_i h3
      simp
    . rename_i h3
      simp at h3
      simpa
  . rename_i a n b m h1 h2
    subst h1 h2
    simp
    split
    . split
      . rename_i h3 h4
        simp
      . rename_i h3 h4
        simp at h4
        sorry -- OK
    . split
      . rename_i h3 h4
        simp at h3
        sorry -- OK
      . rename_i h3 h4
        simp at h3 h4
        sorry -- OK

end SLang
