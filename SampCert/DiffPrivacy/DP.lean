/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import SampCert.DiffPrivacy.ConcentratedBound
import SampCert.SLang
import SampCert.Samplers.GaussianGen.Basic
import SampCert.DiffPrivacy.Neighbours
import SampCert.DiffPrivacy.Sensitivity

noncomputable section

open Classical Nat Int Real ENNReal

def DP (q : List T → SLang U) (ε : ℝ) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  RenyiDivergence (q l₁) (q l₂) α ≤ (1/2) * ε ^ 2 * α

namespace SLang

def NoisedQuery (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  DiscreteGaussianGenSample (Δ * ε₂) ε₁ (query l)

theorem NoisedQueryDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (NoisedQuery query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
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
    rw [_root_.mul_pos_iff]
    left
    simp

def Compose (nq1 nq2 : List T → SLang ℤ) (l : List T) : SLang (ℤ × ℤ) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

theorem DPCompose {nq1 nq2 : List T → SLang ℤ} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : DP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : DP nq2 ((ε₃ : ℝ) / ε₄)) :
  DP (Compose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [Compose, RenyiDivergence, DP]
  intro α h3 l₁ l₂ h4
  simp [DP] at h1 h2
  replace h1 := h1 α h3 l₁ l₂ h4
  replace h2 := h2 α h3 l₁ l₂ h4
  simp [RenyiDivergence] at h1 h2
  rw [tsum_prod' ENNReal.summable (fun b : ℤ => ENNReal.summable)]
  . simp
    have A : ∀ b c : ℤ, ∀ l : List T, (∑' (a : ℤ), nq1 l a * ∑' (a_1 : ℤ), if b = a ∧ c = a_1 then nq2 l a_1 else 0) = nq1 l b * nq2 l c := by
      sorry
    conv =>
      left
      right
      right
      right
      right
      intro b
      right
      intro c
      rw [A]
      rw [A]
      rw [ENNReal.mul_rpow_of_ne_zero sorry sorry]
      rw [ENNReal.mul_rpow_of_ne_zero sorry sorry]
      rw [mul_assoc]
      right
      rw [mul_comm]
      rw [mul_assoc]
      right
      rw [mul_comm]
    conv =>
      left
      right
      right
      right
      right
      intro b
      right
      intro c
      rw [← mul_assoc]
    conv =>
      left
      right
      right
      right
      right
      intro b
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
    rw [ENNReal.toReal_mul]
    rw [Real.log_mul]
    . rw [mul_add]
      have D := _root_.add_le_add h1 h2
      apply le_trans D
      rw [← add_mul]
      rw [mul_le_mul_iff_of_pos_right]
      . rw [← mul_add]
        rw [mul_le_mul_iff_of_pos_left]
        . ring_nf
          simp
        . sorry -- easy
      . sorry -- easy
    . sorry -- ≠ 0 , not obvious
    . sorry -- ≠ 0

def PostProcess (nq : List T → SLang U) (pp : U → ℤ) (l : List T) : SLang ℤ := do
  let A ← nq l
  return pp A

theorem DPPostProcess {nq : List T → SLang U} {ε₁ ε₂ : ℕ+} (h : DP nq ((ε₁ : ℝ) / ε₂)) (pp : U → ℤ)  :
  DP (PostProcess nq pp) ((ε₁ : ℝ) / ε₂) := by
  simp [PostProcess, DP, RenyiDivergence]
  intro α h1 l₁ l₂ h2
  simp [DP, RenyiDivergence] at h
  replace h := h α h1 l₁ l₂ h2
  sorry

end SLang
