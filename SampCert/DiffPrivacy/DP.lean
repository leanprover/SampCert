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

open Classical Nat Int Real

def DP (q : List T → SLang U) (ε₁ ε₂ : ℕ+) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  RenyiDivergence
    (fun x : U => (q l₁ x).toReal)
    (fun x : U => (q l₂ x).toReal) α
    ≤ (1/2) * (ε₁ / ε₂)^2 * α

namespace SLang

def NoisedQuery (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  DiscreteGaussianGenSample (Δ * ε₂) ε₁ (query l)

theorem NoisedQueryDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
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

def Compose (nq1 nq2 : List T → SLang ℤ) (l : List T) : SLang (ℤ × ℤ) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

def RAdd (ε₁ ε₂ ε₃ ε₄ : ℕ+) : ℕ+ × ℕ+ :=
  (ε₁ * ε₃ + ε₂ * ε₄,ε₃ * ε₄)

theorem DPCompose (nq1 nq2 : List T → SLang ℤ) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h1 : DP nq1 ε₁ ε₂)  (h2 : DP nq2 ε₃ ε₄) :
  DP (Compose nq1 nq2) (RAdd ε₁ ε₂ ε₃ ε₄).1 (RAdd ε₁ ε₂ ε₃ ε₄).2 := by
  simp [Compose, RAdd, RenyiDivergence, DP]
  intro α h1 l₁ l₂ h2
  rw [tsum_prod']
  . simp
    sorry
  . sorry
  . sorry

end SLang
