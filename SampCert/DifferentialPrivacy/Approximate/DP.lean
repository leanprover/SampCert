/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Neighbours
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP' (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) ≤ δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0)

def ApproximateDP (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  DP' m ε δ
 ∧ NonZeroNQ m

theorem foo (m : Mechanism T U) (ε : ℝ) (h : DP m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [DP] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h l₁ l₂ neighs S
  rw [ENNReal.div_le_iff_le_mul sorry sorry] at h
  apply le_trans h
  simp

theorem bar (m : Mechanism T U) (ε : ℝ) (h : zCDPBound m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [zCDPBound] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h



def DP_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ x : U,
  (m l₁ x) ≤ δ + ENNReal.ofReal (Real.exp ε) * (m l₂ x)

theorem singleton_to_event (m : Mechanism T U) (ε : ℝ) (δ : NNReal) (h : DP_singleton m ε δ) :
  DP m ε δ := by
  simp [DP]
  simp [DP_singleton] at h
  intros l₁ l₂ h1 S
  replace h1 := h l₁ l₂ h1
  have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0)  ≤ δ + ENNReal.ofReal ε.exp * (if x ∈ S then m l₂ x else 0) := by
    aesop
  have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
    aesop
  have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
    intro b
    right
    simp
    exact Real.exp_pos ε
  have E := fun x : U => (A x)
  have F := ENNReal.tsum_le_tsum E
  apply le_trans F


  rw [ENNReal.tsum_mul_left] at F
  rw [← ENNReal.div_le_iff_le_mul] at F
  . clear h1 A B C D
    trivial
  . aesop
  . right
    simp
    exact Real.exp_pos ε

theorem event_to_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) (h : DP m ε δ) :
  DP_singleton m ε δ := by
  simp [DP_singleton]
  simp [DP] at h
  intros l₁ l₂ h1 x
  replace h1 := h l₁ l₂ h1 {x}
  simp at h1
  rw [tsum_eq_single x] at h1
  . simp at h1
    rw [tsum_eq_single x] at h1
    . simp at h1
      trivial
    . aesop
  . aesop

theorem event_eq_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) :
  DP m ε δ ↔ DP_singleton m ε δ := by
  constructor
  . apply event_to_singleton
  . apply singleton_to_event

end SLang
