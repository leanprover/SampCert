/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Neighbours
import SampCert.DifferentialPrivacy.Sensitivity

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP (m : Mechanism T U) (ε : ℝ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) / (∑' x : U, if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal (Real.exp ε)

def PureDP (m : Mechanism T U) (ε : ℝ) : Prop :=
  DP m ε
 ∧ NonZeroNQ m
 -- ∧ NonTopSum m

def DP_singleton (m : Mechanism T U) (ε : ℝ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ x : U,
  (m l₁ x) / (m l₂ x) ≤ ENNReal.ofReal (Real.exp ε)

theorem singleton_to_event (m : Mechanism T U) (ε : ℝ) (h : DP_singleton m ε) :
  DP m ε := by
  simp [DP]
  simp [DP_singleton] at h
  intros l₁ l₂ h1 S
  replace h1 := h l₁ l₂ h1
  have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0) / (if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal ε.exp := by
    aesop
  have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
    aesop
  have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
    intro b
    right
    simp
    exact Real.exp_pos ε
  have D := fun { x : U } => @ENNReal.div_le_iff_le_mul (if x ∈ S then m l₁ x else 0) (if x ∈ S then m l₂ x else 0) (ENNReal.ofReal ε.exp) (B (if x ∈ S then m l₂ x else 0)) (C (if x ∈ S then m l₂ x else 0))
  have E := fun x : U => D.1 (A x)
  have F := ENNReal.tsum_le_tsum E
  rw [ENNReal.tsum_mul_left] at F
  rw [← ENNReal.div_le_iff_le_mul] at F
  . clear h1 A B C D
    trivial
  . aesop
  . right
    simp
    exact Real.exp_pos ε

theorem event_to_singleton (m : Mechanism T U) (ε : ℝ) (h : DP m ε) :
  DP_singleton m ε := by
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

theorem event_eq_singleton (m : Mechanism T U) (ε : ℝ) :
  DP m ε ↔ DP_singleton m ε := by
  constructor
  . apply event_to_singleton
  . apply singleton_to_event

end SLang
