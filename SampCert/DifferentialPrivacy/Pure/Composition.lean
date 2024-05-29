/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.DP
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Prod

noncomputable section

open Classical Set

namespace SLang

theorem PureDPCompose' {nq1 : Mechanism T U} {nq2 : List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : PureDP nq2 ((ε₃ : ℝ) / ε₄)) :
  DP (Compose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  rcases h1 with ⟨h1a, _⟩
  rcases h2 with ⟨h2a, _⟩
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x y
  replace h1a := h1a l₁ l₂ neighbours x
  replace h2a := h2a l₁ l₂ neighbours y
  simp [Compose]
  conv =>
    left
    congr
    . right
      intro a
      rw [← ENNReal.tsum_mul_left]
    . right
      intro a
      rw [← ENNReal.tsum_mul_left]
  simp
  rw [tsum_tsum_eq_single _ x y]
  . simp
    rw [tsum_tsum_eq_single _ x y]
    . simp
      have A : nq1 l₁ x * nq2 l₁ y / (nq1 l₂ x * nq2 l₂ y) = (nq1 l₁ x / nq1 l₂ x) * (nq2 l₁ y / nq2 l₂ y) := by
        rw [division_def]
        rw [division_def]
        rw [division_def]
        rw [ENNReal.mul_inv]
        . ring_nf
        . aesop
        . aesop
      rw [A]
      have B := mul_le_mul' h1a h2a
      apply le_trans B
      rw [Real.exp_add]
      rw [ENNReal.ofReal_mul (Real.exp_nonneg (↑↑ε₁ / ↑↑ε₂))]
    . aesop
    . aesop
  . aesop
  . aesop

theorem PureDPCompose (nq1 : List T → SLang U) (nq2 : List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : PureDP nq2 ((ε₃ : ℝ) / ε₄)) :
  PureDP (Compose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  have hc := h
  have h'c := h'
  rcases h with ⟨ _ , h2 ⟩
  rcases h' with ⟨ _ , h'2 ⟩
  constructor
  . apply PureDPCompose' hc h'c
  . apply DPCompose_NonZeroNQ h2 h'2

end SLang
