/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.DP
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Prod
import Mathlib.Logic.IsEmpty

/-!
# Pure Composition in Pure Differential Privacy

This file proves a pure DP privacy bound on composed independent queries.
-/

noncomputable section

open Classical Set

variable [Hu : Nonempty U]

namespace SLang

/--
Pure DP privacy bound for ``privCompose``.
-/
theorem privCompose_DP_bound {nq1 : Mechanism T U} {nq2 : Mechanism T V} {ε₁ ε₂ : ℝ} (h1 : PureDP nq1 ε₁)  (h2 : PureDP nq2 ε₂) :
  DP (privCompose nq1 nq2) (ε₁ + ε₂) := by
  simp [PureDP] at *
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x y
  replace h1a := h1 l₁ l₂ neighbours x
  replace h2a := h2 l₁ l₂ neighbours y
  simp [privCompose]
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
      cases (Classical.em (((nq1 l₂) x = 0) ∨ ((nq2 l₂) y = 0)))
      · rename_i Hzero
        cases Hzero
        · rename_i Hz'
          cases (Classical.em (nq1 l₁ x = 0))
          · rename_i Hz''
            simp_all
          · rename_i Hz''
            exfalso
            simp_all
            simp [division_def] at h1a
            rw [ENNReal.mul_top Hz''] at h1a
            simp_all
        · cases (Classical.em (nq2 l₁ y = 0))
          · rename_i Hz''
            simp_all
          · rename_i Hz''
            exfalso
            simp_all
            simp [division_def] at h2a
            rw [ENNReal.mul_top Hz''] at h2a
            simp_all
      · have A : nq1 l₁ x * nq2 l₁ y / (nq1 l₂ x * nq2 l₂ y) = (nq1 l₁ x / nq1 l₂ x) * (nq2 l₁ y / nq2 l₂ y) := by
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
        rw [ENNReal.ofReal_mul (Real.exp_nonneg ε₁)]
    . aesop
    . aesop
  . aesop
  . aesop


/--
Pure DP satisfies pure differential privacy.
-/
theorem privCompose_DP (nq1 : Mechanism T U) (nq2 : Mechanism T V) (ε₁ ε₂ : ℝ) (h : PureDP nq1 ε₁)  (h' : PureDP nq2 ε₂) :
  PureDP (privCompose nq1 nq2) (ε₁ + ε₂) := by
  simp [PureDP] at *
  apply privCompose_DP_bound h h'

end SLang
