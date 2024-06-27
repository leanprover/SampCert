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

theorem PureDP_PostProcess' {nq : Mechanism T U} {ε₁ ε₂ : ℕ+} (h : PureDP nq ((ε₁ : ℝ) / ε₂)) (f : U → V) :
  DP (privPostProcess nq f) (((ε₁ : ℝ) / ε₂)) := by
  simp [PureDP] at *
  rcases h with ⟨ha, _⟩
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x
  replace ha := ha l₁ l₂ neighbours
  simp [privPostProcess]
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum _ ENNReal.summable (by aesop)
  intro i
  split
  . rename_i h
    subst h
    refine (ENNReal.div_le_iff_le_mul ?inl.hb0 ?inl.hbt).mp (ha i)
    . aesop
    . right
      simp
      exact Real.exp_pos ((ε₁: ℝ) / ε₂)
  . simp

theorem PureDP_PostProcess {f : U → V} (sur : Function.Surjective f) (nq : Mechanism T U) (ε₁ ε₂ : ℕ+) (h : PureDP nq ((ε₁ : ℝ) / ε₂)) :
  PureDP (privPostProcess nq f) (((ε₁ : ℝ) / ε₂)) := by
  simp [PureDP] at *
  have hc := h
  rcases h with ⟨ _ , h2 ⟩
  constructor
  . apply PureDP_PostProcess' hc
  . apply privPostProcess_NonZeroNQ h2 sur

end SLang
