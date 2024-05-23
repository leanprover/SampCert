/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.DifferentialPrivacy.Queries.Count.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

open Classical Nat Int Real Rat

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

theorem div_surjective :
  Function.Surjective fun a : ℤ × ℤ => (a.1 : ℚ) / (a.2 : ℚ) := by
  unfold Function.Surjective
  intro b
  cases b
  rename_i n d h1 h2
  simp
  exists n
  exists d
  rw [intCast_div_eq_divInt]
  simp [mkRat, h1, Rat.normalize, h2]

theorem budget_split (ε₁ ε₂ : ℕ+) :
  (ε₁ : ℝ) / (ε₂ : ℝ) = (ε₁ : ℝ) / ((2 * ε₂) : ℕ+) + (ε₁ : ℝ) / ((2 * ε₂) : ℕ+) := by
  field_simp
  ring_nf

theorem BoundedSumQueryDP (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (NoisedBoundedAvgQuery U ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  unfold NoisedBoundedAvgQuery
  simp
  apply dps.postprocess_prop div_surjective
  rw [budget_split]
  apply dps.compose_prop
  . apply NoisedBoundedSumQueryDP
  . apply NoisedCountingQueryDP

end SLang
