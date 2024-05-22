/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Queries.Count.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

open Classical Nat Int Real

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

def NoisedBoundedAvgQuery' (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang (ℤ × ℤ) :=
  let X := dps.compose (NoisedBoundedSumQuery U ε₁ (2 * ε₂)) (NoisedCountingQuery ε₁ (2 * ε₂))
  dps.postprocess X (fun z => z) l

-- theorem NoisedBoundedAvgQueryIdentical (U : ℕ+) (ε₁ ε₂ : ℕ+) :
--   NoisedBoundedAvgQuery' U ε₁ ε₂ = NoisedBoundedAvgQuery U ε₁ ε₂  := by
--   ext l x
--   simp [NoisedBoundedAvgQuery, NoisedBoundedAvgQuery']

theorem BoundedSumQueryDP (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (NoisedBoundedAvgQuery' U ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  unfold NoisedBoundedAvgQuery'
  simp
  apply dps.postprocess_prop
  . exact Function.RightInverse.surjective (congrFun rfl)
  . have A : (ε₁ : ℝ) / ((2 * ε₂) : ℕ+) + (ε₁ : ℝ) / ((2 * ε₂) : ℕ+) = (ε₁ : ℝ) / (ε₂ : ℝ) := by
      field_simp
      ring_nf
    rw [← A]
    apply dps.compose_prop
    . apply NoisedBoundedSumQueryDP
    . apply NoisedCountingQueryDP

end SLang
