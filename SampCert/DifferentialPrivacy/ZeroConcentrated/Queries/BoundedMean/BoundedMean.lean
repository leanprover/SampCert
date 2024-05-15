/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Composition.Composition
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Postprocessing.Postprocessing
import SampCert.DifferentialPrivacy.ZeroConcentrated.Queries.Count.Count
import SampCert.DifferentialPrivacy.ZeroConcentrated.Queries.BoundedSum.BoundedSum

open Classical Nat Int Real

noncomputable section

namespace SLang

def NoisedBoundedAvgQuery (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℤ := do
  let S ← NoisedBoundedSumQuery U ε₁ (2 * ε₂) l
  let C ← NoisedCountingQuery ε₁ (2 * ε₂) l
  return S / C

def NoisedBoundedAvgQuery' (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℤ :=
  let X := Compose (NoisedBoundedSumQuery U ε₁ (2 * ε₂)) (NoisedCountingQuery ε₁ (2 * ε₂))
  PostProcess X (fun z => z.1 / z.2) l

theorem NoisedBoundedAvgQueryIdentical (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  NoisedBoundedAvgQuery' U ε₁ ε₂ = NoisedBoundedAvgQuery U ε₁ ε₂  := by
  ext l x
  simp [NoisedBoundedAvgQuery, NoisedBoundedAvgQuery', PostProcess, Compose]

theorem BoundedSumQueryDP (U : ℕ+) (ε₁ ε₂ : ℕ+) : DP (NoisedBoundedAvgQuery U ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  rw [← NoisedBoundedAvgQueryIdentical]
  unfold NoisedBoundedAvgQuery'
  simp only

  have A₁ := @NoisedCountingQueryDP ℕ ε₁ (2 * ε₂)
  have A₂ := @NoisedCountingQuery_NonZeroNQ ℕ ε₁ (2 * ε₂)
  have A₃ := @NoisedCountingQuery_NonTopNQ ℕ ε₁ (2 * ε₂)
  have A₄ := @NoisedCountingQuery_NonTopRDNQ ℕ ε₁ (2 * ε₂)
  have A₅ := @NoisedCountingQuery_NonTopSum ℕ ε₁ (2 * ε₂)

  have B₁ := NoisedBoundedSumQueryDP U ε₁ (2 * ε₂)
  have B₂ := NoisedBoundedSumQuery_NonZeroNQ U ε₁ (2 * ε₂)
  have B₃ := NoisedBoundedSumQuery_NonTopNQ U ε₁ (2 * ε₂)
  have B₄ := NoisedBoundedSumQuery_NonTopRDNQ U ε₁ (2 * ε₂)
  have B₅ := NoisedBoundedSumQuery_NonTopSum U ε₁ (2 * ε₂)

  have C₁ := DPCompose B₁ A₁ B₂ A₂ B₄ A₄ B₃ A₃
  have C₂ := DPCompose_NonZeroNQ B₂ A₂
  have C₃ := DPCompose_NonTopNQ B₃ A₃
  have C₄ := DPCompose_NonTopRDNQ B₄ A₄ B₂ A₂
  have C₅ := DPCompose_NonTopSum B₅ A₅
  simp at *
  ring_nf at *
  rw [← division_def] at *
  have D := DPPostProcess C₁ C₂ C₄ C₃ C₅ (fun z => z.1 /z.2)
  exact D

end SLang
