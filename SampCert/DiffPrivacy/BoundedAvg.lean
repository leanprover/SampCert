/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DiffPrivacy.DP
import SampCert.DiffPrivacy.Count
import SampCert.DiffPrivacy.BoundedSum

open Classical Nat Int Real

noncomputable section

namespace SLang

def NoisedBoundedAvgQuery (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) (l : List ℤ) : SLang ℤ := do
  let S ← NoisedBoundedSumQuery L U h ε₁ (2 * ε₂) l
  let C ← NoisedCountingQuery ε₁ (2 * ε₂) l
  return S / C

def NoisedBoundedAvgQuery' (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) (l : List ℤ) : SLang ℤ :=
  let X := Compose (NoisedBoundedSumQuery L U h ε₁ (2 * ε₂)) (NoisedCountingQuery ε₁ (2 * ε₂))
  PostProcess X (fun z => z.1 / z.2) l

theorem NoisedBoundedAvgQueryIdentical (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) :
  NoisedBoundedAvgQuery' L U h ε₁ ε₂ = NoisedBoundedAvgQuery L U h ε₁ ε₂  := by
  ext l x
  simp [NoisedBoundedAvgQuery, NoisedBoundedAvgQuery', PostProcess, Compose]

theorem BoundedSumQueryDP (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) : DP (NoisedBoundedAvgQuery L U h ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  rw [← NoisedBoundedAvgQueryIdentical]
  unfold NoisedBoundedAvgQuery'
  simp only

  have A := @NoisedCountingQueryDP ℤ ε₁ (2 * ε₂)
  have B := @NoisedBoundedSumQueryDP L U h ε₁ (2 * ε₂)
  have C := DPCompose B A
  simp at C
  ring_nf at C
  rw [← division_def] at C
  have D := DPPostProcess C (fun z => z.1 / z.2)
  exact D

end SLang
