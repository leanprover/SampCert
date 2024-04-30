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
  if C ≤ 1 then return (L + U) / 2
  else return S / C

theorem BoundedSumQueryDP (L U : ℤ) (h : L < U) (ε₁ ε₂ : ℕ+) : DP (NoisedBoundedAvgQuery L U h ε₁ ε₂) ε₁ ε₂ := by
  have A := @NoisedCountingQueryDP ℤ ε₁ (2 * ε₂)
  have B := @NoisedBoundedSumQueryDP L U h ε₁ (2 * ε₂)
  sorry


end SLang
