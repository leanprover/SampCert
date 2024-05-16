/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Mechanism.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.Queries.Count.Code

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}

theorem CountingQuery1Sensitive :
  @sensitivity T CountingQuery 1 := by
  simp [CountingQuery, sensitivity]
  intros l₁ l₂ H
  cases H
  . rename_i a b n h1 h2
    subst h1 h2
    simp
  . rename_i a b n h1 h2
    subst h1 h2
    simp
  . rename_i a n b m h1 h2
    subst h1 h2
    simp

theorem NoisedCountingQueryDP (ε₁ ε₂ : ℕ+) :
  @DP T ℤ (NoisedCountingQuery ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  apply NoisedQueryDP
  apply CountingQuery1Sensitive

theorem NoisedCountingQuery_NonZeroNQ (ε₁ ε₂ : ℕ+) :
  @NonZeroNQ T ℤ (NoisedCountingQuery ε₁ ε₂) := by
  apply NoisedQuery_NonZeroNQ

theorem NoisedCountingQuery_NonTopNQ (ε₁ ε₂ : ℕ+) :
  @NonTopNQ T ℤ (NoisedCountingQuery ε₁ ε₂) := by
  apply NoisedQuery_NonTopNQ

theorem NoisedCountingQuery_NonTopRDNQ (ε₁ ε₂ : ℕ+) :
  @NonTopRDNQ T ℤ (NoisedCountingQuery ε₁ ε₂) := by
  apply NoisedQuery_NonTopRDNQ

theorem NoisedCountingQuery_NonTopSum (ε₁ ε₂ : ℕ+) :
  @NonTopSum T ℤ (NoisedCountingQuery ε₁ ε₂) := by
  apply NoisedQuery_NonTopSum

end SLang
