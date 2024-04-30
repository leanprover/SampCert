/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DiffPrivacy.DP

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}

def CountingQuery (l : List T) : ℤ := List.length l

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

def NoisedCountingQuery (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  NoisedQuery CountingQuery 1 ε₁ ε₂ l

theorem NoisedCountingQueryDP (ε₁ ε₂ : ℕ+) : @DP T ℤ (NoisedCountingQuery ε₁ ε₂) ε₁ ε₂ := by
  apply NoisedQueryDP
  apply CountingQuery1Sensitive

end SLang
