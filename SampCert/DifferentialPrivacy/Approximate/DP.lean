/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Generic
import SampCert.DifferentialPrivacy.Neighbours
-- import SampCert.DifferentialPrivacy.Pure.DP
-- import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
-- import SampCert.Util.Log

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP' (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) ≤ δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0)

def ApproximateDP (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  DP' m ε δ

/--
Approximate DP is trivial with δ ≥ 1
-/
theorem ApproximateDP_gt1 (m : Mechanism T U) (ε : ℝ) {δ : NNReal} (Hδ : 1 ≤ δ) : ApproximateDP m ε δ := by
  rw [ApproximateDP]
  rw [DP']
  intros l₁ l₂ _ S
  have H1 : (∑' (x : U), if x ∈ S then (m l₁) x else 0) ≤ 1 := by
    rw [<- PMF.tsum_coe (m l₁)]
    apply ENNReal.tsum_le_tsum
    intro u
    split <;> simp
  apply le_trans H1
  conv =>
    left
    rw [<- add_zero 1]
  apply add_le_add
  · simp
    trivial
  · apply mul_nonneg
    · exact zero_le (ENNReal.ofReal (Real.exp ε))
    · exact zero_le (∑' (x : U), if x ∈ S then (m l₂) x else 0)


end SLang
