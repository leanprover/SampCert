/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# zCDP Adaptive Composition

This file builds up to a zCDP bound on adaptively composed zCDP queries.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U V : Type }
variable [HU : Inhabited U]
variable [HV : Inhabited V]

/--
The Renyi divergence is monotonic in its sum
-/
lemma renyi_mono_sum (x y : ENNReal) {α : ℝ} (h : 1 < α) : Real.log (((ENNReal.ofReal α - 1) * x).toReal) ≤ Real.log (((ENNReal.ofReal α - 1) * y).toReal) -> (x ≤ y) :=
  sorry


/--
Adaptively Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privComposeAdaptive_zCDPBound {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : zCDPBound nq1 ((ε₁ : ℝ) / ε₂))  (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) (nn1 : NonZeroNQ nq1) (nn2 : ∀ u, NonZeroNQ (nq2 u)) (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nts1 : NonTopNQ nq1) (nts2 : ∀ u, NonTopNQ (nq2 u)) :
  zCDPBound (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  rw [zCDPBound]

  sorry

/--
Adaptive composed query distribution is nowhere zero
-/
theorem privComposeAdaptive_NonZeroNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonZeroNQ nq1) (nt2 : ∀ u, NonZeroNQ (nq2 u)) :
  NonZeroNQ (privComposeAdaptive nq1 nq2) := by
  simp [NonZeroNQ] at *
  simp [privComposeAdaptive]
  intros l n
  rcases HU with ⟨ u0 ⟩
  exists u0
  apply And.intro
  · apply nt1
  · apply nt2

/--
All outputs of a adaptive composed query have finite probability.
-/
theorem privComposeAdaptive_NonTopNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopNQ nq1) (nt2 : ∀ u, NonTopNQ (nq2 u)) :
  NonTopNQ (privComposeAdaptive nq1 nq2) := by
  simp [NonTopNQ] at *
  simp [privComposeAdaptive]
  admit

/--
Adaptive composed query is a proper distribution
-/
theorem privComposeAdaptive_NonTopSum {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopSum nq1) (nt2 : ∀ u, NonTopSum (nq2 u)) :
  NonTopSum (privComposeAdaptive nq1 nq2) := by
  rw [NonTopSum] at *
  simp only [privComposeAdaptive, Bind.bind, pure, bind_pure, bind_apply]
  intro l
  -- forall n, a, nq1 l a * nq2 a l n ≤ (nq1 l a + nq2 a l n )^2
  -- Bound the series above by ∑' (n : V) (a : U), (nq1 l a + nq2 a l n )^2
  admit



/--
Renyi divergence beteeen adaptive composed queries on neighbours are finite.
-/
theorem privComposeAdaptive_NonTopRDNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nn1 : NonTopNQ nq1) (nn2 : ∀ u, NonTopNQ (nq2 u)) :
  NonTopRDNQ (privComposeAdaptive nq1 nq2) := by admit
  -- simp [NonTopRDNQ] at *
  -- intro α h1 l₁ l₂ h2
  -- replace nt1 := nt1 α h1 l₁ l₂ h2
  -- replace nt2 := nt2 α h1 l₁ l₂ h2
  -- simp [privCompose]
  -- rw [ENNReal.tsum_prod']
  -- simp
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   right
  --   intro y
  --   congr
  --   . left
  --     rw [compose_sum_rw]
  --   . left
  --     rw [compose_sum_rw]
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   right
  --   intro y
  --   rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (lt_trans zero_lt_one h1))]
  --   rw [ENNReal.mul_rpow_of_ne_top (nn1 l₂ x) (nn2 l₂ y)]
  --   rw [mul_assoc]
  --   right
  --   rw [mul_comm]
  --   rw [mul_assoc]
  --   right
  --   rw [mul_comm]
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   right
  --   intro y
  --   rw [← mul_assoc]
  -- conv =>
  --   right
  --   left
  --   right
  --   intro x
  --   rw [ENNReal.tsum_mul_left]
  -- rw [ENNReal.tsum_mul_right]
  -- intro H
  -- rw [mul_eq_top] at H
  -- cases H
  -- . rename_i h3
  --   cases h3
  --   rename_i h4 h5
  --   contradiction
  -- . rename_i h3
  --   cases h3
  --   rename_i h4 h5
  --   contradiction

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privComposeAdaptive_zCDP (nq1 : List T → SLang U) (nq2 : U -> List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : zCDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : ∀ u, zCDP (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  zCDP (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  rcases h with ⟨ _ , _ , _ , _ , _ ⟩
  repeat any_goals constructor
  · admit
  · admit
  · admit
  · admit
  · admit

end SLang
