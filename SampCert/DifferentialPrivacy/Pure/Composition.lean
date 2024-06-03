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


-- FIXME: move
/--
Mediant inequality
-/
lemma tsum_mediant (f g : U -> ENNReal) : (∑' (u : U), f u) / (∑' (u : U), g u) ≤ sSup (range (fun (u : U) => f u / g u)) :=
  sorry

lemma bounded_quotient (f g : U -> ENNReal) (b : ENNReal) (h_bound : ∀ (u : U), f u / g u ≤ b) :
  (∑' (u : U), f u) / (∑' (u : U), g u) ≤ b := by
  apply le_trans
  · apply tsum_mediant
  · simp -- wow, what a simplification
    assumption

namespace SLang

theorem PureDP_Compose' {nq1 : Mechanism T U} {nq2 : List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : PureDP nq2 ((ε₃ : ℝ) / ε₄)) :
  DP (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  rcases h1 with ⟨h1a, _⟩
  rcases h2 with ⟨h2a, _⟩
  -- Suffices to bound at each point in the resulting pmf
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  -- For all neighbouring DB's and output points
  intros l₁ l₂ neighbours x y
  replace h1a := h1a l₁ l₂ neighbours x
  replace h2a := h2a l₁ l₂ neighbours y
  -- Open the implementation
  simp [privCompose]
  -- Rearrange nested sum to double sum
  conv =>
    left
    congr
    . right
      intro a
      rw [← ENNReal.tsum_mul_left]
    . right
      intro a
      rw [← ENNReal.tsum_mul_left]
  simp
  rw [tsum_tsum_eq_single _ x y]
  . simp
    rw [tsum_tsum_eq_single _ x y]
    . simp
      have A : nq1 l₁ x * nq2 l₁ y / (nq1 l₂ x * nq2 l₂ y) = (nq1 l₁ x / nq1 l₂ x) * (nq2 l₁ y / nq2 l₂ y) := by
        rw [division_def]
        rw [division_def]
        rw [division_def]
        rw [ENNReal.mul_inv]
        . ring_nf
        . aesop
        . aesop
      rw [A]
      have B := mul_le_mul' h1a h2a
      apply le_trans B
      rw [Real.exp_add]
      rw [ENNReal.ofReal_mul (Real.exp_nonneg (↑↑ε₁ / ↑↑ε₂))]
    . aesop
    . aesop
  . aesop
  . aesop

theorem PureDP_Compose (nq1 : List T → SLang U) (nq2 : List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : PureDP nq2 ((ε₃ : ℝ) / ε₄)) :
  PureDP (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  have hc := h
  have h'c := h'
  rcases h with ⟨ _ , h2 ⟩
  rcases h' with ⟨ _ , h'2 ⟩
  constructor
  . apply PureDP_Compose' hc h'c
  . apply privCompose_NonZeroNQ h2 h'2


-- set_option pp.notation false

theorem PureDP_ComposeAdaptive' (nq1 : List T → SLang U) (nq2 : U -> List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h1 : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : ∀ u : U, PureDP (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  PureDP (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  rcases h1 with ⟨h1a, _⟩
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  apply And.intro
  · -- Composition satisfies DP bound

    -- For all neighbours...
    intros l₁ l₂ neighbours x
    replace h1a := h1a l₁ l₂ neighbours

    -- Simplify under the ∀ in h2
    have h2' : ∀ (u : U), (nq2 u l₁ x) / (nq2 u l₂ x) <= ENNReal.ofReal (((↑↑ε₃ : ℝ ) / ↑↑ε₄).exp) := by
      intro u
      replace h2 := h2 u
      rw [event_eq_singleton] at h2
      simp [DP_singleton] at h2
      rcases h2 with ⟨h2a, _⟩
      apply h2a
      apply neighbours

    simp [privComposeAdaptive]

    have h3 : ∀ (a : U), nq1 l₁ a * nq2 a l₁ x / (nq1 l₂ a * nq2 a l₂ x) ≤ ENNReal.ofReal (↑↑ε₁ / ↑↑ε₂ + ↑↑ε₃ / ↑↑ε₄ : ℝ).exp := by
      intro a
      have h1a' := h1a a
      have h2a' := h2' a

      rw [Real.exp_add]
      -- How to focus individual goals in lean?
      rw [ENNReal.ofReal_mul]; all_goals (try apply Real.exp_nonneg)

      -- Some inequality pushing I beg lean to let me Search
      sorry

    -- Put a name to the summands (why is this so hard)
    let f := (fun (a : U) => nq1 l₁ a * nq2 a l₁ x)
    let g := (fun (a : U) => nq1 l₂ a * nq2 a l₂ x)
    have hf :  (∑' (a : U), nq1 l₁ a * nq2 a l₁ x) = (∑' (a : U), f a) := sorry
    have hg :  (∑' (a : U), nq1 l₂ a * nq2 a l₂ x) = (∑' (a : U), g a) := sorry
    rw [hf, hg]

    -- Mediant lemma
    apply bounded_quotient

    -- Split the exponential by the sum
    rw [Real.exp_add]
    -- How to focus individual goals in lean?
    rw [ENNReal.ofReal_mul]; all_goals (try apply Real.exp_nonneg)

    -- Apply the inequalities from above
    intro u
    have h1a' := h1a u
    have h2a' := h2' u
    simp [f, g]

    -- Push around inequalities
    sorry

  · -- Composition is nonzero at all elements
    sorry


end SLang
