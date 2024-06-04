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



-- Solving the side conditions needs to be done separately depending on if u is inhabited or not
/--
Mediant inequality
-/
lemma tsum_mediant (f g : U -> ENNReal) (hg0 : ∀ u, g u ≠ 0) (hf0 : ∀ u, f u ≠ 0):
  (∑' (u : U), f u) / (∑' (u : U), g u) ≤ ⨆ u, f u / g u := by
  apply (ENNReal.div_le_iff_le_mul _ _).mpr
  · rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro u
    apply (ENNReal.div_le_iff_le_mul _ _).mp
    · refine (le_iSup (fun u => HDiv.hDiv (f u) (g u)) u)
    · left; apply hg0
    · sorry
  · sorry
  · sorry

lemma bounded_quotient (f g : U -> ENNReal) (b : ENNReal) (h_bound : ∀ (u : U), f u / g u ≤ b) (hg0 : ∀ u, g u ≠ 0) (hf0 : ∀ u, f u ≠ 0) :
  (∑' (u : U), f u) / (∑' (u : U), g u) ≤ b := by
  apply le_trans
  · refine (tsum_mediant _ _ hg0 hf0)
  · simp
    assumption


namespace SLang

theorem PureDP_Compose' {nq1 : Mechanism T U} {nq2 : List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : PureDP nq2 ((ε₃ : ℝ) / ε₄)) :
  DP (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  rcases h1 with ⟨h1a, _⟩
  rcases h2 with ⟨h2a, _⟩
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x y
  replace h1a := h1a l₁ l₂ neighbours x
  replace h2a := h2a l₁ l₂ neighbours y
  simp [privCompose]
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
  rcases h1 with ⟨h1a, h1nz⟩
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  apply And.intro
  · intros l₁ l₂ neighbours x
    replace h1a := h1a l₁ l₂ neighbours

    have h2' : ∀ (u : U), (nq2 u l₁ x) / (nq2 u l₂ x) <= ENNReal.ofReal (((↑↑ε₃ : ℝ ) / ↑↑ε₄).exp) := by
      intro u
      replace h2 := h2 u
      rw [event_eq_singleton] at h2
      simp [DP_singleton] at h2
      rcases h2 with ⟨h2a, h2nz⟩
      apply h2a
      apply neighbours

    simp [privComposeAdaptive]

    have h3 : ∀ (a : U), nq1 l₁ a * nq2 a l₁ x / (nq1 l₂ a * nq2 a l₂ x) ≤ ENNReal.ofReal (↑↑ε₁ / ↑↑ε₂ + ↑↑ε₃ / ↑↑ε₄ : ℝ).exp :=  by
      intro a
      -- Split the expontntial
      rw [Real.exp_add]
      rw [ENNReal.ofReal_mul] <;> try apply Real.exp_nonneg -- How to focus individual goals in lean? This is a mess

      -- Push around inequalities
      rw [ENNReal.div_eq_inv_mul]
      rw [ENNReal.mul_inv]
      · rw [<- mul_assoc]
        rw [mul_right_comm]
        conv =>
          lhs
          arg 1
          rw [mul_assoc]
        rw [mul_right_comm]
        rw [← ENNReal.div_eq_inv_mul]
        rw [← ENNReal.div_eq_inv_mul]
        exact mul_le_mul' (h1a a) (h2' a)
      · left
        apply h1nz
      · right
        rcases (h2 a) with ⟨ _ , h2nz ⟩
        apply h2nz

    -- apply? -- gives me this but it times out. odd.
    -- refine (bounded_quotient (fun u => nq1 l₁ u * nq2 u l₁ x) (fun u => nq1 l₂ u * nq2 u l₂ x) (ENNReal.ofReal (↑↑ε₁ / ↑↑ε₂ + ↑↑ε₃ / ↑↑ε₄ : ℝ).exp) h3 ?intro.left.hg0 ?intro.left.hf0)

    -- Put a name to the summands (why is this so hard)
    let f := (fun (a : U) => nq1 l₁ a * nq2 a l₁ x)
    let g := (fun (a : U) => nq1 l₂ a * nq2 a l₂ x)
    have hf :  (∑' (a : U), nq1 l₁ a * nq2 a l₁ x) = (∑' (a : U), f a) := by congr
    have hg :  (∑' (a : U), nq1 l₂ a * nq2 a l₂ x) = (∑' (a : U), g a) := by congr
    rw [hf, hg]

    -- Conclude by Mediant lemma
    apply bounded_quotient
    apply h3
    all_goals (intro u; rcases (h2 u) with ⟨ _ , h2nz ⟩)
    all_goals (simp only [f, g])
    · exact mul_ne_zero (h1nz l₂ u) (h2nz l₂ x)
    · exact mul_ne_zero (h1nz l₁ u) (h2nz l₁ x)

  · -- Composition is nonzero at all elements
    simp only [NonZeroNQ]
    intros l n

    simp? only [privComposeAdaptive, bind, pure, bind_pure, bind_apply]
    -- Interesting: This relies on U being nonempty again

    -- ne_eq, ENNReal.tsum_eq_zero]
    sorry


end SLang
