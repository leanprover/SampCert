/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan, Markus de Medeiros
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.DP
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Prod
import Mathlib.Logic.IsEmpty

noncomputable section

open Classical Set

variable [Hu : Nonempty U]

/--
Mediant inequality
-/
lemma tsum_mediant (f g : U -> ENNReal) (hg0 : ∀ u, g u ≠ 0) (hf0 : ∀ u, f u ≠ 0):
  (∑' (u : U), f u) / (∑' (u : U), g u) ≤ ⨆ u, f u / g u := by

  -- We need this to discharge side conditions in this proof, but we can get away with
  -- some classical reasoning instead
  cases (Classical.em (∀ u , g u ≠ ⊤))
  case inr =>
    rename_i Hk
    -- rcases Hk with ⟨ ucont, Hcont ⟩
    have hgtop : ∃ u, g u = ⊤ := by apply (Decidable.not_forall_not.mp Hk)
    have sumtop : ∑' (u : U) , g u = ⊤ := by exact ENNReal.tsum_eq_top_of_eq_top hgtop
    rw [sumtop]
    simp
  case inl =>
    rename_i assumption_g
    -- cases (isEmpty_or_nonempty U)
    -- · rename_i HU
    --   rw [iSup_of_empty]
    --   rw [tsum_empty]
    --   rw [tsum_empty]
    --   simp
    -- · rename_i Hu
    rcases Hu with ⟨ u0 ⟩
    apply (ENNReal.div_le_iff_le_mul _ _).mpr
    · rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro u
      apply (ENNReal.div_le_iff_le_mul _ _).mp
      · refine (le_iSup (fun u => HDiv.hDiv (f u) (g u)) u)
      · left; apply hg0
      · right
        apply ne_of_gt
        apply (LT.lt.trans_le ?g1 ?g2)
        case g2 =>
          apply le_iSup
          apply u
        refine (ENNReal.div_pos (hf0 u) ?g1.hb)
        apply assumption_g
    · left
      apply ne_of_gt
      apply (LT.lt.trans_le ?z1 ?z2)
      case z2 =>
        apply ENNReal.le_tsum
        apply u0
      exact pos_iff_ne_zero.mpr (hg0 u0)
    · right
      apply ne_of_gt
      apply (LT.lt.trans_le ?z3 ?z4)
      case z4 =>
        apply le_iSup
        apply u0
      refine (ENNReal.div_pos (hf0 u0) ?z6)
      apply assumption_g

lemma bounded_quotient (f g : U -> ENNReal) (b : ENNReal) (h_bound : ∀ (u : U), f u / g u ≤ b) (hg0 : ∀ u, g u ≠ 0) (hf0 : ∀ u, f u ≠ 0) :
  (∑' (u : U), f u) / (∑' (u : U), g u) ≤ b := by
  apply le_trans
  · refine (tsum_mediant _ _ hg0 hf0)
  · simp
    assumption

namespace SLang

-- Better proof for Pure DP adaptive composition
theorem PureDP_ComposeAdaptive' (nq1 : List T → PMF U) (nq2 : U -> List T → PMF V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h1 : PureDP nq1 ((ε₁ : ℝ) / ε₂))  (h2 : ∀ u : U, PureDP (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  PureDP (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [PureDP] at *
  have h1a := h1
  -- rcases h1 with ⟨h1a, h1nz⟩
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ Hl₁l₂ u v
  rw [privComposeChainRule]
  rw [privComposeChainRule]
  rw [Real.exp_add]
  rw [ENNReal.ofReal_mul ?s1]
  case s1 => apply Real.exp_nonneg
  rw [ENNReal.div_eq_inv_mul]

  cases Classical.em ((nq1 l₂) u * (nq2 u l₂) v = 0)
  · rename_i Hz
    rw [Hz]
    simp
    simp at Hz
    cases Hz
    · cases (Classical.em (nq1 l₁ u = 0))
      · simp_all
      · rename_i HA HB
        exfalso
        have hcont := h1 l₁ l₂ Hl₁l₂ u
        simp [HA, division_def] at hcont
        rw [ENNReal.mul_top HB] at hcont
        simp_all
    · cases (Classical.em (nq2 u l₁ v = 0))
      · simp_all
      · rename_i HA HB
        exfalso
        have hcont := h2 u
        rw [event_eq_singleton] at hcont
        simp [DP_singleton] at hcont
        have hcont := hcont l₁ l₂ Hl₁l₂ v
        simp [HA, division_def] at hcont
        rw [ENNReal.mul_top HB] at hcont
        simp_all
  · rw [ENNReal.mul_inv]
    · rw [<- mul_assoc]
      rw [mul_right_comm]
      conv =>
        lhs
        arg 1
        rw [mul_assoc]
      rw [mul_right_comm]
      rw [← ENNReal.div_eq_inv_mul]
      rw [← ENNReal.div_eq_inv_mul]
      have h2a'_pre := h2 u
      rw [event_eq_singleton] at h2a'_pre
      simp [DP_singleton] at h2a'_pre
      exact (mul_le_mul' (h1a l₁ l₂ Hl₁l₂ u) (h2a'_pre l₁ l₂ Hl₁l₂ v))
    · left
      rename_i hnz
      intro HK
      simp_all
    · right
      intro HK
      simp_all

end SLang
