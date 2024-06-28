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
variable [HU : Inhabited U] [HU_meas : MeasurableSpace U] [HU_discr : MeasurableSingletonClass U] [HU_count : Countable U]
variable [HV : Inhabited V] [HV_meas : MeasurableSpace V] [HV_discr : MeasurableSingletonClass V] [HV_count : Countable V]


lemma exp_non_top : ∀ (z : ENNReal) (β : ℝ), z ≠ 0 -> z ≠ ⊤ -> z ^ β ≠ ⊤ := by
  intro z β Hz0 HzT
  intro W
  have h : z = 0 ∧ β < 0 ∨ z = ⊤ ∧ 0 < β := by
    apply rpow_eq_top_iff.mp
    apply W
  cases h
  · simp_all only [ne_eq, not_true_eq_false]
  · simp_all only [ne_eq, top_ne_zero, not_false_eq_true, not_true_eq_false]

lemma rpow_ne_zero_iff (x : ENNReal) (y : ℝ): (¬x = 0 ∨ ¬ 0 < y) ∧ (¬ x = ⊤ ∨ ¬ y < 0) -> x ^ y ≠ 0 := by
  have _ := (@ENNReal.rpow_eq_zero_iff x y)
  aesop

lemma ne_top_lt_top (x : ENNReal) : (x ≠ ⊤) -> (x < ⊤) := by
  exact fun a => Ne.lt_top' (id (Ne.symm a))

lemma lt_top_ne_top (x : ENNReal) : (x < ⊤) -> ¬ (x = ⊤) := by
  exact fun a => LT.lt.ne_top a

-- RenyiDivergence_exp

-- set_option pp.coercions false


lemma sup_lemma {s : EReal} (HS0 : 0 < s) (HS1 : s < ⊤) (f : U -> EReal) :
    eexp (s * ⨆ (u : U), f u) =  ⨆ (u : U), eexp (s * f u) := by
  apply LE.le.antisymm
  · apply le_iSup_iff.mpr
    intro w Hw
    apply @Classical.by_contradiction
    intro Hw'
    simp at *
    have Hf' := le_iSup f
    -- Somewhat rocky but I'm certain this is provable
    sorry
  · apply iSup_le
    intro i
    apply eexp_mono_le.mp
    apply ereal_le_smul_left s HS0 HS1
    exact le_iSup f i

  -- symm
  -- apply iSup_eq_of_forall_le_of_forall_lt_exists_gt
  -- · sorry -- Easy
  -- · intro w Hw
  --   apply @Classical.by_contradiction
  --   intro Hcont
  --   simp at Hcont
  --   have HR1 : s * ⨆ u, f u = ⨆ u, s * f u := by
  --     sorry
  --   rw [HR1] at Hw
  --   clear HR1
  --   apply iSup_le_iff.mpr at Hcont

    -- have Hcont' : ⨆ u, eexp (s * f u) < eexp (s * ⨆ u, f u) := lt_of_le_of_lt Hcont Hw
    -- clear Hcont

    -- rcases HU with ⟨ u' ⟩
    -- have Hcont' : eexp (s * f u') < eexp (s * ⨆ u, f u) := lt_of_le_of_lt (Hcont u') Hw
    -- apply eexp_mono_lt.mpr at Hcont'
    -- have Hcont'' : f u' < ⨆ u, f u := ereal_smul_lt_left s HS0 HS1 Hcont'

-- set_option pp.coercions false

/--
Bound on Renyi divergence on adaptively composed queries
-/
lemma privComposeAdaptive_renyi_bound {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V}
    {α : ℝ} (Hα : 1 < α) {l₁ l₂ : List T} (HN : Neighbour l₁ l₂)
    (HAC1 : ACNeighbour nq1) (HAC2 : ∀ u, ACNeighbour (nq2 u)) :
    RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + ENNReal.ofEReal (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  -- Open the definition of Renyi divergence
  unfold RenyiDivergence
  rw [<- ofEReal_plus_nonneg ?G1 ?G2]
  case G1 => exact RenyiDivergence_def_nonneg (nq1 l₁) (nq1 l₂) (HAC1 l₁ l₂ HN) Hα
  case G2 =>
    apply le_iSup_iff.mpr
    intro b Hb
    -- Can use the fact that U is nonempty and RD is nonnegative
    sorry
  apply ofEReal_le_mono

  -- Rewrite to series inequality
  -- FIXME: Explicitly prove the side conditions on α we will need, since they're repeated so often
  have Hα' : ((1 : ℝ).toEReal < α.toEReal ) := by exact EReal.coe_lt_coe_iff.mpr Hα
  simp at Hα'
  apply ereal_smul_le_left (α.toEReal - 1) ?G1 ?G2
  case G1 => sorry
  case G2 => sorry
  rw [ereal_smul_distr_le_left _ ?G1 ?G2]
  case G1 => sorry
  case G2 => sorry
  apply eexp_mono_le.mpr
  rw [<- eexp_add]
  rw [RenyiDivergence_def_exp _ _ Hα]
  rw [RenyiDivergence_def_exp _ _ Hα]

  -- Simplify sup
  conv =>
    enter [2, 2, 1, 2, 1, u]
    rw [toEReal_ofENNReal_nonneg]
    · skip
    · apply RenyiDivergence_def_nonneg (nq2 u l₁) (nq2 u l₂) (HAC2 u l₁ l₂ HN) Hα
  rw [sup_lemma ?G1 ?G2]
  case G1 => sorry
  case G2 => sorry
  conv =>
    enter [2, 2, 1, u]
    rw [RenyiDivergence_def_exp _ _ Hα]

  -- Split series
  rw [ENNReal.tsum_prod']

  -- Apply chain rule, and simplify powers
  conv =>
    enter [1, 1, a, 1, b]
    rw [privComposeChainRule]
    rw [privComposeChainRule]
    rw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    rw [ENNReal.mul_rpow_of_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]

  -- Bring sup into the sum
  rw [<- ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a

  -- Commute and cancel the non-adaptive nq l₁ terms
  conv =>
    enter [1, 1, b]
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [mul_assoc]
    skip
  conv =>
    enter [1, 1, b]
    rw [<- mul_assoc]
    skip
  rw [ENNReal.tsum_mul_left]
  apply (ENNReal.mul_le_mul_left ?G1 ?G2).mpr
  case G1 => sorry
  case G2 => sorry

  -- Apply upper bound lemma
  conv =>
    enter [1, 1, b]
    rw [mul_comm]
  exact le_iSup_iff.mpr fun b a_1 => a_1 a

/--
Adaptively Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privComposeAdaptive_zCDPBound {nq1 : List T → PMF U} {nq2 : U -> List T → PMF V} {ε₁ ε₂ ε₃ ε₄ : ℕ+}
  (h1 : zCDPBound nq1 ((ε₁ : ℝ) / ε₂)) (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  zCDPBound (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ Hneighbours

  sorry

  /-
  -- Loose step
  apply (@LE.le.trans _ _ _ (1/2 * (↑↑ε₁ / ↑↑ε₂)^2 * α + 1/2 * (↑↑ε₃ / ↑↑ε₄)^2 * α) _ _ ?case_sq)
  case case_sq =>
    -- Binomial bound
    rw [add_sq]
    rw [<- right_distrib]
    apply (mul_le_mul_of_nonneg_right _ ?goal1)
    case goal1 => linarith
    rw [<- left_distrib]
    apply (mul_le_mul_of_nonneg_left _ ?goal1)
    case goal1 => linarith
    apply add_le_add_right
    have hrw : (↑↑ε₁ / ↑↑ε₂ : ℝ) ^ 2 = (↑↑ε₁ / ↑↑ε₂) ^ 2 + 0 := by linarith
    conv =>
      lhs
      rw [hrw]
    clear hrw
    apply add_le_add_left
    have h : 0 <= (↑↑ε₁ / ↑↑ε₂) * (↑↑ε₃ / ↑↑ε₄ : ℝ) := by
      apply mul_nonneg <;> apply div_nonneg <;> linarith
    linarith
  -- Rewrite the upper bounds in terms of Renyi divergences of nq1/nq2
  rw [zCDPBound] at h1
  have marginal_ub := h1 α Hα l₁ l₂ Hneighbours
  have conditional_ub : (⨆ (u : U),  RenyiDivergence (nq2 u l₁) (nq2 u l₂) α ≤ 1 / 2 * (↑↑ε₃ / ↑↑ε₄) ^ 2 * α) :=
    ciSup_le fun x => h2 x α Hα l₁ l₂ Hneighbours
  apply (@LE.le.trans _ _ _ (RenyiDivergence (nq1 l₁) (nq1 l₂) α + ⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) _ _ ?case_alg)
  case case_alg => linarith
  apply (privComposeAdaptive_renyi_bound _ _ _ _) <;> aesop
  -/


/--
Adaptive composition preserves absolute continuity
-/
def privComposeAdaptive_AC (nq1 : Mechanism T U) (nq2 : U -> Mechanism T V) (Hac1 : ACNeighbour nq1) (Hac2 : ∀ u, ACNeighbour (nq2 u)) :
    ACNeighbour (privComposeAdaptive nq1 nq2) := by
  rw [ACNeighbour]
  simp [privComposeAdaptive]
  intro l₁ l₂ HN x Hx
  rcases x with ⟨ u, v ⟩
  simp [DFunLike.coe, PMF.bind, PMF.pure] at *
  intro u'
  rcases Hx u' with A | B
  · left
    exact Hac1 l₁ l₂ HN u' A
  · right
    intro v'
    simp_all
    exact Hac2 u' l₁ l₂ HN v B


/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privComposeAdaptive_zCDP (nq1 : List T → PMF U) {nq2 : U -> List T → PMF V} {ε₁ ε₂ ε₃ ε₄ : ℕ+}
    (h : zCDP nq1 ((ε₁ : ℝ) / ε₂)) (h' : ∀ u, zCDP (nq2 u) ((ε₃ : ℝ) / ε₄)) :
    zCDP (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  apply And.intro
  · apply privComposeAdaptive_AC <;> aesop
  · apply privComposeAdaptive_zCDPBound  <;> aesop
end SLang
