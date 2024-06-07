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

set_option linter.unusedVariables false

-- Morally, b = ⨆ (u : U), RenyiDivergence .... However, iSup itself does not remember that the supremum
-- exists, setting the value to zero if not.
def RDBound (nq2 : U -> List T -> SLang V) (α : ℝ) (Hα : 1 < α) (l₁ l₂ : List T) (HN : Neighbour l₁ l₂) (b : ℝ) : Prop :=
  ∀ u, (0 < RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) ∧ (RenyiDivergence (nq2 u l₁) (nq2 u l₂) α ≤ b)

lemma RDBound_ofZCDPBound {nq2 : U -> List T → SLang V} {ε₃ ε₄ : ℕ+} (α : ℝ) (Hα : 1 < α) (l₁ l₂ : List T) (HN : Neighbour l₁ l₂)
  (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) : RDBound nq2 α Hα l₁ l₂ HN (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  rw [RDBound]
  intro u
  apply And.intro
  · sorry
  · sorry

def RDBounded (nq2 : U -> List T -> SLang V) : Prop :=
  ∀ (α : ℝ) (Hα : 1 < α) (l₁ l₂ : List T) (HN : Neighbour l₁ l₂), ∃ (b : ℝ), RDBound nq2 α Hα l₁ l₂ HN b

lemma RDBounded_ofZCDPBound {nq2 : U -> List T → SLang V} {ε₃ ε₄ : ℕ+}  (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  RDBounded nq2 := by
  intro α Hα l₁ l₂ HN
  exists (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α)
  apply RDBound_ofZCDPBound <;> aesop


lemma exp_non_top : ∀ (z : ENNReal) (β : ℝ), z ≠ 0 -> z ≠ ⊤ -> z ^ β ≠ ⊤ := by
  intro z β Hz0 HzT
  intro W
  have h : z = 0 ∧ β < 0 ∨ z = ⊤ ∧ 0 < β := by
    apply rpow_eq_top_iff.mp
    apply W
  cases h
  · aesop
  · aesop


lemma RenyiDivergence_exp (p q : SLang T) {α : ℝ} (h : 1 < α)
  (H1 : 0 < ∑' (x : T), p x ^ α * q x ^ (1 - α)) (H2 : ∑' (x : T), p x ^ α * q x ^ (1 - α) < ⊤):
  Real.exp ((α - 1) * RenyiDivergence p q α) = (∑' x : T, (p x)^α * (q x)^(1 - α)).toReal := by
  simp only [RenyiDivergence]
  rw [<- mul_assoc]
  have test : (α - 1) * (α - 1)⁻¹ = 1 := by
    refine mul_inv_cancel ?h
    linarith
  rw [test]
  clear test
  simp
  rw [Real.exp_log]
  apply ENNReal.toReal_pos_iff.mpr
  apply And.intro H1 H2


/--
Adaptive composed query distribution is nowhere zero
-/
theorem privComposeAdaptive_NonZeroNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonZeroNQ nq1) (nt2 : ∀ u, NonZeroNQ (nq2 u)) :
  NonZeroNQ (privComposeAdaptive nq1 nq2) := by
  simp [NonZeroNQ] at *
  simp [privComposeAdaptive]
  aesop

lemma rpow_ne_zero_iff (x : ENNReal) (y : ℝ): (¬x = 0 ∨ ¬ 0 < y) ∧ (¬ x = ⊤ ∨ ¬ y < 0) -> x ^ y ≠ 0 := by
  have H1 := (@ENNReal.rpow_eq_zero_iff x y)
  aesop

lemma ne_top_lt_top (x : ENNReal) : (x ≠ ⊤) -> (x < ⊤) := by
  exact fun a => Ne.lt_top' (id (Ne.symm a))

lemma lt_top_ne_top (x : ENNReal) : (x < ⊤) -> ¬ (x = ⊤) := by
  exact fun a => LT.lt.ne_top a

/--
All outputs of a adaptive composed query have finite probability.
-/
theorem privComposeAdaptive_NonTopNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V}
  (nt1 : NonTopNQ nq1) (nt2 : ∀ u, NonTopNQ (nq2 u)) :
  NonTopNQ (privComposeAdaptive nq1 nq2) := by
  simp [NonTopNQ] at *
  intros l u v
  rw [privComposeChainRule]
  apply ENNReal.mul_ne_top
  · aesop
  · aesop

/--
Adaptive composed query is a proper distribution
-/
theorem privComposeAdaptive_NonTopSum {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V}
  (nt1 : NonTopSum nq1) (nt2 : ∀ u, NonTopSum (nq2 u))
  (Hubound : ∃ (z : ℝ), ∀ (u : U), ∀ l, ∑'(v : V), nq2 u l v ≤ ENNReal.ofReal z) :
  NonTopSum (privComposeAdaptive nq1 nq2) := by
  simp [NonTopSum] at *
  intro l
  simp [privComposeAdaptive]
  rw [ENNReal.tsum_prod']
  conv =>
    right
    left
    right
    intro a
    right
    intro b
    simp
    rw [(compose_sum_rw_adaptive _ _ a b)]
  conv =>
    right
    left
    right
    intro a
    rw [ENNReal.tsum_mul_left]

  rcases Hubound with ⟨ z , Hubound ⟩
  apply lt_top_ne_top
  apply (@LE.le.trans_lt _ _ _ (∑' (a : U), nq1 l a * ENNReal.ofReal z) _ ?goal1)
  case goal1 =>
    apply ENNReal.tsum_le_tsum
    intro a
    apply mul_le_mul_of_nonneg_left
    · aesop
    · aesop
  rw [ENNReal.tsum_mul_right]
  apply ne_top_lt_top
  intro Hcont
  rw [mul_eq_top] at Hcont
  cases Hcont
  · rename_i h
    rcases h with ⟨ h0 , h1 ⟩
    aesop
  · rename_i h
    rcases h with ⟨ h0 , h1 ⟩
    aesop


/--
Renyi divergence beteeen adaptive composed queries on neighbours are finite.
-/
theorem privComposeAdaptive_NonTopRDNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V}
  (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nn1 : NonTopNQ nq1) (nn2 : ∀ u, NonTopNQ (nq2 u)) (nz1 : NonZeroNQ nq1) (nz2 : ∀ u, NonZeroNQ (nq2 u))
  (Hubound : RDBounded nq2) :
  NonTopRDNQ (privComposeAdaptive nq1 nq2) := by
  rw [NonTopRDNQ] at *
  intro α h1 l₁ l₂ h2
  simp [privComposeAdaptive]
  rw [ENNReal.tsum_prod']
  simp

  conv =>
    right
    left
    right
    intro x
    right
    intro y
    congr
    . left
      rw [(compose_sum_rw_adaptive _ _ x y)]
    . left
      rw [(compose_sum_rw_adaptive _ _ x y)]
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (lt_trans zero_lt_one h1))]
    rw [ENNReal.mul_rpow_of_ne_top (nn1 l₂ x) (nn2 x l₂ y)]
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [mul_assoc]
    right
    rw [mul_comm]
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    rw [← mul_assoc]
  conv =>
    right
    left
    right
    intro x
    rw [ENNReal.tsum_mul_left]
  -- Might not be true, terms in the second sum are pointwise bounded but not uniformly bounded

  rcases (Hubound α h1 l₁ l₂ h2) with ⟨ b , Hubound ⟩

  apply lt_top_ne_top
  apply (@LE.le.trans_lt _ _ _ (∑' (x : U), nq1 l₁ x ^ α * nq1 l₂ x ^ (1 - α) * ENNReal.ofReal (rexp ((α - 1) * b))) _ ?goal1)

  case goal1 =>
    apply ENNReal.tsum_le_tsum
    intro a
    refine (ENNReal.mul_le_mul_left ?h.h0 ?h.hinf).mpr ?h.a
    · apply mul_ne_zero_iff.mpr
      apply And.intro
      · refine rpow_ne_zero_iff (nq1 l₁ a) α ?h.h0.left.a
        apply And.intro
        · left
          aesop
        · left
          aesop
      · refine rpow_ne_zero_iff (nq1 l₂ a) (1 - α) ?h.h0.right.a
        apply And.intro
        · left
          aesop
        · left
          aesop
    · intro H
      rw [mul_eq_top] at H
      cases H
      · rename_i Hk
        rcases Hk with ⟨ hk1, hk2 ⟩
        have Hcont : nq1 l₂ a ^ (1-α) ≠ ⊤ := by
          apply exp_non_top
          · aesop
          · aesop
        aesop
      · rename_i Hk
        rcases Hk with ⟨ hk1, hk2 ⟩
        have Hcont : nq1 l₁ a ^ (α) ≠ ⊤ := by
          apply exp_non_top
          · aesop
          · apply nn1
        aesop
    · -- rw [RenyiDivergence_exp (nq1 l₁) (nq1 l₂) Hα ?H1 ?H2]
      sorry

  rw [ENNReal.tsum_mul_right]
  apply ne_top_lt_top
  intro H
  rw [mul_eq_top] at H
  cases H
  . rename_i h3
    rcases h3 with ⟨ h30, h31 ⟩
    aesop
  . rename_i h3
    rcases h3 with ⟨ h30, h31 ⟩
    aesop


/--
Bound on Renyi divergence on adaptively composed queries
-/
lemma privComposeAdaptive_renyi_bound {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (α : ℝ) (Hα : 1 < α)
  (HNT1 : NonTopNQ nq1) (HNTRDNQ1 : NonTopRDNQ nq1) (HNTRDNQ2 : ∀ u, NonTopRDNQ (nq2 u))
  (HN : Neighbour l₁ l₂) (HNZ1 : NonZeroNQ nq1) (HNZ2 : ∀ u, NonZeroNQ (nq2 u)) (HNT2 : ∀ u, NonTopNQ (nq2 u))
  (b : ℝ)
  (Hubound : RDBound nq2 α Hα l₁ l₂ HN b)
  (Hubound2 : RDBounded nq2) :
  RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + b := by
  apply (RenyiDivergence_mono_sum _ _ α Hα)
  rw [RenyiDivergence_exp (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) Hα ?H1 ?H2]
  case H1 =>
    rcases HV with ⟨ v0 ⟩
    rcases HU with ⟨ u0 ⟩
    have Hle : (privComposeAdaptive nq1 nq2 l₁ (u0, v0) ^ α * privComposeAdaptive nq1 nq2 l₂ (u0, v0) ^ (1 - α)) ≤ (∑' (x : U × V), privComposeAdaptive nq1 nq2 l₁ x ^ α * privComposeAdaptive nq1 nq2 l₂ x ^ (1 - α)) := by
      exact ENNReal.le_tsum (u0, v0)
    apply (LE.le.trans_lt' Hle)
    clear Hle
    apply ENNReal.mul_pos
    · apply rpow_ne_zero_iff
      apply And.intro
      · left
        apply privComposeAdaptive_NonZeroNQ <;> aesop
      · left
        apply privComposeAdaptive_NonTopNQ <;> aesop
    · apply rpow_ne_zero_iff
      apply And.intro
      · left
        apply privComposeAdaptive_NonZeroNQ <;> aesop
      · left
        apply privComposeAdaptive_NonTopNQ <;> aesop
  case H2 =>
    apply ne_top_lt_top
    apply privComposeAdaptive_NonTopRDNQ
    · apply HNTRDNQ1
    · apply HNTRDNQ2
    · apply HNT1
    · apply HNT2
    · apply HNZ1
    · apply HNZ2
    · apply Hubound2
    · apply Hα
    · apply HN

  rw [left_distrib]
  rw [Real.exp_add]

  rw [RenyiDivergence_exp (nq1 l₁) (nq1 l₂) Hα ?H1 ?H2]
  case H1 =>
    rcases HU with ⟨ u0 ⟩
    have Hle : nq1 l₁ u0 ^ α * nq1 l₂ u0 ^ (1 - α) <= ∑' (x : U), nq1 l₁ x ^ α * nq1 l₂ x ^ (1 - α) :=  ENNReal.le_tsum u0
    apply (LE.le.trans_lt' Hle)
    clear Hle
    apply ENNReal.mul_pos
    · apply rpow_ne_zero_iff
      apply And.intro
      · left
        apply HNZ1
      · left
        apply HNT1
    · apply rpow_ne_zero_iff
      apply And.intro
      · left
        apply HNZ1
      · left
        apply HNT1
  case H2 =>
    apply ne_top_lt_top
    apply HNTRDNQ1 <;> aesop

  have hexp_b : ∀ u, (rexp ((α - 1) * RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) <= rexp ((α - 1) * b)) := by
    rw [RDBound] at Hubound
    intro u
    rcases (Hubound u) with ⟨ hb1 , hb2 ⟩
    apply Real.exp_le_exp_of_le
    aesop

  rw [mul_comm]
  rw [<- (ENNReal.toReal_ofReal_mul _ _ ?h)]
  case h =>
    exact exp_nonneg ((α - 1) * b)
  rw [mul_comm]
  rw [← ENNReal.tsum_mul_right]

  apply (toReal_mono' _ ?goal2)
  case goal2 =>
    intro H
    exfalso
    rw [ENNReal.tsum_mul_right] at H
    rw [mul_eq_top] at H
    cases H
    · rename_i h
      rcases h with ⟨ _ , h1 ⟩
      apply (@ENNReal.top_ne_ofReal (rexp ((α - 1) * b)))
      aesop
    · rename_i h
      rcases h with ⟨ h0 , _ ⟩
      apply (HNTRDNQ1 α Hα l₁ l₂ HN)
      apply h0

  apply (@LE.le.trans _ _ _ ((∑' (i : U), nq1 l₁ i ^ α * nq1 l₂ i ^ (1 - α) * ENNReal.ofReal (rexp ((α - 1) * RenyiDivergence (nq2 i l₁) (nq2 i l₂) α)))) _ _ ?goal2)
  case goal2 =>
    apply (tsum_le_tsum _ ENNReal.summable ENNReal.summable)
    intro i
    refine (ENNReal.mul_le_mul_left ?h.h.h0 ?h.h.hinf).mpr ?h.h.a
    · apply mul_ne_zero_iff.mpr
      apply And.intro
      · apply rpow_ne_zero_iff
        apply And.intro
        · left
          apply HNZ1
        · left
          apply HNT1
      · apply rpow_ne_zero_iff
        apply And.intro
        · left
          apply HNZ1
        · left
          apply HNT1
    · apply ENNReal.mul_ne_top
      · apply exp_non_top
        · apply HNZ1
        · apply HNT1
      · apply exp_non_top
        · apply HNZ1
        · apply HNT1
    · apply ENNReal.ofReal_le_ofReal
      apply hexp_b

  have GH1 : ∀ i, 0 < ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) := by
    intro i
    rcases HV with ⟨ v0 ⟩
    have Hle : nq2 i l₁ v0 ^ α * nq2 i l₂ v0 ^ (1 - α) <= ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) := ENNReal.le_tsum v0
    apply (LE.le.trans_lt' Hle)
    clear Hle
    apply ENNReal.mul_pos
    · have Hlt : (0 < nq2 i l₁ v0 ^ α) := by
        apply ENNReal.rpow_pos
        · exact pos_iff_ne_zero.mpr (HNZ2 i l₁ v0)
        · apply HNT2
      intro Hk
      aesop
    · have Hlt : (0 < nq2 i l₂ v0 ^ (1 - α)) := by
        apply ENNReal.rpow_pos
        · exact pos_iff_ne_zero.mpr (HNZ2 i l₂ v0)
        · exact HNT2 i l₂ v0
      intro Hk
      aesop

  have GH2 : ∀ i, ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) < ⊤ := by
    exact fun i => ne_top_lt_top (∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α)) (HNTRDNQ2 i α Hα l₁ l₂ HN)

  -- After this point the argument is tight
  apply Eq.le
  conv =>
    rhs
    congr
    intro i
    rw [RenyiDivergence_exp (nq2 i l₁) (nq2 i l₂) Hα]
    rfl
    · apply GH1
    · apply GH2

  conv =>
    lhs
    congr
    intro
    rw [privComposeChainRule]
    rw [privComposeChainRule]

  conv =>
    rhs
    congr
    intro x
    rw [<- (@ENNReal.ofReal_toReal (nq1 l₁ x ^ α * nq1 l₂ x ^ (1 - α)) ?goal2)]
    · rw [<- ENNReal.ofReal_mul]
      · rw [<- ENNReal.toReal_mul]
        rw [(@ENNReal.ofReal_toReal (nq1 l₁ x ^ α * nq1 l₂ x ^ (1 - α) * ∑' (x_1 : V), nq2 x l₁ x_1 ^ α * nq2 x l₂ x_1 ^ (1 - α)) ?goal4)]
        rfl
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply exp_non_top
            · apply HNZ1
            · apply HNT1
          · apply exp_non_top
            · apply HNZ1
            · apply HNT1
        · apply HNTRDNQ2
          apply Hα
          apply HN
      · apply ENNReal.toReal_nonneg
    · apply ENNReal.mul_ne_top
      · apply exp_non_top
        · apply HNZ1
        · apply HNT1
      · apply exp_non_top
        · apply HNZ1
        · apply HNT1

  conv =>
    rhs
    arg 1
    intro x
    rw [<- ENNReal.tsum_mul_left]

  rw [<- ENNReal.tsum_prod]
  congr
  apply funext
  intro p
  rcases p with ⟨ u , v ⟩
  simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ ?sc1]
  case sc1 => linarith
  rw [mul_rpow_of_ne_zero]
  · exact mul_mul_mul_comm (nq1 l₁ u ^ α) (nq2 u l₁ v ^ α) (nq1 l₂ u ^ (1 - α)) (nq2 u l₂ v ^ (1 - α))
  · apply HNZ1
  · apply HNZ2

/--
Adaptively Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privComposeAdaptive_zCDPBound {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : zCDPBound nq1 ((ε₁ : ℝ) / ε₂))  (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) (nn1 : NonZeroNQ nq1) (nn2 : ∀ u, NonZeroNQ (nq2 u)) (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nts1 : NonTopNQ nq1) (nts2 : ∀ u, NonTopNQ (nq2 u)) :
  zCDPBound (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ Hneighbours
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
  apply (privComposeAdaptive_renyi_bound _ Hα _ _)
  · aesop
  · aesop
  · aesop
  · aesop
  · apply RDBound_ofZCDPBound <;> aesop
  · apply RDBounded_ofZCDPBound <;> aesop
  · aesop
  · aesop
  · aesop

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privComposeAdaptive_zCDP (nq1 : List T → SLang U) (nq2 : U -> List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : zCDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : ∀ u, zCDP (nq2 u) ((ε₃ : ℝ) / ε₄))
  (Hubound_nq2 : ∃ (z : ℝ), ∀ (u : U), ∀ l, ∑'(v : V), nq2 u l v ≤ ENNReal.ofReal z) :
  zCDP (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  repeat any_goals constructor
  · apply privComposeAdaptive_zCDPBound <;> aesop
  · apply privComposeAdaptive_NonZeroNQ <;> aesop
  · apply privComposeAdaptive_NonTopSum
    · aesop
    · aesop
    · apply Hubound_nq2  -- Is there any way out of this? Only used in one place
    -- · apply (@RDBounded_ofZCDPBound _ _ _ nq2 ε₃ ε₄)
    --   · aesop
  · apply privComposeAdaptive_NonTopNQ <;> aesop
  · apply privComposeAdaptive_NonTopRDNQ
    · aesop
    · aesop
    · aesop
    · aesop
    · aesop
    · aesop
    · apply (@RDBounded_ofZCDPBound _ _ _ nq2 ε₃ ε₄)
      · aesop
end SLang
