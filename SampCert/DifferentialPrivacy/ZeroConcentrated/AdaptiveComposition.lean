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


-- def NQBounded (nq2 : U -> List T -> SLang V) (b : ENNReal) : Prop :=
--   ∃ b, ∀ u, ∀ l, ∀ v, nq2 u l v <= b < ⊤


-- Morally, b = ⨆ (u : U), RenyiDivergence .... However, iSup itself does not remember that the supremum
-- exists, setting the value to zero if not.
def RDBounded (nq2 : U -> List T -> SLang V) (α : ℝ) (Hα : 1 < α) (l₁ l₂ : List T) (HN : Neighbour l₁ l₂) (b : ℝ): Prop :=
  ∀ u, (0 < RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) ∧ (RenyiDivergence (nq2 u l₁) (nq2 u l₂) α ≤ b)

lemma RDBounded_ofZCDPBound {nq2 : U -> List T → SLang V} {ε₃ ε₄ : ℕ+} (α : ℝ) (Hα : 1 < α) (l₁ l₂ : List T) (HN : Neighbour l₁ l₂)
  (h2 : ∀ u, zCDPBound (nq2 u) ((ε₃ : ℝ) / ε₄)) : RDBounded nq2 α Hα l₁ l₂ HN (⨆ (u : U), RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  rw [RDBounded]
  intro u
  apply And.intro
  · sorry
  · sorry




-- set_option pp.all true
-- Maybe would be better as ENNReal?
lemma iSup_smul_l (a : ℝ) (Ha : 0 <= a) (f : U -> ℝ) : a * ⨆ u, f u = ⨆ u, a * f u := by
  refine (mul_iSup_of_nonneg ?ha fun i => f i)
  apply Ha


-- def funlike_inst : FunLike (ℝ → ℝ) ℝ ℝ := by
--   constructor
--   case coe =>
--     intro f
--     apply f
--   case coe_injective' =>
--     exact fun ⦃a₁ a₂⦄ a => a

-- set_option pp.all true
lemma iSup_exp (f : U -> ℝ) : ⨆ u, Real.exp (f u) = Real.exp (⨆ u, f u) := by
  sorry
  -- apply (@map_iSup (ℝ -> ℝ) ℝ ℝ U funlike_inst _ _ ?SHC rexp f)
  -- · -- sSupHomClass
  --   -- refine { map_sSup := ?SHC.map_sSup : @sSupHomClass (ℝ -> ℝ) ℝ ℝ _ _ _ funlike_inst}
  --   -- May be circular
  --   sorry

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

/--
Bound on Renyi divergence on adaptively composed queries
-/
lemma privComposeAdaptive_renyi_bound {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (α : ℝ) (Hα : 1 < α)
  (HNT1 : NonTopNQ nq1) (HNTRDNQ1 : NonTopRDNQ nq1) (HNTRDNQ2 : ∀ u, NonTopRDNQ (nq2 u))
  (HN : Neighbour l₁ l₂) (HNZ1 : NonZeroNQ nq1) (HNZ2 : ∀ u, NonZeroNQ (nq2 u))
  (b : ℝ)
  (Hubound : RDBounded nq2 α Hα l₁ l₂ HN b) :
  RenyiDivergence (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) α ≤
    RenyiDivergence (nq1 l₁) (nq1 l₂) α + b := by
  sorry

  -- apply (RenyiDivergence_mono_sum _ _ α Hα)
  -- rw [RenyiDivergence_exp (privComposeAdaptive nq1 nq2 l₁) (privComposeAdaptive nq1 nq2 l₂) Hα ?H1 ?H2]
  -- case H1 =>
  --   rcases HV with ⟨ v0 ⟩
  --   rcases HU with ⟨ u0 ⟩
  --   have Hle : (privComposeAdaptive nq1 nq2 l₁ (u0, v0) ^ α * privComposeAdaptive nq1 nq2 l₂ (u0, v0) ^ (1 - α)) ≤ (∑' (x : U × V), privComposeAdaptive nq1 nq2 l₁ x ^ α * privComposeAdaptive nq1 nq2 l₂ x ^ (1 - α)) := by
  --     exact ENNReal.le_tsum (u0, v0)
  --   apply (LE.le.trans_lt' Hle)
  --   clear Hle
  --   apply ENNReal.mul_pos
  --   · sorry
  --   · sorry
  -- case H2 => sorry
  -- rw [left_distrib]
  -- rw [Real.exp_add]

  -- rw [RenyiDivergence_exp (nq1 l₁) (nq1 l₂) Hα ?H1 ?H2]
  -- case H1 => sorry
  -- case H2 => sorry

  -- have hmono_1 : rexp ((α - 1) * ⨆ u, RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) = ⨆ u, rexp ((α - 1) * RenyiDivergence (nq2 u l₁) (nq2 u l₂) α) := by
  --   rw [iSup_smul_l]
  --   rw [iSup_exp]
  --   linarith
  -- rw [hmono_1]
  -- clear hmono_1

  -- rw [mul_comm]
  -- rw [<- (ENNReal.toReal_ofReal_mul _ _ ?h)]
  -- case h =>
  --   refine Real.iSup_nonneg ?hf
  --   intro i
  --   exact exp_nonneg ((α - 1) * RenyiDivergence (nq2 i l₁) (nq2 i l₂) α)
  -- rw [mul_comm]
  -- rw [← ENNReal.tsum_mul_right]

  -- apply (toReal_mono' _ ?goal2)
  -- case goal2 =>
  --   intro H
  --   exfalso
  --   rw [ENNReal.tsum_mul_right] at H
  --   rw [mul_eq_top] at H
  --   cases H
  --   · aesop
  --   · aesop

  -- apply (@LE.le.trans _ _ _ ((∑' (i : U), nq1 l₁ i ^ α * nq1 l₂ i ^ (1 - α) * ENNReal.ofReal (rexp ((α - 1) * RenyiDivergence (nq2 i l₁) (nq2 i l₂) α)))) _ _ ?goal2)
  -- case goal2 =>
  --   apply (tsum_le_tsum _ ENNReal.summable ENNReal.summable)
  --   intro i
  --   refine (ENNReal.mul_le_mul_left ?h.h.h0 ?h.h.hinf).mpr ?h.h.a
  --   · apply mul_ne_zero_iff.mpr
  --     apply And.intro
  --     · sorry
  --     · sorry
  --   · apply ENNReal.mul_ne_top
  --     · apply exp_non_top
  --       · apply HNZ1
  --       · apply HNT1
  --     · apply exp_non_top
  --       · apply HNZ1
  --       · apply HNT1
  --   · apply ENNReal.ofReal_le_ofReal
  --     rw [iSup_exp]
  --     rw [<- iSup_smul_l]
  --     · -- Should be easy
  --       -- Definitely easy w/ bounded assumption
  --       sorry
  --     · linarith
  -- have GH1 : ∀ i, 0 < ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) := by
  --   intro i
  --   rcases HV with ⟨ v0 ⟩
  --   have Hle : nq2 i l₁ v0 ^ α * nq2 i l₂ v0 ^ (1 - α) <= ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) := ENNReal.le_tsum v0
  --   apply (LE.le.trans_lt' Hle)
  --   clear Hle
  --   apply ENNReal.mul_pos
  --   · have Hlt : (0 < nq2 i l₁ v0 ^ α) := by
  --       apply ENNReal.rpow_pos
  --       · sorry
  --       · sorry
  --     intro Hk
  --     aesop
  --   · have Hlt : (0 < nq2 i l₂ v0 ^ (1 - α)) := by
  --       apply ENNReal.rpow_pos
  --       · sorry
  --       · sorry
  --     intro Hk
  --     aesop

  -- have GH2 : ∀ i, ∑' (x : V), nq2 i l₁ x ^ α * nq2 i l₂ x ^ (1 - α) < ⊤ := by
  --   sorry

  -- -- After this point the argument is tight
  -- apply Eq.le
  -- conv =>
  --   rhs
  --   congr
  --   intro i
  --   rw [RenyiDivergence_exp (nq2 i l₁) (nq2 i l₂) Hα]
  --   rfl
  --   · apply GH1
  --   · apply GH2

  -- conv =>
  --   lhs
  --   congr
  --   intro
  --   rw [privComposeChainRule]
  --   rw [privComposeChainRule]

  -- conv =>
  --   rhs
  --   congr
  --   intro x
  --   rw [<- (@ENNReal.ofReal_toReal (nq1 l₁ x ^ α * nq1 l₂ x ^ (1 - α)) ?goal2)]
  --   · rw [<- ENNReal.ofReal_mul]
  --     · rw [<- ENNReal.toReal_mul]
  --       rw [(@ENNReal.ofReal_toReal (nq1 l₁ x ^ α * nq1 l₂ x ^ (1 - α) * ∑' (x_1 : V), nq2 x l₁ x_1 ^ α * nq2 x l₂ x_1 ^ (1 - α)) ?goal4)]
  --       rfl
  --       apply ENNReal.mul_ne_top
  --       · apply ENNReal.mul_ne_top
  --         · apply exp_non_top
  --           · apply HNZ1
  --           · apply HNT1
  --         · apply exp_non_top
  --           · apply HNZ1
  --           · apply HNT1
  --       · apply HNTRDNQ2
  --         apply Hα
  --         apply HN
  --     · apply ENNReal.toReal_nonneg
  --   · apply ENNReal.mul_ne_top
  --     · apply exp_non_top
  --       · apply HNZ1
  --       · apply HNT1
  --     · apply exp_non_top
  --       · apply HNZ1
  --       · apply HNT1

  -- conv =>
  --   rhs
  --   arg 1
  --   intro x
  --   rw [<- ENNReal.tsum_mul_left]

  -- rw [<- ENNReal.tsum_prod]
  -- congr
  -- apply funext
  -- intro p
  -- rcases p with ⟨ u , v ⟩
  -- simp
  -- rw [ENNReal.mul_rpow_of_nonneg _ _ ?sc1]
  -- case sc1 => linarith
  -- rw [mul_rpow_of_ne_zero]
  -- · exact mul_mul_mul_comm (nq1 l₁ u ^ α) (nq2 u l₁ v ^ α) (nq1 l₂ u ^ (1 - α)) (nq2 u l₂ v ^ (1 - α))
  -- · apply HNZ1
  -- · apply HNZ2

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
  · apply RDBounded_ofZCDPBound <;> aesop
  · aesop
  · aesop
  · aesop


/--
All outputs of a adaptive composed query have finite probability.
-/
theorem privComposeAdaptive_NonTopNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopNQ nq1) (nt2 : ∀ u, NonTopNQ (nq2 u)) :
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
theorem privComposeAdaptive_NonTopSum {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopSum nq1) (nt2 : ∀ u, NonTopSum (nq2 u)) :
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

  -- Might need the second query to be bounded above

  sorry
  -- rw [ENNReal.tsum_mul_right]
  -- rw [mul_eq_top]
  -- intro H
  -- cases H
  -- . rename_i H
  --   cases H
  --   contradiction
  -- . rename_i H
  --   cases H
  --   contradiction



/--
Renyi divergence beteeen adaptive composed queries on neighbours are finite.
-/
theorem privComposeAdaptive_NonTopRDNQ {nq1 : List T → SLang U} {nq2 : U -> List T → SLang V} (nt1 : NonTopRDNQ nq1) (nt2 : ∀ u, NonTopRDNQ (nq2 u)) (nn1 : NonTopNQ nq1) (nn2 : ∀ u, NonTopNQ (nq2 u)) :
  NonTopRDNQ (privComposeAdaptive nq1 nq2) := by
  rw [NonTopRDNQ] at *
  intro α h1 l₁ l₂ h2
  -- replace nt1 := nt1 α h1 l₁ l₂ h2
  -- replace nt2 := nt2 α h1 l₁ l₂ h2
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
  sorry

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privComposeAdaptive_zCDP (nq1 : List T → SLang U) (nq2 : U -> List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : zCDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : ∀ u, zCDP (nq2 u) ((ε₃ : ℝ) / ε₄)) :
  zCDP (privComposeAdaptive nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  repeat any_goals constructor
  · apply privComposeAdaptive_zCDPBound <;> aesop
  · apply privComposeAdaptive_NonZeroNQ <;> aesop
  · apply privComposeAdaptive_NonTopSum <;> aesop
  · apply privComposeAdaptive_NonTopNQ <;> aesop
  · apply privComposeAdaptive_NonTopRDNQ <;> aesop

end SLang
