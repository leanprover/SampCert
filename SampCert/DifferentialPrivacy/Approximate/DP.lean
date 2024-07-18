/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Neighbours
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.Util.Log


set_option linter.unusedTactic false

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP' (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) ≤ δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0)

def ApproximateDP (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  DP' m ε δ

-- def ApproximateDP_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
--   ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ x : U,
--   (m l₁ x) ≤ δ + ENNReal.ofReal (Real.exp ε) * (m l₂ x)
--
-- theorem ApproximateDP_singleton_to_event (m : Mechanism T U) (ε : ℝ) (δ : NNReal) (h : ApproximateDP_singleton m ε δ) :
--   ApproximateDP m ε δ := by
--   simp [ApproximateDP]
--   simp [ApproximateDP_singleton] at h
--   intros l₁ l₂ h1 S
--   replace h1 := h l₁ l₂ h1
--   have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0)  ≤ δ + ENNReal.ofReal ε.exp * (if x ∈ S then m l₂ x else 0) := by
--     aesop
--   have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
--     aesop
--   have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
--     intro b
--     right
--     simp
--     exact Real.exp_pos ε
--   have E := fun x : U => (A x)
--   have F := ENNReal.tsum_le_tsum E
--   apply le_trans F
--   -- I'm doubtful that that this is true when |U| > 1
--   sorry
--   -- rw [ENNReal.tsum_mul_left] at F
--   -- rw [← ENNReal.div_le_iff_le_mul] at F
--   -- . clear h1 A B C D
--   --   trivial
--   -- . aesop
--   -- . right
--   --   simp
--   --   exact Real.exp_pos ε
--
-- theorem approximate_event_to_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) (h : ApproximateDP m ε δ) :
--   ApproximateDP_singleton m ε δ := by
--   sorry
--   -- simp [DP_singleton]
--   -- simp [DP] at h
--   -- intros l₁ l₂ h1 x
--   -- replace h1 := h l₁ l₂ h1 {x}
--   -- simp at h1
--   -- rw [tsum_eq_single x] at h1
--   -- . simp at h1
--   --   rw [tsum_eq_single x] at h1
--   --   . simp at h1
--   --     trivial
--   --   . aesop
--   -- . aesop
--
-- theorem approximate_event_eq_singleton (m : Mechanism T U) (ε : ℝ) (δ : NNReal) :
--   ApproximateDP m ε δ ↔ ApproximateDP_singleton m ε δ := by
--   sorry
--   -- constructor
--   -- . apply event_to_singleton
--   -- . apply singleton_to_event





theorem ApproximateDP_of_DP (m : Mechanism T U) (ε : ℝ) (h : DP m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [DP] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h l₁ l₂ neighs S
  rw [ENNReal.div_le_iff_le_mul ?G1 ?G2] at h
  case G1 =>
    right
    simp
  case G2 =>
    left
    have H1 : (∑' (x : U), if x ∈ S then (m l₂) x else 0) ≤ (∑' (x : U), m l₂ x) := by
      apply ENNReal.tsum_le_tsum
      intro u
      split <;> simp
    rw [PMF.tsum_coe] at H1
    intro HK
    simp_all
  apply le_trans h
  simp

set_option pp.coercions false


theorem ApproximateDP_of_zCDP [Countable U] (m : Mechanism T U) (ε : ℝ) (Hε : 0 ≤ ε) (h : zCDPBound m ε) (Hm : ACNeighbour m) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [zCDPBound] at h
  simp [DP']
  intros δ l₁ l₂ neighs S

  -- Different value of α from the paper, since our definition of ε-zCDP is their (1/2)ε^2-zCDP
  let α : Real := (2 * ε + ε ^ 2 + ((2 * ε + ε^2) ^ 2 - 4 * ε^2 * (2*ε^2 + 2 * Real.log δ)) ^ (1 / 2)) / (2 * ε ^ 2)
  have Hα : (1 < α) := by
    sorry
  have Hα' : (0 < α.toEReal - 1) := by sorry
  have HαSpecial : ENNReal.eexp (((α - 1)) * ENNReal.ofReal (2⁻¹ * ε ^ 2 * α)) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) * ↑δ := by
    sorry



  -- Privacy loss random variable
  -- Move to RenyiDivergence file?
  let z (x : U) : EReal := ENNReal.elog ((m l₁ x) / (m l₂ x))
  have Hz (x : U) : z x = ENNReal.elog ((m l₁ x) / (m l₂ x)) := by rfl
  -- Instead of using an outer measure (like in PMF.toMeasure) I'll use a sum of Dirac measures,
  -- so we can turn the lintegral into a sum. The other wya might work too.
  let m1_measure_elt (u : U) : @MeasureTheory.Measure U ⊤ := m l₁ u • @MeasureTheory.Measure.dirac U ⊤ u
  let m1_measure : @MeasureTheory.Measure U ⊤ := MeasureTheory.Measure.sum m1_measure_elt
  have m1_measure_lintegral_sum (f : U -> ENNReal) :
       ∫⁻ (a : U), (f a) ∂m1_measure = ∑'(a : U), (m l₁ a * f a) := by
    rw [MeasureTheory.lintegral_sum_measure]
    apply tsum_congr
    intro u
    rw [MeasureTheory.lintegral_smul_measure]
    rw [@MeasureTheory.lintegral_dirac _]
  have m1_measure_eval (P : U -> Prop) :  m1_measure {x | P x} = ∑'(u : U), m l₁ u * if P u then 1 else 0 := by
    rw [MeasureTheory.Measure.sum_apply m1_measure_elt trivial]
    apply tsum_congr
    intro u
    rw [MeasureTheory.Measure.smul_apply]
    simp only [MeasurableSpace.measurableSet_top, MeasureTheory.Measure.dirac_apply', smul_eq_mul]
    rfl


  -- Separate the indicator function
  conv =>
    enter [1, 1, a]
    rw [<- mul_one ((m l₁) a)]
    rw [<- mul_zero ((m l₁) a)]
    rw [<- mul_ite]


  -- Multiply by indicator function for z
  have HK (x : U) : (1 : ENNReal) = (if (z x < ENNReal.ofReal ε) then 1 else 0) + (if (z x ≥ ENNReal.ofReal ε) then 1 else 0) := by
    split
    · simp
      rw [ite_eq_right_iff.mpr]
      · simp
      · intro
        exfalso
        rename_i h1 h2
        simp at h1
        have C : z x < z x := by exact gt_of_ge_of_gt h2 h1
        simp at C
    · simp
      rw [ite_eq_left_iff.mpr]
      simp
      apply le_of_not_lt
      trivial
  conv =>
    enter [1, 1, a]
    rw [<- mul_one (_ * _)]
    rw [mul_assoc]
    enter [2, 2]
    rw [HK a]
  clear HK

  -- Distribute
  conv =>
    enter [1, 1, a]
    rw [mul_add]
    rw [mul_add]
  rw [ENNReal.tsum_add]

  -- Bound right term above
  have HB :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a ≥ ENNReal.ofReal ε then 1 else 0) ≤
      ∑' (a : U), (m l₁) a * (if z a ≥ ENNReal.ofReal ε then 1 else 0) := by
    apply ENNReal.tsum_le_tsum
    intro x
    apply mul_le_mul'
    · rfl
    split
    · simp
    · simp
  apply (le_trans (add_le_add_left HB _))
  clear HB

  -- Bound right term above by Markov inequality
  have HMarkov : (∑' (a : U), (m l₁) a * if z a ≥ ENNReal.ofReal ε then 1 else 0) ≤ δ := by

    -- Markov inequality, specialized to discrete measure (m l₁)
    have HM :=
      @MeasureTheory.mul_meas_ge_le_lintegral₀ _ ⊤ m1_measure
        (fun (x : U) => ENNReal.eexp ((α - 1) * z x))
        ?HAEmeasurable
        (ENNReal.ofReal (Real.exp ((α - 1) * ε)))
    case HAEmeasurable => exact Measurable.aemeasurable fun ⦃t⦄ a => trivial
    rw [m1_measure_lintegral_sum] at HM
    rw [m1_measure_eval] at HM

    -- Convert between equivalent indicator functions
    have H (u : U) D D' :
        (@ite _ (ENNReal.ofReal (Real.exp ((α - 1) * ε)) ≤ ENNReal.eexp ((↑α - 1) * z u)) D (1 : ENNReal) 0) =
        (@ite _ (z u ≥ ↑(ENNReal.ofReal ε)) D' (1 : ENNReal) 0) := by
      split
      · split
        · rfl
        · exfalso
          rename_i HK1 HK2
          apply HK2
          simp only [ge_iff_le]
          have HK1' : ((α - 1) * ε ≤ (↑α - 1) * z u) := by exact ENNReal.eexp_mono_le.mpr HK1
          have HK1'' : ↑ε ≤ z u  := by
            apply ENNReal.ereal_smul_le_left (α - 1) ?SC1 ?SC2 HK1'
            case SC1 => apply Hα'
            case SC2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
          simp
          rw [max_eq_left Hε]
          trivial
      · split
        · exfalso
          rename_i HK1 HK2
          apply HK1
          rw [ge_iff_le] at HK2
          -- apply ENNReal.eexp_mono_le.mp at HK2
          rw [<- ENNReal.eexp_ofReal]
          apply ENNReal.eexp_mono_le.mp
          simp
          refine ENNReal.ereal_le_smul_left (α.toEReal - OfNat.ofNat 1) Hα' ?G1 ?G2
          case G1 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
          simp only [EReal.coe_ennreal_ofReal] at HK2
          rw [max_eq_left Hε] at HK2
          trivial
        · rfl
    conv at HM =>
      enter [1, 2, 1, u, 2]
      rw [H u]
    clear H

    -- Use the Markov inequality
    suffices ENNReal.ofReal (Real.exp ((α - 1) * ε)) * (∑' (a : U), (m l₁) a * if z a ≥ ↑(ENNReal.ofReal ε) then 1 else 0) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) * ↑δ by
      apply (ENNReal.mul_le_mul_left ?SC1 ?SC2).mp
      apply this
      case SC1 =>
        simp
        exact Real.exp_pos ((α - 1) * ε)
      case SC2 => exact ENNReal.ofReal_ne_top
    apply (le_trans ?G1 _)
    case G1 => apply HM
    clear HM
    clear HM

    -- Rewrite z and simplify
    conv =>
      enter [1, 1, u]
      rw [Hz]
      rw [ENNReal.eexp_mul_nonneg (le_of_lt Hα')]
      simp

    -- Apply Renyi divergence inequality
    have h := h α Hα l₁ l₂ neighs
    rw [RenyiDivergence] at h
    apply (le_trans _ HαSpecial)

    have H (u : U) : (m l₁) u * ((m l₁) u / (m l₂) u) ^ (α.toEReal - 1).toReal =
                     ((m l₁) u) ^ α * ((m l₂) u) ^ (1 - α) := by sorry
    conv =>
      enter [1, 1, u]
      rw [H u]
    clear H
    rw [<- RenyiDivergence_def_exp _ _ Hα]
    apply ENNReal.eexp_mono_le.mp
    refine ENNReal.ereal_le_smul_left (↑α - 1) ?Hr1 ?Hr2 ?H
    case Hr1 => exact Hα'
    case Hr2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    rw [<- ENNReal.ofEReal_ofReal_toENNReal] at h
    apply ENNReal.ofEReal_le_mono_conv_nonneg at h
    · apply (le_trans h)
      rw [EReal.coe_mul]
      rw [ENNReal.ofReal_mul ?G1]
      case G1 => sorry
      rw [ENNReal.ofReal_mul ?G1]
      case G1 => sorry
      rw [EReal.coe_mul]
      simp
      apply Eq.le
      congr 1
      · congr 1
        rw [← EReal.coe_pow]
        congr
        rw [max_eq_left]
        exact sq_nonneg ε
      · congr 1
        rw [max_eq_left]
        linarith
    · apply @RenyiDivergence_def_nonneg U ⊤ ?G1 _ (m l₁) (m l₂) (Hm l₁ l₂ neighs) _ Hα
      sorry
  apply (le_trans (add_le_add_left HMarkov _))
  clear HMarkov

  -- Bound left term above
  have HDP :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a < ENNReal.ofReal ε then 1 else 0) ≤
      ENNReal.ofReal (Real.exp ε) * ∑' (a : U), (m l₂) a * (if a ∈ S then 1 else 0) := by
    -- Eliminate the indicator function
    rw [<- ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro u

    -- Eliminate edge case by absolute continuity
    cases (Classical.em ((m l₂) u = 0))
    · have Hz : (m l₁ u = 0) := by
        rename_i h
        exact Hm l₁ l₂ neighs u h
      simp_all
    rename_i hnz

    conv =>
      congr
      · rw [mul_comm]
        rw [mul_assoc]
      · rw [mul_comm]
        enter [1]
        rw [mul_comm]
    rw [mul_assoc]
    apply mul_le_mul'
    · rfl
    split <;> simp
    rename_i H
    rw [Hz] at H
    apply ENNReal.eexp_mono_lt.mp at H
    simp only [ENNReal.elog_eexp] at H
    rw [mul_comm]
    cases (Classical.em (DFunLike.coe (m l₂) u = ⊤))
    · simp_all
    rename_i Hnt
    apply (ENNReal.div_le_iff hnz Hnt).mp
    simp at H
    rw [max_eq_left Hε] at H
    exact le_of_lt H
  apply (le_trans (add_le_add_right HDP _))
  clear HDP

  -- Conclude by simplification
  simp [add_comm]


end SLang
