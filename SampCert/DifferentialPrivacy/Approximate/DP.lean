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

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP' (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) ≤ δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0)

def ApproximateDP (m : Mechanism T U) (ε : ℝ) (δ : NNReal) : Prop :=
  DP' m ε δ

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


theorem ApproximateDP_of_zCDP [Countable U] (m : Mechanism T U)
  (ε : ℝ) (Hε_pos : 0 < ε) (h : zCDPBound m ε) (Hm : ACNeighbour m) :
  ∀ δ : NNReal, (0 < (δ : ℝ)) -> ((δ : ℝ) < 1) -> DP' m (ε^2/2 + ε * (2*Real.log (1/δ))^(1/2 : ℝ)) δ := by
  -- FIXME: Can I reduce the δ = 0 or the δ ≥ 1 cases or the ε=0 case?
  have Hε : 0 ≤ ε := by exact le_of_lt Hε_pos
  intro δ Hδ0 Hδ1
  generalize Dε' : (ε^2/2 + ε * (2*Real.log (1/δ))^(1/2 : ℝ)) = ε'
  simp [zCDPBound] at h
  simp [DP']
  have Hε' : 0 ≤ ε' := by
    rw [<- Dε']
    apply add_nonneg
    · apply div_nonneg
      · apply sq_nonneg
      · simp
    · apply mul_nonneg
      · trivial
      · apply Real.rpow_nonneg
        apply mul_nonneg
        · simp
        · apply Real.log_nonneg
          apply one_le_one_div Hδ0
          exact le_of_lt Hδ1
  intros l₁ l₂ neighs S


  -- Different value of α from the paper, since our definition of ε-zCDP is their (1/2)ε^2-zCDP
  let α : Real := ((1 / ε) * (2*Real.log (1/δ))^(1/2 : ℝ)) + 1
  have Dα : α = (((1 / ε) * (2*Real.log (1/δ))^(1/2 : ℝ)) + 1 : ℝ) := by rfl
  have Hα : (1 < α) := by
    rw [Dα]
    conv =>
      lhs
      rw [<- zero_add 1]
    apply (add_lt_add_iff_right 1).mpr
    conv =>
      lhs
      rw [<- mul_zero 0]
    apply mul_lt_mul_of_nonneg_of_pos
    · apply one_div_pos.mpr
      trivial
    · apply Real.rpow_nonneg
      apply mul_nonneg
      · simp
      · apply Real.log_nonneg
        apply one_le_one_div Hδ0
        exact le_of_lt Hδ1
    · simp
    · apply Real.rpow_pos_of_pos
      apply Real.mul_pos
      · simp
      · apply Real.log_pos
        apply one_lt_one_div
        · apply Hδ0
        · trivial
  have Hα' : (0 < α.toEReal - 1) := by
    rw [EReal.coe_add]
    simp only [one_div, mul_neg, EReal.coe_mul, EReal.coe_one]
    rw [add_sub_assoc]
    have HZ : (1 - 1 : EReal) = 0 := by
      rw [← EReal.coe_one]
      rw [← EReal.coe_sub]
      simp
    rw [HZ]
    simp only [mul_neg, add_zero, gt_iff_lt]
    apply EReal.mul_pos
    · apply EReal.coe_pos.mpr
      exact inv_pos_of_pos Hε_pos
    · apply EReal.coe_pos.mpr
      apply Real.rpow_pos_of_pos
      apply Real.mul_pos
      · simp
      · apply Real.log_pos
        exact one_lt_inv Hδ0 Hδ1
  have HαSpecial : ENNReal.eexp (((α - 1)) * ENNReal.ofReal (2⁻¹ * ε ^ 2 * α)) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε')) * ↑δ := by
    apply Eq.le
    rw [Dα]
    -- Cancel 1 - 1
    conv =>
      enter [1, 1, 1]
      simp
      rw [add_sub_assoc]
      rw [← EReal.coe_one]
      rw [← EReal.coe_sub]
      simp
    conv =>
      enter [2, 1, 1, 1, 1]
      simp
    simp only [one_div, EReal.coe_ennreal_ofReal]
    repeat rw [← EReal.coe_mul]
    rw [ENNReal.eexp_ofReal]
    rw [ENNReal.ofReal]
    rw [ENNReal.ofReal]
    rw [← ENNReal.coe_mul]
    congr 1
    rw [<- @Real.toNNReal_coe δ]
    rw [<- Real.toNNReal_mul ?G1]
    case G1 => apply Real.exp_nonneg
    congr 1
    conv =>
      enter [2, 2]
      rw [<- @Real.exp_log (δ.toReal) Hδ0]
    conv =>
      enter [2]
      rw [<- Real.exp_add]
    congr 1
    simp only [Real.toNNReal_coe]
    rw [max_eq_left ?G5]
    case G5 =>
      apply mul_nonneg
      · apply mul_nonneg
        · simp
        · apply sq_nonneg
      · apply add_nonneg
        · apply mul_nonneg
          · apply inv_nonneg_of_nonneg
            trivial
          · apply Real.rpow_nonneg
            apply mul_nonneg
            · simp
            · apply Real.log_nonneg
              apply one_le_inv Hδ0
              exact le_of_lt Hδ1
        · simp
    rw [<- Dε']
    simp
    repeat rw [mul_add]


    have SC1 : 0 < -(2 * Real.log δ.toReal) := by
      simp
      apply mul_neg_of_pos_of_neg
      · simp
      · exact Real.log_neg Hδ0 Hδ1

    -- Cancel square roots
    conv =>
      congr
      · congr
        · skip
          rw [mul_comm]
          repeat rw [mul_assoc]
          enter [2, 2, 2]
          rw [mul_comm]
          rw [mul_assoc]
          enter [2]
          rw [<- Real.rpow_add SC1]
          rw [<- two_mul]
          simp
        · simp
      · enter [1, 2]
        repeat rw [mul_assoc]
        enter [2]
        rw [mul_comm]
        rw [mul_assoc]
        enter [2]
        rw [<- Real.rpow_add SC1]
        rw [<- two_mul]
        simp
    clear SC1

    have SC1 : ε ≠ 0 := by linarith
    conv =>
      congr
      · congr
        · enter [2]
          repeat rw [<- mul_assoc]
          enter [1]
          rw [sq]
          simp
          rw [mul_inv_cancel SC1]
        · rw [sq]
          rw [mul_comm]
          repeat rw [mul_assoc]
          enter [2, 2]
          repeat rw [<- mul_assoc]
          enter [1]
          rw [mul_inv_cancel SC1]
          skip
      · enter [1]
        congr
        · rw [division_def]
          rw [sq]
          repeat rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          enter [2]
          rw [mul_comm]
          repeat rw [<- mul_assoc]
          enter [1, 1]
          rw [inv_mul_cancel SC1]
          skip
        · repeat rw [<- mul_assoc]
          rw [inv_mul_cancel SC1]
          simp
    clear SC1
    simp

    -- Quality of life
    have R1 : (-(2 * Real.log δ.toReal)) = 2 * Real.log (1/δ.toReal) := by simp
    rw [R1]
    have R2 : (-Real.log δ.toReal) = Real.log (1/δ.toReal) := by simp
    rw [R2]
    generalize HD : Real.log (1 / δ.toReal) = D
    have HDnn : 0 ≤ D := by
      rw [<- HD]
      apply Real.log_nonneg
      apply one_le_one_div Hδ0
      exact le_of_lt Hδ1
    clear R1 R2

    -- Simplify more
    conv =>
      congr
      · rw [Real.mul_rpow (by simp) HDnn]
        enter [2]
        repeat rw [<- mul_assoc]
        enter [1]
        rw [mul_comm]
        rw [<- mul_assoc]
        enter [1]
        rw [<- Real.rpow_neg_one]
        rw [<- Real.rpow_add (by simp)]
      · rw [Real.mul_rpow (by simp) HDnn]
        enter [1, 1]
        rw [mul_comm]
        repeat rw [mul_assoc]
        enter [2]
        repeat rw [<- mul_assoc]
        enter [1]
        rw [<- Real.rpow_neg_one]
        rw [<- Real.rpow_add (by simp)]
        rw [add_comm]

    generalize HW : (2 : ℝ) ^ ((2 : ℝ) ^ (-(1 : ℝ)) + -(1 : ℝ) : ℝ) = W
    -- Cancel the ε * W * D terms
    conv =>
      enter [1]
      rw [add_comm]
      enter [1, 1]
      rw [mul_comm]
    conv =>
      enter [2, 1, 1]
      repeat rw [<- mul_assoc]
    rw [add_assoc]
    congr 1
    clear HW W

    -- Cancel the D terms
    rw [<- one_add_one_eq_two]
    rw [add_mul]
    rw [<- HD]
    simp


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
  have HK (x : U) : (1 : ENNReal) = (if (z x < ENNReal.ofReal ε') then 1 else 0) + (if (z x ≥ ENNReal.ofReal ε') then 1 else 0) := by
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
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a ≥ ENNReal.ofReal ε' then 1 else 0) ≤
      ∑' (a : U), (m l₁) a * (if z a ≥ ENNReal.ofReal ε' then 1 else 0) := by
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
  --  Pr[Z > ε'] ≤ δ
  have HMarkov : (∑' (a : U), (m l₁) a * if z a ≥ ENNReal.ofReal ε' then 1 else 0) ≤ δ := by

    -- Markov inequality, specialized to discrete measure (m l₁)
    have HM :=
      @MeasureTheory.mul_meas_ge_le_lintegral₀ _ ⊤ m1_measure
        (fun (x : U) => ENNReal.eexp ((α - 1) * z x))
        ?HAEmeasurable
        (ENNReal.ofReal (Real.exp ((α - 1) * ε')))
    case HAEmeasurable => exact Measurable.aemeasurable fun ⦃t⦄ _ => trivial
    rw [m1_measure_lintegral_sum] at HM
    rw [m1_measure_eval] at HM

    -- Convert between equivalent indicator functions
    have H (u : U) D D' :
        (@ite _ (ENNReal.ofReal (Real.exp ((α - 1) * ε')) ≤ ENNReal.eexp ((↑α - 1) * z u)) D (1 : ENNReal) 0) =
        (@ite _ (z u ≥ ↑(ENNReal.ofReal ε')) D' (1 : ENNReal) 0) := by
      split
      · split
        · rfl
        · exfalso
          rename_i HK1 HK2
          apply HK2
          simp only [ge_iff_le]
          have HK1' : ((α - 1) * ε' ≤ (↑α - 1) * z u) := by exact ENNReal.eexp_mono_le.mpr HK1
          have HK1'' : ↑ε' ≤ z u  := by
            apply ENNReal.ereal_smul_le_left (α - 1) ?SC1 ?SC2 HK1'
            case SC1 => apply Hα'
            case SC2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
          simp
          rw [max_eq_left]
          · trivial
          linarith
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
          rw [max_eq_left] at HK2
          · trivial
          linarith
        · rfl
    conv at HM =>
      enter [1, 2, 1, u, 2]
      rw [H u]
    clear H

    -- Use the Markov inequality
    suffices ENNReal.ofReal (Real.exp ((α - 1) * ε')) * (∑' (a : U), (m l₁) a * if z a ≥ ↑(ENNReal.ofReal ε') then 1 else 0) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε')) * ↑δ by
      apply (ENNReal.mul_le_mul_left ?SC1 ?SC2).mp
      apply this
      case SC1 =>
        simp
        apply Real.exp_pos
      case SC2 => exact ENNReal.ofReal_ne_top
    apply (le_trans ?G1 _)
    case G1 => apply HM
    clear HM
    clear HM

    -- Rewrite z and simplify
    conv =>
      enter [1, 1, u]
      rw [Hz]
      rw [ENNReal.eexp_mul_nonneg (le_of_lt Hα') (by exact Ne.symm (ne_of_beq_false rfl))]
      simp

    -- Apply Renyi divergence inequality
    have h := h α Hα l₁ l₂ neighs
    rw [RenyiDivergence] at h
    apply (le_trans _ HαSpecial)

    -- After this point the bound should be as tight as it's going to get

    have H (u : U) : (m l₁) u * ((m l₁) u / (m l₂) u) ^ (α.toEReal - 1).toReal =
                     ((m l₁) u) ^ α * ((m l₂) u) ^ (1 - α) := by
      cases (Classical.em ((m l₂) u = 0))
      · rename_i HZ2
        have HZ1 : (m l₁ u = 0) := by exact Hm l₁ l₂ neighs u HZ2
        simp [HZ2, HZ1]
        left
        linarith
      · rw [division_def]
        rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G3]
        case G1 => exact PMF.apply_ne_top (m l₁) u
        case G3 =>
          apply ENNReal.inv_ne_top.mpr
          trivial
        rw [<- mul_assoc]
        congr 1
        · conv =>
            enter [1, 1]
            rw [<- ENNReal.rpow_one ((m l₁) u)]
          rw [<- (ENNReal.rpow_add 1 _ ?G1 ?G3)]
          case G1 =>
            intro HK
            rename_i HK1
            apply HK1
            apply (Hm l₂ l₁ (Neighbour_symm l₁ l₂ neighs))
            trivial
          case G3 => exact PMF.apply_ne_top (m l₁) u
          congr 1
          exact add_eq_of_eq_sub' rfl
        · rw [<- ENNReal.rpow_neg_one]
          rw [← ENNReal.rpow_mul]
          congr
          simp
          rw [neg_eq_iff_add_eq_zero]
          rw [EReal.toReal_sub]
          all_goals (try simp)
          · exact ne_of_beq_false rfl
          · exact EReal.add_top_iff_ne_bot.mp rfl
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
      case G1 =>
        apply mul_nonneg
        · simp
        · exact sq_nonneg ε
      rw [ENNReal.ofReal_mul ?G1]
      case G1 => simp
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
      infer_instance
    · simp
      apply mul_nonneg
      · apply mul_nonneg
        · apply EReal.coe_nonneg.mpr
          apply inv_nonneg_of_nonneg
          exact zero_le_two
        · rw [sq]
          apply mul_nonneg <;> exact EReal.coe_nonneg.mpr Hε
      · apply EReal.coe_nonneg.mpr
        linarith
  apply (le_trans (add_le_add_left HMarkov _))
  clear HMarkov




  -- Bound left term above
  have HDP :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a < ENNReal.ofReal ε' then 1 else 0) ≤
      ENNReal.ofReal (Real.exp ε') * ∑' (a : U), (m l₂) a * (if a ∈ S then 1 else 0) := by
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
      -- rw [ENNReal.mul_top']
      -- split
      -- · exfalso
      --   rename_i Hk
      --   apply ENNReal.ofReal_eq_zero.mp at Hk
      --   have Hk1 : 0 < Real.exp ε' := by exact Real.exp_pos ε'
      --   linarith
      -- · exact OrderTop.le_top ((m l₁) u)
    rename_i Hnt
    apply (ENNReal.div_le_iff hnz Hnt).mp
    simp at H
    rw [max_eq_left ?G5] at H
    case G5 => linarith
    exact le_of_lt H
  apply (le_trans (add_le_add_right HDP _))
  clear HDP

  -- Conclude by simplification
  simp [add_comm]

end SLang
