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
  cases (Classical.em ((∑' (x : U), if x ∈ S then (m l₂) x else 0) = ⊤))
  · rename_i HT
    rw [HT]
    simp_all
    rw [ENNReal.mul_top']
    split <;> simp
    -- Edge case: 0-DP with SLang term that doens't normalize
    -- Does the same thing break the singleton event proof?
    sorry
  · rename_i HNT
    rw [ENNReal.div_le_iff_le_mul ?G1 ?G2] at h
    case G1 =>
      right
      simp
    case G2 =>
      left
      apply HNT
    apply le_trans h
    simp

-- set_option pp.coercions false


theorem ApproximateDP_of_zCDP (m : Mechanism T U) (ε : ℝ) (h : zCDPBound m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [zCDPBound] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h

  let α : Real := sorry

  -- Privacy loss random variable
  -- Move to RenyiDivergence file?
  let z (x : U) : EReal := ENNReal.elog ((m l₁ x) / (m l₂ x))
  have Hz (x : U) : z x = ENNReal.elog ((m l₁ x) / (m l₂ x)) := by rfl
  -- Instead of using an outer measure, I'll use a sum of Dirac measures, so we can turn the lintegral into a sum
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
        sorry
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
          have HK1'' : ↑ε ≤ z u  := by sorry
          simp
          rw [max_eq_left ?G1]
          case G1 =>
            -- Assumption
            sorry
          trivial
      · split
        · exfalso
          rename_i HK1 HK2
          apply HK1
          rw [ge_iff_le] at HK2
          apply ENNReal.eexp_mono_le.mp at HK2
          -- Doable
          sorry
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
    have SC1 : OfNat.ofNat 0 ≤ α.toEReal - OfNat.ofNat 1 := by sorry
    conv =>
      enter [1, 1, u]
      rw [Hz]
      rw [ENNReal.eexp_mul_nonneg SC1]
      simp

    -- Apply Renyi divergence inequality

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
    apply (ENNReal.div_le_iff ?G1 ?G2).mp
    case G1 =>
      -- Absolute continuity
      sorry
    case G2 =>
      -- Can split this off by cases first
      sorry

    -- Coercions lemma for eexp (that I need to do for the other lemma anyways?)
    simp at H
    rw [max_eq_left ?SC1] at H
    case SC1 =>
      -- epsilon ≥ 0
      sorry
    exact le_of_lt H
  apply (le_trans (add_le_add_right HDP _))
  clear HDP

  -- Conclude by simplification
  simp [add_comm]


end SLang
