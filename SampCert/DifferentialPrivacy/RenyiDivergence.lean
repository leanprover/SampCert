/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import SampCert.Util.Log
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.Integral

/-! Renyi Divergence

This file defines the Renyi divergence and equations for evaluating its expectation.
-/


open Real ENNReal PMF Nat Int MeasureTheory Measure PMF
open Classical

/--
Simplified consequence of absolute continuity (remove me?)
-/
def AbsCts (p q : T -> ENNReal) : Prop := ∀ x : T, q x = 0 -> p x = 0

/--
Specialize the definitation of AbsolutelyContinuous when singletons are measurable
-/
lemma PMF_AbsCts [MeasurableSpace T] [MeasurableSingletonClass T] (p q : PMF T) (H : AbsolutelyContinuous (PMF.toMeasure p) (PMF.toMeasure q)) : AbsCts p q := by
  rw [AbsolutelyContinuous] at H
  rw [AbsCts]
  intro x Hx
  have Hxm : q.toMeasure { x } = 0 := by
    rw [toMeasure]
    simp
    apply (toOuterMeasure_apply_eq_zero_iff q {x}).mpr
    exact Set.disjoint_singleton_right.mpr fun a => a Hx
  have H := H Hxm
  rw [toMeasure] at H
  simp at *
  have Hp : Disjoint p.support {x} := (toOuterMeasure_apply_eq_zero_iff p {x}).mp H
  simp at Hp
  assumption

lemma PMF_mul_mul_inv_eq_mul_cancel (p q : PMF T) (HA : AbsCts p q) (a : T) : (p a  / q a) * q a = p a := by
  apply mul_mul_inv_eq_mul_cancel
  · rw [AbsCts] at HA
    intro
    simp_all
  · simp
    have HK : (q a ≠ ⊤) := apply_ne_top q a
    simp_all only [ne_eq, not_false_eq_true]
    simp

variable {T : Type}

/--
Definition of the Renyi divergence as an EReal.
-/
noncomputable def RenyiDivergence_def (p q : PMF T) (α : ℝ) : EReal :=
  (α - 1)⁻¹  * (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))

/--
Equation for the Renyi divergence series in terms of the Renyi Divergence
-/
lemma RenyiDivergence_def_exp (p q : PMF T) {α : ℝ} (h : 1 < α) :
  eexp (((α - 1)) * RenyiDivergence_def p q α) = (∑' x : T, (p x)^α * (q x)^(1 - α)) := by
  rw [RenyiDivergence_def]
  rw [<- mul_assoc]
  have H1 : (α.toEReal - OfNat.ofNat 1) =  (α - OfNat.ofNat 1).toEReal := by
    rw [EReal.coe_sub]
    congr
  have H2 : ((α.toEReal - OfNat.ofNat 1) * (α - OfNat.ofNat 1)⁻¹.toEReal = 1) := by
    rw [H1]
    rw [← EReal.coe_mul]
    rw [mul_inv_cancel]
    · simp
    · linarith
  simp [H2]


/--
Closed form of the series in the definition of the Renyi divergence.
-/
theorem RenyiDivergenceExpectation (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
  (∑' x : T, (p x)^α  * (q x)^(1 - α)) = ∑' x: T, (p x / q x)^α  * (q x) := by
  congr 4
  ext x
  rw [AbsCts] at H
  generalize Hvq : q x = vq
  cases vq <;> simp
  · -- q x = ⊤
    rw [ENNReal.zero_rpow_of_pos ?H]
    case H => linarith
    simp
    right
    apply h
  · rename_i vq'
    cases (Classical.em (vq' = 0))
    · -- q x = 0
      -- by abs. cty. p x = 0
      rename_i Hvq'
      have Hp : p x = 0 := by
        apply H
        simp [Hvq, Hvq']
      simp [Hp, Hvq', Hvq]
      left
      linarith
    · -- q x ∈ ℝ+
      rename_i Hvq'
      generalize Hvp : p x = vp
      cases vp <;> simp
      · -- q x ∈ ℝ+, p x = ⊤
        rw [ENNReal.top_rpow_of_pos ?H]
        case H => linarith
        rw [top_mul']
        split
        · exfalso
          rename_i Hcont
          apply Hvq'
          have Hcont' : (vq' : ENNReal) = 0 ∧ 0 < (1-α) ∨ (vq' : ENNReal) = ⊤ ∧ (1-α)< 0 := by
            exact rpow_eq_zero_iff.mp Hcont
          cases Hcont'
          · simp_all only [some_eq_coe, none_eq_top, zero_ne_top]
          · simp_all only [some_eq_coe, none_eq_top, top_rpow_of_neg, coe_ne_top, sub_neg, and_true]
        · rw [top_mul']
          split
          · simp_all only [some_eq_coe, none_eq_top, zero_ne_top]
          · rfl
      · rename_i vp
        cases (Classical.em (vq' = 0))
        · -- q x ∈ ℝ+, p x = 0
          rename_i Hvp'
          simp_all
        · -- q x ∈ ℝ+, p x ∈ ℝ+
          rename_i Hvp'
          rw [ENNReal.rpow_sub]
          . rw [← ENNReal.mul_comm_div]
            rw [← ENNReal.div_rpow_of_nonneg]
            . rw [ENNReal.rpow_one]
            . apply le_of_lt (lt_trans Real.zero_lt_one h )
          · simp_all only [some_eq_coe, not_false_eq_true, ne_eq, coe_eq_zero]
          · simp_all only [some_eq_coe, not_false_eq_true, ne_eq, coe_ne_top]


/-!
## Jensen's inequality
-/
section Jensen

variable {T : Type}
variable [t1 : MeasurableSpace T]
variable [t2 : MeasurableSingletonClass T]

variable {U V : Type}
variable [m2 : MeasurableSpace U]
variable [count : Countable U]
variable [disc : DiscreteMeasurableSpace U]
variable [Inhabited U]

lemma Integrable_rpow (f : T → ℝ) (nn : ∀ x : T, 0 ≤ f x) (μ : Measure T) (α : ENNReal) (mem : Memℒp f α μ) (h1 : α ≠ 0) (h2 : α ≠ ⊤)  :
  MeasureTheory.Integrable (fun x : T => (f x) ^ α.toReal) μ := by
  have X := @MeasureTheory.Memℒp.integrable_norm_rpow T ℝ t1 μ _ f α mem h1 h2
  revert X
  conv =>
    left
    left
    intro x
    rw [← norm_rpow_of_nonneg (nn x)]
  intro X
  simp [Integrable] at *
  constructor
  . cases X
    rename_i left right
    rw [@aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.pow_const
    simp [Memℒp] at mem
    cases mem
    rename_i left' right'
    rw [aestronglyMeasurable_iff_aemeasurable] at left'
    simp [left']
  . rw [← hasFiniteIntegral_norm_iff]
    simp [X]

/--
Jensen's ineuquality for the exponential applied to Renyi's sum
-/
theorem Renyi_Jensen_real (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : Memℒp f (ENNReal.ofReal α) (PMF.toMeasure q)) :
  ((∑' x : T, (f x) * (q x).toReal)) ^ α ≤ (∑' x : T, (f x) ^ α * (q x).toReal) := by
  conv =>
    left
    left
    right
    intro x
    rw [mul_comm]
    rw [← smul_eq_mul]
  conv =>
    right
    right
    intro x
    rw [mul_comm]
    rw [← smul_eq_mul]
  rw [← PMF.integral_eq_tsum]
  rw [← PMF.integral_eq_tsum]

  have A := @convexOn_rpow α (le_of_lt h)
  have B : ContinuousOn (fun (x : ℝ) => x ^ α) (Set.Ici 0) := by
    apply ContinuousOn.rpow
    . exact continuousOn_id' (Set.Ici 0)
    . exact continuousOn_const
    . intro x h'
      simp at h'
      have OR : x = 0 ∨ 0 < x := by exact LE.le.eq_or_gt h'
      cases OR
      . rename_i h''
        subst h''
        right
        apply lt_trans zero_lt_one h
      . rename_i h''
        left
        by_contra
        rename_i h3
        subst h3
        simp at h''
  have C : @IsClosed ℝ UniformSpace.toTopologicalSpace (Set.Ici 0) := by
    exact isClosed_Ici
  have D := @ConvexOn.map_integral_le T ℝ t1 _ _ _ (PMF.toMeasure q) (Set.Ici 0) f (fun (x : ℝ) => x ^ α) (PMF.toMeasure.isProbabilityMeasure q) A B C
  simp at D
  apply D
  . exact MeasureTheory.ae_of_all (PMF.toMeasure q) h2
  . apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h
  . rw [Function.comp_def]
    have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    . exact Z
    . apply le_of_lt
      apply lt_trans zero_lt_one h
  . have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    . exact Z
    . apply le_of_lt
      apply lt_trans zero_lt_one h
  . apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h

end Jensen

-- MARKUSDE: move
noncomputable def Renyi_Jensen_f (p q : PMF T) : T -> ℝ := (fun z => ((p z / q z)).toReal)

-- Except for one case, we can rewrite the ENNReal-valued inequality into the form Jenen's inequality expects.
lemma Renyi_Jensen_rw (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)) (x : T) :
  (p x / q x)^α  * (q x) = ENNReal.ofReal (((Renyi_Jensen_f p q) x)^α * (q x).toReal) := sorry


-- FIXME: might be able to simplify this argument with the new rewrite lemmas
/--
Jensen's inquality applied to ENNReals, in the case that q is nonzero
-/
lemma Renyi_Jensen_ENNReal_reduct [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hq : ∀ t, q t ≠ 0):
  (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by
  have Hdiscr : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  cases (Classical.em (∑' (a : T), (p a / q a) ^ α * q a ≠ ⊤))
  · rename_i Hnts
    cases (Classical.em (∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)))
    · -- Typical case
      rename_i Hspecial
      conv =>
        rhs
        arg 1
        intro x
        rw [Renyi_Jensen_rw p q h H Hspecial]
      rw [<- ENNReal.ofReal_tsum_of_nonneg ?Hnonneg ?Hsummable]
      case Hnonneg =>
        intro t
        apply mul_nonneg
        · refine rpow_nonneg ?ha.hx α
          simp [Renyi_Jensen_f]
        · exact toReal_nonneg
      case Hsummable =>
        conv =>
          congr
          intro x
          rw [Renyi_Jensen_f]
        conv =>
          arg 1
          intro x
          lhs
          rw [ENNReal.toReal_rpow]
        conv =>
          arg 1
          intro x
          rw [<- ENNReal.toReal_mul]
        apply ENNReal.summable_toReal
        assumption
      have HRJf_nonneg (a : T) : 0 <= Renyi_Jensen_f p q a := by apply toReal_nonneg
      have HRJf_nt (a : T) : p a / q a ≠ ⊤ := by
        intro HK
        have HK' : (p a ≠ 0 ∧ q a = 0 ∨ p a = ⊤ ∧ q a ≠ ⊤) := by exact div_eq_top.mp HK
        cases HK'
        · rename_i HK'
          rcases HK' with ⟨ HK1 , HK2 ⟩
          rw [AbsCts] at H
          simp_all only [ne_eq, not_and, Decidable.not_not, ENNReal.zero_div, zero_ne_top]
        · rename_i HK'
          rcases HK' with ⟨ HK1 , _ ⟩
          apply (Hspecial a)
          simp_all
      have Hsum_indicator (a : T) : ∑' (i : T), q i * Set.indicator {a} (fun x => 1) i = q a := by
        have Hfun : (fun (i : T) => q i * Set.indicator {a} (fun x => 1) i) = (fun (i : T) => if i = a then q a else 0) := by
          funext i
          rw [Set.indicator]
          split <;> simp <;> split <;> simp_all
        rw [Hfun]
        exact tsum_ite_eq a (q a)
      apply (le_trans ?G1 ?G2)
      case G2 =>
        apply (ofReal_le_ofReal ?Hle)
        case Hle =>
          apply Renyi_Jensen_real
          · apply h
          · simp [Renyi_Jensen_f]
          · simp [Memℒp]
            constructor
            . apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
              apply Measurable.stronglyMeasurable
              apply Measurable.ennreal_toReal
              conv =>
                right
                intro x
                rw [division_def]
              apply Measurable.mul
              . apply measurable_discrete
              . apply Measurable.inv
                apply measurable_discrete
            · simp [snorm]
              split
              · simp
              · rename_i Hα
                simp [snorm']
                rw [MeasureTheory.lintegral_countable']
                rw [toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))]
                apply rpow_lt_top_of_nonneg
                · simp
                  apply le_of_not_ge Hα
                · conv =>
                    lhs
                    arg 1
                    intro a
                    arg 1
                    arg 1
                    rw [<- Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a)]
                    rw [Renyi_Jensen_f]
                    rw [<- ENNReal.ofReal.eq_1]
                    rw [ENNReal.ofReal_toReal (HRJf_nt a)]
                    rfl
                  conv =>
                    lhs
                    arg 1
                    intro a
                    rhs
                    simp [toMeasure]
                    simp [PMF.toOuterMeasure]
                    rw [Hsum_indicator]
                  apply Hnts
      case G1 =>
        -- We need the latter fn to be summable or else it becomes zero and the inequality does not hold
        rw [<- ENNReal.ofReal_rpow_of_nonneg ?Harg ?Hα]
        case Harg =>
          apply tsum_nonneg
          intro i
          apply mul_nonneg
          · apply HRJf_nonneg
          · exact toReal_nonneg
        case Hα => linarith
        apply (ENNReal.rpow_le_rpow _ ?Hα')
        case Hα' => linarith
        conv =>
          rhs
          arg 1
          arg 1
          intro a
          rw [Renyi_Jensen_f]
          rw [<- ENNReal.toReal_mul]
        rw [<- ENNReal.tsum_toReal_eq]
        · rw [ENNReal.ofReal_toReal]
          -- Could do another case at the top if not derivable
          -- Want to bound above my ∑'
          conv =>
            arg 1
            arg 1
            intro a
            rw [PMF_mul_mul_inv_eq_mul_cancel p q H]
          exact tsum_coe_ne_top p
        · -- Bound above by p a
          intro a
          conv =>
            arg 1
            rw [PMF_mul_mul_inv_eq_mul_cancel p q H]
          exact apply_ne_top p a
    · -- Special case: There exists some element x0 with p x0 = ⊤ but q x0 ∈ ℝ+
      rename_i Hspecial
      simp at *
      rcases Hspecial with ⟨ x0, ⟨ H1, H2 , H3 ⟩⟩
      have HT1 : (∑' (x : T), p x / q x * q x) ^ α = ⊤ := by
        apply rpow_eq_top_iff.mpr
        right
        apply And.intro
        · apply ENNReal.tsum_eq_top_of_eq_top
          exists x0
          apply mul_eq_top.mpr
          right
          apply And.intro
          · apply div_eq_top.mpr
            simp_all
          · simp_all
        · linarith
      have HT2 : ∑' (x : T), (p x / q x) ^ α * q x = ⊤ := by
        apply ENNReal.tsum_eq_top_of_eq_top
        exists x0
        apply mul_eq_top.mpr
        right
        apply And.intro
        · apply rpow_eq_top_iff.mpr
          right
          apply And.intro
          · simp_all
            exact top_div_of_ne_top H3
          · simp_all
            linarith
        · simp_all
      rw [HT1, HT2]
  · rename_i HStop
    simp at *
    rw [HStop]
    exact OrderTop.le_top ((∑' (x : T), p x / q x * q x) ^ α)

/--
Jensen's inquality applied to ENNReals
-/
theorem Renyi_Jensen_ENNReal[MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
  (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by
  sorry



-- FIXME
/--
The Renyi divergence is monotonic in the value of its sum.
-/
lemma RenyiDivergence_mono_sum (x y : ℝ) (α : ℝ) (h : 1 < α) : (Real.exp ((α - 1) * x)) ≤ (Real.exp ((α - 1) * y)) -> (x ≤ y) := by
  intro H
  apply _root_.le_of_mul_le_mul_left
  · exact exp_le_exp.mp H
  · linarith

theorem RenyiDivergence_def_nonneg [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (p q : PMF T) (Hpq : AbsCts p q) {α : ℝ} (Hα : 1 < α) :
  (0 ≤ RenyiDivergence_def p q α) := by
  have H1 : eexp (((α - 1)) * 0)  ≤ eexp ((α - 1) * RenyiDivergence_def p q α) := by
    rw [RenyiDivergence_def_exp p q Hα]
    rw [RenyiDivergenceExpectation p q Hα Hpq]
    simp
    apply (le_trans ?G1 (Renyi_Jensen_ENNReal p q Hα Hpq))
    have Hone : (∑' (x : T), p x / q x * q x) = 1 := by
      -- This argument is also necessary to finish the Jensen's inequality proof (filter out the q x = 0 elements)
      sorry
    have Hle : (∑' (x : T), p x / q x * q x) ≤ (∑' (x : T), p x / q x * q x) ^ α := by
      apply ENNReal.le_rpow_self_of_one_le
      · rw [Hone]
      · linarith
    apply le_trans ?X Hle
    rw [Hone]
  apply eexp_mono_le.mpr at H1
  have HX : (0 < (α.toEReal - 1)) := by sorry
  have HX1 : (ofEReal ((↑α - 1) * 0) ≤ ofEReal ((↑α - 1) * RenyiDivergence_def p q α)) := by
    exact ofEReal_le_mono.mp fun a => H1
  rw [ofEReal_mul] at HX1
  -- Circular side condition? Why is cancelling EReals so hard? Make a lemma with the iff cases in Log
  all_goals sorry

theorem RenyiDivergence_def_zero (p q : PMF T) (α : ℝ) : p = q <-> (0 = RenyiDivergence_def p q α) := by
  -- See paper
  sorry

lemma RenyiDivergence_def_log_sum_nonneg (p q : PMF T) (α : ℝ) : (0 ≤ (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))) := by
  -- Follows from RenyiDivergence_def_nonneg
  sorry

/--
The Renyi divergence.
-/
noncomputable def RenyiDivergence (p q : PMF T) (α : ℝ) : ENNReal :=
  ENNReal.ofEReal (RenyiDivergence_def p q α)

-- MARKUSDE: We evaluate through the ENNReal.ofEReal using ``RenyiDivergence_def_nonneg``, these are some special cases
theorem RenyiDivergence_aux_zero (p q : PMF T) (α : ℝ) : p = q <-> RenyiDivergence p q α = 0
  := sorry



-- Unused
/-
Closed form for the Renyi Divergence.
-/
-- theorem RenyiDivergenceExpectation' (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (h1 : ∀ x : T, q x ≠ 0) (h2 : ∀ x : T, q x ≠ ⊤) :
--   (α - 1)⁻¹ * Real.log ((∑' x : T, (p x)^α  * (q x)^(1 - α))).toReal = (α - 1)⁻¹ * Real.log (∑' x : T, (p x / q x)^α  * (q x)).toReal := by
--   congr 4
--   ext x
--   rw [ENNReal.rpow_sub]
--   . rw [← ENNReal.mul_comm_div]
--     rw [← ENNReal.div_rpow_of_nonneg]
--     . rw [ENNReal.rpow_one]
--     . apply le_of_lt (lt_trans Real.zero_lt_one h )
--   . apply h1 x
--   . apply h2 x
