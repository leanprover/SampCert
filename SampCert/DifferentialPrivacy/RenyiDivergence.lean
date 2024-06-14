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

variable {T : Type}

/--
Definition of the Renyi divergence as an EReal.
-/
noncomputable def RenyiDivergence_def (p q : PMF T) (α : ℝ) : EReal :=
  (α - 1)⁻¹  * (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))

/--
Equation for the Renyi divergence series in terms of the Renyi Divergence
-/
lemma RenyiDivergence_def_exp (p q : PMF T) {α : ℝ}
  (h : 1 < α)
  (H1 : 0 < ∑' (x : T), p x ^ α * q x ^ (1 - α))
  (H2 : ∑' (x : T), p x ^ α * q x ^ (1 - α) < ⊤) :
  eexp (((α - 1)) * RenyiDivergence_def p q α) = (∑' x : T, (p x)^α * (q x)^(1 - α)) := by
  simp only [RenyiDivergence_def]
  rw [<- mul_assoc]
  have Hinvert : ((↑α - 1) * ↑(α - 1)⁻¹ : EReal) = 1 := by
    clear H1
    clear H2
    have Hsub : ((↑α - 1) : EReal) = (α - 1 : ℝ) := by simp
    rw [Hsub]
    have Hundo_coe (r1 r2 : ℝ) : (r1 : EReal) * (r2 : EReal) = ((r1 * r2 : ℝ) : EReal) := by
      rw [EReal.coe_mul]
    rw [Hundo_coe]
    have Hinv : (α - 1) * (α - 1)⁻¹ = 1 := by
      apply mul_inv_cancel
      linarith
    rw [Hinv]
    simp
  rw [Hinvert]
  clear Hinvert
  simp

-- FIXME: where is this in mathlib?
-- Need to say that p and q are the PMF's of a measure space (how do I use their typeclasses to do that?)
-- PMF.toMeasure
-- Then get AbsCts from AbsolutelyContinuous
def AbsCts (p q : T -> ENNReal) : Prop := ∀ x : T, q x = 0 -> p x = 0

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
noncomputable def Renyi_Jensen_f (p : T -> ENNReal) (q : PMF T) : T -> ℝ := (fun z => ((p z / q z)).toReal)

-- Except for one case, we can rewrite the ENNReal-valued inequality into the form Jenen's inequality expects.
lemma Renyi_Jensen_rw (p : T → ENNReal) (q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)) (x : T) :
  (p x / q x)^α  * (q x) = ENNReal.ofReal (((Renyi_Jensen_f p q) x)^α * (q x).toReal) := sorry

lemma Renyi_Jensen_ENNReal [MeasurableSpace T] [MeasurableSingletonClass T] (p : T → ENNReal) (q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
  (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by
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
      -- Comes from PMF
      sorry
    case Hsummable =>
      -- Summability
      sorry

    apply (le_trans ?G1 ?G2)
    case G2 =>
      apply (ofReal_le_ofReal ?Hle)
      case Hle =>
        apply Renyi_Jensen_real
        · apply h
        · -- Comes from PMF
          sorry
        · -- Also summability
          sorry
    case G1 =>
      -- We need the latter fn to be summable
      sorry
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




-- FIXME
/--
The Renyi divergence is monotonic in the value of its sum.
-/
lemma RenyiDivergence_mono_sum (x y : ℝ) (α : ℝ) (h : 1 < α) : (Real.exp ((α - 1) * x)) ≤ (Real.exp ((α - 1) * y)) -> (x ≤ y) := by
  intro H
  apply _root_.le_of_mul_le_mul_left
  · exact exp_le_exp.mp H
  · linarith

theorem RenyiDivergence_def_nonneg (p q : PMF T) (α : ℝ) : (0 ≤ RenyiDivergence_def p q α) := by
  -- See paper
  sorry

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
