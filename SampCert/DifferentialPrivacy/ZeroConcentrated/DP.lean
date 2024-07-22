/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.ConcentratedBound
import SampCert.SLang
import SampCert.Samplers.GaussianGen.Basic
import SampCert.DifferentialPrivacy.Neighbours
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral
import SampCert.DifferentialPrivacy.Pure.DP

set_option linter.unusedTactic false

/-!
# Zero Concentrated Differential Privacy

This file defines zero concentrated differential privacy (zCDP).
-/


/--
Inequality defining ``(ε^2)/2``-zCDP.

All ``ε``-DP mechanisms satisfy this bound (though not all mechanisms
satisfying this bound are ``ε``-DP).
-/
def zCDPBound (q : List T → PMF U) (ε : ℝ) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  RenyiDivergence (q l₁) (q l₂) α ≤ ENNReal.ofReal ((1/2) * ε ^ 2 * α)

/--
All neighbouring queries are absolutely continuous
-/
def ACNeighbour (p : List T -> PMF  U) : Prop := ∀ l₁ l₂, Neighbour l₁ l₂ -> AbsCts (p l₁) (p l₂)

/--
The mechanism ``q`` is ``(ε^2)/2``-zCDP
-/
def zCDP (q : List T → PMF U) (ε : NNReal) : Prop := ACNeighbour q ∧ zCDPBound q ε

lemma zCDP_mono {m : List T -> PMF U} {ε₁ ε₂ : NNReal} (H : ε₁ ≤ ε₂) (Hε : zCDP m ε₁) : zCDP m ε₂ := by
  rcases Hε with ⟨ Hac , Hε ⟩
  rw [zCDP] at *
  apply And.intro
  · assumption
  · rw [zCDPBound] at *
    intro α Hα l₁ l₂ N
    apply (@le_trans _ _ _ (ENNReal.ofReal (1 / 2 * ↑ε₁ ^ 2 * α)) _ (Hε α Hα l₁ l₂ N))
    apply ENNReal.coe_mono
    refine (Real.toNNReal_le_toNNReal_iff ?a.hp).mpr ?a.a
    · apply mul_nonneg
      · apply mul_nonneg
        · simp
        · simp
      · linarith
    · repeat rw [mul_assoc]
      apply (mul_le_mul_iff_of_pos_left (by simp)).mpr
      apply (mul_le_mul_iff_of_pos_right (by linarith)).mpr
      apply pow_le_pow_left' H (OfNat.ofNat 2)


/--
Pure DP bound implies absolute continuity
-/
lemma ACNeighbour_of_DP (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : ACNeighbour q := by
  unfold SLang.PureDP at H
  apply (SLang.event_eq_singleton q ε).mp at H
  intro l₁ l₂ HN x Hx2
  apply Classical.by_contradiction
  intro Hx1
  unfold SLang.DP_singleton at H
  have H' := H l₁ l₂ HN x
  rw [Hx2] at H'
  rw [ENNReal.div_zero Hx1] at H'
  simp at H'


/-
## Auxiliary definitions used in the proof of the (ε^2 / 2) bound
-/
section ofDP_bound
variable (ε : NNReal) (Hε : 0 < ε)
variable (p q : PMF U)
variable (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x )
variable (Hpq : ∀ x, (p x / q x ≤ ENNReal.ofReal (Real.exp ε)))
variable (Hac : AbsCts p q)


noncomputable def β (x : U) : ENNReal :=
  (ENNReal.ofReal (Real.exp ε) - (p x / q x)) / (ENNReal.ofReal (Real.exp (ε)) - ENNReal.ofReal (Real.exp (- ε)))

lemma β_le_one {x : U} : β ε p q x ≤ 1 := by
  unfold β
  apply ENNReal.div_le_of_le_mul
  simp
  rw [← tsub_le_iff_right]
  refine (ENNReal.sub_le_sub_iff_left ?h.h ?h.h').mpr ?h.a
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simp
  · simp
  · apply Hqp



lemma one_sub_β (x : U) : 1 - (β ε p q x : ENNReal) =
    ((p x / q x) - ENNReal.ofReal (Real.exp (-ε)) ) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))) := by
  unfold β
  generalize HC : (p x / q x) = C
  generalize HD : (ENNReal.ofReal (Real.exp ε)) = D
  generalize HE : (ENNReal.ofReal (Real.exp (- ε))) = E
  have H1 : (D - E ≠ 0) := by
    rw [<- HD, <- HE]
    rw [<- ENNReal.ofReal_sub]
    · simp
      trivial
    · apply Real.exp_nonneg
  have H2 : (D - E ≠ ⊤) := by simp [<- HD, <- HE]
  apply (@ENNReal.mul_eq_mul_right _ _ (D - E) H1 H2).mp
  rw [ENNReal.sub_mul ?G1]
  case G1 =>
    intros
    trivial
  conv =>
    congr
    · rw [ENNReal.mul_comm_div]
      rw [ENNReal.div_eq_inv_mul]
    · rw [ENNReal.mul_comm_div]
      rw [ENNReal.div_eq_inv_mul]
  simp [ENNReal.inv_mul_cancel H1 H2]
  rw [tsub_tsub]
  rw [tsub_add_eq_tsub_tsub_swap]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp [<- HD]
  case G2 =>
    rw [<- HD, <- HC]
    apply Hpq

/--
Value of the random variable A
-/
noncomputable def A_val (b : Bool) : ENNReal :=
    match b with
    | false => ENNReal.ofReal (Real.exp (-ε))
    | true => ENNReal.ofReal (Real.exp (ε))

/--
Proability space underlying the random variable A
-/
noncomputable def A_pmf (x : U) : PMF Bool :=
  ⟨ fun b =>
        match b with
        | false => β ε p q x
        | true => 1 - β ε p q x,
    by
       simp [(Summable.hasSum_iff ENNReal.summable), tsum_bool, add_tsub_cancel_iff_le]
       apply β_le_one
       trivial ⟩

/--
Expectation for the random variable A at each point x
-/
lemma A_expectation (x : U) : ∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b = p x / q x := by
  rw [tsum_bool]
  unfold A_pmf
  rw [A_val, A_val, DFunLike.coe, PMF.instFunLike]
  simp only []
  conv =>
    lhs
    congr
    · unfold β
    · rw [one_sub_β _ Hε _ _ Hpq]
  generalize HC : (p x / q x) = C
  generalize HD : (ENNReal.ofReal (Real.exp ε)) = D
  generalize HE : (ENNReal.ofReal (Real.exp (- ε))) = E
  have H1 : (D - E ≠ 0) := by
    rw [<- HD, <- HE]
    rw [<- ENNReal.ofReal_sub]
    · simp
      trivial
    · apply Real.exp_nonneg
  have H2 : (D - E ≠ ⊤) := by simp [<- HD, <- HE]
  apply (@ENNReal.mul_eq_mul_right _ _ (D - E) H1 H2).mp
  rw [add_mul]
  rw [division_def]
  rw [division_def]
  repeat rw [mul_assoc]
  simp [ENNReal.inv_mul_cancel H1 H2]
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HE]
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HD]
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HC]
    -- From absolute continuity
    sorry
  skip
  sorry


/--
Jensen's inequality for the random variable A: real reduct
-/
lemma A_jensen_real (α : ℝ) (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), (A_val ε b).toReal * (A_pmf ε p q Hqp x b).toReal) ^ α ≤ (∑'(b : Bool), ((A_val ε b).toReal)^α * (A_pmf ε p q Hqp x b).toReal) := by
  have HJensen := @ConvexOn.map_integral_le _ _ ⊤ _ _ _ _ _ (fun b => (A_val ε b).toReal) _
          (PMF.toMeasure.isProbabilityMeasure (A_pmf ε p q Hqp x))
          (@convexOn_rpow α (le_of_lt Hα))
          ?G1 ?G2 ?G3 ?G4 ?G5
  case G1 =>
    apply ContinuousOn.rpow
    · exact continuousOn_id' (Set.Ici 0)
    · exact continuousOn_const
    · intro _ _
      right
      linarith
  case G2 =>
    exact isClosed_Ici
  case G3 =>
    apply MeasureTheory.ae_of_all
    intro b
    cases b <;> simp
  case G4 => simp
  case G5 => apply MeasureTheory.Integrable.of_finite

  rw [PMF.integral_eq_tsum _ _ ?G4] at HJensen
  case G4 => simp
  rw [PMF.integral_eq_tsum _ _ ?G5] at HJensen
  case G5 => apply MeasureTheory.Integrable.of_finite

  simp at HJensen
  conv at HJensen =>
    congr
    · enter [1, 1, a]
      rw [mul_comm]
    · enter [1, a]
      rw [mul_comm]
  trivial


/--
Jensen's inequality for the random variable A
-/
lemma A_jensen (α : ℝ) (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b) ^ α ≤ (∑'(b : Bool), (A_val ε b)^α * A_pmf ε p q Hqp x b) := by


  sorry

noncomputable def B : PMF Bool := q >>= A_pmf ε p q Hqp

/--
Formula for B which shows up in the main derivation
-/
lemma B_eval_open (b : Bool) : B ε p q Hqp b = ∑'(x : U), A_pmf ε p q Hqp x b * q x := by
  unfold B
  simp
  apply tsum_congr
  intro
  rw [mul_comm]

/--
closed form for B false
-/
lemma B_eval_false : B ε p q Hqp false = (ENNReal.ofReal (Real.exp ε) - 1) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))):= by sorry

/--
closed form for B true
-/
lemma B_eval_true : B ε p q Hqp true = (1 - ENNReal.ofReal (Real.exp (- ε))) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))):= by sorry


end ofDP_bound




/--
Convert ε-DP bound to `(1/2)ε²`-zCDP bound.

Note that `zCDPBound _ ε` corresponds to `(1/2)ε²`-zCDP (not `ε`-zCDP).
-/
lemma ofDP_bound (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : zCDPBound q ε := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ HN

  -- Reduction to (q l₂) nonzero case? See if this reduction is necessary by filling out all the prior lemmas

  -- Suffices le exp sum by monotonicity
  -- Rewrite RD exp sum lemma
  -- Have (RD sum) le (split in terms of A)
  --


  sorry

/-
Convert ε-DP to `(1/2)ε²`-zCDP.

Note that `zCDPBound _ ε` corresponds to `(1/2)ε²`-zCDP (not `ε`-zCDP).
-/
lemma ofDP (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : zCDP q ε := by
  constructor
  · exact ACNeighbour_of_DP ε q H
  · exact ofDP_bound ε q H
