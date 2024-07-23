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

lemma β_ne_top : β ε p q x ≠ ⊤ := by
  unfold β
  intro HK
  apply ENNReal.div_eq_top.mp at HK
  cases HK
  · rename_i HK
    rcases HK with ⟨ _ , HK' ⟩
    rw [<- ENNReal.ofReal_sub] at HK'
    · simp at HK'
      apply not_le.mpr Hε HK'
    · apply Real.exp_nonneg
  · rename_i HK
    rcases HK with ⟨ HK', _ ⟩
    apply ENNReal.sub_eq_top_iff.mp at HK'
    simp at HK'


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


lemma sub_one_β_ne_top : (1 - β ε p q x) ≠ ⊤ := by
  apply ENNReal.sub_ne_top
  simp


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
    have Hac := Hac x
    intro HK
    apply ENNReal.div_eq_top.mp at HK
    cases HK
    · simp_all only [imp_false, not_true_eq_false]
    · rename_i HK'
      cases HK'
      apply PMF.apply_ne_top p x
      trivial

  conv =>
    enter [1, 2, 2]
    rw [mul_comm]

  -- Arithmetic
  -- ENNReal subtraction is difficult
  -- Handle ⊤ cases to convert to NNReal
  generalize HED : (E * D) = ED
  cases ED
  · exfalso
    apply ENNReal.mul_eq_top.mp at HED
    cases HED
    · rename_i h
      rcases h with ⟨ _ , h ⟩
      rw [<- HD] at h
      simp at h
    · exfalso
      rename_i h
      rcases h with ⟨ h , _ ⟩
      rw [<- HE] at h
      simp at h
  rename_i ED

  conv =>
    enter [1, 1, 2]
    rw [mul_comm]
  generalize HCE : (C * E) = CE
  cases CE
  · simp
    apply ENNReal.mul_eq_top.mp at HCE
    cases HCE
    · exfalso
      rename_i h
      rcases h with ⟨ _ , h ⟩
      rw [<- HE] at h
      simp at h
    · rename_i h
      rcases h with ⟨ h , _ ⟩
      exfalso
      rw [<- HC] at h
      apply ENNReal.div_eq_top.mp at h
      cases h
      · rename_i h'
        rcases h' with ⟨ h1, h2 ⟩
        apply h1
        apply Hac
        apply h2
      · rename_i h
        rcases h with ⟨ h, _ ⟩
        apply PMF.apply_ne_top p x h
  rename_i CE
  conv =>
    enter [1, 2, 1]
    rw [mul_comm]
  generalize HCD : (C * D) = CD
  cases CD
  · simp
  rename_i CD
  rw [ENNReal.ofNNReal]
  repeat rw [<- WithTop.coe_sub]
  repeat rw [<- WithTop.coe_add]
  congr

  -- Now convert to Real substraction
  repeat rw [NNReal.sub_def]
  rw [<- Real.toNNReal_add ?G1 ?G2]
  case G1 =>
    rw [sub_nonneg]
    apply (ENNReal.ofReal_le_ofReal_iff ?G3).mp
    case G3 => exact NNReal.zero_le_coe
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HCE]
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HED]
    rw [mul_comm]
    apply mul_le_mul'
    · rfl
    rw [<- HC, <- HD]
    apply Hpq
  case G2 =>
    rw [sub_nonneg]
    apply (ENNReal.ofReal_le_ofReal_iff ?G3).mp
    case G3 => exact NNReal.zero_le_coe
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HED]
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HCD]
    apply mul_le_mul'
    · rw [<- HE, <- HC]
      apply Hqp
    · rfl

  -- Real subtraction is easier
  congr 1
  linarith



/--
Jensen's inequality for the random variable A: real reduct
-/
lemma A_jensen_real {α : ℝ} (Hα : 1 < α) (x : U) :
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
lemma A_jensen {α : ℝ} (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b) ^ α ≤ (∑'(b : Bool), (A_val ε b)^α * A_pmf ε p q Hqp x b) := by

  have SC1 (b : Bool) : A_val ε b ≠ ⊤ := by cases b <;> simp [A_val]
  have SC2 (b : Bool) : (A_pmf ε p q Hqp x) b ≠ ⊤ := by
    cases b <;> simp only [A_pmf, DFunLike.coe, PMF.instFunLike]
    · apply β_ne_top
      apply Hε
    · apply sub_one_β_ne_top

  apply (ENNReal.toReal_le_toReal ?G1 ?G2).mp
  case G1 =>
    apply ENNReal.rpow_ne_top_of_nonneg
    · linarith
    · rw [tsum_bool]
      apply ENNReal.add_ne_top.mpr
      apply And.intro
      · apply ENNReal.mul_ne_top
        · apply (SC1 false)
        · apply (SC2 false)
      · apply ENNReal.mul_ne_top
        · apply (SC1 true)
        · apply (SC2 true)
  case G2 =>
    rw [tsum_bool]
    apply ENNReal.add_ne_top.mpr
    apply And.intro
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · linarith
        apply (SC1 false)
      · apply (SC2 false)
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · linarith
        apply (SC1 true)
      · apply (SC2 true)
  rw [tsum_bool, tsum_bool]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 =>
    apply ENNReal.mul_ne_top
    · apply (SC1 false)
    · apply (SC2 false)
  case G2 =>
    apply ENNReal.mul_ne_top
    · apply (SC1 true)
    · apply (SC2 true)
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 =>
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      apply (SC1 false)
    · apply (SC2 false)
  case G2 =>
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      apply (SC1 true)
    · apply (SC2 true)
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [← ENNReal.toReal_rpow]
  rw [← ENNReal.toReal_rpow]
  have HJR := A_jensen_real ε p q Hqp Hα x
  rw [tsum_bool, tsum_bool] at HJR
  trivial

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
lemma B_eval_false : B ε p q Hqp false = (ENNReal.ofReal (Real.exp ε) - 1) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))):= by
  sorry

/--
closed form for B true
-/
lemma B_eval_true : B ε p q Hqp true = (1 - ENNReal.ofReal (Real.exp (- ε))) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))):= by
  sorry

end ofDP_bound



lemma sinh_inequality {x y : ℝ} (Hy : 0 ≤ y) (Hyx : y < x) (Hx : x ≤ 2) :
    (Real.sinh x - Real.sinh y) / Real.sinh (x - y) ≤ Real.exp (x * y / 2) := by
  sorry


set_option pp.coercions false

/--
Convert ε-DP bound to `(1/2)ε²`-zCDP bound.

Note that `zCDPBound _ ε` corresponds to `(1/2)ε²`-zCDP (not `ε`-zCDP).
-/
lemma ofDP_bound (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : zCDPBound q ε := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ HN

  -- Open RenyiDivergence
  rw [RenyiDivergence]
  rw [<- ENNReal.ofEReal_ofReal_toENNReal]
  apply ENNReal.ofEReal_le_mono

  -- Change LHS to sum by monotonicity
  suffices ENNReal.eexp ((α - 1) * RenyiDivergence_def (q l₁) (q l₂) α) ≤ ENNReal.eexp ((α - 1) * Real.toEReal (1 / 2 * ↑ε ^ 2 * α)) by
    apply (ENNReal.ereal_smul_le_left (α - 1) ?G1 ?G2)
    case G1 => sorry -- Annoying
    case G2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    apply ENNReal.eexp_mono_le.mpr
    trivial
  rw [RenyiDivergence_def_exp _ _ Hα]

  -- Rewrite to conditional expectation, and then to A
  have Hacpq := (ACNeighbour_of_DP _ _ H _ _ HN)
  have Hacqp := (ACNeighbour_of_DP _ _ H _ _ (Neighbour_symm _ _ HN))
  have Hqp : ∀ (x : U), ENNReal.ofReal (Real.exp (-↑ε)) ≤ (q l₁) x / (q l₂) x := by
    rw [SLang.PureDP] at H
    apply SLang.event_to_singleton at H
    suffices (∀ (x : U), (q l₂) x / (q l₁) x ≤ ENNReal.ofReal (Real.exp ↑ε)) by
      intro x
      apply ENNReal.inv_le_inv.mp
      rw [<- ENNReal.ofReal_inv_of_pos ?G4]
      case G4 => apply Real.exp_pos
      rw [<- Real.exp_neg]
      simp
      apply (le_trans _ (this x))
      apply Eq.le
      -- Cases on if they're (both, by AC) zero, apply some rewrite
      rw [ENNReal.div_eq_inv_mul]
      sorry
    apply H
    apply Neighbour_symm
    trivial
  have Hpq : ∀ (x : U), (q l₁) x / (q l₂) x ≤ ENNReal.ofReal (Real.exp ↑ε) := by
    rw [SLang.PureDP] at H
    apply SLang.event_to_singleton at H
    apply H
    trivial
  rw [RenyiDivergenceExpectation _ _ Hα (ACNeighbour_of_DP _ _ H _ _ HN)]

  -- Next step won't work with ε=0
  cases (Classical.em (ε = 0))
  · -- Follows from the DP bound
    simp_all
    rw [SLang.PureDP] at H
    apply SLang.event_to_singleton at H
    rw [SLang.DP_singleton] at H
    have H := H l₁ l₂ HN
    simp at H
    apply (@le_trans _ _ _ (∑' (x : U), 1 ^ α * (q l₂) x))
    · apply ENNReal.tsum_le_tsum
      intro i
      cases (Classical.em ((q l₂) i = 0))
      · rename_i Hz
        rw [Hz]
        simp_all
      apply (ENNReal.mul_le_mul_right ?G1 ?G2).mpr
      case G1 => trivial
      case G2 => exact PMF.apply_ne_top (q l₂) i
      apply ENNReal.rpow_le_rpow (Hpq i)
      linarith
    · simp
  rename_i Hε'

  have Hε : 0 < ε := by exact pos_iff_ne_zero.mpr Hε'

  conv =>
    enter [1, 1, x]
    rw [<- A_expectation ε Hε (q l₁) (q l₂) Hqp Hpq (ACNeighbour_of_DP _ _ H _ _ HN) x]

  -- Apply Jensen's inequality
  apply (@le_trans _ _ _ (∑' (x : U), (∑' (b : Bool), (A_val ε b)^α * (A_pmf ε (q l₁) (q l₂) Hqp x) b) * (q l₂) x))
  · apply ENNReal.tsum_le_tsum
    intro a
    cases (Classical.em ((q l₂) a = 0))
    · simp_all
    rename_i Hqnz
    apply (ENNReal.mul_le_mul_right ?G1 ?G2).mpr
    case G1 => trivial
    case G2 => exact PMF.apply_ne_top (q l₂) a
    exact A_jensen ε Hε (q l₁) (q l₂) Hqp Hα a

  -- Exchange the summations
  conv =>
    enter [1, 1, x]
    rw [<- ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]

  -- Pull out constant from inner series
  -- Rewrite in terms of B
  -- Evaluate A_val and B to a closed form
  conv =>
    enter [1, 1, b, 1, u]
    rw [mul_assoc]
  conv =>
    enter [1, 1, b]
    rw [ENNReal.tsum_mul_left]
    rw [<- B_eval_open]
  rw [tsum_bool]
  rw [B_eval_false]
  rw [B_eval_true]
  simp only [A_val]


  -- Convert to real-valued inequality, simplify the left-hand side
  apply (ENNReal.toReal_le_toReal ?G1 ?G2).mp
  case G1 => sorry -- True, annoying
  case G2 => sorry --True, annoying
  simp
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 => sorry -- True, annoying
  case G2 => sorry -- True, annoying
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_div]
  rw [← ENNReal.toReal_rpow]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  skip
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 => sorry
  case G2 => sorry
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 => sorry
  case G2 => sorry
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 => sorry
  case G2 => simp
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  simp

  -- Combine the fractions
  rw [division_def]
  rw [division_def]
  repeat rw [<- mul_assoc]
  rw [<- add_mul]

  -- Distribute, rearrange
  rw [mul_sub]
  rw [mul_sub]
  simp only [mul_one]
  repeat rw [<- Real.exp_mul]
  repeat rw [<- Real.exp_add]

  -- Rewrite to apply sinh lemma (combine these steps)
  have X : (Real.exp (-ε.toReal * α + ε.toReal) - Real.exp (-ε.toReal * α) + (Real.exp (ε.toReal * α) - Real.exp (ε.toReal * α + -ε.toReal))) =
           (Real.exp (-ε.toReal * α + ε.toReal) - Real.exp (ε.toReal * α + -ε.toReal)) + ((Real.exp (ε.toReal * α) - Real.exp (-ε.toReal * α))) := by
    linarith
  rw [X]
  clear X
  have X : ε.toReal * α + -ε.toReal = (ε.toReal * (α - 1)) := by linarith
  rw [X]
  clear X
  have X : (-ε.toReal * α + ε.toReal) = -(ε.toReal * (α - 1)) := by linarith
  rw [X]
  clear X
  have X : (-ε.toReal * α) = -(ε.toReal * α) := by linarith
  rw [X]
  clear X
  have X : (Real.exp (-(ε.toReal * (α - OfNat.ofNat 1))) - Real.exp (ε.toReal * (α - OfNat.ofNat 1)) +
              (Real.exp (ε.toReal * α) - Real.exp (-(ε.toReal * α)))) =
           ((Real.exp (ε.toReal * α) - Real.exp (-(ε.toReal * α))) -
             (Real.exp (ε.toReal * (α - OfNat.ofNat 1)) - Real.exp (-(ε.toReal * (α - OfNat.ofNat 1))))) := by
    linarith
  rw [X]
  clear X

  have Hsinh (x : ℝ) : (Real.exp x - Real.exp (-x)) = 2 * Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  rw [Hsinh]
  rw [Hsinh]
  rw [Hsinh]
  have X : (OfNat.ofNat 2 * Real.sinh (ε.toReal * α) - OfNat.ofNat 2 * Real.sinh (ε.toReal * (α - OfNat.ofNat (OfNat.ofNat 1)))) * (OfNat.ofNat 2 * Real.sinh ε.toReal)⁻¹ =
           (Real.sinh (ε.toReal * α) - Real.sinh (ε.toReal * (α - OfNat.ofNat (OfNat.ofNat 1)))) * (Real.sinh ε.toReal)⁻¹ := by
    rw [mul_inv]
    repeat rw [<- mul_assoc]
    congr 1
    rw [mul_comm]
    rw [mul_sub]
    repeat rw [<- mul_assoc]
    rw [inv_mul_cancel ?G1]
    case G1 => simp
    simp
  rw [X]
  clear X
  rw [<- division_def]
  simp

  -- Apply the sinh inequality
  have W : ε.toReal = (ε.toReal * α) - ((ε.toReal * (α - 1))) := by linarith
  conv =>
    enter [1, 2]
    rw [W]
  clear W
  apply (le_trans (sinh_inequality ?G1 ?G2 ?G3))
  case G1 => sorry
  case G2 => sorry
  case G3 => sorry

  -- Simplify the eexp
  rw [sq]
  rw [<- EReal.coe_mul]
  rw [<- sq]
  have X : (α.toEReal - OfNat.ofNat 1) = (α - 1 : ℝ).toEReal := by rfl
  rw [X]
  clear X
  rw [<- EReal.coe_mul]
  rw [<- EReal.coe_mul]
  rw [<- EReal.coe_mul]
  rw [ENNReal.eexp, Real.toEReal]
  simp
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => sorry
  apply Eq.le
  congr 1
  linarith



/-
Convert ε-DP to `(1/2)ε²`-zCDP.

Note that `zCDPBound _ ε` corresponds to `(1/2)ε²`-zCDP (not `ε`-zCDP).
-/
lemma ofDP (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : zCDP q ε := by
  constructor
  · exact ACNeighbour_of_DP ε q H
  · exact ofDP_bound ε q H
