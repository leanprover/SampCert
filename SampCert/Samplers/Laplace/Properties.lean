/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Util.Util
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Basic
import SampCert.Samplers.Geometric.Basic
import Mathlib.Data.ENNReal.Inv
import SampCert.Samplers.Laplace.Code

/-!
# ``DiscreteLaplaceSample`` Properties

This file proves evaluation and normalization properties of ``DiscreteLaplaceSample``.
-/

noncomputable section

open Classical PMF Nat Real BigOperators Finset

namespace SLang

@[simp]
theorem DiscreteLaplaceSampleLoopIn1Aux_normalizes (t : PNat) :
  (∑' x : ℕ × Bool, (DiscreteLaplaceSampleLoopIn1Aux t) x) = 1 := by
  simp only [DiscreteLaplaceSampleLoopIn1Aux, Bind.bind, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, tsum_bool,
     ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
    and_true]
  conv =>
    left
    arg 1
    intro a
    congr
    · rw [ENNReal.tsum_eq_add_tsum_ite a]
    · rw [ENNReal.tsum_eq_add_tsum_ite a]
  simp only [↓reduceIte]
  have Hzero : ∀ (f : ℕ → ENNReal) (a : ℕ),
      (fun x => if x = a then (0 : ENNReal) else if a = x then f x else 0) = fun _ => 0 := by
    intro f a
    funext x
    by_cases h : x = a
    · simp [h]
    · simp [h, Ne.symm h]
  simp only [and_false, ↓reduceIte, add_zero, zero_add, mul_zero,
    mul_ite, Bool.false_eq_true, Bool.true_eq_false]
  conv =>
    left
    arg 1
    intro a
    congr
    · right; rw [show (fun x => if x = a then (0 : ENNReal) else
        if a = x then UniformSample t x * BernoulliExpNegSample x t false else 0) = fun _ => 0
          from Hzero _ a]
    · right; rw [show (fun x => if x = a then (0 : ENNReal) else
        if a = x then UniformSample t x * BernoulliExpNegSample x t true else 0) = fun _ => 0
          from Hzero _ a]
  clear Hzero
  simp only [tsum_zero, add_zero]
  conv =>
    left
    arg 1
    intro a
    rw [← mul_add]
  have hnorm : ∀ a : ℕ, BernoulliExpNegSample a t false + BernoulliExpNegSample a t true = 1 := by
    intro a; rw [← tsum_bool, BernoulliExpNegSample_normalizes]
  simp_rw [hnorm, mul_one, UniformSample_normalizes]


theorem DiscreteLaplaceSampleLoopIn1Aux_apply_true (t : PNat) (n : ℕ) :
    DiscreteLaplaceSampleLoopIn1Aux t (n, true)
      = if n < t then ENNReal.ofReal (rexp (- (n / t))) / t else 0 := by
  simp only [DiscreteLaplaceSampleLoopIn1Aux, Bind.bind, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single n]
  · rw [UniformSample_apply']
    split_ifs <;> simp [mul_comm, division_def]
  · intro x hx
    simp [Ne.symm hx]

theorem DiscreteLaplaceSampleLoopIn1Aux_apply_false (t : PNat) (n : ℕ) :
    DiscreteLaplaceSampleLoopIn1Aux t (n, false)
      = if n < t then (1 - ENNReal.ofReal (rexp (- (n / t)))) / t else 0 := by
  simp only [DiscreteLaplaceSampleLoopIn1Aux, Bind.bind, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single n]
  · rw [UniformSample_apply']
    split_ifs <;> simp [mul_comm, division_def]
  · intro x hx
    simp [Ne.symm hx]

theorem DiscreteLaplaceSampleLoopIn1_apply_pre (t : PNat) (n : ℕ) :
    (DiscreteLaplaceSampleLoopIn1 t) n =
      DiscreteLaplaceSampleLoopIn1Aux t (n, true) *
        (∑' (a : ℕ), DiscreteLaplaceSampleLoopIn1Aux t (a, true))⁻¹ := by
  simp only [DiscreteLaplaceSampleLoopIn1, Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
  simp_rw [probUntil_apply_norm _ _ _ (DiscreteLaplaceSampleLoopIn1Aux_normalizes t)]
  simp only [ENNReal.tsum_prod', ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp only [tsum_bool, Bool.false_eq_true, ↓reduceIte, zero_add, tsum_zero]
  rw [tsum_eq_single n (by
    intro x hx
    simp [Ne.symm hx])]
  simp

theorem DiscreteLaplaceSampleLoopIn1_apply (t : PNat) (n : ℕ) (support : n < t) :
    (DiscreteLaplaceSampleLoopIn1 t) n =
      ENNReal.ofReal ((rexp (-ENNReal.toReal (n / t))) *
        ((1 - rexp (- 1 / t)) / (1 - rexp (- 1)))) := by
  rw [DiscreteLaplaceSampleLoopIn1_apply_pre, DiscreteLaplaceSampleLoopIn1Aux_apply_true]
  simp only [support, ↓reduceIte]
  simp_rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
  rw [← Summable.sum_add_tsum_nat_add' (k := (t : ℕ)) ENNReal.summable]
  have hzero : ∀ i : ℕ,
      (if (i + (t : ℕ) < (t : ℕ))
        then ENNReal.ofReal (rexp (-((↑(i + ↑t) : ℝ) / ↑↑t))) / ↑↑t else (0 : ENNReal)) = 0 := by
    intro i
    rw [if_neg (by omega)]
  simp_rw [hzero, tsum_zero, add_zero]
  rw [sum_ite]
  simp only [mem_range, imp_self, forall_const, filter_true_of_mem, not_lt, not_le,
    filter_false_of_mem, sum_const_zero, add_zero]
  conv_lhs => right; right; right; intro x; rw [division_def]
  rw [← Finset.sum_mul]
  rw [ENNReal.ofReal_mul (exp_nonneg (-ENNReal.toReal (↑n / ↑↑t)))]
  rw [division_def]
  rw [mul_assoc]
  congr
  · rw [ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]
  have hsum_nn : ∀ i ∈ range t, 0 ≤ rexp (- (i / t)) :=
    fun i _ => exp_nonneg _
  rw [← ENNReal.ofReal_sum_of_nonneg hsum_nn]
  have hne : rexp (-1 / (t : ℝ)) ≠ 1 := by
    rw [← Real.exp_zero]
    by_contra h
    simp only [exp_zero, exp_eq_one_iff, div_eq_zero_iff, neg_eq_zero, one_ne_zero, cast_eq_zero,
      PNat.ne_zero, or_self] at h
  have hgeom := @geom_sum_Ico' ℝ _ (rexp (-1 / (t : ℝ))) hne 0 t (Nat.zero_le t)
  simp only [Ico_zero_eq_range, _root_.pow_zero] at hgeom
  rw [← exp_nat_mul, mul_div_cancel₀ _ (NeZero.natCast_ne ↑t ℝ)] at hgeom
  have hpow_eq : ∀ i : ℕ, rexp (-((i : ℝ) / (t : ℝ))) = rexp (-1 / (t : ℝ)) ^ i := by
    intro i
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  simp_rw [hpow_eq]
  rw [hgeom]
  rw [ENNReal.mul_inv]
  · have hpos : (0 : ℝ) < (1 - rexp (-1)) / (1 - rexp (-1 / ↑↑t)) := by
      apply _root_.div_pos
      · rw [Real.exp_neg]
        simp only [sub_pos]
        rw [inv_lt_one_iff₀]; right
        rw [one_lt_exp_iff]; exact zero_lt_one
      · simp only [sub_pos, exp_lt_one_iff]
        rw [← neg_div']
        simp [cast_pos, PNat.pos]
    rw [mul_comm, mul_assoc]
    rw [ENNReal.inv_mul_cancel (by simp) (by simp)]
    rw [← ENNReal.ofReal_inv_of_pos hpos, inv_div, mul_one]
  · right; simp
  · right; simp

@[simp]
theorem DiscreteLaplaceSampleLoopIn2_eq (num : Nat) (den : PNat) :
  DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat)
    = probGeometric (BernoulliExpNegSample num den) := by
  unfold DiscreteLaplaceSampleLoopIn2
  unfold DiscreteLaplaceSampleLoopIn2Aux
  unfold probGeometric
  unfold geoLoopCond
  unfold geoLoopBody
  rfl



@[simp]
theorem DiscreteLaplaceSampleLoop_apply (num : PNat) (den : PNat) (n : ℕ) (b : Bool) :
    (DiscreteLaplaceSampleLoop num den) (b, n)
      = ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n *
          (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) * ((2 : ℕ+) : ENNReal)⁻¹ := by
  simp only [DiscreteLaplaceSampleLoop, Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply,
    DiscreteLaplaceSampleLoopIn2_eq, tsum_bool, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single (n + 1)]
  · simp only [probGeometric_apply, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
      add_tsub_cancel_right, and_true]
    cases b <;> simp
    · erw [BernoulliSample_apply_false]
      norm_num
    · erw [BernoulliSample_apply_true]
      norm_num
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxm : x = x - 1 + 1 := (Nat.succ_pred hx0).symm
      have hne : x - 1 ≠ n := by rintro rfl; exact hx hxm
      simp [hx0, Ne.symm hne]

@[simp]
theorem ite_simpl_1 (x y : ℕ) (a : ENNReal) : ite (x = y) 0 (ite (y = x) a 0) = 0 := by
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

@[simp]
theorem ite_simpl_2 (x y : ℕ) (a : ENNReal) : ite (x = 0) 0 (ite ((y : ℤ) = -(x : ℤ)) a 0) = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hyx : (y : ℤ) = -(x : ℤ)
    · have : (x : ℤ) ≤ 0 := by omega
      have : x = 0 := by omega
      exact absurd this hx
    · simp [hx, hyx]

@[simp]
theorem ite_simpl_3 (x y : ℕ) (a : ENNReal) : ite (x = y + 1) 0 (ite (x = 0) 0 (ite (y = x - 1) a 0)) = 0 := by
  by_cases h1 : x = y + 1
  · simp [h1]
  · by_cases h2 : x = 0
    · simp [h2]
    · by_cases h3 : y = x - 1
      · have : x = y + 1 := by omega
        exact absurd this h1
      · simp [h1, h2, h3]

@[simp]
theorem ite_simpl_4 (x y : ℕ) (a : ENNReal) : ite ((x : ℤ) = - (y : ℤ)) (ite (y = 0) 0 a) 0 = 0 := by
  by_cases hy : y = 0
  · subst hy; simp
  · by_cases hxy : (x : ℤ) = -(y : ℤ)
    · have : (y : ℤ) ≤ 0 := by omega
      have : y = 0 := by omega
      exact absurd this hy
    · simp [hxy]

@[simp]
theorem ite_simpl_5 (n c : ℕ) (a : ENNReal) (h : n ≠ 0) : ite (- (n : ℤ) = (c : ℤ)) a 0 = 0 := by
  have : -(n : ℤ) ≠ (c : ℤ) := by
    intro heq
    have : (n : ℤ) = 0 := by omega
    exact h (by exact_mod_cast this)
  simp [this]

@[simp]
theorem DiscreteLaplaceSampleLoop_normalizes (num : PNat) (den : PNat) :
    (∑' x, (DiscreteLaplaceSampleLoop num den) x) = 1 := by
  have hBernNorm : ∀ h : (1 : ℕ) ≤ 2,
      BernoulliSample 1 2 h false + BernoulliSample 1 2 h true = 1 := by
    intro h
    have H := BernoulliSample_normalizes' 1 2 h
    simp only [Fintype.univ_bool, mem_singleton, not_false_eq_true, Finset.sum_insert,
      sum_singleton, Finset.mem_singleton, Bool.true_eq_false] at H
    rw [add_comm]; exact H
  simp only [DiscreteLaplaceSampleLoop, Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, Pure.pure,
    SLang.bind_apply, SLang.pure_apply, tsum_bool, ENNReal.tsum_prod', Prod.mk.injEq, mul_ite,
    mul_one, mul_zero, true_and]
  conv_lhs =>
    congr
    · arg 1; intro b
      rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite (b + 1)]
      right; right; simp
    · arg 1; intro b
      rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite (b + 1)]
      right; right; simp
  simp only [add_tsub_cancel_right, ↓reduceIte, add_eq_zero, one_ne_zero, and_false, add_zero]
  have hGeo0 : probGeometric (BernoulliExpNegSample (↑den) num) 0 = 0 := by simp
  rw [hGeo0]
  simp only [_root_.zero_le, tsub_eq_zero_of_le, zero_mul, zero_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ← mul_add]
  simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero, zero_add, and_true]
  rw [hBernNorm, mul_one]
  apply probGeometric_normalizes'
  · have A := BernoulliExpNegSample_normalizes den num
    rw [tsum_bool] at A
    trivial
  · simp

theorem avoid_double_counting_algebra (r c : ENNReal) (hr_ne_one : 1 - r ≠ 0)
    (hr_ne_top : 1 - r ≠ ⊤) :
    (∑' n : ℕ, r ^ n * (1 - r) * c) + (∑' n : ℕ, r ^ (n + 1) * (1 - r) * c) = c * (1 + r) := by
  simp_rw [pow_succ, mul_assoc _ r _, mul_comm r _, ← mul_assoc, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric]
  have hcancel : (1 - r)⁻¹ * (1 - r) = 1 :=
    ENNReal.inv_mul_cancel hr_ne_one hr_ne_top
  rw [show (1 - r)⁻¹ * (1 - r) * c = c by rw [hcancel, one_mul]]
  rw [show (1 - r)⁻¹ * (1 - r) * r * c = c * r by
    rw [hcancel, one_mul, mul_comm]]
  rw [mul_add, mul_one]

theorem avoid_double_counting (num den : PNat) :
    (∑' (x : Bool × ℕ),
        if x.1 = true → ¬x.2 = 0 then DiscreteLaplaceSampleLoop num den x else 0)
      = (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
  have hr_lt_one : ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    rw [exp_lt_one_iff, neg_lt_zero]
    exact _root_.div_pos (cast_pos.mpr (PNat.pos _)) (cast_pos.mpr (PNat.pos _))
  have hr_ne_one : 1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ≠ 0 :=
    (tsub_pos_of_lt hr_lt_one).ne'
  have hr_ne_top : 1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ≠ ⊤ :=
    ENNReal.sub_ne_top (by simp)
  simp only [ENNReal.tsum_prod', DiscreteLaplaceSampleLoop_apply, tsum_bool, IsEmpty.forall_iff,
    forall_true_left, ite_not, Bool.false_eq_true, ↓reduceIte]
  rw [tsum_shift'_1]
  exact avoid_double_counting_algebra _ _ hr_ne_one hr_ne_top

theorem laplace_normalizer_swap (num den : ℕ+) :
    (1 - rexp (-(↑↑den / ↑↑num))) * (1 + rexp (-(↑↑den / ↑↑num)))⁻¹ =
      (rexp (↑↑den / ↑↑num) - 1) * (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by
  have hA : rexp (↑↑den / ↑↑num) + 1 ≠ 0 :=
    (Right.add_pos_of_nonneg_of_pos (exp_nonneg _) one_pos).ne'
  have hB : 1 + rexp (-(↑↑den / ↑↑num)) ≠ 0 :=
    (Right.add_pos_of_pos_of_nonneg one_pos (exp_nonneg _)).ne'
  have hprod : rexp (↑↑den / ↑↑num) * rexp (-(↑↑den / ↑↑num)) = 1 := by
    rw [← exp_add]; simp
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hB hA]
  nlinarith [hprod]

theorem DiscreteLaplaceSample_one_sub_exp_nonneg (num den : PNat) :
    (0 : ℝ) ≤ 1 - rexp (-(↑↑den / ↑↑num)) := by
  simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
  exact div_nonneg (cast_nonneg _) (cast_nonneg _)

theorem DiscreteLaplaceSample_one_add_exp_pos (num den : PNat) :
    (0 : ℝ) < 1 + rexp (-(↑↑den / ↑↑num)) :=
  Right.add_pos_of_pos_of_nonneg one_pos (exp_nonneg _)

theorem DiscreteLaplaceSample_swap_mul_nonneg (num den : PNat) :
    (0 : ℝ) ≤ (rexp (↑↑den / ↑↑num) - 1) * (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by
  apply mul_nonneg
  · simp only [sub_nonneg, one_le_exp_iff]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  · exact inv_nonneg.mpr (Right.add_nonneg (exp_nonneg _) zero_le_one)


/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
theorem DiscreteLaplaceSample_apply (num den : PNat) (x : ℤ) :
  (DiscreteLaplaceSample num den) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  have hA : 0 ≤ rexp (-(↑↑den / ↑↑num)) := exp_nonneg _
  have hB : 0 ≤ rexp (↑↑den / ↑↑num) := exp_nonneg _
  have hsub_nn := DiscreteLaplaceSample_one_sub_exp_nonneg num den
  have hadd_pos := DiscreteLaplaceSample_one_add_exp_pos num den
  have hswap_nn := DiscreteLaplaceSample_swap_mul_nonneg num den
  have h2ne0 : ((2 : ℕ+) : ENNReal) ≠ 0 := by simp
  have h2netop : ((2 : ℕ+) : ENNReal) ≠ ⊤ := by simp
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply,
    ENNReal.tsum_prod', tsum_bool, ↓reduceIte,
    SLang.pure_apply, mul_ite, mul_one,
    mul_zero, one_div, Int.cast_abs]
  have hfinish : ∀ n : ℕ,
      ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n *
          (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) * ((2 : ℕ+) : ENNReal)⁻¹ *
          (((2 : ℕ+) : ENNReal) * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))))⁻¹) =
        ENNReal.ofReal ((rexp (↑↑den / ↑↑num) - 1) / (rexp (↑↑den / ↑↑num) + 1) *
          rexp (-((n : ℝ) / (↑↑num / ↑↑den)))) := by
    intro n
    rw [mul_assoc _ ((2 : ℕ+) : ENNReal)⁻¹ _, ← mul_assoc ((2 : ℕ+) : ENNReal)⁻¹ _ _,
      ENNReal.inv_mul_cancel h2ne0 h2netop, one_mul]
    rw [ENNReal.ofReal_one.symm, ← ENNReal.ofReal_add zero_le_one hA,
      ← ENNReal.ofReal_sub _ hA, ← ENNReal.ofReal_inv_of_pos hadd_pos]
    rw [mul_assoc, ← ENNReal.ofReal_mul hsub_nn, ← ENNReal.ofReal_pow hA,
      ← ENNReal.ofReal_mul (pow_nonneg hA n)]
    have hpow : rexp (-((n : ℝ) / (↑↑num / ↑↑den))) = rexp (-(↑↑den / ↑↑num)) ^ n := by
      rw [div_div_eq_mul_div, ← exp_nat_mul]
      congr 1
      field_simp
    rw [hpow]
    rw [show (rexp (↑↑den / ↑↑num) - 1) / (rexp (↑↑den / ↑↑num) + 1)
        = (1 - rexp (-(↑↑den / ↑↑num))) * (1 + rexp (-(↑↑den / ↑↑num)))⁻¹ from by
      rw [division_def, ← laplace_normalizer_swap num den]]
    exact congrArg _ (by ring)
  rw [show |(x : ℝ)| = ‖((x : ℝ) : ℂ)‖ from (Complex.norm_real _).symm]
  rcases le_or_gt 0 x with h1 | h1
  · lift x to ℕ using h1
    conv => left; left; rw [ENNReal.tsum_eq_add_tsum_ite x]
    simp only [DiscreteLaplaceSampleLoop_normalizes, probUntil_apply_norm]
    simp (config := { contextual := true }) only [↓reduceIte, IsEmpty.forall_iff, decide_true,
      DiscreteLaplaceSampleLoop_apply, decide_eq_true_eq, Nat.cast_inj, ite_simpl_1, tsum_zero,
      add_zero, forall_true_left, decide_not, Bool.not_eq_true', decide_eq_false_iff_not, ite_not,
      ite_mul, zero_mul, ite_simpl_4, NNReal.coe_natCast, inv_div,
      Bool.false_eq_true]
    rw [avoid_double_counting, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
    simp only [inv_inv]
    have hnorm : ‖(((x : ℤ) : ℝ) : ℂ)‖ = ((x : ℕ) : ℝ) := by push_cast; simp
    rw [hnorm]
    exact hfinish x
  · obtain ⟨n, h2⟩ : ∃ n : ℕ, - (n : ℤ) = x := by
      cases x with
      | ofNat _ => contradiction
      | negSucc a => exact ⟨a + 1, by push_cast; omega⟩
    conv => left; right; rw [ENNReal.tsum_eq_add_tsum_ite n]
    simp only [DiscreteLaplaceSampleLoop_normalizes, probUntil_apply_norm]
    subst h2
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [CharP.cast_eq_zero, neg_zero, lt_self_iff_false] at h1
    simp (config := { contextual := true }) only [IsEmpty.forall_iff, decide_true, ↓reduceIte,
      DiscreteLaplaceSampleLoop_apply, decide_eq_true_eq, ne_eq, hn0, not_false_eq_true, ite_simpl_5,
      tsum_zero, forall_true_left, neg_inj, Nat.cast_inj, decide_not, Bool.not_eq_true',
      decide_eq_false_iff_not, ite_not, ite_mul, zero_mul, ite_simpl_1, add_zero, zero_add,
      NNReal.coe_natCast, inv_div, Int.cast_neg, Bool.false_eq_true]
    rw [avoid_double_counting, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
    simp only [inv_inv]
    have hnorm : ‖(((-(n : ℤ)) : ℝ) : ℂ)‖ = ((n : ℕ) : ℝ) := by push_cast; simp
    rw [hnorm]
    exact hfinish n

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSample_normalizes (num den : PNat) :
    ∑' x : ℤ, (DiscreteLaplaceSample num den) x = 1 := by
  have hloop_norm := DiscreteLaplaceSampleLoop_normalizes num den
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply]
  simp_rw [probUntil_apply_norm _ _ _ hloop_norm, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  conv =>
    left
    arg 1
    intro b
    rw [ENNReal.tsum_comm]
  simp only [decide_eq_true_eq, tsum_bool, forall_true_left, ite_not, ite_mul, zero_mul,
    SLang.pure_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  have hfactor : ∀ a : ℕ, (if a = 0 then (0 : ENNReal)
      else DiscreteLaplaceSampleLoop num den (true, a) *
        ((∑' b : ℕ, if false = true → ¬b = 0 then DiscreteLaplaceSampleLoop num den (false, b) else 0)
          + ∑' b : ℕ, if b = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, b))⁻¹)
      = (if a = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, a)) *
        ((∑' b : ℕ, if false = true → ¬b = 0 then DiscreteLaplaceSampleLoop num den (false, b) else 0)
          + ∑' b : ℕ, if b = 0 then 0 else DiscreteLaplaceSampleLoop num den (true, b))⁻¹ := by
    intro a; by_cases h : a = 0 <;> simp [h]
  conv => left; right; arg 1; intro a; rw [hfactor]
  simp only [Bool.false_eq_true, false_imp_iff, ↓reduceIte]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ← add_mul]
  rw [ENNReal.mul_inv_cancel]
  · simp only [DiscreteLaplaceSampleLoop_apply, ne_eq, add_eq_zero, ENNReal.tsum_eq_zero,
      _root_.mul_eq_zero, pow_eq_zero_iff', ENNReal.ofReal_eq_zero, tsub_eq_zero_iff_le,
      ENNReal.one_le_ofReal, one_le_exp_iff, Left.nonneg_neg_iff, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, or_false, ite_eq_left_iff, not_and, not_forall, exists_prop]
    intro _
    exact ⟨1, by simp [exp_pos]⟩
  · refine ne_of_lt (lt_of_le_of_lt ?_ (by simp : (∑' (x : Bool × ℕ), DiscreteLaplaceSampleLoop num den x) < ⊤))
    rw [← ENNReal.tsum_add, ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp_rw [tsum_bool]
    exact ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp


/--
PMF for the geometric distribution as seen in literature
-/
def Geo (r : ENNReal) : SLang ℕ := (fun n => (1 - r) ^ n * r)

/-
``probGeometric`` in terms of ``Geo``
-/
lemma probGeometric_apply_Geo (t : SLang Bool) (trial_spec : t false + t true = 1)
  (trial_spec' : t true < 1) (x : ℕ) :
    probGeometric t x = if x = 0 then 0 else Geo (1 - t true) (x - 1) := by
  rw [probGeometric_apply]
  split <;> try simp
  rw [Geo]
  congr
  · rw [ENNReal.sub_sub_cancel] <;> try simp
    exact le_of_lt trial_spec'
  · exact trial_one_minus t trial_spec


/--
Closed for for partial geometric series
-/
lemma partial_geometric_series {p : ENNReal} (HP2 : p < 1) (B : ℕ) :
    (∑' (a : ℕ), if a < B then p ^ a else 0) = (1 - p ^ B) / (1 - p) := by
  induction B
  · simp
  · rename_i n IH
    have H (a : ℕ) D : @ite ENNReal (a < n + 1) D (p^a) 0 = (if (a < n) then p^a else 0) + (if a = n then p^a else 0):= by
      split
      · rename_i H
        split
        · split
          · exfalso
            linarith
          · simp
        · split
          · simp
          · exfalso
            apply le_of_lt_succ at H
            apply Nat.le_iff_lt_or_eq.mp at H
            cases H
            · trivial
            · trivial
      · split
        · exfalso
          linarith
        · split
          · exfalso
            linarith
          · simp
    conv =>
      enter [1, 1, a]
      rw [H]
    clear H
    rw [ENNReal.tsum_add]
    rw [IH]
    rw [tsum_eq_single n ?G1]
    case G1 =>
      intro _ _
      simp
      intro _
      trivial
    simp

    have SC1 : (1 - p) ≠ 0 := by
      apply pos_iff_ne_zero.mp
      simp_all only [tsub_pos_iff_lt]
    have SC2 : (1 - p) ≠ ⊤ := by
      apply ENNReal.sub_ne_top
      simp
    have SC3 : 0 < p → p < 1 → p ^ n ≠ ⊤ := by
      intro _ _
      apply ENNReal.pow_ne_top
      exact LT.lt.ne_top HP2

    apply (ENNReal.mul_left_inj (c := 1 - p) SC1 SC2).mp
    rw [add_mul]
    conv =>
      congr
      · congr
        · rw [division_def]
          rw [mul_assoc]
          rw [ENNReal.inv_mul_cancel SC1 SC2]
          simp
        · rw [ENNReal.mul_sub SC3]
          simp
      · rw [division_def]
        rw [mul_assoc]
        rw [ENNReal.inv_mul_cancel SC1 SC2]
        simp
    suffices ((1 - p ^ n + (p ^ n - p ^ n * p)).toReal = (1 - p ^ (n + 1)).toReal) by
      apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
      cases this
      · trivial
      · exfalso
        rename_i HK
        simp_all
    rw [ENNReal.toReal_add ?G1 ?G2]
    case G1 =>
      apply ENNReal.sub_ne_top
      simp
    case G2 =>
      apply ENNReal.sub_ne_top
      apply ENNReal.pow_ne_top
      exact LT.lt.ne_top HP2
    rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
    case G1 =>
      refine pow_le_one' ?H n
      exact le_of_lt HP2
    case G2 => simp
    rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
    case G1 =>
      conv =>
        rhs
        rw [<- mul_one (p ^ n)]
      cases Classical.em (p = 0)
      · simp_all
      · apply (ENNReal.mul_le_mul_iff_right ?G3 ?G4).mpr
        case G3 =>
          apply ENNReal.pow_ne_zero
          assumption
        case G4 =>
          apply ENNReal.pow_ne_top
          exact LT.lt.ne_top HP2
        exact le_of_lt HP2
    case G2 =>
      apply ENNReal.pow_ne_top
      exact LT.lt.ne_top HP2
    rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
    case G1 =>
      refine pow_le_one' ?H (n + 1)
    case G2 => simp
    simp_all only [ne_eq, ENNReal.sub_eq_top_iff, ENNReal.one_ne_top, false_and, not_false_eq_true,
      ENNReal.pow_eq_top_iff, not_and, Decidable.not_not, true_implies, ENNReal.toReal_one, ENNReal.toReal_pow,
      ENNReal.toReal_mul, sub_add_sub_cancel, sub_right_inj]
    rfl


/--
Integer division of a geometric distribution is a geometric distribution
-/
lemma geo_div_geo (k n : ℕ) (p : ENNReal) (Hp : p < 1) (Hn : 0 < n) :
      (Geo (1-p) >>= (fun v => Pure.pure (v / n))) k = Geo (1-(p ^ n)) k := by
  rw [Geo]
  simp

  -- Convert integer division equality into integer inequalities
  have H : (∑' (a : ℕ), if k = a / n then Geo (1 - p) a else 0) =
           (∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then Geo (1 - p) a else 0) := by
      apply tsum_congr
      intro b
      congr
      apply propext
      apply @nat_div_eq_le_lt_iff k b n Hn
  rw [H]
  clear H

  -- Eliminate constant factor from Geo and simplify
  conv =>
    enter [1, 1, a]
    rw [Geo]
  have H : (∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then (1 - (1 - p)) ^ a * (1 - p) else 0) =
           (∑' (a : ℕ), (1 - p) * if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then p ^ a else 0) := by
    apply tsum_congr
    intro b
    split
    · rw [mul_comm]
      congr
      apply ENNReal.sub_sub_cancel
      · simp
      · exact le_of_lt Hp
    · rw [mul_zero]
  rw [H]
  clear H
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp
  case G2 =>
    apply Right.pow_le_one_of_le
    exact le_of_lt Hp

  have SC1 : (1 - p) ≠ 0 := by
    apply pos_iff_ne_zero.mp
    simp_all only [tsub_pos_iff_lt]
  have SC2 : (1 - p) ≠ ⊤ := by
    apply ENNReal.sub_ne_top
    simp

  -- Rewrite to difference of partial geometric series
  have H : (∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then p ^ a else 0) =
           (∑' (a : ℕ), if a < (k + 1) * n then p ^ a else 0) -  (∑' (a : ℕ), if a < k * n then p ^ a else 0) := by
    symm
    apply ENNReal.sub_eq_of_eq_add
    · rw [partial_geometric_series Hp]
      rw [division_def]
      apply ENNReal.mul_ne_top
      · apply ENNReal.sub_ne_top
        simp
      · apply ENNReal.inv_ne_top.mpr
        apply SC1
    rw [<- ENNReal.tsum_add]
    apply tsum_congr
    intro b
    by_cases h1 : k * n ≤ b
    · by_cases h2 : b < (k + 1) * n
      · have h3 : ¬ b < k * n := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ b < k * n := by omega
        simp [h1, h2, h3]
    · have h3 : b < k * n := by omega
      have h2 : b < (k + 1) * n := by
        have : k * n ≤ (k + 1) * n := by nlinarith
        omega
      simp [h1, h2, h3]
  rw [H]
  clear H

  -- Evaluate partial geometric series
  rw [partial_geometric_series Hp]
  rw [partial_geometric_series Hp]

  -- Conclude by simplification

  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intro _ _
    apply SC2

  conv =>
    lhs
    congr
    · rw [division_def]
      rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel SC1 SC2]
      simp
    · rw [division_def]
      rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel SC1 SC2]
      simp
  suffices ((1 - p ^ ((k + 1) * n) - (1 - p ^ (k * n))).toReal = ((p ^ n) ^ k * (1 - p ^ n)).toReal) by
    apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
    cases this
    · trivial
    · simp_all
      rename_i HK
      rcases HK with ⟨ _ , HK ⟩
      apply ENNReal.mul_eq_top.mp at HK
      simp_all only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not, and_imp, ENNReal.sub_eq_top_iff,
        ENNReal.one_ne_top, ENNReal.pow_eq_top_iff, false_and, and_false, false_or, not_top_lt]
  simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    cases (Classical.em (p = 0))
    · rename_i H
      rw [H]
      simp
      rw [zero_pow_eq]
      split
      · rw [zero_pow_eq]
        split
        · simp
        · exfalso
          simp_all
      · simp_all
    · apply (ENNReal.sub_le_sub_iff_left ?G3 ?G4).mpr
      case G3 =>
        apply pow_le_one'
        exact le_of_lt Hp
      case G4 =>
        simp
      rw [add_mul]
      simp
      rw [pow_add]
      -- conv =>
      --   rhs
      --   rw [<- (mul_one (p^(k*n)))]
      apply ENNReal.mul_le_of_le_div'
      rw [division_def]
      rw [ENNReal.mul_inv_cancel ?G3 ?G4]
      case G3 =>
        apply ENNReal.pow_ne_zero
        trivial
      case G4 =>
        apply ENNReal.pow_ne_top
        exact LT.lt.ne_top Hp
      apply Right.pow_le_one_of_le
      exact le_of_lt Hp
  case G2 =>
    apply ENNReal.sub_ne_top
    simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply pow_le_one'
    exact le_of_lt Hp
  case G2 => simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply pow_le_one'
    exact le_of_lt Hp
  case G2 => simp
  simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply pow_le_one'
    exact le_of_lt Hp
  case G2 => simp
  simp
  rw [mul_sub]
  simp
  congr 1
  · exact pow_mul' p.toReal k n
  · conv =>
      rhs
      rw [<- pow_mul']
    rw [<- pow_add]
    congr
    exact succ_mul k n


/--
Equivalence between sampling loops
-/
theorem DiscreteLaplaceSampleLoop_equiv (num : PNat) (den : PNat) :
  DiscreteLaplaceSampleLoop num den = DiscreteLaplaceSampleLoop' num den := by
  apply SLang.ext
  intro ⟨ b, n ⟩
  simp [DiscreteLaplaceSampleLoop_apply]
  simp only [DiscreteLaplaceSampleLoop']


  -- Evaluate the indepenent Bern(1/2) sample
  have H :
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
        Pure.pure (B, (U + ↑num * (v - 1)) / ↑den)) (b, n) =
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        Pure.pure ((U + ↑num * (v - 1)) / ↑den)) (n) * 2⁻¹ := by
      simp
      rw [<- ENNReal.tsum_mul_right]
      congr
      apply funext
      intro x
      rw [mul_assoc]
      congr
      rw [<- ENNReal.tsum_mul_right]
      congr
      apply funext
      intro y
      have HB : ∀ c : Bool, BernoulliSample 1 2 (Nat.le.step Nat.le.refl) c = 2⁻¹ := by
        intro c
        cases c
        · erw [BernoulliSample_apply_false]
          norm_num
        · erw [BernoulliSample_apply_true]
          norm_num
      split <;> try simp [HB]
      all_goals (try (cases b <;> simp [HB]))
  rw [H]
  clear H
  congr

  -- Evaluate the DiscreteSampleLoopIn2 term to geometric distribution and reindex
  have H :
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        (Pure.pure ((U + ↑num * (v - 1)) / ↑den))) n =
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← Geo (1 - ENNReal.ofReal (Real.exp (- 1)))
        (Pure.pure ((U + ↑num * v) / ↑den))) n := by
    simp only [Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, bind_apply]
    apply tsum_congr
    intro a
    congr 1

    have S1 : BernoulliExpNegSample 1 1 false + BernoulliExpNegSample 1 1 true = 1 := by
      have A := BernoulliExpNegSample_normalizes 1 1
      rw [tsum_bool] at A
      assumption
    have S2 : BernoulliExpNegSample 1 1 true < 1 := by
      rw [BernoulliExpNegSample_apply_true]
      apply ENNReal.ofReal_lt_one.mpr
      apply exp_lt_one_iff.mpr
      simp
    conv =>
      enter [1, 1, b]
      rw [probGeometric_apply_Geo _ S1 S2]
    conv =>
      enter [2]
      rw [<- tsum_shift_1]
    apply tsum_congr
    intro b
    split <;> try simp
  rw [H]
  clear H

  -- Separate X and Y
  have H : (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
             let v ← Geo (1 - ENNReal.ofReal (Real.exp (- 1)))
             Pure.pure ((U + ↑num * v) / ↑den)) =
           (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
             let v ← Geo (1 - ENNReal.ofReal (Real.exp (- 1)))
             Pure.pure ((U + ↑num * v))) >>=
           (fun X =>  Pure.pure (X / ↑den)) := by simp
  rw [H]
  clear H

  generalize HX : (do
          let U ← DiscreteLaplaceSampleLoopIn1 num
          let v ← Geo (1 - ENNReal.ofReal (Real.exp (-1)))
          Pure.pure (U + ↑num * v) : SLang ℕ) = X

  -- Fold the left hand side into Geo
  have H : ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) =
           Geo (1 - ENNReal.ofReal (Real.exp (-((den : ℝ) / (num : ℝ))))) n := by
    rw [Geo]
    rw [ENNReal.sub_sub_cancel]
    · simp
    apply ENNReal.ofReal_le_one.mpr
    apply exp_le_one_iff.mpr
    simp
    apply div_nonneg
    · exact cast_nonneg ↑den
    · exact cast_nonneg ↑num
  rw [H]
  clear H

  -- Apply the Geo lemma
  have H : Geo (1 - ENNReal.ofReal (Real.exp (-(↑↑den / ↑↑num)))) n = Geo (1 - (ENNReal.ofReal (Real.exp (-(1 / ↑↑num)))) ^ (den : ℕ)) n := by
    congr
    suffices (ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))).toReal =
             (ENNReal.ofReal (rexp (-(1 / ↑↑num))) ^ (den : ℕ)).toReal by
      apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
      cases this
      · trivial
      · simp_all
    simp_all
    rw [ENNReal.toReal_ofReal ?G1]
    case G1 => apply exp_nonneg
    rw [ENNReal.toReal_ofReal ?G1]
    case G1 => apply exp_nonneg
    rw [← exp_nat_mul]
    congr
    simp [division_def]
  rw [H]
  clear H
  rw [<- geo_div_geo n den (ENNReal.ofReal (Real.exp (-(1 / ↑↑num)))) ?G1 ?G2]
  case G1 =>
    apply ENNReal.ofReal_lt_one.mpr
    apply exp_lt_one_iff.mpr
    simp
  case G2 => exact PNat.pos den
  simp only [Bind.bind, Pure.pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
  apply tsum_congr
  intro b
  congr 1

  -- Prove that X is geometric
  rw [<- HX]
  clear HX

  -- Decompose b by Euclidean division, in order to obtain independent samples
  rcases euclidean_division b (PNat.pos num) with ⟨ bu, bv, Hbv, Hb ⟩
  rw [Hb]
  simp only [one_div, Bind.bind, Pure.pure, bind_apply, pure_apply]

  -- Evaluate the sum (as a singleton)
  conv =>
    enter [2, 1, x]
    rw [<- ENNReal.tsum_mul_left]
  rw [<- ENNReal.tsum_prod]
  rw [tsum_eq_single (bv, bu) ?G1]
  case G1 =>
    intro ⟨b'v, b'u⟩ Hne
    simp
    intro He
    cases (Classical.em (b'v < num))
    · rename_i Hsupport
      exfalso
      apply Hne
      have W := (euclidean_division_uniquness bv b'v bu b'u (PNat.pos num) Hbv Hsupport).mp He
      simp_all
    · rename_i Hnsupport
      left
      simp [DiscreteLaplaceSampleLoopIn1]
      simp [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
      intro Hk
      exfalso
      apply Hnsupport
      apply Hk

  -- Simplify RHS
  simp
  rw [Geo]
  rw [Geo]
  rw [DiscreteLaplaceSampleLoopIn1_apply _ _ Hbv]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp
  case G2 =>
    apply ENNReal.ofReal_le_one.mpr
    apply exp_le_one_iff.mpr
    simp
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp
  case G2 =>
    apply ENNReal.ofReal_le_one.mpr
    apply exp_le_one_iff.mpr
    simp


  suffices ENNReal.toReal (ENNReal.ofReal (rexp (-num.val.cast⁻¹)) ^ (bv + num.val * bu) * (OfNat.ofNat 1 - ENNReal.ofReal (rexp (-num.val.cast⁻¹)))) =
           ENNReal.toReal (ENNReal.ofReal (rexp (-(ENNReal.toReal (bv.cast / num.val.cast))) * ((OfNat.ofNat 1 - rexp (-OfNat.ofNat 1 / num.val.cast)) / (OfNat.ofNat 1 - rexp (-OfNat.ofNat 1)))) *
             (ENNReal.ofReal (rexp (-OfNat.ofNat 1)) ^ bu * (OfNat.ofNat 1 - ENNReal.ofReal (rexp (-OfNat.ofNat 1))))) by
    apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
    cases this
    · trivial
    · exfalso
      simp_all
      rename_i h
      rcases h with ⟨ _ , B ⟩ | ⟨ B , _ ⟩
      · apply ENNReal.mul_eq_top.mp at B
        simp at B
        rcases B with ⟨ _ , B ⟩
        apply ENNReal.mul_eq_top.mp at B
        simp at B
      · apply ENNReal.mul_eq_top.mp at B
        simp at B

  simp_all
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 =>
    apply mul_nonneg
    · apply exp_nonneg
    · rw [division_def]
      apply mul_nonneg
      · apply sub_nonneg.mpr
        apply exp_le_one_iff.mpr
        apply div_nonpos_iff.mpr
        right
        apply And.intro
        · apply toNNReal_eq_zero.mp
          simp only [toNNReal_eq_zero, Left.neg_nonpos_iff, zero_le_one]
        · apply cast_nonneg
      · apply inv_nonneg_of_nonneg
        apply sub_nonneg.mpr
        apply exp_le_one_iff.mpr
        simp

  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply exp_nonneg
  conv =>
    enter [2, 1, 2]
    rw [division_def]
  try simp
  repeat rw [<- mul_assoc]
  rw [<- Real.exp_nat_mul]
  simp
  have H : (1 : ℝ) = OfNat.ofNat (1 : ℕ) := by rfl
  conv =>
    enter [2]
    rw [mul_assoc]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [H]
  rw [mul_inv_cancel₀ ?G1]
  case G1 =>
    apply sub_ne_zero.mpr
    apply _root_.ne_of_gt
    apply exp_lt_one_iff.mpr
    simp
  simp
  conv =>
    enter [2]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
  rw [H]
  rw [<- mul_assoc]
  congr
  · rw [<- Real.exp_nat_mul]
    rw [<- Real.exp_add]
    congr 1
    field_simp
    ring
  · rw [division_def]
    simp

/--
Equivalence between discrete Laplace sampelrs
-/
lemma DiscreteLaplaceSample_equiv (num den : PNat) :
    DiscreteLaplaceSample num den = DiscreteLaplaceSampleOptimized num den := by
  rw [DiscreteLaplaceSample, DiscreteLaplaceSampleOptimized, DiscreteLaplaceSampleLoop_equiv]

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSampleOptimized_normalizes (num den : PNat) :
    ∑' x : ℤ, (DiscreteLaplaceSampleOptimized num den) x = 1 := by
  rw [<- DiscreteLaplaceSample_equiv]
  apply DiscreteLaplaceSample_normalizes

/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
theorem DiscreteLaplaceSampleOptimized_apply (num den : PNat) (x : ℤ) :
    (DiscreteLaplaceSampleOptimized num den) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  rw [<- DiscreteLaplaceSample_equiv]
  apply DiscreteLaplaceSample_apply

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSampleMixed_normalizes (num den : PNat) (mix : ℕ) :
    ∑' x : ℤ, (DiscreteLaplaceSampleMixed num den mix) x = 1 := by
  rw [DiscreteLaplaceSampleMixed]
  split
  · exact DiscreteLaplaceSample_normalizes num den
  · exact DiscreteLaplaceSampleOptimized_normalizes num den

/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
theorem DiscreteLaplaceSampleMixed_apply (num den : PNat) (mix : ℕ) (x : ℤ) :
    (DiscreteLaplaceSampleMixed num den mix) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  rw [DiscreteLaplaceSampleMixed]
  split
  · exact DiscreteLaplaceSample_apply num den x
  · exact DiscreteLaplaceSampleOptimized_apply num den x

/--
Equivalence between discrete Laplace sampelrs
-/
lemma DiscreteLaplaceSampleMixed_equiv (num den : PNat) (mix : ℕ) :
    DiscreteLaplaceSampleMixed num den mix = DiscreteLaplaceSample num den := by
  rw [DiscreteLaplaceSampleMixed]
  split
  · rfl
  · symm
    apply DiscreteLaplaceSample_equiv

end SLang
