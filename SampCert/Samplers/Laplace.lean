/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import SampCert.Samplers.BernoulliNegativeExponential
import SampCert.Foundations.GeometricGen

open Classical PMF Nat Real BigOperators Finset

noncomputable def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : RandomM (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

@[simp]
theorem DiscreteLaplaceSampleLoopIn1Aux_normalizes (t : PNat) :
  (∑' x : ℕ × Bool, (DiscreteLaplaceSampleLoopIn1Aux t) x) = 1 := by
  simp only [DiscreteLaplaceSampleLoopIn1Aux, Bind.bind, Pure.pure, SubPMF.bind_apply,
    SubPMF.pure_apply, tsum_bool,  NNReal.coe_nat_cast,
     ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
    and_true, and_false, ↓reduceIte, add_zero, zero_add]
  conv =>
    left
    right
    intro a
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
  simp only [↓reduceIte, NNReal.coe_nat_cast]
  have A : forall x a, (@ite ENNReal (x = a) (Classical.propDecidable (x = a)) 0
      (if a = x then UniformSample t x * BernoulliExpNegSample x t false else 0)) = 0 := by
    intro x a
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  have B : forall x a, (@ite ENNReal (x = a) (Classical.propDecidable (x = a)) 0
      (if a = x then UniformSample t x * BernoulliExpNegSample x t true else 0)) = 0 := by
    intro x a
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    intro a
    congr
    . right
      right
      intro x
      rw [A]
    . right
      right
      intro x
      rw [B]
  clear A B
  simp only [ NNReal.coe_nat_cast, tsum_zero, add_zero]
  conv =>
    left
    right
    intro a
    rw [← mul_add]
  have A : ∀ a, BernoulliExpNegSample a t false + BernoulliExpNegSample a t true = 1 := by
    intro a
    rw [← tsum_bool]
    rw [BernoulliExpNegSample_normalizes]
  conv =>
    left
    right
    intro a
    rw [A]
  clear A
  simp

theorem DiscreteLaplaceSampleLoopIn1Aux_apply_true (t : PNat) (n : ℕ) :
  DiscreteLaplaceSampleLoopIn1Aux t (n, true)
    = if n < t then ENNReal.ofReal (rexp (- (n / t))) / t else 0 := by
  simp [DiscreteLaplaceSampleLoopIn1Aux]
  conv =>
    left
    right
    intro a
    rw [tsum_bool]
  simp only [and_false, ↓reduceIte, and_true,  NNReal.coe_nat_cast,
    zero_add, mul_ite, mul_zero]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  have A : ∀ x, (@ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
      (@ite ENNReal (n = x) (instDecidableEqNat n x) (UniformSample t x * BernoulliExpNegSample x t true) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [A]
  simp only [↓reduceIte, NNReal.coe_nat_cast, tsum_zero, add_zero]
  rw [UniformSample_apply']
  rw [BernoulliExpNegSample_apply_true n]
  simp
  rw [mul_comm]
  rw [← division_def]

theorem DiscreteLaplaceSampleLoopIn1Aux_apply_false (t : PNat) (n : ℕ) :
  DiscreteLaplaceSampleLoopIn1Aux t (n, false)
    = if n < t then (1 - ENNReal.ofReal (rexp (- (n / t)))) / t else 0 := by
  simp [DiscreteLaplaceSampleLoopIn1Aux]
  conv =>
    left
    right
    intro a
    rw [tsum_bool]
  simp only [and_true,  NNReal.coe_nat_cast, and_false,
    ↓reduceIte, add_zero, mul_ite, mul_zero]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  have A : ∀ x, (@ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
      (@ite ENNReal (n = x) (instDecidableEqNat n x) (UniformSample t x * BernoulliExpNegSample x t false) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [A]
  simp only [↓reduceIte, NNReal.coe_nat_cast, tsum_zero,
    add_zero]
  rw [UniformSample_apply']
  rw [BernoulliExpNegSample_apply_false]
  simp
  rw [mul_comm]
  rw [← division_def]

noncomputable def DiscreteLaplaceSampleLoopIn1 (t : PNat) : RandomM Nat := do
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
  return r1.1

theorem DiscreteLaplaceSampleLoopIn1_apply_pre (t : PNat) (n : ℕ) :
  (DiscreteLaplaceSampleLoopIn1 t) n =
    DiscreteLaplaceSampleLoopIn1Aux t (n, true) * (∑' (a : ℕ), DiscreteLaplaceSampleLoopIn1Aux t (a, true))⁻¹ := by
  simp only [DiscreteLaplaceSampleLoopIn1, Bind.bind, Pure.pure, SubPMF.bind_apply, ite_mul, zero_mul, SubPMF.pure_apply]
  conv =>
    left
    right
    intro a
    rw [prob_until_apply_norm _ _ _ (DiscreteLaplaceSampleLoopIn1Aux_normalizes t)]
  simp [tsum_prod']
  rw [ENNReal.tsum_comm]
  simp [tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp
  have A : ∀ x, (@ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
            (DiscreteLaplaceSampleLoopIn1Aux t (x, true) * (∑' (b : ℕ), DiscreteLaplaceSampleLoopIn1Aux t (b, true))⁻¹ *
            @ite ENNReal (n = x) (Classical.propDecidable (n = (x, true).1)) 1 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        contradiction
      . simp
  conv =>
    left
    right
    right
    intro x
    rw [A]
  clear A
  simp

theorem DiscreteLaplaceSampleLoopIn1_apply (t : PNat) (n : ℕ) (support : n < t) :
  (DiscreteLaplaceSampleLoopIn1 t) n = (ENNReal.ofReal ((rexp (-ENNReal.toReal (n / t))) * ((1 - rexp (- 1 / t)) / (1 - rexp (- 1))))) := by
  rw [DiscreteLaplaceSampleLoopIn1_apply_pre]
  rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
  simp [support]
  conv =>
    left
    right
    right
    right
    intro a
    rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]

  rw [← @sum_add_tsum_nat_add' ENNReal _ _ _ _ _ t ENNReal.summable]
  have B : ∀ i : ℕ, (@ite ENNReal (i + ↑t < ↑t) (decLt (i + ↑t) ↑t) ((ENNReal.ofReal (rexp (- (↑(i + ↑t) / ↑↑t)))) / ↑↑t) 0) = 0 := by
    intro i
    split
    . rename_i h
      simp at h
    . simp
  conv =>
    left
    right
    right
    right
    right
    intro i
    rw [B]
  clear B
  simp

  rw [sum_ite]
  simp

  conv =>
    left
    right
    right
    right
    intro x
    rw [division_def]

  have A := @sum_mul ℕ ENNReal _ (Finset.range t) (fun x => ENNReal.ofReal (rexp (- (↑x / ↑↑t)))) ((↑↑t)⁻¹)
  rw [← A]
  clear A

  rw [ENNReal.ofReal_mul (exp_nonneg (-ENNReal.toReal (↑n / ↑↑t)))]
  rw [division_def]
  rw [mul_assoc]
  congr

  . rw [ENNReal.toReal_div]
    simp

  . have A : ∀ i ∈ range t, 0 ≤ rexp (- (i / t)) := by
      intro i _
      apply exp_nonneg (-(↑i / ↑↑t))

    rw [← ENNReal.ofReal_sum_of_nonneg A]
    clear A

    have A : rexp (- 1 / t) ≠ 1 := by
      rw [← Real.exp_zero]
      by_contra h
      simp at h
    have X := @geom_sum_Ico' ℝ _ (rexp (- 1 / t)) A 0 t (Nat.zero_le t)
    simp at X
    rw [← exp_nat_mul] at X
    rw [mul_div_cancel' _ (NeZero.natCast_ne ↑t ℝ)] at X

    conv =>
      left
      right
      right
      left
      right
      right
      intro i
      rw [division_def]
      rw [neg_mul_eq_mul_neg]
      rw [Real.exp_nat_mul]
      rw [inv_eq_one_div]
      rw [neg_div']

    rw [X]
    clear X
    rw [ENNReal.mul_inv]
    . rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel]
      . rw [ENNReal.ofReal_inv_of_pos]
        . rw [inv_div]
          simp
        . apply div_pos
          . rw [Real.exp_neg]
            simp
            rw [inv_lt_one_iff]
            right
            rw [one_lt_exp_iff]
            simp
          . simp
            rw [← neg_div']
            simp
      . simp
      . simp
    . simp
    . simp

-- Note that for the arxiv algorithm, we can call Unit directly
noncomputable def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat)  (K : Bool × Nat) : RandomM (Bool × Nat) := do
  let A ← BernoulliExpNegSample num den
  return (A, K.2 + 1)

noncomputable def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : RandomM Nat := do
  let r2 ← prob_while (λ K : Bool × Nat => K.1) (DiscreteLaplaceSampleLoopIn2Aux num den) (true,0)
  return r2.2

@[simp]
theorem DiscreteLaplaceSampleLoopIn2_eq (num : Nat) (den : PNat) :
  DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat)
    = Geometric.geometric (BernoulliExpNegSample num den) := by
  unfold DiscreteLaplaceSampleLoopIn2
  unfold DiscreteLaplaceSampleLoopIn2Aux
  unfold Geometric.geometric
  unfold Geometric.loop_cond
  unfold Geometric.loop_body
  rfl

-- We need to generate and test both implementations
noncomputable def DiscreteLaplaceSampleLoop' (num : PNat) (den : PNat) : RandomM (Bool × Nat) := do
  let U ← DiscreteLaplaceSampleLoopIn1 num
  let v ← DiscreteLaplaceSampleLoopIn2 1 1
  let V := v - 1
  let X := U + num * V
  let Y := X / den
  let B ← BernoulliSample 1 2 (le.step le.refl)
  return (B,Y)

noncomputable def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : RandomM (Bool × Nat) := do
  let v ← DiscreteLaplaceSampleLoopIn2 den num
  let V := v - 1
  let B ← BernoulliSample 1 2 (le.step le.refl)
  return (B,V)

@[simp]
theorem DiscreteLaplaceSampleLoop_apply (num : PNat) (den : PNat) (n : ℕ) (b : Bool) :
  (DiscreteLaplaceSampleLoop num den) (b,n)
    = ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) * ((2 : ℕ+): ENNReal)⁻¹ := by
  simp [DiscreteLaplaceSampleLoop, tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
  simp
  have A : ∀ x, (@ite ENNReal (x = n + 1) (Classical.propDecidable (x = n + 1)) 0
      (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0
  (ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ (x - 1) * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) *
    ((if b = false ∧ n = x - 1 then 1 - ((2 : ℕ+): ENNReal)⁻¹ else 0) + if b = true ∧ n = x - 1 then ((2 : ℕ+): ENNReal)⁻¹ else 0))) ) = 0 := by
    intro x
    split
    . simp
    . split
      . simp
      . split
        . split
          . rename_i h1 h2 h3 h4
            cases h3
            cases h4
            rename_i h5 h6 h7 h8
            subst h7
            contradiction
          . rename_i h1 h2 h3 h4
            cases h3
            simp at h4
            rename_i h5 h6
            subst h6
            have B : x = x - 1 + 1 := by
              exact (succ_pred h2).symm
            contradiction
        . split
          . rename_i h1 h2 h3 h4
            cases h4
            rename_i h5 h6
            subst h6
            have B : x = x - 1 + 1 := by
              exact (succ_pred h2).symm
            contradiction
          . rename_i h1 h2 h3 h4
            simp at *

  conv =>
    left
    right
    right
    intro x
    rw [A]
  clear A

  simp
  congr
  split
  . rename_i h
    simp [h]
    exact ENNReal.one_sub_inv_two
  . simp
    rename_i h1
    intro h2
    contradiction

@[simp]
theorem ite_simpl_1 (x y : ℕ) (a : ENNReal) : ite (x = y) 0 (ite (y = x) a 0) = 0 := by
  split
  . simp
  . rename_i h
    simp [h]
    intro h
    subst h
    contradiction

@[simp]
theorem ite_simpl_2 (x y : ℕ) (a : ENNReal) : ite (x = 0) 0 (ite ((y : ℤ) = -(x : ℤ)) a 0) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      have A : (y : ℤ) ≥ 0 := Int.NonNeg.mk (y + 0)
      rw [h2] at A
      simp at *
      subst A
      contradiction
    . simp

@[simp]
theorem ite_simpl_3 (x y : ℕ) (a : ENNReal) : ite (x = y + 1) 0 (ite (x = 0) 0 (ite (y = x - 1) a 0)) = 0 := by
  split
  . simp
  . split
    . simp
    . split
      . rename_i h1 h2 h3
        subst h3
        cases x
        . contradiction
        . simp at h1
      . simp

@[simp]
theorem ite_simpl_4 (x y : ℕ) (a : ENNReal) : ite ((x : ℤ) = - (y : ℤ)) (ite (y = 0) 0 a) 0 = 0 := by
  split
  . split
    . simp
    . rename_i h1 h2
      have B : (y : ℤ) ≥ 0 := by exact Int.NonNeg.mk (y + 0)
      have C : -(y : ℤ) ≥ 0 := by exact le_iff_exists_sup.mpr (Exists.intro (Int.ofNat x) (id h1.symm))
      cases y
      . contradiction
      . rename_i n
        simp at C
        contradiction
  . simp

@[simp]
theorem DiscreteLaplaceSampleLoop_normalizes (num : PNat) (den : PNat) :
  (∑' x, (DiscreteLaplaceSampleLoop num den) x) = 1 := by
  simp only [DiscreteLaplaceSampleLoop, Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, Pure.pure,
    SubPMF.bind_apply,
    NNReal.coe_nat_cast,  cast_one,
    one_div, SubPMF.pure_apply, ite_mul, tsum_bool, ↓reduceIte, zero_mul, ENNReal.tsum_prod',
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, true_and, false_and, add_zero, zero_add]
  conv =>
    left
    left
    right
    intro b
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    rw [ENNReal.tsum_eq_add_tsum_ite (b + 1)]
    right
    right
    simp
  conv =>
    left
    right
    right
    intro b
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    rw [ENNReal.tsum_eq_add_tsum_ite (b + 1)]
    right
    right
    simp

  simp only [add_tsub_cancel_right, ↓reduceIte,  add_eq_zero, one_ne_zero,
    and_false,  NNReal.coe_nat_cast,
     cast_one, one_div, ite_mul, zero_mul]

  simp only [add_zero]

  have A : Geometric.geometric (BernoulliExpNegSample (↑den) num) 0 = 0 := by simp
  rw [A]
  simp only [ge_iff_le, _root_.zero_le, tsub_eq_zero_of_le, ↓reduceIte,
    cast_one, one_div, zero_mul, ite_self,  add_eq_zero, one_ne_zero,
    and_false, NNReal.coe_nat_cast, add_tsub_cancel_right,
     zero_add]

  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [← mul_add]
  have A := BernoulliSample_normalizes' 1 2 DiscreteLaplaceSampleLoop.proof_1
  simp only [Fintype.univ_bool, cast_one, one_div, mem_singleton,
    not_false_eq_true, sum_insert, ↓reduceIte, sum_singleton] at A
  rw [add_comm] at A
  rw [A]
  clear A
  rw [mul_one]
  apply Geometric.geometric_normalizes'
  . have A := BernoulliExpNegSample_normalizes den num
    rw [tsum_bool] at A
    trivial
  . simp
    rw [div_pos_iff]
    left
    simp

noncomputable def DiscreteLaplaceSample (num den : PNat) : RandomM ℤ := do
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

theorem avoid_double_counting (num den : PNat) :
  (∑' (x : Bool × ℕ), if x.1 = true → ¬x.2 = 0 then DiscreteLaplaceSampleLoop num den x else 0)
    = (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
  simp [ENNReal.tsum_prod', tsum_bool]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [tsum_shift'_1]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [mul_comm]
  conv =>
    left
    right
    rw [mul_comm]
  rw [← mul_add]
  conv =>
    left
    right
    rw [mul_comm]
  conv =>
    left
    right
    right
    rw [mul_comm]
  rw [← mul_add]

  -- have A : ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) < 1 := by
  --   have B := @one_lt_exp_iff (-(↑↑den / ↑↑num))
  --   simp
  --   clear B
  --   rw [div_pos_iff]
  --   left
  --   simp
  rw [ENNReal.tsum_geometric]
  conv =>
    left
    right
    right
    right
    right
    intro i
    rw [pow_add]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_geometric]
  rw [mul_add]
  have B : (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) ≠ 0 := by
    simp
    rw [div_pos_iff]
    left
    simp
  have C : (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) ≠ ⊤ := by
    simp
  conv =>
    left
    right
    left
    rw [mul_comm]
  rw [ENNReal.inv_mul_cancel B C]
  conv =>
    left
    right
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  rw [ENNReal.inv_mul_cancel B C]
  rw [one_mul]
  rw [pow_one]

@[simp]
theorem DiscreteLaplaceSample_apply (num den : PNat) (x : ℤ) (gam : t = (num : ℝ) / (den : ℝ)) :
  (DiscreteLaplaceSample num den) x = ENNReal.ofReal (((exp (1/t) - 1) / (exp (1/t) + 1)) * (exp (- (abs x / t)))) := by
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SubPMF.bind_apply,
     decide_eq_true_eq, ENNReal.summable,
    Bool.forall_bool, and_self, tsum_prod', tsum_bool, IsEmpty.forall_iff, ↓reduceIte, tsum_zero,
    forall_true_left, ite_not, zero_add, ite_mul, zero_mul, SubPMF.pure_apply, mul_ite, mul_one,
    mul_zero, one_div, Int.cast_abs, Complex.int_cast_abs]

  have OR : x ≥ 0 ∨ x < 0 := by exact le_or_gt 0 x
  cases OR
  . rename_i h1
    lift x to ℕ using h1
    conv =>
      left
      left
      rw [ENNReal.tsum_eq_add_tsum_ite x]

    simp only [DiscreteLaplaceSampleLoop_normalizes, prob_until_apply_norm]
    simp (config := { contextual := true }) [ite_simpl_4]
    conv =>
      right
      right
      left
      rw [division_def]
    subst gam
    simp
    rw [avoid_double_counting]
    rw [ENNReal.mul_inv]
    . simp
      sorry
    . left
      simp
    . left
      simp
  . rename_i h1
    have A : ∃ n : ℕ, - n = x := by
      cases x
      . contradiction
      . rename_i a
        exists (a + 1)
    cases A
    rename_i n h2
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite n]
    sorry
