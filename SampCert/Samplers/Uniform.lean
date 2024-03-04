/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import Mathlib.Data.ENNReal.Basic

open PMF Classical Finset Nat ENNReal

noncomputable def UniformSample (n : PNat) : RandomM Nat := do
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
  return r

theorem rw1 (n : PNat) :
   (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : ENNReal)
   = (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : NNReal)  := by
  simp only [ne_eq, _root_.mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
    log_eq_zero_iff, reduceLE, or_false, not_lt, false_and, cast_eq_zero, PNat.ne_zero, or_self,
    not_false_eq_true, ENNReal.coe_div, ENNReal.coe_inv, ENNReal.coe_pow, coe_ofNat,
    ENNReal.coe_mul, coe_nat]

theorem rw2 (n : PNat) : ((↑↑n)⁻¹ : ENNReal) = ((↑↑n)⁻¹ : NNReal) := by
  simp only [ne_eq, cast_eq_zero, PNat.ne_zero, not_false_eq_true, ENNReal.coe_inv, coe_nat]

@[simp]
theorem double_large_enough (n : PNat) (x : Nat) (support : x < n) :
  x < 2 ^ (log 2 ↑(2 * n)) := by
  have A : ∀ m : ℕ, m < 2 ^ (log 2 ↑(2 * m)) := by
    intro m
    cases m
    . simp
    . rename_i m
      have H1 := @Nat.lt_pow_succ_log_self 2 le.refl (succ m)
      have H2 := @Nat.log_mul_base 2 (succ m) le.refl (succ_ne_zero m)
      rw [Nat.mul_comm]
      rw [H2]
      exact H1
  exact Nat.lt_trans support (A ↑n)

@[simp]
theorem rw_ite (n : PNat) (x : Nat) :
  (if x < n then (UniformPowerOfTwoSample (2 * n)) x else 0)
  = if x < n then 1 / 2 ^ log 2 ((2 : PNat) * n) else 0 := by
  split
  rw [UniformPowerOfTwoSample_apply]
  simp only [PNat.mul_coe, one_div]
  apply double_large_enough
  trivial
  trivial

@[simp]
theorem UniformSample_apply (n : PNat) (x : Nat) (support : x < n) :
  UniformSample n x = 1 / n := by
  unfold UniformSample
  simp only [Bind.bind, Pure.pure, SubPMF.bind_pure, prob_until_apply_2, decide_eq_true_eq, rw_ite,
   one_div, sum_simple]
  split
  . rw [rw1 n]
    rw [rw2 n]
    have H := div_mul_eq_div_mul_one_div (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹) : NNReal) (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹) : NNReal) (n : NNReal)
    congr
    rw [H]
    simp
  . contradiction

@[simp]
theorem UniformSample_apply_out (n : PNat) (x : Nat) (support : x ≥ n) :
  UniformSample n x = 0 := by
  simp only [UniformSample, Bind.bind, Pure.pure, SubPMF.bind_apply, prob_until_apply_2,
    decide_eq_true_eq, rw_ite, one_div, sum_simple, SubPMF.pure_apply, ENNReal.tsum_eq_zero,
    _root_.mul_eq_zero, ENNReal.div_eq_zero_iff, ite_eq_right_iff, ENNReal.inv_eq_zero,
    pow_eq_top_iff, two_ne_top, ne_eq, log_eq_zero_iff, reduceLE, or_false, not_lt, false_and,
    imp_false]
  intro i
  have OR : ↑n ≤ i ∨ ↑n > i := by exact le_or_lt (↑n) i
  cases OR
  . rename_i h
    simp [h]
  . rename_i h
    have A : x > i := by exact Nat.lt_of_lt_of_le h support
    have B : x ≠ i := by exact Nat.ne_of_gt A
    simp [B]

theorem UniformSample_support_Sum (n : PNat) (m : ℕ) (h : m ≤ n) :
  (Finset.sum (range m) fun i => UniformSample n i) = m / n := by
  induction m
  . simp
  . rename_i m IH
    simp at *
    have A : m ≤ ↑n := by exact lt_succ.mp (le.step h)
    have IH' := IH A
    clear IH
    rw [sum_range_succ]
    simp [IH']
    rw [UniformSample_apply ↑n m h]
    rw [ENNReal.div_add_div_same]

@[simp]
theorem UniformSample_normalizes (n : PNat) :
  ∑' a : ℕ, UniformSample n a = 1 := by
  rw [← @sum_add_tsum_nat_add' _ _ _ _ _ _ n]
  . simp
    rw [UniformSample_support_Sum n n le.refl]
    cases n
    rename_i n p
    simp
    apply ENNReal.div_self
    . simp
      by_contra h
      subst h
      contradiction
    . simp
  . exact ENNReal.summable

theorem UniformSample_HasSum_1  (n : PNat) :
  HasSum (UniformSample n) 1 := by
  have A : Summable (UniformSample n) := by exact ENNReal.summable
  have B := Summable.hasSum A
  rw [UniformSample_normalizes n] at B
  trivial

noncomputable def UniformSample_PMF (n : PNat) : PMF ℕ := ⟨ UniformSample n , UniformSample_HasSum_1 n⟩

theorem UniformSample_apply_ite (a b : ℕ) (c : PNat) (i1 : b ≤ c) :
  (if a < b then (UniformSample c) a else 0) = if a < b then 1 / (c : ENNReal) else 0 := by
  split
  rename_i i2
  rw [UniformSample_apply]
  . exact Nat.lt_of_lt_of_le i2 i1
  . trivial
