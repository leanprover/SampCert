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

theorem rw1_old (n : PNat) :
   (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : ENNReal)
   = (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : NNReal)  := by
  simp only [ne_eq, _root_.mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
    log_eq_zero_iff, reduceLE, or_false, not_lt, false_and, cast_eq_zero, PNat.ne_zero, or_self,
    not_false_eq_true, ENNReal.coe_div, ENNReal.coe_inv, ENNReal.coe_pow, coe_ofNat,
    ENNReal.coe_mul, coe_nat]

theorem rw1 (n : PNat) :
   ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)⁻¹ : ENNReal)
   = ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)⁻¹ : NNReal) := by
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

theorem tsum_comp (n : PNat) :
  (∑' (x : ↑{i : ℕ | decide (↑n ≤ i) = true}ᶜ), (fun i => UniformPowerOfTwoSample (2 * n) i) ↑x)
    = ∑' (i : ↑{i : ℕ| decide (↑n ≤ i) = false}), UniformPowerOfTwoSample (2 * n) ↑i := by
  apply tsum_congr_set_coe
  simp
  ext x
  simp

-- This should be proved more generally
theorem UniformPowerOfTwoSample_autopilot (n : PNat) :
  (1 - ∑' (i : ℕ), if ↑n ≤ i then UniformPowerOfTwoSample (2 * n) i else 0)
    = ∑' (i : ℕ), if i < ↑n then UniformPowerOfTwoSample (2 * n) i else 0 := by
  have X : (∑' (i : ℕ), if decide (↑n ≤ i) = true then UniformPowerOfTwoSample (2 * n) i else 0) +
    (∑' (i : ℕ), if decide (↑n ≤ i) = false then UniformPowerOfTwoSample (2 * n) i else 0) = 1 := by
    have A := UniformPowerOfTwoSample_normalizes (2 * n)
    have B := @tsum_add_tsum_compl ENNReal ℕ _ _ (fun i => UniformPowerOfTwoSample (2 * n) i) _ _ { i : ℕ | decide (↑n ≤ i) = true} ENNReal.summable ENNReal.summable
    rw [A] at B
    clear A
    have C := @tsum_split_coe_right _ (fun i => ↑n ≤ i) (fun i => UniformPowerOfTwoSample (2 * n) i)
    rw [C] at B
    clear C
    have D := @tsum_split_coe_left _ (fun i => ↑n ≤ i) (fun i => UniformPowerOfTwoSample (2 * n) i)
    rw [tsum_comp n] at B
    rw [D] at B
    clear D
    trivial
  apply ENNReal.sub_eq_of_eq_add_rev
  . have Y := tsum_split_less (fun i => ↑n ≤ i) (fun i => UniformPowerOfTwoSample (2 * n) i)
    rw [UniformPowerOfTwoSample_normalizes (2 * n)] at Y
    simp at Y
    clear X
    by_contra
    rename_i h
    rw [h] at Y
    contradiction
  . simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le, one_div] at X
    rw [X]

@[simp]
theorem UniformSample_apply (n : PNat) (x : Nat) (support : x < n) :
  UniformSample n x = 1 / n := by
  unfold UniformSample
  simp only [Bind.bind, Pure.pure, SubPMF.bind_pure, prob_until_apply, decide_eq_true_eq, rw_ite,
    one_div, ite_mul, zero_mul, SubPMF.pure_apply]
  rw [tsum_split_coe_left]
  simp
  rw [UniformPowerOfTwoSample_autopilot]
  split
  . conv =>
      left
      right
      right
      right
      intro i
      rw [rw_ite]
    simp
    rw [rw1 n]
    rw [rw2 n]
    rw [mul_inv]
    simp
  . contradiction

@[simp]
theorem UniformSample_apply_out (n : PNat) (x : Nat) (support : x ≥ n) :
  UniformSample n x = 0 := by
  simp [UniformSample]
  intro i h
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

theorem UniformSample_support_Sum' (n : PNat) :
  (Finset.sum (range n) fun i => UniformSample n i) = 1 := by
  rw [UniformSample_support_Sum n n le.refl]
  apply ENNReal.div_self
  . simp
  . simp

@[simp]
theorem UniformSample_normalizes (n : PNat) :
  ∑' a : ℕ, UniformSample n a = 1 := by
  rw [← @sum_add_tsum_nat_add' _ _ _ _ _ _ n]
  . simp [UniformSample_support_Sum']
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

theorem uniformSample_apply' (n : PNat) (x : Nat) :
  (UniformSample n) x = if x < n then (1 : ENNReal) / n else 0 := by
  split
  . rename_i h
    simp [h]
  . rename_i h
    apply UniformSample_apply_out
    exact Nat.not_lt.mp h
