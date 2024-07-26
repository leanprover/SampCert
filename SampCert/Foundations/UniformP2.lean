/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log
import SampCert.Util.Util
import SampCert.Foundations.Monad
import SampCert.Foundations.Auto

/-!
# ``probUniformP2`` Properties

This file contains lemmas about ``probUniformP2``, a ``SLang`` sampler for the
uniform distribution on spaces whose size is a power of two.
-/


open Classical Nat PMF

namespace SLang





@[simp]
lemma sum_indicator_finrange_gen (n : Nat) (x : Nat) :
  (x < n → (∑' (i : Fin n), @ite ENNReal (x = ↑i) (propDecidable (x = ↑i)) 1 0) = (1 : ENNReal))
  ∧ (x >= n → (∑' (i : Fin n), @ite ENNReal (x = ↑i) (propDecidable (x = ↑i)) 1 0) = (0 : ENNReal)) := by
  revert x
  induction n
  . intro x
    simp
  . rename_i n IH
    intro x
    constructor
    . intro cond
      have OR : x = n ∨ x < n := by exact Order.lt_succ_iff_eq_or_lt.mp cond
      cases OR
      . rename_i cond'
        have IH' := IH x
        cases IH'
        rename_i left right
        have cond'' : x ≥ n := by exact Nat.le_of_eq (id cond'.symm)
        have right' := right cond''
        rw [tsum_fintype] at *
        rw [Fin.sum_univ_castSucc]
        simp [right']
        simp [cond']
      . rename_i cond'
        have IH' := IH x
        cases IH'
        rename_i left right
        have left' := left cond'
        rw [tsum_fintype] at *
        rw [Fin.sum_univ_castSucc]
        simp [left']
        have neq : x ≠ n := by exact Nat.ne_of_lt cond'
        simp [neq]
    . intro cond
      have succ_gt : x ≥ n := by exact lt_succ.mp (le.step cond)
      have IH' := IH x
      cases IH'
      rename_i left right
      have right' := right succ_gt
      rw [tsum_fintype]
      rw [Fin.sum_univ_castSucc]
      simp
      constructor
      . simp at right'
        intro x'
        apply right' x'
      . have neq : x ≠ n := by exact Nat.ne_of_gt cond
        simp [neq]

/--
Computes the sum of an indicator variable (indicating inside the support of ``Fin n``) over the space ``Fin n``.
-/
theorem sum_indicator_finrange (n : Nat) (x : Nat) (h : x < n) :
  (∑' (i : Fin n), @ite ENNReal (x = ↑i) (propDecidable (x = ↑i)) 1 0) = (1 : ENNReal) := by
  have H := sum_indicator_finrange_gen n x
  cases H
  rename_i left right
  apply left
  trivial

/--
Evaluates the ``probUniformP2`` distribution at a point inside of its support.
-/
@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := by
  simp [UniformPowerOfTwoSample]
  sorry

/--
Evaluates the ``probUniformP2`` distribution at a point outside of its support
-/
@[simp]
theorem UniformPowerOfTwoSample_apply' (n : PNat) (x : Nat) (h : x ≥ 2 ^ (log 2 n)) :
  UniformPowerOfTwoSample n x = 0 := by
  simp [UniformPowerOfTwoSample]
  sorry

lemma if_simpl_up2 (n : PNat) (x x_1: Fin (2 ^ log 2 ↑n)) :
  (@ite ENNReal (x_1 = x) (propDecidable (x_1 = x)) 0 (@ite ENNReal ((@Fin.val (2 ^ log 2 ↑n) x) = (@Fin.val (2 ^ log 2 ↑n) x_1)) (propDecidable ((@Fin.val (2 ^ log 2 ↑n) x) = (@Fin.val (2 ^ log 2 ↑n) x_1))) 1 0)) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      cases x
      rename_i x p
      cases x_1
      rename_i y q
      simp at *
      subst h2
      contradiction
    . simp

/--
The ``SLang`` term ``uniformPowerOfTwo`` is a proper distribution on ``ℕ``.
-/
theorem UniformPowerOfTwoSample_normalizes (n : PNat) :
  ∑' i : ℕ, UniformPowerOfTwoSample n i = 1 := by
  sorry

end SLang
