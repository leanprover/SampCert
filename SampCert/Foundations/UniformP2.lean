/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Random
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.Nat.Log
import SampCert.Foundations.Util
import SampCert.Foundations.SubPMF

open Classical

open Nat SubPMF PMF Classical
-- Assumption: the Dafny version indeed has this spec

noncomputable def UniformPowerOfTwoSample (n : PNat) : RandomM Nat :=
  toSubPMF (uniformOfFintype (Fin (2 ^ (log 2 n))))

@[simp]
theorem test1 (b x : ℕ) :
  ((if (x = ↑b : Prop) then 1 else 0): ENNReal)
  = if ↑b = x then 1 else 0 := by
  split
  . rename_i h
    subst h
    simp
  . rename_i h
    split
    . rename_i h2
      rw [h2] at h
      contradiction
    . trivial

@[simp]
theorem test (b x : ℕ) :
  (∑' (b : Fin b), if x = ↑b then 1 else 0)
  = ∑' (b : Fin b), if ↑b = x then 1 else 0 := by
  congr
  ext y
  split
  . rename_i h
    subst h
    simp
  . rename_i h
    split
    . rename_i h2
      rw [h2] at h
      contradiction
    . trivial

-- theorem list_finrange (x n : ℕ) (cond : x < n) :
--   List.sum (List.map (fun i => if x = i then 1 else 0) (List.finRange n)) = 1 := by
--   revert x
--   induction n
--   . intro x H
--     contradiction
--   . rename_i n IH
--     intro x H
--     have OR : x < n ∨ x = n := by exact Nat.lt_succ_iff_lt_or_eq.mp H
--     cases OR
--     . rename_i H'
--       have IH' := IH x H'
--       sorry -- fine
--     . rename_i H'
--       subst H'
--       simp
--       rw?

--set_option pp.all true

@[simp]
theorem sum_indicator_finrange_gen (n : Nat) (x : Nat) :
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




@[simp]
theorem sum_indicator_finrange (n : Nat) (x : Nat) (h : x < n) :
  (∑' (i : Fin n), @ite ENNReal (x = ↑i) (propDecidable (x = ↑i)) 1 0) = (1 : ENNReal) := by
  revert x
  induction n
  . intro x cond
    contradiction
  . rename_i n IH
    intro x cond
    have OR : x = n ∨ x < n := by exact Order.lt_succ_iff_eq_or_lt.mp cond
    cases OR
    . rename_i cond'
      -- In this case, the induction hypothesis is not useful
      clear cond IH
      sorry
    . sorry

@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := by
  simp [UniformPowerOfTwoSample]
  rw [ENNReal.tsum_mul_left]
  rw [sum_indicator_finrange (2 ^ (log 2 n)) x]
  . simp
  . trivial
