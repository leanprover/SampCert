/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SampCert.Foundations.Random

open Function Nat Set

theorem in_subset_satisfies (P : ℕ → Prop) (x : { x // P x }) : P x := by
  cases x
  simp
  trivial

#check tsum_geometric_inv_two_ge
#check sum_add_tsum_nat_add'
#check ite_eq_right_iff

@[simp]
theorem sum_simple (bound : ℕ) (k : ENNReal) (ntop : k ≠ ⊤) :
 (∑' (a : ℕ), if a < bound then k else 0) = k * bound := by
  have A : Summable fun a => if a + bound < bound then k else 0 := by
    exact ENNReal.summable
  have B := @sum_add_tsum_nat_add' ENNReal _ _ _ _ (fun a => if a < bound then k else 0) bound A
  rw [← B]
  clear B
  have C : ∑' (i : ℕ), (fun a => if a < bound then k else 0) (i + bound) = 0 := by
    apply (tsum_eq_zero_iff A).mpr
    intro x
    induction x
    . simp
    . simp
  have D : (Finset.sum (Finset.range bound) fun i => (fun a => if a < bound then k else 0) i) = k * bound := by
    simp
    clear A C
    induction bound
    . simp
    . rename_i n IH
      rw [Finset.sum_range_succ]
      simp
      have E : ∀ t, (Finset.sum (Finset.range n) fun x => if x < n + t then k else 0) = k * ↑n → (Finset.sum (Finset.range n) fun x => if x < n + t + 1 then k else 0) = k * ↑n := by
        clear IH
        induction n
        . simp
        . rename_i n IH
          intro t H
          have F : succ n + t = n + (t + 1) := by
            exact succ_add_eq_add_succ n t
          simp [F] at *
          rw [Finset.sum_range_succ] at H
          simp at H
          have I : (Finset.sum (Finset.range n) fun x => if x < n + (t + 1) then k else 0) = k * ↑n := by
            rw [Mathlib.Tactic.RingNF.add_assoc_rev]
            rw [mul_add_one] at H
            sorry
          have G := IH (t + 1) I
          clear F I H IH
          rw [Finset.sum_range_succ, G]
          have J : n < n + (t + 1) + 1 := by
            rw [lt_succ]
            simp only [le_add_iff_nonneg_right, _root_.zero_le]
          simp [J]
          exact (mul_add_one k ↑n).symm
      have K := E 0 IH
      simp [K]
      clear IH E K
      exact (mul_add_one k ↑n).symm
  simp [C,D]




-- Relevant
#check Finset.tsum_subtype
#check tsum_dite_left
#check tsum_eq_sum
