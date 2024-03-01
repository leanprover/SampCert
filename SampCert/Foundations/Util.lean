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
theorem sum_simple (bound : ℕ) (k : ENNReal) :
 (∑' (a : ℕ), if a < bound then k else 0) = k * bound := by
  have A : Summable fun a => if a + bound < bound then k else 0 := by sorry
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
      sorry -- roundabout but promising!
  simp [C,D]




-- Relevant
#check Finset.tsum_subtype
#check tsum_dite_left
#check tsum_eq_sum
