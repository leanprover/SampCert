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

@[simp]
theorem sum_simple (bound : ℕ) (k : ENNReal) :
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
  simp [C] ; clear A C
  rw [← @Finset.sum_filter]
  have D : Finset.filter (fun x => x < bound) (Finset.range bound) = (Finset.range bound) := by
    apply Finset.filter_true_of_mem
    intro x H
    exact List.mem_range.mp H
  simp [D]
  exact cast_comm bound k
