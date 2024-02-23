/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SampCert.Foundations.Random

open Function Nat

theorem in_subset_satisfies (P : ℕ → Prop) (x : { x // P x }) : P x := by
  cases x
  simp
  trivial

@[simp]
theorem sum_simple (bound : ℕ) (k : ENNReal) :
 (∑' (a : ℕ), if a < bound then k else 0) = k * bound := by
  rw [← tsum_subtype_support]
  unfold support
  simp
  -- show that range is a finite set and tsum_eq_sum
  --rw [tsum_subtype {x | (fun a => if a < bound then k else 0) x ≠ 0} (fun x => if ↑x < bound then k else 0)]
  sorry

-- Relevant
#check Finset.tsum_subtype
#check tsum_dite_left
#check tsum_eq_sum
