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

theorem tsum_simpl_ite_left (cond : ℕ → Bool) (f g : ℕ → ENNReal) :
  (∑' (x : { i : ℕ | cond i}), if cond x then f x else g x)
    = (∑' (x : { i : ℕ | cond i}), f x) := by
  apply tsum_congr
  intro b
  split
  . simp
  . rename_i h
    cases b
    rename_i b P
    simp at *
    have A : cond b = true := by exact P
    simp [A] at h

theorem tsum_simpl_ite_right (cond : ℕ → Bool) (f g : ℕ → ENNReal) :
  (∑' (x : { i : ℕ | ¬ cond i}), if cond x then f x else g x)
    = ((∑' (x : { i : ℕ | ¬ cond i}), g x)) := by
  apply tsum_congr
  intro b
  split
  . rename_i h
    cases b
    rename_i b P
    simp at *
    have A : ¬ cond b = true := by exact P
    simp [A] at h
  . simp

theorem tsum_split_ite (cond : ℕ → Bool) (f g : ℕ → ENNReal) :
  (∑' (i : ℕ), if cond i then f i else g i)
    = (∑' (i : { i : ℕ | cond i}), f i) + (∑' (i : { i : ℕ | ¬ cond i}), g i) := by
  have B := @tsum_add_tsum_compl ENNReal ℕ _ _ (fun i => if cond i then f i else g i) _ _ { i : ℕ | cond i} ENNReal.summable ENNReal.summable
  rw [← B]
  clear B
  rw [tsum_simpl_ite_left]
  have C : { i : ℕ | ¬ cond i} = { i : ℕ | cond i}ᶜ := by exact rfl
  rw [← C]
  rw [tsum_simpl_ite_right]

theorem tsum_simpl_ite_left' (cond : ℕ → Bool) (f g : ℕ → ENNReal) :
  (∑' (x : { i : ℕ | cond i}), if cond x = false then f x else g x)
    = (∑' (x : { i : ℕ | cond i}), g x) := by
  apply tsum_congr
  intro b
  split
  . rename_i h
    cases b
    rename_i b P
    simp at *
    have A : cond b = true := by exact P
    simp [A] at h
  . simp

theorem tsum_simpl_ite_right' (cond : ℕ → Bool) (f g : ℕ → ENNReal) :
  (∑' (x : { i : ℕ | cond i = false}), if cond x = false then f x else g x)
    = ((∑' (x : { i : ℕ | cond i = false}), f x)) := by
  apply tsum_congr
  intro b
  split
  . simp
  . rename_i h
    cases b
    rename_i b P
    simp at *
    have A : cond b = false := by exact P
    simp [A] at h

theorem tsum_split_ite' (cond : ℕ → Bool) (f g : ℕ → ENNReal) :
  (∑' (i : ℕ), if cond i = false then f i else g i)
    = (∑' (i : { i : ℕ | cond i = false}), f i) + (∑' (i : { i : ℕ | cond i = true}), g i) := by
  have B := @tsum_add_tsum_compl ENNReal ℕ _ _ (fun i => if cond i = false then f i else g i) _ _ { i : ℕ | cond i = false} ENNReal.summable ENNReal.summable
  have A : { i : ℕ | cond i = false}ᶜ = { i : ℕ | cond i = true } := by sorry
  rw [A] at B
  rw [← B]
  clear B
  rw [tsum_simpl_ite_left']
  rw [tsum_simpl_ite_right']

theorem tsum_split_coe_right (cond : ℕ → Bool) (f : ℕ → ENNReal) :
  (∑' (i : { i : ℕ | cond i = true}), f i)
    = (∑' (i : ℕ), if cond i = true then f i else 0) := by
  rw [tsum_split_ite]
  simp

theorem tsum_split_coe_left (cond : ℕ → Bool) (f : ℕ → ENNReal) :
  (∑' (i : { i : ℕ | cond i = false}), f i)
    = (∑' (i : ℕ), if cond i = false then f i else 0) := by
  rw [tsum_split_ite']
  simp
