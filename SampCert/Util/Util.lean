/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Function Nat Set BigOperators Finset

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

theorem tsum_simpl_ite_left (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | cond i}), if cond x then f x else g x)
    = (∑' (x : { i : T | cond i}), f x) := by
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

theorem tsum_simpl_ite_right (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | ¬ cond i}), if cond x then f x else g x)
    = ((∑' (x : { i : T | ¬ cond i}), g x)) := by
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

theorem tsum_split_ite (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (i : T), if cond i then f i else g i)
    = (∑' (i : { i : T | cond i}), f i) + (∑' (i : { i : T | ¬ cond i}), g i) := by
  have B := @tsum_add_tsum_compl ENNReal T _ _ (fun i => if cond i then f i else g i) _ _ { i : T | cond i} ENNReal.summable ENNReal.summable
  rw [← B]
  clear B
  rw [tsum_simpl_ite_left]
  have C : { i : T | ¬ cond i} = { i : T | cond i}ᶜ := by exact rfl
  rw [← C]
  rw [tsum_simpl_ite_right]

theorem tsum_simpl_ite_left' (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | cond i}), if cond x = false then f x else g x)
    = (∑' (x : { i : T | cond i}), g x) := by
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

theorem tsum_simpl_ite_right' (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | cond i = false}), if cond x = false then f x else g x)
    = ((∑' (x : { i : T | cond i = false}), f x)) := by
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

theorem tsum_split_ite' (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (i : T), if cond i = false then f i else g i)
    = (∑' (i : { i : T | cond i = false}), f i) + (∑' (i : { i : T | cond i = true}), g i) := by
  have B := @tsum_add_tsum_compl ENNReal T _ _ (fun i => if cond i = false then f i else g i) _ _ { i : T | cond i = false} ENNReal.summable ENNReal.summable
  have A : { i : T | cond i = false}ᶜ = { i : T | cond i = true } := by
    ext x
    simp
  rw [A] at B
  rw [← B]
  clear B
  rw [tsum_simpl_ite_left']
  rw [tsum_simpl_ite_right']

theorem tsum_split_coe_right (cond : T → Bool) (f : T → ENNReal) :
  (∑' (i : { i : T | cond i = true}), f i)
    = (∑' (i : T), if cond i = true then f i else 0) := by
  rw [tsum_split_ite]
  simp

theorem tsum_split_coe_left (cond : T → Bool) (f : T → ENNReal) :
  (∑' (i : { i : T | cond i = false}), f i)
    = (∑' (i : T), if cond i = false then f i else 0) := by
  rw [tsum_split_ite']
  simp

theorem tsum_split_less (cond : ℕ → Bool) (f : ℕ → ENNReal) :
  (∑' i : ℕ, if cond i then f i else 0) ≤ ∑' i : ℕ, f i := by
  have A := @tsum_add_tsum_compl ENNReal ℕ _ _ f _ _ { i : ℕ | cond i} ENNReal.summable ENNReal.summable
  rw [← A]
  rw [tsum_split_coe_right]
  simp

theorem tsum_shift_1 (f : ℕ → ENNReal) :
  (∑' n : ℕ, if n = 0 then 0 else f (n-1)) =
    ∑' n : ℕ, f n := by
  rw [ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_eq_iSup_nat]
  have A : Monotone (fun i => ∑ a in Finset.range i, if a = 0 then 0 else f (a - 1)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [sum_range_succ]
    simp
  rw [← Monotone.iSup_nat_add A 1]
  rw [iSup_congr]
  intro i
  induction i
  . simp
  . rename_i i IH
    rw [sum_range_succ]
    simp
    conv =>
      right
      rw [sum_range_succ]
    rw [← IH]

theorem tsum_shift'_1 (f : ℕ → ENNReal) :
  (∑' n : ℕ, if n = 0 then 0 else f n) =
    ∑' n : ℕ, f (n + 1) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_eq_iSup_nat]
  have A : Monotone fun i => ∑ a in Finset.range i, if a = 0 then 0 else f a := by
    apply monotone_nat_of_le_succ
    intro n
    rw [sum_range_succ]
    simp
  rw [← Monotone.iSup_nat_add A 1]
  rw [iSup_congr]
  intro i
  induction i
  . simp
  . rename_i i IH
    rw [sum_range_succ]
    simp
    conv =>
      right
      rw [sum_range_succ]
    rw [← IH]

theorem tsum_shift'_2 (f : ℕ → ENNReal) :
  (∑' n : ℕ, if n = 0 then 0 else if n = 1 then 0 else f n) =
    ∑' n : ℕ, f (n + 2) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_eq_iSup_nat]
  have A : Monotone fun i => ∑ a in Finset.range i, if a = 0 then 0 else if a = 1 then 0 else f a := by
    apply monotone_nat_of_le_succ
    intro n
    rw [sum_range_succ]
    simp
  rw [← Monotone.iSup_nat_add A 2]
  rw [iSup_congr]
  intro i
  induction i
  . simp
    intro x h1 h2 h3
    cases x
    . contradiction
    . rename_i x
      . cases x
        . contradiction
        . rename_i x
          contradiction
  . rename_i i IH
    rw [sum_range_succ]
    simp
    conv =>
      right
      rw [sum_range_succ]
    rw [← IH]
