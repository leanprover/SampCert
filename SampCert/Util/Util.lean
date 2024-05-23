/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Util

This file contains a variety of utility lemmas.
-/

open Function Nat Set BigOperators Finset

-- MARKUSDE: Surely this is somwehere else? Is this not the defining property of subtypes?
-- MARKUSDE: (subtle) { _ // _ } represents subtypes, not subsets, right?
theorem in_subset_satisfies (P : ℕ → Prop) (x : { x // P x }) : P x := by
  cases x
  simp
  trivial

-- MARKUSDE: Refactored to pass linter. Check with JBT: What considerations should
-- I make when refactoring? Does anything about extraction change etc?
/--
Simplify a sum over a step function
-/
@[simp]
theorem sum_simple (bound : ℕ) (k : ENNReal) :
 (∑' (a : ℕ), if a < bound then k else 0) = k * bound := by
  have A : Summable fun a => if a + bound < bound then k else 0 := by
    exact ENNReal.summable
  have B := @sum_add_tsum_nat_add' ENNReal _ _ _ _ (fun a => if a < bound then k else 0) bound A
  rw [← B]
  clear B
  rw [(tsum_eq_zero_iff A).mpr]
  · rw [← @Finset.sum_filter]
    rw [Finset.filter_true_of_mem]
    . simp
      rw [mul_comm]
    . intro _
      exact List.mem_range.mp
  · intro x
    simp


-- MARKUSDE: add @[simp]? I'd guess that's how it would be used.
/--
Simplify guarded series when series indices satisfy the guard
-/
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

/--
Simplify guarded series when series indices never satisfy the guard
-/
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

-- MARKUSDE: Is absolute convergence under the hood somewhere here or is there some other trick?
-- MARKUSDE: cond x = (x % 2 = 0), f _ = 1, g _ = -1
/--
Partition series indices based on conditional guard
-/
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

/--
Simplify guarded series based on index type
-/
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

/--
Simplify guarded series based on index type
-/
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

/--
Partition series indices based on negation of conditional guard
-/
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

/--
Add vacuous guard to series based on index type
-/
theorem tsum_split_coe_right (cond : T → Bool) (f : T → ENNReal) :
  (∑' (i : { i : T | cond i = true}), f i)
    = (∑' (i : T), if cond i = true then f i else 0) := by
  rw [tsum_split_ite]
  simp

/--
Add vacuous guard to series based on index type
-/
theorem tsum_split_coe_left (cond : T → Bool) (f : T → ENNReal) :
  (∑' (i : { i : T | cond i = false}), f i)
    = (∑' (i : T), if cond i = false then f i else 0) := by
  rw [tsum_split_ite']
  simp

/--
Bound a (nonnegative) guarded series above by an unguarded one
-/
theorem tsum_split_less (cond : ℕ → Bool) (f : ℕ → ENNReal) :
  (∑' i : ℕ, if cond i then f i else 0) ≤ ∑' i : ℕ, f i := by
  have A := @tsum_add_tsum_compl ENNReal ℕ _ _ f _ _ { i : ℕ | cond i} ENNReal.summable ENNReal.summable
  rw [← A]
  rw [tsum_split_coe_right]
  simp

/--
Remove leading zero from series
-/
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

-- MARKUSDE: Simplify me (in terms of tsum_shift_1)
/--
Remove leading zero from series
-/
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

/--
Remove two leading zeroes from series
-/
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


#lint docBlame
