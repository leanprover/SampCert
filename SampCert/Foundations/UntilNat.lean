/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.While
import Mathlib.Probability.ConditionalProbability
import SampCert.Foundations.Util

noncomputable section

open Classical SubPMF ProbabilityTheory Nat ENNReal BigOperators Finset

noncomputable def prob_until (body : RandomM ℕ) (cond : ℕ → Bool) : RandomM ℕ := do
  let v ← body
  prob_while (λ v : ℕ => ¬ cond v) (λ _ : ℕ => body) v

@[simp]
theorem until_zero (st : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 0 st x = 0 := by
  simp [prob_while_cut]

@[simp]
theorem repeat_apply_unsat (body : RandomM ℕ) (cond : ℕ → Bool) (fuel i x : ℕ) (h : ¬ cond x) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel i x = 0 := by
  revert i
  induction fuel
  . simp only [zero_eq, until_zero, forall_const]
  . rename_i fuel IH
    intro j
    simp [prob_while_cut, WhileFunctional, ite_apply]
    split
    . simp [IH]
    . rename_i h'
      split
      . rename_i h'
        subst h'
        simp at h'
        simp [h'] at h
      . simp

@[simp]
theorem prob_until_apply_unsat (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : ¬ cond x) :
  prob_until (body : RandomM ℕ) (cond : ℕ → Bool) x = 0 := by
  simp only [prob_until, Bind.bind, Bool.not_eq_true, bind_apply, prob_while]
  simp only [ENNReal.tsum_eq_zero]
  simp only [_root_.mul_eq_zero]
  simp only [iSup_eq_zero]
  intro i ; right ; intro j
  simp [repeat_apply_unsat, h]

def u₂ (cond : ℕ → Bool) (body : RandomM ℕ) (n : ℕ) (x : ℕ) : ENNReal :=
  body x * (1 - ∑' (x : ℕ), if cond x then body x else 0)^n

def s₂ (cond : ℕ → Bool) (body : RandomM ℕ) (n : ℕ) (x : ℕ)  := ∑ m in range n, u₂ cond body m x

@[simp]
theorem s₂_zero (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) :
  s₂ cond body 0 x = 0 := by
  simp [s₂]

theorem s₂_succ (cond : ℕ → Bool) (body : RandomM ℕ) (n : ℕ) (x : ℕ) :
  s₂ cond body (succ fuel) x = s₂ cond body fuel x + u₂ cond body fuel x := by
  simp [s₂, sum_range_succ]

example (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) (s : ∑' (a : ℕ), body a = 1) :
  ∑' (i : ℕ), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 0 i x
    = 0 := by
  simp

theorem if_simpl (body : RandomM ℕ) (cond : ℕ → Bool) (x_1 x : ℕ) :
  @ite ℝ≥0∞ (x_1 = x) (propDecidable (x_1 = x)) 0 (@ite ℝ≥0∞ (cond x_1 = true) (instDecidableEqBool (cond x_1) true) (body x_1 * @ite ℝ≥0∞ (x = x_1) (propDecidable (x = x_1)) 1 0) 0) = 0 := by
  split
  . simp
  . split
    . split
      . rename_i h1 h2 h3
        simp at *
        subst h3
        contradiction
      . simp
    . simp

example (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) (s : ∑' (a : ℕ), body a = 1) :
  ∑' (i : ℕ), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 1 i x
    = body x := by
  simp only [prob_while_cut, WhileFunctional, decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply,
    bind_apply, pure_apply, mul_ite]
  rw [tsum_split_ite']
  have FOO := tsum_split_coe_right cond (fun i => body ↑i * @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) 1 0)
  rw [FOO]
  clear FOO
  conv =>
    left
    right
    rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp only [h, zero_apply, mul_zero, tsum_zero, ↓reduceIte, mul_one,
    zero_add]
  conv =>
    left
    right
    right
    intro y
    rw [if_simpl]
  simp

example (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) (s : ∑' (a : ℕ), body a = 1) :
  ∑' (i : ℕ), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 2 i x
    = 1 := by
  simp [prob_while_cut, WhileFunctional, ite_apply]
  rw [tsum_split_ite']
  rw [ENNReal.tsum_mul_right]
  rw [tsum_split_ite']
  simp only [tsum_zero, zero_add]
  have FOO := tsum_split_coe_right cond (fun i => body ↑i * @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) 1 0)
  rw [FOO]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp only [h, ↓reduceIte, zero_add]



@[simp]
theorem repeat_apply_sat (body : RandomM ℕ) (cond : ℕ → Bool) (fuel i x : ℕ) (h : cond x) (s : ∑' (a : ℕ), body a = 1) :
  (prob_while_cut (fun v => decide (cond v = false)) (fun x => body) fuel i x)
    = s₂ cond body fuel x := by
  revert i
  induction fuel
  . simp
  . rename_i fuel IH
    intro i
    simp [prob_while_cut, WhileFunctional, ite_apply]
    split
    . rename_i h'
      conv =>
        left
        right
        intro a
        rw [IH a]
      simp [ENNReal.tsum_mul_right, s]
      rw [s₂_succ]
      sorry -- Interesting: this is obvioulsy false, I am missing something, the other branch?
    . sorry -- not right

theorem repeat_move (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (b : ℕ) (h : ¬ cond b) (i : ℕ) :
  (∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)
  =
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (i + 1) b x := by
  simp [prob_while_cut, WhileFunctional, h]

theorem split (cond : ℕ → Bool) (body : RandomM ℕ) (fuel x : ℕ) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ fuel) a x =
  if cond a then if a = x then 1 else 0
  else ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel a x := by
  split
  . rename_i h
    simp [prob_while_cut, WhileFunctional, ite_apply, h]
    split
    . rename_i h'
      simp [h']
    . rename_i h'
      . split
        . rename_i h''
          simp [h''] at h'
        . simp
  . rename_i h
    simp [prob_while_cut, WhileFunctional, ite_apply, h]



theorem repeat_sup (body : RandomM ℕ) (cond : ℕ → Bool) (x a : ℕ) (h : cond x) :
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x
    = body x / ∑' (x : ℕ), if cond x = true then body x else 0 := by
  apply iSup_eq_of_tendsto
  . simp [prob_while_cut_monotonic]
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
    sorry

@[simp]
theorem prob_until_apply_sat (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) (s : ∑' (a : ℕ), body a = 1) :
  prob_until (body : RandomM ℕ) (cond : ℕ → Bool) x = body x / (∑' (x : ℕ), if cond x then body x else 0) := by
  simp only [prob_until, Bind.bind, Bool.not_eq_true, bind_apply, prob_while]
  conv =>
    left
    right
    intro a
    right
    simp [repeat_sup, h]
  simp [ENNReal.tsum_mul_right, s]







-------

@[simp]
theorem until_sat_unsat (fuel st₁ st₂ : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (h1 : cond st₁) (h2 : ¬ cond st₂) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ fuel) st₁ st₂ = 0 := by
  simp [prob_while_cut, WhileFunctional, h1]
  split
  . rename_i h
    subst h
    rw [← h1] at h2
    contradiction
  . simp

@[simp]
theorem until_sat_sat (fuel st₁ st₂ : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (h1 : cond st₁) (h2 : cond st₂) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ fuel) st₁ st₂ = if st₂ = st₁ then 1 else 0 := by
  simp [prob_while_cut, WhileFunctional, h1]
  split
  . simp
  . simp

@[simp]
theorem until_unsat_unsat (fuel st₁ st₂ : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (h1 : ¬ cond st₁) (h2 : ¬ cond st₂) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ fuel) st₁ st₂ =
    ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) fuel a st₂ := by
  simp [prob_while_cut, WhileFunctional, h1]

@[simp]
theorem until_unsat_sat (fuel st₁ st₂ : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (h1 : ¬ cond st₁) (h2 : cond st₂) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ fuel) st₁ st₂ =
    ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) fuel a st₂ := by
  simp [prob_while_cut, WhileFunctional, h1]

@[simp]
theorem until_succ_true' (fuel st₁ st₂ : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (h1 : ¬ cond st₁) (h2 : cond st₂) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel st₁ st₂ = 0 := by
  revert st₁ st₂
  induction fuel
  . simp only [Bool.not_eq_true, zero_eq, until_zero, implies_true, forall_const]
  . rename_i fuel IH
    intro st₁ st₂ h1 h2
    simp [prob_while_cut, WhileFunctional]
    simp at h1
    simp [h1]
    intro i
    right
    have OR : cond i ∨ ¬ cond i := by exact eq_or_ne (cond i) true
    cases OR
    . sorry -- cond i can't be true, invariant
    . rename_i h3
      simp [IH i st₂ h3 h2]

theorem simpl_1 (fuel : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : ¬ cond x) :
  (if cond a = false then
      body a * ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) fuel a x
    else body a * if x = a then 1 else 0) =
    (body a * ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) fuel a x) := by
  split
  . simp
  . rename_i h'
    split
    . rename_i h''
      subst h''
      simp at h'
      rw [← h'] at h
      contradiction
    . rename_i h''
      sorry -- should not ever be in ¬ cond a

theorem until_succ_false_2 (fuel st : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h1 : ¬ cond st) (h2 : ¬ cond x) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ (succ fuel)) st x =
  ∑' (a : ℕ), body a * ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel a x := by
  simp [prob_while_cut, WhileFunctional, h1, ite_apply]
  sorry

def u₂ (cond : ℕ → Bool) (body : RandomM ℕ) (n : ℕ) (x : ℕ) : ENNReal :=
  body x * (1 - ∑' (x : ℕ), if cond x then body x else 0)^n

def s₂ (cond : ℕ → Bool) (body : RandomM ℕ) (n : ℕ) (x : ℕ)  := ∑ m in range n, u₂ cond body m x

@[simp]
theorem s₂_zero (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) :
  s₂ cond body 0 x = 0 := by
  simp [s₂]

theorem s₂_succ (cond : ℕ → Bool) (body : RandomM ℕ) (n : ℕ) (x : ℕ) :
  s₂ cond body (succ fuel) x = s₂ cond body fuel x + u₂ cond body fuel x := by
  simp [s₂, sum_range_succ]

theorem split (cond : ℕ → Bool) (body : RandomM ℕ) (fuel x : ℕ) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (succ fuel) a x =
  if cond a then if a = x then 1 else 0
  else ∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel a x := by
  split
  . rename_i h
    simp [until_succ_true, h]
  . rename_i h
    simp [until_succ_false, h]

-- Naturals are split between the ones for which the condition is true
-- and the others
theorem the_eq (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) (st : ℕ) (h : ¬ cond st) (fuel : ℕ) :
  (prob_while_cut (fun v => decide (cond v = false)) (fun x => body) (fuel + 1) st x)
  =
  s₂ cond body fuel x := by
  induction fuel
  . sorry
  . rename_i fuel IH
    simp [split, h] at *
    rw [IH]
    clear IH

    rw [s₂_succ]





def u₁ (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) (n : ℕ) : ℝ :=
  (body x).toReal * (1 - ∑' (x : ℕ), if cond x then body x else 0).toReal^n

def s₁ (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) (n : ℕ) := ∑ m in range n, u₁ cond body x m



theorem s₁_convergence (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) :
  Filter.Tendsto (fun x_1 => s₁ cond body x (x_1 + 1)) Filter.atTop
  (nhds (ENNReal.toReal ((if cond x = true then body x else 0) / ∑' (x : ℕ), if cond x = true then body x else 0))) := by
  sorry

theorem s₂_convergence (cond : ℕ → Bool) (body : RandomM ℕ) (x : ℕ) :
  Filter.Tendsto (fun x_1 => s₂ cond body x x_1) Filter.atTop
  (nhds ((if cond x = true then body x else 0) / ∑' (x : ℕ), if cond x = true then body x else 0)) := by
  sorry




theorem pwc_convergence_0 (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (a : ℕ) (h : ¬ cond a) :
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x =
  (if cond x then body x else 0) / (∑' (x : ℕ), if cond x then body x else 0) := by
  apply iSup_eq_of_tendsto
  . simp [prob_while_cut_monotonic]
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
    . rw [Filter.tendsto_congr (the_eq cond body x a h)]
      simp [s₂_convergence]

theorem exists_seq_same_ind (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (b : ℕ) (h : ¬ cond b) (i : ℕ) :
  (∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)
  =
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (i + 1) b x := by
  simp [prob_while_cut, WhileFunctional, h]

@[simp]
theorem exists_seq_same_limit (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (b : ℕ) (h : ¬ cond b) (l : ENNReal) :
  Filter.Tendsto (fun i => (∑' (a : ℕ), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)) Filter.atTop (nhds l)
  ↔
  Filter.Tendsto (fun i => prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i b x) Filter.atTop (nhds l) := by
  conv =>
    right
    rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
  refine Filter.tendsto_congr ?h
  intro x1
  apply exists_seq_same_ind
  trivial

theorem exists_seq_same (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (b : ℕ) (h : ¬ cond b) :
  (∑' (a : ℕ), body a * ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x)
  =
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i b x := by
  refine (iSup_eq_of_tendsto ?hf ?_).symm
  . simp [prob_while_cut_monotonic]
  . rw [← exists_seq_same_limit]
    . sorry
    . trivial

@[simp]
theorem prob_until_apply (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (ex : ∃ b : ℕ, ¬ cond b) :
  prob_until (body : RandomM ℕ) (cond : ℕ → Bool) x =
  (if cond x then body x else 0) / (∑' (x : ℕ), if cond x then body x else 0) := by
  simp [prob_until, prob_while]
  cases ex
  rename_i b h
  rw [exists_seq_same body cond x b h]
  rw [pwc_convergence_0]
  trivial