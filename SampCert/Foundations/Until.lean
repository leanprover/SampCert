/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.While
import Mathlib.Probability.ConditionalProbability

noncomputable section

open SubPMF ProbabilityTheory Nat ENNReal BigOperators Finset

variable {T : Type} [MeasurableSpace T]

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

-- def MyP (cond : T → Bool) (body : RandomM T) (x : T) (comp : RandomM T) : Prop :=
--   comp x = (body x) / (body.toMeasure {x : T | cond x})

-- theorem prob_until_prop_aux (body : RandomM T) (cond : T → Bool) (a : T) :
--   MyP  (λ v : T => ¬ cond v) body a (prob_while (λ v : T => ¬ cond v) (λ _ : T => body) sorry a) := by
--   have H := prob_while_rule (MyP (λ v : T => ¬ cond v) body a) (λ v : T => ¬ cond v) (λ _ : T => body) sorry (Pmf.bind body (fun v => Pmf.pure v))
--   apply H
--   sorry
  -- . clear H
  --   unfold MyP
  --   simp
  --   sorry
  -- . clear H
  --   unfold MyP
  --   simp
  --   intros inner a2 H

-- theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) (x : T) :
--   prob_until (body : RandomM T) (cond : T → Bool) h x =
--   body.toMeasure[{ y | y = x }|{y | cond y}] := sorry

-- attribute [simp] cond_apply toMeasure_apply

theorem prob_until_support_1 (body : RandomM T) (cond : T → Bool) (x : T) :
  body x = 0 → prob_until body cond x = 0 := sorry

theorem prob_until_support_2 (body : RandomM T) (cond : T → Bool) (x : T) :
  ¬ cond x → prob_until body cond x = 0 := sorry

-- Since the initializer is the body, the only thing that changes
-- compared to WhileExample is that we the sequence starts earlier

-- One possibility to deal with initializatio is to pick a value for which
-- we know that the condition is false

-- case analysis?
-- If the condition is is false, then
-- Else normal while loop?
-- One theorem of the form: init : T, ¬ cond init = false

def u₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) : ℝ :=
  (body x).toReal * (1 - ∑' (x : T), if cond x then body x else 0).toReal^n

def s₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) := ∑ m in range n, u₁ cond body x (m + 1)

theorem s₁_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (s₁ cond body x) Filter.atTop (nhds ((body x).toReal / (∑' (x : T), if cond x then body x else 0).toReal)) := by
  refine HasSum.tendsto_sum_nat ?h
  rw [hasSum_nat_add_iff 1]
  simp only [range_one, sum_singleton, u₁, _root_.pow_zero, mul_one]



theorem foobar (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n init x) Filter.atTop (nhds ((if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0))) := by
  apply Filter.Tendsto.apply


theorem the_eq (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) (scond : n > 0) (init : T) (h : ¬ cond init) :
  ∑' a : T, body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n a x
  =
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (n + 1) init x := by
  revert init
  induction n
  . contradiction
  . rename_i n IH
    intro init COND
    unfold prob_while_cut
    unfold WhileFunctional
    simp at COND
    simp [COND]
    congr
    ext a
    split
    . rename_i COND'
      simp
      have OR : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
      cases OR
      . rename_i N_0
        subst N_0
        clear IH scond
        simp [prob_while_cut, WhileFunctional, COND']
      . rename_i N_N0
        simp at IH
        have IH' := IH N_N0 a COND'
        clear IH
        simp [IH']
    . rename_i COND'
      unfold prob_while_cut
      unfold WhileFunctional
      simp
      simp [COND']

theorem tendsto1 (body : RandomM T) (cond : T → Bool) (x : T) (v : ENNReal) :
  Filter.Tendsto (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (n + 1) init x) Filter.atTop (nhds v)
  ↔
  Filter.Tendsto (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n init x) Filter.atTop (nhds v) := by
  apply (@Filter.tendsto_add_atTop_iff_nat ENNReal (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n init x) (nhds v)) 1

theorem tendsto2 (body : RandomM T) (cond : T → Bool) (x : T) (v : ENNReal) :
  Filter.Tendsto (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (n + 1) init x) Filter.atTop (nhds v)
  ↔
  Filter.Tendsto (λ n => ∑' a : T, body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n a x) Filter.atTop (nhds v) := by
  apply Filter.tendsto_congr
  intro i
  rw [the_eq]
  sorry
  sorry -- need to take close look, condition not true at the beginnig and loop condition

-- theorem while_apply_2 [Fintype T] (cond : T → Bool) (body : RandomM T) (x : T) (v : ENNReal) :
--   Filter.Tendsto (fun i => (Finset.sum Finset.univ fun a => (λ _ => body) a * prob_while_cut cond (λ _ => body) i a) x) Filter.atTop (nhds v) →
--   SubPMF.bind body (λ a => prob_while cond (λ _ => body) a) x = v := by
--   intro H
--   simp [prob_while]
--   rw [tsum_fintype]
--   conv =>
--     left
--     right
--     intro b
--     rw [ENNReal.mul_iSup]
--   rw [ENNReal.finset_sum_iSup_nat]
--   apply iSup_eq_of_tendsto
--   . sorry
--   . simp at H
--     sorry -- type class mismatch
--   sorry

@[simp]
theorem prob_until_apply [Fintype T] (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while]
  rw [tsum_fintype]
  conv =>
    left
    right
    intro b
    rw [ENNReal.mul_iSup]
  rw [ENNReal.finset_sum_iSup_nat]
  apply iSup_eq_of_tendsto
  . sorry
  . sorry
  . intro a
    apply Monotone.const_mul'
    apply prob_while_cut_monotonic

@[simp]
theorem prob_until_apply_2 (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while]
  sorry
