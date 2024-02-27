/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.While
import Mathlib.Probability.ConditionalProbability

noncomputable section

open Classical SubPMF ProbabilityTheory Nat ENNReal BigOperators Finset

variable {T : Type} [MeasurableSpace T]

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

def u₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) : ℝ :=
  (body x).toReal * (1 - ∑' (x : T), if cond x then body x else 0).toReal^n

def u₂ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) : ENNReal :=
  body x * (1 - ∑' (x : T), if cond x then body x else 0)^n

def s₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) := ∑ m in range n, u₁ cond body x m

def s₂ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) := ∑ m in range n, u₂ cond body x m

theorem at0 (cond : T → Bool) (body : RandomM T) (x : T) :
  s₂ cond body x 0 = 0 := by
  simp [s₂,u₂]

theorem at0' (cond : T → Bool) (body : RandomM T) (x : T) (a : T) :
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 0 a x = 0 := by
  simp [prob_while_cut]

theorem at1 (cond : T → Bool) (body : RandomM T) (x : T) :
  s₂ cond body x 1 = body x := by
  simp [s₂,u₂]

theorem at1'₁ (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : cond a):
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 1 a x = SubPMF.pure a x := by
  simp [prob_while_cut, WhileFunctional, h]

theorem at1'₂ (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : ¬ cond a):
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 1 a x = 0 := by
  simp [prob_while_cut, WhileFunctional, h]

theorem at2 (cond : T → Bool) (body : RandomM T) (x : T) :
  s₂ cond body x 2 = body x + body x * (1 - ∑' (x : T), if cond x then body x else 0) := by
  simp [s₂,u₂]
  rw [sum_range]
  rw [Fin.sum_univ_two]
  simp

theorem at2'₁ (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : cond a) :
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 2 a x = SubPMF.pure a x := by
  simp [prob_while_cut, WhileFunctional, h]

theorem helper1 (cond : T → Bool) (body : RandomM T) (x : T) :
  ∑' (a : T), body a * ite (cond a = false) (fun b => 0) (fun a' => if a' = a then 1 else 0) x = body x := by
  sorry

theorem at2'₂ (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : ¬ cond a) :
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 2 a x = body x := by
  simp [prob_while_cut, WhileFunctional]
  simp at h
  simp [h]
  unfold SubPMF.bind
  unfold SubPMF.pure
  simp [helper1]

theorem at3 (cond : T → Bool) (body : RandomM T) (x : T) :
  s₂ cond body x 3 = body x + body x * (1 - ∑' (x : T), if cond x then body x else 0) + body x * (1 - ∑' (x : T), if cond x = true then body x else 0) ^ 2 := by
  simp [s₂,u₂]
  rw [sum_range]
  rw [Fin.sum_univ_three]
  simp

theorem at3'₁ (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : cond a):
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 3 a x = SubPMF.pure a x := by
  simp [prob_while_cut, WhileFunctional, h]

theorem helper2 (cond : T → Bool) (body : RandomM T) (x : T) :
  ∑' (a : T), body a * ite (cond a = false) (fun b => body b) (fun a' => if a' = a then 1 else 0) x =
  body x + body x * (1 - ∑' (x : T), if cond x = true then body x else 0) := by
  sorry

theorem at3'₂ (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : ¬ cond a):
  prob_while_cut (fun v => decide (cond v = false)) (fun x => body) 3 a x = body x + body x * (1 - ∑' (x : T), if cond x then body x else 0) := by
  simp [prob_while_cut, WhileFunctional, h]
  unfold SubPMF.bind
  unfold SubPMF.pure
  simp [helper1,helper2]


theorem s₁_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (fun x_1 => s₁ cond body x (x_1 + 1)) Filter.atTop
  (nhds (ENNReal.toReal ((if cond x = true then body x else 0) / ∑' (x : T), if cond x = true then body x else 0))) := by
  sorry

theorem s₂_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (fun x_1 => s₂ cond body x x_1) Filter.atTop
  (nhds ((if cond x = true then body x else 0) / ∑' (x : T), if cond x = true then body x else 0)) := by
  sorry

theorem the_eq_1 (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (n : ℕ) :
  (prob_while_cut (fun v => decide (cond v = false)) (fun x => body) (n + 2) a x).toReal
  =
  s₁ cond body x (n+1) := by
  sorry

theorem the_eq_2 (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (n : ℕ) :
  (prob_while_cut (fun v => decide (cond v = false)) (fun x => body) (n + 1) a x)
  =
  s₂ cond body x n := by
  -- case analysis on whether the condition is true or not?
  sorry


theorem pwc_convergence (body : RandomM T) (cond : T → Bool) (x : T) (a : T) :
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  apply iSup_eq_of_tendsto
  . simp [prob_while_cut_monotonic]
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
    --refine (tendsto_toReal_iff ?_ ?_).mp ?_
    -- . sorry -- no top sequence
    -- . sorry -- no top limit
    . rw [Filter.tendsto_congr (the_eq_2 cond body x a)]
      simp [s₂_convergence]

@[simp]
theorem prob_until_apply (body : PMF T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while, pwc_convergence, ENNReal.tsum_mul_right]

@[simp]
theorem prob_until_apply_2 (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  sorry
