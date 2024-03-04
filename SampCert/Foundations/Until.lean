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

theorem s₁_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (fun x_1 => s₁ cond body x (x_1 + 1)) Filter.atTop
  (nhds (ENNReal.toReal ((if cond x = true then body x else 0) / ∑' (x : T), if cond x = true then body x else 0))) := by
  sorry

theorem s₂_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (fun x_1 => s₂ cond body x x_1) Filter.atTop
  (nhds ((if cond x = true then body x else 0) / ∑' (x : T), if cond x = true then body x else 0)) := by
  sorry

theorem split (cond : T → Bool) (body : RandomM T) (x : T) :
  ∑' (a : T),
      body a *
        ite (cond a = false)
          (fun b => ∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) n a b)
          (fun a' => if a' = a then 1 else 0) x
  =
  (∑' (a : { v : T // cond v = false}),
    body a * ∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) n a x)
  +
  (∑' (a : { v : T // cond v = true}), body a * if x = a then 1 else 0) := sorry

theorem ite_simp (cond : T → Bool) (body : RandomM T) (x : T) :
  (∑' (a : { v // cond v = true }), body ↑a * @ite ENNReal (x = ↑a) (propDecidable (x = ↑a)) 1 0) = body x := by sorry

theorem the_eq (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : ¬ cond a) (n : ℕ) :
  (prob_while_cut (fun v => decide (cond v = false)) (fun x => body) (n + 1) a x)
  =
  s₂ cond body x n := by
  induction n
  . simp [prob_while_cut, WhileFunctional, s₂, u₂, h]
  . rename_i n IH
    revert IH
    simp [prob_while_cut, WhileFunctional]
    unfold SubPMF.bind
    unfold SubPMF.pure
    simp [h]
    intro IH
    rw [split]
    rw [IH]
    clear IH
    rw [ENNReal.tsum_mul_right]
    rw [ite_simp]
    simp [s₂]
    rw [sum_range_succ]
    rw [← s₂]
    simp [u₂]
    sorry -- Looks reasonable

theorem pwc_convergence_0 (body : RandomM T) (cond : T → Bool) (x : T) (a : T) (h : ¬ cond a) :
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  apply iSup_eq_of_tendsto
  . simp [prob_while_cut_monotonic]
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
    . rw [Filter.tendsto_congr (the_eq cond body x a h)]
      simp [s₂_convergence]

theorem exists_seq_same_ind (body : RandomM T) (cond : T → Bool) (x : T) (b : T) (h : ¬ cond b) (i : ℕ) :
  (∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)
  =
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (i + 1) b x := by
  simp [prob_while_cut, WhileFunctional, h]

theorem exists_seq_same_limit (body : RandomM T) (cond : T → Bool) (x : T) (b : T) (h : ¬ cond b) (l : ENNReal) :
  Filter.Tendsto (fun i => (∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)) Filter.atTop (nhds l)
  ↔
  Filter.Tendsto (fun i => prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i b x) Filter.atTop (nhds l) := by
  conv =>
    right
    rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
  refine Filter.tendsto_congr ?h
  intro x1
  apply exists_seq_same_ind
  trivial

theorem exists_seq_same (body : RandomM T) (cond : T → Bool) (x : T) (b : T) (h : ¬ cond b) :
  (∑' (a : T), body a * ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x)
  =
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i b x := by
  refine (iSup_eq_of_tendsto ?hf ?_).symm
  . simp [prob_while_cut_monotonic]
  . rw [← exists_seq_same_limit]
    . apply?
    . trivial

@[simp]
theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (x : T) (ex : ∃ b : T, ¬ cond b) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while]
  cases ex
  rename_i b h
  rw [exists_seq_same body cond x b h]
  rw [pwc_convergence_0]
  trivial

@[simp]
theorem prob_until_apply_2 (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  sorry
