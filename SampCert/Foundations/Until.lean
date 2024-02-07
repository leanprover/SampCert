/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.While
import Mathlib.Probability.ConditionalProbability

open PMF ProbabilityTheory

variable {T : Type} [MeasurableSpace T]

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body))  : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) sorry v

def MyP (cond : T → Bool) (body : RandomM T) (x : T) (comp : RandomM T) : Prop :=
  comp x = (body x) / (body.toMeasure {x : T | cond x})

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

theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) h x =
  body.toMeasure[{ y | y = x }|{y | cond y}] := sorry

attribute [simp] cond_apply toMeasure_apply

@[simp]
theorem prob_until_apply_2 (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) h x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  rw [prob_until_apply]
  simp
  rw [cond_apply]
  rw [toMeasure_apply]
  rw [@Set.inter_def]
  rw [← @tsum_subtype]
  simp
  rw [@mul_comm]
  rw [@division_def]
  congr
  sorry
  sorry
  sorry
  sorry
  sorry

theorem prob_until_support (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) :
  (prob_until (body : RandomM T) (cond : T → Bool) h).support = {x | cond x} := sorry

theorem prob_until_true (body : RandomM T) (h : terminates (fun _ => true) (λ _ => body)) :
  prob_until body (fun _ => true) h = body := by
  ext x
  rw [prob_until_apply_2]
  simp
