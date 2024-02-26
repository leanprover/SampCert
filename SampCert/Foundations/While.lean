/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Random
import SampCert.Foundations.SubPMF
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open SubPMF Nat Classical ENNReal OrderHom PMF

variable {T} [Preorder T]

def WhileFunctional (cond : T → Bool) (body : T → RandomM T) (wh : T → RandomM T) : T → RandomM T :=
  λ a : T =>
  if cond a
    then do
      let v ← body a
      wh v
    else return a

def prob_while_cut (cond : T → Bool) (body : T → RandomM T) (n : Nat) (a : T) : RandomM T :=
  match n with
  | Nat.zero => SubPMF.zero
  | succ n => WhileFunctional cond body (prob_while_cut cond body n) a

theorem prob_while_cut_monotonic (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :
  Monotone (fun n : Nat => prob_while_cut cond body n init x) := by
  apply monotone_nat_of_le_succ
  intro n
  revert init
  induction n
  . intro init
    simp [prob_while_cut]
  . rename_i n IH
    intro init
    simp [prob_while_cut,WhileFunctional]
    split
    . rename_i COND
      unfold SubPMF.bind
      unfold SubPMF.pure
      simp
      apply ENNReal.tsum_le_tsum
      intro a
      apply mul_le_mul_left'
      exact IH a
    . simp

def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  fun x => ⨆ (i : ℕ), (prob_while_cut cond body i init x)

@[simp]
theorem while_apply (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) (v : ENNReal) :
  Filter.Tendsto (fun i => prob_while_cut cond body i init x) Filter.atTop (nhds v) →
  prob_while cond body init x = v := by
  intro H
  unfold prob_while
  apply iSup_eq_of_tendsto
  . apply prob_while_cut_monotonic
  . apply H
