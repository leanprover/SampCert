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

variable {T}

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
  refine monotone_nat_of_le_succ ?hf
  intro n
  simp [prob_while_cut, WhileFunctional]
  unfold SubPMF.bind
  unfold SubPMF.pure
  simp
  unfold prob_while_cut
  split
  . rename_i n
    simp [SubPMF.zero]
  . rename_i n1 n2
    simp [WhileFunctional]
    split
    . unfold SubPMF.pure
      unfold SubPMF.bind
      simp
      sorry
    . simp [SubPMF.pure]



def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  fun x => ⨆ (i : ℕ), (prob_while_cut cond body i init x)
