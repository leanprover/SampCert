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

instance wcpo : OmegaCompletePartialOrder (T → SubPMF T) := sorry

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
  | Nat.zero => zero
  | succ n => WhileFunctional cond body (prob_while_cut cond body n) a

theorem prob_while_cut_monotonic (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :
  Monotone (fun n : Nat => prob_while_cut cond body n init x) := sorry

def plop1 (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :=
  tendsto_atTop_iSup (prob_while_cut_monotonic cond body init x)

def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  fun x => ⨆ (i : ℕ), (prob_while_cut cond body i init x)
