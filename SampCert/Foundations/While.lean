/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.SLang
import SampCert.Foundations.SubPMF
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

namespace SLang

variable {T} [Preorder T]

theorem prob_while_cut_monotonic (cond : T → Bool) (body : T → SLang T) (init : T) (x : T) :
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
      unfold SLang.bind
      unfold SLang.pure
      simp
      apply ENNReal.tsum_le_tsum
      intro a
      apply mul_le_mul_left'
      exact IH a
    . simp

@[simp]
theorem while_apply (cond : T → Bool) (body : T → SLang T) (init : T) (x : T) (v : ENNReal) :
  Filter.Tendsto (fun i => prob_while_cut cond body i init x) Filter.atTop (nhds v) →
  prob_while cond body init x = v := by
  intro H
  unfold prob_while
  apply iSup_eq_of_tendsto
  . apply prob_while_cut_monotonic
  . apply H

end SLang
