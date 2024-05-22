/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Foundations.Monad
import SampCert.Foundations.Auto
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# While

This file proves properties about the ``while`` term of ``SLang``.

-/

noncomputable section

namespace SLang

variable {T} [Preorder T]

-- MARKUSDE: Is it true that ≤ ordering between SLang terms here is pointwise? How would I check?
-- In Rocq, I would Unset Printing Notations-- what about Lean?
/--
The ``while`` program is monotonic (as a pointwise function) in terms of the number of unrollings.
-/
theorem probWhileCut_monotonic (cond : T → Bool) (body : T → SLang T) (init : T) (x : T) :
  Monotone (fun n : Nat => probWhileCut cond body n init x) := by
  apply monotone_nat_of_le_succ
  intro n
  revert init
  induction n
  . intro init
    simp [probWhileCut]
  . rename_i n IH
    intro init
    simp [probWhileCut,whileFunctional]
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

/--
The ``probWhile`` term evaluates to the pointwise limit of the ``probWhileCut`` term
-/
@[simp]
theorem probWhile_apply (cond : T → Bool) (body : T → SLang T) (init : T) (x : T) (v : ENNReal) :
  Filter.Tendsto (fun i => probWhileCut cond body i init x) Filter.atTop (nhds v) →
  probWhile cond body init x = v := by
  intro H
  unfold probWhile
  apply iSup_eq_of_tendsto
  . apply probWhileCut_monotonic
  . apply H

end SLang

#lint docBlame
