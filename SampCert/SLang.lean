/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log

open Classical Nat ENNReal PMF

noncomputable section

abbrev SLang.{u} (α : Type u) : Type u := α → ℝ≥0∞

namespace PMF

def toSLang (p : PMF α) : SLang α := p.1

@[simp]
theorem toSubPMF_apply (p : PMF α) (x : α) : (toSLang p x) = p x := by
  unfold toSLang
  unfold DFunLike.coe
  unfold instFunLike
  simp

instance : Coe (PMF α) (SLang α) where
  coe a := toSLang a

end PMF

namespace SLang

variable {T U} -- [Preorder T]

def zero : SLang T := λ _ : T => 0

def pure (a : T) : SLang T := fun a' => if a' = a then 1 else 0

def bind (p : SLang T) (f : T → SLang U) : SLang U :=
  fun b => ∑' a, p a * f a b

instance : Monad SLang where
  pure a := pure a
  bind pa pb := pa.bind pb

def UniformPowerOfTwoSample (n : ℕ+) : SLang ℕ :=
  toSLang (PMF.uniformOfFintype (Fin (2 ^ (log 2 n))))
  --((PMF.uniformOfFintype (Fin (2 ^ (log 2 n)))) : PMF ℕ).1

def WhileFunctional (cond : T → Bool) (body : T → SLang T) (wh : T → SLang T) : T → SLang T :=
  λ a : T =>
  if cond a
    then do
      let v ← body a
      wh v
    else return a

def prob_while_cut (cond : T → Bool) (body : T → SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => zero
  | succ n => WhileFunctional cond body (prob_while_cut cond body n) a

def prob_while (cond : T → Bool) (body : T → SLang T) (init : T) : SLang T :=
  fun x => ⨆ (i : ℕ), (prob_while_cut cond body i init x)

def prob_until (body : SLang T) (cond : T → Bool) : SLang T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

end SLang
