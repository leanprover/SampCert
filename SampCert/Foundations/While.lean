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

def WhileFunctional2 (cond : T → Bool) (body : T → RandomM T) (wh : RandomM T) : RandomM T := do
  let v ← wh
  if cond v then body v else return v

def WhileFunctionalPMF (cond : T → Bool) (body : T → PMF T) (wh : PMF T) : PMF T := do
  let v ← wh
  if cond v then body v else return v

def prob_while_cut2 (cond : T → Bool) (body : T → RandomM T) (n : Nat) (a : T)  : RandomM T :=
  match n with
  | Nat.zero => SubPMF.pure a -- zero
  | succ n => WhileFunctional2 cond body (prob_while_cut2 cond body n a)

def prob_while_cut_PMF (cond : T → Bool) (body : T → PMF T) (n : Nat) (a : T)  : PMF T :=
  match n with
  | Nat.zero => PMF.pure a -- zero
  | succ n => WhileFunctionalPMF cond body (prob_while_cut_PMF cond body n a)

theorem prob_while_cut_monotonic (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :
  Monotone (fun n : Nat => prob_while_cut cond body n init x) := sorry

theorem prob_while_cut_monotonic2 (cond : T → Bool) (body : T → RandomM T) :
  Monotone (WhileFunctional2 cond body) := sorry

theorem prob_while_cut_monotonic2' (cond : T → Bool) (body : T → RandomM T) :
  Monotone (fun n : Nat => prob_while_cut2 cond body n) := sorry

instance myf (cond : T → Bool) (body : T → RandomM T) : OrderHom ℕ (T → SubPMF T) where
  toFun := prob_while_cut2 cond body
  monotone' := prob_while_cut_monotonic2' cond body

def myf2 (cond : T → Bool) (body : T → RandomM T) : @OmegaCompletePartialOrder.Chain (T → SubPMF T) (@PartialOrder.toPreorder (T → SubPMF T) (@OmegaCompletePartialOrder.toPartialOrder (T → SubPMF T) wcpo))  := sorry

def plop1 (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :=
  tendsto_atTop_iSup (prob_while_cut_monotonic cond body init x)

def prob_while' (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  ⟨fun x => ⨆ (i : ℕ), (prob_while_cut cond body i init x), sorry⟩

def prob_while2' (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  ⟨fun x => ⨆ (i : ℕ), (prob_while_cut2 cond body i init x), sorry⟩

def terminates (cond : T → Bool) (body : T → RandomM T) : Prop :=
  forall init : T, HasSum (prob_while' cond body init) 1

-- theorem termination_01_simple (cond : T → Bool) (body : T → RandomM T) :
--   (forall init : T, cond init → PMF.map cond (body init) false > 0) →
--   terminates cond body := sorry

def prob_while_experiment (cond : T → Bool) (body : T → RandomM T) : T → RandomM T :=
  wcpo.ωSup (myf2 cond body)

def prob_while (cond : T → Bool) (body : T → RandomM T) (h : terminates cond body) (a : T) : RandomM T :=
  ⟨ prob_while' cond body a , sorry ⟩

theorem test_pre : (1 : ENNReal) / 2 ≤ 1 := sorry
def test_cond (b : Bool) : Bool := ¬ b
def test_body (_ : Bool) : RandomM Bool := bernoulli (1/2) test_pre

theorem whileC1 (Φ : ( T → RandomM T) → Prop) (cond : T → Bool) (body : T → RandomM T) (init : T) :
  Φ (λ _ => SubPMF.zero) →
  (∀ wh : (T → RandomM T), Φ wh → Φ (WhileFunctional cond body wh)) →
  Φ (prob_while' cond body) := sorry

def loop : RandomM Bool := prob_while' test_cond test_body false

def test_prop (p : SubPMF Bool) : Prop := p true = 1

theorem whileC2 (Φ : RandomM T → Prop) (cond : T → Bool) (body : T → RandomM T) (init : T) :
  Φ SubPMF.zero →
  (∀ wh : (RandomM T), Φ wh → Φ (WhileFunctional2 cond body wh)) →
  Φ (prob_while2' cond body init) := sorry

def loop2 : RandomM Bool := prob_while2' test_cond test_body false

def test_prop2 (p : SubPMF Bool) : Prop := p true > 0 → p true = 1

theorem test_apply_alt (n : ℕ) :
  prob_while_cut2 test_cond test_body n false true = 1 - (1/2)^n := sorry

-- limit is 1

theorem test_apply2 (term : loop2 true > 0) : test_prop2 loop2 := by
  apply whileC2 test_prop2 test_cond test_body
  . unfold test_prop2
    simp
  . intro wh
    unfold test_prop2
    intro IH
    unfold WhileFunctional2
    simp
    rw [tsum_fintype]
    simp
    rw [IH]
    have H2 : wh false = 0 := sorry
    rw [H2]
    simp
    unfold test_cond
    simp
    sorry



-- theorem prob_while_reduction (P : (T → ENNReal) → Prop) (cond : T → Bool) (body : T → PMF T) (h : terminates cond body) (a : T) :
--   (∀ n : ℕ, forall t : T, t ∈ (prob_while_cut cond body n a).support → ¬ cond t → P (prob_while_cut cond body n a)) →
--   P (prob_while' cond body a) := sorry

-- theorem prob_while_reduction' (P : T → Prop) (cond : T → Bool) (body : T → PMF T) (h : terminates cond body) (a : T) :
--   (∀ n : ℕ, ∀ t ∈ (prob_while_cut cond body n a).support, ¬ cond t → P t) →
--   ∀ t ∈ (prob_while cond body h a).support, P t := sorry

-- theorem prob_while_reduction_quant (P : T → Prop) (cond : T → Bool) (body : T → PMF T) (h : terminates cond body) (a : T) (t : T) :
--   (∀ n : ℕ, t ∈ (prob_while_cut cond body n a).support → ¬ cond t → P t) →
--   t ∈ (prob_while cond body h a).support → P t := sorry

-- theorem prob_while_reduction'' (pmf : PMF T) (cond : T → Bool) (body : T → PMF T) (h : terminates cond body) (a : T) :
--   (∀ n : ℕ, ∀ t : T, ¬ cond t → (prob_while_cut cond body n a) t = pmf t) →
--   ∀ t : T, (prob_while cond body h a) t = pmf t := sorry

-- theorem prob_while_reduction''' (pmf : PMF T) (cond : T → Bool) (body : T → PMF T) (h : terminates cond body) (a : T) :
--   (∀ n : ℕ, ∀ t : T, ¬ cond t → f = prob_while_cut cond body n a -> (hf0 : tsum f ≠ 0) → (hf : tsum f ≠ ∞) → normalize f hf0 hf t = pmf t) →
--   ∀ t : T, (prob_while cond body h a) t = pmf t := sorry

-- theorem prob_while_rule (P : RandomM T -> Prop) (cond : T → Bool) (body : T → RandomM T) (h : terminates cond body) (a : T) :
--   (¬ cond a → P (PMF.pure a)) →
--   (forall whil : RandomM T, P whil → forall t : T, t ∈ whil.support → ¬ cond t → P (body t)) →
--   P (prob_while cond body h a) := sorry

-- theorem prob_while_rule' (f : T -> ENNReal) (cond : T → Bool) (body : T → RandomM T) (h : terminates cond body) (a : T) (x : T) :
--   (¬ cond a → (PMF.pure a)) →
--   (forall whil : RandomM T, P whil → forall t : T, t ∈ whil.support → ¬ cond t → P (body t)) →
--   (prob_while cond body h a) x = f x := sorry
