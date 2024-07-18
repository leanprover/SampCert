/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

/-!
# SLang

This file describes the SLang language.

## Implementation notes

Each ``SLang`` value is a distribution over a type (normalization of these distributions
is proven separately). There are no restrictions on the type; the underlying probability
space should be interpreted as discrete.
-/

open Classical Nat ENNReal PMF

/--
The monad of ``SLang`` values
-/
abbrev SLang.{u} (α : Type u) : Type u := α → ℝ≥0∞

namespace PMF

/--
``SLang`` value from ``PMF``
-/
def toSLang (p : PMF α) : SLang α := p.1

@[simp]
theorem toSLang_apply (p : PMF α) (x : α) : (toSLang p x) = p x := by
  unfold toSLang
  unfold DFunLike.coe
  unfold instFunLike
  simp

instance : Coe (PMF α) (SLang α) where
  coe a := toSLang a

end PMF

/-!
### Program terms of ``SLang``
-/
namespace SLang

variable {T U : Type}

/--
The zero distribution as a ``SLang``.
-/
def probZero : SLang T := λ _ : T => 0

/--
The Dirac distribution as a ``SLang``.
-/
@[extern "prob_Pure"]
def probPure (a : T) : SLang T := fun a' => if a' = a then 1 else 0

/--
Monadic bind for ``SLang`` values.
-/
@[extern "prob_Bind"]
def probBind (p : SLang T) (f : T → SLang U) : SLang U :=
  fun b => ∑' a, p a * f a b

instance : Monad SLang where
  pure a := probPure a
  bind pa pb := pa.probBind pb

/--
``SLang`` value for the uniform distribution over ``m`` elements, where
the number``m`` is the largest power of two that is at most ``n``.
-/
-- MARKUSDE: I would like to change this to ``probUniformP2`` once it doesn't break extraction.
@[extern "prob_UniformP2"]
def UniformPowerOfTwoSample (n : ℕ+) : SLang ℕ :=
  toSLang (PMF.uniformOfFintype (Fin (2 ^ (log 2 n))))

/--
``SLang`` functional which executes ``body`` only when ``cond`` is ``false``.
-/
def probWhileFunctional (cond : T → Bool) (body : T → SLang T) (wh : T → SLang T) : T → SLang T :=
  λ a : T =>
  if cond a
    then do
      let v ← body a
      wh v
    else return a

/--
``SLang`` value obtained by unrolling a loop body exactly ``n`` times.
-/
def probWhileCut (cond : T → Bool) (body : T → SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => probZero
  | succ n => probWhileFunctional cond body (probWhileCut cond body n) a


/--
``SLang`` value for an unbounded iteration of a loop.
-/
@[extern "prob_While"]
def probWhile (cond : T → Bool) (body : T → SLang T) (init : T) : SLang T :=
  fun x => ⨆ (i : ℕ), (probWhileCut cond body i init x)

/--
``SLang`` value which rejects samples from ``body`` until they satisfy ``cond``.
-/
--@[extern "prob_Until"]
def probUntil (body : SLang T) (cond : T → Bool) : SLang T := do
  let v ← body
  probWhile (λ v : T => ¬ cond v) (λ _ : T => body) v

@[extern "my_run"]
opaque run (c : SLang T) : IO T

/-- ``Slang`` term for a uniform sample over [0, n). Implemented using rejection sampling on
  top of the power of two uniform sampler ``probUniformP2``. -/
def UniformSample (n : PNat) : SLang Nat := do
  let r ← probUntil (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
  return r

/--
``SLang`` term for Bernoulli trial.

Samples ``true`` with probability ``num / den``.
-/
def BernoulliSample (num : Nat) (den : PNat) (_ : num ≤ den) : SLang Bool := do
  let d ← UniformSample den
  return d < num

lemma halve_wf (num : Nat) (den st : PNat) (wf : num ≤ den) :
  num ≤ ↑(st * den) := by
  simp
  cases st
  rename_i v p
  simp
  exact le_mul_of_one_le_of_le p wf

/--
``SLang`` term which changes the state, according to the discrete Von Neumann's algorithm.

In particular, it updates the state ``(_, n)`` to
  - ``(true, n+1)`` with probability ``(num/den) / n``
  - ``(false, n+1)`` with probability ``1 - (num/den) / n``
-/
def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den) (state : (Bool × PNat)) : SLang (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
  return (A, state.2 + 1)

/--
``SLang`` term for the distribution over ``ℕ`` obtained by performing discrete Von Neumann
updates until the state becomes ``false``, and returning one more than the total number
of updates.

In particular, at ``n ≥ 2`` this distribution evaluates to
```
  (num/den)/1 ⬝ (num/den)/2 ⬝ ⋯ ⬝ (num/den)/(n-2) ⬝ (1 - (num/den)(n-1))
= (num/den)^(n-2) / (n-2)! - (num/den)^(n-1) / (n-1)!
```
and evaluates to ``0`` at ``0``.
-/
def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Nat := do
  let r ← probWhile (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
  return r.2

/--
``SLang`` term which samples ``true`` with probability ``exp (-num/den)``.


This program implments this distrubution by returning ``true`` when
``BernoulliExpNegSampleUnitAux`` is even, namely with probability
```
  0 + (num/den)^0 / 0! - (num/den)^1 / 1! + (num/den)^2 / 2! - (num/den)^3 / 3! + ...
= ∑ (n : ℕ) (-num/den)^i / i!
= exp (-num/den)
```
-/
def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Bool := do
  let K ← BernoulliExpNegSampleUnitAux num den wf
  if K % 2 = 0 then return true else return false

/--
``SLang`` term which samples ``true`` with probability ``exp (- iter)``.

In particular this program returns true upon the success of ``iter`` trials of
``BernoulliExpNegSampleUnit 1 1``, which occurs with probability
  ```
    exp (-1/1) ⬝ ... ⬝ exp (-1/1) = exp (- iter)
  ```
-/
def BernoulliExpNegSampleGenLoop (iter : Nat) : SLang Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
    if ¬ B then return B else
      let R ← BernoulliExpNegSampleGenLoop (iter - 1)
      return R

/--
Proof term to apply a a call to ``BernoulliExpNegSampleUnit``.
-/
lemma rat_less_floor_le1 (num : Nat) (den : PNat) :
  (num % den) ≤ den := by
  have A := Nat.mod_lt num (PNat.pos den)
  exact Nat.lt_succ.mp (Nat.le.step A)

/--
``SLang`` term which samples ``true`` with probability ``exp (- num / den)``.

The algorithm returns ``true`` when a trial for both the integral and fractional
parts of ``num/den``, since
```
exp (-num/den) = exp((-num/den : ℕ_{≤0}) + (num % den)) = exp (-num/den : ℕ_{≤0}) ⬝exp (num % den)
```
-/
-- Can I combine the cases here? Can't tell which way would be less annoying down the road.
def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := do
  if h : num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den h
       return X
  else
    let gamf := num / den
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
      let X ← BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)
      return X
    else return false

def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : SLang (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

def DiscreteLaplaceSampleLoopIn1 (t : PNat) : SLang Nat := do
  let r1 ← probUntil (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
  return r1.1

-- Note that for the arxiv algorithm, we can call Unit directly
def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat)  (K : Bool × Nat) : SLang (Bool × Nat) := do
  let A ← BernoulliExpNegSample num den
  return (A, K.2 + 1)

def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : SLang Nat := do
  let r2 ← probWhile (λ K : Bool × Nat => K.1) (DiscreteLaplaceSampleLoopIn2Aux num den) (true,0)
  return r2.2

-- We need to generate and test both implementations
def DiscreteLaplaceSampleLoop' (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
  let U ← DiscreteLaplaceSampleLoopIn1 num
  let v ← DiscreteLaplaceSampleLoopIn2 1 1
  let V := v - 1
  let X := U + num * V
  let Y := X / den
  let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
  return (B,Y)

def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
  let v ← DiscreteLaplaceSampleLoopIn2 den num
  let V := v - 1
  let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
  return (B,V)

/--
``SLang`` term to obtain a sample from the discrete Laplace distribution.
-/
def DiscreteLaplaceSample (num den : PNat) : SLang ℤ := do
  let r ← probUntil (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

/--
Sample a candidate for the Discrete Gaussian with variance ``num/den``.
-/
def DiscreteGaussianSampleLoop (num den t : PNat) : SLang (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSample t 1
  let y : Nat := Int.natAbs Y
  let n : Nat := (Int.natAbs (Int.sub (y * t * den) num))^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

/--
``SLang`` term to sample a value from the Discrete Gaussian with variance ``(num/den)``^2.
-/
def DiscreteGaussianSample (num : PNat) (den : PNat) : SLang ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , by simp only [add_pos_iff, zero_lt_one, or_true] ⟩
  let num := num^2
  let den := den^2
  let r ← probUntil (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2)
  return r.1

-- The following is unsound and should NOT be part of the code
-- We are using it for now until the Python FFI is richer
@[extern "dirty_io_get"]
opaque DirtyIOGet(x : IO ℤ) : UInt32

@[export dgs_print]
def DiscreteGaussianSamplePrint (num den : UInt32) : IO Unit := do
  let z ← run <| DiscreteGaussianSample ⟨ num.toNat , sorry ⟩ ⟨ den.toNat , sorry ⟩
  IO.println s!"Result = {z}"

@[export dgs_get]
def DiscreteGaussianSampleGet (num den : UInt32) : UInt32 := Id.run do
  let z : IO ℤ ← run <| DiscreteGaussianSample ⟨ num.toNat , sorry ⟩ ⟨ den.toNat , sorry ⟩
  return DirtyIOGet z

@[export my_test]
def Test(u : UInt32) : UInt32 :=
  u + 1

end SLang
