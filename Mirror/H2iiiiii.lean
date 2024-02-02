import Mirror.H1
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Uniform

open Classical Set Function ProbabilityTheory Nat MeasureTheory MeasurableSpace
open Pmf

section Hurd

variable {T U : Type}


abbrev RandomM (T : Type) := ReaderT Nat (OptionT Pmf) T

-- State monad with decreasing fuel?

@[simp]
noncomputable def Coin : RandomM Bool := do
  let flip ← binomial (1/2) sorry 1
  if flip.val = 0 then return false else return true

noncomputable def test1 := (Coin 4)
noncomputable def test2 := (Coin 4).run
theorem test3 : forall n: Nat, (Coin n).run none = 0 := sorry
theorem test4 : forall n: Nat, (Coin n).run (some true) = 1 / 2 := sorry

@[simp]
noncomputable def coin1 : RandomM (Fin 2) := binomial (1/2) sorry 1
@[simp]
noncomputable def coin2 : Pmf (Fin 2) := binomial (1/2) sorry 1

theorem test5 : forall n: Nat, (coin1 n).run none = 0 := by
  intros n
  unfold OptionT.run
  unfold coin1
  simp
  unfold liftM
  unfold monadLift
  unfold instMonadLiftT
  simp
  unfold MonadLift.monadLift
  unfold ReaderT.instMonadLiftReaderT
  simp
  unfold OptionT.instMonadLiftOptionT
  simp
  unfold OptionT.lift
  unfold OptionT.mk
  unfold Pure.pure
  unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold instMonadPmf
  simp

theorem test6 : forall n: Nat, (coin1 n).run none = 0 → coin1 = coin2 := by
  intros; ext; simp

theorem conclusion : coin1 = coin2 := by
  apply test6
  apply test5
  constructor


-- Proof that the fuel is large enough?
noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  λ n : Nat =>
    match n with
    | zero => pure none
    | succ n =>
      if cond init
      then
        do
        let v ← ((body init).run n).run
        prob_while cond body v n
      else return init

-- noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T := sorry

--noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (a : T) : RandomM T := sorry

noncomputable def UniformPowerOfTwoSample (k : Int) : RandomM Int := sorry

-- Extraction starts here

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

-- Sample from [0..n)
noncomputable def UniformSample (n : Nat) (_ : n ≥ 1) : RandomM Int := do
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Int => x ≥ n)
  return r

noncomputable def BernoulliSample (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) : RandomM Bool := do
  let d ← UniformSample den h2
  return d < num

theorem intExtra1 (n : Int) (h : n > 0) : 2 * n > 0 := by
  simp only [← gt_iff_lt, zero_lt_mul_left, imp_self]
  trivial

noncomputable def BernoulliExpNegSampleUnitLoop (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) (state : (Bool × Int)) : RandomM (Bool × Int) := do
  let A ← BernoulliSample num (state.2 * den) h1 (intExtra1 den h2) sorry
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnit (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) : RandomM Bool := do
  let r ← prob_while (λ state : Bool × Int => state.1) (BernoulliExpNegSampleUnitLoop num den h1 h2 h3) (true,1)
  let K := r.2
  if K % 2 = 0 then return true else return false

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  --else if iter = 1 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 sorry sorry sorry
    let R ← BernoulliExpNegSampleGenLoop (iter - 1)
    return (B ∧ R)

noncomputable def BernoulliExpNegSample (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) : RandomM Bool := do
  if num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den h1 h2 h3
       return X
  else
    let gamf := floor (num / den)
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
         let num := num - gamf * den
         let X ← BernoulliExpNegSampleUnit num den sorry h2 sorry
         return X
    else return false

noncomputable def DiscreteLaplaceSampleLoopIn1 (t : Int) : RandomM (Int × Bool) := do
  let U ← UniformSample t sorry
  let D ← BernoulliExpNegSample U t sorry sorry sorry
  return (U,D)

noncomputable def DiscreteLaplaceSampleLoopIn2 (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) (K : Bool × Int) : RandomM (Bool × Int) := do
  let A ← BernoulliExpNegSampleUnit num den h1 h2 h3
  return (A, K.2 + 1)

noncomputable def DiscreteLaplaceSampleLoop (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) : RandomM (Bool × Int) := do
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1 num) (λ x : Int × Bool => ¬ x.2)
  let U := r1.1
  let r2 ← prob_while (λ K : Bool × Int => K.1) (DiscreteLaplaceSampleLoopIn2 1 1 sorry sorry sorry) (true,1)
  let V := r2.2 - 2
  let X := U + num * V
  let Y := floor (X / den)
  let B ← BernoulliSample 1 2 sorry sorry sorry
  return (B,Y)

noncomputable def DiscreteLaplaceSample (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) : RandomM Int := do
  let r ← prob_until (DiscreteLaplaceSampleLoop num den h1 h2 h3) (λ x : Bool × Int => x.1 ∧ x.2 = 0)
  let Z := if r.1 then - r.2 else r.2
  return Z

noncomputable def DiscreteGaussianSampleLoop (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) (t : Int) : RandomM (Int × Bool) := do
  let Y ← DiscreteLaplaceSample t 1 sorry sorry sorry
  let y := abs Y
  let n := (y * t * den - num)^2
  let d := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d sorry sorry sorry
  return (Y,C)

noncomputable def DiscreteGaussianSample (num den : Int) (h1 : num ≥ 0) (h2 : den > 0) (h3 : num ≤ den) : RandomM Int := do
  let t : Nat := floor (num / den) + 1
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den sorry sorry sorry t) (λ x : Int × Bool => ¬ x.2)
  return r.1

-- Trying out reasoning

attribute [simp] Measure.ofAddContent_eq

-- theorem uniformP2_correct (k : Nat) (n : Nat) (_ : 0 ≤ n ∧ n < 2 ^ k) :
--   Prob.volume { s : BitStream | exists s' : BitStream, (UniformPowerOfTwoSample k) s = Except.ok (some (n,s')) } = 1 / 2 ^ k := by
--     revert n
--     induction k
--     . intro n H
--       simp at H
--       subst H
--       simp
--       unfold μ
--       rw [Measure.ofAddContent_eq]
--       unfold UniformPowerOfTwoSample
--       simp
--       sorry
--       sorry -- MeasurableSet
--     . rename_i k iH
--       intro n DOM
--       have HCase : n < 2 ^ k ∨ exists m : Nat, m < 2 ^ k ∧ n = 2 ^ k + m := sorry
--       cases HCase
--       . rename_i CONS
--         have RES := iH n
--         simp at RES
--         have RES2 := RES CONS
--         sorry -- probability to be in lower range is 1/2
--         -- Coin must be independent from the lower bits
--       . rename_i CONS
--         cases CONS
--         rename_i m CONS2
--         cases CONS2
--         rename_i left right
--         have RES := iH m
--         simp at RES
--         have RES2 := RES left
--         sorry

-- theorem uniform_correct (n : Nat) (m : Nat) :
--   Prob.volume { s : BitStream | exists s' : BitStream, (UniformSample n) s = Except.ok (some (m,s')) } = 1 / n := by
--   simp ; unfold μ ; rw [Measure.ofAddContent_eq] ; simp
--   unfold AddContent.toFun ; unfold cont ; simp
--   unfold UniformSample
--   sorry
--   sorry


end Hurd
