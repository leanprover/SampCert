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
variable [MeasT: MeasurableSpace T] [MeasU : MeasurableSpace U]

-- All kinds of instances in MeasurableSpace Basic
--instance M0 : MeasurableSpace BitStream := ⊤
--instance M1 : MeasurableSpace (T × BitStream) := ⊤
--instance M2 : MeasurableSpace (Option (T × BitStream)) := ⊤
instance M3 : MeasurableSpace (StateT BitStream Option T) := ⊤
instance M4 : MeasurableSpace (ExceptT String (StateT BitStream Option) T) := ⊤
instance M5 : MeasurableSpace (OptionT (Except String) (T × BitStream)) := ⊤

--abbrev RandomM (T : Type) := StateT BitStream (OptionT (Except String)) T

--abbrev RandomM (T : Type) := ExceptT String Pmf T

abbrev RandomM (T : Type) := StateT Nat (ExceptT String Pmf) T

-- State monad with decreasing fuel?

@[simp]
noncomputable def Coin : RandomM Bool := do
  let flip ← binomial (1/2) sorry 1
  if flip.val = 0 then return false else return true

noncomputable def test1 := Coin 4
noncomputable def test2 := (Coin 4).run

theorem test3 : exists n : Nat, forall m : Nat, (Coin n).run (Except.ok (true,m)) = 1 / 2 := sorry

noncomputable def UniformPowerOfTwoSampleD (k : Nat) : RandomM Nat := do
  if k = 0 then throwThe String "UniformPowerOfTwoSample: k = 0"
  else
    let flip ← Coin
    let v ← UniformPowerOfTwoSampleD (k - 1)
    if flip
    then return v + 2 ^ (k - 1)
    else return v + 0

noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  λ n : Nat =>
    match n with
    | zero => throwThe String "Ran out of fuel"
    | succ n =>
      if cond init
      then
        do
        let v ← ((body init).run n).run
        prob_while cond body v.1 n
      else return (init,n)

--noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (a : T) : RandomM T := sorry

noncomputable def UniformPowerOfTwoSample (k : Int) : RandomM Int := sorry

-- Extraction starts here

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

-- Sample from [0..n)
noncomputable def UniformSample (n : Int) : RandomM Int := do
  if n < 1 then throwThe String "UniformSample: n < 1" else
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Int => x ≥ n)
  return r

noncomputable def BernoulliSample (num den : Int) : RandomM Bool := do
  if num < 0 then throwThe String "BernoulliSample: num < 0" else
  if num > den then throwThe String "BernoulliSample: num > den" else
  let d ← UniformSample den
  return d < num

noncomputable def BernoulliExpNegSampleUnitLoop (num den : Int) (state : (Bool × Int)) : RandomM (Bool × Int) := do
  let A ← BernoulliSample num (state.2 * den)
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnit (num den : Int) : RandomM Bool := do
  if num < 0 then throwThe String "BernoulliExpNegSampleUnit: num < 0" else
  let r ← prob_while (λ state : Bool × Int => state.1) (BernoulliExpNegSampleUnitLoop num den) (true,1)
  let K := r.2
  if K % 2 = 0 then return true else return false

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  --else if iter = 1 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1
    let R ← BernoulliExpNegSampleGenLoop (iter - 1)
    return (B ∧ R)

noncomputable def BernoulliExpNegSample (num den : Int) : RandomM Bool := do
  if num < 0 then throwThe String "BernoulliExpNegSample: num < 0" else
  if den ≤ 0 then throwThe String "BernoulliExpNegSample: den ≤ 0" else
  if num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den
       return X
  else
    let gamf := floor (num / den)
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
         let num := num - gamf * den
         let X ← BernoulliExpNegSampleUnit num den
         return X
    else return false

noncomputable def DiscreteLaplaceSampleLoopIn1 (t : Int) : RandomM (Int × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

noncomputable def DiscreteLaplaceSampleLoopIn2 (num den : Int) (K : Bool × Int) : RandomM (Bool × Int) := do
  let A ← BernoulliExpNegSampleUnit num den
  return (A, K.2 + 1)

noncomputable def DiscreteLaplaceSampleLoop (num den : Int) : RandomM (Bool × Int) := do
  if den ≤ 0 then throwThe String "DiscreteLaplaceSampleLoop: den ≤ 0" else
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1 num) (λ x : Int × Bool => ¬ x.2)
  let U := r1.1
  let r2 ← prob_while (λ K : Bool × Int => K.1) (DiscreteLaplaceSampleLoopIn2 1 1) (true,1)
  let V := r2.2 - 2
  let X := U + num * V
  let Y := floor (X / den)
  let B ← BernoulliSample 1 2
  return (B,Y)

noncomputable def DiscreteLaplaceSample (num den : Int) : RandomM Int := do
  if num < 1 then throwThe String "DiscreteLaplaceSample: t < 1" else
  if den < 1 then throwThe String "DiscreteLaplaceSample: s < 1" else
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Int => x.1 ∧ x.2 = 0)
  let Z := if r.1 then - r.2 else r.2
  return Z

noncomputable def DiscreteGaussianSampleLoop (num den : Int) (t : Int) : RandomM (Int × Bool) := do
  if den ≤ 0 then throwThe String "DiscreteGaussianSample: den ≤ 0" else
  let Y ← DiscreteLaplaceSample t 1
  let y := abs Y
  let n := (y * t * den - num)^2
  let d := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

noncomputable def DiscreteGaussianSample (num den : Int) : RandomM Int := do
  if num < 0 then throwThe String "DiscreteGaussianSample: num < 0" else
  if den ≤ 0 then throwThe String "DiscreteGaussianSample: den ≤ 0" else
  let t : Nat := floor (num / den) + 1
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => ¬ x.2)
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
