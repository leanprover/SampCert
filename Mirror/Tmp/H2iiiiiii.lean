import Mirror.H1
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Init.Control.Lawful
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.LiminfLimsup

open Classical Set Function ProbabilityTheory Nat MeasureTheory MeasurableSpace
open Pmf PNat Finset TopologicalSpace Filter

section Hurd

variable {T U : Type} [Inhabited T]

abbrev RandomM (T : Type) := OptionT Pmf T

attribute [simp] OptionT.run
attribute [simp] liftM
attribute [simp] monadLift
attribute [simp] instMonadLiftT
attribute [simp] MonadLift.monadLift
attribute [simp] ReaderT.instMonadLiftReaderT
attribute [simp] OptionT.instMonadLiftOptionT
attribute [simp] OptionT.lift
attribute [simp] OptionT.mk
attribute [simp] Pure.pure
attribute [simp] Applicative.toPure
attribute [simp] Monad.toApplicative
attribute [simp] instMonadPmf
attribute [simp] Lean.Internal.coeM
attribute [simp] CoeT.coe
attribute [simp] instCoeT
attribute [simp] CoeHTCT.coe
attribute [simp] instCoeHTCT_1
attribute [simp] CoeHTC.coe
attribute [simp] instCoeHTC_1
attribute [simp] CoeOTC.coe
attribute [simp] instCoeOTC_1
attribute [simp] CoeTC.coe
attribute [simp] instCoeTC_1
attribute [simp] Coe.coe
attribute [simp] optionCoe
attribute [simp] Bind.bind
attribute [simp] Monad.toBind
attribute [simp] ReaderT.instMonadReaderT
attribute [simp] ReaderT.bind
attribute [simp] ReaderT.pure
attribute [simp] OptionT.pure
attribute [simp] OptionT.bind
attribute [simp] OptionT.mk

noncomputable def prob_while_cut (cond : T → Bool) (body : T → RandomM T) (init : T) (n : Nat) : RandomM T :=
  match n with
  | zero => pure none
  | succ n =>
    if cond init
    then
      do
      let v ← body init
      prob_while_cut cond body v n
    else return init

theorem prob_while_cut_monotonic (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :
  Monotone (fun n : Nat => (prob_while_cut cond body init n).run (some x)) := sorry

theorem prob_while_cut_antitonic (cond : T → Bool) (body : T → RandomM T) (init : T) :
  Antitone (fun n : Nat => (prob_while_cut cond body init n).run none) := sorry

def plop1 (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :=
  tendsto_atTop_iSup (prob_while_cut_monotonic cond body init x)

def plop2 (cond : T → Bool) (body : T → RandomM T) (init : T) :=
  tendsto_atBot_iSup (prob_while_cut_antitonic cond body init)

noncomputable def prob_while' (cond : T → Bool) (body : T → RandomM T) (init : T) : Option T → ENNReal :=
  fun x => if x = none then ⨅ (i : ℕ), ((prob_while_cut cond body init i).run x) else ⨆ (i : ℕ), ((prob_while_cut cond body init i).run x)

theorem sum1 (cond : T → Bool) (body : T → RandomM T) (init : T) :
  HasSum (prob_while' cond body init) 1 := sorry

noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T :=
  ⟨ prob_while' cond body init , sum1 cond body init ⟩

-- If cond has probability non-zero, then prob_While cond body init none = 0
--

noncomputable def unfold_while (cond : T → Bool) (body : T → RandomM T) (init : T) : RandomM T := do
  if cond init
  then let v ← body init
       prob_while cond body v
  else return init

theorem prob_while_prop_1 (cond : T → Bool) (body : T → RandomM T) (init : T) :
  prob_while cond body init = unfold_while cond body init := sorry

noncomputable def UniformPowerOfTwoSample (k : PNat) : RandomM Nat :=
  uniformOfFintype (Fin (2 ^ k))

-- Extraction starts here

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

-- Sample from [0..n)
noncomputable def UniformSample (n : PNat) : RandomM Nat := do
  let r ← prob_until (UniformPowerOfTwoSample (n + n)) (λ x : Nat => x < n)
  return r

theorem UniformSampleCorrect1 (n : PNat) :
  (UniformSample n).run none = 0 →
  (UniformSample n).run = uniformOfFintype (Fin n) := by sorry

theorem UniformSampleCorrect2 (n : PNat) :
  (UniformSample n).run none = 0 := by sorry

theorem UniformSampleCorrect (n : PNat) :
  (UniformSample n).run = uniformOfFintype (Fin n) := by sorry

noncomputable def BernoulliSample (num : Nat) (den : PNat) : RandomM Bool := do
  let d ← UniformSample den
  return d < num

theorem BernoulliSampleCorrect (num : Nat) (den : PNat) :
  (BernoulliSample num den).run none = 0 →
  (BernoulliSample num den).run (some true) = num / den := by
  simp
  intro H
  unfold BernoulliSample
  -- rw UniformSampleCorrect
  have H2 := UniformSampleCorrect den
  simp at H2
  rw [H2]
  simp
  rw [tsum_fintype]
  rw [sum_ite]
  simp


  sorry

theorem intExtra1 (n : Int) (h : n > 0) : 2 * n > 0 := by
  simp only [← gt_iff_lt, zero_lt_mul_left, imp_self]
  trivial

noncomputable def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (state : (Bool × PNat)) : RandomM (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den)
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) : RandomM Bool := do
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den) (true,1)
  let K : Nat := r.2
  if K % 2 = 0 then return true else return false

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1
    let R ← BernoulliExpNegSampleGenLoop (iter - 1)
    return (B ∧ R)

noncomputable def BernoulliExpNegSample (num : Nat) (den : PNat) : RandomM Bool := do
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

noncomputable def DiscreteLaplaceSampleLoopIn1 (t : PNat) : RandomM (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

noncomputable def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) (K : Bool × PNat) : RandomM (Bool × PNat) := do
  let A ← BernoulliExpNegSampleUnit num den
  return (A, K.2 + 1)

noncomputable def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : RandomM (Bool × Nat) := do
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1 num) (λ x : Nat × Bool => x.2)
  let U := r1.1
  let r2 ← prob_while (λ K : Bool × PNat => K.1) (DiscreteLaplaceSampleLoopIn2 1 1) (true,1)
  let V := r2.2 - 2
  let X := U + num * V
  let Y := floor (X / den)
  let B ← BernoulliSample 1 2
  return (B,Y)

noncomputable def DiscreteLaplaceSample (num den : PNat) : RandomM Int := do
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

noncomputable def DiscreteGaussianSampleLoop (num den t : PNat) : RandomM (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSample t 1
  let y : Nat := Int.natAbs Y
  let n : Nat := (y * t * den - num)^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

theorem Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, or_true]

noncomputable def DiscreteGaussianSample (num : PNat) (den : PNat) : RandomM Int := do
  let ti : Nat := floor (num.val / den)
  let t : PNat := ⟨ ti + 1 , Add1 ti ⟩
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2)
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
