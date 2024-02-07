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

attribute [simp] Lean.Internal.coeM
attribute [simp] Bind.bind
attribute [simp] Pure.pure
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
attribute [simp] CoeOut.coe

variable {T U : Type} [MeasurableSpace T] [MeasurableSpace U]

abbrev RandomM (T : Type) := Pmf T

noncomputable def prob_while_cut (cond : T → Bool) (body : T → RandomM T) (n : Nat) (a : T) : T → ENNReal :=
  match n with
  | zero => λ x : T => 0
  | succ n =>
    if cond a
    then λ x : T => ∑' c, (body a c) * (prob_while_cut cond body n c) x
    else λ x : T => if x = a then 1 else 0

theorem prob_while_cut_monotonic (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :
  Monotone (fun n : Nat => prob_while_cut cond body n init x) := sorry

def plop1 (cond : T → Bool) (body : T → RandomM T) (init : T) (x : T) :=
  tendsto_atTop_iSup (prob_while_cut_monotonic cond body init x)

noncomputable def prob_while' (cond : T → Bool) (body : T → RandomM T) (init : T) : T → ENNReal :=
  fun x => ⨆ (i : ℕ), (prob_while_cut cond body i init x)

def terminates (cond : T → Bool) (body : T → RandomM T) : Prop :=
  forall init : T, HasSum (prob_while' cond body init) 1

theorem termination_01_simple (cond : T → Bool) (body : T → RandomM T) :
  (forall init : T, cond init → Pmf.map cond (body init) false > 0) →
  terminates cond body := sorry

noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T)(h : terminates cond body) (a : T) : RandomM T :=
  ⟨ prob_while' cond body a , h a ⟩

theorem prob_while_reduction (P : (T → ENNReal) → Prop) (cond : T → Bool) (body : T → Pmf T) (h : terminates cond body) (a : T) :
  (∀ n : ℕ, forall t : T, t ∈ (prob_while_cut cond body n a).support → ¬ cond t → P (prob_while_cut cond body n a)) →
  P (prob_while' cond body a) := sorry

theorem prob_while_rule (P : RandomM T -> Prop) (cond : T → Bool) (body : T → RandomM T) (h : terminates cond body) (a : T) :
  (¬ cond a → P (Pmf.pure a)) →
  (forall whil : RandomM T, P whil → forall t : T, t ∈ whil.support → ¬ cond t → P (body t)) →
  P (prob_while cond body h a) := sorry

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body))  : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) sorry v

def MyP (cond : T → Bool) (body : RandomM T) (x : T) (comp : RandomM T) : Prop :=
  comp x = (body x) / (body.toMeasure {x : T | cond x})

-- theorem prob_until_prop_aux (body : RandomM T) (cond : T → Bool) (a : T) :
--   MyP  (λ v : T => ¬ cond v) body a (prob_while (λ v : T => ¬ cond v) (λ _ : T => body) sorry a) := by
--   have H := prob_while_rule (MyP (λ v : T => ¬ cond v) body a) (λ v : T => ¬ cond v) (λ _ : T => body) sorry (Pmf.bind body (fun v => Pmf.pure v))
--   apply H
--   sorry
  -- . clear H
  --   unfold MyP
  --   simp
  --   sorry
  -- . clear H
  --   unfold MyP
  --   simp
  --   intros inner a2 H

@[simp]
theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) h x =
  ((body x) * (if cond x then 1 else 0)) / (body.toMeasure {x : T | cond x}) := sorry

theorem prob_until_support (body : RandomM T) (cond : T → Bool) (h : terminates cond (λ _ => body)) :
  (prob_until (body : RandomM T) (cond : T → Bool) h).support = {x | cond x} := sorry

theorem prob_until_true (body : RandomM T) (h : terminates (fun _ => true) (λ _ => body)) :
  prob_until body (fun _ => true) h = body := by
  ext x
  rw [prob_until_apply]
  simp

-- Assumption: the Dafny version indeed has this spec
noncomputable def UniformPowerOfTwoSample (n : PNat) : RandomM Nat :=
  uniformOfFintype (Fin (2 ^ (log 2 n)))

@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) :
  x ∈ (UniformPowerOfTwoSample n).support →
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := by
  intro SUPPORT
  simp only [UniformPowerOfTwoSample, Lean.Internal.coeM, Bind.bind, Pure.pure, bind_apply, uniformOfFintype_apply,
    Fintype.card_fin, cast_pow, cast_ofNat, pure_apply, one_div]
  simp only [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeOut.coe]
  -- have k : ENNReal := ((2 ^ log 2 ↑n)⁻¹)
  -- have HYP : Summable (fun a => if x = ↑a then 1 else 0) := sorry
  -- have H := tsum_const_smul' k
  -- rw [tsum_const_smul' k]
  -- rw [tsum_fintype]
  sorry

@[simp]
theorem UniformPowerOfTwoSample_double_apply (n : PNat) (x : Nat) :
  --x ∈ (UniformPowerOfTwoSample (2 * n)).support →
  (UniformPowerOfTwoSample (2 * n)) x = 1 / n := sorry

-- Sample from [0..n)
noncomputable def UniformSample (n : PNat) : RandomM Nat := do
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n) sorry
  return r

theorem UniformSampleCorrect (n : PNat) :
  UniformSample n = uniformOfFintype (Fin n) := by
  ext x
  unfold UniformSample
  simp
  -- rw [prob_until_apply (UniformPowerOfTwoSample (2 * n)) (fun x => decide (x < PNat.val (2 * n))) sorry]
  -- simp
  -- unfold UniformPowerOfTwoSample
  -- unfold UniformPowerOfTwoSample'
  -- simp
  -- rw [tsum_fintype]
  -- rw [tsum_fintype]
  -- rw [tsum_fintype]
  -- -- conv =>
  -- --   left
  -- --   left
  -- --   right
  -- --   intro b
  -- --   simp
  -- --   rw [uniformOfFintype_apply]
  sorry

theorem UniformSample_apply (n : PNat) (x : Nat) :
  x < n →
  UniformSample n x = 1 / n := by
  intro SUPPORT
  unfold UniformSample
  simp
  sorry

noncomputable def BernoulliSample (num : Nat) (den : PNat) : RandomM Bool := do
  let d ← UniformSample den
  return d < num

-- #check Finset.filter_gt_eq_Iio
theorem BernoulliSampleCorrect (num : Nat) (den : PNat) :
  BernoulliSample num den true = num / den := by
  simp
  unfold BernoulliSample
  rw [UniformSampleCorrect]
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
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den) sorry (true,1)
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
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1 num) (λ x : Nat × Bool => x.2) sorry
  let U := r1.1
  let r2 ← prob_while (λ K : Bool × PNat => K.1) (DiscreteLaplaceSampleLoopIn2 1 1) sorry (true,1)
  let V := r2.2 - 2
  let X := U + num * V
  let Y := floor (X / den)
  let B ← BernoulliSample 1 2
  return (B,Y)

noncomputable def DiscreteLaplaceSample (num den : PNat) : RandomM Int := do
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0)) sorry
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
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2) sorry
  return r.1

end Hurd
