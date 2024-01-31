import Mirror.H1
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Rat.Basic

open Classical Set Function ProbabilityTheory Nat MeasureTheory MeasurableSpace

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

abbrev RandomM (T : Type) := StateT BitStream (OptionT (Except String)) T

def lift1 (f : StateT BitStream Option T) : RandomM T :=
  λ s : BitStream => Except.ok (f s)

def lift2 (f : StateM BitStream T) : RandomM T :=
  λ s : BitStream => Except.ok (some (f s))

#check Membership
#check image
#check preimage

def mypreim1 (f : RandomM T) (E : Set T) : Set BitStream :=
  { s : BitStream | exists v, f s = Except.ok (some v) ∧ v.1 ∈ E }

def mypreim2 (f : RandomM T) (E : Set BitStream) : Set BitStream :=
  { s : BitStream | exists v, f s = Except.ok (some v) ∧ v.2 ∈ E }

def family1 (f : RandomM T) : Set (Set BitStream) :=
  { S : Set BitStream | exists I: Set T, MeasT.MeasurableSet' I ∧ mypreim1 f I = S }

def family2 (f : RandomM T) : Set (Set BitStream) :=
  { S : Set BitStream | exists I: Set BitStream, Eps.MeasurableSet' I ∧ mypreim2 f I = S }

def Coin : RandomM Bool := do
  let rng ← get
  let f: BitStream := λ n : Nat => rng (n + 1)
  set f
  return (rng 0)

def countable (f: RandomM T) : Prop :=
  Countable { y : T | exists (s s' : BitStream), f s = Except.ok (some (y,s')) }

def measurable (f : RandomM T) : Prop :=
  Measurable f

def independent (f : RandomM T) : Prop :=
  IndepSets (family1 f) (family2 f)

def prefix_cover (C : Set (List Bool)) : Prop :=
  (∀ l₁ l₂ : List Bool, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂ → ¬ l₁ <+: l₂)
  ∧ Prob.volume (⋃ l ∈ C, prefix_set l) = 1

def strongly_independent (f : RandomM T) : Prop :=
  countable f ∧ measurable f
  ∧ exists C : Set (List Bool), prefix_cover C
    ∧ ∀ (l : List Bool) (s : BitStream), l ∈ C ∧ s ∈ prefix_set l
    ∧ exists v, f s = Except.ok (some v)
    ∧ exists v', f (prefix_seq l) = Except.ok (some v')
    → v = (v'.1, sdrop (List.length l) s)

def prob_while_cut (cond : T → Bool) (body : T → RandomM T) (n : Nat) (a : T) : RandomM T :=
  match n with
  | zero => return a
  | succ n => if cond a then
    do let v ← body a
       prob_while_cut cond body n v
    else return a

-- Smallest n that satisfies f
noncomputable def minimal (f : Nat → Bool) : Nat := sorry

-- var state := a;
-- while (cond state)
--  decreases *
-- {
--   state := body(state);
-- }
noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (a : T) : RandomM T := do
  let s ← get
  if (∃ n : Nat, ∃ v, prob_while_cut cond body n a s = Except.ok (some v) ∧ ¬ cond v.1)
  then prob_while_cut cond body (minimal (λ n : Nat =>  ∃ v, prob_while_cut cond body n a s = Except.ok (some v) ∧ ¬ cond v.1)) a
  else λ _ : BitStream => Except.ok none

-- Sample from [0..2^k - 1]
def UniformPowerOfTwoSample' (k : Nat) : RandomM Nat := do
  if k = 0 then throwThe String "UniformPowerOfTwoSample: k = 0"
  else
    let flip ← Coin
    let v ← UniformPowerOfTwoSample' (k - 1)
    if flip
    then return v + 2 ^ (k - 1)
    else return v + 0

def UniformPowerOfTwoSample (k : Int) : RandomM Int := sorry

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
  else if iter = 1 then return true
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

noncomputable def DiscreteLaplaceSampleLoop (num den : Int) : RandomM (Bool × Int × Int) := do
  if den ≤ 0 then throwThe String "DiscreteLaplaceSampleLoop: den ≤ 0" else
  let r1 ← prob_until (DiscreteLaplaceSampleLoopIn1 num) (λ x : Int × Bool => x.2)
  let U := r1.1
  let r2 ← prob_while (λ K : Bool × Int => K.1) (DiscreteLaplaceSampleLoopIn2 1 1) (true,1)
  let V := r2.2
  let X := U + num * V
  let Y := floor (X / den)
  let B ← BernoulliSample 1 2
  let B' := if B then 1 else 0
  let Z := (1 - 2 * B') * Y
  return (B,Y,Z)

noncomputable def DiscreteLaplaceSample (num den : Int) : RandomM Int := do
  if num < 1 then throwThe String "DiscreteLaplaceSample: t < 1" else
  if den < 1 then throwThe String "DiscreteLaplaceSample: s < 1" else
  let r ← prob_until (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Int × Int => x.1 ∧ x.2.1 = 0)
  return r.2.2

noncomputable def DiscreteGaussianSampleLoop (num den : Int) (t : Int) : RandomM (Int × Bool) := do
  if den ≤ 0 then throwThe String "DiscreteGaussianSample: den ≤ 0" else
  let Y ← DiscreteLaplaceSample t 1
  let C ← BernoulliExpNegSample ((abs Y - num / (den * t))^2)  (2 * num / den)
  return (Y,C)

noncomputable def DiscreteGaussianSample (num den : Int) : RandomM Int := do
  if num < 0 then throwThe String "DiscreteGaussianSample: num < 0" else
  if den ≤ 0 then throwThe String "DiscreteGaussianSample: den ≤ 0" else
  let t : Nat := floor (num / den) + 1
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
