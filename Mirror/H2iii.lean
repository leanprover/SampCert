import Mirror.H1
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Rat.Basic

open Classical Set Function ProbabilityTheory Nat MeasureTheory

section Hurd

variable {T U : Type}
variable [MeasurableSpace T] [MeasurableSpace U]

-- All kinds of instances in MeasurableSpace Basic
--instance M0 : MeasurableSpace BitStream := ⊤
--instance M1 : MeasurableSpace (T × BitStream) := ⊤
--instance M2 : MeasurableSpace (Option (T × BitStream)) := ⊤
instance M3 : MeasurableSpace (StateT BitStream Option T) := ⊤
instance M4 : MeasurableSpace (ExceptT String (StateT BitStream Option) T) := ⊤

abbrev RandomM (T : Type) := ExceptT String (StateT BitStream Option) T

def Coin : RandomM Bool := do
  let rng ← get
  let f: BitStream := λ n : Nat => rng (n + 1)
  set f
  return (rng 0)

def countable (f : RandomM T) : Prop :=
  Countable { y : T | ∃ (g: StateT BitStream Option T) (x : BitStream) (r : BitStream ), f = g ∧  g.run x = (y,r) }

def prob_while_cut (cond : T → Bool) (body : T → RandomM T) (n : Nat) (a : T) : RandomM T :=
  match n with
  | zero => return a
  | succ n => if cond a then
    do let v ← body a
       prob_while_cut cond body n v
    else return a

-- Smallest n that satisfies f
noncomputable def minimal (f : Nat → Bool) : Nat := sorry

noncomputable def prob_while (cond : T → Bool) (body : T → RandomM T) (a : T) : RandomM T := do
  let s ← get
  if (∃ n : Nat, ∃ v : StateT BitStream Option T, ∃ v' : T × BitStream, prob_while_cut cond body n a = v ∧ v s = some v' ∧ ¬ cond v'.1)
  then prob_while_cut cond body (minimal (λ n : Nat =>  ∃ v : StateT BitStream Option T, ∃ v' : T × BitStream, prob_while_cut cond body n a = v ∧ v s = some v' ∧ ¬ cond v'.1)) a
  else none

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  try
    let v ← body
    prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v
  catch m => throw m

-- Sample from [0..2^k - 1]

def uniformP2 (k : Nat) : RandomM Nat := do
  if k = 0 then return 0
  else
    let flip ← Coin
    let v ← uniformP2 (k - 1)
    return (v + if flip then 2 ^ (k - 1) else 0)

-- Sample from [0..n)
noncomputable def uniform (n : Nat) : RandomM Nat := do
  prob_until (uniformP2 (log 2 n + 1)) (λ x : Nat => x < n)

noncomputable def bernoulli (r : Rat) : RandomM Bool := do
  if r < 0 || r > 1 then throw "Argument for Bernoulli not in range"
  let d ← uniform r.den
  return d < r.num

noncomputable def bernoulli_exp_neg_loop1 (gamma : Rat) (K : Bool × Nat) : RandomM (Bool × Nat) := do
  let A ← bernoulli (gamma / (K.2))
  return (A, K.2 + 1)

noncomputable def bernoulli_exp_neg_le1 (gamma : Rat) : RandomM Bool := do
  let r ← prob_while (λ K : Bool × Nat => K.1) (bernoulli_exp_neg_loop1 gamma) (true,1)
  return r.1

noncomputable def bernoulli_exp_neg_loop2 (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  else
    let B ← bernoulli_exp_neg_le1 (-1)
    let R ← bernoulli_exp_neg_loop2 (iter - 1)
    return (B && R)

noncomputable def bernoulli_exp_neg (gamma : Rat) : RandomM Bool := do
  if 0 ≤ gamma && gamma <= 1
  then bernoulli_exp_neg_le1 gamma
  else
    let B ← bernoulli_exp_neg_loop2 (floor gamma)
    if B then bernoulli_exp_neg_le1 (gamma - floor gamma) else return false

noncomputable def laplace_loop1 (t : Nat) : RandomM (Nat × Bool) := do
  let U ← uniform t
  let D ← bernoulli_exp_neg (U / t)
  return (U,D)

noncomputable def laplace_loop2 (K : Bool × Nat) : RandomM (Bool × Nat) := do
  let A ← bernoulli_exp_neg_le1 (-1)
  return (A, K.2 + 1)

noncomputable def laplace_body (t s : Nat) : RandomM (Bool × Nat × Int) := do
  let r ← prob_until (laplace_loop1 t) (λ x : Nat × Bool => x.2)
  let U := r.1
  let r ← prob_while (λ K : Bool × Nat => K.1) laplace_loop2 (true,1)
  let V := r.2
  let X := U + t * V
  let Y := floor (X / s)
  let B ← bernoulli 0.5
  let B' := if B then 1 else 0
  let Z := (1 - 2 * B') * Y
  return (B,Y,Z)

noncomputable def laplace (t s : Nat) : RandomM Int := do
  let r ← prob_until (laplace_body t s) (λ x : Bool × Nat × Int => ¬ x.1 || x.2.1 ≠ 0)
  return r.2.2

noncomputable def gaussian_loop (sigmasquared : Rat) (t : Nat) : RandomM (Int × Bool) := do
  let Y ← laplace t 1
  let C ← bernoulli_exp_neg ((abs Y - sigmasquared / t)^2 / (2 * sigmasquared))
  return (Y,C)

noncomputable def gaussian (sigma : Rat) : RandomM Int := do
  let t : Nat := floor sigma + 1
  let r ← prob_until (gaussian_loop (sigma^2) t) (λ x : Int × Bool => x.2)
  return r.1

-- Trying out reasoning

theorem uniformP2_correct (k : Nat) (n : Nat) (_ : 0 ≤ n ∧ n < 2 ^ k) :
  Prob.volume { s : BitStream | (uniformP2 k) = some n } = 1 / 2 ^ k := by
    revert n
    induction k
    . intro n H
      simp at H
      subst H
      simp
      unfold μ
      rw [Measure.ofAddContent_eq]
      unfold uniformP2
      simp
      sorry
      sorry -- MeasurableSet
    . rename_i k iH
      intro n DOM
      have HCase : n < 2 ^ k ∨ exists m : Nat, m < 2 ^ k ∧ n = 2 ^ k + m := sorry
      cases HCase
      . rename_i CONS
        have RES := iH n
        simp at RES
        have RES2 := RES CONS
        sorry -- probability to be in lower range is 1/2
        -- Coin must be independent from the lower bits
      . rename_i CONS
        cases CONS
        rename_i m CONS2
        cases CONS2
        rename_i left right
        have RES := iH m
        simp at RES
        have RES2 := RES left
        sorry


end Hurd
