import Mirror.H1
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Rat.Basic

open Classical Set Function ProbabilityTheory Nat

section Hurd

variable {T U : Type}
variable [MeasurableSpace T] [MeasurableSpace U]

def Hurd (T: Type) : Type := BitStream → Option (T × BitStream)

instance H : Monad Hurd where
  pure := λ { T : Type } => λ x : T => λ s : BitStream => some (x,s)
  bind := λ { T U : Type } => λ f : Hurd T => λ g : T → Hurd U => λ s : BitStream =>
    let res := f s ;
    match res with
    | none => none
    | some (v,s') => (g v) s'

theorem Pure1 (x : T) (s : BitStream) (v : T × BitStream) (_ : H.pure x s = some v) : v.1 = x := sorry

def Coin : Hurd Bool := λ s : BitStream => some (s 0, λ n : Nat => s (n + 1))

def prob_while_cut (cond : T → Bool) (body : T → Hurd T) (n : Nat) (a : T) : Hurd T :=
  match n with
  | zero => return a
  | succ n => if cond a then
    do let v ← body a
       prob_while_cut cond body n v
    else return a

-- Smallest n that satisfies f
noncomputable def minimal (f : Nat → Bool) : Nat := sorry

noncomputable def prob_while (cond : T → Bool) (body : T → Hurd T) (a : T) : Hurd T :=
  λ s : BitStream => do
  if (∃ n : Nat, ∃ v : T × BitStream, prob_while_cut cond body n a s = some v ∧ ¬ cond (v.1))
  then prob_while_cut cond body (minimal (λ n : Nat =>  ∃ v : T × BitStream, prob_while_cut cond body n a s = some v ∧ ¬ cond (v.1))) a s
  else none

noncomputable def prob_until (body : Hurd T) (cond : T → Bool) : Hurd T :=
  λ s : BitStream => do
    let v ← body s
    prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v.1 s

-- Sample from [0..2^k - 1]

def uniformP2 (k : Nat) : Hurd Nat := do
  if k = 0 then return 0
  else
    let flip ← Coin
    let v ← uniformP2 (k - 1)
    return (v + if flip then 2 ^ (k - 1) else 0)

-- Sample from [0..n)
noncomputable def uniform (n : Nat) : Hurd Nat := do
  prob_until (uniformP2 (log 2 n + 1)) (λ x : Nat => x < n)

noncomputable def bernoulli (r : Rat) : Hurd Bool := do
  let d ← uniform r.den
  return d < r.num

noncomputable def bernoulli_exp_neg_loop1 (gamma : Rat) (K : Bool × Nat) : Hurd (Bool × Nat) := do
  let A ← bernoulli (gamma / (K.2))
  return (A, K.2 + 1)

noncomputable def bernoulli_exp_neg_le1 (gamma : Rat) : Hurd Bool := do
  let r ← prob_while (λ K : Bool × Nat => K.1) (bernoulli_exp_neg_loop1 gamma) (true,1)
  return r.1

noncomputable def bernoulli_exp_neg_loop2 (iter : Nat) : Hurd Bool := do
  if iter = 0 then return true
  else
    let B ← bernoulli_exp_neg_le1 (-1)
    let R ← bernoulli_exp_neg_loop2 (iter - 1)
    return (B && R)

noncomputable def bernoulli_exp_neg (gamma : Rat) : Hurd Bool := do
  if 0 ≤ gamma && gamma <= 1
  then bernoulli_exp_neg_le1 gamma
  else
    let B ← bernoulli_exp_neg_loop2 (floor gamma)
    if B then bernoulli_exp_neg_le1 (gamma - floor gamma) else return false

noncomputable def laplace_loop1 (t : Nat) :  Hurd (Nat × Bool) := do
  let U ← uniform t
  let D ← bernoulli_exp_neg (U / t)
  return (U,D)

noncomputable def laplace_loop2 (K : Bool × Nat) : Hurd (Bool × Nat) := do
  let A ← bernoulli_exp_neg_le1 (-1)
  return (A, K.2 + 1)

noncomputable def laplace_body (t s : Nat) : Hurd (Bool × Nat × Int) := do
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

noncomputable def laplace (t s : Nat) : Hurd Int := do
  let r ← prob_until (laplace_body t s) (λ x : Bool × Nat × Int => ¬ x.1 || x.2.1 ≠ 0)
  return r.2.2

noncomputable def gaussian_loop (sigmasquared : Rat) (t : Nat) : Hurd (Int × Bool) := do
  let Y ← laplace t 1
  let C ← bernoulli_exp_neg ((abs Y - sigmasquared / t)^2 / (2 * sigmasquared))
  return (Y,C)

noncomputable def gaussian (sigma : Rat) : Hurd Int := do
  let t : Nat := floor sigma + 1
  let r ← prob_until (gaussian_loop (sigma^2) t) (λ x : Int × Bool => x.2)
  return r.1

end Hurd
