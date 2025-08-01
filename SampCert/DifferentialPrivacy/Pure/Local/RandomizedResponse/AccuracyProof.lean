import SampCert
import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions

open SLang
open PMF
open RandomizedResponse

-- UNDER CONSTRUCTION --
def toSingletonLists {α : Type u} (l : List α) : List (List α) :=
  l.map (fun x => [x])


def sum_list (Y : List ℕ) := Y.foldl (· + ·) 0

noncomputable def coeff {T : Type} (X : List T) (num : Nat) (den : PNat) : ℝ :=
  (1.0 / (X.length : ℝ)) * ((den : ℝ) / (2.0 * (num : ℝ)))

noncomputable def constants {T : Type} (X : List T) (num : Nat) (den : PNat) : ℝ :=
  (- (X.length) / 2) + (num * X.length) / den

def applying_RR_individually {T : Type} (query: T -> Bool) (X : List T) (num : Nat) (den : PNat) (h : 2 * num < den) : List (SLang Bool) :=
  X.map (fun x => RRSingleSample query num den h x)


def sumBernoulli (xs : List (SLang Bool)) : SLang Nat :=
  xs.foldlM (fun sum x => do
    let b ← x
    return sum + if b then 1 else 0
  ) 0

def addMulRealToRV (Y : SLang Nat) (R : Real) (S: Real): SLang Real := do
  let n ← Y            -- Sample a Nat from Y
  return S * ((n : Real) + R) -- Convert to Real and add R
/-

variables {α : Type*} [AddMonoid α]

instance : AddMonoid (List α) where
  nsmul     := fun n l => List.join (List.replicate n l)
  add       := (· ++ ·)
  zero      := []
  add_assoc := List.append_assoc
  zero_add  := List.nil_append
  add_zero  := List.append_nil



noncomputable def pmf.add (X Y : PMF α) : PMF α :=
  X.bind (λ a => Y.map (λ b => a + b))

noncomputable def pmf.sum_list : List (PMF α) → PMF α
| []      => PMF.pure 0
| (x::xs) => pmf.add x (pmf.sum_list xs)
-/

def p {T : Type} (query: T -> Bool) (X : List T) (num : Nat) (den : PNat) (h : 2 * num < den) : ℚ :=
  let bool_lst := X.map query
  let true_count := (bool_lst.filter (fun b => b)).length
  (true_count) / X.length


noncomputable def unbiased_estimator {T : Type} (query: T -> Bool) (X : List T) (num : Nat) (den : PNat) (h : 2 * num < den):=
  let coef := coeff X num den
  let cons := constants X num den
  let s := applying_RR_individually query X num den h
  let sum_of_ys := sumBernoulli s
  let p_estimate := addMulRealToRV sum_of_ys cons coef
  p_estimate
