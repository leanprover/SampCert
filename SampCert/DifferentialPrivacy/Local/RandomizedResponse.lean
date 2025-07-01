import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert

/- For now, we assume that our databases consist of a single element of type T,
   representing a single user (i.e., a database of size one) -/

/- Implementation of randomized response for a single user with rational parameter 0 ≤ lambda ≤ 1/2 -/

/- def RRRandomizer (query : T -> Bool) (l : T) (num : Nat) (den : PNat) (h: 2 * num < den) : SLang Bool := do
  let result1 ← SLang.BernoulliSample (2 * num + den) (2 * den) (by
    linarith) -- note (2 * num + den) / (2 * den) = 1/2 + num/den
  match result1 with
   | true => return (query l) -- happens with probability (1/2 + num/den)
   | false => return ¬(query l) -- happens with probability (1/2 - num/den)

-/

/- What return actually does is that it returns that Dirac distribution that is either all true or all false...
   So this is wrong?
-/

/- Note that this doesn't work: -/

/- def RRRandomizertest (query : T -> Bool) (l : T) (num : Nat) (den : PNat) (h: 2 * num < den) : Bool -> ENNReal :=
  fun b =>
    let result1 := SLang.BernoulliSample (2 * num + den) (2 * den) (by
    linarith)
    match b with
    | true => query l
    | false => ¬ query l

-/

/- lemma RRRandomizerpmf_lemma (query : T -> Bool) (l : T) (num : Nat) (den : PNat) (h : 2 * num < den):
  HasSum (RRRandomizer query l num den h) 1 := by
  simp [RRRandomizer]
  simp [(Summable.hasSum_iff ENNReal.summable), tsum_bool, add_tsub_cancel_iff_le]
  aesop
  { sorry }
  { sorry }

def RRRandomizerPMF (query : T -> Bool) (l : T) (num : Nat) (den : PNat) (h: 2 * num < den) : PMF Bool :=
  ⟨RRRandomizer query l num den h, RRRandomizerpmf_lemma query l num den h⟩

-/

/-- THERE ARE STILL ISSUES BELOW THIS LINE. DO NOT EDIT YET. -/

/- def mapper (n : Nat) (num : Nat) (den : PNat) (h : 2 * num < den) (_ : Fin n) : SLang Bool := do
  let result1 ← SLang.BernoulliSample (2 * num + den) (2 * den) (by linarith)
  return result1

def matcher (query : T -> Bool) (val_prob : T × Bool): Bool := do
  let a ← val_prob.2


/- Implementation of Randomized Response. Applies local randomizer to each user's data. -/
def RandomizedResponseSample (query: T -> Bool) (l : List T) (num : Nat) (den : PNat) (h: 2 * num < den) : (SLang (List Bool)) := do
  let a ← List.replicate l.length 0
  let a ← List.map (SLang.BernoulliSample (2 * num + den) (2 * den) (by linarith)) a
  let a ← List.zip l a
  let a ← List.map (matcher query) a
  return a


/-- lemma DP_RandomizedResponse (query: T -> Bool) (l : List T) (num : Nat) (den : PNat) (h: 2 * num < den) :
  sorry --/

/- Here is a special case of Randomized Response, with parameter 1/4-/ -/

def count_differences {T : Type} [DecidableEq T]: List T -> List T -> ℕ
    | [], l => l.length
    | l, [] => l.length
    | x :: xs, y :: ys =>
      if x = y then
        count_differences xs ys
      else 1 + count_differences xs ys

noncomputable def output_probabilities {T : Type} [DecidableEq T] (num : ℕ) (den : PNat) (_ : 2 * num < den) (l : List T) : List T → ENNReal :=
  fun l' =>
    let diff := count_differences (List.map (fun x => x) l) l'
    let same := l.length - diff
    (((2 * num + den) / (2 * den)) ^ diff * ((den - 2 * num) / (2 * den)) ^ same : ENNReal)

noncomputable def output_probabilities_SLang {T : Type} [DecidableEq T] (num : ℕ) (den : PNat) (_ : 2 * num < den) (l : List T) : SLang (List T) :=
  fun l' =>
    let diff := count_differences l l'
    let same := l.length - diff
    ENNReal.ofReal (((2 * num + den : ℝ) / (2 * den : ℝ)) ^ diff * ((den - 2 * num : ℝ) / (2 * den : ℝ)) ^ same)

noncomputable def RandomizedResponseSample {T : Type} [DecidableEq T] (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨output_probabilities num den h (List.map query l), by sorry⟩

lemma log_arith: Real.log 3 ≥ 0 := Real.log_nonneg (by linarith)

lemma RRPureDP {T : Type} [DecidableEq T] (query : T -> Bool) (l : List T) (num : Nat) (den : PNat) (h: 2 * num < den): SLang.PureDP (RandomizedResponseSample query num den h) ((Real.log 3).toNNReal) :=
  by
    rw[SLang.PureDP]
    rw[SLang.DP]
    intro l₁ l₂ hl₁l₂ S
    /- Study SampCert PureDP proofs -/
    sorry



/- def CoinFlipSample (query : T -> Bool) (l : T): SLang (Bool):= do
  RRRandomizer query l 1 4 (by decide) /- Randomized Response with parameter 1/4 -/

def CoinFlipPMF (query : T -> Bool) (l : T) : PMF Bool :=
  ⟨CoinFlipSample query l, RRRandomizerpmf_lemma query l 1 4 (by decide)⟩

/- need randomized response as a mechanism... -/
-/
