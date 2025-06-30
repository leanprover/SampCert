import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert

/- For now, we assume that our databases consist of a single element of type T,
   representing a single user (i.e., a database of size one) -/

/- Implementation of randomized response for a single user with rational parameter 0 ≤ lambda ≤ 1/2 -/

def RRRandomizer (query : T -> Bool) (l : T) (num : Nat) (den : PNat) (h: 2 * num < den) : SLang Bool := do
  let result1 ← SLang.BernoulliSample (2 * num + den) (2 * den) (by
    linarith) -- note (2 * num + den) / (2 * den) = 1/2 + num/den
  match result1 with
   | true => return (query l) -- happens with probability (1/2 + num/den)
   | false => return ¬(query l) -- happens with probability (1/2 - num/den)


lemma RRRandomizerpmf_lemma (query : T -> Bool) (l : T) (num : Nat) (den : PNat) (h : 2 * num < den):
  HasSum (RRRandomizer query l num den h) 1 := by
  simp [RRRandomizer]
  simp [(Summable.hasSum_iff ENNReal.summable), tsum_bool, add_tsub_cancel_iff_le]
  aesop
  { sorry }
  { sorry }

def RRRandomizerPMF (query : List T -> Bool) (l : List T) (num : Nat) (den : PNat) (h: 2 * num < den) : PMF Bool :=
  ⟨RRRandomizer query l num den h, RRRandomizerpmf_lemma query l num den h⟩

/-- THERE ARE STILL ISSUES BELOW THIS LINE. DO NOT EDIT YET. -/

/- Implementation of Randomized Response. Applies local randomizer to each user's data. -/
def RandomizedResponseSample (query: T -> Bool) (l : List T) (num : Nat) (den : PNat) (h: 2 * num < den) : (List (SLang Bool)) :=
  do List.map (λ l => RRRandomizer query l num den h) l

/-- lemma DP_RandomizedResponse (query: T -> Bool) (l : List T) (num : Nat) (den : PNat) (h: 2 * num < den) :
  sorry --/

/- Here is a special case of Randomized Response, with parameter 1/4-/

def CoinFlipSample (query : T -> Bool) (l : T): SLang (Bool):= do
  RRRandomizer query l 1 4 (by decide) /- Randomized Response with parameter 1/4 -/

lemma coinflippmf_lemma (query: T -> Bool) (l: T) : HasSum (CoinFlipSample query l) 1 :=
  RRRandomizerpmf_lemma query l 1 4 (by decide)

def CoinFlipPMF (query : T -> Bool) (l : T) : PMF Bool :=
  ⟨CoinFlipSample query l, coinflippmf_lemma query l⟩
