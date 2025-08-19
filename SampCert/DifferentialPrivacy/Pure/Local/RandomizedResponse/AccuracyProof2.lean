import SampCert
import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.BasicLemmas

open SLang
open PMF
open RandomizedResponse
open ENNRealLemmas

-- UNDER CONSTRUCTION --

def coeff_1 (num : Nat) (den : PNat) : NNRat := den / (2 * num)
def coeff_2 (num : Nat) (den : PNat) : NNRat := den / (4 * num) + 1/2

/- Given a list of booleans, p_pushforward returns the proportion of "true" responses
-/
def p_pushforward (l : List Bool) : NNRat :=
  let true_count := (l.filter (fun b => b)).length
  (true_count) / l.length

/- Given a list of users and a query, p_actual returns the proportion of "yes" responses
   Our goal is to estimate p_actual. -/
def p_actual {T : Type} (query: T -> Bool) (l : List T) : NNRat :=
  let bool_lst := l.map query
  p_pushforward bool_lst

/- Unbiased estimator-/
def p_estimate {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (l : List T) : SLang NNRat := do
  let randomized ← RRSample query num den h l
  let avg_yes := p_pushforward randomized
  /- now "return avg_yes" would gives a function that, for each NNRat q,
     returns the probability that the proportion of "yes" responses
     after doing randomized response on l is equal to q. -/
  return (coeff_1 num den) * avg_yes - (coeff_2 num den)

lemma RRSample_diff_lengths_simp {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (l : List T) :
  RRSample query num den h l a = (if l.length = a.length then RRSample query num den h l a else 0) := by
  split
  next h_1 => simp
  next h_1 =>
    rw [RRSample_diff_lengths]
    simp
    exact h_1

lemma estimator_unbiased {T : Type} (query : T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (l : List T) :
  ∑' (q : NNRat), (p_estimate query num den h l q) * (q : NNReal) = (p_actual query l : NNReal) := by
  simp [p_estimate, p_actual]
  have h1 (q : NNRat): (∑' (a : List Bool), if q = (coeff_1 num den) * p_pushforward a - (coeff_2 num den) then RRSample query num den h l a else 0) * (q : NNReal) =
    (∑' (a : List Bool), if q = (coeff_1 num den) * p_pushforward a - (coeff_2 num den) then RRSample query num den h l a * (q : NNReal) else 0) := by
      sorry
  conv =>
    enter [1, 1, q]
    rw [h1]
  rw [@ENNReal.tsum_comm]
  simp_all [ite_not]



  sorry
