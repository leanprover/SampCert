import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
/-import SampCert.DifferentialPrivacy.Local.MultiBernoulli -/

namespace RandomizedResponse

open SLang

/- Arithmetic lemma for the next definition. -/
lemma arith_0 (num : Nat) (den : PNat) (_ : 2 * num < den): den - 2*num ≤ 2 * den := by
  simp_all only [tsub_le_iff_right]
  linarith

/- RRSinglePushForward performs the Randomized Response algorithm, but
   associates each user with their private response.
-/
 def RRSinglePushForward (num : Nat) (den : PNat) (h: 2 * num < den) (l : Bool) : SLang Bool := do
  let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
  return Bool.xor (l) r

/- Single-user Randomized Response with a gven query. -/
def RRSingleSample  {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) : SLang Bool := do
  RRSinglePushForward num den h (query l)

/- Extension of Randomized Response to a dataset by use of monadic map. -/
def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : SLang (List Bool) := do
 l.mapM (fun x => RRSingleSample query num den h x)

/- The next definition is used in RAPPOR. -/
def RRSamplePushForward (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool) : SLang (List Bool) := do
  l.mapM (fun x => RRSinglePushForward num den h x)

end RandomizedResponse
