import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert

lemma arith_0 (num : Nat) (den : PNat) (_ : 2 * num ≤ den): den - 2*num ≤ 2 * den := by
  simp_all only [tsub_le_iff_right]
  linarith

def RRSingleSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
/- RRSingleSample takes in a single user and produces a sample according to the distribution
   induced by the user's actual response.
   If the user's actual response to the query is "true", then RRSingleSample samples "true"
   with probability 1/2 + num/den. If the user's actual response to the query is "false," then RRSingleSample
   samples true with probability 1/2 - num/den.
-/
  match query l with
  | true => let r ← SLang.BernoulliSample (den + 2 * num) (2 * den) (by linarith)
            return r
  | false => let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
              return r

def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample on an entire dataset. -/
 l.mapM (fun x => RRSingleSample query num den h x)

/- At this point, we should be set to prove that RRSample is normalized and that it is
   differentially private. The definition is computable, as we need. -/
