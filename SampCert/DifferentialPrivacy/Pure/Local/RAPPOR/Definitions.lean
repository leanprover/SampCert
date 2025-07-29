import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.PMFProperties

namespace RAPPOR

open RandomizedResponse SLang

/- Definition of One-Time Basic RAPPOR. -/

/- One-hot encoding of a vector-/
@[simp]
def one_hot {T : Type} (n : Nat) (query : T -> Fin n) (v : T) : List Bool := List.ofFn (fun i => query v = i)

/- One-Time Basic RAPPOR for a single user.
   We follow the description in "LDP Protocols for Frequency Estimation"
   by Wang et al.
   The rational privacy parameter lambda = num/den relates to the parameter
   f in the paper via the equation lambda = 1/2 (1 - f).
-/

def RAPPORSingleSample {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : T) : SLang (List Bool) := do
  RRSamplePushForward num den h (one_hot n query v)

/- One-Time Basic RAPPOR for a dataset of users. -/
def RAPPORSample {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) : SLang (List (List Bool)) := do
  v.mapM (fun x => RAPPORSingleSample n query num den h x)

end RAPPOR
