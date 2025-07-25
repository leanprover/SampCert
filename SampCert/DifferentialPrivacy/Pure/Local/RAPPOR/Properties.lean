import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.PMFProperties
import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Definitions

namespace RAPPOR

lemma RAPPORSingleSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : T) :
  HasSum (RAPPORSingleSample n query num den h v) 1 := by
    rw [RAPPORSingleSample]
    apply RRSamplePushForward_PMF_helper

lemma RAPPORSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) :
  HasSum (RAPPORSample n query num den h v) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    unfold RAPPORSample
    apply Norm_func_norm_on_list
    intro a
    rw [← Summable.hasSum_iff ENNReal.summable]
    apply RAPPORSingleSample_PMF_helper query num den h a

def RAPPORSample_PMF [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) : PMF (List (List Bool)) :=
  ⟨RAPPORSample n query num den h v, RAPPORSample_PMF_helper query num den h v⟩

end RAPPOR
