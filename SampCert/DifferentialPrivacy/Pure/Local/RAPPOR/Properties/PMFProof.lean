import SampCert.DifferentialPrivacy.Pure.Local.RAPPOR.Basic

namespace RAPPOR

open SLang
open RandomizedResponse
/- In this file, we show normalization for the One-Time Basic RAPPOR Algorithm.
-/

/- Normalization of the single-user RAPPOR, which essentially relies on the normalization property
   of randomized response. -/
lemma RAPPORSingleSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : T) :
  HasSum (RAPPORSingleSample n query num den h v) 1 := by
    rw [RAPPORSingleSample]
    apply RRSamplePushForward_PMF_helper

/- Extension to the multi-user RAPPOR, which follows from our normalization lemma. -/
lemma RAPPORSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) :
  HasSum (RAPPORSample n query num den h v) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    unfold RAPPORSample
    apply Norm_func_norm_on_list
    intro a
    rw [← Summable.hasSum_iff ENNReal.summable]
    apply RAPPORSingleSample_PMF_helper query num den h a

/- Promotion of RAPPOR to a PMF-/
def RAPPORSample_PMF [LawfulMonad SLang] {T : Type} (n : Nat) (query: T -> Fin n) (num : Nat) (den : PNat) (h: 2 * num < den) (v : List T) : PMF (List (List Bool)) :=
  ⟨RAPPORSample n query num den h v, RAPPORSample_PMF_helper query num den h v⟩
