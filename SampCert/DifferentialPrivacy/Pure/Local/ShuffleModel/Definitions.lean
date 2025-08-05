import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import Mathlib.Probability.ProbabilityMassFunction.Basic


namespace SLang

open SLang
open RandomizedResponse

def Shuffler {α: Type}(l:List α) := do
  let mut a := l.toArray
  let mut b : Array α := Array.empty
  for h: i in [1:a.size] do
   let j ← UniformSample (Nat.toPNat' i+1)

   b := a.swap ⟨i, by aesop; exact Membership.get_elem_helper h rfl⟩ ⟨j, by sorry⟩
  return b.toList

def ShuffleModel(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ←  Shuffler l
  return b


lemma ShuffleModel_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) :
  HasSum (ShuffleModel query num den h l) 1 := by sorry

def ShuffleModel_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨ShuffleModel query num den h l ,ShuffleModel_PMF_helper query num den h l⟩

theorem ShuffleDP (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) :
DP_withUpdateNeighbour (ShuffleModel_PMF query num den h) (Real.log ((2⁻¹ + ↑num / ↑↑↑den) / (2⁻¹ - ↑num / ↑↑↑den))) := by sorry
