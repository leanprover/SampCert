import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization

namespace SLang


def UniformSample' (n : PNat) : SLang (Fin n) := do
  let r ← UniformSample n
  return (r : Fin n)


def Shuffler {α: Type}(l:List α) := do
  let mut a := l.toArray
  let mut b : Array α := Array.empty
  for h: i in [1:a.size] do
   let j ← UniformSample' (Nat.toPNat' i+1)
   have hj : j < a.size := by
    have hi : j ≤ i := by

   b := a.swap ⟨i, by aesop; exact Membership.get_elem_helper h rfl⟩ ⟨j, by sorry⟩
  return b.toList

def ShuffleModel(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  return Shuffler l

lemma Shuffle_norms [LawfulMonad SLang] {α : Type}(l: List α): HasSum (Shuffler l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold Shuffler
  rename_i inst
  simp_all only [bind, pure, pure_bind, Array.toList_eq, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]

  sorry


lemma ShuffleModel_norms [LawfulMonad SLang] (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) :
HasSum (ShuffleModel query num den h l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold ShuffleModel
  unfold RandomizedResponse.RRSample
  rename_i inst
  simp_all only [bind, pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
  sorry
