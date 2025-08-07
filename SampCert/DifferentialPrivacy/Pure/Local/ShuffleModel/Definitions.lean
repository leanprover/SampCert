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

   b := a.swap ⟨i, by aesop; exact Membership.get_elem_helper h rfl⟩ ⟨j, by
   aesop
   have h1: j ≤ i := by
    rw [@Fin.le_iff_val_le_val]
    norm_num
    aesop
    have h1: j.val < i.toPNat' + 1 := j.2
    aesop
    rw[← Nat.lt_add_one_iff]
    exact h1
    linarith[h.1]

   have h2: i < l.length := by exact Membership.get_elem_helper h rfl
   exact Nat.lt_of_le_of_lt h1 (by aesop)
   ⟩
  return b.toList

def ShuffleModel(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ← Shuffler l
  return b

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


lemma ShuffleModel_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) :
  HasSum (ShuffleModel query num den h l) 1 := by sorry

def ShuffleModel_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨ShuffleModel query num den h l ,ShuffleModel_PMF_helper query num den h l⟩

theorem Shuffle_is_DP (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) :
DP_withUpdateNeighbour (ShuffleModel_PMF query num den h) (Real.log ((2⁻¹ + ↑num / ↑↑↑den) / (2⁻¹ - ↑num / ↑↑↑den))) := by sorry
