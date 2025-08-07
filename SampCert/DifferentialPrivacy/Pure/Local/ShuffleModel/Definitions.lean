import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward

namespace SLang


def UniformSample' (n : PNat) : SLang (Fin n) := do
  let r ← UniformSample n
  return (r : Fin n)

lemma fin_helper (x : Nat)(n : PNat) : x = x % n ↔  x < n := by
  constructor
  intro h
  rw [h]
  apply Nat.mod_lt
  simp
  intro h
  exact Eq.symm (Nat.mod_eq_of_lt h)

lemma  UniformSample'_eq_UnformSample (n : PNat)(x : Fin n) : UniformSample' n x = UniformSample n x := by
  unfold UniformSample'
  conv =>
    lhs
    simp [pure, bind]
  rw [tsum_eq_single x.val]
  simp_all only [Fin.cast_val_eq_self, ↓reduceIte, Fin.is_lt, UniformSample_apply, one_div]
  intro b' a
  simp_all only [ne_eq, ite_eq_right_iff]
  intro a_1
  subst a_1
  simp_all only [Fin.val_natCast]
  rw [Not] at a
  have h : b' < n → False := by
    intro h1
    rw [← fin_helper] at h1
    apply a
    exact h1
  rw [← Not] at h
  rw [Nat.not_lt_eq] at h
  simp_all only [imp_false, ge_iff_le, UniformSample_apply_out]

lemma UniformSample'_uniform (n : PNat) (x: Fin n) : UniformSample' n x = 1 / n := by
  rw [UniformSample'_eq_UnformSample]
  exact UniformSample_apply n x.val (Fin.is_lt x)


lemma UniformSample'_norms (n : PNat) : HasSum (UniformSample' n) 1 := by
  rw [UniformSample']
  simp
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  set f : ℕ → Fin n := fun a => a
  set p : SLang ℕ := UniformSample n
  have h1: push_forward p f = (fun (b : Fin n) => ∑' (a : ℕ), if f a = b then p a else 0) := by
    rfl
  rw [←push_forward_prob_is_prob p f]
  simp [h1]
  have h2 (b : Fin n.val) (a : Nat): (if b = f a then p a else 0) = if f a = b then p a else 0 := by aesop
  conv =>
    enter [2, 1, z, 1, a]
    rw [←h2]
  simp [p]



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


#check Shuffler

def ShuffleModel(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) := do
  let l ← RandomizedResponse.RRSample query num den h l
  let b ← Shuffler l
  return b

#check ShuffleModel

lemma Shuffle_norms [LawfulMonad SLang] {α : Type}(l: List α): HasSum (Shuffler l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold Shuffler
  rename_i inst
  simp_all only [bind, PNat.add_coe, PNat.val_ofNat, pure, pure_bind, Array.toList_eq, bind_apply, pure_apply,
    mul_ite, mul_one, mul_zero]
  unfold probBind
  simp [pure, bind]
  set
  sorry


lemma ShuffleModel_norms [LawfulMonad SLang] (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) :
HasSum (ShuffleModel query num den h l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold ShuffleModel
  simp [pure,bind]
  unfold RandomizedResponse.RRSample
  rename_i inst
  simp_all only [bind, pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
  sorry


def ShuffleModel_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨ShuffleModel query num den h l ,ShuffleModel_PMF_helper query num den h l⟩

theorem Shuffle_is_DP (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) :
DP_withUpdateNeighbour (ShuffleModel_PMF query num den h) (Real.log ((2⁻¹ + ↑num / ↑↑↑den) / (2⁻¹ - ↑num / ↑↑↑den))) := by sorry
