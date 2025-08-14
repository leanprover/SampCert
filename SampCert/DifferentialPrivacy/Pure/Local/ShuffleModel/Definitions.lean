import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
namespace SLang


def Shuffler {α: Type}(l:List α) := do
match l with
| [] => pure []
| hd::tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd
#check Shuffler





def BinomialSample (seed: MultiBernoulli.SeedType)(n:PNat) := do
  let seeds := List.replicate n seed
  let list ← MultiBernoulli.MultiBernoulliSample (seeds)
  let k := List.count true list
  return k












theorem BinomialSample_kprob (seed: MultiBernoulli.SeedType) (n : PNat) (k : Nat) :
  BinomialSample seed n k = ((n: Nat).choose k) * ((num / den) ^ k) * ((1 - (num / den)) ^ (n - k)) := by
  rw[BinomialSample]
  simp
  unfold MultiBernoulli.MultiBernoulliSample
  simp [pure, bind]

  sorry





/- This is the Shuffle Model. -/
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
  sorry

lemma one_step {α: Type}[BEq α](hd: α)(tl: List α)(l: List α)(h: List.isPerm (hd::tl) l): Shuffler (hd::tl) l = Shuffler tl (l.erase hd) / (tl.length+1) := by
  unfold Shuffler
  simp[probBind,pure,pure_apply]
  have h: (List.toArray (hd::tl)).size = (List.toArray tl).size+1 := by
    simp
  rename_i inst h_1
  rw[tsum_eq_single (List.toArray l)]
  rw[tsum_eq_single (List.toArray l)]
  simp
  unfold UniformSample'
  simp
  aesop








lemma Shuffle_permutes {α: Type} [BEq α] (l₁ l₂: List α)(hlen: n = l₁.length)(hlen2: n = l₂.length)(h: List.isPerm l₁ l₂): Shuffler l₁ l₂ = 1/Nat.factorial n := by
  induction l₁ generalizing l₂ n with
  | nil =>
    simp [List.isPerm] at h
    have h1: l₂ = [] := by sorry
    subst h1
    sorry
  | cons hd tl ih =>
    simp [List.isPerm] at h
    have h1: Shuffler tl (l₂.erase hd) = 1 / (tl.length).factorial := by
      rw [ih (l₂.erase hd)]
      rfl
      have h2: tl.length = n - 1 := by simp[hlen]
      rw [h2]
      have h3: (l₂.erase hd).length = l₂.length - 1 := by sorry
      rw [h3]
      sorry
      exact h.right
    rw[one_step]
    rw[ih]



 /- induction n generalizing l₁ l₂
  case zero =>
    simp
    symm at hlen
    rw[List.length_eq_zero] at hlen
    symm at hlen2
    rw[List.length_eq_zero] at hlen2
    rw[hlen, hlen2]
    simp [Shuffler]
    aesop
    sorry
  case succ x ih =>

    cases h
    case nil =>
      simp at hlen
    case cons hd tl₁ tl₂ h =>
      simp at hlen
      simp at hlen2
      sorry
 -/


/--/
    cases l₁
    case nil =>
      simp at hlen
    case cons hd tl =>
      cases l₂
      case nil =>
        simp at hlen2
      case cons hd2 tl2 =>














lemma ShuffleModel_PMF_helper (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l: List T) :
HasSum (ShuffleModel query num den h l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold ShuffleModel
  simp [pure,bind]
  unfold RandomizedResponse.RRSample
  sorry


def ShuffleModel_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨ShuffleModel query num den h l ,ShuffleModel_PMF_helper query num den h l⟩

theorem Shuffle_is_DP (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) :
DP_withUpdateNeighbour (ShuffleModel_PMF query num den h) (Real.log ((2⁻¹ + ↑num / ↑↑↑den) / (2⁻¹ - ↑num / ↑↑↑den))) := by sorry
