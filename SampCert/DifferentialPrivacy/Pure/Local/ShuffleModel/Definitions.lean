import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Properties

namespace SLang

def Shuffler {α: Type}(l:List α) := do
match l with
| [] => pure []
| hd::tl =>
    let len := (hd :: tl).length
    let i : Nat ← UniformSample (Nat.toPNat' len)
    let rest : List α ← Shuffler tl
    return rest.insertNth i hd

#eval List.insertNth 0 1 [2,3]
#eval List.eraseIdx [1,2,3] 0
lemma insertNth_helper {α : Type}(b a_1: List α)(a: Nat)(h: α): b = List.insertNth a h a_1 ↔ a_1 = List.eraseIdx b a := by sorry


lemma Shuffler_empty {α: Type}(l:List α)(h: l = []): Shuffler l [] = 1 := by
  unfold Shuffler
  rw [h]
  simp [pure]



lemma Shuffler_norm [DecidableEq α]{α: Type}(l:List α): HasSum (Shuffler l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  induction l with
  | nil =>
    unfold Shuffler
    simp [pure]
    unfold probPure
    simp
  | cons h t ih =>
    unfold Shuffler
    simp [pure]
    rw [← Summable.hasSum_iff ENNReal.summable]
    rw [Summable.hasSum_iff ENNReal.summable]
    simp
    conv =>
      enter [1,1,b,1,a,2,1,a_1]
      rw [insertNth_helper]
    rename_i α_1 inst
    conv =>
      enter [1, 1, b, 1, a, 2, 1, a_1]
    rw [tsum_add]
    have h (a_1:List α)(b:List α)(a : Nat): (if a_1 = b.eraseIdx a then Shuffler t a_1 else 0) = Shuffler t a_1 := by sorry




def BinomialSample (seed: MultiBernoulli.SeedType)(n:PNat) := do
  let seeds := List.replicate n seed
  let list ← MultiBernoulli.MultiBernoulliSample (seeds)
  let k := List.count true list
  return k

theorem BinomialSample_norms [LawfulMonad SLang] (seed : MultiBernoulli.SeedType) (n : PNat) :
  HasSum (BinomialSample seed n) 1 := by
  rw [BinomialSample]
  simp
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  have h: (push_forward (MultiBernoulli.MultiBernoulliSample (List.replicate (↑n) seed))
        (fun (a : List Bool) => (List.count true a))) = (fun (b : Nat) =>
        (∑' (a : List Bool), if b = List.count true a then MultiBernoulli.MultiBernoulliSample
        (List.replicate (↑n) seed) a else 0)) := by
          unfold push_forward
          rfl
  rw [← h]
  rw [push_forward_prob_is_prob]
  simp [MultiBernoulli.MultiBernoulliSample_normalizes]

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

lemma contains_idx {α: Type}[BEq α](l: List α)(a: α)(h: l.contains a): ∃i: Fin l.length, l[i] = a := by sorry

lemma insertNth_eq_iff {α : Type} [DecidableEq α]
  {l : List α} (a : Nat){x : α} {l' : List α}(h: l = l'.insertNth a x):
  l = l'.insertNth a x ↔ l' = l.eraseIdx a ∧ l[a]'(sorry) = x := sorry

lemma erase_eq_eraseIdx [BEq α]{l : List α} {i : Fin l.length} {x : α} (h : l[i] = x) : l.eraseIdx i = l.erase x := by sorry
lemma Shuffle_permutes {α: Type} [DecidableEq α][BEq α] (n: Nat)(l₁ l₂: List α)(hlen1:  l₁.length = n)(hlen2: l₂.length = n)(h: List.isPerm l₁ l₂): Shuffler l₁ l₂ = 1/Nat.factorial n := by
  induction l₁ generalizing l₂ n
  simp at hlen1
  rw[symm hlen1]
  simp
  unfold Shuffler
  simp
  symm at hlen1
  rw[hlen1] at hlen2
  rw[List.length_eq_zero] at hlen2
  exact hlen2

  case cons hd tl ih =>
    unfold Shuffler
    simp
    simp at hlen1
    rw[symm hlen1]
    unfold List.isPerm at h
    rw[Bool.and_eq_true] at h
    cases h
    rename_i left right
    have h := contains_idx l₂ hd left
    cases h
    rename_i j ht
    conv =>
      enter[1,1,a,2]
      rw[tsum_eq_single (l₂.eraseIdx a) (by
        intro l h
        simp
        intro h1
        rw[insertNth_eq_iff] at h1
        cases h1
        rename_i left2 right2
        simp at h
        contradiction
        exact h1
       )]
      rfl
    simp
    rw[tsum_eq_single j.val (by
    intro a h
    simp
    intro h1

    )]
    have h2: l₂ = List.insertNth j hd (l₂.eraseIdx j) := by sorry
    rw[if_pos]

    rw[ih (n-1) (l₂.eraseIdx ↑j) (by simp[symm hlen1]) (by rw[symm hlen2, List.length_eraseIdx];simp) (by rw[erase_eq_eraseIdx ht];exact right)]
    rw[UniformSample_apply]
    rw[hlen1]
    rw[inv_eq_one_div]

    simp
    have nonzero: n > 0 := by rw[symm hlen1]; linarith
    rw[if_pos nonzero]
    rw[← ENNReal.mul_inv]
    rw[inv_inj]
    sorry
    left
    simp
    linarith

    left
    simp
    /-rw[Nat.mul_factorial_pred nonzero]-/
    rw[hlen1]
    rw[symm hlen2]
    have nonzero: n > 0 := by rw[symm hlen1]; linarith
    rw[symm hlen2] at nonzero
    simp[nonzero]
    exact h2


/--/
    unfold List.isPerm at h
    rw[Bool.and_eq_true] at h
    cases h
    rename_i left right
    have h := contains_idx l₂ hd left
    cases h
    rename_i j ht


    conv =>
      enter[1,1,a,2]
      rw[tsum_eq_single (List.eraseIdx l₂ j ) (by
      intro b' h
      simp


      have h2: b' = List.eraseIdx (List.insertNth j hd b') j := by rw[List.eraseIdx_insertNth]
      intro ht
      simp[ht] at h
      sorry


       )]
      rfl
    conv =>
      enter[1,1,a]
      rw[UniformSample_apply (tl.length + 1).toPNat']
      rfl

