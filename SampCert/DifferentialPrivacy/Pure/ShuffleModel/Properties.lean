import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.PMFProof


namespace SLang

lemma Shuffler_empty {α: Type}(l:List α)(h: l = []): Shuffler l [] = 1 := by
  unfold Shuffler
  rw [h]
  simp [pure]

lemma Shuffler_PMF {α: Type} [DecidableEq α][BEq α] (l:List α): HasSum (Shuffler l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  induction l with
  | nil =>
    unfold Shuffler
    simp [pure]
    unfold probPure
    rw [ENNReal.tsum_eq_add_tsum_ite []]
    aesop
  | cons h t ih =>
    unfold Shuffler
    simp [pure]
    rw [← Summable.hasSum_iff ENNReal.summable]
    rw [Summable.hasSum_iff ENNReal.summable]
    simp
    rw [ENNReal.tsum_comm]
    let hpf (b: Nat)(_: List α):  (fun (i: List α) => ∑'(a : List α), (if i = List.insertNth b h a then Shuffler t a else 0)) =
                                  (push_forward (Shuffler t) (fun (a: List α) => List.insertNth b h a)) := by
                                  unfold push_forward
                                  rfl
    conv =>
      enter [1,1,b]
      rw [ENNReal.tsum_mul_left]
      rw [hpf b t]
      enter [2]
      apply push_forward_prob_is_prob_gen
    rw [ih]
    simp

lemma Shuffler_norms {α: Type} [DecidableEq α][BEq α] (l:List α):  ∑' (b : List α), Shuffler l b = 1 := by
  rw [← Summable.hasSum_iff ENNReal.summable]
  apply Shuffler_PMF

lemma ShuffleAlgorithm_norms {U: Type} [BEq U] (m : Mechanism T (List U))(f : List U → SLang (List U))(h: UniformShuffler f)(l: List T):
HasSum (ShuffleAlgorithm (fun x => (m x).1) f h l) 1  := by
  unfold ShuffleAlgorithm
  simp_all only [bind, pure, bind_pure]
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1,1,b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    apply UniformShuffler_norms
    exact h
  simp
  rw [← Summable.hasSum_iff ENNReal.summable]
  exact (m l).2


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

theorem RRShuffle_norms [LawfulMonad SLang]{T : Type}(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l : List T): HasSum (RRShuffle query num den h l) 1 := by
  unfold RRShuffle
  simp_all only [bind, pure, bind_pure]
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1,1,b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    apply Shuffler_norms
  simp
  rw [← Summable.hasSum_iff ENNReal.summable]
  apply RRSample_PMF_helper

lemma UniformShuffler_norms {U: Type}[BEq U](f: List U → SLang (List U)) (h:UniformShuffler f)
:∀(b: List U),∑' (i : List U), f b i = 1 := by
  intro b
  have h2 :∀ x i: List U, f x i  = (if List.isPerm x i then  (1: ENNReal)/(x.length.factorial) else (0: ENNReal)) := by
    unfold UniformShuffler at h
    exact h
  conv =>
    enter [1,1,i]
    rw [h2]

  rw [← @ENNRealLemmas.tsum_ite_mult]
  conv =>
    enter [1]
    rw[ENNReal.tsum_mul_left]
  sorry

theorem BinomialSample_kprob (seed: MultiBernoulli.SeedType) (n : PNat) (k : Nat) :
  BinomialSample seed n k = ((n: Nat).choose k) * ((num / den) ^ k) * ((1 - (num / den)) ^ (n - k)) := by
  rw[BinomialSample]
  simp
  unfold MultiBernoulli.MultiBernoulliSample
  simp [pure, bind]

  sorry
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

def ShuffleAlgorithm_PMF {U: Type}[BEq U] (m : Mechanism T (List U ))(f : List U → SLang (List U))(h: UniformShuffler f)(l: List T) : PMF (List U) :=
  ⟨ShuffleAlgorithm (fun x => (m x).1) f h l, ShuffleAlgorithm_norms m f h l⟩


theorem ShuffleAlgorithm_is_DP [BEq U](m : Mechanism T (List U))(f : List U → SLang (List U))(ε : ℝ)(hdp: DP_withUpdateNeighbour m ε)
(hsa: UniformShuffler f): DP_withUpdateNeighbour (ShuffleAlgorithm_PMF m f hsa) ε := by sorry
