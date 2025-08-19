import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Uniform.Properties
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.PushForward
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Code
import SampCert.DifferentialPrivacy.Pure.Local.MultiBernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.PMFProperties


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


theorem BinomialSample_kprob (seed: MultiBernoulli.SeedType) (n : PNat) (k : Nat) :
  BinomialSample seed n k = ((n: Nat).choose k) * ((num / den) ^ k) * ((1 - (num / den)) ^ (n - k)) := by
  rw[BinomialSample]
  simp
  unfold MultiBernoulli.MultiBernoulliSample
  simp [pure, bind]

  sorry

lemma Shuffle_permutes {α: Type} [BEq α] (l₁ l₂: List α)(hlen1:  l₁.length = n)(hlen2: l₂.length = n)(h: List.isPerm l₁ l₂): Shuffler l₁ l₂ = 1/Nat.factorial n := by
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
    conv =>
      enter[1,1,a,2]
      rw[tsum_eq_single (List.eraseIdx l₂ a ) (by
      intro b' h
      simp

      aesop
      have h2: b' = List.eraseIdx (List.insertNth a hd b') a := by rw[List.eraseIdx_insertNth]
      contradiction
       )]
      rfl

    rw[tsum_eq_single]
    sorry
