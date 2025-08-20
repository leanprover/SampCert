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
import SampCert.DifferentialPrivacy.Pure.RandomizedPostProcessing


namespace SLang
open RandomizedResponse

/- Shuffler function normalizes-/
lemma Shuffler_PMF_helper {α: Type} [DecidableEq α][BEq α] (l:List α): HasSum (Shuffler l) 1 := by
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
  apply Shuffler_PMF_helper

def Shuffler_PMF {α : Type} [DecidableEq α] [BEq α] (l : List α) : PMF (List α) :=
  ⟨Shuffler l, Shuffler_PMF_helper l⟩

/- RRShuffle normalizes. -/
theorem RRShuffle_PMF_helper [LawfulMonad SLang]{T : Type}(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l : List T): HasSum (RRShuffle query num den h l) 1 := by
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

def RRShuffle_PMF [LawfulMonad SLang] {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨RRShuffle query num den h l, RRShuffle_PMF_helper query num den h l⟩

/- Any shuffle algorithm normalizes. -/
lemma ShuffleAlgorithm_PMF_helper {U: Type} [BEq U] (m : Mechanism T (List U))(f : List U → SLang (List U))(h: UniformShuffler f)(h1: ∀u : List U, ∑' (v : List U), f u v = 1) (l: List T):
HasSum (ShuffleAlgorithm m f h l) 1  := by
  unfold ShuffleAlgorithm
  simp_all only [bind, pure, bind_pure]
  unfold probBind
  simp [Summable.hasSum_iff ENNReal.summable]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1,1,b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    apply h1
  simp

/- Conversion of SLang output to PMF.-/
def ShuffleAlgorithm_PMF {U: Type}[BEq U] (m : Mechanism T (List U ))(f : List U → SLang (List U))(h: UniformShuffler f) (h1: ∀u : List U, ∑' (v : List U), f u v = 1) (l: List T) : PMF (List U) :=
  ⟨ShuffleAlgorithm m f h l, ShuffleAlgorithm_PMF_helper m f h h1 l⟩

lemma shuffling_is_postprocessing [LawfulMonad SLang] [BEq U] (m : Mechanism T (List U)) (f : List U → SLang (List U)) (h_uniform : UniformShuffler f) (h1: ∀u : List U, ∑' (v : List U), f u v = 1): privPostProcessRand m (fun u => ⟨f u, by
  simp [Summable.hasSum_iff ENNReal.summable]
  exact h1 u⟩) = ShuffleAlgorithm_PMF m f h_uniform h1:= by
  funext x
  simp [privPostProcessRand, ShuffleAlgorithm_PMF, ShuffleAlgorithm]
  congr

/- Shuffle Algorithm is ε-differentially private, given that the local algorithm is ε-differentially private. -/
theorem ShuffleAlgorithm_is_DP [LawfulMonad SLang] [BEq U](m : Mechanism T (List U))(f : List U → SLang (List U))(ε : ℝ)(hdp: DP_withUpdateNeighbour m ε)
(h_uniform: UniformShuffler f) (h1: ∀u : List U, ∑' (v : List U), f u v = 1): DP_withUpdateNeighbour (ShuffleAlgorithm_PMF m f h_uniform h1) ε := by
have h2 (u : List U): HasSum (f u) 1 := by
  simp [Summable.hasSum_iff ENNReal.summable]
  exact h1 u
conv =>
  enter [1]
  rw [←shuffling_is_postprocessing]
let g : List U → PMF (List U) := (fun u => ⟨f u, h2 u⟩)
apply @randPostProcess_DP_bound_with_UpdateNeighbour T _ _ m ε hdp g
