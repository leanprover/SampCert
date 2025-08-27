import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Basic
import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.DPProof
import Mathlib.Data.Set.Card

namespace SLang
open RandomizedResponse
open Classical

/- Shuffler function normalizes-/
lemma Shuffler_PMF_helper {α: Type} (l:List α): HasSum (Shuffler l) 1 := by
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

/- A restatement of the above lemma. -/
lemma Shuffler_norms {α: Type} (l:List α):  ∑' (b : List α), Shuffler l b = 1 := by
  rw [← Summable.hasSum_iff ENNReal.summable]
  apply Shuffler_PMF_helper

/-Instantiation of Shuffler as a PMF. -/
def Shuffler_PMF {α : Type} (l : List α) : PMF (List α) :=
  ⟨Shuffler l, Shuffler_PMF_helper l⟩

/- Helper lemma about List.isPerm-/
lemma List.isPerm_iff_mem_permutations {U : Type} [DecidableEq U] [DecidableEq (List U)] (l : List U) (a : List U) : l.isPerm a ↔ (a ∈ l.permutations) := by
  apply Iff.intro
  simp
  rw [@List.perm_comm]
  intro hp
  apply (@List.isPerm_iff U _ l a).mp hp
  simp
  intro hp
  rw [@List.perm_comm] at hp
  apply (@List.isPerm_iff U _ l a).mpr hp

lemma UniformShuffler_norms' {U: Type} (f: List U → SLang (List U))(h: UniformShuffler f)(l: List U):
  ∑' (b : List U), f l b = 1 := by
  have h2: ∑' (b : List U), (if List.isPerm l b then ((num_perms l : ENNReal)⁻¹) else 0) = (num_perms l) * (num_perms l : ENNReal)⁻¹ := by
    set b := (num_perms l : ENNReal)⁻¹
    simp [@tsum_split_ite]
    conv =>
      enter [1, 1, b_1]
      rw [←one_mul b]
    rw [@ENNReal.tsum_mul_right]
    congr
    simp [num_perms]
    have h0: {x // l.isPerm x} = {x // x ∈ l.permutations.toFinset} := by
     congr
     apply funext
     intro x
     rw [eq_iff_iff]
     have h0a: x ∈ l.permutations.toFinset ↔ x ∈ l.permutations := by aesop
     rw [h0a]
     exact List.isPerm_iff_mem_permutations l x
    rw [h0]
    rw [tsum_fintype]
    simp_all only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one, Nat.cast_inj]
  simp_all [UniformShuffler]
  apply ENNReal.mul_inv_cancel
  all_goals simp[num_perms, List.permutations]

/- Alternate version -/
lemma UniformShuffler_norms {U: Type} (f: List U → SLang (List U))(h: UniformShuffler f)(l: List U):
  HasSum (f l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  exact UniformShuffler_norms' f h l

/- Any shuffle algorithm normalizes. -/
lemma ShuffleAlgorithm_PMF_helper {U: Type} (m : Mechanism T (List U))(f : List U → SLang (List U))(h: UniformShuffler f) (l: List T):
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
    apply UniformShuffler_norms'
    exact h
  simp

/- Conversion of SLang output to PMF.-/
def ShuffleAlgorithm_PMF {U: Type} [DecidableEq U] (m : Mechanism T (List U ))(f : List U → SLang (List U))(h: UniformShuffler f) (l: List T) : PMF (List U) :=
  ⟨ShuffleAlgorithm m f h l, ShuffleAlgorithm_PMF_helper m f h l⟩

/- RRShuffle normalizes.
   This is a bit unsatisfactory: if we had that ''RandomShuffle'' is in fact
   a UniformShuffler, then the prove would be trivial simply by instantiating RRShuffle as a UniformShuffler-/
lemma RRShuffle_PMF_helper {T : Type}(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l : List T): HasSum (RRShuffle query num den h l) 1 := by
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

/- Instantiation of RRShuffle as a PMF. -/
def RRShuffle_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨RRShuffle query num den h l, RRShuffle_PMF_helper query num den h l⟩

/- Shows that shuffling is a postprocessing function. -/
lemma shuffling_is_postprocessing (m : Mechanism T (List U)) (f : List U → SLang (List U)) (h_uniform : UniformShuffler f): privPostProcessRand m (fun u => ⟨f u, UniformShuffler_norms f h_uniform u⟩) = ShuffleAlgorithm_PMF m f h_uniform := by
  funext
  simp [privPostProcessRand, ShuffleAlgorithm_PMF, ShuffleAlgorithm]
  rfl

/- Shuffle Algorithm is ε-differentially private, given that the local algorithm is ε-differentially private. -/
theorem ShuffleAlgorithm_is_DP (m : Mechanism T (List U))(f : List U → SLang (List U))(ε : ℝ)(hdp: DP_withUpdateNeighbour m ε)
(h_uniform: UniformShuffler f): DP_withUpdateNeighbour (ShuffleAlgorithm_PMF m f h_uniform) ε := by
conv =>
  enter [1]
  rw [←shuffling_is_postprocessing]
let g : List U → PMF (List U) := (fun u => ⟨f u, UniformShuffler_norms f h_uniform u⟩)
apply @randPostProcess_DP_bound_with_UpdateNeighbour T _ _ m ε hdp g
