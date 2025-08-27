import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Basic
import SampCert.DifferentialPrivacy.Pure.ShuffleModel.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.DPProof
import Mathlib.Data.Set.Card

namespace SLang
open RandomizedResponse
open Classical

lemma List.isEmpty_iff (l : List α): l.isEmpty ↔ l = [] := by
 apply Iff.intro
 intro hl
 simp [List.isEmpty] at hl
 cases l with
 | nil => rfl
 | cons hd tl => simp at hl
 intro hl
 simp [List.isEmpty, hl]

lemma Shuffler_on_perm {U : Type} (l₁ l₂ : List U) (hp: l₁.isPerm l₂): Shuffler l₁ l₂ = (num_perms l₁ : ENNReal)⁻¹ := by
  induction l₁ generalizing l₂ with
  | nil =>
   simp_all [List.isPerm]
   rw [List.isEmpty_iff] at hp
   subst hp
   simp [Shuffler, num_perms]
  | cons hd tl ih =>
    simp [Shuffler]
    
    #check List.eraseIdx
    sorry

lemma Shuffler_not_perm {U : Type} (l₁ l₂ : List U) (hp: l₁.isPerm l₂ = false): Shuffler l₁ l₂ = 0 := by
  induction l₁ generalizing l₂ with
  | nil =>
  simp_all [List.isPerm]
  have hp' : ¬l₂ = [] := by aesop
  simp [Shuffler, hp']
  | cons hd tl ih =>
  simp [Shuffler]
  intro i
  cases hi: (i < (hd :: tl).length) == true with
  | false =>
    simp at hi
    apply Or.inl
    refine UniformSample_apply_out (tl.length + 1).toPNat' i ?cons.true.h.support
    aesop
  | true =>
    simp at hi
    apply Or.inr
    intro l₂' hl₂'
    apply ih l₂'
    by_contra hperm
    simp at hperm
    simp [List.isPerm] at hp
    have: hd ∈ l₂ := by
      simp [hl₂']
      refine (List.mem_insertNth ?_).mpr ?_
      have: l₂'.length = tl.length := by
        apply List.Perm.length_eq
        rw [List.isPerm_iff] at hperm
        rw [@List.perm_comm]
        exact hperm
      rw [this]
      linarith
      apply Or.inl
      rfl
    have hp': tl.isPerm (l₂.erase hd) = false := hp this
    have h1: l₂.eraseIdx i = l₂' := by simp_all [List.eraseIdx_insertNth]
    have h2:  tl.isPerm (l₂.eraseIdx i) → tl.isPerm (l₂.erase hd) := by
      rw [List.isPerm_iff, List.isPerm_iff]
      intro h
      constructor
      apply h
      have: l₂.erase hd = l₂.eraseIdx (l₂.indexOf hd) := by
        sorry
      rw [this]
      sorry
    have hp': tl.isPerm (l₂.eraseIdx i) = false := by
      by_contra x
      simp at x
      have: ¬ (tl.isPerm (l₂.erase hd) = false) := by simp [h2 x]
      contradiction
    have nothp: ¬ (tl.isPerm l₂' = true) := by rw[h1] at hp'; simp [hp']
    contradiction

lemma Shuffler_is_uniform {U : Type}: @UniformShuffler U (Shuffler) := by
  simp [UniformShuffler]
  intro l₁ l₂
  cases hp: l₁.isPerm l₂ with
  | true =>
    simp
    apply Shuffler_on_perm
    exact hp
  | false =>
    simp
    apply Shuffler_not_perm
    exact hp

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
    clear h0
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

/- RRShuffle normalizes. -/
theorem RRShuffle_PMF_helper {T : Type}(query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den)(l : List T): HasSum (RRShuffle query num den h l) 1 := by
  have heqv: RRShuffle query num den h = ShuffleAlgorithm (RRSample_PMF query num den h) (Shuffler) (Shuffler_is_uniform) := by rfl
  rw [heqv]
  apply ShuffleAlgorithm_PMF_helper

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

theorem RRShuffle_is_DP (ε : ℝ) (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den): DP_withUpdateNeighbour (RRShuffle_PMF query num den h) (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num))) := by
  have heqv: RRShuffle_PMF query num den h = ShuffleAlgorithm_PMF (RRSample_PMF query num den h) (Shuffler) (Shuffler_is_uniform) := by rfl
  rw [heqv]
  apply ShuffleAlgorithm_is_DP
  exact RRSample_DP query num den h
