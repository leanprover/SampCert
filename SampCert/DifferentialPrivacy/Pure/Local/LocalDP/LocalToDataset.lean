import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.LocalDP
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.ProbabilityProduct
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.Reduction

namespace SLang

open Classical

def local_to_dataset (m : LocalMechanism T U) (l : List T) : SLang (List U) :=
  (l.mapM (fun x => (m x).1))

lemma local_to_dataset_normalizes (m : LocalMechanism T U) (l : List T):
HasSum (local_to_dataset m l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  rw [local_to_dataset]
  apply norm_func_norm_on_list
  intro x
  rw [← Summable.hasSum_iff ENNReal.summable]
  exact (m x).2

def local_to_dataset_PMF (m : LocalMechanism T U) (l : List T) : PMF (List U) :=
  ⟨local_to_dataset m l, local_to_dataset_normalizes m l⟩

lemma local_to_dataset_diff_lengths (l₁ : List T) (x : List U) (hlen : l₁.length ≠ x.length):
  local_to_dataset m l₁ x = 0 := by
  induction l₁ generalizing x with
  | nil => simp [local_to_dataset, -mapM]
           aesop
  | cons hd tl ih =>
  simp [local_to_dataset, -mapM]
  simp [local_to_dataset, -mapM] at ih
  intro b
  apply Or.inr
  intro y hy
  subst hy
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]

lemma local_to_dataset_prob_of_ind_prob_PMF (m: LocalMechanism T U) (l : List T) (a: List U) (k : l.length = a.length) :
  local_to_dataset_PMF m l a = (∏'(i: Fin l.length), m (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

theorem local_to_dataset_reduction {T β: Type} (a b : List T) (n m : T) (l₁ l₂: List T)(x: List β)(f: T → PMF β)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)
(nonzero: ∀(k: T) (bo: β), f k bo ≠ 0)
(noninf: ∀(k: T) (bo: β), f k bo ≠ ⊤):(∏' (i : Fin (l₁.length)), f (l₁[i.val]'(by simp)) (x[i.val]'(by rw[← hx]; simp))) /
    (∏' (i : Fin (l₂.length)), f (l₂[i.val]'(by simp)) (x[i.val]'(by rw[← hy];simp)))  = f (l₁[(a.length)]'(by rw[h1];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) / f (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp))
    := reduction_final l₁ l₂ a b n m x _ h1 h2 hx hy (by simp[nonzero]) noninf

/- We need a stronger version of reduction, where we only assume it's nonzero for b of the same length. -/

lemma LocalDP_to_dataset (m : LocalMechanism T U) (ε : ℝ)
  (nonzero: ∀ (k : T) (bo : U), (m k) bo ≠ 0)
  (noninf: ∀ (k : T) (bo : U), (m k) bo ≠ ⊤):
  Local_DP m ε → DP_withUpdateNeighbour (local_to_dataset_PMF m) ε := by
    intro hloc
    apply singleton_to_event_update
    intros l₁ l₂ h_adj x
    cases xlen1 : l₁.length == x.length with
      | true => simp at xlen1
                have xlen2: l₂.length = x.length := by
                  rw [←xlen1]
                  rw[←UpdateNeighbour_length h_adj]
                rw[local_to_dataset_prob_of_ind_prob_PMF m l₁ x xlen1]
                rw[local_to_dataset_prob_of_ind_prob_PMF m l₂ x xlen2]
                cases h_adj with
                | Update hl₁ hl₂ =>
                  rename_i a y c z
                  simp
                  rw [local_to_dataset_reduction a c y z l₁ l₂ x m hl₁ hl₂ xlen1 xlen2 _ noninf]
                  simp[Local_DP] at hloc
                  apply hloc
                  intro i
                  apply nonzero
      | false => simp at xlen1
                 rw [←Ne.eq_def] at xlen1
                 have numerator_zero: local_to_dataset_PMF m l₁ x = 0 := local_to_dataset_diff_lengths l₁ x xlen1
                 rw [numerator_zero]
                 rw [@ENNReal.zero_div]
                 simp
