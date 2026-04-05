import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.LocalDP
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.ProbabilityProduct
import SampCert.DifferentialPrivacy.Pure.Local.Reduction

namespace SLang

open Classical

/- We define a general way to transform local randomizers into algorithms on datasets,
   and prove that the dataset-level algorithm satisfies the same DP bound as the local randomizer. -/

/- Transforms a local randomizer into a dataset-level algorithm. -/
def local_to_dataset (m : LocalMechanism T U) (l : List T) : SLang (List U) :=
  (l.mapM (fun x => (m x).1))

/- Proof of normalization for local_to_dataset. This is necessary to instantiate
   local_to_dataset as a PMF. -/
lemma local_to_dataset_normalizes (m : LocalMechanism T U) (l : List T):
HasSum (local_to_dataset m l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  rw [local_to_dataset]
  apply norm_func_norm_on_list
  intro x
  rw [← Summable.hasSum_iff ENNReal.summable]
  exact (m x).2

/- Instantiation of local_to_dataset as a PMF. -/
def local_to_dataset_PMF (m : LocalMechanism T U) (l : List T) : PMF (List U) :=
  ⟨local_to_dataset m l, local_to_dataset_normalizes m l⟩

/- local_to_dataset outputs datasets of different length than the input dataset with probability zero. -/
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

/- Prob_of_ind_prob lemma for local_to_dataset. -/
lemma local_to_dataset_prob_of_ind_prob_PMF (m: LocalMechanism T U) (l : List T) (a: List U) (k : l.length = a.length) :
  local_to_dataset_PMF m l a = (∏'(i: Fin l.length), m (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- This lemma states that, under a technical assumption, the algorithm
   that applies the same local randomizer to each row of data satisfies the same
   DP bound as the local randomizer.
   The hypotheses "nonzero" and "equiv" should be regarded as technical conditions.
   Essentially, they require the user to provide a precise characterization of which
   outputs of the local randomizer occur with probability zero.
   This is necessary in order to apply the reduction lemma.
   This lemma is applied in the proof of DP for both Randomized Response and One-Time Basic RAPPOR.
   -/
lemma LocalDP_to_dataset (m : LocalMechanism T U) (ε : ℝ)
  (equiv: ∀ l₁ l₂ : List T, (h_upd: UpdateNeighbour l₁ l₂) → ∀ b : List U, (blen1: l₁.length = b.length) →
  (∀ i : Fin l₁.length, (m l₁[i]) (b[i]) = 0 ↔ (m (l₂[i]'(by
                                                          have h: l₂.length = b.length := by rw[←blen1]; apply (Eq.symm (UpdateNeighbour_length h_upd))
                                                          omega))) b[i] = 0))
  (noninf: ∀ (k : T) (bo : U), (m k) bo ≠ ⊤):
  Local_DP m ε → DP_withUpdateNeighbour (local_to_dataset_PMF m) ε := by
    let P: T → U → Bool := fun k bo => (m k) bo ≠ 0
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
                  have valid_index9 (i : Fin (l₂.length - 1)): i.val + 1 < x.length := by
                    rw[←xlen2]
                    have h1: i.val < l₂.length - 1 := i.2
                    omega
                  have valid_index10 (i : Fin (l₂.length - 1)): i.val < x.length := by
                    rw[←xlen2]
                    omega
                  cases P_true: ((∀ i : Fin (l₂.length - 1), P (l₂[(@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove i]'(by simp[Fin.succAbove]; aesop)) (x[(@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove i]'(by simp [Fin.succAbove]; aesop))) == true) with
                  | true =>
                  rw [reduction_final l₁ l₂ a c y z x _ hl₁ hl₂ xlen1 xlen2 _ noninf]
                  simp[Local_DP] at hloc
                  apply hloc
                  intro i
                  simp[P] at P_true
                  apply P_true i
                  | false =>
                    simp at P_true
                    have nonzero2: ∀ (k : T) (bo : U), P k bo = false ↔ (m k) bo = 0 := by
                          intro k bo
                          apply not_iff_not.mp
                          simp [P]
                    /- The next several "have" statements are just to prove index validity.
                       The proofs can undoubtedly be simplfied with some effort. -/
                    have h1: a.length + (c.length + 1) = l₂.length := by
                        rw [hl₂]
                        simp_all only [ne_eq, Fin.getElem_fin, List.append_assoc, List.singleton_append,
                          List.length_append, List.length_cons]
                    have valid_index11 (t : Fin (l₂.length - 1)): t.val + 1 < a.length + (c.length + 1) := by
                      rw [h1]
                      omega
                    have valid_index12 (t : Fin (l₂.length - 1)): t.val < a.length + (c.length + 1) := by
                      rw [h1]
                      omega
                    have h1: ∏' (i : Fin l₂.length), (m l₂[i.val]) x[i.val] = 0 := by
                      rw [tprod_fintype]
                      rw [@Finset.prod_eq_zero_iff]
                      cases P_true with
                      | intro z hz =>
                        have valid_index13: ((@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove z).val < l₂.length := by
                          simp[Fin.succAbove]
                          rename_i z_1
                          simp_all only [ne_eq, Fin.getElem_fin, List.append_assoc, List.singleton_append,
                            List.length_append, List.length_cons]
                          split
                          next h => simp_all only [Fin.coe_castSucc]
                          next h => simp_all only [not_lt, Fin.val_succ]
                        use ⟨(@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove z, valid_index13⟩
                        apply And.intro
                        simp
                        apply (nonzero2 _ _).mp
                        apply hz
                    have h2: ∏' (i : Fin l₁.length), (m l₁[i.val]) x[i.val] = 0 := by
                      rw [tprod_fintype]
                      rw [@Finset.prod_eq_zero_iff]
                      cases P_true with
                      | intro z hz =>
                        have valid_index13: ((@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove z).val < l₁.length := by
                          simp[Fin.succAbove]
                          rename_i z_1
                          simp_all only [ne_eq, Fin.getElem_fin, List.append_assoc, List.singleton_append,
                            List.length_append, List.length_cons]
                          split
                          next h => simp_all only [Fin.coe_castSucc]
                          next h => simp_all only [not_lt, Fin.val_succ]
                        use ⟨(@Nat.cast (Fin (l₂.length - 1 + 1)) Fin.instNatCast a.length).succAbove z, valid_index13⟩
                        apply And.intro
                        simp
                        apply (equiv l₁ l₂ (UpdateNeighbour.Update hl₁ hl₂) x xlen1 _).mpr
                        simp_all [P]
                    rw [h2]
                    rw [@ENNReal.zero_div]
                    simp
      | false => simp at xlen1
                 rw [←Ne.eq_def] at xlen1
                 have numerator_zero: local_to_dataset_PMF m l₁ x = 0 := local_to_dataset_diff_lengths l₁ x xlen1
                 rw [numerator_zero]
                 rw [@ENNReal.zero_div]
                 simp
