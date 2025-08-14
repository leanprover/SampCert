import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Basic
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.BasicLemmas
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.Reduction
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.LocalToDataset

open SLang
open ENNRealLemmas
open RandomizedResponse

namespace SLang

/- Version of the prod_of_ind_prob lemma for the PMF instantiation of RRSample. -/
theorem RRSample_prod_of_ind_prob_PMF(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample_PMF query num den h l a = (∏'(i: Fin l.length), RRSingleSample query num den h (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- Proof of DP for Randomized Response. We use the reduction lemma from a different file. -/
theorem RRSample_is_DP (query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den) :
DP_withUpdateNeighbour (RRSample_PMF query num den h) (Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den))) := by
apply singleton_to_event_update
intros l₁ l₂ h_adj x
cases xlen1 : l₁.length == x.length with
| true =>
          rw[RRSample_prod_of_ind_prob_PMF query num den h x l₁ (by aesop)]
          rw[RRSample_prod_of_ind_prob_PMF query num den h x l₂
          (by rw[←UpdateNeighbour_length h_adj]
              simp at xlen1
              exact xlen1)]
          cases h_adj with
          | Update hl₁ hl₂ =>
                        rename_i a n b m
                        have hlen: l₁.length = l₂.length := by aesop
                        have xlen2 : l₂.length = x.length := by aesop
                        simp
                        have xlen3 : l₁.length = x.length := by aesop
                        rw[reduction_final l₁ l₂ a b n m x (RRSingleSample query num den h ) hl₁ hl₂ xlen3 xlen2]
                        have i1: a.length < x.length := by
                          rw[←xlen3]
                          subst hl₁ hl₂
                          simp_all only [List.append_assoc, List.singleton_append, List.length_append,
                            List.length_cons, beq_iff_eq]
                          rw[←xlen1]
                          rw [@Nat.lt_add_right_iff_pos]
                          simp
                        {calc
                        RRSingleSample query num den h (l₁[a.length]'(by aesop)) (x[a.length]'(by aesop))
                        / RRSingleSample query num den h (l₂[a.length]'(by aesop)) (x[a.length]'(by aesop)) ≤ (den + 2 * num) / (den - 2 * num) := by apply final_bound
                        _ ≤ ENNReal.ofReal (Real.exp (Real.log ((1/2 + num/den) / (1/2 - num/den)))) := by
                          apply final_coercion
                          exact h
                        _ ≤   ENNReal.ofReal (Real.exp (Real.log ((2⁻¹ + num / den) / (2⁻¹ - num / den)))) := by aesop
                        }
                        {intro i
                         apply RRSingleSample_non_zero query num den h}
                        {apply RRSingleSample_finite query num den h}
| false => simp at xlen1
           rw [←Ne.eq_def] at xlen1
           have numerator_zero: RRSample_PMF query num den h l₁ x = 0 := by
            rw [RRSamplePMF_diff_lengths]
            exact xlen1
           rw [numerator_zero]
           rw [@ENNReal.zero_div]
           simp

/- A different perspective-/
def RRSingle_Local (query : T → Bool) (num: Nat) (den : PNat) (h: 2 * num < den): LocalMechanism T Bool :=
  fun l => ⟨RRSingleSample query num den h l, RRSingleSample_PMF_helper query num den h l⟩

lemma RR_Local_DP (query : T → Bool) (num : Nat) (den : PNat) (h : 2 * num < den): Local_DP (RRSingle_Local query num den h) (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num))) := by
  rw [Local_DP]
  intro u₁ u₂ y
  simp [RRSingle_Local]
  have h1: RRSingleSample query num den h u₁ y / RRSingleSample query num den h u₂ y ≤ ENNReal.ofReal (Real.exp (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num)))) := by
    calc
    RRSingleSample query num den h u₁ y / RRSingleSample query num den h u₂ y ≤ (↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num) := final_bound query num den h u₁ u₂ y
    _ = ENNReal.ofReal (Real.exp (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num)))) := by rw [final_step_combined num den h]
  apply h1

lemma RRSample_DP (query : T → Bool) (num : Nat) (den : PNat) (h : 2 * num < den): DP_withUpdateNeighbour (RRSample_PMF query num den h) (Real.log ((↑(NNReal.ofPNat den) + 2 * ↑num) / (↑(NNReal.ofPNat den) - 2 * ↑num))) := by
  have h1: RRSample_PMF query num den h = local_to_dataset_PMF (RRSingle_Local query num den h) := rfl
  rw [h1]
  apply LocalDP_to_dataset
  apply RRSingleSample_non_zero query num den h
  apply RRSingleSample_finite query num den h
  apply RR_Local_DP
