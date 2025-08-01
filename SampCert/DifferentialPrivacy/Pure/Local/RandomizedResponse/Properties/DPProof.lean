import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Basic
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.BasicLemmas
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Properties.Reduction

open SLang
open ENNRealLemmas
open RandomizedResponse

namespace SLang

/- Helper lemma about mapM to prove "prod_of_ind_prob"-/
lemma mapM_dist_cons {β : Type} [DecidableEq β] (f: T → SLang β) (b: β)(c: List β)(hd: T)(tl: List T):
mapM f (hd :: tl) (b :: c) = f hd b * mapM f tl c := by
  rw[List.mapM_cons]
  simp[-mapM]
  conv =>
    enter [1, 1, a, 2]
    simp[-mapM]
    rw [simplifier_3]
  rw [tsum_eq_single b]
  aesop
  aesop

/- First step of the DP Proof: using indepenendence to rewrite the total probability
   as a product of probabilities. -/
lemma prod_of_ind_prob (β : Type) [DecidableEq β] (f : T -> SLang β) (a : List β) (l : List T) (k : l.length = a.length) :
  mapM f l a = (∏' (i : Fin l.length), f (l.get i) (a.get (Fin.cast k i))) := by
  induction l generalizing a with
  | nil =>
    simp[-mapM]
    rw[List.length_nil] at k
    symm at k
    apply List.eq_nil_of_length_eq_zero at k
    rw[k]
  | cons hd tl ih =>
    cases a with
    | nil =>
      simp at k
    | cons b c =>
      rw [mapM_dist_cons]
      rw [ih c]
      rw [@tprod_fintype]
      rw [@tprod_fintype]
      simp
      rw[Fin.prod_univ_succ]
      simp at k
      apply Eq.refl
      aesop

end SLang

/- Version of the above lemma for the PMF instantiation of RRSample. -/
theorem RRSample_prod_of_ind_prob_PMF(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample_PMF query num den h l a = (∏'(i: Fin l.length), RRSingleSample query num den h (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

/- Proof of DP for Randomized Response. -/
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
                        rw[reduction_final l₁ l₂ x (RRSingleSample query num den h ) hl₁ hl₂ xlen3 xlen2]
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
                        {apply RRSingleSample_non_zero query num den h}
                        {apply RRSingleSample_finite query num den h}
| false => simp at xlen1
           rw [←Ne.eq_def] at xlen1
           have numerator_zero: RRSample_PMF query num den h l₁ x = 0 := by
            rw [RRSamplePMF_diff_lengths]
            exact xlen1
           rw [numerator_zero]
           rw [@ENNReal.zero_div]
           simp
