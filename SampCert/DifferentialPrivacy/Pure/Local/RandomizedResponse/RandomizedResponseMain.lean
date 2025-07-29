import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.Samplers.Bernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.Local.LawfulMonadSLang
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.BasicLemmas
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.DPProof
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.PMFProperties
import SampCert.DifferentialPrivacy.Pure.Local.ENNRealLemmasSuite
/-import SampCert.DifferentialPrivacy.Local.MultiBernoulli -/

open SLang
open ENNRealLemmas
open RandomizedResponse

namespace SLang
lemma simplifier_1 (f : T -> SLang Bool):
(∑' (a : List Bool), if c = a then mapM f tl a else 0) = mapM f tl c := by
rw[tsum_eq_single c]
aesop
intro b h
simp_all only [ne_eq, mapM, ite_eq_right_iff]
intro a
subst a
simp_all only [not_true_eq_false]

lemma mapM_dist_cons (f: T → SLang Bool) (b: Bool)(c: List Bool)(hd: T)(tl: List T):
mapM f (hd :: tl) (b :: c) = f hd b * mapM f tl c := by
rw[List.mapM_cons]
simp[-mapM]
rw [@tsum_bool]
cases b with
| true =>
simp[-mapM]
conv =>
  enter [1, 2]
  rw [simplifier_1]
| false =>
simp [-mapM]
conv =>
  enter [1, 2]
  rw [simplifier_1]

lemma RRSample_rec (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (hd: T)(tl : List T)(b: Bool)(c: List Bool):
RRSample query num den h (hd::tl) (b::c) = RRSingleSample query num den h hd b * RRSample query num den h tl c := by
unfold RRSample
set f := fun x => RRSingleSample query num den h x
rw[mapM_dist_cons f b c hd tl]


lemma prod_of_ind_prob(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample query num den h l a = (∏'(i: Fin l.length), RRSingleSample query num den h (l.get i) (a.get (Fin.cast k i ))):= by
induction l generalizing a with
| nil =>
  simp
  rw[List.length_nil] at k
  symm at k
  apply List.eq_nil_of_length_eq_zero at k
  rw[k]
  unfold RRSample
  rw [List.mapM_nil]
  simp [pure]

| cons hd tl ih =>
  simp
  simp at ih
  cases a with
  | nil =>
  simp at k
  | cons b c =>
  rw[RRSample_rec query num den h]
  rw[ih c]
  rw [@tprod_fintype]
  rw [@tprod_fintype]

  rw[Fin.prod_univ_succ]
  simp
  simp at k
  exact k

theorem prod_of_ind_prob_PMF(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample_PMF query num den h l a = (∏'(i: Fin l.length), RRSingleSample query num den h (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

lemma final_bound (query : T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (a a' : T) (b : Bool):
  RRSingleSample query num den h a b / RRSingleSample query num den h a' b
  ≤ (den + 2 * num) / (den - 2 * num) := by
  cases b with
  | true =>
    cases hqa : query a with
    | true =>
      rw [RRSingleSample_true_true _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hqa']
                rw[ENNReal.div_self]
                {sorry}
                {rw [@ENNReal.div_ne_zero]
                 apply And.intro
                 simp
                 intro hd
                 apply False.elim
                 apply pnat_zero_imp_false den hd
                 apply mult_ne_top
                 simp
                 simp
                }
                { apply div_ne_top
                  simp
                  apply mult_ne_top
                  simp
                  simp
                  simp
                  rw[Not]
                  apply pnat_zero_imp_false den
                }
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hqa']
                -- arithmetic now
                 sorry
    | false =>
      rw [RRSingleSample_false_true _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hqa']
                -- arithmetic now
                sorry
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hqa']
                 rw[ENNReal.div_self]
                 { rw [@Decidable.le_iff_lt_or_eq]
                   cases hnum : num == 0 with
                   | true => simp at hnum
                             apply Or.inr
                             subst hnum
                             simp
                             rw [ENNReal.div_self]
                             norm_num
                             apply pnat_zero_imp_false
                             simp
                   | false => simp at hnum
                              apply Or.inl
                              apply quot_gt_one_rev
                              simp
                              have h1: 0 < (2 : ENNReal) * num + 2 * num := by sorry
                              have h2: den < den + (2 : ENNReal) * num + 2 * num := by sorry
                              aesop
                              sorry
                  }
                 {rw [@ENNReal.div_ne_zero]
                  apply And.intro
                  simp
                  norm_cast
                  simp [Nat.cast_mul]
                  intro hd
                  sorry /- For this sorry, we need the h hypothesis to be a strict inequality -/
                  apply mult_ne_top
                  simp
                  simp
                 }
                 { apply div_ne_top
                   simp
                   aesop
                   apply pnat_zero_imp_false den a_1
                 }
                 -- arithmetic now

  | false =>
    cases hqa : query a with
    | true =>
      rw [RRSingleSample_true_false _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                -- arithmetic now
                sorry
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 -- arithmetic now
                 sorry
    | false =>
      rw [RRSingleSample_false_false _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                -- arithmetic now
                sorry
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 -- arithmetic now
                 sorry

lemma valid_index0 (l₁ : List T)(h1: l₁ = a++[n]++b) (i : Fin (l₁.length - 1)): (Fin.succAbove (a.length) i).val < l₁.length := by
  have hl : l₁.length - 1 + 1 = l₁.length := by
      rw [Nat.sub_add_cancel]
      rw [h1]
      simp
      linarith
  simp [Fin.succAbove]
  split
  simp [Fin.castSucc]
  {calc
  i.val < l₁.length - 1 := i.2
  _ < l₁.length := by aesop}
  {
    calc
    i.succ.val = i.val + 1 := by simp
    _ < l₁.length - 1 + 1 := by linarith[i.2]
    _ = l₁.length := by rw [hl]
  }

lemma valid_index1 (l₁ l₂ : List T)(h1: l₁ = a++[n]++b) (h2: l₂ = a++[m]++b) (i : Fin ((l₁.length - 1))): (Fin.succAbove (a.length) i).val < l₂.length := by
  have hl: l₁.length = l₂.length := by aesop
  rw[←hl]
  apply valid_index0
  exact h1

lemma mod_helper (a b: ℕ)(h1: b ≥ 1)(h2: a<b): a % (b-1+1) = a := by
  rw[Nat.mod_eq_of_lt]
  rw[Nat.sub_add_cancel]
  exact h2
  exact h1

lemma succHelp (l₁ l₂ : List T)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b): ∀i : Fin (l₁.length - 1), l₁[(Fin.succAbove a.length i).val]'(valid_index0 l₁ h1 i) = l₂[Fin.succAbove a.length i]'(valid_index1 l₁ l₂ h1 h2 i) := by
      intro i
      simp only [h1,h2]
      by_cases i < a.length
      case pos h =>
        unfold Fin.succAbove
        have h' : i.castSucc < ↑a.length := by
          rw [@Fin.castSucc_lt_iff_succ_le]
          rw [@Fin.le_iff_val_le_val]
          simp
          rw[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
          simp[Nat.succ_le_of_lt h]

        simp only[h']
        simp only [↓reduceIte, Fin.coe_castSucc,Fin.getElem_fin]
        rw[List.getElem_append_left (a++[n]) b (by simp[h];linarith)]
        rw[List.getElem_append_left a [n] h]
        rw[List.getElem_append_left (a++[m]) b (by simp[h];linarith)]
        rw[List.getElem_append_left]
      case neg h =>
        have iab: i.val - a.length < b.length := by
          have ile : i < l₁.length - 1 := i.is_lt
          simp[h1] at ile
          rw[tsub_lt_iff_left]
          exact ile
          simp at h
          exact h
        unfold Fin.succAbove
        have h' : ¬ i.castSucc < ↑a.length := by
          simp at h
          simp
          rw [@Fin.le_castSucc_iff]
          apply Nat.lt_succ_of_le
          simp
          rw[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
          exact h
        simp only[h']
        simp only [↓reduceIte, Fin.coe_castSucc,
          Fin.getElem_fin]
        rw[List.getElem_append_right (a++[n]) b (by simp;linarith)]
        rw[List.getElem_append_right (a++[m]) b (by simp;linarith)]
        simp
        simp
        linarith
        simp
        exact iab


lemma valid_index2 {l₁ : List T} (h1: l₁ = a++[n]++b) (i : Fin ((l₁.length - 1) + 1)):
  i.val < l₁.length := by
    have hl1: l₁.length - 1 + 1 = l₁.length := by
      rw [Nat.sub_add_cancel]
      rw[h1]
      simp
      linarith
    exact Nat.lt_of_lt_of_eq i.2 hl1

lemma valid_index3 {l₁ : List T} {x : List Bool} (h1: l₁ = a++[n]++b) (hx: l₁.length = x.length) (i : Fin ((l₁.length - 1) + 1)):
  i.val < x.length := by
    rw[←hx]
    apply valid_index2 h1 i


lemma reduction2 (l₁ l₂: List T)(x: List Bool)(f: T → SLang Bool)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)(nonzero: ∀(k: T) (bo: Bool), f k bo ≠ 0)(noninf: ∀(k: T) (bo: Bool), f k bo ≠ ⊤):(∏' (i : Fin ((l₁.length-1)+1)), f (l₁[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) /
    (∏' (i : Fin ((l₂.length-1)+1)), f (l₂[i.val]'(valid_index2 h2 i)) (x[i.val]'(valid_index3 h2 hy i)))  = f (l₁[(a.length)]'(by rw[h1]; simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) / f (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx]; rw[h1]; simp)) := by
    rw[tprod_fintype]
    rw[tprod_fintype]
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₁.length-1)+1)) => f (l₁[b.val]'(valid_index2 h1 b)) (x[b.val]'(valid_index3 h1 hx b))) a.length]

    have ind: a.length < x.length := by
      rw[← hx]
      rw[h1]
      simp
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₂.length-1)+1)) => f (l₂[b.val]'(valid_index2 h2 b)) (x[b.val]'(valid_index3 h2 hy b))) a.length]
    have helper: l₁.length - 1 = l₂.length - 1 := by aesop
    have hlp: (∏ i : Fin (l₁.length - 1), f l₁[(Fin.succAbove a.length i).val] x[↑(Fin.succAbove a.length i).val]) = ∏ i : Fin (l₂.length - 1), f l₂[(Fin.succAbove a.length i).val] x[(Fin.succAbove a.length i).val] := by
      apply Fintype.prod_equiv (Equiv.cast (congr_arg Fin helper))
      simp[succHelp l₁ l₂ h1 h2]
      intro i
      congr
      rw [← propext cast_eq_iff_heq]
      rw [← propext cast_eq_iff_heq]
    rw[hlp]
    rw[ENNReal.mul_div_mul_right]
    simp

    simp[mod_helper (a.length) (l₁.length) (by rw[h1];simp;linarith) (by rw[h1]; simp)]
    simp[mod_helper (a.length) (l₂.length) (by rw[h2];simp;linarith) (by rw[h2]; simp)]

    rw[Finset.prod_ne_zero_iff]
    intro i
    simp[nonzero]

    rw[← lt_top_iff_ne_top]
    apply ENNReal.prod_lt_top
    intro i
    simp[noninf]

lemma fin_prod_cast {n m : ℕ} (h : n = m)(f : Fin n → ENNReal) :
  ∏' i : Fin n, f i = ∏' i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  simp

lemma conversion (l: List T) (x: List Bool)(h1: l = a++[n]++b)(hl : l.length ≥ 1)(hx: l.length = x.length)(f: T → SLang Bool): (∏' (i : Fin (l.length)), f (l[i.val]'(by simp)) (x[i.val]'(by rw[← hx];simp))) = (∏' (i : Fin ((l.length-1)+1)), f (l[i.val]'(valid_index2 h1 i)) (x[i.val]'(valid_index3 h1 hx i))) := by
  rw [fin_prod_cast (by rw [← Nat.sub_add_cancel hl])]
  simp


theorem reduction_final (l₁ l₂: List T)(x: List Bool)(f: T → SLang Bool)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)(nonzero: ∀(k: T) (bo: Bool), f k bo ≠ 0)(noninf: ∀(k: T) (bo: Bool), f k bo ≠ ⊤):(∏' (i : Fin (l₁.length)), f (l₁[i.val]'(by simp)) (x[i.val]'(by rw[← hx]; simp))) /
    (∏' (i : Fin (l₂.length)), f (l₂[i.val]'(by simp)) (x[i.val]'(by rw[← hy];simp)))  = f (l₁[(a.length)]'(by rw[h1];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) / f (l₂[a.length]'(by rw[h2];simp)) (x[a.length]'(by rw[← hx];rw[h1];simp)) := by
    have hl2: l₂.length ≥ 1 := by rw[h2];simp; linarith
    have hl1: l₁.length ≥ 1 := by rw[h1];simp; linarith
    rw[conversion l₂ x h2 hl2 hy f]
    rw[conversion l₁ x h1 hl1 hx f]
    rw [reduction2 l₁ l₂ x f h1 h2 hx hy nonzero noninf]

open Finset
open scoped BigOperators

theorem RRSample_is_DP (query: T → Bool)(num: Nat)(den:PNat)(h: 2*num < den) :
DP_withUpdateNeighbour (RRSample_PMF query num den h) (Real.log ((1/2 + num / den) / (1/2 - num / den))) := by
apply singleton_to_event_update
intros l₁ l₂ h_adj x
cases xlen1 : l₁.length == x.length with
| true =>
          rw[prod_of_ind_prob_PMF query num den h x l₁ (by aesop)]
          rw[prod_of_ind_prob_PMF query num den h x l₂
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
                          apply final_step_combined
                          exact h
                        _ ≤   ENNReal.ofReal (Real.exp (Real.log ((2⁻¹ + ↑num / ↑↑↑den) / (2⁻¹ - ↑num / ↑↑↑den)))) := by aesop}
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
