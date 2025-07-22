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
                 aesop
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

lemma head_tail_prod (x: List Bool)(l : List T)(f: T → SLang Bool) (h: l.length = x.length)(h1: l ≠ [])(h2 : x≠ []) :
 (∏' (i: Fin l.length), f l[i.val] x[i.val]) = f (l[0]'(by sorry)) (x[0]'(by sorry )) * ∏' (i : Fin l.tail.length), f (l.tail)[i.val] (x.tail[i.val]'(by sorry)):= by
  induction l generalizing x with
  | nil => aesop
  | cons l ls hl =>
    rw [tprod_fintype]
    rw[tprod_fintype]
    simp only [List.getElem_cons_zero]
    simp only [List.tail_cons]
    simp [Finset.prod_eq_multiset_prod]

    rw [@Fin.prod_ofFn]
    rw[@Fin.prod_ofFn]
    have h3 : ∀(i: Fin ls.length), (x[i.val+1]'(by sorry)) = (x.tail[i.val]'(by sorry)) := by
      intro i
      induction x with
      | nil => simp_all only [ne_eq, not_false_eq_true, List.length_cons, List.length_nil, add_eq_zero,
        List.length_eq_zero, one_ne_zero, and_false]
      | cons xh xt x => simp
    simp_all only [ne_eq, not_false_eq_true]
lemma prod_split (f: T → SLang Bool)(l a b : List T)(x c d : List Bool)(hl: l = a++b)(hx: x = c++d)(xl : x.length = l.length)(ac: a.length = c.length) :
∏' (i: Fin l.length), f l[i.val] x[i.val] = (∏'(i :Fin a.length), f a[i.val] c[i.val]) * ∏'(i: Fin b.length), f b[i.val] (d[i.val]'(by sorry)) := by
  rw[@tprod_fintype, @tprod_fintype, @tprod_fintype]
  have h1 : l.length = a.length + b.length := by aesop
  have h2: Fin l.length = Fin (a.length + b.length) := by aesop
  sorry
  -- rw [@Fin.prod_univ_add]
  -- simp_all only [Fin.coe_castAdd, Fin.coe_natAdd]

lemma reduction2 (l₁ l₂: List T)(x: List Bool)(f: T → SLang Bool)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)(nonzero: ∀(k: T) (bo: Bool), f k bo ≠ 0)(noninf: ∀(k: T) (bo: Bool), f k bo ≠ ⊤):(∏' (i : Fin ((l₁.length-1)+1)), f (l₁[i.val]'(by sorry)) (x[i.val]'(by sorry))) /
    (∏' (i : Fin ((l₂.length-1)+1)), f (l₂[i.val]'(by sorry)) (x[i.val]'(by sorry)))  = f (l₁[(a.length)]'(by sorry)) (x[a.length]'(by sorry)) / f (l₂[a.length]'(by sorry)) (x[a.length]'(by sorry)) := by
    rw[tprod_fintype]
    rw[tprod_fintype]
    rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₁.length-1)+1)) => f (l₁[b.val]'(by sorry)) (x[b.val]'(by sorry))) a.length]

    have ind: a.length < x.length := by
      rw[← hx]
      rw[h1]
      simp
    conv =>
      enter[1,2]
      rw[Fin.prod_univ_succAbove (fun (b: Fin ((l₂.length-1)+1)) => f (l₂[b.val]'(by sorry)) (x[b.val]'(by sorry))) a.length]
    have helper:  ∀i : Fin (l₁.length - 1), l₁[(Fin.succAbove a.length i).val]'(by sorry) = l₂[Fin.succAbove a.length i]'(by sorry) := by
      intro i
      simp only [h1,h2]
      by_cases i < a.length
      case pos h =>
        unfold Fin.succAbove
        have h' : i.castSucc < ↑a.length := by
          rw [@Fin.castSucc_lt_iff_succ_le]
          rw [@Fin.le_iff_val_le_val]
          simp
          have mod: a.length % (l₁.length-1+1) = a.length := by
            rw[Nat.mod_eq_of_lt]
            rw[hx]
            rw[Nat.sub_add_cancel]
            exact ind
            rw[← hx]
            rw[h1]
            simp
            linarith
          rw[mod]
          simp[Nat.succ_le_of_lt h]



        simp only[h']
        simp only [↓reduceIte, Fin.coe_castSucc,
          Fin.getElem_fin]
        rw[List.getElem_append_left]
        rw[List.getElem_append_left]
        rw[List.getElem_append_left]
        rw[List.getElem_append_left]
        exact h
        simp[h]
        linarith
        simp[h]
        linarith
      case neg h =>
        unfold Fin.succAbove
        have h' : ¬ i.castSucc < ↑a.length := by
          simp at h
          simp
          rw [@Fin.le_castSucc_iff]
          apply Nat.lt_succ_of_le
          simp
          have mod: a.length % (l₁.length-1+1) = a.length := by
            rw[Nat.mod_eq_of_lt]
            rw[hx]
            rw[Nat.sub_add_cancel]
            exact ind
            rw[← hx]
            rw[h1]
            simp
            linarith
          rw[mod]
          exact h


        simp only[h']
        simp only [↓reduceIte, Fin.coe_castSucc,
          Fin.getElem_fin]
        rw[List.getElem_append_right]
        rw[List.getElem_append_right]
        simp
        simp
        linarith
        simp

        have ile : i < l₁.length - 1 := by exact i.is_lt
        simp[h1] at ile
        rw[tsub_lt_iff_left]
        exact ile
        simp at h
        exact h

        simp
        linarith
        simp

        have ile : i < l₁.length - 1 := by exact i.is_lt
        simp[h1] at ile
        rw[tsub_lt_iff_left]
        exact ile
        simp at h
        exact h

    have helper2: Fin (l₁.length - 1) = Fin (l₂.length - 1) := by aesop
    have helper3: l₁.length - 1 = l₂.length - 1 := by aesop
    have hlp: (∏ i : Fin (l₁.length - 1), f l₁[(Fin.succAbove a.length i).val] x[↑(Fin.succAbove a.length i).val]) = ∏ i : Fin (l₂.length - 1), f l₂[(Fin.succAbove a.length i).val] x[(Fin.succAbove a.length i).val] := by
      apply Fintype.prod_equiv (Equiv.cast (congr_arg Fin helper3))
      simp[helper]
      intro i
      congr
      rw [← propext cast_eq_iff_heq]
      rw [← propext cast_eq_iff_heq]
    rw[hlp]
    rw[ENNReal.mul_div_mul_right]
    simp
    have mod: a.length % (l₁.length-1+1) = a.length := by
      rw[Nat.mod_eq_of_lt]
      rw[hx]
      rw[Nat.sub_add_cancel]
      exact ind
      rw[← hx]
      rw[h1]
      simp
      linarith
    simp[mod]
    rw[hx] at mod
    rw[← hy] at mod
    simp[mod]

    rw[Finset.prod_ne_zero_iff]
    intro i
    simp[nonzero]

    rw[← lt_top_iff_ne_top]
    apply ENNReal.prod_lt_top
    intro i
    simp[noninf]













lemma reduction (l₁ l₂: List T)(x: List Bool)(f: T → SLang Bool)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length)(nonzero: f (k: T) (bo: Bool) ≠ 0)(noninf: f (k: T) (bo: Bool) ≠ ⊤):(∏' (i : Fin l₁.length), f (l₁[i.val]) (x[i.val])) /
    ∏' (i : Fin l₂.length), f (l₂[i.val]) (x[i.val])  = f (l₁[(a.length)]'(by sorry)) (x[a.length]'(by sorry)) / f (l₂[a.length]'(by sorry)) (x[a.length]'(by sorry)) := by
    rw[List.append_assoc] at h1
    rw[List.append_assoc] at h2
    let c := List.take a.length x
    have c_def : c = List.take a.length x := rfl
    let d := List.drop a.length x
    have d_def : d = List.drop a.length x := by rfl
    have leq: a.length < x.length := by {
      rw[← hx]
      rw[h1]
      simp
    }
    have ac: a.length = c.length := by {
      rw[c_def]
      rw[List.length_take]
      rw[min_eq_left_of_lt leq]
    }
    rw[prod_split f l₁ a ([n]++b) x c d (by exact h1) (by rw[List.take_append_drop a.length x]) (by simp[hx]) (by exact ac)]
    rw[prod_split f l₂ a ([m]++b) x c d (by exact h2) (by rw[List.take_append_drop a.length x]) (by simp[hy]) (by exact ac)]
    rw[@tprod_fintype]
    rw[ENNReal.mul_div_mul_left]
    let e := List.take ([n].length) d
    have e_def : e = List.take [n].length d := by rfl
    let g := List.drop ([n].length) d
    rw[prod_split f ([n]++b) [n] b d e g (by rfl) (by rw[List.take_append_drop])]
    rw[prod_split f ([m]++b) [m] b d e g (by rfl) (by rw[List.take_append_drop])]
    rw[@tprod_fintype]
    rw[ENNReal.mul_div_mul_right]
    simp only [List.length_singleton, Fin.coe_fin_one, List.getElem_cons_zero]
    rw [tprod_fintype]
    rw [@Fin.prod_univ_one]
    rw [@Fin.prod_univ_one]
    rw [h1]
    rw [h2]
    rw[List.getElem_append_right]
    case h =>
      simp
    case h'' =>
      simp
    rw[List.getElem_append_right a]
    case h =>
      simp
    case h'' =>
      simp
    simp
    have xx : x = c++(e++g) := by
    {
    rw[List.take_append_drop]
    rw[List.take_append_drop]
    }
    rw[xx]
    rw[List.getElem_append_right]


    rw[List.getElem_append_left]
    simp [ac]

    case h =>
      rw[ac]
      simp
      rw[e_def]
      simp
      rw[d_def]
      simp
      exact leq
    case h' =>
      rw[ac]
      simp
      left
      rw[e_def]
      simp
      rw[d_def]
      simp
      exact leq
    case h =>
      rw[ac]
      simp

    case xl =>
      rw[d_def]
      simp
      rw[← hx]
      rw[h1]
      simp
    case ac =>
      rw[e_def]
      rw[d_def]
      simp
      have aux: 1 ≤ x.length - a.length := by linarith [Nat.sub_pos_of_lt leq]
      simp[aux]
    case xl =>
      rw[d_def]
      simp
      rw[← hx]
      rw[h1]
      simp
    case ac =>
      rw[e_def]
      simp
      rw[d_def]
      simp
      have aux: 1 ≤ x.length - a.length := by linarith [Nat.sub_pos_of_lt leq]
      simp[aux]
    case hc =>
      rw[@tprod_fintype]
      rw [@Finset.prod_ne_zero_iff]
      intro a ha
      sorry

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
                        rw[reduction l₁ l₂ x (RRSingleSample query num den h ) hl₁ hl₂ xlen3 xlen2]
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
                        {aesop}
                        {aesop}

| false => simp at xlen1
           rw [←Ne.eq_def] at xlen1
           have numerator_zero: RRSample_PMF query num den h l₁ x = 0 := by
            rw [RRSamplePMF_diff_lengths]
            exact xlen1
           rw [numerator_zero]
           rw [@ENNReal.zero_div]
           simp
