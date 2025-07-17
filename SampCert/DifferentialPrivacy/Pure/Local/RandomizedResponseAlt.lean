import SampCert
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.Samplers.Bernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.Local.LawfulMonadSLang
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.SLang
/-import SampCert.DifferentialPrivacy.Local.MultiBernoulli -/

open SLang
/- open MultiBernoulli -/

lemma arith_0 (num : Nat) (den : PNat) (_ : 2 * num ≤ den): den - 2*num ≤ 2 * den := by
  simp_all only [tsub_le_iff_right]
  linarith

/- Eventually, we may want query to return more than just a Boolean -/
def RRSingleSample  {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
  let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
  return Bool.xor (query l) r

lemma RRSingleSample_true_true {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) (hq : query l = true):
  RRSingleSample query num den h l true = (den + 2 * num) / (2 * den) := by
  rw[RRSingleSample]
  simp_all only [bind, pure, Bool.true_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.true_eq, Bool.not_eq_true', mul_ite,
    Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  sorry /- This is arithmetically true, but proving arithmetic things is a mess -/

lemma RRSingleSample_true_false {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) (hq : query l = true):
  RRSingleSample query num den h l false = (den - 2 * num) / (2 * den) := by
  rw[RRSingleSample]
  simp_all only [bind, pure, Bool.true_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.false_eq, Bool.not_eq_false', mul_ite, ↓reduceIte,
    mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  apply Eq.refl

lemma RRSingleSample_false_true {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) (hq : query l = false):
  RRSingleSample query num den h l true = (den - 2 * num) / (2 * den) := by
  rw[RRSingleSample]
  simp_all only [bind, pure, Bool.false_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.true_eq, Bool.not_eq_true', mul_ite,
    Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  apply Eq.refl

lemma RRSingleSample_false_false {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) (hq : query l = false):
  RRSingleSample query num den h l false = (den + 2 * num) / (2 * den) := by
  rw[RRSingleSample]
  simp_all only [bind, pure, Bool.false_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.false_eq, mul_ite, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  /- This is the same state as the first lemma that's not working,
     again it's just annoying arithmetic. -/
  sorry

lemma RRSingleSample_non_zero {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) (b : Bool):
  RRSingleSample query num den h l b ≠ 0 := by
  cases hb: b with
  | true => cases hq: query l with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hq]
                sorry
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hq]
                 sorry
  | false => cases hq: query l with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hq]
                sorry
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hq]
                 sorry

def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample2 on an entire dataset. -/
 l.mapM (fun x => RRSingleSample query num den h x)

/- def RRSample2 {T : Type} (query : T -> Bool) (seed_list : List SeedType) (l : List T): SLang (List Bool) := do
  let r ← MultiBernoulliSample seed_list
  return List.zipWith (fun u s => Bool.xor (query u) s) l r -/

/- At this point, we should be set to prove that RRSample is normalized and that it is
   differentially private. The definition is computable, as we need. -/

lemma RRSingleSample_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) :
  HasSum (RRSingleSample query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    rw [@tsum_bool]
    rw[RRSingleSample]
    cases query l
    {
      simp_all only [bind, pure, Bool.false_bne, SLang.bind_apply, ENNReal.natCast_sub,
      Nat.cast_mul, Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, SLang.pure_apply, Bool.false_eq, mul_ite,
      Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, Bool.true_eq]
      rw[←SLang.BernoulliSample_normalizes (den - 2 * num) (2 * den) (arith_0 num den h)]
      rw[tsum_bool]
    }
    {
      simp_all only [bind, pure, Bool.true_bne, SLang.bind_apply, ENNReal.natCast_sub,
      Nat.cast_mul, Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, SLang.pure_apply, Bool.false_eq, Bool.not_eq_false',
      mul_ite, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, Bool.true_eq, Bool.not_eq_true', Bool.false_eq_true]
      rw[←SLang.BernoulliSample_normalizes (den - 2 * num) (2 * den) (arith_0 num den h)]
      rw[tsum_bool]
      rw [@AddCommMonoidWithOne.add_comm]
    }

lemma nil_case {T : Type} (query : T -> Bool) (num : Nat) (den: PNat) (h: 2 * num ≤ den):
  ∑' (b : List Bool), (RRSample query num den h) [] b = 1 := by
    have h1: ∑' (b : List Bool), mapM (fun x => RRSingleSample query num den h x) [] b =
             mapM (fun x => RRSingleSample query num den h x) [] [] := by
              rw [@List.mapM_nil]
              simp_all only [pure, SLang.pure_apply, ↓reduceIte]
              rw [ENNReal.tsum_eq_add_tsum_ite []]
              simp_all only [↓reduceIte, ite_self, tsum_zero, add_zero]
    rw[RRSample]
    rw[h1]
    rw [@List.mapM_nil]
    simp

lemma cons_case {T: Type} (query : T -> Bool) (num : Nat) (den: PNat) (h : 2 * num ≤ den)
  (l : List T) : ∑' (b : List Bool), RRSample query num den h l b = 1 := by
    rw[RRSample]
    sorry

/- This should now follow from Renee's abstraction of the MultiBernoulli proof -/
lemma RRSample_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) :
  HasSum (RRSample query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    rw[RRSample]
    induction l with
    | nil => exact nil_case query num den h
    | cons hd tl tail_ih => sorry

/- lemma RRSample2_PMF_helper {T : Type} (query: T -> Bool) (s : List SeedType) (l : List T) :
  HasSum (RRSample2 query s l) 1 := by
  rw[RRSample2]
  simp_all only [bind, pure]
  rw[Summable.hasSum_iff ENNReal.summable]
  rw[←MultiBernoulliSample_normalizes s]
  simp_all only [bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
  sorry
-/


def RRSample_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : PMF (List Bool) :=
  ⟨RRSample query num den h l, RRSample_PMF_helper query num den h l⟩



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

lemma RRSample_rec (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (hd: T)(tl : List T)(b: Bool)(c: List Bool):
RRSample query num den h (hd::tl) (b::c) = RRSingleSample query num den h hd b * RRSample query num den h tl c := by
unfold RRSample
set f := fun x => RRSingleSample query num den h x
rw[mapM_dist_cons f b c hd tl]





lemma prod_of_ind_prob(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num ≤ den)(a: List Bool)(l: List T)(k: l.length = a.length):
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

theorem prod_of_ind_prob_PMF(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num ≤ den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample_PMF query num den h l a = (∏'(i: Fin l.length), RRSingleSample query num den h (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob


open Classical

theorem singleton_to_event2 (m : Mechanism T U) (ε : ℝ) (h : DP_singleton_withUpdateNeighbour m ε) :
  DP_withUpdateNeighbour m ε := by
  simp [DP_withUpdateNeighbour]
  simp [DP_singleton_withUpdateNeighbour] at h
  intros l₁ l₂ h1 S
  replace h1 := h l₁ l₂ h1
  have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0) / (if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal ε.exp := by
    aesop
  have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
    aesop
  have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
    intro b
    right
    simp
    exact Real.exp_pos ε
  have D := fun { x : U } => @ENNReal.div_le_iff_le_mul (if x ∈ S then m l₁ x else 0) (if x ∈ S then m l₂ x else 0) (ENNReal.ofReal ε.exp) (B (if x ∈ S then m l₂ x else 0)) (C (if x ∈ S then m l₂ x else 0))
  have E := fun x : U => D.1 (A x)
  have F := ENNReal.tsum_le_tsum E
  rw [ENNReal.tsum_mul_left] at F
  rw [← ENNReal.div_le_iff_le_mul] at F
  · clear h1 A B C D
    trivial
  · aesop
  · right
    simp
    exact Real.exp_pos ε

lemma list_index_trans (T : Type)(l a b : List T)(x: List Bool)(i : Fin b.length)(h1 : l = a++b)(h2 : l.length ≤ x.length)
(h3: a.length ≤ x.length)(h4: b.length ≤ x.length): a.length + ↑i < x.length := by
  subst h1
  simp_all only [List.length_append]
  have htrans : ↑i < b.length := by simp
  have htrans2 : a.length + ↑i < a.length + b.length := by simp_all only [Fin.is_lt, add_lt_add_iff_left]
  rw []
  sorry



lemma prod_split (f: T → SLang Bool)(l : List T)(x: List Bool)(a b : List T)(hl: l = a++b)(h1: l.length ≤  x.length)(h2: a.length ≤ x.length)(h3: b.length ≤ x.length):
 ∏' (i : Fin l.length), f (l[i.val]) (x[i.val]) = (∏'(i : Fin a.length), f (a[i.val]) (x[i.val]))*(∏'(i : Fin b.length), f (b[i.val]) ((x[(a.length+i.val)]'(by sorry)))) := by sorry


lemma prod_split_left (f: T → SLang Bool)(l : List T)(x: List Bool)(a b : List T)(hl: l = b++a)(h1: l.length ≤  x.length)(h2: a.length ≤ x.length)(h3: b.length ≤ x.length):
 ∏' (i : Fin l.length), f (l[i.val]) (x[i.val]) = (∏'(i : Fin a.length), f (a[i.val]) (x[i.val]))*(∏'(i : Fin b.length), f (b[i.val]) ((x[(a.length+i.val)]'(by sorry)))) := by sorry
#check ENNReal.div_self

lemma quot_gt_one (a b : ENNReal): 1 < a/b -> b < a := by
  intro h
  cases hb: b == 0 with
  | true => simp at hb
            sorry
  | false => sorry


lemma mult_ne_top (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ ⊤): a * b ≠ ⊤ := by
  sorry

lemma div_ne_top (a b : ENNReal) (h1 : a ≠ ⊤) (h2 : b ≠ 0): a / b ≠ ⊤ := by
  sorry

lemma div_div_cancel (a b c : ENNReal) (h : c ≠ 0 ∧ c ≠ ⊤): a/c = b/c -> a = b := by
  intro h1
  sorry

lemma pnat_zero_imp_false (den : PNat): (den : Nat) = 0 -> False := by aesop

lemma final_bound (query : T -> Bool) (num : Nat) (den : PNat) (h : 2 * num ≤ den) (a a' : T) (b : Bool):
  RRSingleSample query num den h a b / RRSingleSample query num den h a' b
  < (den + 2 * num) / (den - 2 * num) := by
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
                 {sorry}
                 {rw [@ENNReal.div_ne_zero]
                  apply And.intro
                  simp
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
      cases hqa' : query a' with(l : T)(ls: List T
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                -- arithmetic now
                sorry
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 -- arithmetic now
                 sorry

open Finset
open scoped BigOperators

lemma append_empty_eq_og (l: List T) : l++[]=l:= by simp
lemma empty_append_eq_og (l: List T) : []++l=l:= by simp
lemma prod_of_one (x: Bool)(f: T → SLang Bool)(l : T) : ∏' (i : Fin ([l].length)), f [l][i.val] [x][i.val] = f l x := by
  simp_all only [List.length_singleton, Fin.coe_fin_one, List.getElem_cons_zero]
  rw [tprod_fintype]
  rw [@Fin.prod_univ_one]
lemma list_fin (ls: List T)(xs : List Bool) (i : Fin ls.length)(h : ls.length = xs.length) : i.val < xs.length :=by
  rw[← h]
  simp

lemma list_len_0_then_empty (l : List T) (h: l.length = 0) : l =[] :=by simp_all only [List.length_eq_zero]
lemma list_head_nonempty (l : List T)(h1: l ≠ []) : 0 < l.length :=by
  rw [List.length_pos_iff_ne_nil]
  exact h1



lemma prod_ENNReal (a : List ENNReal)(h : a≠ []) : ∏' (b: Fin a.length), a[b.val] = (a[0]'(by sorry)) * ∏' (b : Fin (a.tail).length), (a.tail[b.val]'(by sorry)) := by
  induction a with
  | nil => simp_all only [ne_eq, not_true_eq_false]
  | cons ah t x =>
    rw[tprod_fintype]
    rw[tprod_fintype]
    simp_all only [List.getElem_cons_zero, List.tail_cons,
      Fin.prod_univ_get]
    simp_all only [ne_eq, not_false_eq_true, List.prod_cons]

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




  /-ls with
  | nil =>
    induction xs with
    | nil =>
      simp_all only [List.getElem_cons_zero, List.length_nil, tprod_empty,
        mul_one]
      rw [prod_of_one]
    | cons => sorry
  | cons lh lt h1 =>
    induction xs with
    | nil => sorry
    |cons xh xt h2 =>
      rw []
      list_index_tran -/



lemma ennreal_mul_div_mul_comm (a b c d: ENNReal) : a*b/(c*d) = (a/c) *(b/d) := by sorry


lemma prod_div (x: List Bool)(f: T → SLang Bool)(l₁ l₂ : List T) (hx: l₁.length = x.length)(hy: l₂.length = x.length) :
(∏' (i : Fin l₁.length), f (l₁[i.val]) (x[i.val])) / ∏' (i : Fin l₂.length), f (l₂[i.val]) (x[i.val])
= ∏' (i : Fin l₂.length), f (l₁[i.val]) (x[i.val]) / f (l₂[i.val]) (x[i.val]) := by
  have hw : l₁.length = l₂.length := by simp_all only
  induction l₁ with
  | nil =>
    induction l₂ with
    | nil => simp_all only [List.length_nil, tprod_empty, div_one]
    | cons h tl hz =>
      apply False.elim
      have rw_false: (([] : List T).length = (h :: tl).length) ↔ (([] : List T).length ≠ (h :: tl).length -> False) := by aesop
      rw[rw_false] at hw
      apply hw
      have lhs_empty: ([] : List T).length = 0 := by rw [@List.length_eq_zero]
      rw[lhs_empty]
      aesop
  | cons ah t a =>
    induction l₂ with
    | nil =>
      apply False.elim
      have rw_false: ((ah::t).length = ([]: List T).length) ↔ ((ah::t).length ≠ ([]: List T).length -> False) := by aesop
      rw[rw_false] at hw
      apply hw
      have rhs_empty: ([] : List T).length = 0 := by rw [@List.length_eq_zero]
      rw[rhs_empty]
      aesop
    | cons bh bt b =>
      induction x with
      | nil => sorry
      | cons x xt h =>
        rw [head_tail_prod x xt bh bt f hy]
        rw [head_tail_prod x xt ah t f hx]
        rw [ENNReal.mul_div_right_comm]







        sorry







  | cons h t h3 =>



#check Finset.prod


lemma reduction (l₁ l₂: List T)(x: List Bool)(f: T → SLang Bool)(nonzero : f (k:T) (bo : Bool) ≠ 0) (noninf : f (k:T) (bo:Bool) ≠ ⊤)(h1: l₁ = a++[n]++b)(h2: l₂ = a++[m]++b)(hx: l₁.length = x.length)(hy: l₂.length = x.length):(∏' (i : Fin l₁.length), f (l₁[i.val]) (x[i.val])) /
    ∏' (i : Fin l₂.length), f (l₂[i.val]) (x[i.val])  = f (l₁[a.length]'(by sorry)) (x[a.length]'(by sorry)) / f (l₂[a.length]'(by sorry)) (x[a.length]'(by sorry)) := by
  induction a with
  | nil =>
    induction b with
    | nil =>
      simp_all [append_empty_eq_og, empty_append_eq_og]
    | cons bh bt b=> sorry
  | cons h t a =>
    induction b with
    | nil => sorry
    | cons ba bt b => sorry










theorem RRSample_is_DP (query: T → Bool)(num: Nat)(den:PNat)(h: 2*num ≤ den) :
DP_withUpdateNeighbour (RRSample_PMF query num den h) (Real.log ((1/2 + num / den) / (1/2 - num / den))) := by
-- let ε := ↑num / NNReal.ofPNat den
apply singleton_to_event2
intros l₁ l₂ h_adj x
cases xlen1 : l₁.length == x.length with
| true =>
          rw[prod_of_ind_prob_PMF query num den h x l₁ (by aesop)]
          rw[prod_of_ind_prob_PMF query num den h x l₂ (by sorry)]
          cases h_adj with
          | Update hl₁ hl₂ =>
                        rename_i a n b m
                        have hlen: l₁.length = l₂.length := by aesop
                        have xlen2 : l₂.length = x.length := by aesop
                        simp
                        have xlen3 : l₁.length = x.length := by aesop
                        rw[reduction l₁ l₂ x (RRSingleSample query num den h ) hl₁ hl₂ xlen3 xlen2]




| false => sorry


-- rw[reduction l₁ l₂ x (RRSingleSample query num den h) hl₁ hl₂ xlen xlen2]
