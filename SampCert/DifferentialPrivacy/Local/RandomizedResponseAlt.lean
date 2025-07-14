import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.Samplers.Bernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.Local.LawfulMonadSLang


lemma arith_0 (num : Nat) (den : PNat) (_ : 2 * num ≤ den): den - 2*num ≤ 2 * den := by
  simp_all only [tsub_le_iff_right]
  linarith

def RRSingleSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
/- RRSingleSample takes in a single user and produces a sample according to the distribution
   induced by the user's actual response.
   If the user's actual response to the query is "true", then RRSingleSample samples "true"
   with probability 1/2 + num/den. If the user's actual response to the query is "false," then RRSingleSample
   samples true with probability 1/2 - num/den.
-/
  match query l with
  | true => let r ← SLang.BernoulliSample (den + 2 * num) (2 * den) (by linarith)
            return r
  | false => let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
              return r

def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample on an entire dataset. -/
 l.mapM (fun x => RRSingleSample query num den h x)

def RRSingleSample2  {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
  let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
  return Bool.xor (query l) r

def RRSample2 {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample2 on an entire dataset. -/
 l.mapM (fun x => RRSingleSample2 query num den h x)

 lemma RRSingleSample2_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) :
  HasSum (RRSingleSample2 query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    rw [@tsum_bool]
    rw[RRSingleSample2]
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

lemma RRSample2_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) :
  HasSum (RRSample2 query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    induction l.length with
    | zero => have h1: l.length = 0 := by
              sorry
              /- exact nil_case query num den h -/
    | succ n ha => exact ha
/- At this point, we should be set to prove that RRSample is normalized and that it is
   differentially private. The definition is computable, as we need. -/
def RRSample_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : PMF (List Bool) :=
  ⟨RRSample2 query num den h l, RRSample2_PMF_helper query num den h l⟩
-- namespace SLang


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
RRSample2 query num den h (hd::tl) (b::c) = RRSingleSample2 query num den h hd b * RRSample2 query num den h tl c := by
unfold RRSample2
set f := fun x => RRSingleSample2 query num den h x
rw[mapM_dist_cons f b c hd tl]





lemma prod_of_ind_prob(query: T → Bool)(num: Nat)(den:PNat)(h: 2*num ≤ den)(a: List Bool)(l: List T)(k: l.length = a.length):
RRSample2 query num den h l a = (∏'(i: Fin l.length), RRSingleSample2 query num den h (l.get i) (a.get (Fin.cast k i ))):= by
induction l generalizing a with
| nil =>
  simp
  rw[List.length_nil] at k
  symm at k
  apply List.eq_nil_of_length_eq_zero at k
  rw[k]
  unfold RRSample2
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
RRSample_PMF query num den h l a = (∏'(i: Fin l.length), RRSingleSample2 query num den h (l.get i) (a.get (Fin.cast k i ))):= by apply prod_of_ind_prob

namespace SLang


theorem RRSample_is_DP (query: T → Bool)(num: Nat)(den:PNat)(h: 2*num ≤ den) :
PureDP (RRSample_PMF query num den h) ((num: NNReal) / den) := by
-- let ε := ↑num / NNReal.ofPNat den
apply singleton_to_event
intros l₁ l₂ h_adj x
rw[prod_of_ind_prob_PMF query num den h x l₁]
rw[prod_of_ind_prob_PMF query num den h x l₂]
sorry
