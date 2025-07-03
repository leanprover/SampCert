import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.Samplers.Bernoulli.Properties
/- import SampCert.DifferentialPrivacy.Local.ENNRealCoercions -/

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

def RRSingleSample2  {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
  let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
  return Bool.xor (query l) r

def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample on an entire dataset. -/
 l.mapM (fun x => RRSingleSample query num den h x)

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

lemma nil_case {T : Type} (query : T -> Bool) (num : Nat) (den: PNat) (h: 2 * num ≤ den):
  ∑' (b : List Bool), (RRSample2 query num den h) [] b = 1 := by
    have h1: ∑' (b : List Bool), mapM (fun x => RRSingleSample2 query num den h x) [] b =
             mapM (fun x => RRSingleSample2 query num den h x) [] [] := by
              rw [@List.mapM_nil]
              simp_all only [pure, SLang.pure_apply, ↓reduceIte]
              rw [ENNReal.tsum_eq_add_tsum_ite []]
              simp_all only [↓reduceIte, ite_self, tsum_zero, add_zero]
    rw[RRSample2]
    rw[h1]
    rw [@List.mapM_nil]
    simp

lemma cons_case {T: Type} (query : T -> Bool) (num : Nat) (den: PNat) (h : 2 * num ≤ den)
  (hd : T) (tl : List T): ∑' (b : List Bool), RRSample2 query num den h (hd :: tl) b =
                          ∑' (b : List Bool), RRSample2 query num den h (hd :: tl) b = 1
      sorry


lemma RRSample2_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) :
  HasSum (RRSample2 query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    induction l.length with
    | zero => have h1: l.length = 0 := b
              sorry
              /- exact nil_case query num den h -/
    | succ n ha => exact ha

/- At this point, we should be set to prove that RRSample is normalized and that it is
   differentially private. The definition is computable, as we need. -/
def RRSample_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : PMF (List Bool) :=
  ⟨RRSample2 query num den h l, RRSample2_PMF_helper query num den h l⟩
