import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
/- import SampCert.DifferentialPrivacy.Local.ENNRealCoercions -/

lemma arith_0 (num : Nat) (den : PNat) (_ : 2 * num ≤ den): den - 2*num ≤ 2 * den := by
  simp_all only [tsub_le_iff_right]
  linarith

def RRSingleSample  {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) : SLang Bool := do
  let r ← SLang.BernoulliSample (den - 2*num) (2 * den) (arith_0 num den h)
  return Bool.xor (query l) r

def RRSample {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : SLang (List Bool) := do
/- RRSample uses monadic map to apply RRSingleSample2 on an entire dataset. -/
 l.mapM (fun x => RRSingleSample query num den h x)

def RRSample2 {T : Type} (query : T -> Bool) (s : SeedType /- fix -/): SLang (List Bool) := do
  sorry
/- At this point, we should be set to prove that RRSample is normalized and that it is
   differentially private. The definition is computable, as we need. -/

#check SLang.BernoulliSample_normalizes

lemma RRSingleSample2_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : T) :
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

lemma RRSample2_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) :
  HasSum (RRSample query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    rw[RRSample]
    induction l with
    | nil => exact nil_case query num den h
    | cons hd tl tail_ih => sorry

def RRSample_PMF {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num ≤ den) (l : List T) : PMF (List Bool) :=
  ⟨RRSample query num den h l, RRSample2_PMF_helper query num den h l⟩
