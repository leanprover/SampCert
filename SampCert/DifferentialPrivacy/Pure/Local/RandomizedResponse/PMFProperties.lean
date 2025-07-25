import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.Samplers.Bernoulli.Properties

open SLang
open RandomizedResponse

#check RandomizedResponse.RRSingleSample
#check SLang.BernoulliSample_normalizes

lemma RRSinglePushForward_PMF (num : Nat) (den : PNat) (h: 2 * num < den) (l : Bool) :
  HasSum (RRSinglePushForward num den h l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  rw [@tsum_bool]
  rw[RRSinglePushForward]
  cases l
  {
      simp_all only [bind, pure, Bool.false_bne, SLang.bind_apply, ENNReal.natCast_sub,
      Nat.cast_mul, Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, SLang.pure_apply, Bool.false_eq, mul_ite,
      Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, Bool.true_eq]
      rw[←SLang.BernoulliSample_normalizes (den - 2 * num) (2 * den) (arith_0 num den h)]
      rw[tsum_bool]
  }
  {   simp_all only [bind, pure, Bool.true_bne, SLang.bind_apply, ENNReal.natCast_sub,
      Nat.cast_mul, Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, SLang.pure_apply, Bool.false_eq, Bool.not_eq_false',
      mul_ite, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, Bool.true_eq, Bool.not_eq_true', Bool.false_eq_true]
      rw[←SLang.BernoulliSample_normalizes (den - 2 * num) (2 * den) (arith_0 num den h)]
      rw[tsum_bool]
      rw [@AddCommMonoidWithOne.add_comm]
  }

lemma RRSingleSample_PMF_helper {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) :
  HasSum (RRSingleSample query num den h l) 1 := by
    rw [RRSingleSample]
    apply RRSinglePushForward_PMF

lemma RRSample_PMF_helper [LawfulMonad SLang] {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) :
  HasSum (RRSample query num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    unfold RRSample
    apply Norm_func_norm_on_list
    intro a
    rw [← Summable.hasSum_iff ENNReal.summable]
    apply RRSingleSample_PMF_helper

lemma RRSamplePushForward_PMF_helper [LawfulMonad SLang] (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool) :
  HasSum (RRSamplePushForward num den h l) 1 := by
    rw [Summable.hasSum_iff ENNReal.summable]
    unfold RRSamplePushForward
    apply Norm_func_norm_on_list
    intro a
    rw [← Summable.hasSum_iff ENNReal.summable]
    apply RRSinglePushForward_PMF

def RRSample_PMF [LawfulMonad SLang] {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) : PMF (List Bool) :=
  ⟨RRSample query num den h l, RRSample_PMF_helper query num den h l⟩
