import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.Samplers.Bernoulli.Properties
import SampCert.DifferentialPrivacy.Pure.Local.LawfulMonadSLang
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithUpdateNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.DPProof
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.PMFProperties
import SampCert.DifferentialPrivacy.Pure.Local.ENNRealLemmasSuite

namespace RandomizedResponse

open SLang
open ENNRealLemmas

lemma pnat_zero_imp_false (den : PNat): (den : Nat) = 0 -> False := by aesop

lemma RRSingleSample_true_true {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = true):
  RRSingleSample query num den h l true = (den + 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  aesop
  sorry /- This is arithmetically true, but proving arithmetic things is a mess -/

lemma RRSingleSample_true_false {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = true):
  RRSingleSample query num den h l false = (den - 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.true_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.false_eq, Bool.not_eq_false', mul_ite, ↓reduceIte,
    mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  apply Eq.refl

lemma RRSingleSample_false_true {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = false):
  RRSingleSample query num den h l true = (den - 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.false_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.true_eq, Bool.not_eq_true', mul_ite,
    Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  apply Eq.refl

lemma RRSingleSample_false_false {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = false):
  RRSingleSample query num den h l false = (den + 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.false_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.false_eq, mul_ite, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  /- This is the same state as the first lemma that's not working,
     again it's just annoying arithmetic. -/
  sorry

lemma RRSingleSample_non_zero {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (b : Bool):
  RRSingleSample query num den h l b ≠ 0 := by
  simp [RRSingleSample, RRSinglePushForward]
  cases hb : b == query l with
  | true => simp at hb
            subst hb
            simp
            rw [@tsub_eq_zero_iff_le]
            rw [@Mathlib.Tactic.PushNeg.not_le_eq]
            apply quot_lt_one_rev
            norm_cast
            rw [PNat.mul_coe]
            simp_all only [PNat.val_ofNat]
            sorry
  | false => simp at hb
             rw [← Bool.eq_not_of_ne hb]
             intro j
             apply And.intro
             trivial
             apply And.intro
             {norm_cast
              rw [@Nat.sub_eq_zero_iff_le]
              linarith
            }
             {exact ne_of_beq_false rfl}

lemma RRSingleSample_finite {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (b : Bool):
  RRSingleSample query num den h l b ≠ ⊤ := by
  have hden: ↑(NNReal.ofPNat den) ≠ (0 : ENNReal) := by
                rw [@ne_iff_lt_or_gt]
                apply Or.inr
                simp_all only [NNReal.ofPNat, Nonneg.mk_natCast, gt_iff_lt, ENNReal.coe_pos, Nat.cast_pos]
                apply den.2
  cases hb: b with
  | true => cases hq: query l with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hq]
                apply div_ne_top
                exact Ne.symm (ne_of_beq_false rfl)
                refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?true.true.h2.h1 ?true.true.h2.h2
                aesop
                exact hden
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hq]
                 apply div_ne_top
                 aesop
                 refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?true.false.h2.h1 ?true.false.h2.h2
                 aesop
                 exact hden
  | false => cases hq: query l with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hq]
                apply div_ne_top
                aesop
                refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?false.true.h2.h1 ?false.true.h2.h2
                aesop
                exact hden
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hq]
                 apply div_ne_top
                 rw [@ENNReal.add_ne_top]
                 apply And.intro
                 aesop
                 exact Ne.symm (ne_of_beq_false rfl)
                 refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?false.false.h2.h1 ?false.false.h2.h2
                 aesop
                 exact hden

lemma RRSamplePushForward_diff_lengths (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : List Bool) (l₂ : List Bool) (hlen : l₁.length ≠ l₂.length):
  RRSamplePushForward num den h l₁ l₂ = 0 := by
  induction l₁ generalizing l₂ with
  | nil => simp [RRSamplePushForward, -mapM]
           aesop
  | cons hd tl ih =>
  simp [RRSamplePushForward, -mapM]
  simp [RRSamplePushForward, -mapM] at ih
  apply And.intro
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]

lemma RRSample_diff_lengths {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : List T) (l₂ : List Bool) (hlen : l₁.length ≠ l₂.length):
  RRSample query num den h l₁ l₂= 0 := by
  induction l₁ generalizing l₂ with
  | nil => simp [RRSample, -mapM]
           aesop
  | cons hd tl ih =>
  simp [RRSample, -mapM]
  simp [RRSample, -mapM] at ih
  apply And.intro
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]

lemma RRSamplePMF_diff_lengths {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (l₁ : List T) (l₂ : List Bool) (hlen : l₁.length ≠ l₂.length):
  RRSample_PMF query num den h l₁ l₂ = 0 := RRSample_diff_lengths query num den h l₁ l₂ hlen

lemma mwi1 (n : Nat) (f : Fin n -> Real): ∏ (i : Fin n), f i = ∏ (i : Fin (n + 1 - 1)), f i := by congr

lemma mwi2 (n : Nat) (f : Real -> Real) (l : List Real) (h : l.length < n): ∏ (i : Fin n), f (l[i]'(by sorry)) = ∏ (i : Fin (n + 1 - 1)), f (l[i]' (by sorry)) := by congr

lemma valid_index1 (n : Nat) (l : List Real) (h : l.length < n) (i : Fin n): i.val < l.length := by
  sorry

lemma valid_index2 (n : Nat) (l : List Real) (h : l.length < n) (i : Fin (n + 1 - 1)): i.val < l.length := by
  sorry

lemma mwi3 (n : Nat) (f : Real -> Real) (l : List Real) (h : l.length < n): ∏ (i : Fin n), f (l[i]'(by apply valid_index1; apply h)) = ∏ (i : Fin (n + 1 - 1)), f (l[i]' (by apply valid_index2; apply h)) := by congr
