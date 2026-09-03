/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Queries.ReportNoisyMax.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Privacy

/-!
# Privacy of `privReportNoisyMax`

This file proves that the Report-Noisy-Max mechanism with discrete Laplace noise
is `(ε₁/ε₂)`-pure-DP, regardless of the number of candidates.

The proof follows Dwork–Roth Claim 3.9 (adapted from Exponential to Laplace
noise): condition on the noises of all losers, reduce to a one-dimensional
Laplace tail-shift on the winner's noise, and observe that swapping `D` for a
neighbour `D'` shifts the winner's threshold by at most `2Δ`.
-/

noncomputable section

open Classical Nat Int Real ENNReal

namespace SLang

variable {T : Type}

lemma Fin.argmax_succ (n' : ℕ) (f : Fin (n'+2) → ℤ) :
    Fin.argmax (n'+1) f =
      (let prev := Fin.argmax n' (fun i => f i.castSucc)
       if f (Fin.last (n'+1)) < f prev.castSucc then prev.castSucc else Fin.last (n'+1)) :=
  rfl

lemma Fin.lt_succ_or_last {n : ℕ} (j : Fin (n+2)) :
    (∃ k : Fin (n+1), j = k.castSucc) ∨ j = Fin.last (n+1) := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with h | h
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr (Fin.ext (by simp [h]))

lemma Fin.argmax_eq_iff (n : ℕ) (f : Fin (n+1) → ℤ) (i : Fin (n+1)) :
    Fin.argmax n f = i ↔
      (∀ j : Fin (n+1), j.val > i.val → f j < f i) ∧
      (∀ j : Fin (n+1), j.val < i.val → f j ≤ f i) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    refine ⟨fun _ => ⟨fun j hj => ?_, fun j hj => ?_⟩, fun _ => ?_⟩
    · have := j.isLt; rw [hi] at hj; omega
    · have := j.isLt; rw [hi] at hj; omega
    · simp [Fin.argmax, hi]
  | succ n IH =>
    rw [Fin.argmax_succ]
    dsimp only
    set prev := Fin.argmax n (fun j => f j.castSucc)
    have IHprev := (IH (fun j => f j.castSucc) prev).mp rfl
    refine ⟨fun Heq => ?_, fun ⟨H1, H2⟩ => ?_⟩
    · split_ifs at Heq with hlt
      all_goals subst Heq
      · refine ⟨fun j Hj => ?_, fun j Hj => ?_⟩
        · rcases Fin.lt_succ_or_last j with ⟨k, rfl⟩ | rfl
          · exact IHprev.1 k Hj
          · simpa using hlt
        · rcases Fin.lt_succ_or_last j with ⟨k, rfl⟩ | rfl
          · exact IHprev.2 k Hj
          · simp at Hj; exact absurd prev.isLt (by omega)
      · push Not at hlt
        refine ⟨fun j Hj => ?_, fun j Hj => ?_⟩
        · have := j.isLt; simp at Hj; omega
        · rcases Fin.lt_succ_or_last j with ⟨k, rfl⟩ | rfl
          · refine le_trans ?_ hlt
            rcases lt_trichotomy k.val prev.val with h | h | h
            · exact IHprev.2 _ h
            · rw [show k = prev from Fin.ext h]
            · exact (IHprev.1 _ h).le
          · simp at Hj
    · split_ifs with hlt
      · refine Fin.ext ?_
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · rcases Fin.lt_succ_or_last i with ⟨k, rfl⟩ | rfl
          · linarith [IHprev.1 k h, H2 prev.castSucc h]
          · linarith [H2 prev.castSucc h]
        · rcases Fin.lt_succ_or_last i with ⟨k, rfl⟩ | rfl
          · linarith [IHprev.2 k h, H1 prev.castSucc h]
          · exact absurd h (by have := prev.isLt; simp)
      · push Not at hlt
        refine Fin.ext ?_
        by_contra hne
        rcases Fin.lt_succ_or_last i with ⟨k, rfl⟩ | rfl
        · have hilast : (Fin.last (n+1)).val > k.castSucc.val := by simp; omega
          have hH1 := H1 (Fin.last (n+1)) hilast
          by_cases heq : k = prev
          · rw [heq] at hH1; linarith
          · rcases lt_or_gt_of_ne (fun h => heq (Fin.ext h)) with h | h
            · linarith [IHprev.2 _ h]
            · linarith [IHprev.1 _ h]
        · exact hne rfl

lemma fin_eq_iff_castSucc_last {n : ℕ} (f : Fin (n+2) → ℤ) (rest : Fin (n+1) → ℤ) (last : ℤ) :
    f = (fun (i : Fin (n+2)) => if h : i.val < n+1 then rest ⟨i.val, h⟩ else last) ↔
      (∀ j : Fin (n+1), f j.castSucc = rest j) ∧ f (Fin.last (n+1)) = last := by
  refine ⟨fun h => ?_, fun ⟨h_rest, h_last⟩ => ?_⟩
  · refine ⟨fun j => ?_, ?_⟩
    · rw [h]; simp [j.isLt]
    · rw [h]; simp
  · funext i
    by_cases hi : i.val < n+1
    · rw [dif_pos hi, ← h_rest ⟨i.val, hi⟩]; rfl
    · rw [dif_neg hi, ← h_last]
      congr 1
      exact Fin.ext (by have := i.isLt; simp; omega)

lemma privNoisedFamily_apply : ∀ (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) (f : Fin (n+1) → ℤ),
    (privNoisedFamily n s Δ ε₁ ε₂ l) f =
      ∏ i : Fin (n+1), (privNoisedQueryPure (s i) (2 * Δ) ε₁ ε₂ l) (f i) := by
  intro n
  induction n with
  | zero =>
    intro s Δ ε₁ ε₂ l f
    rw [privNoisedFamily, PMF.bind_apply, tsum_eq_single (f 0)]
    · rw [PMF.pure_apply, if_pos, mul_one, Fin.prod_univ_one]
      funext i; rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp i.isLt)]
    · intro b hb
      rw [PMF.pure_apply, if_neg, mul_zero]
      exact fun hc => hb ((congrFun hc 0).symm)
  | succ n' IH =>
    intro s Δ ε₁ ε₂ l f
    rw [privNoisedFamily, PMF.bind_apply, Fin.prod_univ_castSucc]
    simp_rw [PMF.bind_apply, PMF.pure_apply]
    conv_lhs =>
      enter [1, rest, 2]
      rw [tsum_eq_single (f (Fin.last (n'+1))) fun b hb => by
        rw [if_neg, mul_zero]
        exact fun hc => hb ((fin_eq_iff_castSucc_last f rest b).mp hc).2.symm]
    conv_lhs => enter [1, rest]; rw [show ∀ x y z : ENNReal, x * (y * z) = y * (x * z) from
                                     fun _ _ _ => by ring]
    rw [ENNReal.tsum_mul_left,
        tsum_eq_single (fun j : Fin (n'+1) => f j.castSucc) fun b hb => by
          rw [if_neg, mul_zero]
          refine fun hc => hb (funext fun j => ?_)
          exact (((fin_eq_iff_castSucc_last f b _).mp hc).1 j).symm]
    have heq : f = (fun (i : Fin (n'+2)) =>
        if h : i.val < n'+1 then (fun (j : Fin (n'+1)) => f j.castSucc) ⟨i.val, h⟩
        else f (Fin.last (n'+1))) :=
      (fin_eq_iff_castSucc_last f _ _).mpr ⟨fun _ => rfl, rfl⟩
    rw [if_pos heq, mul_one, IH (fun i => s i.castSucc) Δ ε₁ ε₂ l (fun j => f j.castSucc)]
    ring

lemma tsum_pi_shift {n : ℕ} (Δfn : Fin (n+1) → ℤ) (g : (Fin (n+1) → ℤ) → ENNReal) :
    (∑' f : Fin (n+1) → ℤ, g f) = (∑' f : Fin (n+1) → ℤ, g (fun i => f i + Δfn i)) := by
  refine tsum_eq_tsum_of_ne_zero_bij (fun x i => x.1 i + Δfn i) ?_ ?_ (fun _ => rfl)
  · intro x y hxy
    funext i
    have := congrFun hxy i
    simp at this; omega
  · intro x hx
    refine ⟨⟨fun i => x i - Δfn i, ?_⟩, funext fun i => by simp⟩
    have heq : (fun i => x i - Δfn i + Δfn i) = (x : Fin (n+1) → ℤ) := funext fun i => by omega
    simp only [Function.mem_support, heq]; exact hx

def shiftToL₂ {n : ℕ} (iStar : Fin (n+1)) (s : Fin (n+1) → List T → ℤ) (Δ : ℕ+)
    (l₁ l₂ : List T) : Fin (n+1) → ℤ :=
  fun i => if i = iStar then s iStar l₁ - s iStar l₂ - 2 * Δ else s i l₁ - s i l₂

@[simp] lemma shiftToL₂_self {n : ℕ} (iStar : Fin (n+1)) (s : Fin (n+1) → List T → ℤ)
    (Δ : ℕ+) (l₁ l₂ : List T) :
    shiftToL₂ iStar s Δ l₁ l₂ iStar = s iStar l₁ - s iStar l₂ - 2 * Δ := by simp [shiftToL₂]

@[simp] lemma shiftToL₂_of_ne {n : ℕ} {iStar i : Fin (n+1)} (hi : i ≠ iStar)
    (s : Fin (n+1) → List T → ℤ) (Δ : ℕ+) (l₁ l₂ : List T) :
    shiftToL₂ iStar s Δ l₁ l₂ i = s i l₁ - s i l₂ := by simp [shiftToL₂, hi]

lemma sensitivity_abs_le {q : List T → ℤ} {Δ : ℕ+} (Hsens : sensitivity q Δ)
    {l₁ l₂ : List T} (Hn : Neighbour l₁ l₂) : |((q l₁ - q l₂ : ℤ))| ≤ (Δ : ℤ) := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast Hsens l₁ l₂ Hn

lemma argmax_preserved_after_shift {n : ℕ} {s : Fin (n+1) → List T → ℤ} {Δ : ℕ+}
    {l₁ l₂ : List T} (Hn : Neighbour l₁ l₂) (Hsens : ∀ i, sensitivity (s i) Δ)
    (iStar : Fin (n+1)) {f : Fin (n+1) → ℤ}
    (h : Fin.argmax n (fun i => f i + shiftToL₂ iStar s Δ l₁ l₂ i) = iStar) :
    Fin.argmax n f = iStar := by
  rw [Fin.argmax_eq_iff] at h ⊢
  obtain ⟨H_above, H_below⟩ := h
  have abs_winner := abs_le.mp (sensitivity_abs_le (Hsens iStar) Hn)
  refine ⟨fun j Hj => ?_, fun j Hj => ?_⟩
  all_goals
    have hjne : j ≠ iStar := fun heq => by rw [heq] at Hj; exact lt_irrefl _ Hj
    have abs_loser := abs_le.mp (sensitivity_abs_le (Hsens j) Hn)
  · have := H_above j Hj
    rw [shiftToL₂_of_ne hjne, shiftToL₂_self] at this
    linarith
  · have := H_below j Hj
    rw [shiftToL₂_of_ne hjne, shiftToL₂_self] at this
    linarith

lemma loser_density_eq {q : List T → ℤ} {Δ ε₁ ε₂ : ℕ+} {l₁ l₂ : List T} (x : ℤ) :
    (privNoisedQueryPure q (2*Δ) ε₁ ε₂ l₁) (x + (q l₁ - q l₂)) =
    (privNoisedQueryPure q (2*Δ) ε₁ ε₂ l₂) x := by
  simp only [privNoisedQueryPure, DiscreteLaplaceGenSamplePMF, DFunLike.coe]
  rw [DiscreteLaplaceGenSample_periodic, DiscreteLaplaceGenSample_periodic]
  congr 1; ring

lemma winner_density_le {q : List T → ℤ} {Δ ε₁ ε₂ : ℕ+} {l₁ l₂ : List T} {ε : NNReal}
    (HN : (ε₁ : NNReal) / ε₂ = ε) (x : ℤ) :
    (privNoisedQueryPure q (2*Δ) ε₁ ε₂ l₁) (x + (q l₁ - q l₂ - 2 * Δ)) ≤
    ENNReal.ofReal (Real.exp ε) * (privNoisedQueryPure q (2*Δ) ε₁ ε₂ l₂) x := by
  simp only [privNoisedQueryPure, DiscreteLaplaceGenSamplePMF, DFunLike.coe]
  rw [DiscreteLaplaceGenSample_periodic, DiscreteLaplaceGenSample_periodic,
      show (x + (↑(q l₁) - ↑(q l₂) - 2 * ↑Δ) - ↑(q l₁) : ℤ) = (x - ↑(q l₂)) + (-(2 * ↑Δ)) by ring]
  have hlap := laplace_inequality_sub ε₁ ε₂ (x - ↑(q l₂)) (-(2 * ↑Δ)) (2 * Δ)
  simp only [DiscreteLaplaceGenSamplePMF, DFunLike.coe, DiscreteLaplaceGenSample_periodic,
             sub_zero] at hlap
  refine hlap.trans (_root_.mul_le_mul_left ?_ _)
  refine ENNReal.ofReal_le_ofReal (Real.exp_monotone (le_of_eq ?_))
  rw [← HN]
  push_cast [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Δ)]
  field_simp

theorem privReportNoisyMax_DP (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+)
    (ε : NNReal) (HN : laplace_pureDP_noise_priv ε₁ ε₂ ε)
    (Hsens : ∀ i, sensitivity (s i) Δ) :
    PureDPSystem.prop (privReportNoisyMax n s Δ ε₁ ε₂) ε := by
  unfold laplace_pureDP_noise_priv at HN
  simp only [DPSystem.prop, PureDP]
  apply singleton_to_event
  unfold DP_singleton
  intro l₁ l₂ Hn iStar
  apply ENNReal.div_le_of_le_mul
  unfold privReportNoisyMax
  show (PMF.bind _ _) iStar ≤ _ * (PMF.bind _ _) iStar
  rw [PMF.bind_apply, PMF.bind_apply]
  simp_rw [PMF.pure_apply]
  conv_lhs => enter [1, f]; rw [privNoisedFamily_apply n s Δ ε₁ ε₂ l₁ f]
  conv_rhs => enter [2, 1, f]; rw [privNoisedFamily_apply n s Δ ε₁ ε₂ l₂ f]
  rw [tsum_pi_shift (shiftToL₂ iStar s Δ l₁ l₂), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun f => ?_
  by_cases hf : Fin.argmax n (fun i => f i + shiftToL₂ iStar s Δ l₁ l₂ i) = iStar
  swap
  · rw [if_neg fun h => hf h.symm, mul_zero]; exact _root_.zero_le _
  rw [if_pos hf.symm, if_pos (argmax_preserved_after_shift Hn Hsens iStar hf).symm,
      mul_one, mul_one,
      ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ iStar),
      ← Finset.prod_erase_mul Finset.univ
        (fun i => (privNoisedQueryPure (s i) (2*Δ) ε₁ ε₂ l₂) (f i)) (Finset.mem_univ iStar)]
  have h_losers : ∀ i ∈ Finset.univ.erase iStar,
      (privNoisedQueryPure (s i) (2*Δ) ε₁ ε₂ l₁) (f i + shiftToL₂ iStar s Δ l₁ l₂ i) =
      (privNoisedQueryPure (s i) (2*Δ) ε₁ ε₂ l₂) (f i) := fun i hi => by
    rw [shiftToL₂_of_ne (Finset.ne_of_mem_erase hi)]; exact loser_density_eq _
  have h_winner :
      (privNoisedQueryPure (s iStar) (2*Δ) ε₁ ε₂ l₁) (f iStar + shiftToL₂ iStar s Δ l₁ l₂ iStar) ≤
      ENNReal.ofReal (Real.exp ε) * (privNoisedQueryPure (s iStar) (2*Δ) ε₁ ε₂ l₂) (f iStar) := by
    rw [shiftToL₂_self]; exact winner_density_le HN _
  rw [Finset.prod_congr rfl h_losers, mul_left_comm]
  exact _root_.mul_le_mul_right h_winner _

theorem privReportNoisyMaxSPMF_DP (n : ℕ) (s : Fin (n+1) → List T → ℤ) (Δ ε₁ ε₂ : ℕ+)
    (ε : NNReal) (HN : laplace_pureDP_noise_priv ε₁ ε₂ ε)
    (Hsens : ∀ i, sensitivity (s i) Δ) :
    PureDPSystem.prop (privReportNoisyMaxSPMF n s Δ ε₁ ε₂) ε := by
  have heq : (fun l => privReportNoisyMaxSPMF n s Δ ε₁ ε₂ l) =
             (fun l => (privReportNoisyMax n s Δ ε₁ ε₂ l : SPMF _)) := by
    funext l
    apply Subtype.ext
    exact privReportNoisyMaxSLang_eq n s Δ ε₁ ε₂ l
  rw [show privReportNoisyMaxSPMF n s Δ ε₁ ε₂ = _ from heq]
  exact privReportNoisyMax_DP n s Δ ε₁ ε₂ ε HN Hsens

end SLang

end
