/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Mathlib.Data.List.Fold
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Code

noncomputable section
open Classical

namespace SLang

section helpers

variable {sv_T : Type}

lemma SPMF_sum_one (p : SPMF ℤ) : ∑' (a : ℤ), p a = 1 := by
  rw [← Summable.hasSum_iff ENNReal.summable]
  exact p.2

/--
Bijection-style tsum equality. Local replacement for a previously-removed mathlib
lemma of the same name. Stated in terms of `Equiv.tsum_eq`.
-/
theorem tsum_eq_tsum_of_ne_zero_bij {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {β γ : Type*} {f : β → α} {g : γ → α} (i : Function.support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
    (hf : Function.support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : ∑' x, f x = ∑' y, g y := by
  symm
  rw [← tsum_subtype_support g, ← tsum_subtype_support f]
  have hi' : Function.Injective i := fun x y h => Subtype.ext (hi h)
  have himem : ∀ x : Function.support g, i x ∈ Function.support f := by
    intro x
    rw [Function.mem_support, hfg]
    exact x.2
  let i' : Function.support g → Function.support f := fun x => ⟨i x, himem x⟩
  have hi'inj : Function.Injective i' := fun x y h => hi' (Subtype.ext_iff.mp h)
  have hi'surj : Function.Surjective i' := by
    intro ⟨b, hb⟩
    obtain ⟨x, hx⟩ := hf hb
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let e : Function.support g ≃ Function.support f :=
    Equiv.ofBijective i' ⟨hi'inj, hi'surj⟩
  rw [← Equiv.tsum_eq e]
  apply tsum_congr
  intro x
  show g x = f (i x)
  exact (hfg x).symm

/--
Stronger congruence rule for probBind: The bound-to functions have to be equal only on the support of
the bound-from function.
-/
lemma probBind_congr_strong (p : SLang T) (f : T -> SLang U) (g : T -> SLang U) (Hcong : ∀ t : T, p t ≠ 0 -> f t = g t) :
    p >>= f = p >>= g := by
  simp only [bind]
  unfold probBind
  apply SLang.ext
  intro u
  apply tsum_congr
  intro t
  by_cases hp : p t = 0
  · simp [hp]
  · rw [Hcong t hp]

lemma iSup_tsum_le_tsum_iSup (f : T -> U -> ENNReal) : ⨆ y, ∑' x, f x y ≤ ∑' x, ⨆ y, f x y  := by
  rw [iSup_le_iff]
  intro i
  apply ENNReal.tsum_le_tsum
  intro a
  apply le_iSup

lemma getLastI_eq_getLast (L : List ℤ) (H : L ≠ []) : L.getLastI = L.getLast H := by
  rw [List.getLastI_eq_getLast?_getD]
  rw [List.getLast?_eq_getLast_of_ne_nil H]
  rfl

lemma dropLast_append_getLastI (L : List ℤ) (H : L ≠ []) : L.dropLast ++ [L.getLastI] = L := by
  rw [getLastI_eq_getLast _ H]
  apply List.dropLast_append_getLast H

lemma cons_headI_tail {L : List ℤ} (H : L ≠ []) : List.headI L :: L.tail = L := by
  apply List.cons_head?_tail
  apply Option.mem_def.mpr
  cases L
  · exfalso
    simp at H
  simp

lemma tsum_comm_mul_left {α β : Type*} (f : α → ENNReal) (g : β → ENNReal) (h : α → β → ENNReal) :
    ∑' a, f a * ∑' b, g b * h a b = ∑' b, g b * ∑' a, f a * h a b := by
  conv =>
    lhs
    enter [1, a]
    rw [← ENNReal.tsum_mul_left]
    enter [1, b]
    rw [mul_left_comm]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

lemma ENNReal.tsum_lb_single (x : T) (f : T -> ENNReal)  (l : ENNReal) :
    l ≤ f x -> l ≤ ∑' (a : T), f a := by
  intro H
  apply le_trans H
  apply ENNReal.le_tsum

lemma ENNReal.tsum_lb_subset (P : T -> Prop) (f : T -> ENNReal)  (l : ENNReal) :
    l ≤ (∑'(a : {t : T // P t}), f a.1) -> l ≤ ∑' (a : T), f a := by
  intro H
  apply le_trans H
  apply ENNReal.tsum_comp_le_tsum_of_injective
  simp

lemma ENNReal.tsum_split (P : T -> Prop) (f : T -> ENNReal) :
    ∑' (a : T), f a = (∑'(a : {t : T // P t}), f a.1) + (∑'(a : {t : T // ¬P t}), f a.1) := by
  symm
  apply Summable.tsum_add_tsum_compl (f := f) (s := {t | P t}) <;> apply ENNReal.summable

def vsm_0 (x : {l : List ℤ // l.length = n + 1}) : ℤ :=
  List.headI x.1

def vsm_rest (x : {l : List ℤ // l.length = n + 1}) : {l : List ℤ // l.length = n } :=
  ⟨ List.tail x.1, by simp [x.2] ⟩

def vsm_last (x : {l : List ℤ // l.length = n + 1}) : ℤ :=
  List.getLastI x.1

def vsm_init (x : {l : List ℤ // l.length = n + 1}) : {l : List ℤ // l.length = n } :=
  ⟨ List.dropLast x.1, by simp [x.2] ⟩

lemma vector_sum_singleton (f : { l : List ℤ // l.length = 1 } -> ENNReal) :
    (∑'(x : { l : List ℤ // l.length =  1 }), f x) = (∑' (x : ℤ), f ⟨ [x], by simp ⟩) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i =>
    simp [Function.support]
    exact fun x => ⟨ [x.1], by simp ⟩
  · intro a y h
    have h' : ([(a : ℤ)] : List ℤ) = [(y : ℤ)] := congrArg Subtype.val h
    simpa using h'
  · simp [Function.support, Set.range]
    intro L HL HN
    cases L with
    | nil => simp at HL
    | cons v R =>
    cases R with
    | nil => exists v
    | cons => simp at HL
  · simp [Function.support]

lemma vector_sum_merge (n : ℕ) (f : ℤ × { l : List ℤ // l.length = n } -> ENNReal) :
    (∑'p, f p) = ∑'(p : {l : List ℤ // l.length = n + 1}), f (vsm_0 p, vsm_rest p) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i =>
    simp [Function.support]
    exact fun x => (vsm_0 x.1, vsm_rest x.1)
  · simp
    simp [vsm_0, vsm_rest]
    intro L1 HL1 HL1f L2 HL2 HL2f Heq1
    cases L1
    · simp at HL1
    cases L2
    · simp at HL2
    rename_i a1 t1 a2 t2
    have hf : ((a1 :: t1 : List ℤ).headI) = ((a2 :: t2 : List ℤ).headI) :=
      congrArg Prod.fst Heq1
    have hs : ((a1 :: t1 : List ℤ).tail) = ((a2 :: t2 : List ℤ).tail) :=
      congrArg (fun p => (Prod.snd p).val) Heq1
    simp at hf hs
    simp_all
  · simp [Function.support, Set.range]
    intro z L HL HF
    exists (z :: L)
    simp
    exists HL
  · simp [Function.support]

def geo_cdf (β : ENNReal) (n : ℕ) : ENNReal := 1 - (1 - β)^n

lemma ite_conv_left {P : Prop} {D} {a b c : ENNReal} (H : a = c) : @ite _ P D a b = @ite _ P D c b := by
  split <;> trivial

lemma ite_mono_left {P : Prop} {D} {a b c : ENNReal} (H : a ≤ c) : @ite _ P D a b ≤ @ite _ P D c b := by
  split <;> trivial

lemma ite_lemma_1 {P : Prop} {D} {f : T -> ENNReal} : ∑'(a : T), @ite _ P D (f a) 0 = @ite _ P D (∑'(a : T), f a) 0 := by
  split
  · rfl
  · simp

lemma geo_cdf_rec (β : ENNReal) (Hβ1: β ≤ 1) (n : ℕ) :
      geo_cdf β (n + 1) = β + (1 - β) * geo_cdf β n := by
  unfold geo_cdf
  suffices ENNReal.toReal (1 - (1 - β) ^ (n + 1)) = ENNReal.toReal (β + (1 - β) * (1 - (1 - β) ^ n)) by
    apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
    rcases this with heq | hne
    · exact heq
    rcases hne with ⟨A, B⟩ | ⟨A, _⟩
    · simp_all
      exfalso
      rcases B with hB | hB
      · simp_all
      · apply ENNReal.mul_eq_top.mp at hB
        simp_all
    · simp_all
  ring_nf
  have C1 : β ≠ ⊤ := by
    intro K
    simp_all
  have C3 : (1 - β) ^ (n + 1) ≤ 1 := by
    apply pow_le_one'
    apply tsub_le_self
  have C4 : (1 - β) ^ n ≤ 1 := by
    apply pow_le_one'
    apply tsub_le_self
  have C2 : (1 - β) * (1 - (1 - β) ^ n) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.sub_ne_top
      simp
    · apply ENNReal.sub_ne_top
      simp
  rw [ENNReal.toReal_add C2 C1]
  rw [ENNReal.toReal_mul]
  rw [← pow_succ']
  rw [ENNReal.toReal_sub_of_le C3 (by simp)]
  rw [ENNReal.toReal_sub_of_le Hβ1 (by simp)]
  rw [ENNReal.toReal_sub_of_le C4 (by simp)]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.toReal_sub_of_le Hβ1 (by simp)]
  rw [mul_sub]
  simp
  rw [pow_succ]
  linarith

/-- The supremum of the geometric CDF with parameter `ρ ∈ (0, 1]` tends to 1. -/
lemma iSup_geo_cdf_ge_one (ρ : ENNReal) (Hρ_nz : ρ ≠ 0) :
    1 ≤ ⨆ (y : ℕ), geo_cdf ρ y := by
  apply le_iSup_iff.mpr
  intro b H
  apply Classical.by_contradiction
  intro H1
  simp at H1
  have Hz : (∃ z, (1 - ρ)^z < 1 - b) := by
    have W := exists_pow_lt_of_lt_one (x := ENNReal.toNNReal (1 - b)) (y := ENNReal.toNNReal (1 - ρ)) ?G2 ?G1
    case G2 =>
      rw [ENNReal.toNNReal_pos_iff]
      apply And.intro
      · simp
        trivial
      · apply ENNReal.sub_lt_of_lt_add
        · exact le_of_lt H1
        · simp
    case G1 =>
      apply ENNReal.toNNReal_lt_of_lt_coe
      simp
      apply ENNReal.sub_lt_self
      · simp
      · simp
      · trivial
    rcases W with ⟨ N, HN ⟩
    exists N
    rw [← ENNReal.toNNReal_pow] at HN
    apply (ENNReal.toNNReal_lt_toNNReal _ _).mp
    · trivial
    · apply ENNReal.pow_ne_top
      apply ENNReal.sub_ne_top
      simp
    · apply ENNReal.sub_ne_top
      simp
  rcases Hz with ⟨ z, Hz ⟩
  have Hz' : 1 - (1 - ρ) ^ z > 1 - (1 - b) := by
    apply LT.lt.gt
    apply (ENNReal.sub_lt_iff_lt_right _ _).mpr
    · apply ENNReal.lt_add_of_sub_lt_left
      · left
        simp
      · apply Eq.trans_lt _ Hz
        apply ENNReal.sub_sub_cancel
        · simp
        apply Right.pow_le_one_of_le
        apply tsub_le_self
    · apply ENNReal.sub_ne_top
      simp
    · apply tsub_le_self
  have H' := H z
  have X : 1 - (1 - b) = b := by
    apply ENNReal.sub_sub_cancel
    · simp
    exact le_of_lt H1
  rw [X] at Hz'
  exact absurd Hz'.lt H'.not_gt

end helpers

section equiv

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]
variable {sv_T : Type}

lemma sv1_tsum_iSup_probWhileCut_comm (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) (τ v0 : ℤ):
     ∑' b, ⨆ i, probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) i ([], v0) b =
     ⨆ i, ∑' b, probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) i ([], v0) b := by
  rw [ENNReal.tsum_eq_iSup_sum]
  conv =>
    rhs
    enter [1, y]
    rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  apply iSup_congr
  intro s
  apply ENNReal.finsetSum_iSup_of_monotone
  intro a
  apply probWhileCut_monotonic

lemma sv1_loop_ub (qs : sv_query sv_T) (T τ : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) (cut : ℕ) : ∀ L : List ℤ, ∀ (v0 : ℤ), (∑' (x : sv1_state), probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) cut (L, v0) x ≤ 1) := by
  induction cut with
  | zero => simp [probWhileCut]
  | succ cut' IH =>
    intro L v0
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      simp [sv1_aboveThreshF, probBind]
      conv =>
        enter [1, 1, x]
        conv =>
          enter [1, a]
          rw [← ENNReal.tsum_mul_right]
          simp
        rw [ENNReal.tsum_comm]
        enter [1, b]

      apply
        @le_trans _ _ _
        (∑' (x : sv1_state) (b : ℤ), (privNoiseGuess ε₁ ε₂) b * probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) cut' (L ++ [v0], b) x)
        _ ?G5 ?G6
      case G5 =>
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_le_tsum
        intro b
        unfold sv1_state
        rw [ENNReal.tsum_eq_add_tsum_ite (L ++ [v0], b)]
        simp
        conv =>
          rhs
          rw [← add_zero (_ * _)]
        apply add_le_add
        · simp
        · simp
          intros
          aesop
      case G6 =>
        rw [ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left]
        apply @le_trans _ _ _ (∑' (b : ℤ), (privNoiseGuess ε₁ ε₂) b * 1)
        · apply ENNReal.tsum_le_tsum
          intro a
          gcongr
          apply IH
        · simp [SPMF_sum_one]
    · exact le_of_eq (probPure_norm _)


lemma sv1_ub (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    ∑'s, sv1_aboveThresh qs T ε₁ ε₂ l s ≤ 1 := by
  unfold sv1_aboveThresh
  unfold sv1_threshold
  simp
  -- Push the sum over s inwards
  conv =>
    rw [ENNReal.tsum_comm]
    enter [1, 1, b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    rw [ENNReal.tsum_comm]
    enter [1, i]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    rw [ENNReal.tsum_comm]
  apply
    @le_trans _ _ _
    (∑' (a : ℤ), (privNoiseThresh ε₁ ε₂) a * ∑' (a_1 : ℤ), (privNoiseGuess ε₁ ε₂) a_1 * 1)
    _ ?G2 ?G1
  case G1 =>
    apply Eq.le
    simp [SPMF_sum_one]
  case G2 =>
    apply ENNReal.tsum_le_tsum
    intro τ
    apply mul_le_mul_right
    apply ENNReal.tsum_le_tsum
    intro v0
    apply mul_le_mul_right

    apply
      @le_trans _ _ _
      (∑' (b : sv1_state), probWhile (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) ([], v0) b )
      _ ?G3 ?G4
    case G3 =>
      apply ENNReal.tsum_le_tsum
      intro a
      rw [tsum_ite_eq]
    case G4 =>
      unfold probWhile
      rw [sv1_tsum_iSup_probWhileCut_comm]
      apply iSup_le_iff.mpr
      intro cut
      apply sv1_loop_ub

/-
## Program version 2
  - Only moves the loop into a non-executable form, ie. explicitly defines the PMF
-/

def sv2_aboveThresh (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- probWhile (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) ([], v0)
    return (sv1_threshold sk)
  computation point

lemma sv1_sv2_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv1_aboveThresh qs T ε₁ ε₂ l = sv2_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext
  intro result
  simp [sv1_aboveThresh, sv2_aboveThresh]



/-
## Program version 3
  - Truncates the loop
-/

def sv3_loop (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List sv_T) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (point + 1) init

def sv3_aboveThresh (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- sv3_loop qs T ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point

def cone_of_possibility (cut : ℕ) (initial hist : List ℤ) : Prop :=
  (hist.length < cut + initial.length) ∧ (initial.length ≤ hist.length)

def constancy_at {qs : sv_query sv_T} {T : ℤ} {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List sv_T} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) : Prop :=
  probWhileCut (sv1_aboveThreshC qs T τ data) (sv1_aboveThreshF ε₁ ε₂) (1 + cut) (initial, v0) (hist, vk) =
  probWhileCut (sv1_aboveThreshC qs T τ data) (sv1_aboveThreshF ε₁ ε₂) cut       (initial, v0) (hist, vk)


-- All points outside of the cone are zero
lemma external_to_cone_zero :
    (¬ cone_of_possibility cut initial hist) ->
    probWhileCut (sv1_aboveThreshC qs T τ data) (sv1_aboveThreshF ε₁ ε₂) cut (initial, v0) (hist, vk) = 0 := by
  revert initial v0 vk
  induction cut
  · simp [probWhileCut, probZero]
  · next cut' IH =>
    intro intial v0 vk Hcut'
    simp only [probWhileCut]
    unfold probWhileFunctional
    split <;> simp [probBind]
    · intro h
      rcases h with ⟨ initial', vk' ⟩
      by_cases hexists : ∃ v', initial' = intial ++ [v']
      · rcases hexists with ⟨ v', Hinitial' ⟩
        right
        apply IH
        simp_all [cone_of_possibility]
        intro
        have Hcut'' := Hcut' (by linarith)
        linarith
      · left
        simp [sv1_aboveThreshF]
        intro i
        exact absurd ⟨v0, i⟩ hexists
    · apply SLang.pure_apply_of_ne
      intro H
      cases H
      simp_all [cone_of_possibility]

-- Base case: left edge of the cone satisfies constancy
lemma cone_left_edge_constancy {qs : sv_query sv_T} {T : ℤ} {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List sv_T} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    hist.length = initial.length ->
    cone_of_possibility cut initial hist ->
    @constancy_at _ _ _ qs T ε₁ ε₂ τ data v0 vk cut initial hist := by
  intro Hlen Hcone
  -- cut > 0 due to cone
  cases cut with
  | zero =>
    exfalso
    simp [cone_of_possibility] at Hcone
    simp_all only [lt_self_iff_false, le_refl, and_true]
  | succ cut' =>
  -- Unfold the first iterate
  unfold constancy_at
  simp only [probWhileCut]
  unfold probWhileFunctional

  cases (sv1_aboveThreshC qs T τ data (initial, v0))
  · -- False case: both programs terminate with initial state
    simp
  · -- True case: both programs step to a point outside of the cone, so are zero
    simp
    apply tsum_congr
    intro ⟨ initial', v1 ⟩

    simp [sv1_aboveThreshF]
    rw [← ENNReal.tsum_mul_right]
    rw [← ENNReal.tsum_mul_right]

    -- Ignore the cases when hist' is not a legal step
    by_cases hexists : ∃ v', initial' = initial ++ [v']
    swap
    · apply tsum_congr
      intro z
      split
      · next h' =>
        exfalso
        apply hexists
        exists v0
        cases h'
        assumption
      · simp
    rcases hexists with ⟨ _, Hv1' ⟩
    simp [Hv1']
    apply tsum_congr
    intro _

    -- Both branches are outside of the cone now
    rw [external_to_cone_zero (by simp_all [cone_of_possibility])]
    rw [external_to_cone_zero (by simp_all [cone_of_possibility])]

lemma cone_constancy {qs} {T : ℤ} {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List sv_T} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    cone_of_possibility cut initial hist ->
    @constancy_at _ _ _ qs T ε₁ ε₂ τ data v0 vk cut initial hist := by
  -- Need theorem to be true for all initial states, since this will increase during the induction
  -- v0 and vk will also change in ways which don't matter
  revert initial v0 vk

  induction cut
  · -- Not true base case (cut 0 is always outside of the cone)
    -- Mercifully it is easy to prove
    intro v0 vk initial Hcone
    unfold constancy_at
    simp [probWhileCut, probWhileFunctional]
    cases (sv1_aboveThreshC qs T τ data (initial, v0)) <;> simp [probBind, probZero]
    unfold cone_of_possibility at Hcone
    linarith

  next n IH =>
  intro v0 vk initial Hcone
  -- True base case: are we on the left-hand edge of the cone
  cases Classical.em (hist.length = initial.length) with
  | inl h => apply cone_left_edge_constancy <;> assumption
  | inr Hcone_interior =>

  -- If not, unfold the first (and only the first) level of the induction
  unfold constancy_at
  simp only [probWhileCut]
  unfold probWhileFunctional

  -- If the conditional is false, we are done
  cases hcond : (sv1_aboveThreshC qs T τ data (initial, v0))
  · simp


  -- If the conditional is true, we decrement N by one and add a sample to the history
  unfold constancy_at at IH
  simp
  apply tsum_congr
  intro ⟨ initial', vk' ⟩

  -- We only need to consider the cases where sv1_aboveThreshF is nonzero
  -- And this is exactly the case where initial' is initial plus one element
  simp [sv1_aboveThreshF]
  rw [← ENNReal.tsum_mul_right]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro z
  by_cases hexists : ∃ v', initial' = initial ++ [v']
  swap
  · split
    · next h2 =>
      exfalso
      apply hexists
      exists v0
      cases h2
      trivial
    · simp
  rcases hexists with ⟨ v', Hinitial' ⟩
  split <;> try simp
  next h =>
  cases h
  congr 1

  -- Apply the IH
  apply IH

  -- Prove that the new value is in the new cone of possibility
  unfold cone_of_possibility at Hcone
  rcases Hcone with ⟨ Hcone1, Hcone2 ⟩
  unfold cone_of_possibility
  apply And.intro
  · subst_vars
    simp
    linarith
  · subst_vars
    simp
    apply Nat.lt_iff_add_one_le.mp
    apply LE.le.eq_or_lt at Hcone2
    cases Hcone2
    · exfalso
      apply Hcone_interior
      symm
      trivial
    · trivial


lemma sv2_sv3_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv2_aboveThresh qs T ε₁ ε₂ l = sv3_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext

  -- Step through equal headers
  intro point
  unfold sv2_aboveThresh
  unfold sv3_aboveThresh
  unfold sv3_loop
  simp
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1
  apply tsum_congr
  intro final_state
  rcases final_state with ⟨ hist, vk ⟩
  split <;> try rfl
  next H =>
  simp [H, sv1_threshold]

  -- Apply a lemma about eventual constancy
  apply probWhile_apply
  apply tendsto_atTop_of_eventually_const (i₀ := hist.length + 1)
  intro i H

  -- i is in the cone, reduce by induction
  induction i with
  | zero => simp at H
  | succ i IH =>
    -- Real base case
    cases Classical.em (i = hist.length) with
    | inl heq => simp_all
    | inr hne =>
    -- Inductive case: use constancy
    rw [← IH ?G1]
    case G1 =>
      apply LE.le.ge
      apply GE.ge.le at H
      apply LE.le.lt_or_eq at H
      cases H with
      | inl h => exact Nat.le_of_lt_succ h
      | inr h => exact absurd (by linarith : i = hist.length) hne
    have HK := @cone_constancy _ _ _ qs T ε₁ ε₂ τ l v0 vk i [] hist
    unfold constancy_at at HK
    conv =>
      enter [1, 3]
      rw [add_comm]
    apply HK
    unfold cone_of_possibility
    simp
    apply GE.ge.le at H
    apply LE.le.lt_or_eq at H
    cases H with
    | inl h => linarith
    | inr h => exact absurd (by linarith : i = hist.length) hne



-- Commute out a single sample from the loop
lemma sv3_loop_unroll_1 (qs : sv_query sv_T) (T τ : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) (point : ℕ) (L : List ℤ) (vk : ℤ) :
    sv3_loop qs T ε₁ ε₂ τ l (point + 1) (L, vk) =
    (do
      let vk1 <- privNoiseGuess ε₁ ε₂
      if (sv1_aboveThreshC qs T τ l (L, vk))
        then (sv3_loop qs T ε₁ ε₂ τ l point (L ++ [vk], vk1))
        else probPure (L, vk)) := by
  conv =>
    lhs
    unfold sv3_loop
    simp [probWhileCut, probWhileFunctional]
  split
  · apply SLang.ext
    intro ⟨ HF, vkf ⟩
    simp [probBind]
    unfold sv3_loop
    conv =>
      enter [1, 1, a, 1]
      unfold sv1_aboveThreshF
      simp [probBind]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro a
    have tsum_eq_single' :
        ∀ (f : sv1_state → ENNReal) (x₀ : sv1_state),
          (∀ b, b ≠ x₀ → f b = 0) → (∑' b, f b) = f x₀ :=
      fun f x₀ hf => tsum_eq_single x₀ (fun b hb => hf b hb)
    rw [tsum_eq_single' _ (L ++ [vk], a) (fun b hb => by simp [probPure]; intro h; exact absurd h hb)]
    simp
    rfl
  · simp
    apply SLang.ext
    intro ⟨ HF, vkf ⟩
    simp [probBind]
    rw [ENNReal.tsum_mul_right, SPMF_sum_one, one_mul]

/-
## Program version 4
  - Executable
  - Presamples at each point, and then executes a deterministic loop
-/

-- An sv4 state is an sv1 state plus a list of presamples
def sv4_state : Type := sv1_state × List ℤ

def sv4_presample (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang { l : List ℤ // List.length l = n } :=
  match n with
  | Nat.zero => return ⟨ [], by simp ⟩
  | Nat.succ n' => do
    let vk1 <- privNoiseGuess ε₁ ε₂
    let vks  <- sv4_presample ε₁ ε₂ n'
    return ⟨ vks ++ [vk1], by simp [vks.2] ⟩


def sv4_aboveThreshF (s : sv4_state) : SLang sv4_state :=
  match s.2 with
  | [] => probZero
  | (p :: ps) => return ((s.1.1 ++ [s.1.2], p), ps)

def sv4_aboveThreshC (qs : sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (st : sv4_state) : Bool :=
  sv1_aboveThreshC qs T τ l st.1

def sv4_loop (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List sv_T) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  let presamples <- sv4_presample ε₁ ε₂ point
  let v <- probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (point + 1) (init, presamples)
  return v.1

/-- Total mass of a point distribution restricted to the states with a given
first component. -/
lemma tsum_indicator_pure (X : sv4_state) (fs : sv1_state) (h : fs = X.1) :
    (∑' (a : sv4_state), if fs = a.1 then probPure X a else 0) = 1 := by
  rw [tsum_eq_single X (fun b hb => by simp [SLang.pure_apply_of_ne _ _ hb, hb])]
  simp [h, SLang.pure_apply_self]

/-- When `sv4`'s loop condition fails the loop halts immediately. -/
lemma sv4_probWhileCut_succ_false (qs : sv_query sv_T) (T τ : ℤ) (l : List sv_T) (n : ℕ)
    (s : sv1_state) (ps : List ℤ) (h : ¬ sv1_aboveThreshC qs T τ l s = true) :
    probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (n + 1) (s, ps) =
    probPure (s, ps) := by
  have hC : ¬ sv4_aboveThreshC qs T τ l (s, ps) = true := h
  simp only [probWhileCut, probWhileFunctional]
  rw [if_neg hC]
  rfl

/-- One step of `sv4`'s loop: when the condition holds, the head presample is
consumed and the state advances. -/
lemma sv4_probWhileCut_succ (qs : sv_query sv_T) (T τ : ℤ) (l : List sv_T) (n : ℕ)
    (s : sv1_state) (p : ℤ) (ps : List ℤ) (h : sv1_aboveThreshC qs T τ l s = true) :
    probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (n + 1) (s, p :: ps) =
    probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF n ((s.1 ++ [s.2], p), ps) := by
  have hC : sv4_aboveThreshC qs T τ l (s, p :: ps) = true := h
  simp only [probWhileCut, probWhileFunctional, hC, if_true, sv4_aboveThreshF,
    Bind.bind, Pure.pure]
  exact SLang.pure_bind _ _

lemma sv3_loop_unroll_1_alt (qs : sv_query sv_T) (T τ : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) (point : ℕ) (initial_state : sv1_state) :
    sv3_loop qs T ε₁ ε₂ τ l (point + 1) initial_state =
    (do
      let vk1 <- privNoiseGuess ε₁ ε₂
      if (sv1_aboveThreshC qs T τ l initial_state)
        then (sv3_loop qs T ε₁ ε₂ τ l point (initial_state.1 ++ [initial_state.2], vk1))
        else probPure initial_state) := by
  rcases initial_state with ⟨ _ , _ ⟩
  rw [sv3_loop_unroll_1]

def len_list_append_rev {m n : ℕ} (x : { l : List ℤ // l.length = m }) (y: { l : List ℤ // l.length = n }) : { l : List ℤ // l.length = n + m } :=
  ⟨ x.1 ++ y.1 , by simp [x.2, y.2, add_comm] ⟩


lemma sv4_presample_eval (ε₁ ε₂ : ℕ+) (n : ℕ) (s : { l : List ℤ // List.length l = n }) :
    sv4_presample ε₁ ε₂ n ⟨ List.reverse s, by simp [s.2] ⟩ = List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂ b)) 1 s.1 := by
  rcases s with ⟨ s, Hs ⟩
  simp
  revert n
  induction s
  · intro n Hs
    simp_all
    simp at Hs
    unfold sv4_presample
    split
    · simp
    · exfalso
      simp at Hs
  · next s0 ss IH =>
    intro n Hs
    simp at Hs
    simp only [List.reverse_cons, List.foldl_cons]
    unfold sv4_presample
    cases n with
    | zero => exfalso; simp at Hs
    | succ n' =>
    generalize HF : (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) = F
    simp
    conv =>
      enter [1, 1, a]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i]
      simp
    rw [← ENNReal.tsum_prod]
    rw [ENNReal.tsum_eq_add_tsum_ite (s0, ⟨ ss.reverse, by simp; linarith ⟩)]
    conv =>
      rhs
      rw [← add_zero (List.foldl _ _ _ )]
      rw [add_comm]
    conv =>
      lhs
      rw [add_comm]
    congr 1
    · simp
      intro a a_1 _ Hneq Heq1 Heq2
      exfalso
      exact (Hneq Heq2.symm) Heq1.symm
    simp
    rw [IH _ ?G1]
    case G1 => linarith
    rw [HF]
    suffices (F (List.foldl F 1 ss) s0 = List.foldl F (F 1 s0) ss) by
      rw [← HF] at this
      simp at this
      rw [← HF]
      rw [← this]
      rw [mul_comm]
    haveI : RightCommutative F := by
      subst HF
      exact ⟨fun b a₁ a₂ => mul_right_comm _ _ _⟩
    rw [← List.foldl_cons]
    exact List.foldl_cons_eq_apply_foldl.symm

lemma sv4_presample_eval' (ε₁ ε₂ : ℕ+) (n : ℕ) (s : { l : List ℤ // List.length l = n }) :
    sv4_presample ε₁ ε₂ n s = List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂ b)) 1 (List.reverse s) := by
  have X := sv4_presample_eval ε₁ ε₂ n ⟨ List.reverse s, by simp [s.2] ⟩
  simp only [List.reverse_reverse, Subtype.coe_eta] at X
  trivial


-- Split in the other order, used as a helper function
lemma sv4_presample_split' (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ) (p : { l : List ℤ // List.length l = point }) :
    privNoiseGuess ε₁ ε₂ z * sv4_presample ε₁ ε₂ point p =
    sv4_presample ε₁ ε₂ (point + 1) ⟨ (p.1 ++ [z]), by simp [p.2] ⟩ := by
  rcases p with ⟨ L, HL ⟩
  revert HL
  induction L
  · intro HL
    simp at HL
    simp
    conv =>
      rhs
      unfold sv4_presample
    unfold sv4_presample
    split
    · simp
    · exfalso
      simp at HL

  · next L0 LL _ =>
    intro HL
    simp
    conv => rhs; unfold sv4_presample
    simp
    conv =>
      enter [2, 1, a]
      rw [← ENNReal.tsum_mul_left]
      enter [1, b]
      simp
    rw [← ENNReal.tsum_prod]
    rw [ENNReal.tsum_eq_add_tsum_ite (z, ⟨ L0 :: LL, HL ⟩)]
    conv => lhs; rw [← (add_zero (_ * _))]
    congr 1
    · simp
    · symm
      simp
      intro A B C D E
      exfalso
      apply (congrArg List.reverse) at E
      simp at E
      cases E
      apply D
      · symm
        trivial
      next E =>
      apply (congrArg List.reverse) at E
      simp at E
      symm
      trivial


lemma foldl_mul_left (g : ℤ → ENNReal) (a : ENNReal) (l : List ℤ) :
    List.foldl (fun acc b => acc * g b) a l = a * List.foldl (fun acc b => acc * g b) 1 l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, one_mul]
    rw [ih (a * g x), ih (g x), mul_assoc]

lemma sv4_presample_split'' (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ) (p : { l : List ℤ // List.length l = point })
    (HP : List.length (p.1 ++ [z]) = point + 1) :
    privNoiseGuess ε₁ ε₂ z * sv4_presample ε₁ ε₂ point p =
    sv4_presample ε₁ ε₂ (point + 1) ⟨ (p.1 ++ [z]), HP ⟩ := by rw [sv4_presample_split']

-- Splits and rearranges the functions
def sv4_presample_split (ε₁ ε₂ : ℕ+) (point : ℕ) :
    sv4_presample ε₁ ε₂ (point + 1) =
    (do
      let presample_1 <- sv4_presample ε₁ ε₂ 1
      let presample_r <- sv4_presample ε₁ ε₂ point
      return len_list_append_rev presample_1 presample_r) := by
  apply SLang.ext
  intro final_state
  simp [sv4_presample]
  conv =>
    enter [1, 1, a]
    rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  rw [vector_sum_singleton]

  have X (x : ℤ) : (∑' (x_1 : ℤ),
      @ite ENNReal (x_1 = x) (Classical.propDecidable _) 0
        (if x = x_1 then SLang.privNoiseGuess ε₁ ε₂ x_1 else 0)) = 0 := by
    rw [ENNReal.tsum_eq_zero]; intro x_1; split_ifs <;> simp_all
  conv =>
    enter [2, 1, x, 1]
    simp
  clear X
  simp
  conv =>
    enter [2, 1, x]
    rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  simp_all [len_list_append_rev]

  -- Join the sv4_presamples
  simp only [mul_ite, mul_zero, sv4_presample_split']
  rw [vector_sum_merge]
  rw [vector_sum_merge]

  -- Both sums are singletons
  simp [vsm_rest, vsm_0]
  symm
  rw [ENNReal.tsum_eq_add_tsum_ite final_state]
  conv =>
    rhs
    rw [← (zero_add (tsum _))]
  conv =>
    lhs
    rw [add_comm]
  congr 1
  · simp
    intro A B C
    right
    apply if_neg
    intro K
    apply C
    subst K
    apply Subtype.ext
    exact (cons_headI_tail (by intro K'; subst K'; simp at B)).symm

  rw [ENNReal.tsum_eq_add_tsum_ite ⟨[vsm_last final_state] ++ (vsm_init final_state), by simp [(vsm_init final_state).2, Nat.add_comm] ⟩ ]
  refine Eq.trans (zero_add _).symm ?_
  conv =>
    rhs
    rw [add_comm]
  congr 1
  · symm
    simp
    intro A B C
    apply if_neg
    intro K
    apply C
    subst K
    simp [vsm_last, vsm_init, List.getLastI_eq_getLast?_getD]
    exact (cons_headI_tail (by intro K'; subst K'; simp at B)).symm

  -- Apply the closed form to evaluate
  rcases final_state with ⟨ f, Hf ⟩
  simp [vsm_last, vsm_init]
  rw [sv4_presample_eval']
  rw [sv4_presample_eval']
  simp only []

  have Hfoldl_eq :
      ((privNoiseGuess ε₁ ε₂) f.headI *
         List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 f.tail.reverse =
       List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.dropLast ++ [f.getLastI]).reverse):= by
    have H0 : (privNoiseGuess ε₁ ε₂) f.headI *
        List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 f.tail.reverse =
        List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.tail ++ [f.headI]).reverse := by
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.foldl_cons, one_mul]
      rw [foldl_mul_left _ ((privNoiseGuess ε₁ ε₂) f.headI) f.tail.reverse]
    rw [H0]
    have rcomm : RightCommutative (fun (acc : ENNReal) (b : ℤ) => acc * (privNoiseGuess ε₁ ε₂) b) := by
      refine ⟨fun z x y => ?_⟩
      rw [mul_assoc, mul_assoc]
      congr 1
      rw [mul_comm]
    have Hperm : (f.tail ++ [f.headI]).reverse.Perm (f.dropLast ++ [f.getLastI]).reverse := by
      conv =>
        lhs
        simp
      have H1 : (f.headI :: f.tail.reverse).Perm (f.headI :: f.tail) := by
        apply List.Perm.cons f.headI
        apply List.reverse_perm
      trans
      · apply H1
      rw [cons_headI_tail ?G2]
      case G2 => intro _ ; simp_all
      rw [dropLast_append_getLastI _ ?G2]
      case G2 => intro _ ; simp_all
      apply List.Perm.symm
      apply List.reverse_perm
    exact Hperm.foldl_eq 1
  rw [Hfoldl_eq]
  clear Hfoldl_eq
  generalize HX : List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.dropLast ++ [f.getLastI]).reverse = X
  clear HX

  -- Both of the conditionals are true
  split
  · split
    · rfl
    · next _ hne =>
      exfalso; apply hne
      rw [dropLast_append_getLastI]; intro K; simp [K] at Hf
  · split
    · next hne _ =>
      exfalso; apply hne
      rw [cons_headI_tail]; intro K; simp [K] at Hf
    · rfl



def len_1_list_to_val (x : { l : List ℤ // l.length = 1 }) : ℤ :=
  match x with
  | ⟨ v :: _, _ ⟩ => v
  | ⟨ [], h ⟩ => absurd h (by simp)

-- When we do induction on point,
-- We will want to generalize over all init
-- Unfolding this loop just moves the first presample into init
-- Which can apply the IH-- since it's some arbitrary init state and a presamples state generated by one fewer point


lemma presample_norm_lemma  (point : ℕ) (ε₁ ε₂ : ℕ+) :
    ∑' (a : { l : List ℤ // l.length = point }), sv4_presample ε₁ ε₂ point a = 1 := by
  induction point
  · simp [sv4_presample]
    rw [ENNReal.tsum_eq_add_tsum_ite (⟨ [], by simp ⟩ : { l : List ℤ // l.length = 0 })]
    conv =>
      rhs
      rw [← add_zero 1]
    congr <;> simp
  · next n IH =>

    -- sv4_presample_split'
    suffices (∑' (a : ℤ × { l : List ℤ // l.length = n }), privNoiseGuess ε₁ ε₂ a.1 * sv4_presample ε₁ ε₂ n a.2 = 1) by
      conv at this =>
        enter [1, 1, a]
        rw [sv4_presample_split']
      rw [← this]
      symm
      rw [vector_sum_merge]
      simp only []
      simp [vsm_0, vsm_rest]
      symm
      apply @tsum_eq_tsum_of_ne_zero_bij
      case i =>
        simp [Function.support]
        exact fun x => ⟨ ↑(vsm_rest x.1) ++ [vsm_0 x.1], by simp [(vsm_rest x.1).2] ⟩
      · simp
        simp [vsm_0, vsm_rest]
        intro L1 HL1 HL1f L2 HL2 HL2f Heq
        cases L1
        · simp at HL1
        cases L2
        · simp at HL2
        rename_i a1 t1 a2 t2
        have h' : (t1 ++ [a1] : List ℤ) = (t2 ++ [a2]) := congrArg Subtype.val Heq
        have h2 := congrArg List.reverse h'
        simp at h2
        simp_all
      · simp [Function.support, Set.range]
        intro L1 HL1 Hf1
        exists ((vsm_last ⟨ L1, HL1 ⟩) :: (vsm_init ⟨ L1, HL1 ⟩))
        simp
        refine ⟨(vsm_init ⟨L1, HL1⟩).2, ?_, ?_⟩
        · simp [vsm_init, vsm_last]
          intro K
          apply Hf1
          rw [← K]
          congr
          symm
          apply dropLast_append_getLastI
          intro K
          simp [K] at HL1
        · simp [vsm_0, vsm_rest, vsm_init, vsm_last]
          apply dropLast_append_getLastI
          intro K
          simp [K] at HL1
      · simp [Function.support]
        intros
        congr
    rw [ENNReal.tsum_prod']
    conv =>
      enter [1, 1, a]
      simp
      rw [ENNReal.tsum_mul_left]
      rw [IH]
    simp

    exact SPMF_sum_one _


/-- Replacing a single `privNoiseGuess` sample with an equivalent presample of length 1 under an
`if sv1_aboveThreshC ...` guard. -/
lemma sv3_sv4_loop_presample_step (qs : sv_query sv_T) (T τ : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T)
    (point : ℕ) (init : sv1_state) :
    (do
      let vk1 ← privNoiseGuess ε₁ ε₂
      if sv1_aboveThreshC qs T τ l init = true
        then sv4_loop qs T ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
        else probPure init) =
    (do
      let vps ← sv4_presample ε₁ ε₂ 1
      let vk1 := len_1_list_to_val vps
      if sv1_aboveThreshC qs T τ l init = true
        then sv4_loop qs T ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
        else probPure init) := by
  apply SLang.ext
  intro final_state
  simp
  rw [vector_sum_singleton]
  apply tsum_congr
  intro x
  simp [len_1_list_to_val]
  simp [sv4_presample]

/-- Base case of `sv3_sv4_loop_eq`: at `point = 0`, both loops perform zero steps. -/
lemma sv3_sv4_loop_eq_zero (qs : sv_query sv_T) (T τ : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T)
    (init : sv1_state) :
    sv3_loop qs T ε₁ ε₂ τ l 0 init = sv4_loop qs T ε₁ ε₂ τ l 0 init := by
  simp [sv3_loop, sv4_loop, probWhileCut, probWhileFunctional, sv4_presample, sv4_aboveThreshC]
  split
  · next h =>
    simp [sv4_aboveThreshF, sv1_aboveThreshF]
    apply SLang.ext
    intro final_state
    simp [probBind, probZero, h]
  · next hcond =>
    apply SLang.ext
    intro final_state
    simp
    split
    · next h =>
      simp_all
      symm
      rw [condition_to_subset]
      rw [tsum_eq_single (⟨(init, []), rfl⟩ : ↑{a : sv4_state | init = a.1})]
      · exact pure_apply_self _
      · intro b hb
        rcases b with ⟨⟨b1, b2⟩, Hb⟩
        have Hb' : init = b1 := Hb
        subst Hb'
        apply pure_apply_of_ne
        intro Hk
        apply hb
        apply Subtype.ext
        exact Hk
    · next hk2 =>
      symm
      simp
      intro i H
      show (if sv1_aboveThreshC qs T τ l init = true then
              ((sv4_aboveThreshF (init, ([] : List ℤ))).probBind fun _ => probZero)
            else probPure (init, ([] : List ℤ))) i = 0
      rw [if_neg hcond]
      apply pure_apply_of_ne
      intro HK
      apply hk2
      rw [H, HK]

theorem sv3_sv4_loop_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List sv_T) (point : ℕ) (init : sv1_state) :
    sv3_loop qs T ε₁ ε₂ τ l point init = sv4_loop qs T ε₁ ε₂ τ l point init := by
  revert init
  induction point
  · intro init
    exact sv3_sv4_loop_eq_zero qs T τ ε₁ ε₂ l init
  · -- Inductive case
    next point IH =>
    intro init

    -- Unfold sv3_loop on the left
    rw [sv3_loop_unroll_1_alt]

    -- Apply the IH on the left
    have ApplyIH :
      ((do
        let vk1 ← privNoiseGuess ε₁ ε₂
        if sv1_aboveThreshC qs T τ l init = true
          then sv3_loop qs T ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else (SLang.probPure init) : SLang _) =
      ((do
        let vk1 ← privNoiseGuess ε₁ ε₂
        if sv1_aboveThreshC qs T τ l init = true
          then sv4_loop qs T ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else probPure init) : SLang _)) := by
      simp
      apply SLang.ext
      intro final_state
      simp
      apply tsum_congr
      intro _
      congr
      split
      · exact congrFun (IH _) final_state
      · rfl

    rw [ApplyIH]
    clear ApplyIH IH
    rw [sv3_sv4_loop_presample_step]

    -- Now, just need to prove this unfolding of sv4_loop
    unfold sv4_loop
    conv =>
      enter [2]
      unfold probWhileCut
      unfold probWhileFunctional
      unfold sv4_aboveThreshC

    split
    · conv =>
        enter [2]
        rw [sv4_presample_split]
      simp

      apply SLang.ext
      intro final_state
      simp
      apply tsum_congr
      intro vsample_1
      congr 1
      apply tsum_congr
      intro vsample_rest
      congr 1
      -- Commute out the indicator on final_state
      apply tsum_congr
      intro ⟨ ns_state, ns_presamples ⟩
      simp
      split <;> try simp
      next HF =>

      -- Investigate the RHS term for simplifications?
      rcases vsample_1 with ⟨ vs1, Hvs1 ⟩
      rcases vsample_rest with ⟨ vsr, Hvsr ⟩
      match vs1, Hvs1 with
      | [], Hvs1 => exact absurd Hvs1 (by simp)
      | vs1 :: vs_emp, Hvs1 =>
      conv =>
        enter [2, 1, a, 1]
        unfold sv4_aboveThreshF
        simp [len_list_append_rev]
      have Hemp : vs_emp = [] := by cases vs_emp <;> simp_all
      subst Hemp
      show probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (point + 1)
          ((init.1 ++ [init.2], vs1), vsr) (ns_state, ns_presamples) =
        probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (point + 1 + 1)
          (init, vs1 :: vsr) (ns_state, ns_presamples)
      exact (congrFun (sv4_probWhileCut_succ qs T τ l (point + 1) init vs1 vsr (by assumption))
        (ns_state, ns_presamples)).symm

    · conv =>
        enter [2]
        rw [sv4_presample_split]
      simp
      apply SLang.ext
      intro final_state
      simp
      apply tsum_congr
      intro v1
      split
      · next Hfs =>
        have Hcond : ¬ sv1_aboveThreshC qs T τ l init = true := by assumption
        have Hinner : ∀ (a : { l : List ℤ // l.length = point }),
            (∑' (a_1 : sv4_state),
              if final_state = a_1.1 then
                probWhileCut (fun st => sv1_aboveThreshC qs T τ l st.1) sv4_aboveThreshF
                  (point + 1 + 1) (init, (↑(len_list_append_rev v1 a) : List ℤ)) a_1
              else 0) = 1 := by
          intro a
          show (∑' (a_1 : sv4_state),
              if final_state = a_1.1 then
                probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF
                  (point + 1 + 1) (init, (↑(len_list_append_rev v1 a) : List ℤ)) a_1
              else 0) = 1
          rw [sv4_probWhileCut_succ_false qs T τ l (point + 1) init _ Hcond]
          exact tsum_indicator_pure _ _ Hfs
        simp only [Hinner, mul_one, presample_norm_lemma]
      · next Hfs =>
        have Hcond : ¬ sv1_aboveThreshC qs T τ l init = true := by assumption
        simp
        right
        intro a b
        right
        intro i Hi
        show probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (point + 1 + 1)
            (init, (↑(len_list_append_rev v1 ⟨a, b⟩) : List ℤ)) i = 0
        rw [sv4_probWhileCut_succ_false qs T τ l (point + 1) init _ Hcond]
        apply SLang.pure_apply_of_ne
        intro HK
        apply Hfs
        rw [Hi, HK]

def sv4_aboveThresh (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- sv4_loop qs T ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point

theorem sv3_sv4_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv3_aboveThresh qs T ε₁ ε₂ l = sv4_aboveThresh qs T ε₁ ε₂ l := by
    unfold sv3_aboveThresh
    unfold sv4_aboveThresh
    simp
    funext point
    apply tsum_congr
    intro a
    congr 1
    apply tsum_congr
    intro a_1
    congr 1
    apply tsum_congr
    intro a_2
    erw [sv3_sv4_loop_eq]

/-
## Program version 5
  - Executable
  - Isolates the loop for the next step
-/

def sv5_loop (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (point : ℕ) (init : sv4_state) : SLang ℕ := do
  let sk <- probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (point + 1) init
  return (sv1_threshold sk.1)

def sv5_aboveThresh (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let presamples <- sv4_presample ε₁ ε₂ point
    @sv5_loop _ qs T τ l point (([], v0), presamples)
  computation point

theorem sv4_sv5_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv4_aboveThresh qs T ε₁ ε₂ l = sv5_aboveThresh qs T ε₁ ε₂ l := by
  unfold sv4_aboveThresh
  unfold sv5_aboveThresh
  unfold sv4_loop
  unfold sv5_loop
  simp


/-
## Program version 6
  - Executable
  - Changes the loop from a probWhileCut into a single, deterministic, check
-/

@[simp]
def sv6_cond_rec (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (past : List ℤ) (pres : ℤ) (future : List ℤ) : Bool :=
  match future with
  | [] => ¬ (sv4_aboveThreshC qs T τ l ((past, pres), []))
  | (f :: ff) => (sv4_aboveThreshC qs T τ l ((past, pres), f :: ff) = true) && (sv6_cond_rec qs T τ l (past ++ [pres]) f ff)

@[simp]
def sv6_cond (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (init : sv4_state) : Bool :=
  sv6_cond_rec qs T τ l init.1.1 init.1.2 init.2

def sv6_loop (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (point : ℕ) (init : sv4_state) : SLang ℕ := do
  if (sv6_cond qs T τ l init)
    then return point
    else probZero

omit [DPSystem ℕ] [DPNoise dps] in
lemma sv5_sv6_loop_base_case (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    future = [] ->
    List.length future = eval ->
    List.length (past ++ [pres] ++ future) = point + 1 ->
    (sv6_loop qs T τ l point ((past, pres), future)) point = (sv5_loop qs T τ l eval ((past, pres), future)) point := by
  intro Hfuture Heval Hstate
  rw [Hfuture]
  simp_all
  rw [← Heval]
  unfold sv5_loop
  simp only [probWhileCut]
  unfold probWhileFunctional
  split
  · next h =>
    simp [probWhileCut, sv6_loop]
    rw [h]
    simp
  · next h =>
    simp at h
    simp [sv6_loop]
    simp [h]
    unfold sv4_state
    unfold sv1_state
    rw [ENNReal.tsum_eq_add_tsum_ite ((past, pres), [])]
    simp
    have Hpt : point = sv1_threshold (past, pres) := by
      simp [sv1_threshold]
      omega
    rw [if_pos Hpt]
    conv =>
      lhs; rw [← add_zero (1 : ENNReal)]
    congr 1
    symm
    rw [ENNReal.tsum_eq_zero]
    intro x
    split_ifs <;> simp_all

omit [DPSystem ℕ] [DPNoise dps] in
lemma sv6_loop_ind (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (point : ℕ) (past ff: List ℤ) (pres f: ℤ) :
      (sv4_aboveThreshC qs T τ l ((past, pres), f :: ff) = true) ->
      List.length (past ++ [pres] ++ f :: ff) = point + 1 ->
      (sv6_loop qs T τ l point ((past, pres), f :: ff)) point = (sv6_loop qs T τ l point ((past ++ [pres], f), ff)) point := by
  intro Hcondition _
  unfold sv6_loop
  suffices (sv6_cond qs T τ l ((past, pres), f :: ff) = sv6_cond qs T τ l ((past ++ [pres], f), ff)) by
    split <;> split <;> try rfl
    all_goals simp_all
  conv =>
    lhs
    unfold sv6_cond
    simp
  simp [Hcondition]


omit [DPSystem ℕ] [DPNoise dps] in
lemma sv5_loop_ind (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (eval point : ℕ) (past ff: List ℤ) (pres f: ℤ) :
      (sv4_aboveThreshC qs T τ l ((past, pres), f :: ff) = true) ->
      (sv5_loop qs T τ l (eval + 1) ((past, pres), f :: ff)) point = (sv5_loop qs T τ l eval ((past ++ [pres], f), ff)) point := by
  intro Hcondition
  unfold sv5_loop
  rw [sv4_probWhileCut_succ qs T τ l (eval + 1) (past, pres) f ff (by exact Hcondition)]

def sv6_aboveThresh (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let presamples <- sv4_presample ε₁ ε₂ point
    @sv6_loop _ qs T τ l point (([], v0), presamples)
  computation point


-- sv6_loop and sv5_loop are equal at point (under some conditions)
omit [DPSystem ℕ] [DPNoise dps] in
theorem sv5_sv6_loop_eq_point (qs : sv_query sv_T) (T τ : ℤ) (l : List sv_T) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    List.length (past ++ [pres] ++ future) = point + 1 ->
    List.length future = eval ->
    @sv5_loop _ qs T τ l eval ((past, pres), future) point = @sv6_loop _ qs T τ l point ((past, pres), future) point := by
  revert past pres eval
  induction future
  · intro eval past pres H1 H2
    symm
    simp at H1
    apply (sv5_sv6_loop_base_case _ _ _ _ _ _ _ _ _ (by rfl) H2 ?G2)
    case G2 =>
      simp
      trivial
  · next f ff IH =>
    intro eval past pres Hstate Heval
    cases eval with
    | zero => simp at Heval
    | succ eval =>
    cases (Classical.em (sv4_aboveThreshC qs T τ l ((past, pres), f :: ff) = true)) with
    | inl Hcondition =>
      rw [sv5_loop_ind _ _ _ _ _ _ _ _ _ _ Hcondition]
      rw [sv6_loop_ind _ _ _ _ _ _ _ _ _ Hcondition Hstate]
      apply (IH eval (past ++ [pres]) f ?G1 ?G2)
      case G1 => simp_all
      case G2 => simp_all
    | inr Hcondition =>
    simp at Hcondition
    simp [sv6_loop, Hcondition]
    unfold sv5_loop
    simp only [probWhileCut]
    unfold probWhileFunctional
    rw [Hcondition]
    simp
    intro i Hi
    apply SLang.pure_apply_of_ne
    intro HK
    subst HK
    simp [sv1_threshold] at Hi
    simp at Hstate
    omega


theorem sv5_sv6_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv5_aboveThresh qs T ε₁ ε₂ l = sv6_aboveThresh qs T ε₁ ε₂ l := by
  unfold sv5_aboveThresh
  unfold sv6_aboveThresh
  apply SLang.ext
  intro eval_point
  simp
  apply tsum_congr
  intro τ
  congr
  apply funext
  intro v0
  congr
  apply funext
  intro future
  congr
  rw [sv5_sv6_loop_eq_point]
  · simp [future.2]
  · exact List.Vector.length_val future


/-
## Program version 7
Not executable
Separates out the zero case
-/

def sv7_aboveThresh (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    match point with
    | 0 =>
      if (¬ (sv4_aboveThreshC qs T τ l (([], v0), [])))
        then probPure point
        else probZero
    | (Nat.succ point') => do
      let presamples <- sv4_presample ε₁ ε₂ point'
      let vk <- privNoiseGuess ε₁ ε₂
      if (sv6_cond qs T τ l (([], v0), presamples ++ [vk]))
        then probPure point
        else probZero
  computation point

theorem sv6_sv7_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv6_aboveThresh qs T ε₁ ε₂ l = sv7_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv6_aboveThresh
  unfold sv7_aboveThresh
  cases point
  · simp [sv6_loop, sv6_cond]
    apply tsum_congr
    intro τ
    congr 1
    apply tsum_congr
    intro v0
    congr 1
    simp [sv4_presample]
    exact congrFun (if_congr
      ((Iff.of_eq decide_eq_true_eq).trans (Iff.of_eq (Bool.not_eq_true _))) rfl rfl) 0
  · next point' =>
    simp only []
    apply tsum_congr
    intro τ
    congr 1
    apply tsum_congr
    intro v0
    congr 1
    simp
    conv =>
      enter [2, 1, a]
      rw [← ENNReal.tsum_mul_left]
    conv =>
      lhs
      unfold sv6_loop
    simp
    rw [ENNReal.tsum_comm]
    rw [← ENNReal.tsum_prod]
    conv =>
      rhs
      enter [1, a]
      rw [← mul_assoc]
      enter [1]
      rw [mul_comm]
      rw [sv4_presample_split']
    apply @tsum_eq_tsum_of_ne_zero_bij
    case i =>
      exact fun x => ⟨ x.1.2.1 ++ [x.1.1], by simp [(x.1.2).2] ⟩
    · intro a b H
      simp only [Subtype.mk.injEq] at H
      have H' : List.reverse (a.1.2.1 ++ [a.1.1]) = List.reverse (b.1.2.1 ++ [b.1.1]) :=
        congrArg List.reverse H
      simp at H'
      rcases a with ⟨⟨a1, a2, Ha2⟩, Ha⟩
      rcases b with ⟨⟨b1, b2, Hb2⟩, Hb⟩
      simp_all
    · simp [Function.support, Set.range]
      intros L HL Hf1 Hf2
      exists (vsm_last ⟨ L, HL ⟩)
      exists (vsm_init ⟨ L, HL ⟩)
      refine ⟨⟨(vsm_init ⟨L, HL⟩).2, ?_, ?_⟩, ?_⟩
      · intro K
        apply Hf1
        rw [← K]
        congr
        simp [vsm_init, vsm_last]
        symm
        apply dropLast_append_getLastI
        intro K
        simp [K] at HL
      · intro K
        apply Hf2
        rw [← K]
        have Hl : (↑(vsm_init ⟨L, HL⟩) ++ [vsm_last ⟨L, HL⟩] : List ℤ) = L := by
          simp [vsm_init, vsm_last]
          apply dropLast_append_getLastI
          intro K'
          simp [K'] at HL
        rw [Hl]
      · simp [vsm_init, vsm_last]
        apply dropLast_append_getLastI
        intro K
        simp [K] at HL
    · simp

/-
## Program version 8

Not executable
Defines G from the paper
-/



def sv8_sum (qs :  sv_query sv_T) (l : List sv_T) (past : List ℤ) (pres : ℤ) : ℤ :=
  qs (List.length past) l + pres

-- G is the maximum value of sv8_sum over the tape
def sv8_G (qs :  sv_query sv_T) (l : List sv_T) (past : List ℤ) (pres : ℤ) (future : List ℤ) : ℤ :=
  match future with
  | []        => sv8_sum qs l past pres
  | (f :: ff) => max (sv8_sum qs l past pres) (sv8_G qs l (past ++ [pres]) f ff)

 def sv8_cond (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (past : List ℤ) (pres : ℤ) (future : List ℤ) (last : ℤ) : Bool :=
   (sv8_G qs l past pres future < τ + T) ∧ (sv8_sum qs l (past ++ [pres] ++ future) last ≥ τ + T)

def sv8_aboveThresh (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    match point with
    | 0 =>
      if (sv8_sum qs l [] v0 ≥ τ + T)
        then probPure point
        else probZero
    | (Nat.succ point') => do
      let presamples <- sv4_presample ε₁ ε₂ point'
      let vk <- privNoiseGuess ε₁ ε₂
      if (sv8_cond qs T τ l [] v0 presamples vk)
        then probPure point
        else probZero
  computation point

omit [DPSystem ℕ] [DPNoise dps] in
lemma sv7_sv8_cond_eq (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (v0 : ℤ) (vs : List ℤ) (vk : ℤ) :
    sv8_cond qs T τ l [] v0 vs vk = sv6_cond qs T τ l (([], v0), vs ++ [vk]) := by
  suffices (∀ init, sv8_cond qs T τ l init v0 vs vk = sv6_cond qs T τ l ((init, v0), vs ++ [vk])) by
    apply this
  revert v0
  unfold sv8_cond
  simp
  induction vs
  · intro v0 init
    simp [sv6_cond_rec, sv4_aboveThreshC, sv1_aboveThreshC, sv1_threshold, sv1_noise, List.length]
    simp [sv8_G, sv8_sum]
    congr 1
    exact (Bool.decide_coe _).symm
  · next vi_1 rest IH =>
    intro vi init
    have IH' := IH vi_1 (init ++ [vi])
    simp at IH'
    clear IH
    conv => rhs; simp [sv6_cond_rec]
    rw [← IH']
    clear IH'
    cases (decide (τ + T ≤ sv8_sum qs l (init ++ vi :: vi_1 :: rest) vk)) <;> simp
    conv => lhs; unfold sv8_G; simp
    cases (decide (sv8_G qs l (init ++ [vi]) vi_1 rest < τ + T)) <;> simp
    simp [sv4_aboveThreshC, sv1_aboveThreshC, sv8_sum, sv1_threshold, sv1_noise]
    rfl


theorem sv7_sv8_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv7_aboveThresh qs T ε₁ ε₂ l = sv8_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv7_aboveThresh
  unfold sv8_aboveThresh
  cases point with
  | zero =>
    simp [sv4_aboveThreshC, sv1_aboveThreshC, sv8_sum, sv1_threshold, sv1_noise]
    apply tsum_congr
    intro a
    congr 1
    apply tsum_congr
    intro a_1
    congr 1
    exact congrFun (if_congr (decide_eq_false_iff_not.trans not_lt) rfl rfl) 0
  | succ point' =>
    simp only []
    repeat (apply tsum_congr; intro _; congr 1)
    simp [sv7_sv8_cond_eq, sv6_cond]
    rfl


/-
## Program version 9

Not executable
Rewritten so that the randomness we will cancel out is right at the front
-/


def sv9_aboveThresh (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    match point with
    | 0 => do
      let τ <- privNoiseThresh ε₁ ε₂
      let v0 <- privNoiseGuess ε₁ ε₂
      if (sv8_sum qs l [] v0 ≥ τ + T)
        then probPure point
        else probZero
    | (Nat.succ point') => do
      let v0 <- privNoiseGuess ε₁ ε₂
      let presamples <- sv4_presample ε₁ ε₂ point'
      let τ <- privNoiseThresh ε₁ ε₂
      let vk <- privNoiseGuess ε₁ ε₂
      if (sv8_cond qs T τ l [] v0 presamples vk)
        then probPure point
        else probZero
  computation point

theorem sv8_sv9_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv8_aboveThresh qs T ε₁ ε₂ l = sv9_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv8_aboveThresh
  unfold sv9_aboveThresh
  simp
  split
  · simp
  · simp
    conv => lhs; rw [tsum_comm_mul_left]
    apply tsum_congr
    intro b
    congr 1
    rw [tsum_comm_mul_left]


end equiv


abbrev has_lucky {sv_T : Type} (qs : sv_query sv_T) (T : ℤ) : Prop :=
  ∀ (τ : ℤ) (l : List sv_T), ∃ (K : ℤ), ∀ A, ∀ (K' : ℤ), K ≤ K' -> qs A l + K' ≥ τ + T

section pmf

variable (qs :  sv_query sv_T)
variable (T : ℤ)

/-- Unrolling one step of `probWhileCut` gives a lower bound on the total probability. -/
lemma sv1_lb_advance (τ : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) (cut : ℕ) (H : List ℤ) (v : ℤ) :
    (∑' (x1 : ℕ) (x2 : sv1_state),
        if x1 = sv1_threshold x2
          then (sv1_aboveThreshF ε₁ ε₂ (H, v)).probBind
                 (fun v => probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1) v) x2
          else 0)
    ≤ (∑' (x : ℕ) (x_1 : sv1_state),
        if x = sv1_threshold x_1
          then probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1 + 1) (H, v) x_1
          else 0) := by
  have Hunroll : probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1 + 1) (H, v)
      = probWhileFunctional (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂)
          (probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1)) (H, v) := rfl
  rw [Hunroll]
  unfold probWhileFunctional
  by_cases hcond : sv1_aboveThreshC qs T τ l (H, v) = true
  · rw [if_pos hcond]
    simp
  · rw [if_neg hcond]
    simp
    apply ENNReal.tsum_lb_single (List.length H)
    apply ENNReal.tsum_lb_single (H, v)
    conv =>
      rhs
      simp [sv1_threshold]
    have X :
      (∑' (x1 : ℕ) (x2 : sv1_state),
        if x1 = sv1_threshold x2 then
          ∑' (a : sv1_state),
            sv1_aboveThreshF ε₁ ε₂ (H, v) a * probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1) a x2
        else 0) =
      (∑' (x1 : ℕ) (x2 : sv1_state),
        if x1 = sv1_threshold x2 then
          ((sv1_aboveThreshF ε₁ ε₂ (H, v) >>=  probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1)) x2)
        else 0) := by
      simp
    rw [X]
    clear X
    rw [ENNReal.tsum_comm]
    have X : ∀ b : sv1_state,
             (∑' (a : ℕ),
               if a = sv1_threshold b then
                 (sv1_aboveThreshF ε₁ ε₂ (H, v) >>= probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1)) b
             else 0) =
             ((sv1_aboveThreshF ε₁ ε₂ (H, v) >>= probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1)) b) :=  by
        intro b
        rw [tsum_ite_eq]
    conv =>
      lhs
      enter [1, b]
      rw [X b]
    clear X
    simp [sv1_aboveThreshF, probBind]
    apply le_trans
    · apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro a1
      gcongr
    rw [ENNReal.tsum_comm]
    conv =>
      lhs
      enter [1, b]
      rw [ENNReal.tsum_mul_left]
    apply le_trans (b := ∑' (x : sv1_state),
      probBind (⇑(privNoiseGuess ε₁ ε₂)) (fun vn => probPure (H ++ [v], vn)) x * 1)
    · apply ENNReal.tsum_le_tsum
      intro x
      gcongr
      exact sv1_loop_ub qs T τ ε₁ ε₂ l (cut + 1) x.1 x.2
    · simp only [mul_one]
      refine le_trans ?_ (le_of_eq (SLang.pure_apply_self _).symm)
      exact le_of_eq (SLang.probBind_norm _ _ (SPMF_sum_one _) (fun a => SLang.probPure_norm _))

lemma privNoiseGuess_pure_pos (ε₁ ε₂ : ℕ+) (k : ℤ) :
    0 < @privNoiseGuess PureDPSystem laplace_pureDPSystem ε₁ ε₂ k := by
  simp [privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure, DiscreteLaplaceGenSamplePMF]
  simp [DFunLike.coe]
  apply mul_pos
  · apply div_pos
    · simp
    · apply Right.add_pos'
      · apply Real.exp_pos
      · simp
  · apply Real.exp_pos

lemma sv1_lb (lucky_guess : has_lucky qs T) ε₁ ε₂ l :
    1 ≤ ∑'s, (@sv1_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l s)  := by
  simp only [sv1_aboveThresh, bind, pure, bind_apply]
  -- Push the sum over s inwards
  conv =>
    rhs
    rw [ENNReal.tsum_comm]
    enter [1, b]
    rw [ENNReal.tsum_mul_left]
    enter [2]
    rw [ENNReal.tsum_comm]
    enter [1, i]
    rw [ENNReal.tsum_mul_left]

  -- Reduce to CDF problem
  apply @le_trans _ _ _ (∑' (b : ℤ), (privNoiseThresh ε₁ ε₂) b  * 1) _ ?G1
  case G1 =>
    simp [SPMF_sum_one]
  apply ENNReal.tsum_le_tsum
  intro τ
  gcongr

  -- Turn it into a supremum
  conv =>
    enter [2, 1, i_1, 2, 1, i ,1, b]
    simp only [probWhile]
    rw [ENNReal.iSup_mul]
  conv =>
    enter [2, 1, v0, 2, 1, state_size, 1, state]

  -- Commute out the cut number first
  apply le_trans _ ?G1
  case G1 =>
    apply ENNReal.tsum_le_tsum
    intro v0
    apply mul_le_mul_right
    apply ENNReal.tsum_le_tsum
    intro state_size
    apply iSup_tsum_le_tsum_iSup
  apply le_trans _ ?G1
  case G1 =>
    apply ENNReal.tsum_le_tsum
    intro v0
    apply mul_le_mul_right
    apply iSup_tsum_le_tsum_iSup
  simp
  conv =>
    enter [2, 1, v0]
    rw [ENNReal.mul_iSup]
  apply le_trans _ ?G1
  case G1 =>
    apply iSup_tsum_le_tsum_iSup

  -- The lucky event: sampling above a value T, which forces the loop to terminate
  rcases (lucky_guess τ l) with ⟨ K, HK ⟩
  let PLucky (K' : ℤ) : Prop := K ≤ K'
  have HLucky : ∀ (K' : ℤ), ∀ A, PLucky K' → qs A l + K' ≥ τ + T :=
    fun K' A hK' => HK A K' hK'
  clear HK

  -- We will split the sum based on PLucky at each step

  -- ρ is the probability of the lucky event
  let ρ : ENNReal := (∑'(a : {t : ℤ // PLucky t}), privNoiseGuess ε₁ ε₂ a.1)
  have Hρ_1 : (∑'a, privNoiseGuess ε₁ ε₂ a) = 1 := SPMF_sum_one _
  have Hρ_lb : 0 < ρ := by
    -- There is at least one lucky element
    have HU : PLucky K := by simp [PLucky]
    apply LT.lt.trans_le _ ?G2
    case G2 => apply ENNReal.le_tsum ⟨ _, HU ⟩
    exact privNoiseGuess_pure_pos ε₁ ε₂ K
  have Hρ_nz : ρ ≠ 0 := by apply pos_iff_ne_zero.mp Hρ_lb
  have Hρ_ub : ρ ≤ 1 := by
    rw [← Hρ_1]
    rw [ENNReal.tsum_split PLucky]
    simp_all only [ge_iff_le, self_le_add_right, PLucky, ρ]
  have Hρ_ub_strict : ρ < 1 := by
    rw [← Hρ_1]
    rw [ENNReal.tsum_split PLucky]
    conv =>
      lhs
      rw [← add_zero ρ]
    apply ENNReal.add_lt_add_of_le_of_lt
    · intro X; simp_all
    · rfl
    · -- There is at least one unlucky element
      have HU : ¬PLucky (K - 1) := by simp [PLucky]
      apply LT.lt.trans_le _ ?G2
      case G2 => apply ENNReal.le_tsum ⟨ _, HU ⟩
      exact privNoiseGuess_pure_pos ε₁ ε₂ (K - 1)

  -- Bound the CDF below by the geometric CDF
  apply le_trans (iSup_geo_cdf_ge_one ρ Hρ_nz)
  apply iSup_mono
  intro cut


  -- Because v0 is not in the loop, we need to do one of the unrollings first
  -- Our IH is going to include a condition on "present"
  cases cut with
  | zero => simp [probWhileCut, geo_cdf]
  | succ cut =>

  rw [geo_cdf_rec _ Hρ_ub]
  rw [ENNReal.tsum_split PLucky]
  apply add_le_add
  · -- Lucky guess
    simp [probWhileCut, probWhileFunctional, sv1_aboveThreshC, sv1_noise]
    conv =>
      rhs
      enter [1, a, 2, 1, x, 1, x1]
      rw [ite_conv_left
            (by
               refine congrFun (ite_eq_right_iff.mpr ?_) x1
               intro i
               exfalso
               rcases a with ⟨ v, Hv ⟩
               simp [sv1_threshold] at i
               have luck := HLucky v 0 Hv
               have i' := of_decide_eq_true i
               omega)]
      rfl
    -- The rightmost sum is 1
    apply @le_trans _ _ _ (∑' (a : { t // PLucky t }), (privNoiseGuess ε₁ ε₂) ↑a * 1)
    · simp [ρ]
    apply ENNReal.tsum_le_tsum
    intro x
    gcongr
    apply ENNReal.tsum_lb_single 0
    apply ENNReal.tsum_lb_single ([], x.1)
    simp [sv1_threshold]
    exact le_of_eq (SLang.pure_apply_self _).symm


  -- Unlucky
  suffices (∀ H, ∀ a : {t : ℤ // ¬ PLucky t}, geo_cdf ρ cut ≤
                  ∑' (x : ℕ) (x_1 : sv1_state),
                    if x = sv1_threshold x_1 then probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1) (H, ↑a) x_1 else 0) by
    apply le_trans _ ?G1
    case G1 =>
      apply ENNReal.tsum_le_tsum
      intro a
      apply mul_le_mul_right
      apply this
    rw [ENNReal.tsum_mul_right]
    apply mul_le_mul_left
    apply Eq.le
    -- Math
    rw [← Hρ_1]
    conv =>
      enter [1, 1]
      rw [ENNReal.tsum_split PLucky]
    apply ENNReal.add_sub_cancel_left
    exact LT.lt.ne_top Hρ_ub_strict

  -- Now we have the right inductive structure
  induction cut with
  | zero => simp [geo_cdf]
  | succ cut IH =>
    intro H a
    rcases a with ⟨ v, Hv ⟩
    simp

    -- Because the first sample is not lucky, we can't say anything about the branch we end up in
    -- It may terminate, or it may not.
    apply le_trans _ (sv1_lb_advance qs T τ ε₁ ε₂ l cut H v)
    simp

    -- Now we want to commute out the randomness associate to that s1_aboveThreshF
    apply le_trans _ ?G1
    case G1 =>
      apply ENNReal.tsum_le_tsum
      intro x
      apply ENNReal.tsum_le_tsum
      intro x_1
      rw [← ite_lemma_1]
    conv =>
      enter [2]
      conv =>
        enter [1, a]
        rw [ENNReal.tsum_comm]
      rw [ENNReal.tsum_comm]

    -- Split the sv1_state sum
    conv =>
      enter [2]
      unfold sv1_state
      rw [ENNReal.tsum_prod']
      rw [ENNReal.tsum_comm]

    -- Now, condition on the luckiness of the next value
    rw [ENNReal.tsum_split PLucky]


    -- Split the sum and the recurrence relation
    rw [geo_cdf_rec _ Hρ_ub]
    apply add_le_add
    · -- Guess is lucky
      -- The loop will terminate and we can show it

      simp_rw [← mul_ite_zero, ENNReal.tsum_mul_left]

      -- Conclude by simplification
      simp only [sv1_aboveThreshF, bind, pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
      simp only [probWhileCut]
      unfold probWhileFunctional
      -- Push the ite inside so that all of the sums are in a row
      simp_rw [← ENNReal.tsum_mul_right]
      simp
      simp_rw [← mul_ite_zero, ← ite_lemma_1, ← ENNReal.tsum_mul_left]
      -- Move the lucky sample inwards
      conv =>
        rhs
        rw [ENNReal.tsum_comm]
        enter [1, b]
        rw [ENNReal.tsum_comm]
        enter [1, c]
        rw [ENNReal.tsum_comm]
        enter [1, d]
        rw [ENNReal.tsum_comm]
      -- Pick elements for each of the other sums to make it terminate
      apply ENNReal.tsum_lb_single (H ++ [v])
      rw [ENNReal.tsum_comm]
      apply ENNReal.tsum_lb_single (List.length H + 1)
      rw [ENNReal.tsum_comm]
      rw [ENNReal.tsum_prod']
      apply ENNReal.tsum_lb_single (H ++ [v])
      apply le_trans _ ?G1
      case G1 =>
        apply ENNReal.tsum_le_tsum
        intro b
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_le_tsum
        intro c
        gcongr

      -- Now move the lucky sum out to the front, so that we can constrain the other sum values to equal it
      conv =>
        rhs
        enter [1, a]
        rw [ENNReal.tsum_comm]
      rw [ENNReal.tsum_comm]

      apply le_trans _ ?G1
      case G1 =>
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_lb_single a.1
        apply ENNReal.tsum_lb_single a.1
        rfl
      simp
      -- Remaining goal: ρ ≤ ∑' a, if H.length+1 = sv1_threshold (H++[v], ↑a) then priv ↑a else 0
      -- The condition is always true since sv1_threshold (H++[v], _) = (H++[v]).length = H.length+1
      apply le_of_eq
      show (∑' (a : { t // PLucky t }), (privNoiseGuess ε₁ ε₂) ↑a) = _
      congr 1
      ext a
      rw [if_pos (by simp [sv1_threshold])]
      rcases a with ⟨a, Ha⟩
      have hcond : sv1_aboveThreshC qs T τ l (H ++ [v], a) = false := by
        simp [sv1_aboveThreshC, sv1_noise, sv1_threshold]
        have := HLucky a (H.length + 1) Ha
        omega
      simp [hcond, probPure]

    · -- Guess is unlucky
      -- Commute out the samples related to the first sample (which will evenetually become a (1- ρ) factor)
      simp_rw [← mul_ite_zero, ENNReal.tsum_mul_left]
      unfold sv1_state at IH

      apply le_trans _ ?G1
      case G1 =>
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_le_tsum
        intro b
        apply mul_le_mul_right
        apply IH
      simp_rw [ENNReal.tsum_mul_right]
      apply mul_le_mul_left

      -- Conclude by simplification
      simp only [sv1_aboveThreshF, bind, pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
      apply le_trans _ ?G1
      case G1 =>
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_lb_single (H ++ [v])
        apply ENNReal.tsum_lb_single a.1
        rfl
      simp
      rw [← Hρ_1]
      rw [ENNReal.tsum_split PLucky]
      rw [add_comm]


/-- Under a lucky-guess condition, `sv1_aboveThresh` is a proper probability distribution. -/
lemma sv1_hasSum_one (lucky_guess : has_lucky qs T) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    HasSum (@sv1_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  apply LE.le.antisymm
  · apply sv1_ub
  · exact sv1_lb qs T lucky_guess ε₁ ε₂ l

def sv1_aboveThresh_PMF (lucky_guess : has_lucky qs T) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SPMF ℕ :=
  ⟨ sv1_aboveThresh qs T ε₁ ε₂ l, sv1_hasSum_one qs T lucky_guess ε₁ ε₂ l ⟩

/--
sv9 normalizes because sv1 normalizes
-/
def sv9_aboveThresh_SPMF (lucky_guess : has_lucky qs T) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SPMF ℕ :=
  ⟨ @sv9_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l,
    by
      rw [← @sv8_sv9_eq]
      rw [← @sv7_sv8_eq]
      rw [← @sv6_sv7_eq]
      rw [← @sv5_sv6_eq]
      rw [← @sv4_sv5_eq]
      rw [← @sv3_sv4_eq]
      rw [← @sv2_sv3_eq]
      rw [← @sv1_sv2_eq]
      exact sv1_hasSum_one qs T lucky_guess ε₁ ε₂ l ⟩

end pmf

end SLang
