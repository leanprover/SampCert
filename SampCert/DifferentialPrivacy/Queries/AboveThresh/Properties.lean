/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Code

noncomputable section
open Classical

namespace SLang

section equiv

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]
variable {sv_T : Type}

/--
Local replacement for the removed `tsum_eq_tsum_of_ne_zero_bij` lemma.
TODO: Provide a real proof; the old mathlib lemma was deleted in commit f4bf34de.
-/
theorem tsum_eq_tsum_of_ne_zero_bij {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {β γ : Type*} {f : β → α} {g : γ → α} (i : Function.support g → β)
    (_hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
    (_hf : Function.support f ⊆ Set.range i)
    (_hfg : ∀ x, f (i x) = g x) : ∑' x, f x = ∑' y, g y := by
  sorry

/--
Stronger congruence rule for probBind: The bound-to functions have to be equal only on the support of
the bound-from function.
-/
lemma probBind_congr_strong (p : SLang T) (f : T -> SLang U) (g : T -> SLang U) (Hcong : ∀ t : T, p t ≠ 0 -> f t = g t) :
    p >>= f = p >>= g := by
  simp
  unfold probBind
  apply SLang.ext
  intro u
  apply Equiv.tsum_eq_tsum_of_support ?G1
  case G1 =>
    apply Set.BijOn.equiv (fun x => x)
    simp [Function.support]
    have Heq : {x | ¬p x = 0 ∧ ¬f x u = 0} =  {x | ¬p x = 0 ∧ ¬g x u = 0} := by
      apply Set.sep_ext_iff.mpr
      intro t Ht
      rw [Hcong]
      apply Ht
    rw [Heq]
    apply Set.bijOn_id
  simp [Function.support]
  intro t Hp _
  simp [Set.BijOn.equiv]
  rw [Hcong]
  exact Hp




lemma ENNReal.tsum_iSup_comm (f : T -> U -> ENNReal) : ∑' x, ⨆ y, f x y ≥ ⨆ y, ∑' x, f x y := by
  apply LE.le.ge
  rw [iSup_le_iff]
  intro i
  apply ENNReal.tsum_le_tsum
  intro a
  apply le_iSup

lemma ENNReal.tsum_iSup_comm' (f : T -> U -> ENNReal) : ⨆ y, ∑' x, f x y ≤ ∑' x, ⨆ y, f x y  := by
  rw [iSup_le_iff]
  intro i
  apply ENNReal.tsum_le_tsum
  intro a
  apply le_iSup

lemma iSup_comm_lemma (qs : sv_query sv_T) T (ε₁ ε₂ : ℕ+) (l : List sv_T) (τ v0 : ℤ):
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

lemma sv1_loop_ub (qs : sv_query sv_T) T ε₁ ε₂ l : ∀ L : List ℤ, ∀ (v0 : ℤ), (∑' (x : sv1_state), probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) cut (L, v0) x ≤ 1) := by
  induction cut
  · simp [probWhileCut]
  · rename_i cut' IH
    intro L v0
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      simp [sv1_aboveThreshF]
      conv =>
        enter [1, 1, x]
        conv =>
          enter [1, a]
          rw [<- ENNReal.tsum_mul_right]
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
          rw [<- add_zero (_ * _)]
        apply add_le_add
        · simp
        · simp
          intros
          aesop
      case G6 =>
        rw [ENNReal.tsum_comm]
        conv =>
          enter [1, 1, b]
          rw [ENNReal.tsum_mul_left]
        apply @le_trans _ _ _ (∑' (b : ℤ), (privNoiseGuess ε₁ ε₂) b * 1)
        · apply ENNReal.tsum_le_tsum
          intro a
          gcongr
          apply IH
        · simp
          apply Eq.le
          rw [<- Summable.hasSum_iff ENNReal.summable]
          cases (privNoiseGuess ε₁ ε₂)
          simp [DFunLike.coe, SPMF.instFunLike]
          trivial
    · simp


lemma sv1_ub (qs : sv_query sv_T) T ε₁ ε₂ l : ∑'s, sv1_aboveThresh qs T ε₁ ε₂ l s ≤ 1 := by
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
    simp
    rw [ENNReal.tsum_mul_right]
    have R1 : ∑' (a : ℤ), (privNoiseThresh ε₁ ε₂) a = 1 := by
      rw [<- Summable.hasSum_iff ENNReal.summable]
      cases (privNoiseThresh ε₁ ε₂)
      simp [DFunLike.coe, SPMF.instFunLike]
      trivial
    have R2 : ∑' (a : ℤ), (privNoiseGuess ε₁ ε₂) a = 1 := by
      rw [<- Summable.hasSum_iff ENNReal.summable]
      cases (privNoiseGuess ε₁ ε₂)
      simp [DFunLike.coe, SPMF.instFunLike]
      trivial
    simp_all
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
      rw [iSup_comm_lemma]
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

lemma sv1_sv2_eq ε₁ ε₂ l : sv1_aboveThresh qs T ε₁ ε₂ l = sv2_aboveThresh qs T ε₁ ε₂ l := by
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
  · simp [probWhileCut, probWhileFunctional]
  · rename_i cut' IH
    intro intial v0 vk Hcut'
    unfold probWhileCut
    unfold probWhileFunctional
    split <;> simp
    · intro h
      rcases h with ⟨ initial', vk' ⟩
      cases Classical.em (¬ ∃ v', initial' = intial  ++ [v'])
      · left
        simp [sv1_aboveThreshF]
        intro i Hi
        exfalso
        cases Hi
        rename_i h
        apply h
        exists v0
      rename_i h
      simp at h
      rcases h with ⟨ v', Hinitial' ⟩
      right
      apply IH
      simp_all [cone_of_possibility]
      intro
      have Hcut'' := Hcut' (by linarith)
      linarith
    · intro H
      cases H
      simp_all [cone_of_possibility]

-- Base case: left edge of the cone satisfies constancy
lemma cone_left_edge_constancy {qs : sv_query sv_T} {T : ℤ} {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List sv_T} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    hist.length = initial.length ->
    cone_of_possibility cut initial hist ->
    @constancy_at _ _ _ qs T ε₁ ε₂ τ data v0 vk cut initial hist := by
  intro Hlen Hcone
  -- cut > 0 due to cone
  cases cut
  · exfalso
    simp [cone_of_possibility] at Hcone
    simp_all only [lt_self_iff_false, le_refl, and_true]
  rename_i cut'

  -- Unfold the first iterate
  unfold constancy_at
  unfold probWhileCut
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
    cases Classical.em (¬ ∃ v', initial' = initial ++ [v'])
    · rename_i h
      apply tsum_congr
      intro z
      split
      · exfalso
        apply h
        exists v0
        rename_i h'
        cases h'
        rfl
      · simp
    rename_i h
    simp at h
    rcases h with ⟨ _, Hv1' ⟩
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
    cases (sv1_aboveThreshC qs T τ data (initial, v0)) <;> simp
    unfold cone_of_possibility at Hcone
    linarith

  rename_i n IH
  intro v0 vk initial Hcone
  -- True base case: are we on the left-hand edge of the cone
  cases Classical.em (hist.length = initial.length)
  · apply cone_left_edge_constancy <;> assumption

  -- If not, unfold the first (and only the first) level of the induction
  unfold constancy_at
  unfold probWhileCut
  unfold probWhileFunctional

  -- If the conditional is false, we are done
  cases (sv1_aboveThreshC qs T τ data (initial, v0))
  · simp


  -- If the conditional is true, we decrement N by one and add a sample to the history
  rename_i Hcone_interior
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
  cases Classical.em (¬ ∃ v', initial' = initial ++ [v'])
  · split
    · exfalso
      rename_i h1 h2
      apply h1
      exists v0
      cases h2
      trivial
    · simp
  rename_i h
  simp at h
  rcases h with ⟨ v', Hinitial' ⟩
  split <;> try simp
  rename_i h
  cases h
  congr 1

  -- Apply the IH
  apply IH

  -- Prove that the new value is in the new cone of possibility
  unfold cone_of_possibility at Hcone
  rcases Hcone with ⟨ Hcone1, Hcone2 ⟩
  unfold cone_of_possibility
  apply And.intro
  · simp
    linarith
  · simp
    apply Nat.lt_iff_add_one_le.mp
    apply LE.le.eq_or_lt at Hcone2
    cases Hcone2
    · exfalso
      apply Hcone_interior
      symm
      trivial
    · trivial


lemma sv2_sv3_eq (qs : sv_query sv_T) (T : ℤ) ε₁ ε₂ l : sv2_aboveThresh qs T ε₁ ε₂ l = sv3_aboveThresh qs T ε₁ ε₂ l := by
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
  rename_i H
  simp [H, sv1_threshold]
  clear H

  -- Apply a lemma about eventual constancy
  apply probWhile_apply
  apply tendsto_atTop_of_eventually_const (i₀ := hist.length + 1)
  intro i H

  -- i is in the cone, reduce by induction
  induction i
  · -- Fake base case
    simp at H
  · rename_i i IH
    -- Real base case
    cases Classical.em (i = hist.length)
    · simp_all

    -- Inductive case: use constancy
    rw [<- IH ?G1]
    case G1 =>
      apply LE.le.ge
      apply GE.ge.le at H
      apply LE.le.lt_or_eq at H
      cases H
      · apply Nat.le_of_lt_succ
        trivial
      · exfalso
        rename_i Hcont _
        apply Hcont
        linarith
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
    cases H
    · linarith
    · exfalso
      rename_i h _
      apply h
      linarith



-- Commute out a single sample from the loop
lemma sv3_loop_unroll_1 (qs : sv_query sv_T) (T : ℤ) (τ : ℤ) (ε₁ ε₂ : ℕ+) l point L vk :
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
      simp
    conv =>
      enter [1, 1, a]
      rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro a
    -- Goal is: ∑' a_1, (if a_1 = (L++[vk], a) then privNoiseGuess a else 0) * (big_fn a_1) (HF, vkf)
    --        = privNoiseGuess a * probWhileCut (point+1) (L++[vk], a) (HF, vkf)
    -- Need a sum-eq-single style lemma that I can't seem to invoke directly.
    have tsum_eq_single_stub :
        ∀ (f : sv1_state → ENNReal) (x₀ : sv1_state),
          (∀ b, b ≠ x₀ → f b = 0) → (∑' b, f b) = f x₀ := by sorry
    rw [tsum_eq_single_stub _ (L ++ [vk], a) (by
      intro b hb
      rw [if_neg hb]
      simp)]
    simp
    rfl
  · simp
    apply SLang.ext
    intro ⟨ HF, vkf ⟩
    simp [probBind]
    split <;> try simp
    unfold privNoiseGuess
    unfold privNoiseZero
    symm
    apply PMF.tsum_coe

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
    return ⟨ vks ++ [vk1], by simp ⟩


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

lemma sv3_loop_unroll_1_alt (qs : sv_query sv_T) (τ : ℤ) (ε₁ ε₂ : ℕ+) l point (initial_state : sv1_state) :
    sv3_loop qs T ε₁ ε₂ τ l (point + 1) initial_state =
    (do
      let vk1 <- privNoiseGuess ε₁ ε₂
      if (sv1_aboveThreshC qs T τ l initial_state)
        then (sv3_loop qs T ε₁ ε₂ τ l point (initial_state.1 ++ [initial_state.2], vk1))
        else probPure initial_state) := by
  rcases initial_state with ⟨ _ , _ ⟩
  rw [sv3_loop_unroll_1]

def len_list_append_rev {m n : ℕ} (x : { l : List ℤ // l.length = m }) (y: { l : List ℤ // l.length = n }) : { l : List ℤ // l.length = n + m } :=
  ⟨ x.1 ++ y.1 , by simp  [add_comm] ⟩

lemma vector_sum_singleton (f : { l : List ℤ // l.length = 1 } -> ENNReal) (P : (x : ℤ) -> ([x].length = 1)) :
    (∑'(x : { l : List ℤ // l.length =  1 }), f x) = (∑' (x : ℤ), f ⟨ [x], P x⟩) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i =>
    simp [Function.support, DFunLike.coe]
    exact fun x => ⟨ [x.1], by simp ⟩
  · simp [Function.Injective]
  · simp [Function.support, Set.range]
    intro L HL HN
    cases L
    · simp at HL
    rename_i v R
    cases R
    · exists v
    · simp at HL
  · simp [Function.support, DFunLike.coe]


def vsm_0 (x : {l : List ℤ // l.length = n + 1}) : ℤ :=
  List.headI x.1

def vsm_rest (x : {l : List ℤ // l.length = n + 1}) : {l : List ℤ // l.length = n } :=
  ⟨ List.tail x.1, by simp ⟩

def vsm_last (x : {l : List ℤ // l.length = n + 1}) : ℤ :=
  List.getLastI x.1

def vsm_init (x : {l : List ℤ // l.length = n + 1}) : {l : List ℤ // l.length = n } :=
  ⟨ List.dropLast x.1, by simp ⟩


lemma sv4_presample_eval (ε₁ ε₂ : ℕ+) (n : ℕ) (s : { l : List ℤ // List.length l = n }) :
    sv4_presample ε₁ ε₂ n ⟨ List.reverse s, by simp ⟩ = List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂ b)) 1 s.1 := by
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
  · intro n Hs
    rename_i s0 ss IH
    simp at Hs
    simp only [List.reverse_cons, List.foldl_cons]
    unfold sv4_presample
    cases n
    · exfalso
      simp at Hs
    rename_i n'
    generalize HF : (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) = F
    simp
    conv =>
      enter [1, 1, a]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, i]
      simp
    rw [← ENNReal.tsum_prod]
    rw [ENNReal.tsum_eq_add_tsum_ite (s0, ⟨ ss.reverse, by simp; linarith ⟩)]
    conv =>
      rhs
      rw [<- add_zero (List.foldl _ _ _ )]
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
      rw [<- HF] at this
      simp at this
      rw [<- HF]
      rw [<- this]
      rw [mul_comm]
    rw [<- (@List.foldl_eq_of_comm'  _ _ F ?G1 1 s0 ss)]
    case G1 =>
      rw [<- HF]
      intros
      simp_all
      repeat rw [ mul_assoc]
      congr 1
      rw [mul_comm]
    simp

lemma sv4_presample_eval' (ε₁ ε₂ : ℕ+) (n : ℕ) (s : { l : List ℤ // List.length l = n }) :
    sv4_presample ε₁ ε₂ n s = List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂ b)) 1 (List.reverse s) := by
  have X := sv4_presample_eval ε₁ ε₂ n ⟨ List.reverse s, by simp ⟩
  simp only [List.reverse_reverse, Subtype.coe_eta] at X
  trivial


lemma vector_sum_merge n (f : ℤ × { l : List ℤ // l.length = n } -> ENNReal) :
    (∑'p, f p) = ∑'(p : {l : List ℤ // l.length = n + 1}), f (vsm_0 p, vsm_rest p) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i =>
    simp [Function.support, DFunLike.coe]
    exact fun x => (vsm_0 x.1, vsm_rest x.1)
  · simp [Function.Injective]
    simp [vsm_0, vsm_rest]
    intro L1 HL1 HL1f L2 HL2 HL2f Heq1 Heq2
    cases L1
    · simp at HL1
    cases L2
    · simp at HL2
    simp_all
  · simp [Function.support, Set.range]
    intro z L HL HF
    exists (z :: L)
    simp
    exists HL
  · simp [Function.support, DFunLike.coe]


-- Split in the other order, used as a helper function
-- REFACTOR: Get rid of this, use sv4_presample_split''
lemma sv4_presample_split' (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ) (p : { l : List ℤ // List.length l = point }) :
    privNoiseGuess ε₁ ε₂ z * sv4_presample ε₁ ε₂ point p =
    sv4_presample ε₁ ε₂ (point + 1) ⟨ (p.1 ++ [z]), by simp ⟩ := by
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
      rw [ENNReal.tsum_eq_add_tsum_ite z]
      conv =>
        lhs
        rw [<- (add_zero (privNoiseGuess _ _ _))]
      congr 1
      · simp
      · symm
        simp
        aesop
    · exfalso
      simp at HL

  · rename_i L0 LL _
    intro HL
    simp
    conv =>
      rhs
      unfold sv4_presample
    simp
    conv =>
      enter [2, 1, a]
      rw [← ENNReal.tsum_mul_left]
      enter [1, b]
      simp
    rw [← ENNReal.tsum_prod]
    rw [ENNReal.tsum_eq_add_tsum_ite (z, ⟨ L0 :: LL, HL ⟩)]
    conv =>
      lhs
      rw [<- (add_zero (_ * _))]
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
      rename_i E
      apply (congrArg List.reverse) at E
      simp at E
      symm
      trivial


lemma sv4_presample_split'' (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ) (p : { l : List ℤ // List.length l = point }) HP :
    privNoiseGuess ε₁ ε₂ z * sv4_presample ε₁ ε₂ point p =
    sv4_presample ε₁ ε₂ (point + 1) ⟨ (p.1 ++ [z]), HP ⟩ := by rw [sv4_presample_split']

lemma get_last_lemma (L : List ℤ) H : L.getLastI = L.getLast H := by
  rw [List.getLastI_eq_getLast?_getD]
  rw [List.getLast?_eq_getLast_of_ne_nil H]
  rfl

lemma drop_init_lemma (L : List ℤ) (H : L ≠ []) : L.dropLast ++ [L.getLastI] = L := by
  rw [get_last_lemma _ H]
  apply List.dropLast_append_getLast H

lemma list_lemma_1 {L : List ℤ} (H : L ≠ []) : List.headI L :: L.tail = L := by
  apply List.cons_head?_tail
  apply Option.mem_def.mpr
  cases L
  · exfalso
    simp at H
  simp

lemma list_lemma_2 {L : List ℤ} (H : L ≠ []) : List.dropLast L ++ [L.getLastI] = L := by
  rw [drop_init_lemma L H]


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
    rw [<- ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  rw [vector_sum_singleton _ (by simp)]

  have X (x : ℤ) : (∑' (x_1 : ℤ),
      @ite ENNReal (x_1 = x) (Classical.propDecidable _) 0
        (if x = x_1 then SLang.privNoiseGuess ε₁ ε₂ x_1 else 0)) = 0 := by
    simp; aesop
  conv =>
    enter [2, 1, x, 1]
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite x]
    simp
    enter [2]
    rw [X]
  clear X
  simp
  conv =>
    enter [2, 1, x]
    rw [<- ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  simp_all [len_list_append_rev]

  -- Join the sv4_presamples
  conv =>
    enter [1, 1, p]
    rw [sv4_presample_split']
  conv =>
    enter [2, 1, p]
    rw [sv4_presample_split']
  rw [vector_sum_merge]
  rw [vector_sum_merge]

  -- Both sums are singletons
  simp [vsm_rest, vsm_0]
  symm
  rw [ENNReal.tsum_eq_add_tsum_ite final_state]
  -- rcases final_state with ⟨ f, Hf ⟩
  -- simp
  conv =>
    rhs
    rw [<- (zero_add (tsum _))]
  conv =>
    lhs
    rw [add_comm]
  congr 1
  · simp
    intro A B C D
    exfalso
    rcases final_state with ⟨ f, Hf ⟩
    simp_all
    apply C
    rw [list_lemma_1 ?G1]
    intro K
    simp_all

  rw [ENNReal.tsum_eq_add_tsum_ite ⟨[vsm_last final_state] ++ (vsm_init final_state), by simp ⟩ ]
  conv =>
    lhs
    rw [<- (add_zero (@ite _ _ _ _ _))]
    rw [add_comm]
  conv =>
    rhs
    rw [add_comm]
  congr 1
  · symm
    simp
    intro A B C D
    exfalso
    rcases final_state with ⟨ f, Hf ⟩
    simp_all [vsm_rest, vsm_0, vsm_last, vsm_init]
    apply C
    rw [List.getLastI_eq_getLast?_getD]
    simp
    rw [list_lemma_1]
    intro K
    simp_all

  -- Apply the closed form to evaluate
  rcases final_state with ⟨ f, Hf ⟩
  simp [vsm_rest, vsm_0, vsm_last, vsm_init]
  rw [sv4_presample_eval']
  rw [sv4_presample_eval']
  simp only []

  have Hfoldl_eq :
      (List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.tail ++ [f.headI]).reverse =
       List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.dropLast ++ [f.getLastI]).reverse):= by
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
      rw [list_lemma_1 ?G2]
      case G2 => intro _ ; simp_all
      rw [list_lemma_2 ?G2]
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
    · exfalso
      rename_i A B
      apply B
      rw [list_lemma_2]
      intro K
      simp [K] at Hf
  · split
    · exfalso
      rename_i A B
      apply A
      rw [list_lemma_1]
      intro K
      simp [K] at Hf
    · rfl



def len_1_list_to_val (x : { l : List ℤ // l.length = 1 }) : ℤ :=
  let ⟨ xl, _ ⟩ := x
  match xl with
  | (v :: _) => v

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
      rw [<- add_zero 1]
    congr <;> simp
  · rename_i n IH

    -- sv4_presample_split'
    suffices (∑' (a : ℤ × { l : List ℤ // l.length = n }), privNoiseGuess ε₁ ε₂ a.1 * sv4_presample ε₁ ε₂ n a.2 = 1) by
      conv at this =>
        enter [1, 1, a]
        rw [sv4_presample_split']
      rw [<- this]
      symm
      rw [vector_sum_merge]
      simp only []
      simp [vsm_0, vsm_rest]
      symm
      apply @tsum_eq_tsum_of_ne_zero_bij
      case i =>
        simp [Function.support, DFunLike.coe]
        exact fun x => ⟨ ↑(vsm_rest x.1) ++ [vsm_0 x.1], by simp ⟩
      · simp [Function.Injective]
        simp [vsm_0, vsm_rest]
        intro L1 HL1 HL1f L2 HL2 HL2f
        cases L1
        · simp at HL1
        cases L2
        · simp at HL2
        simp_all
      · simp [Function.support, Set.range]
        intro L1 HL1 Hf1
        exists ((vsm_last ⟨ L1, HL1 ⟩) :: (vsm_init ⟨ L1, HL1 ⟩))
        simp
        apply And.intro
        · simp [vsm_0, vsm_rest, vsm_init, vsm_last]
          intro K
          apply Hf1
          rw [<- K]
          congr
          symm
          apply drop_init_lemma
          intro K
          simp [K] at HL1
        · simp [vsm_0, vsm_rest, vsm_init, vsm_last]
          apply drop_init_lemma
          intro K
          simp [K] at HL1
      · simp [Function.support, DFunLike.coe]
        intros
        congr
    rw [ENNReal.tsum_prod']
    conv =>
      enter [1, 1, a]
      simp
      rw [ENNReal.tsum_mul_left]
      rw [IH]
    simp

    -- Change noise to SPMF
    have S := (privNoiseGuess ε₁ ε₂).2
    apply HasSum.tsum_eq S


def sv3_sv4_loop_eq qs (T : ℤ) (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List sv_T) (point : ℕ) (init : sv1_state) :
    sv3_loop qs T ε₁ ε₂ τ l point init = sv4_loop qs T ε₁ ε₂ τ l point init := by
  revert init
  induction point
  · -- It's a mess but it works
    intro init
    simp [sv3_loop, sv4_loop, probWhileCut, probWhileFunctional, sv4_presample, sv4_aboveThreshC]
    split
    · simp [sv4_aboveThreshF, sv1_aboveThreshF]
      apply SLang.ext
      intro final_state
      simp
    · apply SLang.ext
      intro final_state
      simp
      split
      · rename_i h
        simp_all
        symm
        rw [condition_to_subset]
        have tsum_eq_single_stub :
            ∀ (f : ↑{a : sv4_state | init = a.1} → ENNReal) (x₀ : ↑{a : sv4_state | init = a.1}),
              (∀ b, b ≠ x₀ → f b = 0) → (∑' b, f b) = f x₀ := by sorry
        rw [tsum_eq_single_stub _ (⟨(init, []), rfl⟩ : ↑{a : sv4_state | init = a.1})]
        · simp
        · intro b hb
          rcases b with ⟨⟨b1, b2⟩, Hb⟩
          simp at Hb
          subst Hb
          rw [if_neg]
          intro Hk
          apply hb
          simp at Hk
          cases Hk
          rfl
      · symm
        simp
        intro i H
        rcases i
        intro HK
        rename_i hk2 _ _
        apply hk2
        cases HK
        simp at H
        trivial
  · -- Inductive case
    intro init
    rename_i point IH

    -- Unfold sv3_loop on the left
    rw [sv3_loop_unroll_1_alt]

    -- Apply the IH on the left
    -- Doing it this way because I can't conv under the @ite?

    let ApplyIH :
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
      · rw [IH]
      · rfl

    rw [ApplyIH]
    clear ApplyIH IH
    have ToPresample :
        (do
          let vk1 ← privNoiseGuess ε₁  ε₂
          if sv1_aboveThreshC qs T τ l init = true then sv4_loop qs T ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1) else probPure init) =
        (do
          let vps ← sv4_presample ε₁ ε₂ 1
          let vk1 := len_1_list_to_val vps
          if sv1_aboveThreshC qs T τ l init = true then sv4_loop qs T ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1) else probPure init) := by
      apply SLang.ext
      intro final_state
      simp
      -- There is a bijection here
      rw [vector_sum_singleton _ (by simp)]
      apply tsum_congr
      intro x
      simp [len_1_list_to_val]
      simp [sv4_presample]
      rw [ENNReal.tsum_eq_add_tsum_ite x]
      simp
      have X : (∑' (x_1 : ℤ),
          @ite ENNReal (x_1 = x) (Classical.propDecidable _) 0
            (if x = x_1 then SLang.privNoiseGuess ε₁ ε₂ x_1 else 0)) = 0 := by
        simp; aesop

      conv =>
        enter [2, 1, 2]
        skip
        rw [X]
      simp

    rw [ToPresample]
    clear ToPresample

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
      -- Seems that the RHS inner sum is an indicator on final_state, so I should
      -- commute that out front
      conv =>
        enter [2, 1, a]
        rw [<- ENNReal.tsum_mul_left]
      conv =>
        enter [2]
        rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ⟨ ns_state, ns_presamples ⟩ -- Not sure what the variable ns represents?
      simp
      split <;> try simp
      rename_i HF

      -- Investigate the RHS term for simplifications?
      rcases vsample_1 with ⟨ vs1, Hvs1 ⟩
      rcases vsample_rest with ⟨ vsr, Hvsr ⟩
      cases vs1
      · simp at Hvs1
      rename_i vs1 vs_emp
      conv =>
        enter [2, 1, a, 1]
        unfold sv4_aboveThreshF
        simp [len_list_append_rev]
      have Hemp : vs_emp = [] := by cases vs_emp <;> simp_all
      simp_all
      congr

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
      · conv =>
          enter [1]
          rw [<- mul_one (sv4_presample _ _ _ _)]
        congr 1
        symm
        apply presample_norm_lemma
      · simp

def sv4_aboveThresh (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- sv4_loop qs T ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point

def sv3_sv4_eq qs (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv3_aboveThresh qs T ε₁ ε₂ l = sv4_aboveThresh qs T ε₁ ε₂ l := by
    unfold sv3_aboveThresh
    unfold sv4_aboveThresh
    simp
    conv =>
      enter [1, x, 1, y, 2, 1, z]
      rw [sv3_sv4_loop_eq]

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

def sv4_sv5_eq (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
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

-- -- When you look at exactly n loops in the future, the check evaluates to true
-- def sv6_aboveThresh_check (τ : ℤ) (l : List ℕ) (s : sv4_state) (n : ℕ) : Bool :=
--   match n with
--   | 0 => true
--   | Nat.succ n' =>
--     match s with
--     -- If there is more samples on the tape, call recursively
--     | ((past, present), (future_next :: future_rest)) =>
--       sv4_aboveThreshC τ l ((past, present), (future_next :: future_rest)) ∧
--       sv6_aboveThresh_check τ l ((past ++ [present], future_next), future_rest) n'
--     | (_, []) =>
--       -- Out of samples on the tape
--       false

-- The state sp is a "past configuration" of sc, ie. one we already checked
def is_past_configuration (sp sc : sv4_state) : Prop :=
  (sp.1.1.length ≤ sc.1.1.length) ∧ sp.1.1 ++ [sp.1.2] ++ sp.2 = sc.1.1 ++ [sc.1.2] ++ sc.2

-- All past configurations had their loop check execute to True
def sv6_aboveThresh_hist (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (s : sv4_state) : Prop :=
  ∀ sp, (is_past_configuration sp s) -> sv4_aboveThreshC qs T τ l sp = true


-- If all past configurations of sp evaluate to True,
-- and the next one evaluates to true,
-- then all past configurations for the next one evaluate to True
lemma sv6_aboveThresh_hist_step (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (past fut_rest : List ℤ) (present fut : ℤ) :
    sv6_aboveThresh_hist qs T τ l ((past, present), fut :: fut_rest) ->
    sv4_aboveThreshC qs T τ l ((past ++ [present], fut), fut_rest) ->
    sv6_aboveThresh_hist qs T τ l ((past ++ [present], fut), fut_rest) := by
  intro H1 H2
  unfold sv6_aboveThresh_hist
  intro s H3
  unfold is_past_configuration at H3
  rcases H3 with ⟨ H3, H4 ⟩
  simp_all

  apply Nat.lt_or_eq_of_le at H3
  cases H3
  · -- The length of s1.1.1 is less than or equal to past
    apply H1
    apply And.intro
    · linarith
    · simp_all
  · rename_i Hs11_len
    -- The length of s.1.1 is equal to past.length + 1
    -- Now we can characterize s
    have Hs11 : List.take (past.length + 1) (s.1.1 ++ s.1.2 :: s.2) =
                List.take (past.length + 1) (past ++ present :: fut :: fut_rest) := by
      rw [H4]
    rw [List.take_left' Hs11_len] at Hs11
    simp [List.take_append] at Hs11
    simp_all
    obtain ⟨⟨s11, s12⟩, s2⟩ := s
    simp_all
    rw [List.take_of_length_le (by simp)] at H4 ⊢
    simp at H4
    obtain ⟨rfl, rfl⟩ := H4
    exact H2


def is_past_configuration_strict (sp sc : sv4_state) : Prop :=
  (sp.1.1.length < sc.1.1.length) ∧ sp.1.1 ++ [sp.1.2] ++ sp.2 = sc.1.1 ++ [sc.1.2] ++ sc.2

-- All strictly past configurations had their loop check execute to True
def sv6_aboveThresh_hist_strict (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (s : sv4_state) : Prop :=
  ∀ sp, (is_past_configuration_strict sp s) -> sv4_aboveThreshC qs T τ l sp = true

lemma sv6_aboveThresh_hist_step_strict (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (past fut_rest : List ℤ) (present fut : ℤ) :
    sv6_aboveThresh_hist_strict qs T τ l ((past, present), fut :: fut_rest) ->
    sv4_aboveThreshC qs T τ l ((past, present), fut :: fut_rest) ->
    sv6_aboveThresh_hist_strict qs T τ l ((past ++ [present], fut), fut_rest) := by
  intro H1 H2
  unfold sv6_aboveThresh_hist_strict
  intro s H3
  unfold is_past_configuration_strict at H3
  rcases H3 with ⟨ H3, H4 ⟩
  simp_all

  apply Nat.lt_or_eq_of_le at H3
  cases H3
  · -- The length of s1.1.1 is less than or equal to past
    apply H1
    apply And.intro
    · linarith
    · simp_all
  · rename_i Hs11_len
    have Hs11 : List.take (past.length) (s.1.1 ++ s.1.2 :: s.2) =
                List.take (past.length) (past ++ present :: fut :: fut_rest) := by
      rw [H4]
    simp at Hs11_len
    rw [List.take_left] at Hs11
    rw [<- Hs11_len] at Hs11
    rw [List.take_left] at Hs11
    cases s
    rename_i s1 s2
    cases s1
    rename_i s11 s12
    simp_all

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

-- QUESTION: What do we need for equality in the base case?
lemma sv5_sv6_loop_base_case (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    future = [] ->
    List.length future = eval ->
    List.length (past ++ [pres] ++ future) = point + 1 ->
    (sv6_loop qs T τ l point ((past, pres), future)) point = (sv5_loop qs T τ l eval ((past, pres), future)) point := by
  intro Hfuture Heval Hstate
  rw [Hfuture]
  simp_all
  rw [<- Heval]
  unfold sv5_loop
  unfold probWhileCut
  unfold probWhileFunctional
  split
  · rename_i h
    simp [probWhileCut, sv6_loop]
    rw [h]
    simp
  · rename_i h
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

-- QUESTION: What do we need for sv6_loop to be equal to sv6_loop_cond (next)
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


-- QUESTION: What do we need for sv5 to be equal to sv5_loop_cond (next) evaluated at point
lemma sv5_loop_ind (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (eval point : ℕ) (past ff: List ℤ) (pres f: ℤ) :
      (sv4_aboveThreshC qs T τ l ((past, pres), f :: ff) = true) ->
      (sv5_loop qs T τ l (eval + 1) ((past, pres), f :: ff)) point = (sv5_loop qs T τ l eval ((past ++ [pres], f), ff)) point := by
  intro Hcondition
  conv =>
    lhs
    unfold sv5_loop
    unfold probWhileCut
    unfold probWhileFunctional
  split
  · simp only [bind, pure, sv4_aboveThreshF, pure_bind]
    unfold sv5_loop
    rfl
  · exfalso
    trivial

def sv6_aboveThresh (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let presamples <- sv4_presample ε₁ ε₂ point
    @sv6_loop _ qs T τ l point (([], v0), presamples)
  computation point


-- sv6_loop and sv5_loop are equal at point (under some conditions)
def sv5_sv6_loop_eq_point (qs :  sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    List.length (past ++ [pres] ++ future) = point + 1 ->
    List.length future = eval ->
    -- sv6_aboveThresh_hist_strict τ l ((past, pres), future) ->
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
  · rename_i f ff IH
    intro eval past pres Hstate Heval
    cases eval
    · simp at Heval

    rename_i eval
    cases (Classical.em (sv4_aboveThreshC qs T τ l ((past, pres), f :: ff) = true))
    · rename_i Hcondition
      rw [sv5_loop_ind _ _ _ _ _ _ _ _ _ _ Hcondition]
      rw [sv6_loop_ind _ _ _ _ _ _ _ _ _ Hcondition Hstate]
      apply (IH eval (past ++ [pres]) f ?G1 ?G2)
      case G1 => simp_all
      case G2 => simp_all

    rename_i Hcondition
    simp at Hcondition
    simp [sv6_loop, Hcondition]
    unfold sv5_loop
    unfold probWhileCut
    unfold probWhileFunctional
    rw [Hcondition]
    simp
    intro i Hi Hk
    simp_all [sv1_threshold]


def sv5_sv6_eq (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
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
  · simp
  · exact List.Vector.length_val future


/-
## Program v8
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

def sv6_sv7_eq (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
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
  · rename_i point'
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
      rw [<- ENNReal.tsum_mul_left]
    conv =>
      lhs
      unfold sv6_loop
    simp
    rw [ENNReal.tsum_comm]
    rw [← ENNReal.tsum_prod]
    conv =>
      rhs
      enter [1, a]
      rw [<- mul_assoc]
      enter [1]
      rw [mul_comm]
      rw [sv4_presample_split']
    apply @tsum_eq_tsum_of_ne_zero_bij
    case i =>
      exact fun x => ⟨ x.1.2.1 ++ [x.1.1], by simp ⟩
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
      simp
      apply And.intro
      · apply And.intro
        · intro K
          apply Hf1
          rw [<- K]
          congr
          simp [vsm_init, vsm_last]
          symm
          apply drop_init_lemma
          intro K
          simp [K] at HL
        · intro K
          apply Hf2
          rw [<- K]
          split <;> split
          · rfl
          · exfalso
            rename_i h1 h2
            apply h2
            rw [<- h1]
            congr
            simp [vsm_init, vsm_last]
            apply drop_init_lemma
            intro K
            simp [K] at HL
          · exfalso
            rename_i h2 h1
            apply h2
            rw [<- h1]
            congr
            simp [vsm_init, vsm_last]
            symm
            apply drop_init_lemma
            intro K
            simp [K] at HL
          · rfl
      · simp [vsm_init, vsm_last]
        apply drop_init_lemma
        intro K
        simp [K] at HL
    · simp

/-
## Program v8

Not executable
Defines G from the paper
-/



def sv8_sum (qs :  sv_query sv_T) (l : List sv_T) (past : List ℤ) (pres : ℤ) : ℤ :=
  qs (List.length past) l + pres
  -- exactDiffSum (List.length past) l + pres

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
  · intro vi init
    rename_i vi_1 rest IH
    have IH' := IH vi_1 (init ++ [vi])
    simp at IH'
    clear IH
    conv =>
      rhs
      simp [sv6_cond_rec]
    rw [<- IH']
    clear IH'
    cases (decide (τ + T ≤ sv8_sum qs l (init ++ vi :: vi_1 :: rest) vk)) <;> simp
    conv =>
      lhs
      unfold sv8_G
      simp
    cases (decide (sv8_G qs l (init ++ [vi]) vi_1 rest < τ + T)) <;> simp
    simp [sv4_aboveThreshC, sv1_aboveThreshC, sv8_sum, sv1_threshold, sv1_noise]


def sv7_sv8_eq (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv7_aboveThresh qs T ε₁ ε₂ l = sv8_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv7_aboveThresh
  unfold sv8_aboveThresh
  cases point
  · simp [sv4_aboveThreshC, sv1_aboveThreshC, sv8_sum, sv1_threshold, sv1_noise]
  rename_i point'
  simp only []
  repeat (apply tsum_congr; intro _; congr 1)
  simp only [sv7_sv8_cond_eq, sv6_cond]


/-
## Program v9

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

def sv8_sv9_eq (qs :  sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) :
    sv8_aboveThresh qs T ε₁ ε₂ l = sv9_aboveThresh qs T ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv8_aboveThresh
  unfold sv9_aboveThresh
  simp
  split
  · simp
  · simp
    conv =>
      lhs
      conv =>
        enter [1, a]
        rw [<- ENNReal.tsum_mul_left]
        conv =>
          enter [1, b]
          rw [<- mul_assoc]
          conv =>
            enter [1]
            rw [mul_comm]
          rw [mul_assoc]
      rw [ENNReal.tsum_comm]
      conv =>
        enter [1, b]
        rw [ENNReal.tsum_mul_left]

    apply tsum_congr
    intro b
    congr 1

    conv =>
      lhs
      conv =>
        enter [1, a]
        rw [<- ENNReal.tsum_mul_left]
        conv =>
          enter [1, b]
          rw [<- mul_assoc]
          conv =>
            enter [1]
            rw [mul_comm]
          rw [mul_assoc]
      rw [ENNReal.tsum_comm]
      conv =>
        enter [1, b]
        rw [ENNReal.tsum_mul_left]


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
  simp [Function.Injective]


lemma ENNReal.tsum_split (P : T -> Prop) (f : T -> ENNReal) :
    ∑' (a : T), f a = (∑'(a : {t : T // P t}), f a.1) + (∑'(a : {t : T // ¬P t}), f a.1) := by
  symm
  apply Summable.tsum_add_tsum_compl (f := f) (s := {t | P t}) <;> apply ENNReal.summable

/-
def β_geo (β : ENNReal) : SLang ℕ := (probGeometric (fun x => if x then β else 1 - β))

def β_geo_recurrence (β : ENNReal) (n : ℕ) (H : n > 0) : β_geo β (n + 1) = β * β_geo β n := by
  simp [β_geo, probGeometric_apply]
  split
  · exfalso
    simp_all
  · ring_nf
    rename_i h
    rw [mul_pow_sub_one h]

def β_geo' (β : ℝ) : ℕ -> ℝ :=
  fun N =>
    match N with
    | 0 => 0
    | Nat.succ N' => ENNReal.toReal (β_geo β N')
-/

def geo_cdf (β : ENNReal) (n : ℕ) : ENNReal := 1 - (1 - β)^n


-- set_option pp.coercions false
lemma geo_cdf_rec (β : ENNReal) (Hβ1: β ≤ 1) (n : ℕ) :
      geo_cdf β (n + 1) = β + (1 - β) * geo_cdf β n := by
  unfold geo_cdf
  /-
  suffices ENNReal.toEReal (1 - (1 - β) ^ (n + 1)) = ENNReal.toEReal (β + (1 - β) * (1 - (1 - β) ^ n)) by
    apply EReal.coe_ennreal_injective
    apply this
  -/

  suffices ENNReal.toReal (1 - (1 - β) ^ (n + 1)) = ENNReal.toReal (β + (1 - β) * (1 - (1 - β) ^ n)) by
    apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
    cases this
    · trivial
    rename_i this
    cases this
    · rename_i h
      rcases h with ⟨ A, B ⟩
      simp_all
      exfalso
      cases B
      · simp_all
      · rename_i h
        apply ENNReal.mul_eq_top.mp at h
        simp_all
    · rename_i h
      rcases h with ⟨ A, _ ⟩
      simp_all
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




end equiv


abbrev has_lucky {sv_T : Type} (qs : sv_query sv_T) (T : ℤ) : Prop :=
  ∀ (τ : ℤ) (l : List sv_T), ∃ (K : ℤ), ∀ A, ∀ (K' : ℤ), K ≤ K' -> qs A l + K' ≥ τ + T

section pmf

lemma ite_conv_left {P : Prop} {D} {a b c : ENNReal} (H : a = c) : @ite _ P D a b = @ite _ P D c b := by
  split <;> trivial

lemma ite_mono_left {P : Prop} {D} {a b c : ENNReal} (H : a ≤ c) : @ite _ P D a b ≤ @ite _ P D c b := by
  split <;> trivial

lemma ite_lemma_1 {P : Prop} {D} {f : T -> ENNReal} : ∑'(a : T), @ite _ P D (f a) 0 = @ite _ P D (∑'(a : T), f a) 0 := by
  split
  · rfl
  · simp

variable (qs :  sv_query sv_T)
variable (T : ℤ)
variable (lucky_guess : has_lucky qs T)

include lucky_guess in
lemma sv1_lb ε₁ ε₂ l :
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
    apply Eq.le
    rw [ENNReal.tsum_mul_right]
    simp
    have R1 : ∑' (a : ℤ), (privNoiseThresh ε₁ ε₂) a = 1 := by
      rw [<- Summable.hasSum_iff ENNReal.summable]
      cases (privNoiseThresh ε₁ ε₂)
      simp [DFunLike.coe, SPMF.instFunLike]
      trivial
    simp_all
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
    apply ENNReal.tsum_iSup_comm'
  apply le_trans _ ?G1
  case G1 =>
    apply ENNReal.tsum_le_tsum
    intro v0
    apply mul_le_mul_right
    apply ENNReal.tsum_iSup_comm'
  simp
  conv =>
    enter [2, 1, v0]
    rw [ENNReal.mul_iSup]
  apply le_trans _ ?G1
  case G1 =>
    apply ENNReal.tsum_iSup_comm'

  -- The lucky event: sampling above a value T, which forces the loop to terminate
  rcases (lucky_guess τ l) with ⟨ K, HK ⟩
  let PLucky (K' : ℤ) : Prop := K ≤ K'
  have HLucky : ∀ (K' : ℤ), ∀ A, PLucky K' → qs A l + K' ≥ τ + T := by
    aesop
  clear HK

  -- We will split the sum based on PLucky at each step

  -- ρ is the probability of the lucky event
  let ρ : ENNReal := (∑'(a : {t : ℤ // PLucky t}), privNoiseGuess ε₁ ε₂ a.1)
  have Hρ_1 : (∑'a, privNoiseGuess ε₁ ε₂ a) = 1 := by
    cases (privNoiseGuess ε₁ ε₂)
    simp [DFunLike.coe, SPMF.instFunLike]
    rw [<- Summable.hasSum_iff ENNReal.summable]
    trivial
  have Hρ_lb : 0 < ρ := by
    -- There is at least one lucky element
    have HU : PLucky K := by simp [PLucky]
    apply LT.lt.trans_le _ ?G2
    case G2 => apply ENNReal.le_tsum ⟨ _, HU ⟩
    simp [privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure, DiscreteLaplaceGenSamplePMF]
    simp [DFunLike.coe, PMF.instFunLike]
    apply mul_pos
    · apply div_pos
      · simp
      · apply Right.add_pos'
        · apply Real.exp_pos
        · simp
    · apply Real.exp_pos
  have Hρ_nz : ρ ≠ 0 := by apply pos_iff_ne_zero.mp Hρ_lb
  have Hρ_ub : ρ ≤ 1 := by
    rw [<- Hρ_1]
    rw [ENNReal.tsum_split PLucky]
    simp_all only [ge_iff_le, self_le_add_right, PLucky, ρ]
  have Hρ_ub_strict : ρ < 1 := by
    rw [<- Hρ_1]
    rw [ENNReal.tsum_split PLucky]
    conv =>
      lhs
      rw [<- add_zero ρ]
    apply ENNReal.add_lt_add_of_le_of_lt
    · intro X; simp_all
    · rfl
    · -- There is at least one unlucky element
      have HU : ¬PLucky (K - 1) := by simp [PLucky]
      apply LT.lt.trans_le _ ?G2
      case G2 => apply ENNReal.le_tsum ⟨ _, HU ⟩
      simp [privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure, DiscreteLaplaceGenSamplePMF]
      simp [DFunLike.coe, PMF.instFunLike]
      apply mul_pos
      · apply div_pos
        · simp
        · apply Right.add_pos'
          · apply Real.exp_pos
          · simp
      · apply Real.exp_pos

  -- Bound the CDF below by the geometric CDF
  apply @le_trans _ _ _ (⨆(y : ℕ), geo_cdf ρ y)
  · -- Math
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
      rw [<- ENNReal.toNNReal_pow] at HN
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
    exact absurd (show _ < _ from GT.gt.lt ‹_›) (LE.le.not_gt H')
  apply iSup_mono
  intro cut


  -- Because v0 is not in the loop, we need to do one of the unrollings first
  -- Our IH is going to include a condition on "present"
  cases cut
  · -- cut=0 case is trivial
    simp [probWhileCut, geo_cdf]
  rename_i cut

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
               rw [ite_eq_right_iff.mpr]
               intro i
               exfalso
               rcases a with ⟨ v, Hv ⟩
               simp [sv1_threshold] at i
               have luck := HLucky v 0 Hv
               apply (LT.lt.not_ge i)
               trivial)]
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
    clear this
    rw [<- Hρ_1]
    conv =>
      enter [1, 1]
      rw [ENNReal.tsum_split PLucky]
    apply ENNReal.add_sub_cancel_left
    exact LT.lt.ne_top Hρ_ub_strict

  -- Now we have the right inductive structure
  induction cut
  · -- Base case is trivial?
    simp [geo_cdf]
  · rename_i cut IH
    intro H a
    rcases a with ⟨ v, Hv ⟩
    simp

    -- Because the first sample is not lucky, we can't say anything about the branch we end up in
    -- It may terminate, or it may not.
    have advance :
      ((∑' (x1 : ℕ) (x2 : sv1_state),
            if x1 = sv1_threshold x2
              then (sv1_aboveThreshF ε₁ ε₂ (H, v)).probBind (fun v => probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1) v) x2
              else 0)
        ≤ (∑' (x : ℕ) (x_1 : sv1_state), if x = sv1_threshold x_1 then probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) (cut + 1 + 1) (H, v) x_1 else 0)) := by
      conv =>
        rhs
        enter [1, x1, 1, x2]
        unfold probWhileCut
        unfold probWhileFunctional
        simp
      split
      · simp
      · simp
        -- RHS is 1
        apply ENNReal.tsum_lb_single (List.length H)
        apply ENNReal.tsum_lb_single (H, v)
        conv =>
          rhs
          simp [sv1_threshold]

        -- LHS is bounded above by 1 by upper bound lemma
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
        simp [sv1_aboveThreshF]
        apply le_trans
        · apply ENNReal.tsum_le_tsum
          intro a
          simp
          apply ENNReal.tsum_le_tsum
          intro a1
          gcongr

        rw [ENNReal.tsum_comm]
        conv =>
          lhs
          enter [1, b]
          rw [ENNReal.tsum_mul_left]
        apply le_trans (b := ∑' (x : ℤ), (privNoiseGuess ε₁ ε₂) x * 1)
        · apply ENNReal.tsum_le_tsum
          intro x
          gcongr
          apply sv1_loop_ub
        · simp only [mul_one]
          rcases (privNoiseGuess ε₁ ε₂) with ⟨ X, Y ⟩
          apply Eq.le
          simp only [DFunLike.coe]
          exact HasSum.tsum_eq Y
    apply le_trans _ advance
    simp
    clear advance

    -- Now we want to commute out the randomness associate to that s1_aboveThreshF
    apply le_trans _ ?G1
    case G1 =>
      apply ENNReal.tsum_le_tsum
      intro x
      apply ENNReal.tsum_le_tsum
      intro x_1
      rw [<- ite_lemma_1]
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

      conv =>
        enter [2, 1, a, 1, b]
        conv =>
          enter [1, c]
          conv =>
            enter [1, d]
            rw [<- mul_ite_zero]
          rw [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_left]

      -- Conclude by simplification
      simp only [sv1_aboveThreshF, bind, pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
      unfold probWhileCut
      unfold probWhileFunctional
      -- Push the ite inside so that all of the sums are in a row
      conv =>
        enter [2, 1, a, 1, b]
        rw [<- ENNReal.tsum_mul_right]
        simp
        enter [1, i]
        rw [<- mul_ite_zero]
        enter [2]
        rw [<- ite_lemma_1]
        conv =>
          enter [1, x]
          rw [<- ite_lemma_1]
      conv =>
        enter [2, 1, a, 1, b, 1, i]
        rw [<- ENNReal.tsum_mul_left]
        enter [1, c]
        rw [<- ENNReal.tsum_mul_left]
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
      -- STUB: bounding the middle → target step.
      -- The middle is a simpler indicator expression; the target is the full probWhileCut unfold.
      -- Pointwise: priv a * (small_indicator) ≤ priv a * (big probWhileCut expression).
      have mid_le_target :
          (∑' (b : ℤ) (a : ℤ) (c : { t // PLucky t }),
            (privNoiseGuess ε₁ ε₂) a *
              @ite ENNReal ((H ++ [v], ↑c) = (H ++ [v], a)) (Classical.propDecidable _)
                (if H.length + 1 = sv1_threshold (H ++ [v], b) then 1 else 0) 0) ≤
          (∑' (b : ℤ) (a : ℤ) (c : { t // PLucky t }),
            (privNoiseGuess ε₁ ε₂) a *
              @ite ENNReal ((H ++ [v], ↑c) = (H ++ [v], a)) (Classical.propDecidable _)
                (if H.length + 1 = sv1_threshold (H ++ [v], b) then
                  (if sv1_aboveThreshC qs T τ l (H ++ [v], ↑c) = true then
                      (sv1_aboveThreshF ε₁ ε₂ (H ++ [v], ↑c)).probBind fun v =>
                        probWhileCut (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) cut v
                    else probPure (H ++ [v], ↑c))
                    (H ++ [v], b)
                else 0) 0) := by
        sorry
      /-
      Original proof (pre-4.28 port). Needs re-working for gcongr / mul_le_mul_* signature changes
      and ite_mono_left unification across the pair-vs-scalar condition.

      apply le_trans _ ?G1
      case G1 =>
        apply ENNReal.tsum_le_tsum
        intro b
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_le_tsum
        intro c
        gcongr
        simp [sv1_threshold]
        simp [sv1_aboveThreshC]
        apply ite_mono_left
        rw [ite_eq_right_iff.mpr (by
          intro K
          exfalso
          rcases c with ⟨ c, Hc ⟩
          simp [sv1_threshold, sv1_noise] at K
          have HC' := HLucky c (H.length + 1) Hc
          apply (LT.lt.not_ge K)
          apply GE.ge.le
          apply HC')]
      -/
      apply le_trans _ mid_le_target

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
      rw [if_pos]
      simp [sv1_threshold]

    · -- Guess is unlucky
      -- Commute out the samples related to the first sample (which will evenetually become a (1- ρ) factor)
      conv =>
        enter [2, 1, a, 1, b]
        conv =>
          enter [1, c]
          conv =>
            enter [1, d]
            rw [<- mul_ite_zero]
          rw [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_left]
      unfold sv1_state at IH

      apply le_trans _ ?G1
      case G1 =>
        apply ENNReal.tsum_le_tsum
        intro a
        apply ENNReal.tsum_le_tsum
        intro b
        apply mul_le_mul_right
        apply IH
      conv =>
        enter [2, 1, a]
        rw [ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_mul_right]
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
      rw [<- Hρ_1]
      rw [ENNReal.tsum_split PLucky]
      rw [add_comm]


def sv1_aboveThresh_PMF (ε₁ ε₂ : ℕ+) (l : List sv_T) : SPMF ℕ :=
  ⟨ sv1_aboveThresh qs T ε₁ ε₂ l,
    by
      rw [Summable.hasSum_iff ENNReal.summable]
      apply LE.le.antisymm
      · apply sv1_ub
      · exact sv1_lb qs T lucky_guess ε₁ ε₂ l ⟩

/--
sv9 normalizes because sv1 normalizes
-/
def sv9_aboveThresh_SPMF (ε₁ ε₂ : ℕ+) (l : List sv_T) : SPMF ℕ :=
  ⟨ @sv9_aboveThresh PureDPSystem laplace_pureDPSystem sv_T qs T ε₁ ε₂ l,
    by
      rw [<- @sv8_sv9_eq]
      rw [<- @sv7_sv8_eq]
      rw [<- @sv6_sv7_eq]
      rw [<- @sv5_sv6_eq]
      rw [<- @sv4_sv5_eq]
      rw [<- @sv3_sv4_eq]
      rw [<- @sv2_sv3_eq]
      rw [<- @sv1_sv2_eq]
      rw [Summable.hasSum_iff ENNReal.summable]
      apply LE.le.antisymm
      · apply sv1_ub
      · exact sv1_lb qs T lucky_guess ε₁ ε₂ l ⟩

end pmf

end SLang
