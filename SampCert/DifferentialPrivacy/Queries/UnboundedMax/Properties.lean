/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Abstract

noncomputable section
open Classical

namespace SLang


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
  intro t ⟨ Hp, _ ⟩
  simp [Set.BijOn.equiv]
  rw [Hcong]
  apply Hp


/-
## Helper programs
-/

/--
Sum over a list, clipping each element to a maximum.

Similar to exactBoundedSum, however exactClippedSum allows m = 0.
-/
def exactClippedSum (m : ℕ) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n m)) l)

/--
Rate at which a given clipping thresold is impacting the accuracy of the sum.

Always negative or zero.
-/
def exactDiffSum (m : ℕ) (l : List ℕ) : ℤ := exactClippedSum m l - exactClippedSum (m + 1) l

/--
Noise the constant 0 value using the abstract noise function.

This looks strange, but will specialize to Lap(ε₁/ε₂, 0) in the pure DP case.
-/
def privNoiseZero [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) : SLang ℤ := dps.noise (fun _ => 0) 1 ε₁ ε₂ []

/-
Not used for anything, but to give confidence in our definitions

(exactDiffSum l m) is zero if and only if m is an upper bound on the list elements
-/
-- lemma exactDiffSum_eq_0_iff_ge_max (l : List ℕ) (m : ℕ) :
--     l.maximum ≤ m <-> exactDiffSum m l ≤ 0 := by
--   apply Iff.intro
--   · induction l
--     · simp [exactDiffSum, exactClippedSum]
--     · rename_i l0 ls IH
--       intro Hmax
--       simp [List.maximum_cons] at Hmax
--       rcases Hmax with ⟨ Hmax0, Hmax1 ⟩
--       have IH' := IH Hmax1
--       clear IH
--       simp [exactDiffSum, exactClippedSum] at *
--       apply Int.add_le_of_le_neg_add
--       apply le_trans IH'
--       simp
--   · intro H1
--     apply List.maximum_le_of_forall_le
--     revert H1
--     induction l
--     · simp
--     · rename_i l0 ls IH
--       intro Hdiff a Ha
--       rw [List.mem_cons_eq] at Ha
--       cases Ha
--       · rename_i H
--         rw [H]
--         rw [Nat.cast_withBot]
--         apply WithBot.coe_le_coe.mpr
--
--         sorry
--       · apply IH; clear IH
--         · simp only [exactDiffSum, exactClippedSum] at *
--           have H : (min (l0.cast : ℤ) (m.cast : ℤ) - min (l0.cast) ((m.cast : ℤ) + 1)) = 0 := by
--             sorry
--           -- rw [H] at Hdiff
--           -- rw [<- Hdiff]
--           -- simp
--           sorry
--         · trivial


/-
## Program version 0
  - Executable
  - Tracks single state
-/

def sv0_state : Type := ℕ × ℤ

def sv0_threshold (s : sv0_state) : ℕ := s.1

def sv0_noise (s : sv0_state) : ℤ := s.2

def sv0_privMaxC (τ : ℤ) (l : List ℕ) (s : sv0_state) : Bool :=
  decide (exactDiffSum (sv0_threshold s) l + (sv0_noise s) < τ)

def sv0_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv0_state) : SLang sv0_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  let n := (sv0_threshold s) + 1
  return (n, vn)

def sv0_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
  let sk <- probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0)
  return (sv0_threshold sk)

/-
## Program version 1
  - Executable
  - Tracks history of samples
-/

def sv1_state : Type := List ℤ × ℤ

def sv1_threshold (s : sv1_state) : ℕ := List.length s.1

def sv1_noise (s : sv1_state) : ℤ := s.2

def sv1_privMaxC (τ : ℤ) (l : List ℕ) (s : sv1_state) : Bool :=
  decide (exactDiffSum (sv1_threshold s) l + (sv1_noise s) < τ)

def sv1_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv1_state) : SLang sv1_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  return (s.1 ++ [s.2], vn)

def sv1_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
  let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
  return (sv1_threshold sk)

/--
History-aware progam computes the same as the history-agnostic program
-/
lemma sv0_eq_sv1 [dps : DPSystem ℕ] ε₁ ε₂ l : sv0_privMax ε₁ ε₂ l = sv1_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Initial setup is equal
  intro result
  simp [sv0_privMax, sv1_privMax]
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1

  -- unfold sum over product; term re. last sample should be equal as well
  conv =>
    congr
    · unfold sv0_state
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    · unfold sv1_state
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  apply tsum_congr
  intro vk

  -- LHS: simplify singleton sum
  conv =>
    enter [1, 1, a]
    simp [sv0_threshold]
  rw [ENNReal.tsum_eq_add_tsum_ite result]
  simp
  rw [@tsum_congr ENNReal ℕ _ _ _ (fun _ => 0) ?G1]
  case G1 =>
    intro
    split <;> simp
    rename_i H1
    intro
    exfalso
    apply H1
    symm
    trivial
  simp only [tsum_zero, add_zero]

  -- RHS: sum over all lists of length "result"?
  -- rw [tsum_ite_eq]
  sorry



/-
## Program version 2
  - Only moves the loop into a non-executable form, ie. explicitly defines the PMF
-/

def sv2_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
    return (sv1_threshold sk)
  computation point

lemma sv1_eq_sv2 [dps : DPSystem ℕ] ε₁ ε₂ l : sv1_privMax ε₁ ε₂ l = sv2_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro result
  simp [sv1_privMax, sv2_privMax]




/-
## Program version 3
  - Truncates the loop
-/

def sv3_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  probWhileCut (sv1_privMaxC τ l) (@sv1_privMaxF dps ε₁ ε₂) (point + 1) init

def sv3_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- @sv3_loop dps ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point


def cone_of_possibility (cut : ℕ) (initial hist : List ℤ) : Prop :=
  (hist.length < cut + initial.length) ∧ (initial.length ≤ hist.length)

def constancy_at [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) : Prop :=
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) (1 + cut) (initial, v0) (hist, vk) =
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut       (initial, v0) (hist, vk)


-- All points outside of the cone are zero
lemma external_to_cone_zero [DPSystem ℕ] :
    (¬ cone_of_possibility cut initial hist) ->
    probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut (initial, v0) (hist, vk) = 0 := by
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
        simp [sv1_privMaxF]
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
lemma cone_left_edge_constancy [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    hist.length = initial.length ->
    cone_of_possibility cut initial hist ->
    @constancy_at _ ε₁ ε₂ τ data v0 vk cut initial hist := by
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

  cases (sv1_privMaxC τ data (initial, v0))
  · -- False case: both programs terminate with initial state
    simp
  · -- True case: both programs step to a point outside of the cone, so are zero
    simp
    apply tsum_congr
    intro ⟨ initial', v1 ⟩

    simp [sv1_privMaxF]
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


lemma cone_constancy [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    cone_of_possibility cut initial hist ->
    @constancy_at _ ε₁ ε₂ τ data v0 vk cut initial hist := by
  -- Need theorem to be true for all initial states, since this will increase during the induction
  -- v0 and vk will also change in ways which don't matter
  revert initial v0 vk

  induction cut
  · -- Not true base case (cut 0 is always outside of the cone)
    -- Mercifully it is easy to prove
    intro v0 vk initial Hcone
    unfold constancy_at
    simp [probWhileCut, probWhileFunctional]
    cases (sv1_privMaxC τ data (initial, v0)) <;> simp
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
  cases (sv1_privMaxC τ data (initial, v0))
  · simp


  -- If the conditional is true, we decrement N by one and add a sample to the history
  rename_i Hcone_interior
  unfold constancy_at at IH
  simp
  apply tsum_congr
  intro ⟨ initial', vk' ⟩

  -- We only need to consider the cases where sv1_privMaxF is nonzero
  -- And this is exactly the case where initial' is initial plus one element
  simp [sv1_privMaxF]
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


lemma sv2_eq_sv3 [dps : DPSystem ℕ] ε₁ ε₂ l : sv2_privMax ε₁ ε₂ l = sv3_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Step through equal headers
  intro point
  unfold sv2_privMax
  unfold sv3_privMax
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
  apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ (hist.length + 1)
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
    have HK := @cone_constancy dps ε₁ ε₂ τ l v0 vk i [] hist
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
lemma sv3_loop_unroll_1 [dps : DPSystem ℕ] (τ : ℤ) (ε₁ ε₂ : ℕ+) l point L vk :
    sv3_loop ε₁ ε₂ τ l (point + 1) (L, vk) =
    (do
      let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
      if (sv1_privMaxC τ l (L, vk))
        then (sv3_loop ε₁ ε₂ τ l point (L ++ [vk], vk1))
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
      unfold sv1_privMaxF
      simp
    conv =>
      enter [1, 1, a]
      rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro a
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite ?G1]
    case G1 => apply (L ++ [vk], a)
    split
    · conv =>
        rhs
        rw [<- add_zero (_ * _)]
      congr 1
      simp
      intro i HK1 HK2
      exfalso
      apply HK1
      apply HK2
    · exfalso
      rename_i hk
      apply hk
      rfl
  · simp
    apply SLang.ext
    intro ⟨ HF, vkf ⟩
    simp [probBind]
    split <;> try simp
    unfold privNoiseZero
    exact Eq.symm (PMF.tsum_coe (DPSystem.noise (fun _ => 0) 1 ε₁ (4 * ε₂) []))

/-
## Program version 4
  - Executable
  - Presamples at each point, and then executes a deterministic loop
-/

-- An sv4 state is an sv1 state plus a list of presamples
def sv4_state : Type := sv1_state × List ℤ

def sv4_presample [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang { l : List ℤ // List.length l = n } :=
  match n with
  | Nat.zero => return ⟨ [], by simp ⟩
  | Nat.succ n' => do
    let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let vks  <- @sv4_presample dps ε₁ ε₂ n'
    return ⟨ vks ++ [vk1], by simp ⟩


def sv4_privMaxF (s : sv4_state) : SLang sv4_state :=
  match s.2 with
  | [] => probZero
  | (p :: ps) => return ((s.1.1 ++ [s.1.2], p), ps)

def sv4_privMaxC (τ : ℤ) (l : List ℕ) (st : sv4_state) : Bool := sv1_privMaxC τ l st.1

def sv4_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  let presamples <- @sv4_presample dps ε₁ ε₂ point
  let v <- probWhileCut (sv4_privMaxC τ l) sv4_privMaxF (point + 1) (init, presamples)
  return v.1

lemma sv3_loop_unroll_1_alt [dps : DPSystem ℕ] (τ : ℤ) (ε₁ ε₂ : ℕ+) l point (initial_state : sv1_state) :
    sv3_loop ε₁ ε₂ τ l (point + 1) initial_state =
    (do
      let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
      if (sv1_privMaxC τ l initial_state)
        then (sv3_loop ε₁ ε₂ τ l point (initial_state.1 ++ [initial_state.2], vk1))
        else probPure initial_state) := by
  rcases initial_state with ⟨ _ , _ ⟩
  rw [sv3_loop_unroll_1]

def len_list_append_rev {m n : ℕ} (x : { l : List ℤ // l.length = m }) (y: { l : List ℤ // l.length = n }) : { l : List ℤ // l.length = n + m } :=
  ⟨ x.1 ++ y.1 , by simp  [add_comm] ⟩

def sv4_presample_split [DPSystem ℕ] (ε₁ ε₂ : ℕ+) (point : ℕ) :
    sv4_presample ε₁ ε₂ (point + 1) =
    (do
      let presample_1 <- sv4_presample ε₁ ε₂ 1
      let presample_r <- sv4_presample ε₁ ε₂ point
      return len_list_append_rev presample_1 presample_r) := by
  apply SLang.ext
  intro final_state
  simp [sv4_presample]

  -- By bijection
  -- #check tsum_eq_tsum_of_ne_zero_bij
  sorry


def len_1_list_to_val (x : { l : List ℤ // l.length = 1 }) : ℤ :=
  let ⟨ xl, _ ⟩ := x
  match xl with
  | (v :: _) => v


-- When we do induction on point,
-- We will want to generalize over all init
-- Unfolding this loop just moves the first presample into init
-- Which can apply the IH-- since it's some arbitrary init state and a presamples state generated by one fewer point


def sv3_sv4_loop_eq [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) :
    @sv3_loop dps ε₁ ε₂ τ l point init = @sv4_loop dps ε₁ ε₂ τ l point init := by
  revert init
  induction point
  · -- It's a mess but it works
    intro init
    simp [sv3_loop, sv4_loop, probWhileCut, probWhileFunctional, sv4_presample, sv4_privMaxC]
    split
    · simp [sv4_privMaxF, sv1_privMaxF]
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
        rw [ENNReal.tsum_eq_add_tsum_ite ⟨(init, []), rfl⟩]
        simp_all
        conv =>
          rhs
          rw [<- add_zero 1]
        congr
        simp
        intro a
        rcases a
        simp_all
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
      (do
        let vk1 ← privNoiseZero ε₁ (4 * ε₂)
        if sv1_privMaxC τ l init = true
          then sv3_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else probPure init) =
      (do
        let vk1 ← privNoiseZero ε₁ (4 * ε₂)
        if sv1_privMaxC τ l init = true
          then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else probPure init) := by
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
          let vk1 ← privNoiseZero ε₁ (4 * ε₂)
          if sv1_privMaxC τ l init = true then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1) else probPure init) =
        (do
          let vps ← sv4_presample ε₁ ε₂ 1
          let vk1 := len_1_list_to_val vps
          if sv1_privMaxC τ l init = true then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1) else probPure init) := by
      apply SLang.ext
      intro final_state
      simp
      -- There is a bijection here
      sorry

    rw [ToPresample]
    clear ToPresample

    -- Now, just need to prove this unfolding of sv4_loop
    unfold sv4_loop
    conv =>
      enter [2]
      unfold probWhileCut
      unfold probWhileFunctional
      unfold sv4_privMaxC

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
        unfold sv4_privMaxF
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
        sorry
        -- Sum of PMF is 1
      · simp


def sv4_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- @sv4_loop dps ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point

def sv3_eq_sv4 [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @sv3_privMax dps ε₁ ε₂ l = @sv4_privMax dps ε₁ ε₂ l := by
    unfold sv3_privMax
    unfold sv4_privMax
    simp
    conv =>
      enter [1, x, 1, y, 2, 1, z]
      rw [sv3_sv4_loop_eq]


/-
## Program version 5
  - Executable
  - Isolates the loop for the next step
-/

def sv5_loop (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang ℕ := do
  let sk <- probWhileCut (sv4_privMaxC τ l) sv4_privMaxF (point + 1) init
  return (sv1_threshold sk.1)

def sv5_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let presamples <- @sv4_presample dps ε₁ ε₂ point
    @sv5_loop τ l point (([], v0), presamples)
  computation point

def sv4_eq_sv5 [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @sv4_privMax dps ε₁ ε₂ l = @sv5_privMax dps ε₁ ε₂ l := by
  unfold sv4_privMax
  unfold sv5_privMax
  unfold sv4_loop
  unfold sv5_loop
  simp


/-
## Program version 6
  - Executable
  - Changes the loop from a probWhileCut into a single, deterministic, check
-/


-- Evaluate the nth conditional starting at state s
-- Return false if the loop will not terminate on iterate n, starting at s
-- Return true if the loop will terminate on iterate n, starting at s
-- Return false if the loop never gets to iterate n, starting at s
def sv6_privMax_nth (τ : ℤ) (l : List ℕ) (s : sv4_state) (n : ℕ) : Bool :=
  match s with
  | ((past, present), future) =>
    match n with
    | 0 => sorry
    | Nat.succ n' => sorry

def sv6_loop (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang ℕ :=
  if (sv6_privMax_nth τ l init point) ∧ ¬ (sv6_privMax_nth τ l init (point + 1))
    then return point
    else probZero

-- These functions are not equal. However, they are equal at "point" (+- 1?)
def sv5_sv6_loop_eq_point (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) :
    @sv5_loop τ l point init point = @sv6_loop τ l point init point := by
  unfold sv5_loop
  unfold sv6_loop

  -- What is the inductive argument? What can I unroll?
  sorry

def sv6_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let presamples <- @sv4_presample dps ε₁ ε₂ point
    @sv6_loop τ l point (([], v0), presamples)
  computation point

def sv5_sv6_eq [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @sv5_privMax dps ε₁ ε₂ l = @sv6_privMax dps ε₁ ε₂ l := by
  unfold sv5_privMax
  unfold sv6_privMax
  apply SLang.ext
  intro eval_point
  simp
  apply tsum_congr
  intro _
  congr
  apply funext
  intro _
  congr
  apply funext
  intro _
  congr
  rw [sv5_sv6_loop_eq_point]
