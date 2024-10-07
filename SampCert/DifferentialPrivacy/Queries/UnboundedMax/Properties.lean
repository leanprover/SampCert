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




/-
def sv4_state : Type := (n : ℕ) × { l : List ℤ // List.length l = n ∧ n > 0}

def sv4_threshold (s : sv4_state) : ℕ := s.1

-- Last noise value, because length > 0
def sv4_last (s : sv4_state) : ℤ := sorry

-- Add one more noise value onto the end
def sv4_append (s : sv4_state) (z : ℤ) : sv4_state := sorry

def sv4_initial (z : ℤ) : sv4_state := sorry


-- TODO? Bijection between sv4_states and sv1_states?

def sv4_privMaxC (τ : ℤ) (l : List ℕ) (s : sv4_state) : Bool :=
  decide (exactDiffSum (sv4_threshold s) l + (sv4_last s) < τ)


def sv4_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv4_state) : SLang sv4_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  return (sv4_append s vn)

def sv4_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang sv4_state := do
  probWhileCut (sv4_privMaxC τ l) (@sv4_privMaxF dps ε₁ ε₂) (point + 1) init


def sv4_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- @sv4_loop dps ε₁ ε₂ τ l point (sv4_initial v0)
    return (sv4_threshold sk)
  computation point


-- sv3 to sv4 argument : there is a bijection between sv3 states and sv4 states
-- Prove this is sv4 to sv5 ends up being provable




def sv5_presample [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang { l : List ℤ // List.length l = n } :=
  match n with
  | Nat.zero => return ⟨ [], by simp ⟩
  | Nat.succ n' => do
    let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let vks  <- @sv5_presample dps ε₁ ε₂ n'
    return ⟨ vks ++ [vk1], by simp ⟩
-/



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




-- New attempt: Let's just actually use consumable tape
-- We will not be able to prove the equality between loops, because they have different types
-- We can still unroll sv3, inductively
-- Can we get equality between loops back, if the tape loop projects out to the non-tape state?
-- Can we unroll tape inductively?


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

    · -- This is true, I'm pretty confident
      -- Both can reduce to probPure init

      sorry

  




-- def sv3_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
--   probWhileCut (sv1_privMaxC τ l) (@sv1_privMaxF dps ε₁ ε₂) (point + 1) init
--
-- def sv3_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
--   fun (point : ℕ) =>
--   let computation : SLang ℕ := do
--     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
--     let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
--     let sk <- @sv3_loop dps ε₁ ε₂ τ l point ([], v0)
--     return (sv1_threshold sk)
--   computation point


/-



-- How much excess state does s have above i
def state_len_excess (i : sv1_state) (s : sv1_state) : Option ℕ :=
  Int.toNat' ((List.length s.1 : Int) - (List.length i.1) : Int)

-- Return the next sample from presamples, ignoring the first n elements
def sv4_next_pre (presamples : List ℤ) (n : ℕ) : Option ℤ :=
  match presamples with
  | [] => none
  | (x :: xs) =>
    match n with
    | 0 => some x
    | (Nat.succ n') => sv4_next_pre xs n'

def sv4_state_shift (s : sv1_state) (z : ℤ) : sv1_state := (s.1 ++ [s.2], z)

-- If there are 5 more samples in state than there are in intial state, we want to ignore the first 5 entries in presamples
def sv4_next_def (initial_state : sv1_state) (presamples : List ℤ) (state : sv1_state) : Option sv1_state := do
  let excess <- state_len_excess initial_state state
  let next_sample <- sv4_next_pre presamples excess
  return (sv4_state_shift state next_sample)

-- Intuition:
-- If there are 5 more samples in state than there are in intial state, we want to ignore the first 5 entries in presamples
def sv4_next (initial_state : sv1_state) (presamples : List ℤ) (state : sv1_state) : SLang sv1_state :=
  match sv4_next_def initial_state presamples state with
  | none => probZero
  | some x => return x


lemma sv4_next_self (st : sv1_state) (y : ℤ) (ys : List ℤ) :
    sv4_next st (y :: ys) st = probPure (sv4_state_shift st y) := by
  simp [sv4_next, sv4_next_def, state_len_excess, Int.toNat', sv4_next_pre]



lemma sv4_next_self_emp (st : sv1_state) :
    sv4_next st [] st = probZero := by
  simp [sv4_next, sv4_next_def, state_len_excess, Int.toNat', sv4_next_pre]






def sv4_privMaxC (τ : ℤ) (l : List ℕ) (st : sv1_state) : Bool := sv1_privMaxC τ l st

-- Assume that st is a prefix state of presamples? If we can't add on a state such that
-- the returned state is still a prefix state, then probZero.
def sv4_privMaxF (initial : sv1_state) (presamples : List ℤ) (st : sv1_state) : SLang sv1_state :=
  sv4_next initial presamples st


-- Init starts out with some length
-- point starts out with a fixed value
-- We want to move "point" samples outwards, while keeping the state the same


-- Partway through, we don't know anything about the initial_length and init relationship
-- Just that the current state "starts with" init
-- The current state "adds onto" init
-- The difference between the new stuff in the state and init is at most "point"
-- The value of init doesn't matter
--
-- How does this change when we add one sample onto the end of init?
-- The current state still has to start ith init
-- The current state still has to add onto init
-- The current state has increased in length by 1 but init hasn't so the differece is still at most "point"



-- Compute the loop, but using presamples instead
def sv4_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) :
  SLang sv1_state := do
  let presamples <- @sv4_presample dps ε₁ ε₂ point
  probWhileCut
    (sv4_privMaxC τ l)
    (sv4_privMaxF init presamples)
    (point + 1)
    init



-- I want to prove that sv4_loop is equal to sv3_loop

lemma sv3_loop_eq_sv4_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) :
    @sv3_loop dps ε₁ ε₂ τ l point init = @sv4_loop dps ε₁ ε₂ τ l point init := by
  unfold sv3_loop
  unfold sv4_loop

  -- The support of state' is contains only length l states,
  -- where l is a value freater than init

  suffices ∀ state',
           (List.length state'.1 ≥ List.length init.1) ->
           (probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) (point + 1) state' =
           (do
             let presamples ← sv4_presample ε₁ ε₂ point
             probWhileCut (sv4_privMaxC τ l) (sv4_privMaxF init presamples) (point + 1) state'))
    by
      apply this
      simp

  induction point
  · intro init
    rename_i init_start
    simp [sv4_presample]
    unfold sv4_privMaxC
    simp [probWhileCut, probWhileFunctional]
    split <;> try rfl
    -- Does the left side have more samples than the right side?
    -- Not a good sign!
    intro _
    apply SLang.ext
    intro _
    simp
    intro _
    simp
  · intro init
    rename_i point' IH

    -- Unroll it once, using the lemma
    -- Do we need to unroll this beforehand?
    let H := sv3_loop_unroll_2 τ ε₁ ε₂ l point'
    unfold sv3_loop at H
    rw [H]
    clear H

    cases (Classical.em (sv1_privMaxC τ l init = true))
    · simp
      rename_i init_start Hcond
      intro Hlen

      -- Horrifying, but only because I can't conv under the if (dependent types)?
      have X :
        ((sv4_presample ε₁ ε₂ 1).probBind fun presample_list =>
          if sv1_privMaxC τ l init = true then
              (sv4_next init (↑presample_list) init).probBind fun next_state =>
              probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) (point' + 1) next_state
          else probPure init) =
        ((sv4_presample ε₁ ε₂ 1).probBind fun presample_list =>
          if sv1_privMaxC τ l init = true then
              (sv4_next init (↑presample_list) init).probBind fun next_state =>
                (do
                  let presamples ← sv4_presample ε₁ ε₂ point'
                  probWhileCut (sv4_privMaxC τ l) (sv4_privMaxF init_start ↑presamples) (point' + 1) next_state)
          else probPure init) := by

        -- apply probBind_congr_strong
        apply SLang.ext
        intro x
        simp
        apply tsum_congr
        intro a
        congr 1
        split
        · simp
          -- a is nonzero
          -- This sum is only nonzero for a_1 equal to a plus one element
          -- In that case, the IH is provable
          -- Regular tsum congr will work but do cases on that after
          sorry
        · simp
          sorry
      rw [X]
      clear X
      clear IH
      simp_all

      apply SLang.ext
      intro final_state
      simp

      -- Commute the presample steps together on the LHS?
      conv =>
        enter [1, 1, a, 2, 1, a1]
        rw [<- ENNReal.tsum_mul_left]
      conv =>
        enter [1, 1, a]
        rw [ENNReal.tsum_comm]
        rw [<- ENNReal.tsum_mul_left]
      conv =>
        enter [1, 1, a, 1, i, 2, 1, a1]
        rw [mul_comm]
        rw [mul_assoc]
      conv =>
        enter [1, 1, a, 1, i]
        rw [ENNReal.tsum_mul_left]
        rw [<- mul_assoc]

      have Hcond' : sv4_privMaxC τ l init = true := by
        simp [sv4_privMaxC]
        trivial
      conv =>
        enter [2, 1, a]
        unfold probWhileCut
        unfold probWhileFunctional
      simp_all
      conv =>
        enter [2, 1, a, 2, 1, i1]
        simp only [sv4_privMaxF]
        rw [mul_comm]

      -- Now just need to finish this by a bijection?
      -- The RHS is zero on empty lists
      -- Make general support lemma for sv4_presample?

      -- still a difference the sv4_next term


      rw [<- ENNReal.tsum_prod]

      sorry
    · sorry
      /-
      simp_all
      simp [probWhileCut, probWhileFunctional]
      have X : sv4_privMaxC τ l init = false := by
        unfold sv4_privMaxC
        trivial
      simp_all
      apply SLang.ext
      intro final_state
      -- Both 1 because sum of PMF?
      simp
      split
      · sorry
      · simp
      -/


    -- apply SLang.ext
    -- intro final_state
    -- simp
    --
    -- -- Step through to get a new init?
    -- conv =>
    --   -- I want to enter into theat probWhileCut
    --   enter [1, 1, a, 2]
    --   simp

    --   skip
    -- simp


    -- -- Then use the IH


    -- sorry



-/



/-

def sv1_to_list (s : sv1_state) : List ℤ := s.1 ++ [s.2]

def list_to_sv1 (s : List ℤ) : sv1_state :=
  match s with
  | [] => ([], 0) -- Error case
  | [x] => ([], x)
  | (x :: xs) =>
    let w := list_to_sv1 xs
    (x :: w.1, w.2)


def sv1_prefix (s : sv1_state) (n : ℕ) := list_to_sv1 $ List.take n $ sv1_to_list s


def sv4_0_cond (presamples  : sv1_state) (τ : ℤ) (l : List ℕ) (n : ℕ) : Bool :=
  sv1_privMaxC τ l (sv1_prefix presamples n)

def sv4_0_body (n : ℕ) : SLang ℕ :=
  return (n + 1)


def sv4_0_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (samples : ℕ) (init : sv1_state) : SLang ℕ := do
  let presamples <- @sv4_0_presample dps ε₁ ε₂ init samples
  let sk <- probWhileCut
    (sv4_0_cond presamples τ l)
    sv4_0_body
    (samples + 1)
    (List.length (init.1))
  return sk + 1


def sv3_loop_mod [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (samples : ℕ) (init : sv1_state) : SLang ℕ := do
  let st <- probWhileCut (@sv1_privMaxC τ l) (@sv1_privMaxF dps ε₁ ε₂) samples init
  return sv1_threshold st


-- Turn the state back into a nat, but this time, over the presampled list
-- FIXME: Rename if this actually works
def sv4_0_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
     @sv4_0_loop dps ε₁ ε₂ τ l point ([], v0)
   computation point



-- Now try to prove this equivalence by induction for all inits

lemma sv3_eq_sv4_0_loop [dps : DPSystem ℕ] ε₁ ε₂ τ l point init :
  @sv3_loop_mod dps τ ε₁ ε₂ l (point + 1) init = @sv4_0_loop dps τ ε₁ ε₂ l point init := by
  revert init
  induction point
  · intro init
    apply SLang.ext
    intro p'
    simp

    -- Simplify the RHS: zero presampling occurs
    simp [sv4_0_loop]
    simp [sv4_0_presample]
    rw [ENNReal.tsum_eq_add_tsum_ite init]
    simp
    conv =>
      lhs
      rw [<- zero_add (sv3_loop_mod _ _ _ _ _ _ _)]
    conv =>
      rhs
      rw [add_comm]
    congr 1
    · symm
      simp
      intro _ HK1 HK2
      exfalso
      apply HK1
      apply HK2

    -- Simplify the LHS
    simp [sv3_loop_mod] -- ?
    simp [probWhileCut, probWhileFunctional]
    simp [sv4_0_cond]
    simp [sv1_prefix, sv1_to_list, list_to_sv1]
    rw [List.take_append]
    simp [list_to_sv1]
    have H : (list_to_sv1 (init.1 ++ [init.2])) = init := by
      sorry
    simp [H]
    simp [sv4_0_body]
    split <;> simp
    simp [sv1_threshold]
    rw [ENNReal.tsum_eq_add_tsum_ite init]
    simp

    sorry
  · sorry





lemma sv3_eq_sv4_0 [dps : DPSystem ℕ] ε₁ ε₂ l : sv3_privMax ε₁ ε₂ l = sv4_0_privMax ε₁ ε₂ l := by
  sorry





-- -- Probably useless as stated but should be true?
-- -- For the inductive argument we only need n2 = 1, btw
-- lemma sv3_0_presample_additive [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (x0 : sv1_state) (n1 n2 : ℕ) :
--     ((@sv4_0_presample dps ε₁ ε₂ x0 n1) >>= fun x1 => @sv4_0_presample dps ε₁ ε₂ x1 n2) =
--     @sv4_0_presample dps ε₁ ε₂ x0 (n1 + n2) := by
--   revert x0
--   induction n2
--   · intro x0
--     apply SLang.ext
--     intro v
--     simp [sv4_0_presample]
--     rw [ENNReal.tsum_eq_add_tsum_ite ?G1]
--     case G1 => apply v
--     simp
--     conv =>
--       rhs
--       rw [<- add_zero (sv4_0_presample _ _ _ _ _)]
--     congr 1
--     simp
--     intro i H1 H2
--     exfalso
--     apply H1
--     symm
--     apply H2
--   · intro x0
--     rename_i n' IH
--     apply SLang.ext
--     intro v
--     simp
--     -- IDK. Something is doable for sure?
--     sorry





-- def sv3_1_threshold (s : sv3_1_state) : ℕ := List.length s.1
--
-- def sv3_1_noise (s : sv3_1_state) : ℤ := s.2.1
--
-- def sv3_1_count (s : sv3_1_state) : ℕ := s.2.2
--
-- def sv3_1_privMaxC (τ : ℤ) (l : List ℕ) (s : sv3_1_state) : Bool :=
--   decide (exactDiffSum (sv3_1_threshold s) l + (sv3_1_noise s) < τ)
--
-- def sv3_1_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv3_1_state) : SLang sv3_1_state := do
--   let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
--   return (s.1 ++ [s.2.1], vn, s.2.2 + 1)
--
-- def sv3_1_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
--   fun (point : ℕ) =>
--   let computation : SLang ℕ := do
--     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
--     let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
--     let sk <- probWhileCut (sv3_1_privMaxC τ l) (sv3_1_privMaxF ε₁ ε₂) (point + 1) ([], v0, 0)
--     return (sv3_1_count sk)
--   computation point
--
--
--
-- lemma sv3_eq_sv3_1 [dps : DPSystem ℕ] ε₁ ε₂ l : sv3_privMax ε₁ ε₂ l = sv3_1_privMax ε₁ ε₂ l := by
--   apply SLang.ext
--   intro point
--   unfold sv3_privMax
--   unfold sv3_1_privMax
--   simp
--   apply tsum_congr
--   intro τ
--   congr 1
--   apply tsum_congr
--   intro v0
--   congr 1
--
--   sorry




/-
## Program version 4
  - Presamples each vk
  - Iteratively checks if the loop
  - Still loops through prefixes of the vk's iteratively
-/

-- Presamples the list (v_(n-1), v_(n-2), ..., v0)
def sv4_presample [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang (List ℤ) := do
  match n with
  | Nat.zero => return []
  | (Nat.succ n') => do
      let v <- @privNoiseZero dps ε₁ (4 * ε₂)
      let l <- sv4_presample ε₁ ε₂ n'
      return (v :: l)

def sv4_evaluate_history (vks : List ℤ) (τ : ℤ) (l : List ℕ) : Bool :=
  match vks with
  | [] => true
  | (v0 :: vs) => sv1_privMaxC τ l (vs, v0) && sv4_evaluate_history vs τ l


def sv4_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let history <- sv4_presample ε₁ ε₂ point
     let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
     if (sv4_evaluate_history history τ l && (! (sv4_evaluate_history (history ++ [vk]) τ l)))
       then return point
       else probZero
   computation point

lemma sv3_eq_sv4 [dps : DPSystem ℕ] ε₁ ε₂ l : sv3_privMax ε₁ ε₂ l = sv4_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv3_privMax
  unfold sv4_privMax

  simp
  apply tsum_congr
  intro τ
  congr 1

  conv =>
    enter [1, 1, v0, 2, 1, st]
  conv =>
    enter [2, 1, hist, 2, 1, vk]

  -- Maybe don't keep this?
  cases point
  · -- point is 0
    simp [sv4_presample, sv1_threshold]
    unfold sv1_state
    conv =>
      enter [1, 1, v0]
      rw [<- ENNReal.tsum_mul_left]
    conv =>
      rw [ENNReal.tsum_comm]
      rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro hist
    simp
    sorry

  sorry



  -- -- Simplify the common start to the programs

  -- Rewrite sv4_presample .. (n + 1) into a program which presamples n and 1 separately


  -- let sv4_presample_sep : SLang (List ℤ) := do
  --   let v0 <- privNoiseZero ε₁ (4 * ε₂)
  --   let L <- sv4_presample ε₁ ε₂ n
  --   return (v0 :: L)

  -- have sv4_presample_sep_eq a : sv4_presample ε₁ ε₂ (n + 1) a = sv4_presample_sep a := by
  --   dsimp only [sv4_presample_sep]
  --   clear sv4_presample_sep
  --   revert a
  --   induction n
  --   · simp [sv4_presample]
  --   rename_i n IH
  --   intro a

  --   -- Rewrite LHS to include LHS of IH
  --   unfold sv4_presample
  --   simp
  --   conv =>
  --     enter [1, 1, b, 2, 1, c]
  --     rw [IH]
  --   clear IH

  --   -- Conclude by simplification
  --   simp
  --   apply tsum_congr
  --   intro v0
  --   congr 1

  --   sorry -- Rewriting through the ite is annoying but doable
  -- conv =>
  --   enter [2, 1, a]
  --   rw [sv4_presample_sep_eq]
  --   dsimp [sv4_presample_sep]
  -- clear sv4_presample_sep sv4_presample_sep_eq



  -- conv =>
  --   enter [1, 1, a]
  --   rw [<- ENNReal.tsum_mul_left]
  -- conv =>
  --   enter [2, 1, a]
  --   rw [<- ENNReal.tsum_mul_left]
  --   enter [1, i]
  --   rw [<- ENNReal.tsum_mul_right]
  -- conv =>
  --   enter [2]
  --   rw [ENNReal.tsum_comm]
  -- apply tsum_congr
  -- intro v0
  -- unfold sv1_state
  -- rw [ENNReal.tsum_prod']
  -- apply tsum_congr
  -- intro hist
  -- apply tsum_congr
  -- intro vk

  -- conv =>
  --   enter [2]
  --   rw [mul_comm]
  -- repeat rw [mul_assoc]
  -- congr 1
  -- simp [sv1_threshold]

  -- split
  -- ·
  --   sorry
  -- · -- Can I solve this one without induction?
  --   -- It simplifies the induction on the other side
  --   simp
  --   split
  --   · right
  --     right
  --     intro l Hl
  --     induction n
  --     · simp_all
  --       unfold sv4_presample
  --       simp
  --       intro H1
  --       simp_all
  --       sorry
  --     · sorry
  --   · sorry

  -- revert hist vk
  -- induction n
  -- · simp_all
  --   sorry
  -- · rename_i n IH
  --   intro hist vk

  --   have Hcond : hist = [] ∨ ∃ vl hist', hist = hist' ++ [vl] := by sorry
  --   cases Hcond
  --   · simp_all
  --   rename_i h
  --   rcases h with ⟨ hist', ⟨ vk', H ⟩ ⟩
  --   simp [H]
  --   clear H
  --   conv =>
  --     enter [1]
  --     unfold probWhileCut
  --     unfold probWhileFunctional






/-
## Program version 5
  - Presamples each vk
  - Performs a single check, rather than a loop
-/
def sv5_evaluate_history (vks : List ℤ) (τ : ℤ) (l : List ℕ) : Bool :=
  match vks with
  | [] => true
  | (v0 :: vs) => sv1_privMaxC τ l (vs, v0)

def sv5_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let history <- sv4_presample ε₁ ε₂ (point + 1)
     let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
     if (sv5_evaluate_history history τ l && (! sv1_privMaxC τ l (history, vk)))
       then return point
       else probZero
   computation point

lemma sv4_eq_sv5 [dps : DPSystem ℕ] ε₁ ε₂ l : sv4_privMax ε₁ ε₂ l = sv5_privMax ε₁ ε₂ l := by
  sorry
-/
