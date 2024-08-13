/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` reductions
-/

open Classical Nat Int Real

noncomputable section

namespace SLang


/-
# Util
-/

/--
Simpler bijection lemma which ignores the support (makes for much easier fn definitions)
-/
lemma tsum_eq_tsum_of_bij {α : Type u_1} {β : Type u_2} {γ : Type u_3} [AddCommMonoid α]
  [TopologicalSpace α] {f : β → α} {g : γ → α}
    (i : γ → β)
    (hi : Function.Injective i)
    (hf : Function.support f ⊆ Set.range fun (x : ↑(Function.support g)) => i ↑x)
    (hfg : ∀ (x : γ), f (i x) = g x) :
  ∑' (x : β), f x = ∑' (y : γ), g y := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun x => i x)
  · simp [Function.Injective]
    exact fun a _ a_1 _ a_2 => hi a_2
  · trivial
  · simp_all




/-
## Abstract sparse vector mechanism code
-/

def gen_sv_cond (st : Bool × List ℤ) : Bool := st.1

def gen_sv_body (cond : List ℤ -> Bool) (noise : SLang ℤ) (st : Bool × List ℤ) : SLang (Bool × List ℤ) := do
  let z <- noise
  return (st.1 ∧ cond (st.2 ++ [z]), st.2 ++ [z])

/--
Generic, history-aware, sparse-vector trial.

Given a history-aware condition cond, it returns the shortest history of random events
drawn from noise such that the history fails cond.
-/
def gen_sv (cond : List ℤ -> Bool) (noise : SLang ℤ) : SLang (List ℤ) := do
  let x <- probWhile gen_sv_cond (gen_sv_body cond noise) (true, [])
  return x.2


def gen_sv_cut (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (init : Bool × List ℤ) : SLang (List ℤ) := do
  let x <- probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel init
  return x.2


lemma gen_sv_cut_zero (cond : List ℤ -> Bool) (noise : SLang ℤ) (st_init st_eval : Bool × List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) 0 st_init st_eval = 0 := by
  simp [probWhileCut]


lemma gen_sv_succ_true (cond : List ℤ -> Bool) (noise : SLang ℤ) (hist_init : List ℤ) (st_eval: Bool × List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) (fuel + 1) (true, hist_init) st_eval =
    (noise >>= (fun z =>
      probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel ((cond (hist_init ++ [z])), hist_init ++ [z]))) st_eval := by
    simp [probWhileCut, probWhileFunctional]
    simp [gen_sv_cond]
    rw [ENNReal.tsum_prod']
    simp [gen_sv_body]
    conv =>
      enter [1, 1, a, 1, b]
      rw [<- ENNReal.tsum_mul_right]
    conv =>
      enter [1, 1, a]
      rw [ENNReal.tsum_comm]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro vk
    rw [<- ENNReal.tsum_prod]
    generalize _HK : cond (hist_init ++ [vk]) = K
    rw [ENNReal.tsum_eq_add_tsum_ite (K, hist_init ++ [vk])]
    simp
    rw [ENNReal.tsum_eq_zero.mpr]
    · simp
    intro i
    split <;> simp
    intro H1 H2
    cases i
    simp_all

lemma gen_sv_succ_false (cond : List ℤ -> Bool) (noise : SLang ℤ) (hist_init : List ℤ) (st_eval: Bool × List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) (fuel + 1) (false, hist_init) st_eval =
    if (st_eval = (false, hist_init)) then 1 else 0 := by
    simp [probWhileCut, probWhileFunctional, gen_sv_cond]
    split <;> rfl


lemma gen_sv_body_support (cond : List ℤ -> Bool) (noise : SLang ℤ) (hist : List ℤ) (f1 f2: Bool) :
    gen_sv_body cond noise (f1, hist) (f2, eval) ≠ 0 -> eval.length = hist.length + 1 := by
  simp [gen_sv_body]
  intro _ _ Hx _
  simp [Hx]

lemma gen_sv_body_support' (cond : List ℤ -> Bool) (noise : SLang ℤ) (hist : List ℤ) (f1 f2: Bool) :
    gen_sv_body cond noise (f1, hist) (f2, eval) ≠ 0 -> ∃ vk, eval = hist ++ [vk] := by
  simp [gen_sv_body]
  intro _ _ Hx _
  simp [Hx]


-- False states are absorbing
lemma gen_sv_loop_false_true_supp (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (hist pres: List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (false, hist) (true, pres) = 0 := by
  cases fuel <;> simp [probWhileCut, probWhileFunctional, gen_sv_cond]


-- The only way to end in a True state is to start in a true state
lemma gen_sv_loop_end_true_true_flag (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (hist pres: List ℤ) (f : Bool) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (f, hist) (true, pres) ≠ 0 -> f = true := by
  revert hist pres
  induction fuel
  · intro _ _
    simp [probWhileCut]
  · intro hist pres
    rename_i N' IH
    cases f
    simp [probWhileCut, probWhileFunctional, gen_sv_cond]
    simp

lemma gen_sv_loop_true_true_length (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (hist pres: List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (true, pres) ≠ 0 -> hist.length + fuel = pres.length := by
  revert hist pres
  induction fuel
  · simp [probWhileCut]
  · rename_i fuel' IH
    intro hist pres Hsupp
    simp [probWhileCut, probWhileFunctional, gen_sv_cond, ↓reduceIte] at Hsupp
    have Hsupp' := Hsupp ?G1
    case G1 =>
      intro b
      right
      apply gen_sv_loop_false_true_supp
    clear Hsupp
    rcases Hsupp' with ⟨ F_hist, ⟨ Hbody, Hloop ⟩ ⟩
    apply gen_sv_body_support' at Hbody
    rcases Hbody with ⟨ vk, Hvk ⟩
    subst Hvk
    have IH' := IH _ _ Hloop
    clear IH
    simp_all
    linarith


-- -- Not sure
-- lemma gen_sv_loop_true_trans_support (cond : List ℤ -> Bool) (noise : SLang ℤ)
--     (fuel fuel': ℕ) (hist hist' hist'': List ℤ) (f : Bool)
--     (H1 : probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (true, hist') ≠ 0)
--     (H2 : probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel' (true, hist') (f, hist'') ≠ 0) :
--     (probWhileCut gen_sv_cond (gen_sv_body cond noise) (fuel + fuel') (true, hist') (f, hist'') ≠ 0) := by
--   induction hist
--   · apply gen_sv_loop_true_true_length at H1
--     simp at H1
--     s orry
--   · s orry



-- -- False is constant
-- lemma gen_sv_loop_false_const (cond : List ℤ -> Bool) (noise : SLang ℤ)
--     (fuel fuel': ℕ) (hist hist' hist'': List ℤ) (f : Bool) :
--     (H1 : probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (false, hist') ≠ 0) =
--     (H1 : probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (false, hist') ≠ 0) =


-- THe only way to terminate in a false state is to be true and then fail the check exactly once
lemma gen_sv_loop_true_false_supp (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (hist hist': List ℤ) (last : ℤ):
    probWhileCut gen_sv_cond (gen_sv_body cond noise) (fuel + 1) (true, hist) (false, pres ++ [last]) ≠ 0 ->
    (probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (true, pres) ≠ 0) := by
  revert hist last fuel
  induction pres
  · simp
    sorry
  · intro fuel hist last
    cases fuel
    · sorry
    simp [probWhileCut, probWhileFunctional, gen_sv_cond]
    sorry



-- lemma gen_sv_loop_cut_transition_true_false_self (cond : List ℤ -> Bool) (noise : SLang ℤ) (hist : List ℤ)
--      : probWhileCut gen_sv_cond (gen_sv_body cond noise) 1 (true, hist) (false, hist) = 0 := by

lemma gen_sv_loop_cut_bound_lower (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (hist pres : List ℤ)
      (Hlen : hist.length > pres.length) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (false, pres) = 0 := by
  -- Was proven in the old version, should be provable here
  sorry

lemma gen_sv_loop_cut_bound_upper (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (hist pres : List ℤ)
      (HAB : hist.length + fuel < pres.length + 1) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, hist) (false, pres) = 0 := by
  -- Was proven in the old version, should be provable here.
  sorry

-- Prove that probWhileCut ... (true, false) is a step function in terms of the amount of fuel?



/--
Each point depends on at most a finite number of iterations
-/
theorem gen_sv_loop_cut_eventually_constant_true_false (cond : List ℤ -> Bool) (noise : SLang ℤ) (diff fuel : ℕ) (init eval : List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) (eval.length + 1) (true, init) (false, init ++ eval) =
    probWhileCut gen_sv_cond (gen_sv_body cond noise) (eval.length + 1 + fuel) (true, init) (false, init ++ eval) := by
  revert init eval
  induction fuel
  · simp
  · intro init eval
    rename_i fuel' IH
    conv =>
      rhs
      simp only [probWhileCut, probWhileFunctional, gen_sv_cond, ↓reduceIte]
    rw [IH]
    -- Not sure
    sorry


/--
After a threshold, probWhileCut gen_sv_cond (gen_sv_body cond noise) is constant in terms of the amount of fuel.
-/
def gen_sv_loop_cut_step (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (init : List ℤ) : SLang (Bool × List ℤ) :=
  (fun (eval_f, eval) =>
    match eval_f with
    | true => 0 -- What is the true->true closed form?
    | false =>
        -- true->false closed form: Either there is not enough iterates to reach the eval point, so the
        -- probability is zero, or there is enough, and the probability is constant.
        if fuel ≤ eval.length - init.length
          then 0
          else probWhileCut gen_sv_cond (gen_sv_body cond noise) (1 + eval.length - init.length) (true, init) (false, eval))


theorem gen_sv_loop_closed (cond : List ℤ -> Bool) (noise : SLang ℤ) (fuel : ℕ) (init : List ℤ) :
    probWhileCut gen_sv_cond (gen_sv_body cond noise) fuel (true, init)  =
    gen_sv_loop_cut_step cond body fuel init := by
  sorry


/--
History-tracking sparse-vector mechanism
-/
def gen_sv_num (cond : List ℤ -> Bool) (noise : SLang ℤ) : SLang ℕ :=
  gen_sv cond noise >>= (probPure ∘ List.length)

/--
Sparse vector mechanism which calculates each point using a fixed number of iterates
-/
def gen_sv_num_cut (cond : List ℤ -> Bool) (noise : SLang ℤ) : SLang ℕ :=
  fun N => (gen_sv_cut cond noise (N + 1) (true, []) >>= (probPure ∘ List.length)) N

/-
## Reduction 1: Unbounded compilable program to bounded noncompilable program
-/

lemma gen_sv_reduction_1 cond noise : gen_sv_num cond noise = gen_sv_num_cut cond noise := by
  -- Prove that gen_sv_num_cut is constant after N iterates
  -- Apply the limit lemma
  sorry



/-
## Reduction 2: Bounded noncompilable program to Presampled program
-/


def gen_sv_presampleN (noise : SLang ℤ) (N : ℕ) : SLang (List ℤ) :=
  match N with
  | Nat.zero => probPure []
  | Nat.succ N' => do
      let vN' <- noise
      let rec <- gen_sv_presampleN noise N'
      return rec ++ [vN']

lemma gen_sv_presampleN_supp (noise : SLang ℤ) (N : ℕ) (eval : List ℤ) :
    gen_sv_presampleN noise N eval ≠ 0 -> eval.length = N := by
  sorry


/--
Conditionals which are monotone
-/
def cond_mono_pred (cond : List ℤ -> Bool) : Prop :=
  ∀ l d : List ℤ, cond l = false -> cond (l ++ d) = false

/--
Sparse vector mechanism which calculates randomness ahead of time and
only checks one point
-/
def gen_sv_presampled (cond : List ℤ -> Bool) (noise : SLang ℤ) : SLang ℕ :=
  fun N =>
  (gen_sv_presampleN noise N >>= fun hist =>
   noise >>= fun last =>
   if (¬ cond (hist ++ [last]) ∧ cond hist)
     then probPure N
     else 0)
  N

lemma gen_sv_reduction_2 (cond : List ℤ -> Bool) (noise : SLang ℤ) (Hcond : cond_mono_pred cond) :
  gen_sv_num_cut cond noise = gen_sv_presampled cond noise := by
  sorry



/-
## Specialization to the terms used for privMax
-/




/--
G: Maximum noised prefix sum.

vis is a fixed list of noise samples.
-/
def G (l : List ℕ) (vis : { v : List ℤ // 0 < v.length }) : ℤ :=
  let vis' := (List.mapIdx (fun i vi => exactDiffSum i l + vi) vis)
  let Hvis' : 0 < vis'.length := by
    dsimp [vis']
    cases vis
    simp [List.length_mapIdx]
    trivial
  List.maximum_of_length_pos Hvis'


/--
Adding additional random samples (thereby extending the prefix sum) can only increase the value of G
-/
lemma G_mono (l : List ℕ) (vis : { v : List ℤ // 0 < v.length }) (c : ℤ) pf :
    G l vis ≤ G l ⟨ vis.1 ++ [c], pf ⟩ := by
  simp [G]
  apply List.maximum_le_of_forall_le
  intro a Ha
  apply List.le_maximum_of_mem'
  rw [List.mapIdx_append_one]
  rw [List.mem_append]
  left
  trivial


/--
History-aware loop condition for the privMax program
-/
def privMax_eval_alt_cond (l : List ℕ) (τ : ℤ) (history : List ℤ) : Bool :=
  match history with
  | [] => true
  | (h :: hs) => G l ⟨ h :: hs , by simp ⟩ < τ


/--
Compute privMax with presampling
-/
def privMax_presample {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  gen_sv_presampled (privMax_eval_alt_cond l τ) (@privNoiseZero dps ε₁ (4 * ε₂))


lemma privMax_presample_normalizes {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : HasSum (@privMax_presample dps ε₁ ε₂ l) 1 := by
  sorry

/--
privMax as a PMF
-/
def privMax_presample_PMF {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : PMF ℕ :=
  ⟨ @privMax_presample dps ε₁ ε₂ l, @privMax_presample_normalizes dps ε₁ ε₂ l⟩

end SLang
