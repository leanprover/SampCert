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





/-
Reduction 1: Unbounded compilable program to bounded noncompilable program
-/


/-
Reduction 2: Bounded noncompilable program to Presampled program
-/








/-
# Concrete program, used in the pure DP proof
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





















































/-
# Loop unrolling lemmas

`probWhileSplit cond body continuation n` is an n-unrolling of a loop, where `continuation` is
      applied in the case that n is exhaused.

`probWhileCut cond body n` is a `probWhileSplit` with continuation zero.

`probWhileSplit .. continuation (m + n)` is the same as `probWhileSplit .. .. m` with a
    `probWhileSplit .. continuation n` continuation.

`probWhileSplit .. probPure (m + n)`  is the same as `probWhileSplit .. probPure m` bound to
    `probWhileSplit .. probPure b`.

`probWhileSplit .. probZero (m + n)`  is the same as `probWhileSplit .. probPure m` bound to
    `probWhileSplit .. probZero b`, provided `n > 0`. This last lemma enables us to separate
    the first m unrollings of a nontrivial probWhile loop.

The helper function `probBind_congr_strong` enables us to restruct congruence proofs between
    probBind programs to their support.

The predicate
-/

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

lemma probBind_congr_medium (p : SLang T) (f : T -> SLang U) (g : T -> SLang U) (u : U)
      (Hcong : ∀ t : T, p t ≠ 0 -> f t u = g t u) :
      (p >>= f) u = (p >>= g) u := by
   simp
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


/--
``SLang`` value obtained by applying a loop body exactly ``n`` times to a given distribution
-/
def probWhileSplit (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => continuation a
  | Nat.succ n => do
    if cond a
      then
        let v ← body a
        probWhileSplit cond body continuation n v
      else
        return a


/--
probWhileCut is probWhileSplit applied to the zero distribution
-/
lemma probWhileCut_probWhileSplit_zero (cond : T → Bool) (body : T → SLang T) (n : Nat) :
    probWhileCut cond body n = probWhileSplit cond body (fun _ => probZero) n := by
  apply funext
  induction n
  · simp [probWhileCut, probWhileSplit]
  · rename_i n IH
    simp [probWhileCut, probWhileSplit]
    rw [funext IH]
    intro _
    rfl

/--
Evaluate probWhileSplit when out of steps
-/
lemma probWhileSplit_zero (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (init : T):
    probWhileSplit cond body continuation 0 init = continuation init := by
  simp [probWhileSplit]

/--
probWhileSplit is constant when the condition is false
-/
lemma probWhileSplit_cond_false_cst (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T)
    (n : Nat) (init : T) (HF : cond init ≠ true) :
    probWhileSplit cond body continuation (Nat.succ n) init =
    probPure init := by
  rw [probWhileSplit]
  split
  · exfalso
    simp_all
  rfl

/--
Move an iterate of of probWhileSplit into the continuation.
-/
lemma probWhileSplit_succ_l (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (n : Nat) (init : T):
    probWhileSplit cond body continuation (Nat.succ n) init =
    (probWhileSplit cond body (probWhileSplit cond body continuation n) 1 init) := by
  apply funext
  intro _
  simp [probWhileSplit]

/--
Move multiple iterates of of probWhileSplit into the continuation.
-/
lemma probWhileSplit_add_l (cond : T → Bool) (body : T → SLang T) (continuation : T -> SLang T) (m n : Nat) (init : T):
    probWhileSplit cond body continuation (n + m) init =
    (probWhileSplit cond body (probWhileSplit cond body continuation n) m init) := by
  revert init
  induction m
  · intro init
    rw [probWhileSplit_zero]
    simp only [add_zero]
  · intro init
    rename_i m' IH
    rw [probWhileSplit_succ_l]
    rw [<- (funext IH)]
    rw [<- probWhileSplit_succ_l]
    rfl


/--
Move iterate of probWhileSplit into the initial value, when the continuation is probPure
-/
lemma probWhileSplit_succ_r_pure (cond : T → Bool) (body : T → SLang T) (n : Nat) (init : T):
    probWhileSplit cond body probPure (Nat.succ n) init =
    (probWhileSplit cond body probPure 1 init)  >>=  (probWhileSplit cond body probPure n) := by
  apply funext
  intro x
  have H : (probWhileSplit cond body probPure 1 init) = if (cond init) then (body init) >>= probPure else pure init := by
    apply funext
    intro x
    rw [probWhileSplit]
    split
    · simp [probWhileSplit]
    · rfl
  rw [H]
  simp only [probWhileSplit]
  split
  · simp
  · have H : (pure init >>= probWhileSplit cond body probPure n) = pure init := by
      apply funext
      intro x
      simp [pure_apply]
      conv =>
        lhs
        enter [1, a]
      rw [ENNReal.tsum_eq_add_tsum_ite init]
      simp
      cases n
      · simp [probWhileSplit]
        rw [ENNReal.tsum_eq_zero.mpr ?G1]
        case G1 =>
          intro i
          split <;> rfl
        simp
      · rename_i n'
        rw [probWhileSplit_cond_false_cst _ _ _ _ _ (by trivial)]
        simp [probPure]
        rw [ENNReal.tsum_eq_zero.mpr ?G1]
        case G1 =>
          intro i
          split <;> rfl
        simp
    rw [H]


/--
Move iterates of probWhileSplit into the initial value, when the continuation is probPure
-/
lemma probWhileSplit_add_r_pure (cond : T → Bool) (body : T → SLang T) (m n : Nat) (init : T):
    probWhileSplit cond body probPure (m + n) init =
    (probWhileSplit cond body probPure m init)  >>=  (probWhileSplit cond body probPure n) := by
  revert init
  induction m
  · simp [probWhileSplit]
  · intro init
    rename_i m' IH
    rw [add_comm, <- add_assoc]
    rw [probWhileSplit_succ_r_pure]
    rw [add_comm]
    rw [bind_congr IH]
    rw [probWhileSplit_succ_r_pure _ _ m']
    conv =>
      congr
      · enter [1]
        simp [probWhileSplit]
      · enter [1, 1]
        simp [probWhileSplit]
    split <;> simp




/--
Move iterate of probWhileSplit into initial condition, when continuation is probZero
-/
lemma probWhileSplit_succ_r_zero (cond : T → Bool) (body : T → SLang T) (n : Nat) (Hn : n > 0) (init : T):
    probWhileSplit cond body (fun _ => probZero) (Nat.succ n) init =
    (probWhileSplit cond body probPure 1 init)  >>=  (probWhileSplit cond body (fun _ => probZero) n) := by
  apply funext
  intro x
  simp [probWhileSplit]
  split
  · simp [probBind]
  · rename_i h
    simp at h
    conv =>
      rhs
      enter [1, a]
      simp [probPure]
    rw [ENNReal.tsum_eq_add_tsum_ite init]
    simp
    have H1 :
      (∑' (x_1 : T), if x_1 = init then 0 else if x_1 = init then probWhileSplit cond body (fun _ => probZero) n x_1 x else 0) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro i
      split <;> simp
    simp [H1]
    clear H1
    unfold probWhileSplit
    cases n
    · exfalso
      linarith
    · simp [h]


/--
Move iterate of probWhileSplit into initial condition, when continuation is probZero
-/
lemma probWhileSplit_add_r_zero (cond : T → Bool) (body : T → SLang T) (m n : Nat) (Hn : n > 0) (init : T):
    probWhileSplit cond body (fun _ => probZero) (m + n) init =
    (probWhileSplit cond body probPure m init)  >>=  (probWhileSplit cond body (fun _ => probZero) n) := by
  revert init
  induction m
  · intro init
    simp [probWhileSplit]
  · intro init
    rename_i m' IH
    conv =>
      lhs
      rw [add_comm, <- add_assoc]
    rw [probWhileSplit_succ_r_zero _ _ _ (by linarith)]
    rw [add_comm]
    cases m'
    · simp
    rename_i m''
    rw [bind_congr IH]
    clear IH
    unfold probWhileSplit
    simp
    split <;> simp
    · rename_i h
      apply probBind_congr_strong
      intro t _
      simp [probWhileSplit]
    · rw [if_neg (by trivial)]
      simp

/--
Separate out the first m unrollings of a nontrivial probWhileCut loop
-/
theorem probWhileCut_add_r (cond : T → Bool) (body : T → SLang T) (m n : Nat) (Hn : n > 0) (init : T):
    probWhileCut cond body (m + n) init =
    (probWhileSplit cond body probPure m init) >>= (probWhileCut cond body n) := by
  rw [probWhileCut_probWhileSplit_zero]
  rw [probWhileCut_probWhileSplit_zero]
  apply probWhileSplit_add_r_zero
  trivial



lemma unfunext (f g : A -> B) (a : A) (H : f = g) : f a = g a := by
  subst H
  rfl


-- /--
-- Probability that loop terminates using exactly N successful evaluations of the loop head
-- -/
-- def probTermCut (cond : T → Bool) (body : T → SLang T) (N : ℕ) (init : T) : SLang Bool :=
--   match N with
--   | Nat.zero =>
--     -- Have done N successes at the loop head, next loop head must fail
--     if cond init
--       then probPure False
--       else probPure True
--   | Nat.succ N' =>
--     -- Haven't done N successes at the loop head, next loop head must succeed
--     if cond init
--       then (body init) >>= (probTermCut cond body N')
--       else probPure False
--
--
-- /--
-- Probability mass at each point associated only to loop iterates that terminate in N steps
-- -/
-- def indicTermN (cond : T → Bool) (body : T → SLang T) (N : ℕ) (init : T) : SLang T := do
--   let tN <- probTermCut cond body N init
--   if tN
--     then probWhileSplit (fun _ => true) body probPure N init
--     else probZero
--
--
-- lemma probWhileCut_indic_ind (cond : T → Bool) (body : T → SLang T) (N : ℕ) (init : T) (eval : T) :
--   probWhileCut cond body (N + 1) init eval = probWhileCut cond body N init eval + indicTermN cond body N init eval := by
--   simp [indicTermN]
--   rw [tsum_bool]
--   simp
--
--   sorry
  -- revert init eval
  -- induction N
  -- · intro init eval
  --   simp [probWhileCut, probWhileFunctional]
  --   simp [indicTermN, probTermCut]
  --   rw [tsum_bool]
  --   split <;> simp [probWhileSplit]
  -- · intro init eval
  --   rename_i N' IH
  --   rw [probWhileCut_probWhileSplit_zero]
  --   rw [probWhileSplit_add_l]
  --   rw [<- probWhileCut_probWhileSplit_zero]
  --   have IH' : probWhileCut cond body (N' + 1) = (fun init eval => probWhileCut cond body N' init eval + indicTermN cond body N' init eval) := by
  --     apply funext
  --     intro init'
  --     apply funext
  --     intro eval'
  --     apply IH init' eval'
  --   simp [probWhileSplit]
  --   split
  --   · sorry
  --   · simp [probWhileCut, probWhileFunctional]
  --     simp [indicTermN]
  --     sorry



-- lemma probWhileCut_indic_sum (cond : T → Bool) (body : T → SLang T) (N : ℕ) (init : T) (eval : T) :
--   probWhileCut cond body N init eval = ∑'(i : ℕ), if i < N then (indicTermN cond body i init) eval else 0 := by
--   induction N
--   · simp [probWhileCut]
--   rename_i N' IH
--   sorry




























/-

/--
Once a history terminates the loop, any hypothetical future loop conditions are also aware that it terminates
-/
lemma privMax_G_continue_alt_mono (l : List ℕ) (τ : ℤ) (history : List ℤ) (future : ℤ) :
    ¬ privMax_eval_alt_cond l τ history -> ¬ privMax_eval_alt_cond l τ (history ++ [future]):= by
  unfold privMax_eval_alt_cond
  cases history
  · simp
  rename_i a b
  simp only [decide_eq_true_eq, List.cons_append]
  intro H1 H2
  apply H1
  apply LE.le.trans_lt _ H2
  apply G_mono



/--
History-aware body for the privMax sampling loop
-/
def privMax_eval_alt_F {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (history : List ℤ) : SLang (List ℤ) := do
  let candidate <- @privNoiseZero dps ε₁ (4 * ε₂)
  return history ++ [candidate]



/--
Support of privMaxEval_alt_body is contained in the extensions of the history by one element
-/
lemma privMaxEval_alt_body_supp {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) history eval :
    (@privMax_eval_alt_F dps ε₁ ε₂ history eval) ≠ 0 -> ∃ z, eval = history ++ [z] := by
  simp [privMax_eval_alt_F ]
  intro x Heval _
  exists x

-- FIXME: cleanup proof
lemma privMaxEval_alt_body_supp' {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) history eval :
    (¬(∃ z, eval = history ++ [z])) -> (@privMax_eval_alt_F dps ε₁ ε₂ history eval) = 0 := by
  apply Classical.by_contradiction
  intro A
  apply A
  intro B
  suffices ¬(privMax_eval_alt_F ε₁ ε₂ history eval ≠ 0) by
    exact False.elim (this fun a => A fun _ => a)
  intro C
  apply B
  apply privMaxEval_alt_body_supp ε₁ ε₂
  trivial


def privMax_eval_alt_loop {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) : SLang (List ℤ) := do
  probWhile
    (privMax_eval_alt_cond l τ)
    (@privMax_eval_alt_F dps ε₁ ε₂)
    []


/--
History-aware privMax program
-/
def privMax_eval_alt {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let final_history <- @privMax_eval_alt_loop dps ε₁ ε₂ l τ
  return final_history.length - 1

/-
## Reduction 0: The implementation version is the same as the history-tracking version


This reduction is not necessary, technically, since privMax_eval_alt is computable.
The later reductions, on the other hand, are necessary.
-/

lemma privMax_reduction_0 (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @privMax_eval dps ε₁ ε₂ l = @privMax_eval_alt dps ε₁ ε₂ l := by
  unfold privMax_eval privMax_eval_alt
  simp
  apply funext
  intro N
  simp
  apply tsum_congr
  intro τ
  congr 1
  unfold privMax_eval_alt_loop
  conv =>
    enter [1, 1, a, 2]
    rw [ENNReal.tsum_prod']

  -- Separate the sum on the right into a sum over list lengths?
  sorry




/-
## Reduction 1: The history-tracking version is the same as a bounded history-tracking version
-/


/--
Sampling loop for the bounded history-aware privMax function

Truncated to N iterates; stable for all lists of length at most N-1
-/
def privMax_eval_alt_loop_cut {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (N : ℕ) : SLang (List ℤ) := do
  probWhileCut
    (privMax_eval_alt_cond l τ)
    (@privMax_eval_alt_F dps ε₁ ε₂)
    N
    []

/--
Closed form for privMax_eval_alt_loop_cut evaluated on the history hist, in terms of the number of iterates.

Namely, it is a step function. The function probWhileCut needs (hist.length + 1) iterates before hist
is in its support, and afterwards, no additional iterates return hist.
-/
def privMax_eval_alt_loop_cut_step {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (iterates : ℕ) (hist : List ℤ) : ENNReal :=
  if (iterates ≤ hist.length)
    then 0
    else probWhileCut (privMax_eval_alt_cond l τ) (@privMax_eval_alt_F dps ε₁ ε₂) (hist.length + 1) [] hist


/--
Length of the supported region is bounded below by the length of the initial history.
-/
lemma privMax_eval_cut_supp_bound {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool) (A B : List ℤ)
  (HAB : A.length > B.length) :
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) N A B = 0 := by
  revert A
  induction N
  · simp [probWhileCut]
  · intro A HA
    rename_i N' IH
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      intro F_A
      cases Classical.em (∃ z : ℤ, F_A = A ++ [z])
      · rename_i h
        rcases h with ⟨ z, HF_A ⟩
        right
        apply IH
        simp [HF_A]
        linarith
      · left
        apply privMaxEval_alt_body_supp'
        trivial
    · simp
      intro HK
      simp [HK] at HA






/--
Length of supported region is bounded abouve by the length of the initial history, plus the number of iterations.
-/
lemma privMax_eval_cut_supp_bound' {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool) (A B : List ℤ)
    (HAB : A.length + N < B.length + 1) :
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) N A B = 0 := by
  revert A
  induction N
  · intro _ _
    simp [probWhileCut]
  · intro A HA
    rename_i N' IH
    simp [probWhileCut, probWhileFunctional]
    split
    · simp
      intro F_A
      cases Classical.em (∃ z : ℤ, F_A = A ++ [z])
      · rename_i h
        rcases h with ⟨ z, HF_A ⟩
        right
        apply IH
        simp [HF_A]
        linarith
      · left
        apply privMaxEval_alt_body_supp'
        trivial
    · simp
      intro HK
      simp [HK] at HA

-- TODO: Can I prove strong congruence for the constant true split?


-- TODO: Can I prove support for the constant true split?


-- lemma privMax_eval_const_true_supp_spec {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (cont : List ℤ -> SLang (List ℤ)) (A B : List ℤ) (N : ℕ)
--     (HContSupp : ∀ C D : List ℤ, C.length < D.length + 1 -> cont C D = 0) (H : A.length + N < B.length + 1) :
--     probWhileSplit (fun _ => True) (@privMax_eval_alt_F dps ε₁ ε₂) cont N A B = 0 := by
--   revert A
--   induction N
--   · intro A HA
--     simp [probWhileSplit]
--     apply HContSupp
--     simp_all
--   · intro A HA
--     rename_i n' IH
--     simp [probWhileSplit]
--     intro F_A
--     cases Classical.em (∃ z : ℤ, F_A = A ++ [z])
--     · right
--       rename_i h
--       rcases h with ⟨ z, Hz ⟩
--       subst Hz
--       apply IH
--       simp
--       linarith
--     · left
--       apply privMaxEval_alt_body_supp'
--       trivial
--
--
--
-- -- Effectively circular due to the side condition constraint on ConstSupp?
-- lemma privMax_eval_split_supp_bound' {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool)
--     (cont : List ℤ -> SLang (List ℤ)) (B : List ℤ)
--     (HContSupp : ∀ (C D : List ℤ), C.length < D.length + 1 → cont C D = 0)
--     (HB : A.length + N < B.length + 1) :
--     probWhileSplit C (@privMax_eval_alt_F dps ε₁ ε₂) cont N A B =
--     probWhileSplit (fun _ => True) (@privMax_eval_alt_F dps ε₁ ε₂) cont N A B := by
--   revert A
--   induction N
--   · intro _ _
--     simp [probWhileSplit]
--   · intro A HA
--     rename_i N' IH
--     simp only [probWhileSplit, decide_True, ↓reduceIte]
--     split
--     · apply probBind_congr_medium
--       intro A' HA'
--       apply IH
--       apply privMaxEval_alt_body_supp at HA'
--       rcases HA' with ⟨ z, hz ⟩
--       subst hz
--       simp
--       linarith
--     · conv =>
--         lhs
--         simp
--       split
--       · exfalso
--         rename_i HK
--         subst HK
--         simp at HA
--       symm
--       simp
--       intro F_A
--       cases Classical.em (∃ z : ℤ, F_A = A ++ [z])
--       · rename_i h
--         rcases h with ⟨ z, Hz ⟩
--         subst Hz
--         right
--         -- After the N' iterates, the length of F(F(F(...(F(A ++ [z]))))) is A.length + N' + 1
--         -- This length is less than B + 1 by hyp.
--         -- So, applying the contniuation support property, it is zero.
--         apply privMax_eval_const_true_supp_spec
--         · trivial
--         · simp
--           linarith
--       · left
--         apply privMaxEval_alt_body_supp'
--         trivial


/--
Test lemma: privMax loop cut equals its closed form at []
-/
lemma privMax_eval_alt_loop_cut_closed_base {dps : DPSystem ℕ} :
    @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ N [] = @privMax_eval_alt_loop_cut_step dps ε₁ ε₂ l τ N [] := by
  simp [privMax_eval_alt_loop_cut]

  cases N
  · -- For N = 0 we are below the step
    -- Simplify the RHS. Below the step, so it is constant 0.
    conv =>
      rhs
      simp [privMax_eval_alt_loop_cut_step]
    -- Simplify the LHS. There are not enough steps (0 ≤ [].length) so it is 0.
    conv =>
      lhs
      simp [probWhileCut]
  · -- For N ≥ 1 we are above the step
    rename_i N'
    -- Simplify the RHS. Above the step, so it is probWhilecut _ _ ([].length + 1) [] []
    conv =>
      rhs
      simp [privMax_eval_alt_loop_cut_step]
    -- Separate the first iterate from both sides.
    -- Have to handle special case where N' = 0 and the formula doesn't hold
    cases N'
    · simp
    rename_i N''
    rw [probWhileCut_probWhileSplit_zero,
        probWhileCut_probWhileSplit_zero]
    rw [add_comm]
    rw [probWhileSplit_add_r_zero _ _ _ _ ?G1]
    case G1 => simp

    -- rewrite the RHS to a bind

    -- Either the bound-from term will do:
    --  early return, so false forever
    --  continuation, with so much context that the RHS is false forever





    sorry

























/--
After a certain number of iterations, the function stops changing.
-/
lemma privMax_eval_cut_const_ind {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (C : List ℤ -> Bool) (B : List ℤ)
    (HN : B.length + 1 ≤ N) :
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) N [] B =
    probWhileCut C (@privMax_eval_alt_F dps ε₁ ε₂) (N + 1) [] B := by

  -- We should be able to prove this by rewriting into the split form, and then applying the strong
  -- congruence theorem with the support bound above.
  apply le_iff_exists_add.mp at HN
  rcases HN with ⟨ diff, Hdiff ⟩
  subst Hdiff
  rw [probWhileCut_probWhileSplit_zero]
  rw [probWhileCut_probWhileSplit_zero]

  -- Turn into a sequence of nested probWhileSplits


  -- Re-evaluate: what does this split actually equal?
  -- Is it
  --    - last element of the outermost split?
  --    - the first element of the continuation?
  -- Which do I want it to be?
  -- How do I specify that?

  -- Intuition says either might be good
  -- FRIDAY: Finish lemma about the support of probWhileSplit with True conditional


  conv =>
    lhs
    enter [4]
    rw [add_assoc, add_comm]
  rw [probWhileSplit_add_l]
  have SC1 :  ∀ (C_1 D : List ℤ), C_1.length < D.length + 1 → probWhileSplit C (@privMax_eval_alt_F dps ε₁ ε₂) (fun x => probZero) (1 + diff) C_1 D = 0 := by
    intro C1 D HL


    -- FIXME Might not be provable sadly


    sorry
  rw [privMax_eval_split_supp_bound' _ _ _ _ _ SC1 (by simp)]
  conv =>
    rhs
    enter [4]
    rw [add_assoc, add_comm]
    rw [add_comm B.length]
    rw [<- add_assoc]
  rw [probWhileSplit_add_l]
  have SC2 : ∀ (C_1 D : List ℤ), C_1.length < D.length + 1 → probWhileSplit C (@privMax_eval_alt_F dps ε₁ ε₂) (fun x => probZero) (diff + 1 + 1) C_1 D = 0 := by
    sorry
  conv =>
    rhs
    rw [privMax_eval_split_supp_bound' _ _ _ _ _ SC2 (by simp)]

  -- Strong congruence and the support equation for the true eqn makes progress????
  sorry


/--
privMax_eval_alt equals its closed form
-/
lemma privMax_eval_alt_loop_cut_closed {dps : DPSystem ℕ} :
    @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ N h = @privMax_eval_alt_loop_cut_step dps ε₁ ε₂ l τ N h := by

  unfold privMax_eval_alt_loop_cut_step
  split
  · -- Below the step
    unfold privMax_eval_alt_loop_cut
    apply privMax_eval_cut_supp_bound'
    simp
    linarith
  · -- Above the step
    rename_i h

    sorry


    -- -- Equal to the step point
    -- cases Classical.em (N = h.length)
    -- · rename_i Hn
    --   subst Hn
    --   sorry
    --   -- rfl
    -- · -- Greater than the step point

    --   -- Cleanup context
    --   rename_i H1 H2
    --   have H3 : h.length < N := by
    --     apply lt_of_not_ge
    --     intro HK
    --     apply GE.ge.le at HK
    --     apply LE.le.eq_or_lt at HK
    --     cases HK <;> simp_all
    --   clear H1 H2

    --   induction N
    --   · exfalso
    --     simp at H3
    --   rename_i N' IH

    --   cases Classical.em (N' = h.length)
    --   · simp_all
    --     simp [privMax_eval_alt_loop_cut]
    --     -- The real base case
    --     -- Should be basically the same as the other argument though
    --     -- Just can't/don't need to rewrite with the IH
    --     -- unfold privMax_eval_alt_loop_cut
    --     -- symm
    --     -- apply privMax_eval_cut_const_ind
    --     -- sorry
    --     -- rfl
    --   rw [<- IH ?G1]
    --   case G1 =>
    --     apply Nat.lt_add_one_iff.mp at H3
    --     apply LE.le.eq_or_lt at H3
    --     cases H3 <;> simp_all

    --   unfold privMax_eval_alt_loop_cut
    --   symm
    --   apply privMax_eval_cut_const_ind
    --   --  OK
    --   sorry
    --   -- linarith




/--
The first reduction: Evaluate each point using a finite number of iterates
-/
def privMax_eval_alt_cut {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := (fun N =>
  (do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let final_history <- @privMax_eval_alt_loop_cut dps ε₁ ε₂ l τ (N + 2)
    return final_history.length - 1) N)

/-
The main program equals the cut program
-/
-- lemma privMax_eval_alt_loop_limit :

lemma privMax_reduction_1 (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @privMax_eval_alt dps ε₁ ε₂ l = @privMax_eval_alt_cut dps ε₁ ε₂ l := by
  -- Want to show that the eval (unbounded at each point) equals the cut version (cut to N at each point)
  apply SLang.ext
  intro N
  simp [privMax_eval_alt, privMax_eval_alt_cut]
  apply tsum_congr
  intro τ
  congr
  apply funext
  intro returned_hist
  split <;> try simp
  rename_i Hreturned_hist
  simp [privMax_eval_alt_loop, privMax_eval_alt_loop_cut]

  -- Apply probWhile limit lemma
  apply probWhile_apply
  apply (@tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ (N + 2))

  -- Prove that probWhileCut is eventually constant
  intro later_cutoff Hlep
  rw [<- Nat.add_sub_cancel' Hlep]


  -- Change to closed form
  generalize Hd : (later_cutoff - (N + 1)) = d
  cases d
  · simp_all
    -- OK as long as returned_hist is nonepty, which is always is.
    sorry


  rename_i d'


  have H := @privMax_eval_alt_loop_cut_closed
  unfold privMax_eval_alt_loop_cut at H
  rw [H]

  -- conv =>
  --   enter [1, 3]
  --   rw [add_comm]
  --   rw [<- add_assoc]
  --   enter [1]
  --   rw [add_comm]
  -- rw [H]
  -- rename_i d'

  -- rw [privMax_eval_alt_loop_cut_step, privMax_eval_alt_loop_cut_step]
  -- clear H
  sorry



/-
## Reduction 2: The bounded history-tracking version is the same as a predicate on eager presample
-/

-/
/--
Sample N noised values. Always returns a list of length N.
-/
def privMax_sampN {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (N : ℕ) : SLang { v : List ℤ // v.length = N } :=
  match N with
  | Nat.zero => probPure ⟨ [], by simp ⟩
  | Nat.succ N' => do
      let v <- @privNoiseZero dps ε₁ (4 * ε₂)
      let r <- @privMax_sampN dps ε₁ ε₂ N'
      probPure ⟨ r.1 ++ [v], by cases r; simp ; trivial ⟩

/-
def initDep {N : ℕ} (l : List T) (_ : l.length = N.succ) : List T :=
  match l with
  | [_] => []
  | (v :: h1 :: hs) => v :: @initDep _ (hs.length) (h1 :: hs) (by simp)

lemma initDep_append_singleton {N : ℕ} (l : List T) (vk : T) (Hl : (l ++ [vk]).length = N.succ) :
    @initDep T N (l ++ [vk]) Hl = l := by
  revert N
  induction l
  · simp [initDep]
  rename_i h t IH
  cases t <;> simp_all [initDep]



/--
Sample N+1 noise values upfront. Return (N+1) when the first N noised prefix
sums are less than τ, and the N+1st noised prefix sum exceeds τ.
-/
def privMax_presample {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
(fun N =>
  (do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let history <- @privMax_sampN dps ε₁ ε₂ N.succ
    if (¬ privMax_eval_alt_cond l τ history.1) ∧ (privMax_eval_alt_cond l τ (@initDep ℤ N history.1 (by cases history ; simp ; trivial )) )
      then probPure N
      else probZero)
  N)



lemma privMax_reduction_2 {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ)  :
    @privMax_eval_alt_cut dps ε₁ ε₂ l = @privMax_presample dps ε₁ ε₂ l := by
  -- Evaluate the identical preludes
  unfold privMax_presample
  unfold privMax_eval_alt_cut
  apply SLang.ext
  intro N
  simp only [bind]
  congr 1
  apply funext
  intro τ

  simp [privMax_eval_alt_loop_cut]
  induction N
  · simp [privMax_sampN]
    simp [probWhileCut, probWhileFunctional]
    conv =>
      lhs
      simp [privMax_eval_alt_cond]
      simp [privMax_eval_alt_F]
    apply probBind_congr_strong
    intro v0 Hv0
    apply SLang.ext
    intro v
    simp

    simp [initDep]
    simp [privMax_eval_alt_cond]

    symm
    split <;> symm
    · have Hfin : (∑' (a : List ℤ), if v = a.length - 1 then probPure [v0] a else 0) = probPure 0 v := by
        simp
        split
        · rename_i h
          subst h
          rw [ENNReal.tsum_eq_add_tsum_ite [v0]]
          simp
          conv =>
            lhs
            enter [2]
            rw [ENNReal.tsum_eq_zero.mpr]
            · skip
            · exact by
                intro i
                split <;> simp
          simp
        · apply ENNReal.tsum_eq_zero.mpr
          intro _
          simp
          intro _ _
          simp_all
      sorry
      -- conv =>
      -- enter [1, 1, a]
      -- split
      -- · exfalso
      --   linarith
      -- · apply Hfin
    · sorry
      -- simp
      -- intro i Hv
      -- split
      -- · simp
      -- · exfalso
      --   aesop

  · rename_i N' IH
    -- I want to unfold one iteration from both sides, but that means I should
    -- generalize over initial condition from [] to A
    sorry


/-
## Reduction 3: Separate the random samples we will view as deterministic, from the random samples for the DP proof.
-/


-/

def privMax_presample_sep_det {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (N : ℕ) : SLang { v : List ℤ // v.length = N} :=
  @privMax_sampN dps ε₁ ε₂ N


def privMax_presample_sep {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
(fun N =>
  (do
    -- Part we will parameterize over (ie. using tsum_congr)
    let history <- @privMax_presample_sep_det dps ε₁ ε₂ N

    -- Part which includes the randomness in the proof (τ and the final sample)
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
    if (¬ privMax_eval_alt_cond l τ (history.1 ++ [vk])) ∧ (privMax_eval_alt_cond l τ history.1)
      then probPure N
      else probZero)
  N)



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
def sum_lem_split_lemma_i (N : ℕ) (x : { v : List T // v.length = N } × T) : { v : List T // v.length = N + 1 } :=
  let ⟨ hist, vk ⟩ := x
  ⟨ hist ++ [vk], by cases hist ; simp; trivial ⟩


lemma splitting_list_lemma {N : ℕ} (hist : List T) (Hhist : hist.length = N + 1) :
    ∃ vr, ∃ l : List T, hist = l ++ [vr] := by
  revert N
  induction hist
  · simp_all
  · rename_i hh ht IH
    cases ht
    · simp
      exists hh
      exists []
    intro N Hl
    simp at Hl
    rename_i hh1 hh2
    have IH := @IH (hh2.length) ?G1
    case G1 => simp_all
    rcases IH with ⟨ a, ⟨ b, c ⟩ ⟩
    exists a
    exists (hh :: b)
    simp [c]


lemma sum_len_split_lemma (N : ℕ) (f : { v : List T // v.length = N + 1 } -> ENNReal) :
    ∑' (a : { v : List T // v.length = N + 1 }), f a =
    ∑' (a : { v : List T // v.length = N}), ∑'(b : T), f ⟨ a ++ [b], (by cases a; simp; trivial) ⟩ := by
  rw [← ENNReal.tsum_prod]
  apply tsum_eq_tsum_of_bij  (sum_lem_split_lemma_i N)
  · simp [Function.Injective]
    simp [sum_lem_split_lemma_i]
    intros _ _ _ _ _ _ H
    have _ := List.append_inj_left' H
    simp_all
  · simp [Function.support]
    apply Set.setOf_subset.mpr
    intro x H
    simp [Set.range]
    rcases x with ⟨ hist, Hhist ⟩
    rcases (splitting_list_lemma hist Hhist) with ⟨ a, ⟨ b, c ⟩ ⟩
    exists b
    exists ?G1
    case G1 =>
      subst c
      simp at Hhist
      trivial
    exists a
    subst c
    apply And.intro
    · trivial
    · simp [sum_lem_split_lemma_i]
  · intro x
    congr 1


lemma privMax_reduction_3 {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @privMax_presample dps ε₁ ε₂ l = @privMax_presample_sep dps ε₁ ε₂ l := by
  unfold privMax_presample
  unfold privMax_presample_sep
  unfold privMax_presample_sep_det
  simp
  apply funext
  intro N

  -- Commute out τ and cancel
  conv =>
    enter [2, 1, a]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, i]
    rw [<- mul_assoc]
    enter [1]
    rw [mul_comm]
  conv =>
    enter [2, 1, a, 1, b]
    rw [mul_assoc]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [2, 1, a]
    rw [ENNReal.tsum_mul_left]
  apply tsum_congr
  intro τ
  congr 1

  -- Separate the sums
  rw [sum_len_split_lemma N]
  conv =>
    rhs
    enter [1, i]
    rw [<- ENNReal.tsum_mul_left]
  apply tsum_congr
  intro history
  apply tsum_congr
  intro vk

  -- Simplify away the conditional
  rcases history with ⟨ history, Hhistory ⟩
  simp
  conv =>
    enter [1, 2]
    rw [initDep_append_singleton]
  rw [<- mul_assoc]
  congr 1

  -- Separate the indicator
  simp [privMax_sampN]
  have H (a : ℤ) (b : { v // v.length = N }) :
       (if history ++ [vk] = ↑b ++ [a] then @privMax_sampN dps ε₁ ε₂ N b else 0) =
       (if history = ↑b then 1 else 0) * (if vk = a then 1 else 0) * (@privMax_sampN dps ε₁ ε₂ N b) := by
    symm
    split <;> try simp_all
    apply eq_ite_iff.mpr
    right
    simp
    intro HK
    rename_i h
    apply h
    exact List.append_inj_left' HK rfl
  conv =>
    enter [1, 1, a, 2, 1, b]
    rw [H]
  clear H

  -- Move the a indicator to the outside
  conv =>
    enter [1, 1, a, 2, 1, b]
    rw [mul_comm]
    rw [<- mul_assoc]
    rw [mul_comm]
  conv =>
    enter [1, 1, a]
    rw [ENNReal.tsum_mul_left]
    rw [<- mul_assoc]
    rw [mul_ite, mul_zero, mul_one]

  rw [<- @tsum_subtype_eq_of_support_subset _ _ _ _ _ { v : ℤ | v = vk } ?G1]
  case G1 =>
    simp [Function.support]
  simp
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨vk, rfl⟩]
  simp
  conv =>
    lhs
    enter [2]
    rw [ENNReal.tsum_eq_zero.mpr
       (by
         intro i
         split <;> simp_all
         intro H
         exfalso
         rename_i H'
         apply H'
         subst Hhistory
         simp_all only [Subtype.coe_eta, not_true_eq_false])]
    · skip
  simp
  rw [mul_comm]
  congr 1

  -- Same for the other indicator
  rw [<- @tsum_subtype_eq_of_support_subset _ _ _ _ _ { v : { v // v.length = N } | v = ⟨ history, Hhistory ⟩ } ?G1]
  case G1 =>
    simp [Function.support]
    intros
    symm
    trivial
  rw [ENNReal.tsum_eq_add_tsum_ite ⟨⟨history, Hhistory⟩, rfl⟩]
  simp
  rw [ENNReal.tsum_eq_zero.mpr]
  · simp
  simp



-/
def privMax_presample_sep_normalizes : HasSum (@privMax_presample_sep dps ε₁ ε₂ l) 1 := by
  sorry
  -- rw [<- privMax_reduction_3]
  -- rw [<- privMax_reduction_2]
  -- rw [<- privMax_reduction_1]
  -- rw [<- privMax_reduction_0]
  -- exact privMaxPMF_normalizes


-- To express differential privacy, we need pricMax_presample_sep to be a PMF
def privMax_presample_sep_PMF {dps : DPSystem ℕ} (ε₁ ε₂ : ℕ+) (l : List ℕ) : PMF ℕ :=
  ⟨ @privMax_presample_sep dps ε₁ ε₂ l, privMax_presample_sep_normalizes ⟩


end SLang
