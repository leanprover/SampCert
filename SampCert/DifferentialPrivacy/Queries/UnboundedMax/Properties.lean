/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` Properties

This file proves pure DP for privMax, and zCDP for privMax using
the (ε^2/2)-zCDP bound.

privMax implemented using the abstract DP system, but I am not aware of how
to generalize the privacy proof to the abstract DP case.

Follows the proof given for Algorithm 1 pp. 57 "The Sparse Vector Technique"
in "The Algorithmic Foundations of Differential Privacy", Dwork & Roth.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

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

    -- probWhileFunctional cond body (probWhileSplit cond body base n) a

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
Move iterates of probWhileSplit into the initial value, when the continuation is probPure

Probably no use for this theorem
-/
lemma probWhileSplit_succ_r (cond : T → Bool) (body : T → SLang T) (n : Nat) (init : T):
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
privMax unrolled at most k times
-/
def privMax_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) (N : ℕ) : SLang ℕ := do
  let τ <- privNoiseZero ε₁ (2 * ε₂)
  let v0 <- privNoiseZero ε₁ (4 * ε₂)
  let r <- (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N (0, v0))
  return r.1


lemma privMax_cut_loop_0 (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (init : ℕ × ℤ) :
    probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) 0 init = probZero := by
  simp [probWhileCut]

/--
Move one iterate from a probWhileCut out to a probWhileSplit

MARKUSDE: We probably want the other direction: moving into init
-/
lemma privMax_cut_loop_succ_l (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (N : ℕ) (init : ℕ × ℤ) :
    probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) (Nat.succ N) init =
    probWhileSplit (privMaxC τ l) (privMaxF ε₁ ε₂) (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N) 1 init := by
  simp [probWhileCut, probWhileFunctional, probWhileSplit]

/--
Separate the first N iterates from probMax_cut:
Do n iterates inside a probWhileSplit, and the remaining M iterates inside probWhileCut
-/
lemma privMax_cut_loop_add_l (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (N M : ℕ) (init : ℕ × ℤ) :
    probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) (N + M) init =
    probWhileSplit (privMaxC τ l) (privMaxF ε₁ ε₂) (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N) M init := by
  revert init
  induction N
  · intro init
    simp [probWhileCut]
    rw [probWhileCut_probWhileSplit_zero]
  · intro init
    rename_i N' IH
    rw [add_assoc, add_comm, add_assoc, add_comm]
    rw [privMax_cut_loop_succ_l]
    rw [add_comm]
    rw [funext IH]
    rw [(funext (privMax_cut_loop_succ_l _ _ _ _ _))]
    rw [<- probWhileSplit_add_l]
    rw [<- probWhileSplit_add_l]
    rw [add_comm]


/--
Boundary of the support of the privMax_cut loop:
If we start in state (N, ?), for any k, (N + K + 1) will be zero after K steps.
ie. We step zero times, (N + 0 + 1) = N and beyond is still zero (since it starts with zero distribution)
     We step two times, (N + 2) and beyond is zero.
-/
lemma privMax_cut_loop_support_bound (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (K N : ℕ) (vp: ℤ) (vi : ℤ)  :
    probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) K (N, vi) (N + K, vp) = 0 := by
  revert vi vp
  induction K
  · -- Exact boundary
    induction N <;> simp [probWhileCut]
  · rename_i K' IH
    induction N
    · sorry
    · rename_i N' IH'
      intro vp vi
      simp [probWhileCut, probWhileFunctional]
      split
      · simp
        simp at *
        rename_i H
        intro a b
        simp [privMaxF]
        have Ha : a ≠ N' + 1 + 1 := by sorry
        right
        have IH := IH vp vi
        -- This is not helping
        sorry
      · simp

    -- intros vp vi
    -- simp [probWhileCut, probWhileFunctional]
    -- split
    -- · simp
    --   revert vi vp
    --   induction N
    --   · intro vi vp Hc a b
    --     simp [privMaxF]
    --     simp at IH

    --     have Ha : a ≠ 1 := by admit -- Could use full support of Laplace to get this if we need it
    --     right

    --     -- What we need to finish this proof is the relationship between taking a step
    --     -- and the support changing, which for some reaons, is proving to be difficult.
    --     -- Are my definitions correct?


    --     -- So lost
    --     sorry


    --   · sorry

    --   -- intro a b
    --   -- right
    --   -- revert a b -- vp vi

    -- · simp



/--
Support of privMax_cut is bounded abouve by the cut number
-/
lemma privMax_cut_support_le_k (ε₁ ε₂ : ℕ+) (l : List ℕ) (N K : ℕ) :
    privMax_cut ε₁ ε₂ l N (N + K) = 0 := by
  simp [privMax_cut]
  intro τ
  right
  intro v0
  right
  intro r vr Hr
  subst Hr

  -- The condition itself does not matter to this proof
  generalize HC : (fun (x : ℕ × ℤ) => decide (exactDiffSum x.1 l + x.2 < τ)) = C
  clear HC
  rw [probWhileCut_probWhileSplit_zero]
  revert v0 N
  induction K
  · intros N v0
    simp
    -- Equality case. Hmm.
    sorry
  · intros N v0
    rename_i K' IH
    have IH := IH N v0

    sorry

  -- -- Am I inducting on the wrong thing?
  -- induction N
  -- · aesop
  -- · rename_i N' IH
  --   intro K v0

  --   -- Same as doing 1 iteration and then N' iterations
  --   rw [probWhileSplit_succ_l]
  --   simp [probWhileSplit]
  --   split
  --   · simp
  --     intro v1
  --     right
  --     rw [<- IH K v1]

  --     -- Need a shifting lemma

  --     -- Err... the shifting lemma might not be provable
  --     -- Because the condition depends on the start value

  --     -- Incremeting the start condition just shifts the final distribution
  --     -- Simplify irrelevant the expression for quality of life
  --     generalize HF : (fun (x : ℕ × ℤ) => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) = F
  --     conv =>
  --       enter [1, 6, 1]
  --       rw [add_comm]
  --       rw [<- add_assoc]
  --       enter [1]
  --       rw [add_comm]
  --     generalize HD : (N' + K) = D
  --     clear HD
  --     clear IH
  --     induction N'
  --     · simp [probWhileSplit]
  --     · rename_i N'' IH''
  --       conv =>
  --         enter [1]
  --         rw [probWhileSplit_succ_l]
  --       rw [probWhileSplit_succ_l]
  --       simp [probWhileSplit]
  --       sorry
  --   · simp



-- Since the max returnable value increases by at most 1 every iteration, and
--    privMaxCut _ _ _ 0 = (fun _ => 0),
-- we should be able to prove that for all N ≥ K ≥ 0
--   privMaxCut _ _ _ N K = 0



/--
privMax_cut is eventually constant (at every point N, it is constant after N terms).
-/
lemma privMax_cut_support_eventually_constant (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (N K : ℕ) (VN : ℤ) :
    probWhileCut (privMaxC τ l)
      (fun x => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) (N + K) (0, v0) (N, VN) =
    probWhileCut (privMaxC τ l)
      (fun x => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) N (0, v0) (N, VN) := by

  rw [probWhileCut_probWhileSplit_zero]
  rw [probWhileCut_probWhileSplit_zero]

  -- Induction: Reduce from (... N + K) to (... N + 1)
  induction K
  · simp
  · rename_i K' IH
    conv =>
      enter [1, 4]
      rw [<- add_assoc]
    rw [probWhileSplit_succ_l]
    generalize HF : (fun (x : ℕ × ℤ) => (privNoiseZero ε₁ (4 * ε₂)).probBind fun vk => probPure (x.1 + 1, vk)) = F
    rw [HF] at IH
    rw [<- IH]
    rw [<- probWhileSplit_succ_l]

    -- Split it up into the first N terms, and the remaining K' or K'+1 terms in the contiunation
    -- The "extra branches" should all be 0 when evaluated at N, their initial values all start higher than N.


    -- FIXME: Actually do this step to make sure the lemmas I'm trying to prove are the right ones.

    sorry



-- This can be used in a lemma to show that it's eventually constant, ie
-- for all N ≥ S k:
--    privMaxCut _ _ _ (N + 1) k = privMaxCut _ _ _ N k


-- This is because, if we do more unrollings, it just adds more branches
-- into a paths which all return values greater than k, by the lemma before.

-- Then, there should be a lemma about the limits of eventually constant sequences, which
-- alongside probWhile_apply, should be able to rewrite
--  privMax ... k = (let τ <- ..., privMax_cut ... k k)
lemma privMax_eval_limit {ε₁ ε₂ : ℕ+} {l : List ℕ} {k : ℕ} :
    @privMax_eval PureDPSystem ε₁ ε₂ l k = privMax_cut ε₁ ε₂ l k k := by
  simp [privMax_eval, privMax_cut]
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1
  apply tsum_congr
  intro (r, vr)
  split <;> try simp
  rename_i Hk
  subst Hk
  apply probWhile_apply

  -- Evaluate the filter
  apply (@tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ k)
  intro i Hi
  rw [<- Nat.add_sub_cancel' Hi]
  apply (@privMax_cut_support_eventually_constant v0 ε₁ ε₂ τ l k (i - k) vr)






-- Now we have to evaluate privMaxCut _ _ _ k k into a closed form.

-- We can define the G quantity. This is not a random variable!
-- equals a simple program which samples τ and vk, computes (G l) and tests an inequality between them.

-- To do this, we will rewrite into "GD form" which is
--    - Compute the max from the first k-1 unrollings
--    - Compute G k from that
--    - Do that last iteration comparing to GD
-- Since (privMaxCut _ _ _ k) only returns k after exactly k iterations, this should
-- be provable by induction.

/--
privMax unrolled at most k times
-/
def privMax_G_form (ε₁ ε₂ : ℕ+) (l : List ℕ) (N : ℕ) : SLang ℕ := do
  let τ <- privNoiseZero ε₁ (2 * ε₂)
  let v0 <- privNoiseZero ε₁ (4 * ε₂)
  let (r, vr) <- (probWhileCut (privMaxC τ l) (privMaxF ε₁ ε₂) N (0, v0))
  if (privMaxC τ l (r, vr))
    then
      let (v, _) <- (privMaxF ε₁ ε₂ r)
      return v
    else
      return r







-- Then, we can generalize over GD, to mimic the determinstic definition from the paper.
-- To do this, we need to know that
--    - G(D) is a positive natural number
--    - |G(D) - G(D')| < ε/4


-- /-
-- The maximum value of (exactDiffSum i l + vi) for i < k (not right?)
-- -/
-- def G (k : ℕ) (l : List ℕ) (ε₁ ε₂ : ℕ+) : SLang ℤ :=
--   match k with
--   | Nat.zero => DiscreteLaplaceGenSample ε₁ (4 * ε₂) (exactDiffSum 0 l)
--   | Nat.succ n' => do
--     let z' <- G n' l ε₁ ε₂
--     let v <- DiscreteLaplaceGenSample ε₁ (4 * ε₂) (exactDiffSum (Nat.succ n') l)
--     return (max z' v)

-- G(D) form: Program that equals privMax_unroll in terms of G(D)

-- Now this program should have only two random events, leading us to
-- ∑'(a : ℤ), ∑'(b : ℤ), (distrib. τ) a * (distrib. v_k) b * (indic. (inequality for a b (G l k)))

-- The next step is a change of variables (see pencil and paper)
-- Allowed, since we can shift sums over ℤ by any determistic amount.
-- THen we bound the new difference terms by ε/2 and 2ε/4 resp.

-- Finally we are in G(D')-form
-- We can fold back up to privMax_eval_unroll for D'
-- Then the limits are equal up to e^ε, since they are pointwise equal
-- Then the values of probWhile are equal up to e^ε, since they equal the limit
-- Then the DP property holds




-- New idea: Is there a form which is easier to prove about, and which we can turn into
-- a probWhile after the fact?


-- Maximum noised diffSum of the first vis.length entries
def G (l : List ℕ) (vis : { v : List ℤ // 0 < v.length }) : ℤ :=
  let vis' := (List.mapIdx (fun i vi => exactDiffSum i l + vi) vis)
  let Hvis' : 0 < vis'.length := by
    dsimp [vis']
    cases vis
    simp [List.length_mapIdx]
    trivial
  List.maximum_of_length_pos Hvis'

/--
G is an upper bound on all fuzzed elements
-/
lemma G_spec (l : List ℕ) (vis : { v : List ℤ // 0 < v.length }) (i : ℕ) (Hi : i < vis.1.length) : True := sorry


/--
G only increases as we extend it
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







-- The loop continues when the maximum value so far does not exceed τ.
-- Once it is false once, it is false forever.
def privMax_eval_alt_cond (l : List ℕ) (τ : ℤ) (history : List ℤ) : Bool :=
  match history with
  | [] => true
  | (h :: hs) => G l ⟨ h :: hs, by simp ⟩ < τ

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

-- NOTE Somehow, this could help us do induction on the branches the program never explores.
-- Inductively rewriting branches that are never executed seems like overkill, but the alternative
-- (with the splittting, for example) proved to be quite hard.





def privMax_eval_alt_F (ε₁ ε₂ : ℕ+) (history : List ℤ) : SLang (List ℤ) := do
  let candidate <- privNoiseZero ε₁ (4 * ε₂)
  return history ++ [candidate]

/--
Support of privMaxEval_alt_body is contained in the extensions of the history by one element
-/
lemma privMaxEval_alt_body_supp (ε₁ ε₂ : ℕ+) history eval :
    (privMax_eval_alt_F ε₁ ε₂ history eval) ≠ 0 -> ∃ z, eval = history ++ [z] := by
  simp [privMax_eval_alt_F ]
  intro x Heval _
  exists x



def privMax_eval_alt_loop (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) : SLang (List ℤ) := do
  probWhile
    (privMax_eval_alt_cond l τ)
    (privMax_eval_alt_F ε₁ ε₂)
    (<- privMax_eval_alt_F ε₁ ε₂ [])










-- 0th reduction: Go from complete history-tracking sampler to the sampler I have implemented in code
--  (how do I do this?)

def privMax_eval_alt (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- privNoiseZero ε₁ (2 * ε₂)
  let final_history <- privMax_eval_alt_loop ε₁ ε₂ l τ
  return final_history.length





-- 1st reduction: Pointwise bound on the number of loop iterates
def privMax_eval_alt_loop_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) (N : ℕ) : SLang (List ℤ) := do
  probWhileCut
    (privMax_eval_alt_cond l τ)
    (privMax_eval_alt_F ε₁ ε₂)
    N
    (<- privMax_eval_alt_F ε₁ ε₂ [])

-- Evaluates a point ℕ by evaluating at most N iterates
def privMax_eval_alt_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := (fun N =>
  (do
    let τ <- privNoiseZero ε₁ (2 * ε₂)
    let final_history<- privMax_eval_alt_loop_cut ε₁ ε₂ l τ N
    return final_history.length) N)


lemma privMax_reduction_1 (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    privMax_eval_alt ε₁ ε₂ l = privMax_eval_alt_cut ε₁ ε₂ l := by
  -- Want to show that the eval (unbounded at each point) equals the cut version (cut to N at each point)
  apply SLang.ext
  intro cutoff
  simp [privMax_eval_alt, privMax_eval_alt_cut]
  apply tsum_congr
  intro initial_point
  congr
  apply funext
  -- Loop should be the same evaluated at every history whose length is equal to cutoff
  intro evaluated_history
  split <;> try simp
  rename_i Hcutoff
  simp [privMax_eval_alt_loop, privMax_eval_alt_loop_cut]
  apply tsum_congr
  intro initial_history
  congr

  -- Apply probWhile limit lemma
  apply probWhile_apply
  apply (@tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ cutoff)

  -- Prove that probWhileCut is eventually constant
  intro later_cutoff Hlep
  rw [<- Nat.add_sub_cancel' Hlep]

  -- Change of variables
  generalize Hd : later_cutoff - cutoff = d
  clear Hlep Hd later_cutoff

  -- Revert something about the size of the tape?
  induction d
  · simp
  · -- Apply IH to reduce the difference to 1
    rename_i d' IH
    rw [<- IH]
    clear IH

    -- The tricky thing: The continuation isn't the same for _all_ histories, just
    -- those with at least cutoff samples.
    -- To separate this program into the cuttoff + (d, d+1) part, and prove that the d part
    -- equals the (d+1) part, I need the (d, d+1) parts to know that their tapes have at least cutoff samples
    sorry


  -- Maybe this? Not sure
  -- Split into (do cutoff) with (do d) as continuation
  -- Prove that inner (do d) is zero
  --  - Prove that condition does not change
  --  - Prove that
  -- Continuation is zero
  -- Fold back into probWhile





-- Reduction 2: Sample all the noise upfront (that is, calculate G(D)), and then
-- Check to see if the nth iterate is the terminating one.

def privMax_sampN (ε₁ ε₂ : ℕ+) (N : ℕ) : SLang { v : List ℤ // N = v.length } :=
  match N with
  | Nat.zero => probPure ⟨ [], by simp ⟩
  | Nat.succ N' => do
      let v <- privNoiseZero ε₁ (4 * ε₂)
      let r <- privMax_sampN ε₁ ε₂ N'
      probPure ⟨ v :: r.1, by cases r; simp ; trivial ⟩

-- A length N list only happens when we sample exactly N times,
-- Everyting up to the N-1th time did not terminate, and the Nth time did terminate.
-- (Put this in a probUntil to normalize)
def privMax_eval_alt_loop_cut_presample (ε₁ ε₂ : ℕ+) (l : List ℕ) (τ : ℤ) : SLang ℕ :=
  fun N =>
    ((do
        let candidate <- (privNoiseZero ε₁ (4 * ε₂))
        let history <- privMax_sampN ε₁ ε₂ (N + 1)
        let GD := G l ⟨ history, sorry ⟩ -- Biggest
        probPure 0) N)
  --  >>= (fun candidate => sorry)) N)


-- do
--   let history <-
--   let candidate <- privNoiseZero ε₁ (4 * ε₂)
--   if sorry
--     then probPure sorry -- history
--     else sorry -- probZero?? What?









end SLang
