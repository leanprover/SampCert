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
Probability that privMax evaluates to k, ie, the probability
the the loop unrolls exactly k times.
-/
def privMax_cut (ε₁ ε₂ : ℕ+) (l : List ℕ) (N : ℕ) : SLang ℤ := do
  let τ <- privNoiseZero ε₁ (2 * ε₂)
  let (k, _) <-
    (probWhileCut
      (fun (k, vk) => exactDiffSum k l + vk < τ)
      (fun (km1, _) => do
        let k := km1 + 1
        let vk <- privNoiseZero ε₁ (4 * ε₂)
        return (k, vk))
      N
      ((0 : ℕ), <- privNoiseZero ε₁ (4 * ε₂)))
  return k

-- Since the max returnable value increases by at most 1 every iteration, and
--    privMaxCut _ _ _ 0 = (fun _ => 0),
-- we should be able to prove that for all N ≥ K ≥ 0
--   privMaxCut _ _ _ N K = 0

-- This can be used in a lemma to show that it's eventually constant, ie
-- for all N ≥ S k:
--    privMaxCut _ _ _ (N + 1) k = privMaxCut _ _ _ N k
-- This is because, if we do more unrollings, it just adds more branches
-- into a paths which all return values greater than k, by the lemma before.

-- Then, there should be a lemma about the limits of eventually constant sequences, which
-- alongside probWhile_apply, should be able to rewrite
--  privMax ... k = (let τ <- ..., privMax_cut ... k k)

lemma privMax_eval_unroll {ε₁ ε₂ : ℕ+} {l : List ℕ} {k : ℕ} :
    @privMax_eval PureDPSystem ε₁ ε₂ l k = 0 := by
  sorry




-- Now we have to evaluate privMaxCut _ _ _ k k into a closed form.

-- We can define the G quantity. This is not a random variable!
-- equals a simple program which samples τ and vk, computes (G l) and tests an inequality between them.

-- To do this, we will rewrite into "GD form" which is
--    - Compute the max from the first k-1 unrollings
--    - Compute G k from that
--    - Do that last iteration comparing to GD
-- Since (privMaxCut _ _ _ k) only returns k after exactly k iterations, this should
-- be provable by induction.

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




end SLang
