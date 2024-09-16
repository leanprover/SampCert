/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Properties
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` pure DP

This file proves pure DP for privMax.

Follows the proof given for Algorithm 1 pp. 57 "The Sparse Vector Technique"
in "The Algorithmic Foundations of Differential Privacy", Dwork & Roth.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

-- Enables the change of variables in privMax_reduct_PureDP
/--
Sums over ℤ can be shifted by any any amount
-/
lemma tsum_shift_lemma (f : ℤ -> ENNReal) (Δ : ℤ) : ∑'(t : ℤ), f t = ∑'(t : ℤ), f (t + Δ) := by
  apply tsum_eq_tsum_of_bij (fun z => z + Δ) <;> simp [Function.Injective]
  intro x Hf
  exists (x - Δ)
  simp
  trivial


lemma exactClippedSum_append : exactClippedSum i (A ++ B) = exactClippedSum i A + exactClippedSum i B := by
  simp [exactClippedSum]


lemma exactClippedSum_singleton_diff : (-exactClippedSum i [v] + exactClippedSum (1 + i) [v]).natAbs ≤ 1 := by
  simp [exactClippedSum]
  cases Classical.em ((v : ℤ) ≤ (i : ℤ))
  · rw [min_eq_left_iff.mpr (by trivial)]
    rw [min_eq_left_iff.mpr (by linarith)]
    simp
  · rw [min_eq_right_iff.mpr (by linarith)]
    cases Classical.em ((v : ℤ) ≤ 1 + (i : ℤ))
    · rw [min_eq_left_iff.mpr (by linarith)]
      have Z : (-(i : ℤ) + (v : ℤ) = 1) := by linarith
      simp_all
    · rw [min_eq_right_iff.mpr (by linarith)]
      simp


lemma exactDiffSum_neighbours {l₁ l₂ : List ℕ} (i : ℕ) (HN : Neighbour l₁ l₂) :
    (exactDiffSum i l₁ - exactDiffSum i l₂).natAbs ≤ 2 := by
  cases HN
  · rename_i A B v H1 H2
    subst H1 H2
    unfold exactDiffSum
    repeat rw [exactClippedSum_append]
    ring_nf
    apply le_trans ?G1 ?G2
    case G1 => apply exactClippedSum_singleton_diff
    linarith

  · rename_i A v B H1 H2
    subst H1 H2
    unfold exactDiffSum
    repeat rw [exactClippedSum_append]
    ring_nf

    apply @le_trans _ _ _ 1 <;> try simp
    apply le_trans _ (@exactClippedSum_singleton_diff i v)
    apply Eq.le
    apply natAbs_eq_natAbs_iff.mpr
    simp
    right
    linarith

  · -- FIXME: We have to double the bound in the literature because of this case.
    -- The literature assumes that neighbours involve addition or deletion of a record, not modification.
    -- This will change the constants used in the program (namely, from ε₁/2ε₂ and ε₁/4ε₂ to something else).
    rename_i A v1 B v2 H1 H2
    subst H1 H2
    unfold exactDiffSum
    repeat rw [exactClippedSum_append]
    ring_nf

    rw [Int.sub_eq_add_neg]
    conv =>
      enter [1, 1]
      rw [add_assoc]
      rw [add_assoc]
      rw [<- add_assoc]
    apply le_trans
    · apply natAbs_add_le
    have X : 1 + 1 = 2 := by simp
    rw [<- X]
    clear X
    apply _root_.add_le_add
    · apply le_trans _ (@exactClippedSum_singleton_diff i v1)
      apply Eq.le
      apply natAbs_eq_natAbs_iff.mpr
      simp
      right
      linarith
    · exact exactClippedSum_singleton_diff


-- Probably delete this
def List.max_default (l : List ℤ) (default : ℤ) : ℤ :=
  match l.maximum with
  | none => default
  | some v => v


-- Probably delete this
lemma max_unbot_eq_max_default (v : ℤ) (l : List ℤ) H :
  (v :: l).maximum.unbot H = List.max_default (v :: l) 0 := by
  unfold List.max_default
  split
  · rename_i x Hx
    exfalso
    apply H
    apply Hx
  · rename_i x Hx
    simp_all
    simp [WithBot.unbot]


-- Element-wise difference between lists
-- Reformulate this as proposition over indicies, which says | L1[k] - L2[k] | ≤ N for all k
-- The inductive prop only really makes sense if
-- diff_le_1_dif_max_le_1 uses an inductive argument, which it shouldn't.
inductive ListDiffLe (N : ℕ) : List ℤ -> List ℤ -> Prop where
| emp {l1 l2 : List ℤ} (H1 : l1 = []) (H2 : l2 = []) :  ListDiffLe N l1 l2
| snoc {v1 v2 : ℤ} {l1 l2 L1 L2: List ℤ} (H1 : ListDiffLe N l1 l2) (H2 : (v1 - v2).natAbs ≤ N)
      (H3 : l1 ++ [v1] = L1) (H4 : l2 ++ [v2] = L2) :
       ListDiffLe N L1 L2


/--
If two lists are pointwise close, then the difference between their maximums are pointwise close
-/
lemma diff_le_1_dif_max_le_1 {N : ℕ} {l1 l2 : List ℤ} (Hl1 : 0 < l1.length) (Hl2 : 0 < l2.length)
  (Hdiff : ListDiffLe N l1 l2) : (List.maximum_of_length_pos Hl1 - List.maximum_of_length_pos Hl2).natAbs ≤ N := by
  simp [List.maximum_of_length_pos]
  --  Get rid of length requirements by cases
  cases l1
  · simp at Hl1
  rename_i v1 l1'
  cases l2
  · simp at Hl2
  rename_i v2 l2'

  -- Get rid of proof terms
  rw [max_unbot_eq_max_default]
  rw [max_unbot_eq_max_default]
  simp_all
  generalize HL1 : (v1 :: l1') = L1
  generalize HL2 : (v2 :: l2') = L2
  simp_all
  clear HL1 HL2 l1' l2' v1 v2

  -- The inductive proof is a mess. Cleaner outline:
  -- let L1[i] be the maximum of L1
  -- let L2[j] is the maximum of L2
  -- assume the lists are pw close: | L1[k] - L2[k] | ≤ N for all k
  -- wlog L2[j] ≤ L1[i]
  -- then
  --    L1[i] - N ≤ L2[i]     By def'n pw close
  --              ≤ L2[j]     By def'n max
  --              ≤ L1[i]     By assumption wlog
  --
  -- so | L1[i] - L2[j] | ≤ N

  sorry


lemma helper1 (A B C D : ENNReal) : (C = D) -> A ≤ B -> A * C ≤ B * D := by
  intro H1 H2
  apply mul_le_mul' H2
  subst H1
  rfl

/--
Reduced, history-aware, presampled, separated program  is (ε₁/ε₂)-DP
-/
lemma privMax_reduct_PureDP {ε₁ ε₂ : ℕ+} : PureDP (@privMax_presample_PMF PureDPSystem ε₁ ε₂) (ε₁ / ε₂) := by
  -- Transform into inequality
  simp [PureDP]
  apply singleton_to_event
  simp [DP_singleton]
  intro l₁ l₂ HN n
  apply (ENNReal.div_le_iff_le_mul ?G1 ?G2).mpr
  case G1 =>
    right
    exact ENNReal.ofReal_ne_top
  case G2 =>
    left
    apply PMF.apply_ne_top
  unfold privMax_presample_PMF
  simp [DFunLike.coe, PMF.instFunLike]

  -- Eliminate the first n-1 random choices by cancellation
  simp [privMax_presample, gen_sv_presampled]
  conv =>
    enter [1, 1, τ]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, vk]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
  conv =>
    enter [1]
    rw [ENNReal.tsum_comm]
    enter [1, vk]
    rw [ENNReal.tsum_mul_left]
  conv =>
    enter [2, 2, 1, τ]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, vk]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
  conv =>
    enter [2, 2]
    rw [ENNReal.tsum_comm]
    enter [1, vk]
    rw [ENNReal.tsum_mul_left]
  conv =>
    enter [2]
    rw [<- ENNReal.tsum_mul_left]
    enter [1, τ]
    rw [<- mul_assoc]
    rw [mul_comm (ENNReal.ofReal _)]
    rw [mul_assoc]
  apply ENNReal.tsum_le_tsum
  intro history
  apply mul_le_mul'
  · rfl

  -- Change of variables will not work for empty history as it uses G explicitly
  -- We do a different change of variables in the history=[] case
  cases history
  · simp [privMax_eval_alt_cond]
    unfold G

    -- Cancel τ
    conv =>
      enter [2]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, vk]
      rw [mul_comm]
      rw [mul_assoc]
      enter [2]
      rw [mul_comm]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply mul_le_mul'
    · rfl

    -- Unfold defs
    simp [privNoiseZero, DPSystem.noise]

    -- Change of variables
    let cov_Δvk : ℤ := exactDiffSum 0 l₁ - exactDiffSum 0 l₂
    conv =>
      enter [2, 2]
      rw [tsum_shift_lemma _ cov_Δvk]
      dsimp [cov_Δvk]

    -- After the COV, the bodies satisfy the bound pointwise
    rw [<- ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro vk
    rw [<- mul_assoc]
    apply helper1
    · -- Indicator functions are equal
      split <;> split <;> try rfl
      · rename_i HK1 HK2
        exfalso
        apply HK2
        apply le_trans HK1
        conv =>
          enter [2, 2]
          rw [add_comm]
        rw [<- add_assoc]
        apply _root_.add_le_add _ (by rfl)
        rw [← WithBot.coe_add]
        rw [WithBot.coe_le_coe]
        linarith
      · rename_i HK1 HK2
        exfalso
        apply HK1
        apply le_trans HK2
        conv =>
          enter [1, 2]
          rw [add_comm]
        rw [<- add_assoc]
        apply _root_.add_le_add _ (by rfl)
        rw [← WithBot.coe_add]
        rw [WithBot.coe_le_coe]
        linarith

    · -- Constants satisfy inequality

      -- Simplify noise expression
      simp [privNoisedQueryPure]
      simp [DiscreteLaplaceGenSamplePMF]
      simp only [DFunLike.coe, PMF.instFunLike]
      simp [DiscreteLaplaceGenSample_apply]

      -- Combine the coercions
      rw [<- ENNReal.ofReal_mul ?G1]
      case G1 => apply exp_nonneg
      apply ENNReal.ofReal_le_ofReal

      -- Cancel constant factor terms
      conv =>
        enter [2]
        rw [mul_comm]
        rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ ?G1
      case G1 =>
        apply div_nonneg
        · simp
          apply div_nonneg
          · apply cast_nonneg'
          · apply mul_nonneg
            · simp
            · apply cast_nonneg'
        · apply add_nonneg <;> try simp
          apply exp_nonneg
      rw [← exp_add]
      apply Real.exp_le_exp.mpr
      simp only [le_neg_add_iff_add_le, add_neg_le_iff_le_add]


      -- Move factor to other side
      apply div_le_of_nonneg_of_le_mul ?G1 ?G2
      case G1 => apply mul_nonneg <;> simp
      case G2 =>
        apply add_nonneg
        · apply div_nonneg <;> simp
        · apply div_nonneg <;> try simp
          apply mul_nonneg <;> simp

      -- Simplify fractions on RHS
      simp [add_mul]
      conv =>
        enter [2, 1]
        rw [mul_comm]
        rw [division_def]
        rw [division_def]
        repeat rw [mul_assoc]
        enter [2]
        rw [mul_comm]
        repeat rw [<- mul_assoc]
        simp
      simp
      rw [add_comm]

      -- Transitivity with triangle inequality on LHS
      apply le_trans (abs_add _ _)
      apply _root_.add_le_add _ (by rfl)
      rw [← natAbs_to_abs]
      simp
      apply le_trans (@exactDiffSum_neighbours l₁ l₂ 0 HN)
      simp

  · -- History is not empty

    -- Change of variables
    rename_i hist0 histR
    generalize Hhistory : (hist0 :: histR) = history
    have Hhistory_len : 0 < history.length := by
      rw [<- Hhistory]
      simp
    let cov_τ : ℤ := G l₂ ⟨ history, Hhistory_len ⟩ - G l₁ ⟨ history, Hhistory_len  ⟩
    let cov_vk  : ℤ := G l₂ ⟨ history, Hhistory_len ⟩ - G l₁ ⟨ history, Hhistory_len ⟩ + exactDiffSum n l₁ - exactDiffSum n l₁
    conv =>
      enter [2, 2]
      rw [tsum_shift_lemma _ cov_τ]
      enter [1, t, 2]
      rw [tsum_shift_lemma _ cov_vk]

    -- The inequality now holds element-wise
    conv =>
      enter [1, 1, i]
      rw [<- ENNReal.tsum_mul_left]
    conv =>
      enter [2]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, i]
      rw [<- ENNReal.tsum_mul_left]
      rw [<- ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply ENNReal.tsum_le_tsum
    intro vk
    repeat rw [<- mul_assoc]
    apply helper1
    · -- The conditionals are equal
      split <;> split <;> try rfl
      · rename_i HK1 HK2
        rcases HK1 with ⟨ HK11, HK12 ⟩
        exfalso
        apply HK2
        -- Separate the upper and lower bounds
        apply And.intro
        · dsimp [cov_τ]
          dsimp [cov_vk]
          simp [privMax_eval_alt_cond]
          cases history
          · simp_all
          rw [List.cons_append]
          simp
          simp [privMax_eval_alt_cond] at HK11
          apply le_trans ?G3
          case G3 =>
            apply _root_.add_le_add
            · apply HK11
            · rfl
          rename_i hist0 histT
          -- rw [<- List.cons_append] -- Type error
          sorry

          -- -- Want to use HK11
          -- simp only []
          -- simp only [decide_eq_false_iff_not, not_lt]
          -- simp only [G, List.le_maximum_of_length_pos_iff, WithBot.coe_add]
          -- rw [<- List.cons_append]
          -- rw [List.mapIdx_append_one]
          -- simp [privMax_eval_alt_cond] at HK11
          -- simp [G] at HK11
          -- simp
          -- clear HK11
          -- rw [List.maximum_cons]
          -- rw [List.maximum_cons]
          -- rw [List.maximum_concat]

        · dsimp [cov_τ]
          simp [privMax_eval_alt_cond]
          split
          · simp
          simp
          simp [privMax_eval_alt_cond] at HK12
          linarith
      · rename_i HK1 HK2
        rcases HK2 with ⟨ HK21, HK22 ⟩
        exfalso
        apply HK1
        -- Separate the upper and lower bounds
        apply And.intro
        · -- Similar to sorry in other case
          sorry

        · simp [privMax_eval_alt_cond]
          split <;> simp
          simp [privMax_eval_alt_cond] at HK22
          dsimp [cov_τ] at HK22
          linarith

    · -- Noise inequality
      conv =>
        enter [2]
        rw [mul_assoc]
        rw [mul_comm]
        rw [mul_assoc]

      simp [privNoiseZero]
      simp only [DFunLike.coe, PMF.instFunLike]
      simp [DPSystem.noise]
      simp [privNoisedQueryPure]
      simp [DiscreteLaplaceGenSamplePMF]

      -- Combine coercions
      -- Simplify me
      rw [<- ENNReal.ofReal_mul ?G1]
      case G1 =>
        apply mul_nonneg
        · apply div_nonneg
          · simp
            apply div_nonneg <;> simp
          · apply add_nonneg <;> try simp
            apply exp_nonneg
        · apply exp_nonneg
      rw [<- ENNReal.ofReal_mul ?G1]
      case G1 =>
        apply mul_nonneg
        · apply div_nonneg
          · simp
            apply div_nonneg <;> simp
          · apply add_nonneg <;> try simp
            apply exp_nonneg
        · apply exp_nonneg
      rw [<- ENNReal.ofReal_mul ?G1]
      case G1 =>
        apply mul_nonneg
        · apply div_nonneg
          · simp
            apply div_nonneg <;> simp
          · apply add_nonneg <;> try simp
            apply exp_nonneg
        · apply exp_nonneg
      apply ENNReal.ofReal_le_ofReal

      -- Combine and cancel exponentials
      conv =>
        congr
        · enter [1, 1]
          rw [division_def]
        · enter [1, 1]
          rw [division_def]
      repeat rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ ?G1
      case G1 =>
        simp
        apply div_nonneg <;> simp
      apply mul_le_mul_of_nonneg_left _ ?G1
      case G1 =>
        simp
        apply add_nonneg <;> try simp
        apply exp_nonneg
      repeat rw [<- exp_add]
      conv =>
        congr
        · rw [mul_comm]
        · rw [mul_comm]
      repeat rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ ?G1
      case G1 =>
        apply div_nonneg
        · simp
          apply div_nonneg <;> simp
        · apply add_nonneg <;> try simp
          apply exp_nonneg
      repeat rw [<- exp_add]
      apply Real.exp_le_exp.mpr
      simp

      -- Move factor to other side
      apply (@_root_.mul_le_mul_right _ (OfNat.ofNat 4 * ε₂.val.cast / ε₁.val.cast) _ _ _ _ _ _ _ ?G1).mp
      case G1 => simp

      -- Simplify
      repeat rw [add_mul]
      simp
      conv =>
        enter [1, 2, 1, 2]
        repeat rw [division_def]
        repeat rw [mul_inv]
        repeat rw [mul_assoc]
        simp
        enter [1, 2, 2]
        rw [mul_comm (ε₁.val.cast) _]
        rw [mul_comm]
        repeat rw [mul_assoc]
        simp
      conv =>
        enter [1, 2, 2]
        rw [division_def]
        repeat rw [mul_inv]
        rw [mul_assoc]
        enter [2]
        rw [mul_comm]
        rw [division_def]
        rw [mul_assoc]
        rw [mul_assoc]
        enter [2]
        rw [mul_comm]
        rw [mul_comm (_⁻¹) _]
        rw [division_def]
        rw [mul_inv]
        rw [mul_inv]
        repeat rw [mul_assoc]
        simp
      conv =>
        enter [2]
        rw [mul_comm]
        rw [division_def]
        repeat rw [mul_assoc]
        enter [2]
        rw [division_def]
        simp
      simp
      ring_nf

      -- Apply the triangle inequality
      apply le_trans ?G1
      case G1 =>
        apply (_root_.add_le_add ?G2 ?G3)
        case G2 =>
          apply (_root_.add_le_add ?G4 ?G5)
          case G4 => apply abs_add
          case G5 => rfl
        case G3 =>
          apply (_root_.mul_le_mul ?G4 ?G5 ?G6 ?G7)
          case G4 => apply abs_add
          case G5 => rfl
          case G6 => simp
          case G7 =>
            apply Left.add_nonneg
            · apply abs_nonneg
            · apply abs_nonneg
      ring_nf
      simp [G]
      apply (le_div_iff ?G1).mp
      case G1 => simp
      -- FIXME: the constant on the right is too small now, we need to increase it to 2
      -- by changing the constants.
      -- This is because out version of neighbours is different to the paper's.

      -- Then:
      -- Apply the difference of maximums lemma with N = 2
      -- Show that the lists have pointwise difference at most 2 using exactDiffSum_neighbours

      sorry

/--
privMax is (ε₁/ε₂)-DP
-/
lemma privMax_PureDP {ε₁ ε₂ : ℕ+} : PureDP (@privMaxPMF PureDPSystem ε₁ ε₂) (ε₁ / ε₂) := by
  -- apply DPSystem_mech_prop_ext _ _ _ privMax_reduct_PureDP
  -- apply funext
  -- intro l
  -- unfold privMax_presample_sep_PMF
  -- unfold privMaxPMF
  -- congr
  sorry
  -- rw [privMax_reduction_0]
  -- rw [privMax_reduction_1]
  -- rw [privMax_reduction_2]
  -- rw [privMax_reduction_3]

end SLang
