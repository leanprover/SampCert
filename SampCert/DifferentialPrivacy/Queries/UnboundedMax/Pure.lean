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


lemma exactDiffSum_neighbours {l₁ l₂ : List ℕ} (i : ℕ) (HN : Neighbour l₁ l₂) :
    (exactDiffSum i l₁ - exactDiffSum i l₂).natAbs ≤ 1 := by
  cases HN
  · rename_i A B v H1 H2
    subst H1 H2
    unfold exactDiffSum
    unfold exactClippedSum
    rw [Int.sub_sub]
    repeat rw [List.map_append]
    generalize HV1 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n i)) A) = V1
    generalize HV2 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n i)) B) = V2
    generalize HV3 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n (i + 1))) A) = V3
    generalize HV4 : (List.map (fun (n : Nat) => @Nat.cast Int _ (Nat.min n (i + 1))) B) = V4
    simp
    -- Doable
    sorry
  · sorry
  · sorry



def List.max_default (l : List ℤ) (default : ℤ) : ℤ :=
  match l.maximum with
  | none => default
  | some v => v

-- Since the list is nonempty, the argmax exists
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
inductive ListDiffLe (N : ℕ) : List ℤ -> List ℤ -> Prop where
| emp {l1 l2 : List ℤ} (H1 : l1 = []) (H2 : l2 = []) :  ListDiffLe N l1 l2
| snoc {v1 v2 : ℤ} {l1 l2 L1 L2: List ℤ} (H1 : ListDiffLe N l1 l2) (H2 : (v1 - v2).natAbs ≤ N)
      (H3 : l1 ++ [v1] = L1) (H4 : l2 ++ [v2] = L2) :
       ListDiffLe N L1 L2


lemma ldle_eq_lens_r {N : ℕ} {L : List ℤ} (H : ListDiffLe N [] L) :  L = [] := by
  sorry

lemma ldle_eq_lens_l {N : ℕ} {L : List ℤ} (H : ListDiffLe N L []) :  L = [] := by
  sorry


lemma cons_ex_app (v : T) (L : List T) : ∃ v' : T, ∃ L' : List T, v :: L = L' ++ [v'] := by
  sorry


lemma list_max_default_snoc {v : ℤ} {L : List ℤ} : List.max_default (l1 ++ [v1]) 0  = max v1 (List.max_default l1 0) := by
  sorry

/-
If two lists are pointwise close, then the difference between their maximums are pointwise close
-/
lemma diff_le_1_dif_max_le_1 {N : ℕ} {l1 l2 : List ℤ} (Hl1 : 0 < l1.length) (Hl2 : 0 < l2.length)
  (Hdiff : ListDiffLe N l1 l2) : (List.maximum_of_length_pos Hl1 - List.maximum_of_length_pos Hl2).natAbs ≤ N + N := by
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

  revert L2

  -- Need to do reversed induction here too
  revert L1
  apply List.list_reverse_induction
  · intro L2 Hdiff
    rw [ldle_eq_lens_r Hdiff]
    simp

  intro L1' L1v IH' L2 Hdiff

  cases L2
  · rw [ldle_eq_lens_l Hdiff]
    simp
  rename_i v2' L2'

  rcases (cons_ex_app v2' L2') with ⟨ v2'', ⟨ L2'', Hab ⟩ ⟩
  rw [Hab]
  rw [Hab] at Hdiff
  clear Hab

  cases Hdiff
  · simp_all
  rename_i v1 v2 l1 l2 Hdiff_rec Hdiff_head Heq1 Heq2
  -- Fix for dependent pattern match
  have X (A B : List ℤ) (c d : ℤ) : A ++ [c] = B ++ [d] -> A = B ∧ c = d := by
    intro H
    apply List.of_concat_eq_concat
    simp_all
  rcases (X _ _ _ _ Heq1) with ⟨ Heq11, Heq12 ⟩
  subst Heq11 Heq12
  rcases (X _ _ _ _ Heq2) with ⟨ Heq21, Heq22 ⟩
  subst Heq21 Heq22
  clear Heq1 Heq2 X

  have IH := IH' _ Hdiff_rec
  clear IH' Hdiff_rec

  simp [List.max_default]
  split
  · rename_i _ Hcontra
    exfalso
    -- Weird warning
    apply List.maximum_eq_none.mp at Hcontra
    simp at Hcontra
  rename_i _ m1 Hm1
  apply List.maximum_eq_coe_iff.mp at Hm1
  rcases Hm1 with ⟨ Hm1_in, Hm1_ge ⟩
  split
  · rename_i _ Hcontra
    exfalso
    -- Weird warning
    apply List.maximum_eq_none.mp at Hcontra
    simp at Hcontra
  rename_i _ m2 Hm2
  apply List.maximum_eq_coe_iff.mp at Hm2
  rcases Hm2 with ⟨ Hm2_in, Hm2_ge ⟩

  simp at Hm1_in
  cases Hm1_in
  · simp_all
    cases Hm2_in
    · sorry
    sorry
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

      -- -- Suffices to show that ExactDiffSum is le 1 on neighbours
      -- rw [← natAbs_to_abs]
      -- suffices ((exactDiffSum (OfNat.ofNat 0) l₁ - exactDiffSum (OfNat.ofNat 0) l₂).natAbs ≤ 1) by
      --   cases Classical.em ((exactDiffSum (OfNat.ofNat 0) l₁ - exactDiffSum (OfNat.ofNat 0) l₂) = 0)
      --   · simp_all
      --   apply (Real.natCast_le_toNNReal ?G1).mp
      --   case G1 =>
      --     simp_all only [ne_eq, natAbs_eq_zero, not_false_eq_true]
      --   simp
      --   apply le_trans this
      --   simp
      -- apply (exactDiffSum_neighbours _ HN)
      sorry

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
        · sorry
        · sorry
      · rename_i HK1 HK2
        rcases HK2 with ⟨ HK21, HK22 ⟩
        sorry

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
      -- I guess since G is the max of exactDiffSum, each of which has difference less than 1,
      -- so the difference of maximums can't be less than 1
      apply (le_div_iff ?G1).mp
      case G1 => simp


      -- Seems that we do need to improve this argument, actually, since the difference between G's
      -- is bounded above by 2

      sorry


      /-
      apply (@le_trans _ _ _ 1 _ _ (by linarith))
      rw [← natAbs_to_abs]
      simp
      apply diff_le_1_dif_max_le_1

      -- Show that the lists are uniformly close
      clear cov_τ cov_vk
      clear Hhistory Hhistory_len

      revert history
      apply List.list_reverse_induction
      · simp
        constructor <;> simp
      · intro history' vk IH
        rw [List.mapIdx_append_one]
        rw [List.mapIdx_append_one]
        apply (@ListDiffLe.snoc 1 _ _ _ _ _ _ IH ?G1 (by rfl) (by rfl))
        simp only [add_sub_add_right_eq_sub]
        apply exactDiffSum_neighbours history'.length
        apply Neighbour_symm
        apply HN
      -/


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
