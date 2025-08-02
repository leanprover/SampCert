import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Basic

namespace RandomizedResponse

open SLang
open ENNRealLemmas

/- Basic facts about Randomized Response, e.g., its distribution and finiteness.
   We then use these facts to prove the final bound for the proof of DP.
-/

 /- RRSinglePushForward is like RRSingleSample, but with "query" taken to be the identity map-/
lemma RRSingleSample_is_RRSinglePushForward (num : Nat) (den : PNat) (h: 2 * num < den) (l : Bool):
  RRSingleSample (fun x => x) num den h l = RRSinglePushForward num den h l := by
  simp [RRSingleSample, RRSinglePushForward]

 /- RRSamplePushForward is like RRSample, but with "query" taken to be the identity map -/
lemma RRSample_is_RRSamplePushForward (num : Nat) (den : PNat) (h: 2 * num < den) (l : List Bool):
  RRSample (fun x => x) num den h l = RRSamplePushForward num den h l := by
  simp [RRSample, RRSamplePushForward, -mapM]
  rfl

/- Probability of a person with private answer "true" giving randomized response "true."-/
lemma RRSingleSample_true_true {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = true):
  RRSingleSample query num den h l true = (den + 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.true_bne, bind_apply, BernoulliSample_apply,
    pure_apply, Bool.true_eq, Bool.not_eq_true', mul_ite,
    Bool.false_eq_true, reduceIte, mul_one, mul_zero, tsum_ite_eq]
  simp
  rw [ENNReal.sub_eq_of_add_eq]
  simp
  rw [@ENNReal.div_eq_top]
  rw [Not]
  intro A
  rcases A with ⟨_,hb⟩
  simp at hb
  rename_i h_1
  simp_all only [ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top, ne_eq, false_and]
  have h_le : (2:ENNReal) *num ≤ den.val := by
    rw [@Nat.lt_iff_le_and_ne] at h
    rcases h with ⟨hl,_⟩
    exact mod_cast hl
  have two_num_fin : (2:ENNReal)* num ≠ ⊤:= by
    simp
    rw [Not]
    intro B
    norm_cast
  have hh : 1 = (den.val + (2:ENNReal) * num)/(2 *den) + (den-2*num)/(2*den):= by
    simp
    rw [@ENNReal.div_add_div_same]
    rw [add_comm]
    conv =>
      enter [2,1,2]
      rw [add_comm]
    rw [← add_assoc]
    rw [sub_add_cancel_ennreal]
    have den_den : 1 = ((den.val :ENNReal) + den.val)/(2*(den.val:ENNReal)) := by
      rw[two_mul]
      rw [ENNReal.div_self]
      simp
      simp
    norm_cast
    rw [@ENNReal.le_coe_iff]
    simp_all only [ne_eq, Nat.cast_mul, Nat.cast_ofNat]
    apply h_le
    simp_all only [WithTop.coe_natCast, Nat.cast_inj]
    apply Eq.refl
    exact two_num_fin
  symm
  exact hh

/- Probability of a person with private answer "true" giving randomized response "false."-/
lemma RRSingleSample_true_false {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = true):
  RRSingleSample query num den h l false = (den - 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.true_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.false_eq, Bool.not_eq_false', mul_ite, ↓reduceIte,
    mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  apply Eq.refl

/- Probability of a person with private answer "false" giving randomized response "true."-/
lemma RRSingleSample_false_true {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = false):
  RRSingleSample query num den h l true = (den - 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.false_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.true_eq, Bool.not_eq_true', mul_ite,
    Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  apply Eq.refl

/- Probability of a person with private answer "false" giving randomized response "false."-/
lemma RRSingleSample_false_false {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (hq : query l = false):
  RRSingleSample query num den h l false = (den + 2 * num) / (2 * den) := by
  rw[RRSingleSample, RRSinglePushForward]
  simp_all only [bind, pure, Bool.false_bne, bind_apply, BernoulliSample_apply, ENNReal.natCast_sub, Nat.cast_mul,
    Nat.cast_ofNat, PNat.mul_coe, PNat.val_ofNat, pure_apply, Bool.false_eq, mul_ite, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_zero, tsum_ite_eq, NNReal.ofPNat, Nonneg.mk_natCast]
  rw [ENNReal.sub_eq_of_add_eq]
  simp
  rw [@ENNReal.div_eq_top]
  rw [Not]
  intro A
  rcases A with ⟨_,hb⟩
  simp at hb
  rename_i h_1
  simp_all only [ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top, ne_eq, false_and]
  have h_le : (2:ENNReal) *num ≤ den.val := by
    rw [@Nat.lt_iff_le_and_ne] at h
    rcases h with ⟨hl,_⟩
    exact mod_cast hl
  have two_num_fin : (2:ENNReal)* num ≠ ⊤:= by
    simp
    rw [Not]
    intro B
    norm_cast
  have hh : 1 = (den.val + (2:ENNReal) * num)/(2 *den) + (den-2*num)/(2*den):= by
    simp
    rw [@ENNReal.div_add_div_same]
    rw [add_comm]
    conv =>
      enter [2,1,2]
      rw [add_comm]
    rw [← add_assoc]
    rw [sub_add_cancel_ennreal]
    have den_den : 1 = ((den.val :ENNReal) + den.val)/(2*(den.val:ENNReal)) := by
      rw[two_mul]
      rw [ENNReal.div_self]
      simp
      simp
    norm_cast
    rw [@ENNReal.le_coe_iff]
    simp_all only [ne_eq, Nat.cast_mul, Nat.cast_ofNat]
    apply h_le
    simp_all only [WithTop.coe_natCast, Nat.cast_inj]
    apply Eq.refl
    exact two_num_fin
  symm
  exact hh

/- RRSinglePushForward always outputs non-zero probabilities. -/
lemma RRSinglePushForward_non_zero {T : Type} (query : T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (l : T) (b : Bool):
  RRSinglePushForward num den h (query l) b ≠ 0 := by
  simp [RRSinglePushForward]
  cases hb : b == query l with
  | true => simp at hb
            subst hb
            simp
            rw [@tsub_eq_zero_iff_le]
            rw [@Mathlib.Tactic.PushNeg.not_le_eq]
            apply quot_lt_one_rev
            norm_cast
            rw [PNat.mul_coe]
            simp_all only [PNat.val_ofNat]
            have hh : den.val - 2*num ≤  den.val:= by simp
            have gg : den.val < 2 *den.val := by simp
            rw [@Nat.le_iff_lt_or_eq] at hh
            cases hh with
            | inl hl =>
              apply LT.lt.trans hl gg
            | inr hr =>
              rw [hr]
              simp
  | false => simp at hb
             rw [← Bool.eq_not_of_ne hb]
             intro
             apply And.intro
             trivial
             apply And.intro
             {norm_cast
              rw [@Nat.sub_eq_zero_iff_le]
              linarith
            }
             {exact ne_of_beq_false rfl}

/- RRSingleSample always outputs non-zero probabilities. -/
lemma RRSingleSample_non_zero {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (b : Bool):
  RRSingleSample query num den h l b ≠ 0 := by
  rw [RRSingleSample]
  apply RRSinglePushForward_non_zero

/- RRSinglePushForward always outputs finite probabilities. -/
lemma RRSingleSample_finite {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : T) (b : Bool):
  RRSingleSample query num den h l b ≠ ⊤ := by
  have hden: ↑(NNReal.ofPNat den) ≠ (0 : ENNReal) := by
                rw [@ne_iff_lt_or_gt]
                apply Or.inr
                simp_all only [NNReal.ofPNat, Nonneg.mk_natCast, gt_iff_lt, ENNReal.coe_pos, Nat.cast_pos]
                apply den.2
  cases hb: b with
  | true => cases hq: query l with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hq]
                apply div_ne_top
                exact Ne.symm (ne_of_beq_false rfl)
                refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?true.true.h2.h1 ?true.true.h2.h2
                aesop
                exact hden
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hq]
                 apply div_ne_top
                 aesop
                 refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?true.false.h2.h1 ?true.false.h2.h2
                 aesop
                 exact hden
  | false => cases hq: query l with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hq]
                apply div_ne_top
                aesop
                refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?false.true.h2.h1 ?false.true.h2.h2
                aesop
                exact hden
      | false => rw [RRSingleSample_false_false _ _ _ _ _ hq]
                 apply div_ne_top
                 rw [@ENNReal.add_ne_top]
                 apply And.intro
                 aesop
                 exact Ne.symm (ne_of_beq_false rfl)
                 refine mult_ne_zero 2 ↑(NNReal.ofPNat den) ?false.false.h2.h1 ?false.false.h2.h2
                 aesop
                 exact hden

/- RRSinglePushForward always outputs finite probabilities.
   Given what was already proved, the simplest way to prove the next lemma
   is to note that RRSinglePushForward and RRSample with the identity query are the same -/
lemma RRSinglePushForward_finite (num : Nat) (den : PNat) (h: 2 * num < den) (l : Bool) (b : Bool):
  RRSinglePushForward num den h l b ≠ ⊤ := by
    rw [←RRSingleSample_is_RRSinglePushForward]
    apply RRSingleSample_finite

/- The next lemma is helpful for the DP Proof. -/
lemma RRSinglePushForward_div_finite (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ l₂ : Bool) (b : Bool):
  RRSinglePushForward num den h l₁ b /  RRSinglePushForward num den h l₂ b ≠ ⊤ := by
    simp
    rw [Not]
    intro h1
    rw [@ENNReal.div_eq_top] at h1
    cases h1 with
    | inl hl =>
      apply And.right at hl
      have hcontr : RRSinglePushForward num den h l₂ b ≠  0 := by apply RRSinglePushForward_non_zero (fun x : Bool => x)
      contradiction
    | inr hr =>
      apply And.left at hr
      have hcontr: RRSinglePushForward num den h l₁ b ≠ ⊤ := by apply RRSinglePushForward_finite
      contradiction

/- The corresponding lemmas showing that RRPushForward is non-zero and finite are in a different file,
   since we need our prod_of_ind_prob lemma for them.
-/

/- RRSamplePushForward assigns a zero probability of transition to a list of different length. -/
lemma RRSamplePushForward_diff_lengths (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : List Bool) (l₂ : List Bool) (hlen : l₁.length ≠ l₂.length):
  RRSamplePushForward num den h l₁ l₂ = 0 := by
  induction l₁ generalizing l₂ with
  | nil => simp [RRSamplePushForward, -mapM]
           aesop
  | cons hd tl ih =>
  simp [RRSamplePushForward, -mapM]
  simp [RRSamplePushForward, -mapM] at ih
  apply And.intro
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]

/- RRSample assigns a zero probability of transition to a list of different length. -/
lemma RRSample_diff_lengths {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l₁ : List T) (l₂ : List Bool) (hlen : l₁.length ≠ l₂.length):
  RRSample query num den h l₁ l₂= 0 := by
  induction l₁ generalizing l₂ with
  | nil => simp [RRSample, -mapM]
           aesop
  | cons hd tl ih =>
  simp [RRSample, -mapM]
  simp [RRSample, -mapM] at ih
  apply And.intro
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]
  apply Or.inr
  intro b
  intro a
  subst a
  simp_all only [mapM, List.length_cons, ne_eq, add_left_inj, not_false_eq_true]

/- Applies the above to the PMF instantiation of RRSample. -/
lemma RRSamplePMF_diff_lengths {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (l₁ : List T) (l₂ : List Bool) (hlen : l₁.length ≠ l₂.length):
  RRSample_PMF query num den h l₁ l₂ = 0 := RRSample_diff_lengths query num den h l₁ l₂ hlen

/- Final arithmetic bound for the DP proof,
   by considering eight possible cases. -/
lemma final_bound (query : T -> Bool) (num : Nat) (den : PNat) (h : 2 * num < den) (a a' : T) (b : Bool):
  RRSingleSample query num den h a b / RRSingleSample query num den h a' b
  ≤ (den + 2 * num) / (den - 2 * num) := by
  cases b with
  | true =>
    cases hqa : query a with
    | true =>
      rw [RRSingleSample_true_true _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_true _ _ _ _ _ hqa']
                rw[ENNReal.div_self]
                {rw [@Decidable.le_iff_lt_or_eq]
                 cases hnum : num == 0 with
                   | true => simp at hnum
                             apply Or.inr
                             subst hnum
                             simp
                             rw [ENNReal.div_self]
                             norm_num
                             apply pnat_zero_imp_false
                             simp
                   | false => simp at hnum
                              apply Or.inl
                              apply quot_gt_one_rev
                              simp
                              have h1: 0 < (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [@Nat.pos_iff_ne_zero]
                                simp
                                exact hnum
                              have h2: den < den + (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [add_assoc]
                                apply ENNReal.lt_add_right
                                simp
                                norm_num
                                exact hnum

                              simp_all only [pos_add_self_iff, CanonicallyOrderedCommSemiring.mul_pos, Nat.ofNat_pos,
                                Nat.cast_pos, true_and, NNReal.ofPNat, Nonneg.mk_natCast, gt_iff_lt]
                              apply ENNReal.sub_lt_of_lt_add
                              rw [@Decidable.le_iff_eq_or_lt]
                              right
                              rw [← ENNReal.coe_two]
                              exact_mod_cast h

                              simp_all only}
                {rw [@ENNReal.div_ne_zero]
                 apply And.intro
                 simp
                 intro hd
                 apply False.elim
                 apply pnat_zero_imp_false den hd
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                }
                { simp
                  rw [@ENNReal.div_eq_top]
                  rw[Not]
                  intro b
                  rcases b with ⟨_, br⟩
                  have hh : ¬ den.val = 0 := by simp
                  simp at br
                  rw [Not] at hh
                  apply hh at br
                  exact br
                  rename_i h_1
                  simp_all only [ENNReal.add_eq_top, ENNReal.coe_ne_top, false_or, ne_eq]
                  obtain ⟨left⟩ := h_1
                  norm_cast
                }
      | false => rw [RRSingleSample_false_true _ _ _ _ _ hqa']
                -- arithmetic now
                 simp_all only [NNReal.ofPNat, Nonneg.mk_natCast]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [mul_assoc]
                 rw [mul_comm]
                 rw [mul_comm]
                 rw [← mul_assoc]
                 rw [← mul_assoc]
                 conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 simp_all only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ENNReal.coe_eq_zero, Nat.cast_eq_zero,
                   false_or]
                 apply pnat_zero_imp_false
                 simp_all only [ne_eq]
                 apply Aesop.BuiltinRules.not_intro
                 intro a_1
                 norm_cast
                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 apply pnat_zero_imp_false
    | false =>
      rw [RRSingleSample_false_true _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true =>
                 rw [RRSingleSample_true_true _ _ _ _ _ hqa']
                 simp_all only [NNReal.ofPNat, Nonneg.mk_natCast]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [mul_assoc]
                 rw [mul_comm]
                 rw [mul_comm]
                 rw [← mul_assoc]
                 rw [← mul_assoc]
                 conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 rw [← @ENNReal.div_eq_inv_mul]
                 rw  [← @ENNReal.div_eq_inv_mul]
                 apply ENNReal.div_le_div
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp
                 apply pnat_zero_imp_false
                 simp
                 rw [Not]
                 intro a
                 norm_cast
                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast
                 left
                 simp
                 apply pnat_zero_imp_false

      | false => rw [RRSingleSample_false_true _ _ _ _ _ hqa']
                 rw[ENNReal.div_self]
                 { rw [@Decidable.le_iff_lt_or_eq]
                   cases hnum : num == 0 with
                   | true => simp at hnum
                             apply Or.inr
                             subst hnum
                             simp
                             rw [ENNReal.div_self]
                             norm_num
                             apply pnat_zero_imp_false
                             simp
                   | false => simp at hnum
                              apply Or.inl
                              apply quot_gt_one_rev
                              simp
                              have h1: 0 < (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [@Nat.pos_iff_ne_zero]
                                simp
                                exact hnum
                              have h2: den < den + (2 : ENNReal) * num + 2 * num := by
                                simp
                                rw [add_assoc]
                                apply ENNReal.lt_add_right
                                simp
                                norm_num
                                exact hnum

                              simp_all only [pos_add_self_iff, CanonicallyOrderedCommSemiring.mul_pos, Nat.ofNat_pos,
                                Nat.cast_pos, true_and, NNReal.ofPNat, Nonneg.mk_natCast, gt_iff_lt]
                              apply ENNReal.sub_lt_of_lt_add
                              rw [@Decidable.le_iff_eq_or_lt]
                              right
                              rw [← ENNReal.coe_two]
                              exact_mod_cast h

                              simp_all only

                  }
                 {simp
                  apply And.intro
                  rw [Not]
                  intro b
                  rw [@Nat.lt_iff_le_and_not_ge] at h
                  rw [@tsub_eq_zero_iff_le] at b
                  rcases h with ⟨hl, hr⟩
                  rw [← ENNReal.coe_two] at b
                  have hh : den.val ≤ 2 * num := by
                    exact_mod_cast b
                  linarith

                  rw [Not]
                  intro a_1
                  norm_cast
                 }
                 { simp
                   rw [@ENNReal.div_eq_top]
                   rw[Not]
                   intro b
                   rcases b with ⟨_, br⟩
                   have hh : ¬ den.val = 0 := by simp
                   simp at br
                   rw [Not] at hh
                   apply hh at br
                   exact br
                   rename_i h_1
                   simp_all only [ENNReal.add_eq_top, ENNReal.coe_ne_top, false_or, ne_eq]
                   obtain ⟨left⟩ := h_1
                   norm_cast
                 }

  | false =>
    cases hqa : query a with
    | true =>
      rw [RRSingleSample_true_false _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                simp
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [ENNReal.mul_inv]
                simp
                rw [← mul_assoc]
                conv =>
                  enter [1,1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                rw [ENNReal.inv_mul_cancel]
                rw [one_mul]
                rw [ENNReal.inv_mul_cancel]
                rw [ENNReal.le_div_iff_mul_le]
                rw [one_mul]
                simp_all only [tsub_le_iff_right]
                rw [add_assoc]
                have hh (a b : ENNReal) : a ≤ a + b := by simp
                apply hh

                right
                simp_all only [ne_eq, add_eq_zero, ENNReal.coe_eq_zero, Nat.cast_eq_zero, mul_eq_zero,
                  OfNat.ofNat_ne_zero, false_or, not_and]
                intro a_1
                apply Aesop.BuiltinRules.not_intro
                intro a_2
                subst a_2
                simp_all only [mul_zero, PNat.pos]
                have h' : ¬ (den : Nat) = 0:= PNat.ne_zero den
                contradiction

                left
                norm_num

                simp
                rw [Not]
                intro b
                rw [@Nat.lt_iff_le_and_not_ge] at h
                rw [@tsub_eq_zero_iff_le] at b
                rcases h with ⟨hl, hr⟩
                rw [← ENNReal.coe_two] at b
                have hh : den.val ≤ 2 * num := by
                  exact_mod_cast b
                linarith

                norm_num
                simp
                apply pnat_zero_imp_false

                simp
                rw[Not]
                intro b
                norm_cast


                left
                simp
                rw[Not]
                intro b
                norm_cast

                left
                simp
                apply pnat_zero_imp_false


      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 -- arithmetic now
                 simp
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [mul_assoc]
                 rw [mul_comm]
                 rw [mul_comm]
                 rw [← mul_assoc]
                 rw [← mul_assoc]
                 conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 rw [← @ENNReal.div_eq_inv_mul]
                 rw  [← @ENNReal.div_eq_inv_mul]
                 apply ENNReal.div_le_div
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh
                 simp
                 apply pnat_zero_imp_false
                 simp
                 rw [Not]
                 intro a
                 norm_cast

                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast

                 left
                 simp
                 apply pnat_zero_imp_false

    | false =>
      rw [RRSingleSample_false_false _ _ _ _ _ hqa]
      cases hqa' : query a' with
      | true => rw [RRSingleSample_true_false _ _ _ _ _ hqa']
                -- arithmetic now
                simp
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [@ENNReal.div_eq_inv_mul]
                rw [ENNReal.mul_inv]
                simp
                rw [mul_assoc]
                rw [mul_comm]
                rw [mul_comm]
                rw [← mul_assoc]
                rw [← mul_assoc]
                conv =>
                  enter [1, 1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                  enter [1]
                rw [ENNReal.inv_mul_cancel]
                rw [one_mul]
                simp
                apply pnat_zero_imp_false

                simp
                rw [Not]
                intro b
                norm_cast

                left
                simp
                rw[Not]
                intro b
                norm_cast

                left
                simp
                apply pnat_zero_imp_false


      | false => rw [RRSingleSample_false_false _ _ _ _ _ hqa']
                 -- arithmetic now
                 simp
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [@ENNReal.div_eq_inv_mul]
                 rw [ENNReal.mul_inv]
                 simp
                 rw [← mul_assoc]
                 conv =>
                  enter [1,1]
                  rw [mul_comm]
                  rw [← mul_assoc]
                 rw [ENNReal.inv_mul_cancel]
                 rw [one_mul]
                 rw [ENNReal.inv_mul_cancel]
                 rw [ENNReal.le_div_iff_mul_le]
                 rw [one_mul]
                 simp_all only [tsub_le_iff_right]
                 rw [add_assoc]
                 have hh (a b : ENNReal) : a ≤ a + b := by simp
                 apply hh

                 right
                 simp_all only [ne_eq, add_eq_zero, ENNReal.coe_eq_zero, Nat.cast_eq_zero, mul_eq_zero,
                   OfNat.ofNat_ne_zero, false_or, not_and]
                 intro a_1
                 apply Aesop.BuiltinRules.not_intro
                 intro a_2
                 subst a_2
                 simp_all only [mul_zero, PNat.pos]
                 have h' : ¬ (den : Nat) = 0:= PNat.ne_zero den
                 contradiction

                 left
                 norm_num

                 simp
                 intro b
                 rw [Not]
                 intro
                 have h' : ¬ (den : Nat) = 0:= PNat.ne_zero den
                 contradiction

                 simp
                 rw[Not]
                 intro b
                 norm_cast

                 simp
                 apply pnat_zero_imp_false

                 simp
                 rw[Not]
                 intro b
                 norm_cast

                 left
                 simp
                 rw[Not]
                 intro b
                 norm_cast

                 left
                 simp
                 apply pnat_zero_imp_false
