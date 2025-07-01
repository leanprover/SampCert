import SampCert

lemma real_to_ennreal_eq (a b : Real): a = b -> ENNReal.ofReal a = ENNReal.ofReal b := by
  intro h
  exact congrArg ENNReal.ofReal h

#check ENNReal.ofReal_lt_ofReal_iff_of_nonneg
#check ENNReal.ofReal_le_ofReal_iff
#check ENNReal.mul_ne_top
#check ENNReal.add_ne_top


lemma div_not_top (a b : ENNReal) (h0: a ≠ ⊤) (h1: b ≠ 0): a/b ≠ ⊤ := by
    rw [@ENNReal.div_eq_inv_mul]
    apply ENNReal.mul_ne_top
    {apply ENNReal.inv_ne_top.mpr h1}
    {exact h0}

lemma arith_0 (a : ENNReal) (h0 : a ≠ ⊤) (h1: a < 1) : 1 - a + a = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  have h2: (1 - a + a).toReal = 1 - a.toReal + a.toReal := by
    rw [@tsub_add_eq_max]
    rw[max_eq_left_of_lt h1]
    rw [ENNReal.one_toReal]
    ring
  rw[h2]
  ring

lemma arith_1 (num : Nat) (den : PNat) (h : 2 * num < den):
  1 - ((2 : ENNReal) * num + den) / (2 * den) + (2 * num + den) / (2 * den) = 1 :=
  by
    apply arith_0
    apply div_not_top
    {
      simp
      apply ENNReal.mul_ne_top
      simp
      simp
    }
    {
      simp
      exact Nat.not_eq_zero_of_lt h
    }
    { refine ENNReal.div_lt_of_lt_mul' ?h1.h
      aesop
      have h1 : ENNReal.ofReal (2 * num) < den := by
        refine (ENNReal.ofReal_lt_iff_lt_toReal ?ha ?hb).mpr ?_
        simp
        simp
        simp
        sorry
    }
