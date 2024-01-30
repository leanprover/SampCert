import Mirror.H2
import Mirror.Trial

open Classical
open MeasureTheory MeasurableSpace Measure

def uniformP2 (k : Nat) : Hurd Nat :=
  if k = 0 then H.pure 0
  else do
    let flip ← Coin
    let v ← uniformP2 (k - 1)
    H.pure (v + if flip then 2 ^ (k - 1) else 0)

theorem uniformP2_indep (k : Nat) : strongly_independent (uniformP2 k) :=
  by
    induction k
    . unfold uniformP2
      simp
    . unfold uniformP2
      rename_i n n_ih
      simp
      apply Indep2
      apply Indep3
      introv
      apply Indep2
      assumption
      introv
      simp

theorem uniformP2_correct (k : Nat) (n : Nat) (_ : 0 ≤ n ∧ n < 2 ^ k) :
  Prob.volume { s : BitStream | Prod.fst (uniformP2 k s) = n } = 1 / 2 ^ k :=
  by
    sorry
    -- revert n
    -- induction k
    -- . intro n H
    --   simp at H
    --   subst H
    --   simp
    --   unfold μ
    --   rw [ofMeasurable_apply]
    --   unfold uniformP2
    --   simp
    --   sorry
    --   sorry -- MeasurableSet
    -- . rename_i k iH
    --   intro n DOM
    --   have HCase : n < 2 ^ k ∨ exists m : Nat, m < 2 ^ k ∧ n = 2 ^ k + m := sorry
    --   cases HCase
    --   . rename_i CONS
    --     have RES := iH n
    --     simp at RES
    --     have RES2 := RES CONS
    --     sorry -- probability to be in lower range is 1/2
    --     -- Coin must be independent from the lower bits
    --   . rename_i CONS
    --     cases CONS
    --     rename_i m CONS2
    --     cases CONS2
    --     rename_i left right
    --     have RES := iH m
    --     simp at RES
    --     have RES2 := RES left
    --     sorry

@[simp]
noncomputable def UniformDist (k : Nat) : Measure Nat := Push (uniformP2 k)

theorem correct (k : Nat) (n : Nat) (_ : 0 ≤ n ∧ n < 2 ^ k) : UniformDist k { m : Nat | m = n } = 1 / 2 ^ k := sorry
