import SampCert.Foundations.Distributions

open Pmf

noncomputable def UniformSample (n : PNat) : RandomM Nat := do
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n) sorry
  return r

theorem UniformSampleCorrect (n : PNat) :
  UniformSample n = uniformOfFintype (Fin n) := by
  ext x
  unfold UniformSample
  simp
  -- rw [prob_until_apply (UniformPowerOfTwoSample (2 * n)) (fun x => decide (x < PNat.val (2 * n))) sorry]
  -- simp
  -- unfold UniformPowerOfTwoSample
  -- unfold UniformPowerOfTwoSample'
  -- simp
  -- rw [tsum_fintype]
  -- rw [tsum_fintype]
  -- rw [tsum_fintype]
  -- -- conv =>
  -- --   left
  -- --   left
  -- --   right
  -- --   intro b
  -- --   simp
  -- --   rw [uniformOfFintype_apply]
  sorry

theorem UniformSample_apply (n : PNat) (x : Nat) :
  x < n →
  UniformSample n x = 1 / n := by
  intro SUPPORT
  unfold UniformSample
  simp
  sorry
