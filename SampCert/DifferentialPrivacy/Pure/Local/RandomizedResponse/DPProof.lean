import Mathlib.Probability.ProbabilityMassFunction.Basic
import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.RandomizedResponse.Definitions
import SampCert.DifferentialPrivacy.Pure.Local.Normalization
import SampCert.Samplers.Bernoulli.Properties

lemma temp {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) :
  (1/2 + num/den) / (1/2 - num/den) = (1 + (2 * num)/den) / (1 - (2*num) / den) := by
  have hden : den ≠ (0 : ℕ+) := by exact PNat.ne_zero den



lemma final_step {T : Type} (query: T -> Bool) (num : Nat) (den : PNat) (h: 2 * num < den) (l : List T) :
  (1/2 + num/den) / (1/2 - num/den) ≤ Real.exp (Real.log ((1/2 + num/den) / (1/2 - num/den))) := by
  rw [Real.exp_log]

  apply le_of_eq
