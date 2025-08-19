import SampCert

namespace SLang

/- We define local differential privacy. The definition is the same as
   for central DP, but the mechanisms take in a user, not a dataset, as input.
   as input. -/

open Classical

abbrev LocalMechanism (T U : Type) := T → PMF U

def Local_DP (m : LocalMechanism T U) (ε : ℝ) : Prop :=
  ∀ u₁ u₂ : T, ∀ y : U,
  m u₁ y / m u₂ y ≤ ENNReal.ofReal (Real.exp ε)
