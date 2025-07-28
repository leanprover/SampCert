import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithGeneralNeighbour
import SampCert.DifferentialPrivacy.Neighbours

namespace SLang

open SLang

/- Abstraction of SampCert definition of DP.
   ARU stands for Add-Remove-Update Neighbour
-/
def DP_withARUNeighbour (m : Mechanism T U) (ε : ℝ) : Prop :=
  DP_withGeneralNeighbour m (Neighbour) ε

/- Proof that our definitions are equivalent -/
theorem DP_withARUNeighbour_isDP (m : Mechanism T U) (ε : ℝ) :
  DP_withARUNeighbour m ε ↔ DP m ε := by simp [DP_withARUNeighbour, DP_withGeneralNeighbour, DP]

end SLang

