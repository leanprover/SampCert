import SampCert
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.DPwithGeneralNeighbour
import SampCert.DifferentialPrivacy.Pure.Local.LocalDP.UpdateNeighbour

open SLang
open Classical

namespace SLang

def DP_withUpdateNeighbour (m : Mechanism T U) (ε : ℝ) : Prop :=
 DP_withGeneralNeighbour m (UpdateNeighbour) ε

end SLang
