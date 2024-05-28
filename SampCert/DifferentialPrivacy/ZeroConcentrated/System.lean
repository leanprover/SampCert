/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.Composition
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing

/-!
# zCDP System
-/

namespace SLang

variable { T : Type }

/--
Instance of a DP system for zCDP, using the discrete Gaussian as a noising mechanism.
-/
noncomputable instance zCDPSystem : DPSystem T where
  prop := zCDP
  noise := privNoisedQuery
  noise_prop := NoisedQueryzCDP
  compose_prop := compose_zCDP
  postprocess_prop := zCDPPostProcess

end SLang
