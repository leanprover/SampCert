/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Basic
import SampCert.DifferentialPrivacy.Pure.Composition
import SampCert.DifferentialPrivacy.Pure.Postprocessing

namespace SLang

variable { T : Type }

noncomputable instance PureDPSystem : DPSystem T where
  prop := PureDP
  noise := privNoisedQueryPure
  noise_prop := NoisedQuery_PureDP
  compose_prop := PureDP_Compose
  postprocess_prop := PureDP_PostProcess

end SLang
