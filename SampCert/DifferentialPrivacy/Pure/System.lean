/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Basic
import SampCert.DifferentialPrivacy.Pure.Composition
import SampCert.DifferentialPrivacy.Pure.AdaptiveComposition
import SampCert.DifferentialPrivacy.Pure.Postprocessing

namespace SLang

variable { T : Type }

noncomputable instance PureDPSystem : DPSystem T where
  prop := PureDP
  noise := privNoisedQueryPure
  noise_prop := NoisedQuery_PureDP
  compose_prop := PureDP_Compose
  adaptive_unif_prop := fun _ => True
  adaptive_compose_prop := fun {U V}
    [MeasurableSpace U] [Countable U] [DiscreteMeasurableSpace U] [Inhabited U]
    [MeasurableSpace V] [Countable V] [DiscreteMeasurableSpace V] [Inhabited V]
    m₁ m₂ ε₁ ε₂ ε₃ ε₄ a a_1 _ =>
    PureDP_ComposeAdaptive' m₁ m₂ ε₁ ε₂ ε₃ ε₄ a a_1
  postprocess_prop := PureDP_PostProcess

end SLang
