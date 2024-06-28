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

/-!
# Pure DP system
-/

namespace SLang

variable { T : Type }

/--
Pure ε-DP with noise drawn from the discrete Laplace distribution.
-/
noncomputable instance PureDPSystem : DPSystem T where
  prop := PureDP
  noise := privNoisedQueryPure
--  adaptive_unif_prop := fun _ => True
--  adaptive_compose_prop := fun {U V}
--    [MeasurableSpace U] [Countable U] [DiscreteMeasurableSpace U] [Inhabited U]
--    [MeasurableSpace V] [Countable V] [DiscreteMeasurableSpace V] [Inhabited V]
--    m₁ m₂ ε₁ ε₂ ε₃ ε₄ a a_1 _ =>
--    PureDP_ComposeAdaptive' m₁ m₂ ε₁ ε₂ ε₃ ε₄ a a_1
  noise_prop := privNoisedQueryPure_DP
  compose_prop := privCompose_DP
  postprocess_prop_f := Function.Surjective
  postprocess_prop := PureDP_PostProcess

end SLang
