/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Mechanism.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Composition.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Postprocessing.Basic

namespace SLang

variable { T U V : Type }
variable [MeasurableSpace U]
variable [Countable U]
variable [DiscreteMeasurableSpace U]
variable [Inhabited U]
variable [MeasurableSpace V]
variable [Countable V]
variable [DiscreteMeasurableSpace V]
variable [Inhabited V]

noncomputable instance : @DPSystem T U V where
  prop := zCDP
  noise := NoisedQuery
  compose := Compose
  postprocess := PostProcess
  noise_prop := NoisedQueryzCDP
  compose_prop := zCDPCompose
  postprocess_prop := zCDPPostProcess

end SLang
