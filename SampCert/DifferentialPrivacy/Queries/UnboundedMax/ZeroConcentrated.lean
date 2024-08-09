/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Properties
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMax`` zCDP

This file proves zCDP for privMaxusing the (ε^2/2)-zCDP bound.

privMax implemented using the abstract DP system, but I am not aware of how
to generalize the privacy proof to the abstract DP case.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

-- FIXME: Need stuff from the other branch, then it becomes trivial

end SLang
