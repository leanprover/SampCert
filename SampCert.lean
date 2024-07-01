/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Queries.BoundedMean.Basic
import SampCert.DifferentialPrivacy.Queries.Histogram.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.System
import SampCert.DifferentialPrivacy.Pure.System

open SLang

def combineConcentrated := @privNoisedBoundedMean_DP gaussian_zCDPSystem
def combinePure := @privNoisedBoundedMean_DP PureDPSystem
