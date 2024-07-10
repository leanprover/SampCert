/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Extractor.Export
import SampCert.Extractor.Align
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Bernoulli.Code
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code
import SampCert.Samplers.Gaussian.Code

import SampCert.DifferentialPrivacy.Queries.Count.Code
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Code
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code
import SampCert.DifferentialPrivacy.Queries.Histogram.Code
import SampCert.DifferentialPrivacy.Queries.HistogramMean.Code

import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.ZeroConcentrated.System


open SLang

/-! Extractor

Attributes which trigger extraction.

The names in this file are protected: the extractor will not work if these names are changed.a

Additionally, the following names are protected:
 - ``UniformPowerOfTwoSample``
-/

-- attribute [export_dafny] UniformSample
-- attribute [export_dafny] BernoulliSample
-- attribute [export_dafny] BernoulliExpNegSampleUnitLoop
-- attribute [export_dafny] BernoulliExpNegSampleUnitAux
-- attribute [export_dafny] BernoulliExpNegSampleUnit
-- attribute [export_dafny] BernoulliExpNegSampleGenLoop
-- attribute [export_dafny] BernoulliExpNegSample
-- attribute [export_dafny] DiscreteLaplaceSampleLoopIn1Aux
-- attribute [export_dafny] DiscreteLaplaceSampleLoopIn1
-- attribute [export_dafny] DiscreteLaplaceSampleLoopIn2Aux
-- attribute [export_dafny] DiscreteLaplaceSampleLoopIn2
-- attribute [export_dafny] DiscreteLaplaceSampleLoop
-- attribute [export_dafny] DiscreteLaplaceSample
-- attribute [export_dafny] DiscreteGaussianSampleLoop
-- attribute [export_dafny] DiscreteGaussianSample


-- This one fails because of polymorphism, in the list type, and the DPSystem.
-- I don't think we want to support polymorphism in the DP system, and in this example
-- means we can't support polymorphism in the list type either (because the type of
-- DPSystem in parameterized by the list type).

attribute [export_dafny] privNoisedCount

-- To unfold these definitions, we mark them as reducible.
attribute [reducible] SLang.privNoisedCount

-- This one has concrete types only
noncomputable def privNoisedCount_nat_pure := @privNoisedCount ℕ PureDPSystem
attribute [export_dafny] privNoisedCount_nat_pure


-- attribute [export_dafny] privNoisedBoundedSum
-- attribute [export_dafny] privNoisedBoundedMean
-- attribute [export_dafny] privNoisedBinCount
-- attribute [export_dafny] privNoisedHistogramAux
-- attribute [export_dafny] privNoisedHistogram
-- attribute [export_dafny] privMaxBinAboveThreshold
-- attribute [export_dafny] privMeanHistogram
