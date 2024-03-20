/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Extractor.Export
import SampCert.Extractor.Align
import SampCert.Extractor.Print
import SampCert.Extractor.Inline
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import SampCert.Samplers.BernoulliNegativeExponential
import SampCert.Samplers.Laplace
import SampCert.Samplers.Gaussian

attribute [export_dafny] UniformSample
attribute [export_dafny] BernoulliSample
attribute [export_dafny] BernoulliExpNegSampleUnitLoop
attribute [export_dafny] BernoulliExpNegSampleUnitAux
attribute [export_dafny] BernoulliExpNegSampleUnit
attribute [export_dafny] BernoulliExpNegSampleGenLoop
attribute [export_dafny] BernoulliExpNegSample
attribute [export_dafny] DiscreteLaplaceSampleLoopIn1Aux
attribute [export_dafny] DiscreteLaplaceSampleLoopIn1
attribute [export_dafny] DiscreteLaplaceSampleLoopIn2Aux
attribute [export_dafny] DiscreteLaplaceSampleLoopIn2
attribute [export_dafny] DiscreteLaplaceSampleLoop
attribute [export_dafny] DiscreteLaplaceSample
attribute [export_dafny] DiscreteGaussianSampleLoop
attribute [export_dafny] DiscreteGaussianSample

#print_dafny_exports
