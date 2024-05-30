/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Extractor.Abstract
import SampCert.Extractor.Export
import SampCert.Extractor.Align
import SampCert.Samplers.Uniform.Code
import SampCert.Samplers.Bernoulli.Code
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code
import SampCert.Samplers.Gaussian.Code

noncomputable section

open SLang


/-! Extraction using Capsid

This file instantiates a Capsid instance for SLang, and marks a list of SLang files for extraction.

The names in this file are protected: the extractor will not work if these names are changed.a

Additionally, the following names are protected:
 - ``UniformPowerOfTwoSample``
-/

-- instance : Capsid SLang where
--   capsWhile := probWhile

instance SLang_Capsid : Capsid SLang where
  capsWhile := probWhile


def testSLang : SLang Nat := (return 5) >>= (fun x => x)

-- MARKUSDE: Can't figure out how to get it to synthesize a typeclass instance
-- at export time, so I'll pass them in instead. Maybe a macro
def testCapsid := (SLang_Capsid, UniformSample)
attribute [export_dafny] testCapsid


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
