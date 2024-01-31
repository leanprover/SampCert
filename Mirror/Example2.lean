import Mirror.Export
import Mirror.Align
import Mirror.Print
import Mirror.H2iiii
import Mirror.Inline

attribute [export_dafny] UniformSample
attribute [export_dafny] BernoulliSample
attribute [inline_RandomM] BernoulliExpNegSampleUnitLoop
attribute [export_dafny] BernoulliExpNegSampleUnitLoop
attribute [export_dafny] BernoulliExpNegSampleUnit
attribute [export_dafny] BernoulliExpNegSampleGenLoop
attribute [export_dafny] BernoulliExpNegSample
--attribute [inline_RandomM] DiscreteLaplaceSampleLoopIn1
attribute [export_dafny] DiscreteLaplaceSampleLoopIn1
--attribute [inline_RandomM] DiscreteLaplaceSampleLoopIn2
attribute [export_dafny] DiscreteLaplaceSampleLoopIn2
--attribute [inline_RandomM] DiscreteLaplaceSampleLoop
attribute [export_dafny] DiscreteLaplaceSampleLoop
attribute [export_dafny] DiscreteLaplaceSample
--attribute [inline_RandomM] DiscreteGaussianSampleLoop
attribute [export_dafny] DiscreteGaussianSampleLoop
attribute [export_dafny] DiscreteGaussianSample

#print_dafny_exports
