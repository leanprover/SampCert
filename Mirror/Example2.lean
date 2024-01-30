import Mirror.Export
import Mirror.Align
import Mirror.Print
import Mirror.H2iiii
import Mirror.Inline

attribute [export_dafny] UniformSample
attribute [export_dafny] BernoulliSample
attribute [inline_RandomM] bernoulli_exp_neg_loop1
attribute [export_dafny] bernoulli_exp_neg_loop1
attribute [export_dafny] bernoulli_exp_neg_le1
--attribute [export_dafny] bernoulli_exp_neg_loop2
--attribute [export_dafny] BernoulliExpNegSample
--attribute [export_dafny] laplace_loop1
--attribute [export_dafny] laplace_loop2
--attribute [export_dafny] laplace_body
--attribute [export_dafny] DiscreteLaplaceSample
--attribute [export_dafny] gaussian_loop
--attribute [export_dafny] DiscreteGaussianSample

#print_dafny_exports
