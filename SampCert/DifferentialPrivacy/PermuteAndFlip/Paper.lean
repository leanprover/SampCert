import SampCert.DifferentialPrivacy.PermuteAndFlip.Paper.Polynomials
import SampCert.DifferentialPrivacy.PermuteAndFlip.Paper.Counting
import SampCert.DifferentialPrivacy.PermuteAndFlip.Paper.ClosedForm

/-!
Reader-facing entry point for the paper-style proof ingredients.

Reading order:
- `Paper.Polynomials` defines the real-valued paper expressions.
- `Paper.Counting` proves the permutation-counting coefficients.
- `Paper.ClosedForm` connects the executable PMF to the paper closed form.

Key bridge theorem:
- `permuteAndFlipPMF_eq_ofReal_paperProb_mul_paperAlt`
-/
