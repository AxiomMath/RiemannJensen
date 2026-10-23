module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# The exact Gamma remainder

This module defines the exact remainder obtained by dividing $(1 - 1/(4w^2)) \Gamma(w/2 + 1/4)$
by its principal Stirling approximation $\sqrt{2\pi} (w/2)^{w/2 - 1/4} e^{-w/2}$.

## Main definitions

* `RiemannJensen.gammaRemainder`: The exact Gamma remainder as a function of `w : ℂ`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The exact remainder after extracting the principal Stirling exponential
from the Gamma factor in xi. -/
noncomputable def gammaRemainder (w : ℂ) : ℂ :=
  (1 - 1 / (4 * w ^ 2)) * Complex.Gamma (w / 2 + 1 / 4) /
    (Complex.sqrt (2 * Real.pi) *
      Complex.cpow (w / 2) (w / 2 - 1 / 4) *
      Complex.exp (-w / 2))

end RiemannJensen
