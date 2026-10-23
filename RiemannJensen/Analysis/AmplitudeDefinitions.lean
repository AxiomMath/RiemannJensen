module

public import RiemannJensen.Analysis.SaddleDefinitions
public import RiemannJensen.Analysis.GammaRemainderDefinition
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Amplitude and leading saddle contribution

The amplitude of the saddle-point integrand on a saddle circle, the principal lower-saddle
contribution built from it, and the counting interval.

## Main definitions

* `contourW`: The scaled Gamma argument on a saddle circle.
* `amplitude`: The nonexponential amplitude on the saddle circle.
* `leadingSaddle`: The principal lower-saddle contribution.
* `countingWindow`: The counting interval for constants `M` and `c₀`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set

/-- The scaled Gamma argument on a saddle circle. -/
noncomputable def contourW (d : ℕ) (q θ : ℝ) : ℂ :=
  (scaleT d * saddleRadius d (saddleAngle d q) : ℝ) *
    Complex.exp (Complex.I * (θ : ℂ) / 2)

/-- The nonexponential amplitude on the saddle circle. -/
noncomputable def amplitude (d : ℕ) (q θ : ℝ) : ℂ :=
  Complex.cpow (Real.pi / 2) (1 / 4) *
    Complex.cpow (contourW d q θ) (7 / 4) *
    riemannZeta (1 / 2 + contourW d q θ) *
    gammaRemainder (contourW d q θ)

/-- The principal lower-saddle contribution. -/
noncomputable def leadingSaddle (d : ℕ) (q : ℝ) : ℂ :=
  ((d.factorial : ℂ) / (d : ℂ) ^ d) *
    (amplitude d q (-2 * saddleAngle d q) *
      Complex.exp ((d : ℂ) * phase d q (saddle d q))) /
    Complex.sqrt (2 * Real.pi * d * saddleHessian d q)

/-- The counting interval for chosen constants `M` and `c₀`. -/
noncomputable def countingWindow (M c₀ : ℝ) (d : ℕ) : Set ℝ :=
  Set.Icc
    (edgeQ d + M * Real.sqrt (Real.log d / d))
    (c₀ * scaleT d)

end RiemannJensen
