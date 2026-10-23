module

public import RiemannJensen.Analysis.CauchyRepresentation
public import RiemannJensen.Analysis.TaylorBridge

/-!
# Closed Cauchy representation for the Riemann Jensen polynomial

The rescaled Jensen polynomial of degree `d` attached to `riemannF` is expressed as a contour
integral of `cauchyNumerator` over a circle about the origin.

## Main results

* `cauchy_representation_riemannF`: For `1 ≤ d`, `ρ > 0` and `gammaCoeff d ≠ 0`, the value of
  `rescaledJensen d` at `x` equals `d! / (2πi d^d)` times the integral of
  `cauchyNumerator d x u / u ^ (d + 1)` over the circle of radius `ρ`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- For `1 ≤ d`, `ρ > 0` and `gammaCoeff d ≠ 0`, the value of `rescaledJensen d` at `x` equals
`d! / (2πi d^d)` times the integral of `cauchyNumerator d x u / u ^ (d + 1)` over the circle of
radius `ρ` about the origin. -/
theorem cauchy_representation_riemannF
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hγ : gammaCoeff d ≠ 0) :
    (↑((rescaledJensen d).eval x) : ℂ) =
      ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ), cauchyNumerator d x u / u ^ (d + 1)) :=
  cauchy_representation_of_riemannF_jet d hd x ρ hρ hγ
    differentiable_riemannF fun j _ => iteratedDeriv_riemannF_zero j

end RiemannJensen
