module

public import RiemannJensen.Definitions

/-!
# Riemann's xi function

Riemann's xi function `riemannXi` is entire and satisfies the functional equation
`ξ(1 - s) = ξ(s)`; equivalently, the centered xi function `centeredXi` is entire and even. This
module also defines the power series in `z = w ^ 2` built from the Taylor coefficients of
`centeredXi`, the xi formulation of the Riemann hypothesis, and hyperbolicity of real polynomials.

## Main definitions

* `riemannF`: The power series `∑ j, γ(j) / j! * z ^ j` in the coefficients `gammaCoeff`.
* `RiemannHypothesis`: Every zero of `riemannXi` has real part `1 / 2`.
* `Hyperbolic`: Every complex root of a real polynomial is real.

## Main results

* `differentiable_riemannXi`: `riemannXi` is entire.
* `riemannXi_one_sub`: `riemannXi (1 - s) = riemannXi s`.
* `differentiable_centeredXi`: `centeredXi` is entire.
* `centeredXi_neg`: `centeredXi` is even.
-/

@[expose] public section

namespace RiemannJensen

open Polynomial

/-- Riemann's xi function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  have := differentiable_completedZeta₀
  fun_prop

/-- The functional equation `ξ(1 - s) = ξ(s)` of Riemann's xi function. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  congr 2
  ring

/-- The centered xi function is entire. -/
theorem differentiable_centeredXi : Differentiable ℂ centeredXi := by
  unfold centeredXi
  have := differentiable_riemannXi
  fun_prop

/-- The centered xi function is even. -/
@[simp]
theorem centeredXi_neg (w : ℂ) : centeredXi (-w) = centeredXi w := by
  unfold centeredXi
  rw [← riemannXi_one_sub (1 / 2 + w)]
  congr 1
  ring

/-- The power series `∑ j, γ(j) / j! * z ^ j` with the coefficients `γ = gammaCoeff`, so that
formally `centeredXi w = riemannF (w ^ 2)`. -/
noncomputable def riemannF (z : ℂ) : ℂ :=
  ∑' j : ℕ, (gammaCoeff j : ℂ) / (j.factorial : ℂ) * z ^ j

/-- `riemannF z` is the sum `∑' j, γ(j) / j! * z ^ j`. -/
theorem riemannF_apply (z : ℂ) :
    riemannF z = ∑' j : ℕ, (gammaCoeff j : ℂ) / (j.factorial : ℂ) * z ^ j := rfl

/-- The Riemann hypothesis in terms of `riemannXi`: every zero of `riemannXi` has real part
`1 / 2`. This is the xi formulation, not Mathlib's `_root_.RiemannHypothesis` for
`riemannZeta`. -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, riemannXi s = 0 → s.re = 1 / 2

/-- A real polynomial `p` is hyperbolic if every complex root of `p` is real. -/
def Hyperbolic (p : ℝ[X]) : Prop :=
  ∀ z ∈ (p.map Complex.ofRealHom).roots, z.im = 0

end RiemannJensen
