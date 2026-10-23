module

public import RiemannJensen.Analysis.HessianBounds

/-!
# Normalized local saddle phase

The angular displacement from the saddle point is `localWidth ε d q * y`, and the phase
difference is divided by `‖saddleHessian d q‖ * localWidth ε d q ^ 2`. With this normalization
the quadratic Taylor coefficient has unit norm.

## Main definitions

* `localPhase`: The phase difference at angular displacement `localWidth ε d q * y` from the
  saddle point, divided by `‖saddleHessian d q‖ * localWidth ε d q ^ 2`.
-/

@[expose] public section

namespace RiemannJensen

/-- The phase on the local angular scale, normalized by its quadratic size. -/
noncomputable def localPhase (ε : ℝ) (d : ℕ) (q y : ℝ) : ℂ :=
  let ℓ := localWidth ε d q
  (phase d q (saddle d q * Complex.exp (Complex.I * ((ℓ * y : ℝ) : ℂ))) -
    phase d q (saddle d q)) / ((‖saddleHessian d q‖ * ℓ ^ 2 : ℝ) : ℂ)

/-- The normalized local phase vanishes at the saddle point `y = 0`. -/
@[simp] theorem localPhase_zero (ε : ℝ) (d : ℕ) (q : ℝ) :
    localPhase ε d q 0 = 0 := by
  simp [localPhase]

end RiemannJensen
