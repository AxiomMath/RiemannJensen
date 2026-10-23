module

public import RiemannJensen.Analysis.AmplitudeFactorization
public import RiemannJensen.Analysis.GammaLog
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Nonvanishing of the Gamma remainder on the saddle contour

The exact Gamma remainder `gammaRemainder` factors as `gammaPolarCorrection` times
`Complex.Gamma (w / 2 + 1 / 4)` divided by `gammaMainDenominator`. This file shows that it does
not vanish in the right half-plane outside the disc of radius `1 / 2`, and hence at the points
`contourW d q θ`, `θ ∈ (-π, π)`, of the saddle circle.

## Main results

* `gammaRemainder_ne_zero_of_re_pos`: `gammaRemainder w ≠ 0` when `0 < w.re` and `1 / 2 < ‖w‖`.
* `norm_contourW`: `‖contourW d q θ‖` equals the radius `scaleT d * saddleRadius d _`.
* `gammaRemainder_contourW_ne_zero_of_radius`: `gammaRemainder` does not vanish at
  `contourW d q θ` for `θ ∈ (-π, π)` when the saddle radius exceeds `1 / 2`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- `gammaRemainder w` is nonzero for `w` in the right half-plane with `1 / 2 < ‖w‖`. -/
theorem gammaRemainder_ne_zero_of_re_pos {w : ℂ} (hre : 0 < w.re) (hnorm : 1 / 2 < ‖w‖) :
    gammaRemainder w ≠ 0 := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at hre
  have harg : 0 < (w / 2 + 1 / 4).re := by
    norm_num [div_re]
    linarith
  exact div_ne_zero
    (mul_ne_zero (gammaPolarCorrection_ne_zero hnorm) (Complex.Gamma_ne_zero_of_re_pos harg))
    (gammaMainDenominator_ne_zero hw)

/-- For `0 < R` and `θ ∈ (-π, π)`, the point `R * exp (I * θ / 2)` has positive real part. -/
theorem mul_exp_I_half_re_pos {R θ : ℝ} (hR : 0 < R)
    (hθ_lower : -Real.pi < θ) (hθ_upper : θ < Real.pi) :
    0 < (((R : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)).re) := by
  norm_num [Complex.exp_re, mul_re, div_re]
  exact mul_pos hR (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

/-- For `θ ∈ (-π, π)` and positive radius, the saddle-circle point `contourW d q θ` has positive
real part. -/
theorem contourW_re_pos (d : ℕ) (q θ : ℝ)
    (hR : 0 < scaleT d * saddleRadius d (saddleAngle d q))
    (hθ_lower : -Real.pi < θ) (hθ_upper : θ < Real.pi) :
    0 < (contourW d q θ).re := by
  unfold contourW
  exact mul_exp_I_half_re_pos hR hθ_lower hθ_upper

/-- The norm of `contourW d q θ` is the (nonnegative) radius
`scaleT d * saddleRadius d (saddleAngle d q)`, independent of `θ`. -/
theorem norm_contourW (d : ℕ) (q θ : ℝ)
    (hR : 0 ≤ scaleT d * saddleRadius d (saddleAngle d q)) :
    ‖contourW d q θ‖ = scaleT d * saddleRadius d (saddleAngle d q) := by
  unfold contourW
  rw [norm_mul, norm_real, Real.norm_of_nonneg hR, Complex.norm_exp]
  norm_num [div_re, mul_re]

/-- `gammaRemainder` does not vanish at `contourW d q θ` for `θ ∈ (-π, π)` when the radius is
positive and `1 / 2 < ‖contourW d q θ‖`. -/
theorem gammaRemainder_contourW_ne_zero (d : ℕ) (q θ : ℝ)
    (hR : 0 < scaleT d * saddleRadius d (saddleAngle d q))
    (hθ_lower : -Real.pi < θ) (hθ_upper : θ < Real.pi)
    (hnorm : 1 / 2 < ‖contourW d q θ‖) :
    gammaRemainder (contourW d q θ) ≠ 0 :=
  gammaRemainder_ne_zero_of_re_pos
    (contourW_re_pos d q θ hR hθ_lower hθ_upper) hnorm

/-- `gammaRemainder` does not vanish at `contourW d q θ` for `θ ∈ (-π, π)` when the saddle radius
exceeds `1 / 2`. -/
theorem gammaRemainder_contourW_ne_zero_of_radius (d : ℕ) (q θ : ℝ)
    (hR : 1 / 2 < scaleT d * saddleRadius d (saddleAngle d q))
    (hθ_lower : -Real.pi < θ) (hθ_upper : θ < Real.pi) :
    gammaRemainder (contourW d q θ) ≠ 0 :=
  gammaRemainder_contourW_ne_zero d q θ (by linarith) hθ_lower hθ_upper
    (by rwa [norm_contourW d q θ (by linarith)])

end RiemannJensen
