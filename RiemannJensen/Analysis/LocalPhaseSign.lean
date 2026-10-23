module

public import RiemannJensen.Analysis.LocalWindowGeometry
public import RiemannJensen.Analysis.CirclePhaseBridge
public import RiemannJensen.Analysis.LocalPhaseGeometry

/-!
# Sign of the normalized lower-contour phase

The normalized lower-contour phase coincides with `localPhase`, and its real part is nonpositive
on the local window `y ∈ [-1, 1]`.

## Main results

* `lowerNormalizedPhase_eq_localPhase`: The lower-contour normalized phase equals `localPhase`.
* `lowerNormalizedPhase_re_nonpos`: The real part of the normalized phase is nonpositive on
  `[-1, 1]`.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The lower-contour normalized phase agrees with `localPhase`. -/
theorem lowerNormalizedPhase_eq_localPhase
    {d : ℕ} (hd : 0 < d) (ε q y : ℝ) :
    lowerNormalizedPhase ε d q y = localPhase ε d q y := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpoint : lowerContourPoint d q (-2 * saddleAngle d q + localWidth ε d q * y) =
      saddle d q * Complex.exp (Complex.I * ((localWidth ε d q * y : ℝ) : ℂ)) := by
    rw [lowerContourPoint, saddle, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [lowerNormalizedPhase, windowPhase, lowerPhaseAngle, hpoint, lowerPhaseAngle_center,
    localPhase, effectiveN]
  push_cast
  by_cases hD : ‖saddleHessian d q‖ = 0
  · simp [hD]
  by_cases hℓ : localWidth ε d q = 0
  · simp [hℓ]
  field_simp [hdR, hdC, hD, hℓ]

/-- Every point in the normalized window corresponds to an angle in the
closed upper quarter-circle. -/
theorem normalized_beta_mem
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    saddleAngle d q - localWidth ε d q * y / 2 ∈
      Set.Icc 0 (Real.pi / 2) := by
  have hcont := localWindow_contained_lower_semicircle d hd hq hε0 hε1
  have hℓ0 : 0 ≤ localWidth ε d q := by
    rw [localWidth]
    exact mul_nonneg hε0 (min_angle_cos_pos_on_scale_window d hd hq).le
  constructor <;> linarith [hcont.1, hcont.2, mul_le_of_le_one_right hℓ0 hy.2,
    mul_le_mul_of_nonneg_left hy.1 hℓ0]

/-- The local phase point is the circle point with angle
`β = α - ℓ y / 2`. -/
theorem localPhase_point_eq_circle
    (ε : ℝ) (d : ℕ) (q y : ℝ) :
    saddle d q * Complex.exp (Complex.I *
        ((((localWidth ε d q * y : ℝ)) : ℂ))) =
      ((((saddleRadius d (saddleAngle d q)) ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I *
          (((-2 * (saddleAngle d q - localWidth ε d q * y / 2) : ℝ) : ℂ)))) := by
  rw [saddle, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The real part of the normalized phase is nonpositive throughout the local interval
`y ∈ [-1, 1]`. -/
theorem lowerNormalizedPhase_re_nonpos
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε : 0 < ε) (hε1 : ε ≤ 1) {y : ℝ}
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    (lowerNormalizedPhase ε d q y).re ≤ 0 := by
  obtain ⟨hα0, hαtop, hinv⟩ := saddle_inverse_on_scale_window d hd hq
  have hgap := phase_circle_quadratic_gap d hd hΛ ⟨hα0, hαtop.le⟩
    (normalized_beta_mem d hd hq hε.le hε1 hy)
  have hcenter :
      ((((saddleRadius d (saddleAngle d q)) ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((-2 * saddleAngle d q : ℝ) : ℂ)))) =
        saddle d q := by
    rw [saddle]
    congr 2
    push_cast
    ring
  rw [hcenter, hinv] at hgap
  have hD := (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).1
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hden : 0 < ‖saddleHessian d q‖ * localWidth ε d q ^ 2 :=
    mul_pos (by nlinarith) (pow_pos (localWidth_pos_on_scale_window d hd hq hε) 2)
  rw [lowerNormalizedPhase_eq_localPhase (by omega) ε q y, localPhase,
    localPhase_point_eq_circle, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Complex.sub_re,
    Complex.normSq_ofReal, zero_div, add_zero]
  refine div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg ?_ hden.le) (mul_nonneg hden.le hden.le)
  nlinarith [sq_nonneg (Real.cos (saddleAngle d q - localWidth ε d q * y / 2) -
    Real.cos (saddleAngle d q))]

end RiemannJensen
