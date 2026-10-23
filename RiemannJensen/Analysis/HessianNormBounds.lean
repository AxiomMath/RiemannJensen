module

public import RiemannJensen.Analysis.HessianBounds
public import Mathlib.Analysis.Complex.Norm

/-!
# Uniform norm bounds for the saddle Hessian

For `α ∈ (0, π/2)` and `24π ≤ scaleLambda d`, the saddle Hessian at `saddleQ d α` has norm
between `(3/8) sin α` and `4 sin α`. The imaginary part of the Hessian is expressed with the
logarithm of the saddle radius eliminated by the real saddle equation.

## Main results

* `saddleHessian_im_rearranged`: the imaginary part of the Hessian with `log r` eliminated.
* `abs_saddleHessian_im_le_two_sin`: the imaginary part has absolute value at most `2 sin α`.
* `saddleHessian_norm_bounds_saddleQ`: `(3/8) sin α ≤ ‖saddleHessian d (saddleQ d α)‖ ≤ 4 sin α`.
* `saddleHessian_norm_bounds_on_scale_window`: the same bounds in the coordinate `q` on
  `(edgeQ d, scaleT d]`, with `α = saddleAngle d q`.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- Imaginary Hessian formula with the logarithm eliminated by the real
saddle equation. -/
theorem saddleHessian_im_rearranged
    (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (saddleHessian d (saddleQ d α)).im =
      (saddleQ d α * saddleRadius d α ^ 2 + 1) / 2 *
          Real.sin α * Real.cos α +
        (Real.pi * saddleRadius d α / (2 * scaleLambda d)) *
          (α * Real.cos α - Real.sin α) := by
  have hre := saddle_real_relation_at_angle d hd ⟨hα.1.le, hα.2.le⟩
  have hr :=
    (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩).1
  have hΛ := (scaleLambda_pos d hd).ne'
  have hA :
      1 + 2 * Real.log (saddleRadius d α) / scaleLambda d =
          2 * (saddleQ d α * saddleRadius d α ^ 2 + 1) * Real.cos α /
            (Real.pi * saddleRadius d α) -
          2 / scaleLambda d := by
    field_simp [hΛ, hr.ne', Real.pi_ne_zero] at hre ⊢
    nlinarith
  rw [saddleHessian_im_saddleQ d hd hα, hA]
  field_simp [hΛ, hr.ne', Real.pi_ne_zero]
  ring

/-- The correction term of `saddleHessian_im_rearranged` is at most `sin α / 8` in absolute
value. -/
theorem abs_saddleHessian_im_correction_le
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Real.pi * saddleRadius d α / (2 * scaleLambda d) * (α * Real.cos α - Real.sin α)|
      ≤ (1 / 8 : ℝ) * Real.sin α := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  have ha : α ≤ 2 * Real.sin α := by linarith [half_mul_le_sin hαcc]
  have hr0 : 0 ≤ saddleRadius d α :=
    (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩).1.le
  have hr2 := saddleRadius_le_two d hd hαcc
  have hΛpos := scaleLambda_pos d hd
  have hcoef : Real.pi * saddleRadius d α / (2 * scaleLambda d) ≤ 1 / 24 := by
    apply (div_le_iff₀ (show 0 < 2 * scaleLambda d by positivity)).2
    nlinarith [Real.pi_pos]
  have hcoef0 : 0 ≤ Real.pi * saddleRadius d α / (2 * scaleLambda d) := by positivity
  have hinner : |α * Real.cos α - Real.sin α| ≤ 3 * Real.sin α := by
    rw [abs_le]
    constructor <;>
      nlinarith [mul_nonneg hα.1.le hc0, mul_le_mul_of_nonneg_left (Real.cos_le_one α) hα.1.le]
  rw [abs_mul, abs_of_nonneg hcoef0]
  linarith [mul_le_mul_of_nonneg_left hinner hcoef0,
    mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℝ) ≤ 3 * Real.sin α)]

/-- The imaginary part has absolute value at most twice `sin α`. -/
theorem abs_saddleHessian_im_le_two_sin
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    |(saddleHessian d (saddleQ d α)).im| ≤ 2 * Real.sin α := by
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  have hqr := saddleQ_radius_sq_bounds d hd ⟨hα.1.le, hα.2.le⟩
  have hqr2 : saddleQ d α * saddleRadius d α ^ 2 ≤ 2 := by
    linarith [(div_le_one (scaleLambda_pos d hd)).2
      (by linarith [Real.pi_pos] : 2 * Real.pi ≤ scaleLambda d)]
  have hA0 : 0 ≤ (saddleQ d α * saddleRadius d α ^ 2 + 1) / 2 * Real.sin α * Real.cos α :=
    mul_nonneg (mul_nonneg (by linarith [hqr.1]) hs.le) hc0
  have hAle : (saddleQ d α * saddleRadius d α ^ 2 + 1) / 2 * Real.sin α * Real.cos α ≤
      (3 / 2 : ℝ) * Real.sin α := by
    nlinarith [mul_nonneg hs.le hc0, mul_le_mul_of_nonneg_left (Real.cos_le_one α) hs.le]
  rw [saddleHessian_im_rearranged d hd hα]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hA0]
  linarith [abs_saddleHessian_im_correction_le d hd hΛ hα]

/-- Lower norm bound on the angle-parameterized branch. -/
theorem three_eighths_sin_le_norm_saddleHessian_saddleQ
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (3 / 8 : ℝ) * Real.sin α ≤ ‖saddleHessian d (saddleQ d α)‖ := by
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  by_cases hsmall : Real.sin α < 1 / 2
  · have htrig := Real.sin_sq_add_cos_sq α
    have hc : 1 / 2 ≤ Real.cos α := by nlinarith [sq_nonneg (Real.cos α)]
    have hqr := saddleQ_radius_sq_bounds d hd ⟨hα.1.le, hα.2.le⟩
    have hcorr := (abs_le.1 (abs_saddleHessian_im_correction_le d hd hΛ hα)).1
    have hmain : (1 / 2 : ℝ) * Real.sin α ≤
        (saddleQ d α * saddleRadius d α ^ 2 + 1) / 2 * Real.sin α * Real.cos α := by
      nlinarith [mul_nonneg hs.le hc0]
    refine le_trans ?_ (Complex.im_le_norm _)
    rw [saddleHessian_im_rearranged d hd hα]
    linarith
  · have hre := saddleHessian_re_bounds_saddleQ d hd
      (by linarith [Real.pi_pos] : 4 * Real.pi ≤ scaleLambda d) hα
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr (le_of_not_gt hsmall)),
      Complex.re_le_norm (saddleHessian d (saddleQ d α))]

/-- Upper norm bound on the angle-parameterized branch. -/
theorem norm_saddleHessian_saddleQ_le_four_sin
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖saddleHessian d (saddleQ d α)‖ ≤ 4 * Real.sin α := by
  have hs : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hre := saddleHessian_re_bounds_saddleQ d hd
    (by linarith [Real.pi_pos] : 4 * Real.pi ≤ scaleLambda d) hα
  have hresin : (saddleHessian d (saddleQ d α)).re ≤ 2 * Real.sin α := by
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr (Real.sin_le_one α))]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [abs_of_nonneg ((sq_nonneg _).trans hre.1)]
  linarith [abs_saddleHessian_im_le_two_sin d hd hΛ hα]

/-- Explicit norm comparison on the angle-parameterized branch. -/
theorem saddleHessian_norm_bounds_saddleQ
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (3 / 8 : ℝ) * Real.sin α ≤ ‖saddleHessian d (saddleQ d α)‖ ∧
      ‖saddleHessian d (saddleQ d α)‖ ≤ 4 * Real.sin α :=
  ⟨three_eighths_sin_le_norm_saddleHessian_saddleQ d hd hΛ hα,
    norm_saddleHessian_saddleQ_le_four_sin d hd hΛ hα⟩

/-- Norm comparison in the inverse `q`-coordinate on the scale window. -/
theorem saddleHessian_norm_bounds_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    (3 / 8 : ℝ) * Real.sin (saddleAngle d q) ≤ ‖saddleHessian d q‖ ∧
      ‖saddleHessian d q‖ ≤ 4 * Real.sin (saddleAngle d q) := by
  obtain ⟨hα0, hαtop, hinv⟩ := saddle_inverse_on_scale_window d hd hq
  simpa only [hinv] using
    saddleHessian_norm_bounds_saddleQ d hd hΛ ⟨hα0, hαtop⟩

end RiemannJensen
