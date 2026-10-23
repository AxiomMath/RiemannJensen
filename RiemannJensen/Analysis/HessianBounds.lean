module

public import RiemannJensen.Analysis.HessianFormula
public import RiemannJensen.Analysis.CircleGap
public import RiemannJensen.Analysis.SaddleInverse

/-!
# Quantitative Hessian bounds on the saddle branch

This file gives explicit two-sided bounds on the real part of the saddle Hessian: when
`4π ≤ scaleLambda d`, the real part of `saddleHessian d q` lies between `sin² α` and `2 sin² α`,
where `α` is the saddle angle.

## Main results

* `hessianCorrectionNumerator_nonneg`: `0 ≤ sin α cos α - α cos 2α` for `α ∈ [0, π/2]`.
* `hessianCorrectionNumerator_le`: `sin α cos α - α cos 2α ≤ 4 sin³ α` for `α ∈ [0, π/2]`.
* `hessianCorrectionBracket_bounds`: `0 ≤ cos α - α cos 2α / sin α ≤ 4 sin² α` for
  `α ∈ (0, π/2)`.
* `saddleHessian_eq_explicit_on_scale_window`: the saddle Hessian equals
  `explicitSaddleHessian` at the saddle radius and angle on the scale window.
* `saddleHessian_re_bounds_saddleQ`: the two-sided real-part bound at `saddleQ d α`.
* `saddleHessian_re_bounds_on_scale_window`: the two-sided real-part bound on the scale window.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The trigonometric numerator occurring in the real Hessian correction is
nonnegative throughout the saddle-angle interval. -/
theorem hessianCorrectionNumerator_nonneg {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin α * Real.cos α - α * Real.cos (2 * α) := by
  rcases hα.1.eq_or_lt with rfl | hαpos
  · simp
  have hcos0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα.2⟩
  have hcos1 : Real.cos α ≤ 1 := Real.cos_le_one α
  have hbase : α * Real.cos α ≤ Real.sin α :=
    (self_mul_cos_lt_sin hαpos hα.2).le
  rw [Real.cos_two_mul]
  by_cases hc : 0 ≤ 2 * Real.cos α ^ 2 - 1
  · have hsq : 2 * Real.cos α ^ 2 - 1 ≤ Real.cos α ^ 2 := by
      nlinarith [mul_nonneg hcos0 (sub_nonneg.mpr hcos1)]
    have hmul : α * (2 * Real.cos α ^ 2 - 1) ≤
        (α * Real.cos α) * Real.cos α := by
      nlinarith
    have := mul_le_mul_of_nonneg_right hbase hcos0
    nlinarith
  · have hc' : 2 * Real.cos α ^ 2 - 1 ≤ 0 := le_of_not_ge hc
    have hsin0 : 0 ≤ Real.sin α :=
      Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2, Real.pi_pos])
    nlinarith

/-- For `α ∈ [0, π/2]`, `sin α cos α - α cos 2α ≤ 4 sin³ α`. -/
theorem hessianCorrectionNumerator_le {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.sin α * Real.cos α - α * Real.cos (2 * α) ≤
      4 * Real.sin α ^ 3 := by
  have hnum := circleCurvatureNumerator_nonneg hα
  have hhalf := half_mul_le_sin hα
  have hsin0 : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2, Real.pi_pos])
  rw [Real.cos_two_mul]
  nlinarith [mul_nonneg hnum hsin0, mul_nonneg hα.1 (sq_nonneg (Real.sin α)),
    Real.sin_sq_add_cos_sq α]

/-- For `α ∈ (0, π/2)`, the Hessian correction bracket `cos α - α cos 2α / sin α` lies
in `[0, 4 sin² α]`. -/
theorem hessianCorrectionBracket_bounds {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Real.cos α - α * Real.cos (2 * α) / Real.sin α ∧
      Real.cos α - α * Real.cos (2 * α) / Real.sin α ≤ 4 * Real.sin α ^ 2 := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hspos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hn4 := hessianCorrectionNumerator_le hαcc
  have hbr : Real.cos α - α * Real.cos (2 * α) / Real.sin α =
      (Real.sin α * Real.cos α - α * Real.cos (2 * α)) / Real.sin α := by
    field_simp [hspos.ne']
  rw [hbr]
  refine ⟨div_nonneg (hessianCorrectionNumerator_nonneg hαcc) hspos.le, ?_⟩
  rw [div_le_iff₀ hspos]
  nlinarith

/-- For `q` in the scale window `(edgeQ d, scaleT d]`, the saddle Hessian at `q` equals
`explicitSaddleHessian` evaluated at the saddle radius and saddle angle of `q`. -/
theorem saddleHessian_eq_explicit_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    saddleHessian d q =
      explicitSaddleHessian d (saddleRadius d (saddleAngle d q))
        (saddleAngle d q) := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  simpa only [hinv] using
    saddleHessian_saddleQ d hd ⟨hα0, hαtop⟩

/-- If `4π ≤ scaleLambda d` and `α ∈ (0, π/2)`, the real part of the saddle Hessian at
`saddleQ d α` lies between `sin² α` and `2 sin² α`. -/
theorem saddleHessian_re_bounds_saddleQ
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin α ^ 2 ≤ (saddleHessian d (saddleQ d α)).re ∧
      (saddleHessian d (saddleQ d α)).re ≤ 2 * Real.sin α ^ 2 := by
  obtain ⟨hb0, hb4⟩ := hessianCorrectionBracket_bounds hα
  have hr0 : 0 ≤ saddleRadius d α :=
    (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩).1.le
  have hr2 := saddleRadius_le_two d hd ⟨hα.1.le, hα.2.le⟩
  have hΛpos := scaleLambda_pos d hd
  have hcoef0 : 0 ≤ Real.pi * saddleRadius d α / (2 * scaleLambda d) := by positivity
  have hcoef : Real.pi * saddleRadius d α / (2 * scaleLambda d) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hcorr0 := mul_nonneg hcoef0 hb0
  have hcorrle : Real.pi * saddleRadius d α / (2 * scaleLambda d) *
      (Real.cos α - α * Real.cos (2 * α) / Real.sin α) ≤ Real.sin α ^ 2 :=
    calc
      _ ≤ (Real.pi * saddleRadius d α / (2 * scaleLambda d)) *
          (4 * Real.sin α ^ 2) := mul_le_mul_of_nonneg_left hb4 hcoef0
      _ ≤ (1 / 4 : ℝ) * (4 * Real.sin α ^ 2) := by gcongr
      _ = Real.sin α ^ 2 := by ring
  rw [saddleHessian_re_saddleQ d hd hα]
  constructor <;> nlinarith

/-- If `4π ≤ scaleLambda d` and `q` lies in the scale window `(edgeQ d, scaleT d]`, the real
part of the saddle Hessian at `q` lies between `sin² α` and `2 sin² α`, where
`α = saddleAngle d q`. -/
theorem saddleHessian_re_bounds_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    Real.sin (saddleAngle d q) ^ 2 ≤ (saddleHessian d q).re ∧
      (saddleHessian d q).re ≤ 2 * Real.sin (saddleAngle d q) ^ 2 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  simpa only [hinv] using
    saddleHessian_re_bounds_saddleQ d hd hΛ ⟨hα0, hαtop⟩

end RiemannJensen
