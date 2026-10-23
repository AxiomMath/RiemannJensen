module

public import RiemannJensen.Analysis.SaddleBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative curvature on the saddle circle

The second derivative of the real phase in the coordinate `z = cos β` contains the quotient
`(β - sin β cos β) / sin³ β`. We extend it continuously to `β = 0` by the value `2 / 3`, bound it
uniformly on `[0, π / 2]`, and deduce that the model second derivative is at most `-3` once
`Λ ≥ 24π`.

## Main definitions

* `circleCurvatureQuotient`: The quotient `(β - sin β cos β) / sin³ β`, with value `2 / 3` at `0`.
* `circleModelCurvature`: The model second derivative of the real phase on the saddle circle.

## Main results

* `circleCurvatureQuotient_bounds`: The quotient lies in `[0, 6]` on `[0, π / 2]`.
* `saddleRadius_le_two`: The saddle radius is at most `2` on `[0, π / 2]`.
* `circleModelCurvature_le_neg_three`: If `24π ≤ Λ`, the model curvature is at most `-3`.

## Implementation notes

The identification of `circleModelCurvature` with the second derivative of
`Re (phase d q (r² exp (-2 i β)))` is not asserted here.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The quotient `(β - sin β cos β) / sin³ β` of the circle curvature formula, extended by its
limit `2 / 3` at `β = 0`. -/
noncomputable def circleCurvatureQuotient (β : ℝ) : ℝ :=
  if β = 0 then 2 / 3
  else (β - Real.sin β * Real.cos β) / Real.sin β ^ 3

/-- The curvature quotient takes the value `2 / 3` at `0`. -/
@[simp] theorem circleCurvatureQuotient_zero :
    circleCurvatureQuotient 0 = 2 / 3 := by
  simp [circleCurvatureQuotient]

/-- For `β ∈ [0, π / 2]`, the numerator `β - sin β cos β` of the curvature quotient is
nonnegative. -/
theorem circleCurvatureNumerator_nonneg {β : ℝ}
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ β - Real.sin β * Real.cos β := by
  have hsin := Real.sin_le (x := 2 * β) (mul_nonneg (by norm_num) hβ.1)
  rw [Real.sin_two_mul] at hsin
  nlinarith

/-- For `0 ≤ β`, `β - sin β cos β ≤ (2 / 3) β³`. -/
theorem circleCurvatureNumerator_le {β : ℝ} (hβ : 0 ≤ β) :
    β - Real.sin β * Real.cos β ≤ (2 / 3 : ℝ) * β ^ 3 := by
  rcases hβ.eq_or_lt with rfl | hpos
  · simp
  · have hsin := Real.sin_gt_sub_cube (x := 2 * β) (mul_pos (by norm_num) hpos)
    rw [Real.sin_two_mul] at hsin
    nlinarith

/-- For `β ∈ [0, π / 2]`, `β / 2 ≤ sin β`. -/
theorem half_mul_le_sin {β : ℝ}
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    β / 2 ≤ Real.sin β := by
  refine le_trans ?_ (Real.mul_le_sin hβ.1 hβ.2)
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  nlinarith [Real.pi_le_four, hβ.1]

/-- For `β ∈ [0, π / 2]`, the curvature quotient lies in `[0, 6]`. -/
theorem circleCurvatureQuotient_bounds {β : ℝ}
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ circleCurvatureQuotient β ∧ circleCurvatureQuotient β ≤ 6 := by
  rcases hβ.1.eq_or_lt with rfl | hpos
  · norm_num
  rw [circleCurvatureQuotient, ite_eq_right hpos.ne']
  have hsin : 0 < Real.sin β ^ 3 :=
    pow_pos (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [hβ.2, Real.pi_pos])) 3
  refine ⟨div_nonneg (circleCurvatureNumerator_nonneg hβ) hsin.le, (div_le_iff₀ hsin).2 ?_⟩
  linarith [circleCurvatureNumerator_le hβ.1,
    pow_le_pow_left₀ (by positivity) (half_mul_le_sin hβ) 3]

/-- The expression `-4 q r² + (2π r / Λ) · circleCurvatureQuotient β` for the second derivative of
the real phase in the coordinate `z = cos β`, where `q = saddleQ d α` and `r = saddleRadius d α`.
-/
noncomputable def circleModelCurvature (d : ℕ) (α β : ℝ) : ℝ :=
  -4 * saddleQ d α * saddleRadius d α ^ 2 +
    (2 * Real.pi * saddleRadius d α / scaleLambda d) *
      circleCurvatureQuotient β

/-- For `α ∈ [0, π / 2]`, the saddle radius is at most `2`. -/
theorem saddleRadius_le_two (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) : saddleRadius d α ≤ 2 := by
  have hsone : 1 ≤ sinRatio α := by
    rcases hα.1.eq_or_lt with rfl | hpos
    · simp
    · exact (one_lt_sinRatio hpos hα.2).le
  have hr0 := (saddleRadius_pos_and_eq d hd
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩).1.le
  nlinarith [mul_le_mul_of_nonneg_left hsone hr0, saddleRadius_mul_sinRatio_le_two d hd hα]

/-- If `24π ≤ Λ`, then the model curvature is at most `-3` for all `α, β ∈ [0, π / 2]`. -/
theorem circleModelCurvature_le_neg_three (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d) {α β : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    circleModelCurvature d α β ≤ -3 := by
  have hquot := circleCurvatureQuotient_bounds hβ
  have hrq : saddleRadius d α * circleCurvatureQuotient β ≤ 12 := by
    nlinarith [mul_le_mul (saddleRadius_le_two d hd hα) hquot.2 hquot.1 zero_le_two]
  have hcorr :
      (2 * Real.pi * saddleRadius d α / scaleLambda d) *
          circleCurvatureQuotient β ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (scaleLambda_pos d hd)]
    nlinarith [Real.pi_pos]
  rw [circleModelCurvature]
  nlinarith [one_le_saddleQ_mul_radius_sq d hd hα]

end RiemannJensen
