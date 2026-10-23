module

public import RiemannJensen.Analysis.HessianNormBounds
public import RiemannJensen.Analysis.SaddleInverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Elementary bounds for the saddle action

The saddle action in the inverse `q`-coordinate on the window `(edgeQ d, scaleT d]`, its
nonnegativity, and cubic upper bounds in the saddle angle.

## Main results

* `saddleAction_eq_on_scale_window`: The closed formula for `saddleAction d q` in terms of
  `saddleAngle d q` for `q ∈ (edgeQ d, scaleT d]`.
* `saddleAction_saddleQ_nonneg`: `saddleAction d (saddleQ d α)` is nonnegative for
  `α ∈ [0, π / 2]`.
* `saddleAction_saddleQ_le_three_halves_cube`: If `24π ≤ scaleLambda d`, then
  `saddleAction d (saddleQ d α) ≤ (3 / 2) α ^ 3` for `α ∈ [0, π / 2]`.
-/

@[expose] public section

namespace RiemannJensen

/-- Exact action formula in the inverse `q`-coordinate for `q ∈ (edgeQ d, scaleT d]`. -/
theorem saddleAction_eq_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    saddleAction d q =
      2 * saddleAngle d q - Real.sin (2 * saddleAngle d q) +
        (2 * Real.pi * saddleRadius d (saddleAngle d q) / scaleLambda d) *
          (Real.sin (saddleAngle d q) -
            saddleAngle d q * Real.cos (saddleAngle d q)) := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  simpa only [hinv] using saddleAction_saddleQ d hd ⟨hα0.le, hαtop.le⟩

/-- On `[0, π / 2]`, `α cos α ≤ sin α`. -/
theorem sin_sub_self_mul_cos_nonneg {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin α - α * Real.cos α := by
  rcases hα.1.eq_or_lt with rfl | ha
  · simp
  · exact sub_nonneg.mpr (self_mul_cos_lt_sin ha hα.2).le

/-- The saddle action at `saddleQ d α` is nonnegative for `α ∈ [0, π / 2]`. -/
theorem saddleAction_saddleQ_nonneg (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ saddleAction d (saddleQ d α) := by
  have hΛ := scaleLambda_pos d hd
  have hr := (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩).1
  have hbase : 0 ≤ 2 * α - Real.sin (2 * α) :=
    sub_nonneg.mpr (Real.sin_le (by linarith [hα.1]))
  have hcorr := sin_sub_self_mul_cos_nonneg hα
  rw [saddleAction_saddleQ d hd hα]
  positivity

/-- For `0 ≤ α`, `sin α - α cos α ≤ α ^ 3 / 2`. -/
theorem sin_sub_self_mul_cos_le_cube {α : ℝ} (hα : 0 ≤ α) :
    Real.sin α - α * Real.cos α ≤ α ^ 3 / 2 := by
  have hs := Real.sin_le hα
  have hc := Real.one_sub_sq_div_two_le_cos (x := α)
  nlinarith [mul_nonneg hα (sub_nonneg.mpr hc)]

/-- For `0 ≤ α`, `2 α - sin (2 α) ≤ (4 / 3) α ^ 3`. -/
theorem two_mul_sub_sin_two_mul_le_cube {α : ℝ} (hα : 0 ≤ α) :
    2 * α - Real.sin (2 * α) ≤ (4 / 3 : ℝ) * α ^ 3 := by
  rcases hα.eq_or_lt with rfl | ha
  · norm_num
  · nlinarith [Real.sin_gt_sub_cube (x := 2 * α) (by positivity)]

/-- If `24π ≤ scaleLambda d`, then `saddleAction d (saddleQ d α) ≤ (3 / 2) α ^ 3` for
`α ∈ [0, π / 2]`. -/
theorem saddleAction_saddleQ_le_three_halves_cube
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleAction d (saddleQ d α) ≤ (3 / 2 : ℝ) * α ^ 3 := by
  have hr2 := saddleRadius_le_two d hd hα
  have hcoef : 2 * Real.pi * saddleRadius d α / scaleLambda d ≤ 1 / 6 := by
    apply (div_le_iff₀ (scaleLambda_pos d hd)).2
    nlinarith [Real.pi_pos]
  rw [saddleAction_saddleQ d hd hα]
  nlinarith [mul_le_mul hcoef (sin_sub_self_mul_cos_le_cube hα.1)
      (sin_sub_self_mul_cos_nonneg hα) (by norm_num : (0 : ℝ) ≤ 1 / 6),
    two_mul_sub_sin_two_mul_le_cube hα.1, pow_nonneg hα.1 3]

end RiemannJensen
