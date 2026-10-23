module

public import RiemannJensen.Analysis.SaddleGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform radial bounds for the saddle branch

For `α ∈ [0, π / 2]` and degree `d ≥ 1`, the saddle radius satisfies
`saddleRadius d α * sinRatio α ≤ 2`, and consequently `1 ≤ q r² ≤ 1 + 2π / Λ`, where
`q = saddleQ d α`, `r = saddleRadius d α` and `Λ = scaleLambda d`.

## Main results

* `saddleRadius_mul_sinRatio_le_two`: `saddleRadius d α * sinRatio α ≤ 2` on `[0, π / 2]`.
* `saddleQ_radius_sq_bounds`: `1 ≤ saddleQ d α * saddleRadius d α ^ 2 ≤ 1 + 2π / scaleLambda d`.
-/

@[expose] public section

namespace RiemannJensen

/-- The continuous extension of `α cot α` never exceeds its value at zero. -/
theorem alphaCot_le_one_of_mem {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    alphaCot α ≤ 1 := by
  rcases hα.1.eq_or_lt with hzero | hpos
  · subst α
    simp
  · exact (alphaCot_lt_one hpos hα.2).le

/-- For `α ∈ [0, π / 2]`, the sine ratio `α / sin α` is at most `2`. -/
theorem sinRatio_le_two {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) : sinRatio α ≤ 2 := by
  rcases hα.1.eq_or_lt with hzero | hpos
  · subst α
    simp
  · have hsin : 0 < Real.sin α :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos, hα.2])
    have hconst : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith [Real.pi_le_four]
    rw [sinRatio_of_ne hpos.ne', div_le_iff₀ hsin]
    linarith [Real.mul_le_sin hα.1 hα.2, mul_le_mul_of_nonneg_right hconst hα.1]

/-- The product of cosine with the sine ratio is the continuous extension of
`α cot α`, including at zero. -/
theorem cos_mul_sinRatio (α : ℝ) : Real.cos α * sinRatio α = alphaCot α := by
  by_cases hα : α = 0
  · subst α
    simp
  · rw [sinRatio_of_ne hα, alphaCot_of_ne hα]
    ring

/-- For `α ∈ [0, π / 2]`, the radius `2 / sinRatio α` is positive. -/
theorem two_div_sinRatio_pos {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    0 < 2 / sinRatio α :=
  div_pos (by norm_num) (sinRatio_pos_of_mem hα)

/-- For `d ≥ 1` and `α ∈ [0, π / 2]`, the radial equation of the saddle point is nonpositive at
the radius `2 / sinRatio α`. -/
theorem radialEquation_two_div_sinRatio_nonpos (d : ℕ) (hd : 1 ≤ d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    radialEquation (saddleRadialCoeff d α) (saddleRadialConst d α) (2 / sinRatio α) ≤ 0 := by
  have hs : 0 < sinRatio α := sinRatio_pos_of_mem hα
  have hlog : 0 ≤ Real.log (2 / sinRatio α) :=
    Real.log_nonneg ((le_div_iff₀ hs).2 (by simpa using sinRatio_le_two hα))
  have hcot : alphaCot α ≤ 1 := alphaCot_le_one_of_mem hα
  have hfrac : alphaCot α / Real.pi ≤ 1 / 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.two_le_pi]
  have hterm :
      saddleRadialCoeff d α / (2 / sinRatio α) =
        scaleLambda d * alphaCot α / Real.pi := by
    rw [saddleRadialCoeff, ← cos_mul_sinRatio α]
    field_simp [hs.ne', Real.pi_ne_zero]
  rw [radialEquation, saddleRadialConst, hterm]
  calc
    scaleLambda d * alphaCot α / Real.pi +
          (alphaCot α - scaleLambda d / 2 - 1) -
        Real.log (2 / sinRatio α) =
      scaleLambda d * (alphaCot α / Real.pi - 1 / 2) +
          (alphaCot α - 1) - Real.log (2 / sinRatio α) := by ring
    _ ≤ 0 := by
      linarith [mul_nonpos_of_nonneg_of_nonpos (scaleLambda_pos d hd).le (sub_nonpos.2 hfrac)]

/-- For `d ≥ 1` and `α ∈ [0, π / 2]`, the saddle radius satisfies
`saddleRadius d α * sinRatio α ≤ 2`. -/
theorem saddleRadius_mul_sinRatio_le_two (d : ℕ) (hd : 1 ≤ d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleRadius d α * sinRatio α ≤ 2 := by
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hr := saddleRadius_pos_and_eq d hd hαfull
  have hcandE := radialEquation_two_div_sinRatio_nonpos d hd hα
  have hrle : saddleRadius d α ≤ 2 / sinRatio α := le_of_not_gt fun hlt => by
    linarith [radialEquation_strictAntiOn (B := saddleRadialConst d α)
      (saddleRadialCoeff_nonneg d hd hαfull) (two_div_sinRatio_pos hα) hr.1 hlt]
  exact (le_div_iff₀ (sinRatio_pos_of_mem hα)).1 hrle

/-- For `d ≥ 1` and `α ∈ [0, π / 2]`,
`saddleQ d α * saddleRadius d α ^ 2 ≤ 1 + 2π / scaleLambda d`. -/
theorem saddleQ_mul_radius_sq_le (d : ℕ) (hd : 1 ≤ d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleQ d α * saddleRadius d α ^ 2 ≤ 1 + 2 * Real.pi / scaleLambda d := by
  rw [saddleQ_mul_radius_sq d hd hα]
  have hc : 0 ≤ Real.pi / scaleLambda d :=
    (div_pos Real.pi_pos (scaleLambda_pos d hd)).le
  calc
    1 + Real.pi / scaleLambda d * sinRatio α * saddleRadius d α =
        1 + Real.pi / scaleLambda d * (saddleRadius d α * sinRatio α) := by ring
    _ ≤ 1 + Real.pi / scaleLambda d * 2 := by
      gcongr
      exact saddleRadius_mul_sinRatio_le_two d hd hα
    _ = 1 + 2 * Real.pi / scaleLambda d := by ring

/-- For `d ≥ 1` and `α ∈ [0, π / 2]`,
`1 ≤ saddleQ d α * saddleRadius d α ^ 2 ≤ 1 + 2π / scaleLambda d`. -/
theorem saddleQ_radius_sq_bounds (d : ℕ) (hd : 1 ≤ d)
    {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 ≤ saddleQ d α * saddleRadius d α ^ 2 ∧
      saddleQ d α * saddleRadius d α ^ 2 ≤ 1 + 2 * Real.pi / scaleLambda d :=
  ⟨one_le_saddleQ_mul_radius_sq d hd hα, saddleQ_mul_radius_sq_le d hd hα⟩

end RiemannJensen
