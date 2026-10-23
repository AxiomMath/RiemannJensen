module

public import RiemannJensen.Analysis.SaddleGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact algebra for the saddle action

We compute the imaginary part of `phase` at a lower-semicircle point
`r² exp (-2 i α)` and reduce it, under the real saddle relation, to a closed formula. At the
saddle `saddleRadius d α` this gives a closed formula for `saddleAction d (saddleQ d α)`.

## Main results

* `phase_im_sq_exp_neg_two_mul_I`: the imaginary part of `phase` at `r² exp (-2 i α)`.
* `phase_im_eq_closed_action_of_saddle_relation`: the closed action formula under the real
  saddle relation.
* `saddle_real_relation_at_angle`: `saddleRadius d α` and `saddleQ d α` satisfy the real saddle
  relation.
* `saddleAction_saddleQ`: the closed formula for `saddleAction d (saddleQ d α)`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- `alphaCot α = sinRatio α * cos α` for every real `α`, including `α = 0`. -/
theorem alphaCot_eq_sinRatio_mul_cos (α : ℝ) :
    alphaCot α = sinRatio α * Real.cos α := by
  by_cases hα : α = 0
  · simp [hα]
  · simp only [alphaCot_of_ne hα, sinRatio_of_ne hα]
    ring

/-- Exact imaginary part of the phase at a lower-semicircle point
`r² exp (-2 i α)`. -/
theorem phase_im_sq_exp_neg_two_mul_I
    (d : ℕ) (q r α : ℝ) (hr : 0 < r)
    (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi / 2) :
    (phase d q
      (((r ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)))).im =
      q * r ^ 2 * Real.sin (2 * α) - Real.pi * r * Real.sin α -
        (2 * Real.pi * r / scaleLambda d) *
          (α * Real.cos α + Real.log r * Real.sin α) + 2 * α := by
  have hθlower : -Real.pi ≤ -2 * α := by linarith
  have hθupper : -2 * α ≤ 0 := by linarith
  rw [phase,
    lowerSqrt_sq_mul_exp_I_mul hr hθlower hθupper,
    lowerLog_sq_mul_exp_I_mul hr hθlower hθupper]
  have hexp_arg :
      Complex.I * ((-2 * α : ℝ) : ℂ) / 2 = ((-α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hexp_two :
      Complex.I * ((-2 * α : ℝ) : ℂ) =
        ((-2 * α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hsin_two : Real.sin (-2 * α) = -Real.sin (2 * α) := by
    rw [show -2 * α = -(2 * α) by ring, Real.sin_neg]
  rw [hexp_arg, hexp_two]
  simp only [Complex.add_im, Complex.add_re, Complex.sub_im, Complex.neg_im,
    Complex.neg_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  rw [hsin_two]
  ring

/-- Under the real saddle relation `hre`, the expression
`q r² sin 2α - π r sin α - (2π r / Λ)(α cos α + log r sin α) + 2α` equals
`2α - sin 2α + (2π r / Λ)(sin α - α cos α)`. -/
theorem saddle_action_algebra
    (Λ q r α : ℝ) (hΛ : Λ ≠ 0)
    (hre : Real.pi * r * (1 + 2 * Real.log r / Λ) =
      2 * (q * r ^ 2 + 1) * Real.cos α - 2 * Real.pi * r / Λ) :
    q * r ^ 2 * Real.sin (2 * α) - Real.pi * r * Real.sin α -
        (2 * Real.pi * r / Λ) *
          (α * Real.cos α + Real.log r * Real.sin α) + 2 * α =
      2 * α - Real.sin (2 * α) +
        (2 * Real.pi * r / Λ) *
          (Real.sin α - α * Real.cos α) := by
  rw [Real.sin_two_mul]
  field_simp [hΛ] at hre ⊢
  linear_combination -Real.sin α * hre

/-- Under the real saddle relation, the imaginary part of `phase` at `r² exp (-2 i α)` equals
`2α - sin 2α + (2π r / scaleLambda d)(sin α - α cos α)`. -/
theorem phase_im_eq_closed_action_of_saddle_relation
    (d : ℕ) (q r α : ℝ) (hr : 0 < r)
    (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi / 2)
    (hΛ : scaleLambda d ≠ 0)
    (hre : Real.pi * r * (1 + 2 * Real.log r / scaleLambda d) =
      2 * (q * r ^ 2 + 1) * Real.cos α -
        2 * Real.pi * r / scaleLambda d) :
    (phase d q
      (((r ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)))).im =
      2 * α - Real.sin (2 * α) +
        (2 * Real.pi * r / scaleLambda d) *
          (Real.sin α - α * Real.cos α) := by
  rw [phase_im_sq_exp_neg_two_mul_I d q r α hr hα0 hαpi]
  exact saddle_action_algebra (scaleLambda d) q r α hΛ hre

/-- For `α ∈ [0, π/2]`, the saddle radius `saddleRadius d α` and the parameter `saddleQ d α`
satisfy the real saddle relation. -/
theorem saddle_real_relation_at_angle
    (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.pi * saddleRadius d α *
        (1 + 2 * Real.log (saddleRadius d α) / scaleLambda d) =
      2 * (saddleQ d α * saddleRadius d α ^ 2 + 1) * Real.cos α -
        2 * Real.pi * saddleRadius d α / scaleLambda d := by
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hr := (saddleRadius_pos_and_eq d hd hαfull).1
  have hchar := saddleRadius_characterization d hd hαfull
  rw [alphaCot_eq_sinRatio_mul_cos] at hchar
  rw [saddleQ_mul_radius_sq d hd hα]
  field_simp [(scaleLambda_pos d hd).ne', hr.ne', Real.pi_ne_zero] at hchar ⊢
  nlinarith

/-- Closed formula for the action at the saddle parameterized by its angle `α ∈ [0, π/2]`. -/
theorem saddleAction_saddleQ
    (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleAction d (saddleQ d α) =
      2 * α - Real.sin (2 * α) +
        (2 * Real.pi * saddleRadius d α / scaleLambda d) *
          (Real.sin α - α * Real.cos α) := by
  have hr := (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩).1
  rw [saddleAction, saddle, saddleAngle_saddleQ d hd hα,
    show -2 * I * (α : ℂ) = I * ((-2 * α : ℝ) : ℂ) by push_cast; ring]
  exact phase_im_eq_closed_action_of_saddle_relation d (saddleQ d α) (saddleRadius d α) α hr
    hα.1 hα.2 (scaleLambda_pos d hd).ne' (saddle_real_relation_at_angle d hd hα)

end RiemannJensen
