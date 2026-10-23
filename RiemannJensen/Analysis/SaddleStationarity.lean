module

public import RiemannJensen.Analysis.HessianFormula
public import RiemannJensen.Analysis.SaddleInverse

/-! # Complex stationarity of the recovered saddle -/

@[expose] public section

namespace RiemannJensen

open scoped Topology

/-- In the open lower half-plane the branch phase has the expected complex first derivative. -/
theorem hasDerivAt_phase_of_im_neg (d : ℕ) (q : ℝ) {u : ℂ} (hu : u.im < 0) :
    HasDerivAt (phase d q) (analyticPhaseDeriv d q u) u := by
  have heq : phase d q =ᶠ[𝓝 u] analyticPhase d q := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hu]
      with z hz
    exact phase_eq_analyticPhase_of_im_neg d q hz
  exact (hasDerivAt_analyticPhase (Complex.mem_slitPlane_iff.mpr (Or.inr hu.ne))
    ).congr_of_eventuallyEq heq

/-- The point `r ^ 2 * exp (-2 i α)` lies in the open lower half-plane for `0 < α < π / 2`. -/
theorem im_ofReal_sq_mul_exp_I_mul_neg_two_mul_neg {r α : ℝ} (hr : 0 < r)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))).im < 0 := by
  rw [mul_comm Complex.I, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    show -2 * α = -(2 * α) by ring, Real.sin_neg]
  have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * α) (by linarith) (by linarith)
  nlinarith [sq_pos_of_pos hr]

/-- The holomorphic derivative vanishes at `r ^ 2 * exp (-2 i α)` whenever `r`, `α` and `Q`
satisfy the two real saddle relations. -/
theorem analyticPhaseDeriv_ofReal_sq_mul_exp_eq_zero {d : ℕ} {Q r α : ℝ}
    (hΛ : scaleLambda d ≠ 0) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < Real.pi / 2)
    (hq : Q * r ^ 2 = 1 + Real.pi / scaleLambda d * (α / Real.sin α) * r)
    (hre : Real.pi * r * (1 + 2 * Real.log r / scaleLambda d) =
      2 * (Q * r ^ 2 + 1) * Real.cos α - 2 * Real.pi * r / scaleLambda d) :
    analyticPhaseDeriv d Q
      (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) = 0 := by
  set u : ℂ := ((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))
  have hu0 : u ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hr.ne')) (Complex.exp_ne_zero _)
  have huim : u.im < 0 := im_ofReal_sq_mul_exp_I_mul_neg_two_mul_neg hr hα0 hα1
  have hs : analyticLowerSqrt u =
      (r : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ) / 2) := by
    rw [analyticLowerSqrt, ← sqrt_eq_exp hu0, ← lowerSqrt_eq_sqrt_of_im_neg huim]
    exact lowerSqrt_sq_mul_exp_I_mul hr (by linarith [Real.pi_pos]) (by linarith)
  have hl : Complex.log u =
      ((2 * Real.log r : ℝ) : ℂ) + Complex.I * ((-2 * α : ℝ) : ℂ) := by
    rw [← lowerLog_eq_log_of_im_neg huim]
    exact lowerLog_sq_mul_exp_I_mul hr (by linarith) (by linarith)
  rw [analyticPhaseDeriv, hs, hl]
  field_simp [hu0, hΛ]
  dsimp [u]
  rw [show Complex.I * (((-(2 * α)) : ℝ) : ℂ) / 2 = ((-α : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    show Complex.I * ((-2 * α : ℝ) : ℂ) = ((-2 * α : ℝ) : ℂ) * Complex.I by ring]
  have he1 : Complex.exp (((-α : ℝ) : ℂ) * Complex.I) =
      ((Real.cos α : ℝ) : ℂ) - ((Real.sin α : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I (-α), Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have he2 : Complex.exp (((-2 * α : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (2 * α) : ℝ) : ℂ) - ((Real.sin (2 * α) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I (-2 * α), show -2 * α = -(2 * α) by ring, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  rw [he1, he2]
  apply Complex.ext
  all_goals
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    norm_num
    simp only [Real.cos_two_mul, Real.sin_two_mul]
    field_simp [hr.ne', hΛ, Real.pi_ne_zero,
      (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])).ne'] at hq hre ⊢
  · linear_combination
      Real.cos α * hre + 2 * Real.sin α * hq +
        (2 * scaleLambda d * (1 - r ^ 2 * Q)) * (Real.sin_sq_add_cos_sq α)
  · linear_combination -Real.sin α * hre + 2 * Real.cos α * hq

/-- The holomorphic derivative vanishes at the saddle parameterized by an open angle. -/
theorem analyticPhaseDeriv_saddleQ_eq_zero (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    analyticPhaseDeriv d (saddleQ d α) (saddle d (saddleQ d α)) = 0 := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hq := saddleQ_mul_radius_sq d hd hαcc
  rw [sinRatio_of_ne hα.1.ne'] at hq
  rw [saddle, saddleAngle_saddleQ d hd hαcc,
    show -2 * Complex.I * (α : ℂ) = Complex.I * ((-2 * α : ℝ) : ℂ) by push_cast; ring]
  exact analyticPhaseDeriv_ofReal_sq_mul_exp_eq_zero (scaleLambda_pos d hd).ne'
    (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩).1 hα.1 hα.2 hq
    (saddle_real_relation_at_angle d hd hαcc)

/-- The recovered saddle is a stationary point of the complex phase. -/
theorem deriv_phase_saddle_eq_zero (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    deriv (phase d q) (saddle d q) = 0 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hr := (saddleRadius_pos_and_eq d hd ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩).1
  have huim : (saddle d q).im < 0 := by
    rw [saddle, show (-2 : ℂ) * Complex.I * (saddleAngle d q : ℂ) =
      Complex.I * ((-2 * saddleAngle d q : ℝ) : ℂ) by push_cast; ring]
    exact im_ofReal_sq_mul_exp_I_mul_neg_two_mul_neg hr hα0 hαtop
  rw [(hasDerivAt_phase_of_im_neg d q huim).deriv, ← hinv]
  exact analyticPhaseDeriv_saddleQ_eq_zero d hd ⟨hα0, hαtop⟩

end RiemannJensen
