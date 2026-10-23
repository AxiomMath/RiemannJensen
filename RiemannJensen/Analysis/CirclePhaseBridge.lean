module

public import RiemannJensen.Analysis.CircleGapIntegration
public import RiemannJensen.Analysis.LowerBranchDeriv

/-! # Identifying the real-coordinate circle phase with the complex phase -/

@[expose] public section

namespace RiemannJensen

open Set

/-- The real-coordinate model is exactly the real part of the branch-sensitive
complex phase on the closed lower saddle semicircle. -/
theorem circleRealPhaseZ_cos_eq_phase_re
    (d : ℕ) (hd : 1 ≤ d) {α β : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    circleRealPhaseZ d α (Real.cos β) =
      (phase d (saddleQ d α)
        ((((saddleRadius d α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * β : ℝ) : ℂ))))).re := by
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hr := (saddleRadius_pos_and_eq d hd hαfull).1
  have heval := phase_sq_mul_exp_I_mul d (saddleQ d α) hr
    (show -Real.pi ≤ -2 * β by nlinarith [hβ.2])
    (show -2 * β ≤ 0 by nlinarith [hβ.1])
  have harccos : Real.arccos (Real.cos β) = β :=
    Real.arccos_cos hβ.1 (hβ.2.trans (by linarith [Real.pi_pos]))
  have hsqrt := sqrt_one_sub_cos_sq hβ
  rw [heval]
  rw [circleRealPhaseZ, circleArc, harccos, hsqrt]
  have harg : Complex.I * (((-2 * β : ℝ) : ℂ)) =
      (((-2 * β : ℝ) : ℂ)) * Complex.I := by ring
  have hhalf : ((((-2 * β : ℝ) : ℂ)) * Complex.I) / 2 =
      (((-β : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  rw [harg, hhalf]
  rw [Complex.exp_ofReal_mul_I (-2 * β), Complex.exp_ofReal_mul_I (-β)]
  have hβtwo : (2 : ℂ) * (β : ℂ) = ((2 * β : ℝ) : ℂ) := by
    push_cast
    ring
  simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Real.cos_neg, Real.sin_neg, pow_two]
  rw [hβtwo]
  simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  rw [Real.cos_two_mul]
  ring

/-- The global quadratic gap stated directly for the complex phase. -/
theorem phase_circle_quadratic_gap
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α β : ℝ} (hα : α ∈ Set.Ioc 0 (Real.pi / 2))
    (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    (3 / 2 : ℝ) * (Real.cos β - Real.cos α) ^ 2 ≤
      (phase d (saddleQ d α)
        ((((saddleRadius d α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * α : ℝ) : ℂ))))).re -
      (phase d (saddleQ d α)
        ((((saddleRadius d α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-2 * β : ℝ) : ℂ))))).re := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2⟩
  have hz : Real.cos β ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩,
      Real.cos_le_one β⟩
  have hgap := circleRealPhaseZ_quadratic_gap d hd hΛ hα hz
  rw [circleRealPhaseZ_cos_eq_phase_re d hd hαcc hβ,
    circleRealPhaseZ_cos_eq_phase_re d hd hαcc hαcc] at hgap
  exact hgap

end RiemannJensen
