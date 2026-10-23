module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# The lower closed logarithm and square-root branches

The usual principal argument takes the value `π` on the negative real axis.
For the lower semicircular contours in the saddle-point argument, the endpoint
must instead be approached with argument `-π`.  This file makes that endpoint
convention explicit and evaluates the resulting logarithm and square root on
the entire closed lower semicircle, including its left endpoint.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The principal argument, with its value on the negative real axis changed
from `π` to `-π`. -/
noncomputable def lowerArg (u : ℂ) : ℝ :=
  if Complex.arg u = Real.pi then -Real.pi else Complex.arg u

/-- The logarithm determined by `lowerArg`.  As in Mathlib's principal
logarithm, this is total; its intended analytic use is away from zero. -/
noncomputable def lowerLog (u : ℂ) : ℂ :=
  (Real.log ‖u‖ : ℂ) + Complex.I * (lowerArg u : ℂ)

/-- The square root determined by `lowerArg`.  Its value on the negative real
axis is the lower, rather than the principal upper, square root. -/
noncomputable def lowerSqrt (u : ℂ) : ℂ :=
  (Real.sqrt ‖u‖ : ℂ) *
    Complex.exp (Complex.I * (lowerArg u : ℂ) / 2)

private lemma arg_exp_I_mul_of_neg_pi_lt {θ : ℝ}
    (hθ_lower : -Real.pi < θ) (hθ_upper : θ ≤ Real.pi) :
    Complex.arg (Complex.exp (Complex.I * (θ : ℂ))) = θ := by
  have hlog : Complex.log (Complex.exp (Complex.I * (θ : ℂ))) =
      Complex.I * (θ : ℂ) := by
    apply Complex.log_exp
    · simpa using hθ_lower
    · simpa using hθ_upper
  have him := congrArg Complex.im hlog
  simpa [Complex.log_im] using him

/-- On the closed lower unit semicircle the lower argument is the parameter,
including at the exceptional endpoint `θ = -π`. -/
theorem lowerArg_exp_I_mul {θ : ℝ}
    (hθ_lower : -Real.pi ≤ θ) (hθ_upper : θ ≤ 0) :
    lowerArg (Complex.exp (Complex.I * (θ : ℂ))) = θ := by
  by_cases hendpoint : θ = -Real.pi
  · subst θ
    rw [show Complex.I * ((-Real.pi : ℝ) : ℂ) =
        -((Real.pi : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_neg_pi_mul_I]
    simp [lowerArg, Complex.arg_neg_one]
  · have hθ_strict : -Real.pi < θ :=
      lt_of_le_of_ne hθ_lower (Ne.symm hendpoint)
    have hθ_pi : θ ≤ Real.pi := hθ_upper.trans (le_of_lt Real.pi_pos)
    have harg := arg_exp_I_mul_of_neg_pi_lt hθ_strict hθ_pi
    rw [lowerArg, harg]
    split_ifs with hp
    · linarith [Real.pi_pos]
    · rfl

/-- Positive radial scaling does not change the lower argument on the closed
lower semicircle. -/
theorem lowerArg_sq_mul_exp_I_mul {r θ : ℝ} (hr : 0 < r)
    (hθ_lower : -Real.pi ≤ θ) (hθ_upper : θ ≤ 0) :
    lowerArg (((r ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (θ : ℂ))) = θ := by
  have hr_sq : 0 < r ^ 2 := sq_pos_of_pos hr
  have harg : Complex.arg (((r ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (θ : ℂ))) =
      Complex.arg (Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.arg_real_mul _ hr_sq
  unfold lowerArg
  rw [harg]
  simpa [lowerArg] using lowerArg_exp_I_mul hθ_lower hθ_upper

private lemma norm_sq_mul_exp_I_mul {r θ : ℝ} (hr : 0 < r) :
    ‖(((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ = r ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_I_mul_ofReal, mul_one, abs_of_pos (sq_pos_of_pos hr)]

/-- Exact evaluation of the lower logarithm on every closed lower circular
arc, including `θ = -π`. -/
theorem lowerLog_sq_mul_exp_I_mul {r θ : ℝ} (hr : 0 < r)
    (hθ_lower : -Real.pi ≤ θ) (hθ_upper : θ ≤ 0) :
    lowerLog (((r ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (θ : ℂ))) =
      ((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ) := by
  have hlog : Real.log (r ^ 2) = 2 * Real.log r := by
    simp
  rw [lowerLog, norm_sq_mul_exp_I_mul hr,
    lowerArg_sq_mul_exp_I_mul hr hθ_lower hθ_upper, hlog]

/-- Exact evaluation of the lower square root on every closed lower circular
arc, including `θ = -π`. -/
theorem lowerSqrt_sq_mul_exp_I_mul {r θ : ℝ} (hr : 0 < r)
    (hθ_lower : -Real.pi ≤ θ) (hθ_upper : θ ≤ 0) :
    lowerSqrt (((r ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (θ : ℂ))) =
      (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) := by
  rw [lowerSqrt, norm_sq_mul_exp_I_mul hr,
    lowerArg_sq_mul_exp_I_mul hr hθ_lower hθ_upper,
    Real.sqrt_sq hr.le]

end RiemannJensen
