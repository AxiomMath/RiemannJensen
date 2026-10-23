module

public import RiemannJensen.Analysis.CircleGap
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Differentiation of the lower branches along the saddle circle

The lower branches coincide with the principal argument and logarithm in the open lower
half-plane, and their restrictions to an open lower semicircle have explicit angular
derivatives.

## Main results

* `lowerArg_eq_arg_of_im_neg`: in the open lower half-plane, `lowerArg` is `Complex.arg`.
* `lowerLog_eq_log_of_im_neg`: in the open lower half-plane, `lowerLog` is `Complex.log`.
* `phase_sq_mul_exp_I_mul`: an explicit formula for `phase` on the closed lower semicircle.
* `hasDerivAt_lowerLog_circle`: the angular derivative of `lowerLog` on an open lower semicircle.
* `hasDerivAt_lowerSqrt_circle`: the angular derivative of `lowerSqrt` on an open lower
  semicircle.
-/

@[expose] public section

namespace RiemannJensen

/-- In the open lower half-plane the modified argument is the principal argument. -/
theorem lowerArg_eq_arg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    lowerArg u = Complex.arg u := by
  rw [lowerArg, ite_eq_right]
  exact fun h => absurd (Complex.arg_eq_pi_iff.mp h).2 hu.ne

/-- In the open lower half-plane the lower logarithm is Mathlib's principal
complex logarithm. -/
theorem lowerLog_eq_log_of_im_neg {u : ℂ} (hu : u.im < 0) :
    lowerLog u = Complex.log u := by
  apply Complex.ext <;>
    simp [lowerLog, lowerArg_eq_arg_of_im_neg hu, Complex.log_re, Complex.log_im]

/-- Explicit formula for `phase d q` at the point `r ^ 2 * exp (I θ)` of the closed lower
semicircle, `-π ≤ θ ≤ 0`, endpoints included. -/
theorem phase_sq_mul_exp_I_mul (d : ℕ) (q : ℝ) {r θ : ℝ} (hr : 0 < r)
    (hθ_lower : -Real.pi ≤ θ) (hθ_upper : θ ≤ 0) :
    phase d q (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      -(q : ℂ) * (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
      (Real.pi : ℂ) * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)) +
      ((Real.pi / scaleLambda d : ℝ) : ℂ) * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)) *
        (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) -
      (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) := by
  rw [phase, lowerSqrt_sq_mul_exp_I_mul hr hθ_lower hθ_upper,
    lowerLog_sq_mul_exp_I_mul hr hθ_lower hθ_upper]

/-- Angular derivative of the lower logarithm on an open lower semicircle. -/
theorem hasDerivAt_lowerLog_circle {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo (-Real.pi) 0) :
    HasDerivAt (fun t : ℝ => lowerLog (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
      Complex.I θ := by
  have hg : HasDerivAt (fun t : ℝ => ((2 * Real.log r : ℝ) : ℂ) + Complex.I * (t : ℂ))
      Complex.I θ := by
    simpa using (((hasDerivAt_id (θ : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      ((2 * Real.log r : ℝ) : ℂ)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact lowerLog_sq_mul_exp_I_mul hr ht.1.le ht.2.le

/-- Angular derivative of the lower square root on an open lower semicircle. -/
theorem hasDerivAt_lowerSqrt_circle {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo (-Real.pi) 0) :
    HasDerivAt (fun t : ℝ => lowerSqrt (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
      ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) * (Complex.I / 2)) θ := by
  have hinner : HasDerivAt (fun z : ℂ => Complex.I * z / 2) (Complex.I / 2) (θ : ℂ) := by
    simpa using ((hasDerivAt_id (θ : ℂ)).const_mul Complex.I).div_const 2
  have hg : HasDerivAt (fun t : ℝ => (r : ℂ) * Complex.exp (Complex.I * (t : ℂ) / 2))
      ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) * (Complex.I / 2)) θ := by
    simpa [mul_assoc] using
      (((Complex.hasDerivAt_exp _).comp (θ : ℂ) hinner).const_mul (r : ℂ)).comp_ofReal
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact lowerSqrt_sq_mul_exp_I_mul hr ht.1.le ht.2.le

end RiemannJensen
