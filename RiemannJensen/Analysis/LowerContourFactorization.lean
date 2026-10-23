module

public import RiemannJensen.Analysis.LowerContour
public import RiemannJensen.Analysis.AmplitudeFactorization
public import RiemannJensen.Analysis.TaylorBridge
public import RiemannJensen.Analysis.CauchyRepresentation
public import RiemannJensen.Analysis.ScaleExponent

/-!
# The integrand factorization on the lower semicircle

On the lower semicircle `u = r² e^{iθ}`, `-π ≤ θ ≤ 0`, with `w = T r e^{iθ/2}`,
the Cauchy integrand factors exactly as
`F(T² u) e^{-d q u} u^{-d} = a_q(θ) e^{d h_q(u)}`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The Gamma-zeta main factor of `centeredXi` at `w = T r e^{iθ/2}`, written as
the amplitude constant times the scale exponential. -/
theorem xi_main_factor_eq {T r θ : ℝ} (hT : 0 < T) (hr : 0 < r)
    (hθ1 : -Real.pi ≤ θ) (hθ2 : θ ≤ 0) {w : ℂ}
    (hw : w = ((T * r : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)) :
    (w ^ 2 / 2) * Complex.cpow Real.pi (-(1 / 2 + w) / 2) * gammaMainDenominator w =
      Complex.cpow (Real.pi / 2) (1 / 4) * Complex.cpow w (7 / 4) *
        Complex.exp ((((T / 2 : ℝ) : ℂ) * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2))) *
          ((((Real.log (T / (2 * Real.pi)) - 1 : ℝ) : ℂ) +
            (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) / 2))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hR : 0 < T * r := mul_pos hT hr
  set z : ℂ := ((Real.log (T * r) : ℝ) : ℂ) + Complex.I * (θ : ℂ) / 2 with hz
  have hzim : z.im = θ / 2 := by simp [z]
  have hwz : w = Complex.exp z := by
    rw [hw, hz, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hR]
  have hw0 : w ≠ 0 := by rw [hwz]; exact Complex.exp_ne_zero _
  have him1 : -Real.pi < z.im := by rw [hzim]; linarith
  have him2 : z.im ≤ Real.pi := by rw [hzim]; linarith
  have hlogw : Complex.log w = z := by rw [hwz, Complex.log_exp him1 him2]
  set z2 : ℂ := z - ((Real.log 2 : ℝ) : ℂ) with hz2
  have hw2 : w / 2 = Complex.exp z2 := by
    rw [hz2, Complex.exp_sub, ← hwz, ← Complex.ofReal_exp, Real.exp_log two_pos]
    push_cast; ring
  have hz2im : z2.im = θ / 2 := by rw [hz2, Complex.sub_im, hzim, Complex.ofReal_im, sub_zero]
  have hlogw2 : Complex.log (w / 2) = z2 := by
    rw [hw2, Complex.log_exp (by rw [hz2im]; linarith) (by rw [hz2im]; linarith)]
  have hE : ((T / 2 : ℝ) : ℂ) * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)) = w / 2 := by
    rw [hw]; push_cast; ring
  rw [hE]
  have hsq : w ^ 2 = Complex.exp (2 * z) := by
    rw [hwz, ← Complex.exp_nat_mul]; norm_num
  have hhalf : (2 : ℂ)⁻¹ = Complex.exp (-((Real.log 2 : ℝ) : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log two_pos]; push_cast; ring
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  have hcpi : ∀ s : ℂ, Complex.cpow Real.pi s =
      Complex.exp (((Real.log Real.pi : ℝ) : ℂ) * s) := by
    intro s
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hpi0, Complex.ofReal_log hpi.le]
  have hcpi2 : Complex.cpow (Real.pi / 2) (1 / 4) =
      Complex.exp (((Real.log (Real.pi / 2) : ℝ) : ℂ) * (1 / 4)) := by
    have h0 : ((Real.pi : ℂ) / 2) ≠ 0 := div_ne_zero hpi0 two_ne_zero
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero h0,
      Complex.ofReal_log (by positivity)]
    push_cast; ring_nf
  have hcw : Complex.cpow w (7 / 4) = Complex.exp (z * (7 / 4)) := by
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hw0, hlogw]
  have hsqrt : Complex.sqrt (2 * Real.pi) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * 2⁻¹) := by
    have h0 : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi0
    rw [Complex.sqrt, Complex.cpow_def_of_ne_zero h0, Complex.ofReal_log (by positivity)]
    push_cast; ring_nf
  have hcw2 : (w / 2) ^ (w / 2 - 1 / 4) = Complex.exp (z2 * (w / 2 - 1 / 4)) := by
    rw [Complex.cpow_def_of_ne_zero (div_ne_zero hw0 two_ne_zero), hlogw2]
  unfold gammaMainDenominator
  rw [div_eq_mul_inv (w ^ 2), hsq, hhalf, hcpi, hcpi2, hcw, hsqrt, Complex.cpow_eq_pow,
    hcw2]
  simp only [← Complex.exp_add]
  congr 1
  rw [hz2, hz, Real.log_mul hT.ne' hr.ne', Real.log_div hT.ne' (by positivity),
    Real.log_mul two_ne_zero hpi.ne', Real.log_div hpi.ne' two_ne_zero]
  rw [hw]
  push_cast
  ring

/-- **Integrand factorization**: on the closed lower semicircle `u = r² e^{iθ}`,
`-π ≤ θ ≤ 0`, of the saddle circle, `F(T² u) e^{-d q u} / u^d = a_q(θ) e^{d h_q(u)}`. -/
theorem cauchyNumerator_lower_factorization (d : ℕ) (hd : 1 ≤ d) (q θ : ℝ)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hR : 1 < scaleT d * saddleRadius d (saddleAngle d q))
    (hθ1 : -Real.pi ≤ θ) (hθ2 : θ ≤ 0) :
    cauchyNumerator d (-q) (lowerContourPoint d q θ) / (lowerContourPoint d q θ) ^ d =
      amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ)) := by
  set r := saddleRadius d (saddleAngle d q) with hr_def
  set T := scaleT d with hT_def
  have hT : 0 < T := by
    by_contra h
    have h' : T ≤ 0 := not_lt.mp h
    nlinarith
  set u := lowerContourPoint d q θ with hu_def
  have hu : u = ((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := rfl
  set w := contourW d q θ with hw_def
  have hw : w = ((T * r : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) := rfl
  have he : Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ) / 2) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hTu : ((T ^ 2 : ℝ) : ℂ) * u = w ^ 2 := by
    rw [hu, hw, he]; push_cast; ring
  have heI : Complex.exp (Complex.I * (θ : ℂ) / 2) =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Complex.exp_ne_zero _)
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hs : 0 < (1 / 2 + w).re := by
    rw [Complex.add_re, hw, Complex.re_ofReal_mul, heI, Complex.exp_ofReal_mul_I_re]
    norm_num
    positivity
  have hnw : ‖w‖ = T * r := by
    rw [hw, norm_mul, Complex.norm_real, heI, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_of_nonneg (by positivity)]
  have hs1 : 1 / 2 + w ≠ 1 := by
    intro h
    have : w = 1 / 2 := by linear_combination h
    rw [this] at hnw
    norm_num at hnw
    linarith
  have hsqu : lowerSqrt u = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) :=
    lowerSqrt_sq_mul_exp_I_mul hr hθ1 hθ2
  have hlogu : lowerLog u = ((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ) :=
    lowerLog_sq_mul_exp_I_mul hr hθ1 hθ2
  have hexpL : Complex.exp (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) = u := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, hu]
    congr 2
    rw [show 2 * Real.log r = Real.log (r ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  have hud : u ^ d =
      Complex.exp ((d : ℂ) * (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ))) := by
    rw [Complex.exp_nat_mul, hexpL]
  have hscale := scale_exponent_lower_circle d hd hr hθ1 hθ2
  have hkey := xi_main_factor_eq hT hr hθ1 hθ2 hw
  rw [hscale] at hkey
  have hph : (d : ℂ) * phase d q u =
      (((Real.pi * d : ℝ) : ℂ) * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2))) *
          (1 + (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) / (scaleLambda d : ℂ)) +
        (((d : ℝ) * -q : ℝ) : ℂ) * u -
        (d : ℂ) * (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) := by
    rw [phase, hsqu, hlogu]
    push_cast
    ring
  rw [cauchyNumerator, hTu, riemannF_sq, centeredXi_eq_gammaRemainder hw0 hs hs1, hkey,
    amplitude, hph, Complex.exp_sub, Complex.exp_add, hud]
  ring

end RiemannJensen
