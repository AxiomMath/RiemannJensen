module

public import RiemannJensen.Analysis.AmplitudeDefinitions

/-!
# Normalization of the Gaussian main term

The Gaussian estimate produces the main term `(π / ((n / 2) * A)) ^ (1 / 2)` with
`n = d ‖D‖ ℓ²` and `A = D / ‖D‖`.  Multiplied by the width `ℓ` and divided by
`2π`, this is exactly `1 / √(2π d D)` for the principal square root, provided
`0 < Re D`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- For `0 < Re D`, the direction `D / ‖D‖` has norm `1`. -/
theorem norm_div_norm_eq_one {D : ℂ} (hD : 0 < D.re) : ‖D / (‖D‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr (ne_zero_of_re_pos hD))]

/-- For `0 < Re D`, the direction `D / ‖D‖` has positive real part. -/
theorem re_div_norm_pos {D : ℂ} (hD : 0 < D.re) : 0 < (D / (‖D‖ : ℂ)).re := by
  rw [Complex.div_ofReal_re]
  exact div_pos hD (norm_pos_iff.mpr (ne_zero_of_re_pos hD))

/-- The effective Gaussian parameter times the direction recovers `d D ℓ²`. -/
theorem effective_mul_direction {D : ℂ} (hD : 0 < D.re) (dd ℓ : ℝ) :
    ((dd * ‖D‖ * ℓ ^ 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)) = (dd : ℂ) * D * (ℓ : ℂ) ^ 2 := by
  have hn : ((‖D‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ne_zero_of_re_pos hD))
  push_cast
  field_simp

/-- Half the effective Gaussian parameter times the direction is `d D ℓ² / 2`. -/
theorem half_effective_mul_direction {D : ℂ} (hD : 0 < D.re) (dd ℓ : ℝ) :
    (((dd * ‖D‖ * ℓ ^ 2) / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)) =
      (dd : ℂ) * D * (ℓ : ℂ) ^ 2 / 2 := by
  rw [Complex.ofReal_div, div_mul_eq_mul_div, effective_mul_direction hD dd ℓ]
  norm_num

/-- For `0 < Re L` and `0 < c`, the principal square roots of `c² L⁻¹` and `L`
multiply to `c`. -/
theorem cpow_half_sq_mul_inv_mul_cpow_half {L : ℂ} (hL : 0 < L.re) {c : ℝ} (hc : 0 < c) :
    (((c ^ 2 : ℝ) : ℂ) * L⁻¹) ^ (1 / 2 : ℂ) * L ^ (1 / 2 : ℂ) = c := by
  have hL0 := ne_zero_of_re_pos hL
  have harg : L.arg ≠ Real.pi :=
    ((abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hL))).2.trans
      (by linarith [Real.pi_pos])).ne
  have hc2 : 0 < c ^ 2 := by positivity
  rw [Complex.cpow_def_of_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc2.ne') (inv_ne_zero hL0)),
    Complex.cpow_def_of_ne_zero hL0, ← Complex.exp_add,
    Complex.log_ofReal_mul hc2 (inv_ne_zero hL0), Complex.log_inv L harg, Real.log_pow]
  have : (((((2 : ℕ) : ℝ) * Real.log c : ℝ) : ℂ) + -Complex.log L) * (1 / 2) +
      Complex.log L * (1 / 2) = ((Real.log c : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.ofReal_log hc.le, Complex.exp_log (Complex.ofReal_ne_zero.mpr hc.ne')]

/-- The width factor cancels the scale in the Gaussian main term:
`ℓ (π / ((n/2) A))^{1/2} / (2π) = 1 / √(2π d D)` with `n = d ‖D‖ ℓ²`,
`A = D / ‖D‖`. -/
theorem gaussian_main_term_normalization {D : ℂ} (hD : 0 < D.re) {dd ℓ : ℝ} (hdd : 0 < dd)
    (hℓ : 0 < ℓ) :
    (ℓ : ℂ) * (((Real.pi : ℂ) /
        ((((dd * ‖D‖ * ℓ ^ 2) / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ)) /
        (2 * Real.pi) =
      1 / Complex.sqrt (2 * Real.pi * dd * D) := by
  set L : ℂ := 2 * Real.pi * dd * D with hLdef
  have hLre : 0 < L.re := by
    rw [show L = ((2 * Real.pi * dd : ℝ) : ℂ) * D by push_cast; rfl, Complex.re_ofReal_mul]
    positivity
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hdd0 : (dd : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdd.ne'
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hX : (Real.pi : ℂ) / ((((dd * ‖D‖ * ℓ ^ 2) / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ))) =
      ((((2 * Real.pi / ℓ) ^ 2 : ℝ)) : ℂ) * L⁻¹ := by
    rw [half_effective_mul_direction hD dd ℓ, hLdef]
    push_cast
    field_simp
  have hS0 : L ^ (1 / 2 : ℂ) ≠ 0 := fun h =>
    ne_zero_of_re_pos hLre ((Complex.cpow_eq_zero_iff _ _).1 h).1
  rw [hX, show Complex.sqrt L = L ^ (1 / 2 : ℂ) by rw [Complex.sqrt, one_div],
    eq_div_iff hS0, div_mul_eq_mul_div, mul_assoc,
    cpow_half_sq_mul_inv_mul_cpow_half hLre (by positivity : 0 < 2 * Real.pi / ℓ)]
  push_cast
  field_simp

/-- Nonvanishing of the principal square root `√(2π d D)` when `0 < Re D`. -/
theorem sqrt_two_pi_mul_ne_zero {D : ℂ} (hD : 0 < D.re) {dd : ℝ} (hdd : 0 < dd) :
    Complex.sqrt (2 * Real.pi * dd * D) ≠ 0 := by
  rw [Complex.sqrt, Ne, Complex.cpow_eq_zero_iff]
  exact fun h => by simp [Real.pi_ne_zero, hdd.ne', ne_zero_of_re_pos hD] at h

/-- Nonvanishing of the principal square root `√(2π d D)` for a natural number `d > 0` when
`0 < Re D`. -/
theorem sqrt_two_pi_natCast_mul_ne_zero {D : ℂ} (hD : 0 < D.re) {d : ℕ} (hd : 0 < d) :
    Complex.sqrt (2 * Real.pi * d * D) ≠ 0 := by
  simpa using sqrt_two_pi_mul_ne_zero hD (dd := (d : ℝ)) (Nat.cast_pos.mpr hd)

/-- The Gaussian main term at the saddle, normalized by the local width, is the
square-root factor of `leadingSaddle`. -/
theorem gaussian_main_term_eq_saddle_factor {d : ℕ} {q ε : ℝ} (hd : 0 < d)
    (hH : 0 < (saddleHessian d q).re) (hℓ : 0 < localWidth ε d q) :
    (localWidth ε d q : ℂ) * (((Real.pi : ℂ) /
        ((((effectiveN ε d q) / 2 : ℝ) : ℂ) *
          (saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))) ^ (1 / 2 : ℂ)) /
        (2 * Real.pi) =
      1 / Complex.sqrt (2 * Real.pi * d * saddleHessian d q) := by
  simpa [effectiveN] using
    gaussian_main_term_normalization hH (dd := (d : ℝ)) (Nat.cast_pos.mpr hd) hℓ

end RiemannJensen
