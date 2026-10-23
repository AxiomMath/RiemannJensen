module

public import RiemannJensen.Analysis.GammaRemainderCore
public import RiemannJensen.Analysis.GammaRemainderDefinition
public import RiemannJensen.Analysis.GammaPolarCorrection

/-!
# Quantitative bounds for the exact Gamma remainder

The remainder `gammaRemainder w` is the product of the polar factor `1 - 1 / (4w²)` and the
Stirling remainder `GammaCore.gammaCoreRemainder w`. On the closed right half-plane with
`‖w‖ ≥ 4`, it differs from one by `O(‖w‖⁻¹)` and its logarithmic derivative is `O(‖w‖⁻²)`, with
explicit constants.

## Main results

* `gammaRemainder_eq_polar_mul_core`: `gammaRemainder` factors as `gammaPolarCorrection` times
  `GammaCore.gammaCoreRemainder`.
* `differentiableOn_gammaRemainder`: `gammaRemainder` is holomorphic on `GammaCore.grDomain`.
* `gammaRemainder_ne_zero`: `gammaRemainder` does not vanish on `GammaCore.grDomain`.
* `norm_gammaRemainder_sub_one_le`: `‖gammaRemainder w - 1‖ ≤ 66 / ‖w‖`.
* `norm_logDeriv_gammaRemainder_le`: `‖logDeriv gammaRemainder w‖ ≤ 14 / ‖w‖ ^ 2`.
-/

@[expose] public section

namespace RiemannJensen

open scoped ComplexOrder

/-- The Gamma remainder is the polar correction times the Stirling remainder. -/
theorem gammaRemainder_eq_polar_mul_core (w : ℂ) :
    gammaRemainder w = gammaPolarCorrection w * GammaCore.gammaCoreRemainder w := by
  have hsqrt : Complex.sqrt (2 * Real.pi) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
      Complex.sqrt_of_nonneg (by positivity), Complex.ofReal_re]
  simp only [gammaRemainder, gammaPolarCorrection, GammaCore.gammaCoreRemainder, hsqrt,
    Complex.cpow_eq_pow]
  ring

/-- The Gamma remainder is holomorphic on the open domain `GammaCore.grDomain`. -/
theorem differentiableOn_gammaRemainder :
    DifferentiableOn ℂ gammaRemainder GammaCore.grDomain := by
  intro w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num [GammaCore.grDomain] at hw
  rw [show gammaRemainder = gammaPolarCorrection * GammaCore.gammaCoreRemainder from
    funext gammaRemainder_eq_polar_mul_core]
  exact ((hasDerivAt_gammaPolarCorrection hw0).differentiableAt.mul
    (GammaCore.differentiableOn_gammaCoreRemainder.differentiableAt
      (GammaCore.isOpen_grDomain.mem_nhds hw))).differentiableWithinAt

/-- The Gamma remainder is nonzero throughout `GammaCore.grDomain`. -/
theorem gammaRemainder_ne_zero {w : ℂ} (hw : w ∈ GammaCore.grDomain) :
    gammaRemainder w ≠ 0 := by
  rw [gammaRemainder_eq_polar_mul_core]
  exact mul_ne_zero
    (gammaPolarCorrection_ne_zero (lt_trans (by norm_num) hw.2))
    (GammaCore.gammaCoreRemainder_ne_zero hw)

/-- For `0 ≤ re w` and `4 ≤ ‖w‖`, the Gamma remainder satisfies
`‖gammaRemainder w - 1‖ ≤ 66 / ‖w‖`. -/
theorem norm_gammaRemainder_sub_one_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖gammaRemainder w - 1‖ ≤ 66 / ‖w‖ := by
  have hcore := GammaCore.norm_gammaCoreRemainder_sub_one_le hw hw4
  have hcoreNorm : ‖GammaCore.gammaCoreRemainder w‖ ≤ 17 := by
    have h64 : 64 / ‖w‖ ≤ 16 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith [norm_le_norm_sub_add (GammaCore.gammaCoreRemainder w) 1, norm_one (α := ℂ)]
  rw [gammaRemainder_eq_polar_mul_core,
    show gammaPolarCorrection w * GammaCore.gammaCoreRemainder w - 1 =
      (gammaPolarCorrection w - 1) * GammaCore.gammaCoreRemainder w +
        (GammaCore.gammaCoreRemainder w - 1) by ring]
  calc
    _ ≤ ‖gammaPolarCorrection w - 1‖ * ‖GammaCore.gammaCoreRemainder w‖ +
          ‖GammaCore.gammaCoreRemainder w - 1‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ (1 / (4 * ‖w‖ ^ 2)) * 17 + 64 / ‖w‖ := by
          gcongr
          exact (norm_gammaPolarCorrection_sub_one w).le
    _ ≤ 66 / ‖w‖ := by
          field_simp
          nlinarith [sq_nonneg ‖w‖]

/-- The logarithmic derivative of the polar correction is bounded by `1 / ‖w‖ ^ 2` once
`4 ≤ ‖w‖`. -/
theorem norm_logDeriv_gammaPolarCorrection_le {w : ℂ} (hw4 : 4 ≤ ‖w‖) :
    ‖logDeriv gammaPolarCorrection w‖ ≤ 1 / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hnw : 0 < ‖w‖ := by linarith
  have hsmall : ‖gammaPolarCorrection w - 1‖ ≤ 1 / 64 := by
    rw [norm_gammaPolarCorrection_sub_one w, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ‖w‖]
  have hpLower : 63 / 64 ≤ ‖gammaPolarCorrection w‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (gammaPolarCorrection w)
    rw [norm_one, norm_sub_rev] at hrev
    linarith
  rw [logDeriv_apply, (hasDerivAt_gammaPolarCorrection hw0).deriv, norm_div,
    show ‖(1 : ℂ) / (2 * w ^ 3)‖ = 1 / (2 * ‖w‖ ^ 3) by simp,
    div_le_iff₀ (by linarith)]
  have hprod : 1 ≤ ‖w‖ * ‖gammaPolarCorrection w‖ := by nlinarith
  field_simp
  nlinarith [sq_pos_of_pos hnw]

/-- For `0 ≤ re w` and `4 ≤ ‖w‖`, the logarithmic derivative of the Gamma remainder satisfies
`‖logDeriv gammaRemainder w‖ ≤ 14 / ‖w‖ ^ 2`. -/
theorem norm_logDeriv_gammaRemainder_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖logDeriv gammaRemainder w‖ ≤ 14 / ‖w‖ ^ 2 := by
  have hcMem : w ∈ GammaCore.grDomain := GammaCore.subset_grDomain hw hw4
  rw [show gammaRemainder = gammaPolarCorrection * GammaCore.gammaCoreRemainder from
      funext gammaRemainder_eq_polar_mul_core,
    logDeriv_mul w (gammaPolarCorrection_ne_zero (by linarith))
      (GammaCore.gammaCoreRemainder_ne_zero hcMem)
      (hasDerivAt_gammaPolarCorrection (norm_ne_zero_iff.mp (by linarith))).differentiableAt
      (GammaCore.differentiableOn_gammaCoreRemainder.differentiableAt
        (GammaCore.isOpen_grDomain.mem_nhds hcMem))]
  calc
    _ ≤ ‖logDeriv gammaPolarCorrection w‖ +
          ‖logDeriv GammaCore.gammaCoreRemainder w‖ := norm_add_le _ _
    _ ≤ 1 / ‖w‖ ^ 2 + 13 / ‖w‖ ^ 2 :=
      add_le_add (norm_logDeriv_gammaPolarCorrection_le hw4)
        (GammaCore.norm_logDeriv_gammaCoreRemainder_le hw hw4)
    _ = 14 / ‖w‖ ^ 2 := by ring

end RiemannJensen
