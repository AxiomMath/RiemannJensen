module

public import RiemannJensen.Analysis.StirlingNative
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The elementary polar correction in the Gamma remainder

The rational function `w ↦ 1 - 1 / (4 * w ^ 2)`, with exact formulas and bounds for its distance
from one and for its complex derivative.

## Main definitions

* `gammaPolarCorrection`: The function `w ↦ 1 - 1 / (4 * w ^ 2)` on `ℂ`.

## Main results

* `norm_gammaPolarCorrection_sub_one`: `‖gammaPolarCorrection w - 1‖ = 1 / (4 * ‖w‖ ^ 2)`.
* `gammaPolarCorrection_ne_zero`: `gammaPolarCorrection w ≠ 0` when `1 / 2 < ‖w‖`.
* `hasDerivAt_gammaPolarCorrection`, `deriv_gammaPolarCorrection`: The derivative at `w ≠ 0`
  is `1 / (2 * w ^ 3)`.
* `norm_deriv_gammaPolarCorrection`: `‖deriv gammaPolarCorrection w‖ = 1 / (2 * ‖w‖ ^ 3)`
  for `w ≠ 0`.
* `norm_deriv_gammaPolarCorrection_le`: The derivative has norm at most `1 / (2 * ‖w‖ ^ 2)`
  when `1 ≤ ‖w‖`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The rational function `w ↦ 1 - 1 / (4 * w ^ 2)` on `ℂ`. -/
noncomputable def gammaPolarCorrection (w : ℂ) : ℂ :=
  1 - 1 / (4 * w ^ 2)

/-- Unfolding `gammaPolarCorrection`. -/
theorem gammaPolarCorrection_apply (w : ℂ) : gammaPolarCorrection w = 1 - 1 / (4 * w ^ 2) := rfl

/-- `‖gammaPolarCorrection w - 1‖ = 1 / (4 * ‖w‖ ^ 2)` for every `w`. -/
theorem norm_gammaPolarCorrection_sub_one (w : ℂ) :
    ‖gammaPolarCorrection w - 1‖ = 1 / (4 * ‖w‖ ^ 2) := by
  simp only [gammaPolarCorrection_apply, sub_sub_cancel_left, norm_neg, norm_div, norm_one,
    norm_mul, norm_ofNat, norm_pow]

/-- If `1 / 2 < ‖w‖`, then `gammaPolarCorrection w ≠ 0`. -/
theorem gammaPolarCorrection_ne_zero {w : ℂ} (hw : 1 / 2 < ‖w‖) :
    gammaPolarCorrection w ≠ 0 := by
  have hsmall : 1 / (4 * ‖w‖ ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [norm_nonneg w]
  intro hzero
  have hnorm : ‖gammaPolarCorrection w - 1‖ = 1 := by
    simp [hzero]
  rw [norm_gammaPolarCorrection_sub_one] at hnorm
  linarith

/-- For `w ≠ 0`, `gammaPolarCorrection` has complex derivative `1 / (2 * w ^ 3)` at `w`. -/
theorem hasDerivAt_gammaPolarCorrection {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt gammaPolarCorrection (1 / (2 * w ^ 3)) w := by
  have hden : (4 : ℂ) * w ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hw)
  unfold gammaPolarCorrection
  convert (hasDerivAt_const w (1 : ℂ)).sub
    (((hasDerivAt_const w (4 : ℂ)).mul ((hasDerivAt_id w).pow 2)).inv hden) using 1
  · funext z
    simp [div_eq_mul_inv]
  · simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

/-- For `w ≠ 0`, `deriv gammaPolarCorrection w = 1 / (2 * w ^ 3)`. -/
theorem deriv_gammaPolarCorrection {w : ℂ} (hw : w ≠ 0) :
    deriv gammaPolarCorrection w = 1 / (2 * w ^ 3) :=
  (hasDerivAt_gammaPolarCorrection hw).deriv

/-- For `w ≠ 0`, `‖deriv gammaPolarCorrection w‖ = 1 / (2 * ‖w‖ ^ 3)`. -/
theorem norm_deriv_gammaPolarCorrection {w : ℂ} (hw : w ≠ 0) :
    ‖deriv gammaPolarCorrection w‖ = 1 / (2 * ‖w‖ ^ 3) := by
  rw [deriv_gammaPolarCorrection hw]
  simp only [norm_div, norm_one, norm_mul, norm_ofNat, norm_pow]

/-- If `1 ≤ ‖w‖`, then `‖deriv gammaPolarCorrection w‖ ≤ 1 / (2 * ‖w‖ ^ 2)`. -/
theorem norm_deriv_gammaPolarCorrection_le {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖deriv gammaPolarCorrection w‖ ≤ 1 / (2 * ‖w‖ ^ 2) := by
  have hpos : 0 < ‖w‖ := by linarith
  rw [norm_deriv_gammaPolarCorrection (norm_pos_iff.mp hpos)]
  gcongr
  norm_num

end RiemannJensen
