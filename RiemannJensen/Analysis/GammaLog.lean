module

public import RiemannJensen.Analysis.GammaRemainderBounds

/-!
# A logarithm of the Gamma remainder

We define `gammaLog`, the sum of the shifted-Gamma logarithm `GammaCore.gammaCoreLog` and the
principal logarithm of the polar correction `gammaPolarCorrection`. It is a holomorphic logarithm
of `gammaRemainder` on `GammaCore.grDomain`, and it and its derivative are `O(‖w‖⁻¹)` and
`O(‖w‖⁻²)` on the closed right half-plane for `4 ≤ ‖w‖`.

## Main definitions

* `gammaLog`: The sum `GammaCore.gammaCoreLog w + log (gammaPolarCorrection w)`.

## Main results

* `gammaRemainder_eq_exp_gammaLog`: `gammaRemainder w = exp (gammaLog w)` on
  `GammaCore.grDomain`.
* `hasDerivAt_gammaLog`: The derivative of `gammaLog`.
* `norm_gammaLog_le`: `‖gammaLog w‖ ≤ 9 / ‖w‖` for `0 ≤ re w` and `4 ≤ ‖w‖`.
* `norm_deriv_gammaLog_le`: `‖deriv gammaLog w‖ ≤ 14 / ‖w‖ ^ 2` for `0 ≤ re w` and `4 ≤ ‖w‖`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The logarithm of `gammaRemainder` given by the sum of `GammaCore.gammaCoreLog` and the
principal logarithm of `gammaPolarCorrection`. -/
noncomputable def gammaLog (w : ℂ) : ℂ :=
  GammaCore.gammaCoreLog w + Complex.log (gammaPolarCorrection w)

private theorem gammaPolarCorrection_re_pos {w : ℂ} (hw : w ∈ GammaCore.grDomain) :
    0 < (gammaPolarCorrection w).re := by
  have hsq : 9 < ‖w‖ ^ 2 := by
    nlinarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 3) hw.2]
  have hsmall : ‖gammaPolarCorrection w - 1‖ < 1 := by
    rw [norm_gammaPolarCorrection_sub_one w, div_lt_one (by positivity)]
    nlinarith
  have hre := abs_re_le_norm (gammaPolarCorrection w - 1)
  rw [sub_re, one_re] at hre
  linarith [neg_le_of_abs_le hre]

/-- The Gamma remainder is the exponential of `gammaLog` on `GammaCore.grDomain`. -/
theorem gammaRemainder_eq_exp_gammaLog {w : ℂ} (hw : w ∈ GammaCore.grDomain) :
    gammaRemainder w = Complex.exp (gammaLog w) := by
  rw [gammaRemainder_eq_polar_mul_core, gammaLog, Complex.exp_add,
    ← GammaCore.gammaCoreRemainder_eq_exp hw,
    Complex.exp_log (gammaPolarCorrection_ne_zero (lt_trans (by norm_num) hw.2)), mul_comm]

/-- For `0 ≤ re w` and `4 ≤ ‖w‖`, `‖gammaLog w‖ ≤ 9 / ‖w‖`. -/
theorem norm_gammaLog_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖gammaLog w‖ ≤ 9 / ‖w‖ := by
  have hpolar := norm_gammaPolarCorrection_sub_one w
  have hhalf : ‖gammaPolarCorrection w - 1‖ ≤ 1 / 2 := by
    rw [hpolar, div_le_iff₀ (by positivity)]
    nlinarith
  have hlog : ‖Complex.log (gammaPolarCorrection w)‖ ≤ 1 / ‖w‖ :=
    calc
      ‖Complex.log (gammaPolarCorrection w)‖ =
          ‖Complex.log (1 + (gammaPolarCorrection w - 1))‖ := by rw [add_sub_cancel]
      _ ≤ 3 / 2 * ‖gammaPolarCorrection w - 1‖ := norm_log_one_add_half_le_self hhalf
      _ = 3 / 2 * (1 / (4 * ‖w‖ ^ 2)) := by rw [hpolar]
      _ ≤ 1 / ‖w‖ := by
        field_simp
        nlinarith
  calc
    ‖gammaLog w‖ ≤ 8 / ‖w‖ + 1 / ‖w‖ :=
      (norm_add_le _ _).trans (add_le_add (GammaCore.norm_gammaCoreLog_le hw hw4) hlog)
    _ = 9 / ‖w‖ := by ring

/-- On `GammaCore.grDomain`, the derivative of `gammaLog` is the sum of
`GammaCore.gammaCoreLogDeriv` and the logarithmic derivative of `gammaPolarCorrection`. -/
theorem hasDerivAt_gammaLog {w : ℂ} (hw : w ∈ GammaCore.grDomain) :
    HasDerivAt gammaLog
      (GammaCore.gammaCoreLogDeriv w + logDeriv gammaPolarCorrection w) w := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num [GammaCore.grDomain] at hw
  have hp := hasDerivAt_gammaPolarCorrection hw0
  have hlog : HasDerivAt (fun z => Complex.log (gammaPolarCorrection z))
      (logDeriv gammaPolarCorrection w) w := by
    rw [logDeriv_apply, hp.deriv, div_eq_mul_inv, mul_comm]
    simpa [Function.comp_def] using
      (Complex.hasDerivAt_log (Or.inl (gammaPolarCorrection_re_pos hw))).comp w hp
  exact (GammaCore.hasDerivAt_gammaCoreLog hw).add hlog

/-- `gammaLog` is continuous on `GammaCore.grDomain`. -/
theorem continuousOn_gammaLog : ContinuousOn gammaLog GammaCore.grDomain :=
  fun _ hw => (hasDerivAt_gammaLog hw).continuousAt.continuousWithinAt

/-- For `0 ≤ re w` and `4 ≤ ‖w‖`, `‖deriv gammaLog w‖ ≤ 14 / ‖w‖ ^ 2`. -/
theorem norm_deriv_gammaLog_le {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖deriv gammaLog w‖ ≤ 14 / ‖w‖ ^ 2 := by
  have hmem : w ∈ GammaCore.grDomain := GammaCore.subset_grDomain hw hw4
  rw [(hasDerivAt_gammaLog hmem).deriv]
  calc
    ‖GammaCore.gammaCoreLogDeriv w + logDeriv gammaPolarCorrection w‖
        ≤ ‖GammaCore.gammaCoreLogDeriv w‖ + ‖logDeriv gammaPolarCorrection w‖ :=
          norm_add_le _ _
    _ ≤ 13 / ‖w‖ ^ 2 + 1 / ‖w‖ ^ 2 := by
      rw [← GammaCore.logDeriv_gammaCoreRemainder hmem]
      exact add_le_add (GammaCore.norm_logDeriv_gammaCoreRemainder_le hw hw4)
        (norm_logDeriv_gammaPolarCorrection_le hw4)
    _ = 14 / ‖w‖ ^ 2 := by ring

end RiemannJensen
