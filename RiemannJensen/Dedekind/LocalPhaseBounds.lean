module

public import RiemannJensen.Dedekind.LocalPhaseHigher
public import RiemannJensen.Analysis.RemotePhaseGap

/-!
# Uniform higher local-phase and remote phase bounds

For the normalized Dedekind saddle-point phase, this file proves eventual uniform bounds on the
local phase over the normalized interval `[-1, 1]`, and a quadratic gap for the real part of the
phase away from the local window on the lower contour.

## Main definitions

* `dedekindRemoteGapConst`: The constant `dedekindLocalEpsilon ^ 2 * remoteGapConst 6`.

## Main results

* `eventually_dedekindLocalPhase_third`: Eventually in `d`, the third derivative of
  `dedekindLocalPhase K d q` is bounded by `1/2` on `[-1, 1]`.
* `eventually_dedekindLocalPhase_deriv_lower`: Eventually in `d`, the derivative of
  `dedekindLocalPhase K d q` at `y ∈ [-1, 1]` has norm at least `|y| / 2`.
* `dedekindLocalPhase_hasDerivAt_chain`: The local phase is three times differentiable on
  `[-1, 1]`, with explicit derivatives.
* `eventually_dedekindRemotePhase_gap`: Eventually in `d`, outside the local window the real part
  of the phase drops below its saddle value by at least
  `dedekindRemoteGapConst * min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹`.
-/

@[expose] public section

namespace RiemannJensen

open _root_.Complex Set Filter Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem norm_higherLocalArc_real
    (d : ℕ) (q y : ℝ) :
    ‖higherLocalArc K d q (y : ℂ)‖ =
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 := by
  simp [higherLocalArc, dedekindSaddle, Complex.norm_exp, Complex.norm_real]

private theorem norm_higherLocalArc_pos
    (d : ℕ) (hd : 1 ≤ d) {q y : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    0 < ‖higherLocalArc K d q (y : ℂ)‖ := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  rw [norm_higherLocalArc_real]
  exact pow_pos (dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩) 2

private theorem norm_analyticLowerSqrt_higherLocalArc
    (d : ℕ) (hd : 1 ≤ d) {q y : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖analyticLowerSqrt (higherLocalArc K d q (y : ℂ))‖ =
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q) :=
    dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  rw [analyticLowerSqrt, Complex.norm_exp, Complex.div_re]
  norm_num
  rw [Complex.log_re, norm_higherLocalArc_real, Real.log_pow]
  norm_num
  convert Real.exp_log hr using 2
  ring

private theorem norm_log_higherLocalArc_le_scaleLambda
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖Complex.log (higherLocalArc K d q (y : ℂ))‖ ≤
      (19 / 24 : ℝ) * dedekindScaleLambda K d := by
  let r := dedekindSaddleRadius K d (dedekindSaddleAngle K d q)
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hr2 : r ≤ 2 := dedekindSaddleRadius_le_two K d hd ⟨hα.1.le, hα.2.le⟩
  have hT := dedekindScaleT_pos K d hd
  have hlo : -(3 * dedekindScaleLambda K d / 8) ≤ Real.log r := by
    apply saddleRadiusAtLambda_log_lower (dedekindScaleLambda_pos K d hd) hT
      (log_dedekindScaleT_le_three_mul_lambda_div_four K d hd hlarge)
      ⟨hα.1.le, hα.2.le⟩
    simpa [dedekindSaddleQ] using hinv.le.trans hq.2
  have hlog2 : Real.log 2 ≤ 3 * dedekindScaleLambda K d / 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [Real.pi_gt_three]
  have habslog : |Real.log r| ≤ 3 * dedekindScaleLambda K d / 8 := by
    rw [abs_le]
    exact ⟨by linarith, (Real.log_le_log hr hr2).trans hlog2⟩
  have hre : (Complex.log (higherLocalArc K d q (y : ℂ))).re =
      2 * Real.log r := by
    rw [Complex.log_re, norm_higherLocalArc_real]
    simp [r]
  have him : |(Complex.log (higherLocalArc K d q (y : ℂ))).im| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩
  calc
    _ ≤ |(Complex.log (higherLocalArc K d q (y : ℂ))).re| +
        |(Complex.log (higherLocalArc K d q (y : ℂ))).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 3 * dedekindScaleLambda K d / 4 + Real.pi := by
      rw [hre, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith
    _ ≤ (19 / 24 : ℝ) * dedekindScaleLambda K d := by nlinarith

private theorem pi_div_scaleLambda_mul_norm_log_higherLocalArc_le
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    Real.pi / dedekindScaleLambda K d * ‖Complex.log (higherLocalArc K d q (y : ℂ))‖ ≤
      19 * Real.pi / 24 := by
  have hΛ0 := dedekindScaleLambda_pos K d hd
  have hh := mul_le_mul_of_nonneg_left
    (norm_log_higherLocalArc_le_scaleLambda K d hd hΛ hlarge hq (y := y))
    (div_nonneg Real.pi_pos.le hΛ0.le)
  field_simp [hΛ0.ne'] at hh ⊢
  nlinarith [Real.pi_pos]

private theorem q_mul_norm_higherLocalArc_le_two
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 2 * Real.pi ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    q * ‖higherLocalArc K d q (y : ℂ)‖ ≤ 2 := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  rw [norm_higherLocalArc_real]
  have hb := dedekindSaddleQ_mul_radius_sq_le K d hd ⟨hα.1.le, hα.2.le⟩
  rw [hinv] at hb
  linarith [(div_le_one (dedekindScaleLambda_pos K d hd)).2 hΛ]


private theorem norm_higherAnalyticPhaseThird_le
    (d : ℕ) (q y : ℝ)
    (hD : 0 < ‖dedekindSaddleHessian K d q‖)
    (hℓ : 0 < dedekindLocalWidth K d q) :
    ‖higherAnalyticPhaseThird K d q (y : ℂ)‖ ≤
      dedekindLocalWidth K d q / ‖dedekindSaddleHessian K d q‖ *
        (‖higherCoeffDeriv3 (dedekindScaleLambda K d)
              (higherLocalArc K d q (y : ℂ))‖ *
            ‖higherLocalArc K d q (y : ℂ)‖ ^ 3 +
          3 * ‖analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
              ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)
              (higherLocalArc K d q (y : ℂ))‖ *
            ‖higherLocalArc K d q (y : ℂ)‖ ^ 2 +
          ‖analyticPhaseCoeffDeriv q (Real.pi : ℂ)
              ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)
              (higherLocalArc K d q (y : ℂ))‖ *
            ‖higherLocalArc K d q (y : ℂ)‖) := by
  let u := higherLocalArc K d q (y : ℂ)
  let ℓ := dedekindLocalWidth K d q
  have hden : 0 < ‖dedekindSaddleHessian K d q‖ * ℓ ^ 2 :=
    mul_pos hD (sq_pos_of_pos hℓ)
  change ‖(higherCoeffDeriv3 (dedekindScaleLambda K d) u *
        (u * (Complex.I * (ℓ : ℂ))) ^ 3 +
      3 * analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u *
        (u * (Complex.I * (ℓ : ℂ))) ^ 2 * (Complex.I * (ℓ : ℂ)) +
      analyticPhaseCoeffDeriv q (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u *
        (u * (Complex.I * (ℓ : ℂ)) ^ 3)) /
        (((‖dedekindSaddleHessian K d q‖ * ℓ ^ 2 : ℝ) : ℂ))‖ ≤
    ℓ / ‖dedekindSaddleHessian K d q‖ *
      (‖higherCoeffDeriv3 (dedekindScaleLambda K d) u‖ * ‖u‖ ^ 3 +
        3 * ‖analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u‖ * ‖u‖ ^ 2 +
        ‖analyticPhaseCoeffDeriv q (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u‖ * ‖u‖)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hden.le]
  apply (div_le_iff₀ hden).2
  calc
    _ ≤ (‖higherCoeffDeriv3 (dedekindScaleLambda K d) u *
          (u * (Complex.I * (ℓ : ℂ))) ^ 3‖ +
        ‖3 * analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u *
          (u * (Complex.I * (ℓ : ℂ))) ^ 2 * (Complex.I * (ℓ : ℂ))‖ +
        ‖analyticPhaseCoeffDeriv q (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u *
          (u * (Complex.I * (ℓ : ℂ)) ^ 3)‖) :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = (ℓ / ‖dedekindSaddleHessian K d q‖ *
        (‖higherCoeffDeriv3 (dedekindScaleLambda K d) u‖ * ‖u‖ ^ 3 +
          3 * ‖analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
            ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u‖ * ‖u‖ ^ 2 +
          ‖analyticPhaseCoeffDeriv q (Real.pi : ℂ)
            ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u‖ * ‖u‖)) *
          (‖dedekindSaddleHessian K d q‖ * ℓ ^ 2) := by
      simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real]
      norm_num
      rw [abs_of_pos hℓ]
      field_simp [hD.ne', hℓ.ne']
      ring

private theorem dedekindLocalWidth_div_hessianNorm_le
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    dedekindLocalWidth K d q / ‖dedekindSaddleHessian K d q‖ ≤
      (16 / 3 : ℝ) * dedekindLocalEpsilon := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hD := dedekindSaddleHessian_norm_bounds K d hd hΛ hα
  rw [hinv] at hD
  have hsin : 0 < Real.sin (dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  have hmin : min (dedekindSaddleAngle K d q)
      (Real.cos (dedekindSaddleAngle K d q)) ≤
      2 * Real.sin (dedekindSaddleAngle K d q) :=
    (min_le_left _ _).trans (by linarith [half_mul_le_sin ⟨hα.1.le, hα.2.le⟩])
  rw [dedekindLocalWidth]
  apply (div_le_iff₀ (lt_of_lt_of_le (mul_pos (by norm_num) hsin) hD.1)).2
  have hm0 : 0 ≤ min (dedekindSaddleAngle K d q)
      (Real.cos (dedekindSaddleAngle K d q)) :=
    le_min hα.1.le (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩)
  have hε : 0 ≤ dedekindLocalEpsilon := by norm_num [dedekindLocalEpsilon]
  nlinarith [mul_le_mul_of_nonneg_left hmin hε]


private theorem dedekindHigherCoeffDeriv3_mul_arc_norm_le_eight
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖higherCoeffDeriv3 (dedekindScaleLambda K d) (higherLocalArc K d q (y : ℂ))‖ *
        ‖higherLocalArc K d q (y : ℂ)‖ ^ 3 ≤ 8 := by
  let u := higherLocalArc K d q (y : ℂ)
  let r := dedekindSaddleRadius K d (dedekindSaddleAngle K d q)
  let Λ := dedekindScaleLambda K d
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hr2 : r ≤ 2 := dedekindSaddleRadius_le_two K d hd ⟨hα.1.le, hα.2.le⟩
  have hΛ0 : 0 < Λ := dedekindScaleLambda_pos K d hd
  have hu0 : 0 < ‖u‖ := norm_higherLocalArc_pos K d hd hq
  have hs : ‖analyticLowerSqrt u‖ = r := norm_analyticLowerSqrt_higherLocalArc K d hd hq
  have hk : Real.pi / Λ ≤ (1 / 24 : ℝ) :=
    (div_le_iff₀ hΛ0).2 (by nlinarith [Real.pi_pos])
  let a : ℂ := 3 * (Real.pi : ℂ) * analyticLowerSqrt u / 8
  let b : ℂ := 3 * ((Real.pi / Λ : ℝ) : ℂ) *
    analyticLowerSqrt u * Complex.log u / 8
  let c : ℂ := ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt u / 4
  have ha : ‖a‖ ≤ 3 := by
    dsimp [a]
    simp only [norm_div, norm_mul, Complex.norm_real]
    norm_num
    rw [hs]
    nlinarith [Real.pi_le_four]
  have hb : ‖b‖ ≤ 2 := by
    dsimp [b]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg Real.pi_pos.le hΛ0.le)]
    norm_num
    rw [hs]
    have hprod : (Real.pi / Λ) * ‖Complex.log u‖ ≤ 19 * Real.pi / 24 :=
      pi_div_scaleLambda_mul_norm_log_higherLocalArc_le K d hd hΛ hlarge hq
    have hp1 := mul_le_mul_of_nonneg_right hprod hr.le
    have hp2 := mul_le_mul_of_nonneg_left hr2
      (by positivity : 0 ≤ 19 * Real.pi / 24)
    nlinarith [hp1, hp2, Real.pi_lt_d2]
  have hc : ‖c‖ ≤ 1 / 48 := by
    dsimp [c]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg Real.pi_pos.le hΛ0.le)]
    norm_num
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_right hk hr.le]
  have hnum : ‖(-2 : ℂ) + a + b - c‖ ≤ 8 := by
    linarith [norm_sub_le ((-2 : ℂ) + a + b) c, norm_add_le ((-2 : ℂ) + a) b,
      norm_add_le (-2 : ℂ) a, show ‖(-2 : ℂ)‖ = 2 by norm_num]
  rw [higherCoeffDeriv3, norm_div, norm_pow]
  change ‖(-2 : ℂ) + a + b - c‖ / ‖u‖ ^ 3 * ‖u‖ ^ 3 ≤ 8
  rwa [div_mul_cancel₀ _ (pow_ne_zero 3 hu0.ne')]

/-- The second analytic derivative has a uniform scale-invariant bound on
the local arc. -/
private theorem dedekindHigherCoeffDeriv2_mul_arc_norm_le_four
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖analyticPhaseCoeffDeriv2 (Real.pi : ℂ) (((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ))
        (higherLocalArc K d q (y : ℂ))‖ *
        ‖higherLocalArc K d q (y : ℂ)‖ ^ 2 ≤ 4 := by
  let u := higherLocalArc K d q (y : ℂ)
  let r := dedekindSaddleRadius K d (dedekindSaddleAngle K d q)
  let Λ := dedekindScaleLambda K d
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hr2 : r ≤ 2 := dedekindSaddleRadius_le_two K d hd ⟨hα.1.le, hα.2.le⟩
  have hΛ0 : 0 < Λ := dedekindScaleLambda_pos K d hd
  have hu0 : 0 < ‖u‖ := norm_higherLocalArc_pos K d hd hq
  have hs : ‖analyticLowerSqrt u‖ = r :=
    norm_analyticLowerSqrt_higherLocalArc K d hd hq
  let a : ℂ := (Real.pi : ℂ) * analyticLowerSqrt u / 4
  let b : ℂ := ((Real.pi / Λ : ℝ) : ℂ) *
    analyticLowerSqrt u * Complex.log u / 4
  have ha : ‖a‖ ≤ 8 / 5 := by
    dsimp [a]
    simp only [norm_div, norm_mul, Complex.norm_real]
    norm_num
    rw [hs]
    nlinarith [Real.pi_lt_d2]
  have hb : ‖b‖ ≤ 5 / 4 := by
    dsimp [b]
    simp only [norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg Real.pi_pos.le hΛ0.le)]
    norm_num
    rw [hs]
    have hp : (Real.pi / Λ) * ‖Complex.log u‖ ≤ 19 * Real.pi / 24 :=
      pi_div_scaleLambda_mul_norm_log_higherLocalArc_le K d hd hΛ hlarge hq
    have hp1 := mul_le_mul_of_nonneg_right hp hr.le
    have hp2 := mul_le_mul_of_nonneg_left hr2
      (by positivity : 0 ≤ 19 * Real.pi / 24)
    nlinarith [hp1, hp2, Real.pi_lt_d2]
  have hnum : ‖(1 : ℂ) - a - b‖ ≤ 4 := by
    linarith [norm_sub_le ((1 : ℂ) - a) b, norm_sub_le (1 : ℂ) a, norm_one (α := ℂ)]
  rw [analyticPhaseCoeffDeriv2, norm_div, norm_pow]
  change ‖(1 : ℂ) - a - b‖ / ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤ 4
  rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hu0.ne')]

private theorem higherCoeffDeriv_log_term_mul_arc_norm_le
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) *
        ((analyticLowerSqrt (higherLocalArc K d q (y : ℂ)) /
            (2 * higherLocalArc K d q (y : ℂ))) * Complex.log (higherLocalArc K d q (y : ℂ)) +
          analyticLowerSqrt (higherLocalArc K d q (y : ℂ)) / higherLocalArc K d q (y : ℂ))‖ *
        ‖higherLocalArc K d q (y : ℂ)‖ ≤ 8 / 3 := by
  set u := higherLocalArc K d q (y : ℂ)
  set Λ := dedekindScaleLambda K d
  let r := dedekindSaddleRadius K d (dedekindSaddleAngle K d q)
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hr2 : r ≤ 2 := dedekindSaddleRadius_le_two K d hd ⟨hα.1.le, hα.2.le⟩
  have hΛ0 : 0 < Λ := dedekindScaleLambda_pos K d hd
  have hu0 : 0 < ‖u‖ := norm_higherLocalArc_pos K d hd hq
  have hs : ‖analyticLowerSqrt u‖ = r :=
    norm_analyticLowerSqrt_higherLocalArc K d hd hq
  calc
    _ ≤ (Real.pi / Λ) *
        (‖analyticLowerSqrt u / (2 * u)‖ * ‖Complex.log u‖ +
          ‖analyticLowerSqrt u / u‖) * ‖u‖ := by
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg Real.pi_pos.le hΛ0.le)]
      gcongr
      calc
        _ ≤ ‖(analyticLowerSqrt u / (2 * u)) * Complex.log u‖ +
            ‖analyticLowerSqrt u / u‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    _ = (Real.pi / Λ) * r * (‖Complex.log u‖ / 2 + 1) := by
      simp only [norm_div, norm_mul]
      norm_num
      rw [hs]
      field_simp [hu0.ne']
    _ ≤ 8 / 3 := by
      have hp : (Real.pi / Λ) * ‖Complex.log u‖ ≤ 19 * Real.pi / 24 :=
        pi_div_scaleLambda_mul_norm_log_higherLocalArc_le K d hd hΛ hlarge hq
      have hk : Real.pi / Λ ≤ 1 / 24 :=
        (div_le_iff₀ hΛ0).2 (by nlinarith [Real.pi_pos])
      have hp1 := mul_le_mul_of_nonneg_right hp hr.le
      have hp2 := mul_le_mul_of_nonneg_left hr2
        (by positivity : 0 ≤ 19 * Real.pi / 24)
      have hk1 := mul_le_mul_of_nonneg_right hk hr.le
      have hk2 := mul_le_mul_of_nonneg_left hr2
        (by positivity : 0 ≤ (1 / 24 : ℝ))
      nlinarith [hp1, hp2, hk1, hk2, Real.pi_lt_d2]

private theorem quarter_le_of_dedekind_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    1 / 4 ≤ q := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hp := one_le_dedekindSaddleQ_mul_radius_sq K d hd
    ⟨hα.1.le, hα.2.le⟩
  rw [hinv] at hp
  have hr0 := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hr2 := dedekindSaddleRadius_le_two K d hd ⟨hα.1.le, hα.2.le⟩
  have hq0 : 0 < q := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (sq_nonneg (dedekindSaddleRadius K d (dedekindSaddleAngle K d q)))
    linarith
  have hr4 : dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 ≤ 4 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hr4 hq0.le]

/-- The first analytic derivative has a uniform scale-invariant bound on the
local arc. -/
private theorem dedekindHigherCoeffDeriv_mul_arc_norm_le_nine
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖analyticPhaseCoeffDeriv q (Real.pi : ℂ) (((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ))
        (higherLocalArc K d q (y : ℂ))‖ *
        ‖higherLocalArc K d q (y : ℂ)‖ ≤ 9 := by
  let u := higherLocalArc K d q (y : ℂ)
  let r := dedekindSaddleRadius K d (dedekindSaddleAngle K d q)
  let Λ := dedekindScaleLambda K d
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hr2 : r ≤ 2 := dedekindSaddleRadius_le_two K d hd ⟨hα.1.le, hα.2.le⟩
  have hΛ0 : 0 < Λ := dedekindScaleLambda_pos K d hd
  have hu0 : 0 < ‖u‖ := norm_higherLocalArc_pos K d hd hq
  have hs : ‖analyticLowerSqrt u‖ = r :=
    norm_analyticLowerSqrt_higherLocalArc K d hd hq
  have hqterm : q * ‖u‖ ≤ 2 := q_mul_norm_higherLocalArc_le_two K
    d hd (by linarith [Real.pi_pos]) hq
  have hq0 : 0 ≤ q := by linarith [quarter_le_of_dedekind_scale_window K d hd hq]
  let a : ℂ := (Real.pi : ℂ) * (analyticLowerSqrt u / (2 * u))
  let b : ℂ := ((Real.pi / Λ : ℝ) : ℂ) *
    ((analyticLowerSqrt u / (2 * u)) * Complex.log u +
      analyticLowerSqrt u / u)
  let c : ℂ := 1 / u
  have ha : ‖a‖ * ‖u‖ ≤ 16 / 5 := by
    dsimp [a]
    simp only [norm_mul, norm_div, Complex.norm_real]
    norm_num
    rw [hs]
    field_simp [hu0.ne']
    nlinarith [Real.pi_lt_d2]
  have hb : ‖b‖ * ‖u‖ ≤ 8 / 3 :=
    higherCoeffDeriv_log_term_mul_arc_norm_le K d hd hΛ hlarge hq
  have hc : ‖c‖ * ‖u‖ = 1 := by
    dsimp [c]
    rw [norm_div]
    norm_num
    exact inv_mul_cancel₀ hu0.ne'
  have hnum :
      ‖(-(q : ℂ) + a + b) - c‖ * ‖u‖ ≤ 9 := by
    have ht :
        ‖(-(q : ℂ) + a + b) - c‖ ≤
          ‖-(q : ℂ)‖ + ‖a‖ + ‖b‖ + ‖c‖ := by
      calc
        _ ≤ ‖-(q : ℂ) + a + b‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ (‖-(q : ℂ) + a‖ + ‖b‖) + ‖c‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ((‖-(q : ℂ)‖ + ‖a‖) + ‖b‖) + ‖c‖ := by
          gcongr
          exact norm_add_le _ _
    have hmul := mul_le_mul_of_nonneg_right ht (norm_nonneg u)
    rw [add_mul, add_mul, add_mul] at hmul
    simp only [norm_neg, Complex.norm_real, Real.norm_of_nonneg hq0] at hmul
    nlinarith [hmul]
  rwa [analyticPhaseCoeffDeriv]


private theorem norm_dedekindSaddleHessian_pos
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    0 < ‖dedekindSaddleHessian K d q‖ := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hDb := dedekindSaddleHessian_norm_bounds K d hd hΛ hα
  rw [dedekindSaddle_inverse K d hd hq] at hDb
  exact lt_of_lt_of_le (mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos])))) hDb.1

private theorem dedekindLocalWidth_pos_of_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    0 < dedekindLocalWidth K d q := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  unfold dedekindLocalWidth dedekindLocalEpsilon
  exact mul_pos (by norm_num)
    (lt_min hα.1 (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα.2⟩))

/-- The analytic third derivative of the normalized Dedekind local phase is
uniformly bounded by `1/2` on the scale window. -/
theorem higherAnalyticPhaseThird_le_half
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    ‖higherAnalyticPhaseThird K d q (y : ℂ)‖ ≤ (1 / 2 : ℝ) := by
  have hraw := norm_higherAnalyticPhaseThird_le K d q y
    (norm_dedekindSaddleHessian_pos K d hd hΛ hq) (dedekindLocalWidth_pos_of_window K d hd hq)
  have h3 := dedekindHigherCoeffDeriv3_mul_arc_norm_le_eight
    K d hd hΛ hlarge (q := q) (y := y) hq
  have h2 := dedekindHigherCoeffDeriv2_mul_arc_norm_le_four
    K d hd hΛ hlarge (q := q) (y := y) hq
  have h1 := dedekindHigherCoeffDeriv_mul_arc_norm_le_nine
    K d hd hΛ hlarge (q := q) (y := y) hq
  let B : ℝ :=
    ‖higherCoeffDeriv3 (dedekindScaleLambda K d)
        (higherLocalArc K d q (y : ℂ))‖ * ‖higherLocalArc K d q (y : ℂ)‖ ^ 3 +
      3 * ‖analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)
        (higherLocalArc K d q (y : ℂ))‖ * ‖higherLocalArc K d q (y : ℂ)‖ ^ 2 +
      ‖analyticPhaseCoeffDeriv q (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)
        (higherLocalArc K d q (y : ℂ))‖ * ‖higherLocalArc K d q (y : ℂ)‖
  have hB : B ≤ 30 := by
    dsimp [B]
    linarith
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hratio := dedekindLocalWidth_div_hessianNorm_le K d hd hΛ hq
  change ‖higherAnalyticPhaseThird K d q (y : ℂ)‖ ≤
    dedekindLocalWidth K d q / ‖dedekindSaddleHessian K d q‖ * B at hraw
  calc
    _ ≤ dedekindLocalWidth K d q / ‖dedekindSaddleHessian K d q‖ * B := hraw
    _ ≤ ((16 / 3 : ℝ) * dedekindLocalEpsilon) * 30 :=
      mul_le_mul hratio hB hB0 (by norm_num [dedekindLocalEpsilon])
    _ ≤ (1 / 2 : ℝ) := by norm_num [dedekindLocalEpsilon]


private theorem dedekindLocalWidth_le_saddleAngle
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    dedekindLocalWidth K d q ≤ dedekindSaddleAngle K d q := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hcos0 : 0 < Real.cos (dedekindSaddleAngle K d q) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα.2⟩
  have hm := min_le_left (dedekindSaddleAngle K d q) (Real.cos (dedekindSaddleAngle K d q))
  have hm0 := le_min hα.1.le hcos0.le
  unfold dedekindLocalWidth dedekindLocalEpsilon
  nlinarith

private theorem dedekindLocalWidth_le_pi_div_two_sub
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    dedekindLocalWidth K d q ≤ Real.pi / 2 - dedekindSaddleAngle K d q := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hcos0 : 0 < Real.cos (dedekindSaddleAngle K d q) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα.2⟩
  have hcosdist : Real.cos (dedekindSaddleAngle K d q) ≤
      Real.pi / 2 - dedekindSaddleAngle K d q := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le (by linarith [hα.2.le])
  have hm := min_le_right (dedekindSaddleAngle K d q) (Real.cos (dedekindSaddleAngle K d q))
  have hm0 := le_min hα.1.le hcos0.le
  unfold dedekindLocalWidth dedekindLocalEpsilon
  nlinarith

private theorem higherLocalArc_im_neg
    (d : ℕ) (hd : 1 ≤ d) {q y : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    (higherLocalArc K d q (y : ℂ)).im < 0 := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hr := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  let α := dedekindSaddleAngle K d q
  let ℓ := dedekindLocalWidth K d q
  have hℓ0 : 0 ≤ ℓ := (dedekindLocalWidth_pos_of_window K d hd hq).le
  have hℓα : ℓ ≤ α := dedekindLocalWidth_le_saddleAngle K d hd hq
  have hℓtop : ℓ ≤ Real.pi / 2 - α := dedekindLocalWidth_le_pi_div_two_sub K d hd hq
  have hlo := mul_le_mul_of_nonneg_left hy.1 hℓ0
  have hhi := mul_le_mul_of_nonneg_left hy.2 hℓ0
  have htheta : -Real.pi < -2 * α + ℓ * y ∧ -2 * α + ℓ * y < 0 := by
    constructor <;> nlinarith
  rw [higherLocalArc, dedekindSaddle, mul_assoc, ← Complex.exp_add]
  rw [show -2 * Complex.I * (α : ℂ) + Complex.I * (ℓ : ℂ) * (y : ℂ) =
      (((-2 * α + ℓ * y : ℝ) : ℂ)) * Complex.I by
    push_cast
    ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [sq_pos_of_pos hr, Real.sin_neg_of_neg_of_neg_pi_lt htheta.2 htheta.1]

private theorem isOpen_setOf_higherLocalArc_im_neg (d : ℕ) (q : ℝ) :
    IsOpen {t : ℝ | (higherLocalArc K d q (t : ℂ)).im < 0} := by
  unfold higherLocalArc
  apply isOpen_lt <;> fun_prop

private theorem deriv_higherAnalyticPhase_eventuallyEq (d : ℕ) {q y : ℝ}
    (huim : (higherLocalArc K d q (y : ℂ)).im < 0) :
    deriv (fun t : ℝ => higherAnalyticPhase K d q (t : ℂ)) =ᶠ[𝓝 y]
      fun t : ℝ => higherAnalyticPhaseFirst K d q (t : ℂ) := by
  filter_upwards [(isOpen_setOf_higherLocalArc_im_neg K d q).mem_nhds huim] with t ht
  exact (hasDerivAt_higherAnalyticPhase K d q
    (Complex.mem_slitPlane_iff.mpr (Or.inr ht.ne))).comp_ofReal.deriv

private theorem deriv_higherAnalyticPhaseFirst_eventuallyEq (d : ℕ) {q y : ℝ}
    (huim : (higherLocalArc K d q (y : ℂ)).im < 0) :
    deriv (fun t : ℝ => higherAnalyticPhaseFirst K d q (t : ℂ)) =ᶠ[𝓝 y]
      fun t : ℝ => higherAnalyticPhaseSecond K d q (t : ℂ) := by
  filter_upwards [(isOpen_setOf_higherLocalArc_im_neg K d q).mem_nhds huim] with t ht
  exact (hasDerivAt_higherAnalyticPhaseFirst K d q
    (Complex.mem_slitPlane_iff.mpr (Or.inr ht.ne))).comp_ofReal.deriv

private theorem dedekindLocalPhase_eventuallyEq_higher_of_im_neg
    (d : ℕ) (hd : 1 ≤ d) {q y : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (huim : (higherLocalArc K d q (y : ℂ)).im < 0) :
    dedekindLocalPhase K d q =ᶠ[𝓝 y]
      fun t : ℝ => higherAnalyticPhase K d q (t : ℂ) := by
  have hsaddle := higherLocalArc_im_neg K d hd hq
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  filter_upwards [(isOpen_setOf_higherLocalArc_im_neg K d q).mem_nhds huim] with t ht
  rw [dedekindLocalPhase, higherAnalyticPhase]
  change
    (saddlePhaseAtLambda (dedekindScaleLambda K d) q (higherLocalArc K d q (t : ℂ)) -
      saddlePhaseAtLambda (dedekindScaleLambda K d) q (dedekindSaddle K d q)) / _ = _
  rw [saddlePhaseAtLambda_eq_analytic_of_im_neg _ _ ht,
    saddlePhaseAtLambda_eq_analytic_of_im_neg _ _ (by simpa [higherLocalArc_zero] using hsaddle)]

private theorem dedekindLocalPhase_eventuallyEq_higher_at
    (d : ℕ) (hd : 1 ≤ d) {q y : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    dedekindLocalPhase K d q =ᶠ[𝓝 y]
      fun t : ℝ => higherAnalyticPhase K d q (t : ℂ) :=
  dedekindLocalPhase_eventuallyEq_higher_of_im_neg K d hd hq (higherLocalArc_im_neg K d hd hq hy)

private theorem eventually_dedekind_scale_hyps :
    ∀ᶠ d : ℕ in atTop, 1 ≤ d ∧ 24 * Real.pi ≤ dedekindScaleLambda K d ∧
      4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d := by
  obtain ⟨DΛ, hDΛ⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  obtain ⟨DA, hDA1, hDA⟩ := eventually_const_le_dedekindScaleLambda K
    (4 * (1 + Real.log (dedekindScaleA K)))
  filter_upwards [eventually_ge_atTop (max DΛ DA)] with d hd
  exact ⟨hDA1.trans ((le_max_right _ _).trans hd), hDΛ d ((le_max_left _ _).trans hd),
    hDA d ((le_max_right _ _).trans hd)⟩

/-- Eventually in `d`, for every `q ∈ (dedekindEdgeQ K d, dedekindScaleT K d]`, the third
derivative of the normalized Dedekind local phase has norm at most `1/2` on `[-1, 1]`. -/
theorem eventually_dedekindLocalPhase_third :
    ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
      dedekindEdgeQ K d < q → q ≤ dedekindScaleT K d →
      ∀ y ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv 3 (dedekindLocalPhase K d q) y‖ ≤ (1 / 2 : ℝ) := by
  filter_upwards [eventually_dedekind_scale_hyps K] with d ⟨hd1, hΛ, hlarge⟩
  intro q hedge hqT y hy
  have hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hedge, hqT⟩
  have heq := dedekindLocalPhase_eventuallyEq_higher_at K d hd1 hq hy
  rw [Filter.EventuallyEq.iteratedDeriv_eq 3 heq]
  have huim := higherLocalArc_im_neg K d hd1 hq hy
  have e12 := (deriv_higherAnalyticPhase_eventuallyEq K d huim).deriv.trans
    (deriv_higherAnalyticPhaseFirst_eventuallyEq K d huim)
  have h3 := (hasDerivAt_higherAnalyticPhaseSecond K d q
    (Complex.mem_slitPlane_iff.mpr (Or.inr huim.ne))).comp_ofReal
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    e12.deriv_eq, h3.deriv]
  exact higherAnalyticPhaseThird_le_half K d hd1 hΛ hlarge hq


private theorem higherAnalyticPhaseFirst_zero
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    higherAnalyticPhaseFirst K d q 0 = 0 := by
  have heq := localPhase_eventuallyEq_higher K d hd hq
  have hactual := dedekindLocalPhase_first K d hd hq
  have huim := higherLocalArc_im_neg K d hd hq
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have hslit : higherLocalArc K d q 0 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using huim.ne))
  have ha := (hasDerivAt_higherAnalyticPhase K d q hslit).comp_ofReal
  rwa [heq.deriv_eq, ha.deriv] at hactual

private theorem higherAnalyticPhaseSecond_zero
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    higherAnalyticPhaseSecond K d q 0 =
      -(dedekindSaddleHessian K d q / (‖dedekindSaddleHessian K d q‖ : ℂ)) := by
  have ht := dedekindLocalPhase_taylor K d hd hq (norm_dedekindSaddleHessian_pos K d hd hΛ hq)
    (dedekindLocalWidth_pos_of_window K d hd hq)
  have heq := localPhase_eventuallyEq_higher K d hd hq
  rw [Filter.EventuallyEq.iteratedDeriv_eq 2 heq] at ht
  have huim := higherLocalArc_im_neg K d hd hq
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have e1 := deriv_higherAnalyticPhase_eventuallyEq K d huim
  have h2 : HasDerivAt (fun t : ℝ => higherAnalyticPhaseFirst K d q (t : ℂ))
      (higherAnalyticPhaseSecond K d q 0) 0 :=
    (hasDerivAt_higherAnalyticPhaseFirst K d q
      (Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using huim.ne)))).comp_ofReal
  rwa [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    e1.deriv_eq, h2.deriv] at ht

private theorem norm_higherAnalyticPhaseSecond_add_le
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hy : y ∈ Icc (-1 : ℝ) 1) {t : ℝ} (ht : t ∈ uIcc 0 y) :
    ‖higherAnalyticPhaseSecond K d q (t : ℂ) +
        dedekindSaddleHessian K d q / (‖dedekindSaddleHessian K d q‖ : ℂ)‖ ≤
      (1 / 2 : ℝ) * |y| := by
  let A : ℂ := dedekindSaddleHessian K d q / (‖dedekindSaddleHessian K d q‖ : ℂ)
  have hzero : higherAnalyticPhaseSecond K d q (((0 : ℝ) : ℂ)) + A = 0 := by
    rw [Complex.ofReal_zero, higherAnalyticPhaseSecond_zero K d hd hΛ hq]
    simp [A]
  have hts : uIcc 0 t ⊆ Icc (-1 : ℝ) 1 :=
    (uIcc_subset_uIcc_left ht).trans (Gaussian.uIcc_zero_subset hy)
  have hm := Gaussian.norm_sub_zero_le_of_hasDerivAt
    (h := fun s : ℝ => higherAnalyticPhaseSecond K d q (s : ℂ) + A)
    (h' := fun s : ℝ => higherAnalyticPhaseThird K d q (s : ℂ))
    (y := t) (K := (1 / 2 : ℝ))
    (fun s hs' =>
      ((hasDerivAt_higherAnalyticPhaseSecond K d q
        (Complex.mem_slitPlane_iff.mpr (Or.inr
          (higherLocalArc_im_neg K d hd hq (hts hs')).ne))).comp_ofReal).add_const A)
    (fun s hs' => higherAnalyticPhaseThird_le_half K d hd hΛ hlarge hq)
  rw [hzero, sub_zero] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (Gaussian.abs_le_of_mem_uIcc_zero ht) (by norm_num))

private theorem higherAnalyticPhaseFirst_norm_lower
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q y : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    (1 / 2 : ℝ) * |y| ≤ ‖higherAnalyticPhaseFirst K d q (y : ℂ)‖ := by
  let A : ℂ := dedekindSaddleHessian K d q / (‖dedekindSaddleHessian K d q‖ : ℂ)
  have hD := norm_dedekindSaddleHessian_pos K d hd hΛ hq
  have hA : ‖A‖ = 1 := by
    dsimp [A]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self hD.ne'
  have hsub := Gaussian.uIcc_zero_subset hy
  have h2 : ∀ t ∈ uIcc 0 y,
      ‖higherAnalyticPhaseSecond K d q (t : ℂ) + A‖ ≤ (1 / 2 : ℝ) * |y| :=
    fun _ ht => norm_higherAnalyticPhaseSecond_add_le K d hd hΛ hlarge hq hy ht
  have hd1 : ∀ t ∈ uIcc 0 y,
      HasDerivAt
        (fun s : ℝ => higherAnalyticPhaseFirst K d q (s : ℂ) + A * (s : ℂ))
        (higherAnalyticPhaseSecond K d q (t : ℂ) + A) t := by
    intro t ht
    have hlin := ((hasDerivAt_id (t : ℂ)).const_mul A).comp_ofReal
    exact (((hasDerivAt_higherAnalyticPhaseFirst K d q
      (Complex.mem_slitPlane_iff.mpr (Or.inr
        (higherLocalArc_im_neg K d hd hq (hsub ht)).ne))).comp_ofReal).add hlin).congr_deriv
      (by simp)
  have hm := Gaussian.norm_sub_zero_le_of_hasDerivAt hd1 h2
  have hfirst0 : higherAnalyticPhaseFirst K d q (((0 : ℝ) : ℂ)) = 0 := by
    simpa using higherAnalyticPhaseFirst_zero K d hd hq
  rw [hfirst0] at hm
  simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_zero] at hm
  have hAy : ‖A * (y : ℂ)‖ = |y| := by
    rw [norm_mul, hA, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have htri := norm_sub_le
    (higherAnalyticPhaseFirst K d q (y : ℂ) + A * (y : ℂ))
    (higherAnalyticPhaseFirst K d q (y : ℂ))
  rw [add_sub_cancel_left, hAy] at htri
  have hyabs : |y| ≤ 1 := by simpa [abs_le] using hy
  have hsq : |y| * |y| ≤ |y| :=
    mul_le_of_le_one_right (abs_nonneg y) hyabs
  have herr : ‖higherAnalyticPhaseFirst K d q (y : ℂ) + A * (y : ℂ)‖ ≤
      (1 / 2 : ℝ) * |y| := by
    calc
      _ ≤ (1 / 2 : ℝ) * |y| * |y| := hm
      _ ≤ (1 / 2 : ℝ) * |y| := by nlinarith
  linarith

/-- Eventually in `d`, for every `q ∈ (dedekindEdgeQ K d, dedekindScaleT K d]` and
`y ∈ [-1, 1]`, the derivative of the normalized Dedekind local phase at `y` has norm at least
`|y| / 2`. -/
theorem eventually_dedekindLocalPhase_deriv_lower :
    ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
      dedekindEdgeQ K d < q → q ≤ dedekindScaleT K d →
      ∀ y ∈ Icc (-1 : ℝ) 1,
        (1 / 2 : ℝ) * |y| ≤ ‖deriv (dedekindLocalPhase K d q) y‖ := by
  filter_upwards [eventually_dedekind_scale_hyps K] with d ⟨hd1, hΛ, hlarge⟩
  intro q hedge hqT y hy
  have hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hedge, hqT⟩
  have heq := dedekindLocalPhase_eventuallyEq_higher_at K d hd1 hq hy
  have huim := higherLocalArc_im_neg K d hd1 hq hy
  have ha := (hasDerivAt_higherAnalyticPhase K d q
    (Complex.mem_slitPlane_iff.mpr (Or.inr huim.ne))).comp_ofReal
  rw [heq.deriv_eq, ha.deriv]
  exact higherAnalyticPhaseFirst_norm_lower K d hd1 hΛ hlarge hq hy

/-- The normalized Dedekind local phase is three times differentiable on the whole normalized
local interval `[-1, 1]`. -/
theorem dedekindLocalPhase_hasDerivAt_chain
    (d : ℕ) (hd : 1 ≤ d) {q y : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (dedekindLocalPhase K d q)
        (deriv (dedekindLocalPhase K d q) y) y ∧
      HasDerivAt (deriv (dedekindLocalPhase K d q))
        (iteratedDeriv 2 (dedekindLocalPhase K d q) y) y ∧
      HasDerivAt (iteratedDeriv 2 (dedekindLocalPhase K d q))
        (iteratedDeriv 3 (dedekindLocalPhase K d q) y) y := by
  have huim := higherLocalArc_im_neg K d hd hq hy
  have hslit := Complex.mem_slitPlane_iff.mpr (Or.inr huim.ne)
  have heq := dedekindLocalPhase_eventuallyEq_higher_of_im_neg K d hd hq huim
  have ep1 := heq.deriv.trans (deriv_higherAnalyticPhase_eventuallyEq K d huim)
  have ep2 := ep1.deriv.trans (deriv_higherAnalyticPhaseFirst_eventuallyEq K d huim)
  have hp0 := heq.hasDerivAt_iff.mpr (hasDerivAt_higherAnalyticPhase K d q hslit).comp_ofReal
  have hp1 :=
    ep1.hasDerivAt_iff.mpr (hasDerivAt_higherAnalyticPhaseFirst K d q hslit).comp_ofReal
  have hp2 :=
    ep2.hasDerivAt_iff.mpr (hasDerivAt_higherAnalyticPhaseSecond K d q hslit).comp_ofReal
  have h2 : iteratedDeriv 2 (dedekindLocalPhase K d q) =
      deriv (deriv (dedekindLocalPhase K d q)) := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  refine ⟨hp0.differentiableAt.hasDerivAt, ?_, ?_⟩
  · rw [h2]
    exact hp1.differentiableAt.hasDerivAt
  · rw [h2, show 3 = 2 + 1 by norm_num, iteratedDeriv_succ, h2]
    exact hp2.differentiableAt.hasDerivAt

private theorem remote_gap_le_of_cos_separation {ε α ℓ x : ℝ}
    (hℓ : ℓ = ε * min α (Real.cos α)) (hℓ0 : 0 ≤ ℓ) (hs : 0 ≤ Real.sin α)
    (hsep : ℓ * Real.sin α / (2 * Real.pi) ≤ |x|) :
    3 / (8 * Real.pi ^ 2) * ε ^ 2 * min α (Real.cos α) ^ 2 * Real.sin α ^ 2 ≤
      3 / 2 * x ^ 2 := by
  have h := pow_le_pow_left₀ (by positivity) hsep 2
  rw [sq_abs] at h
  have heq : 3 / (8 * Real.pi ^ 2) * ε ^ 2 * min α (Real.cos α) ^ 2 * Real.sin α ^ 2 =
      3 / 2 * (ℓ * Real.sin α / (2 * Real.pi)) ^ 2 := by
    rw [hℓ]
    field_simp
    ring
  rw [heq]
  linarith

private theorem dedekind_remote_phase_gap_generic
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hout : θ ∉ Ioo
      (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
      (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q)) :
    3 / (8 * Real.pi ^ 2) * dedekindLocalEpsilon ^ 2 *
        min (dedekindSaddleAngle K d q)
          (Real.cos (dedekindSaddleAngle K d q)) ^ 2 *
        Real.sin (dedekindSaddleAngle K d q) ^ 2 ≤
      (dedekindSaddlePhase K d q (dedekindSaddle K d q)).re -
      (dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ)).re := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  set α := dedekindSaddleAngle K d q with hαdef
  set ℓ := dedekindLocalWidth K d q
  have hℓ0 : 0 < ℓ := dedekindLocalWidth_pos_of_window K d hd hq
  have hℓα : ℓ ≤ α := dedekindLocalWidth_le_saddleAngle K d hd hq
  have hℓtop : ℓ ≤ Real.pi / 2 - α := dedekindLocalWidth_le_pi_div_two_sub K d hd hq
  set β := -θ / 2 with hβdef
  have hβ : β ∈ Icc 0 (Real.pi / 2) :=
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hfar : β ≤ α - ℓ / 2 ∨ α + ℓ / 2 ≤ β := by
    by_contra hn
    push Not at hn
    exact hout ⟨by linarith [hn.2], by linarith [hn.1]⟩
  have hsep := cos_separation_of_far hα.1 hℓ0 hℓα hℓtop hβ hfar
  have hgap := dedekindSaddlePhase_circle_quadratic_gap K d hΛ
    ⟨hα.1, hα.2.le⟩ hβ
  rw [hinv] at hgap
  have hθeq : ((-2 * β : ℝ) : ℂ) = (θ : ℂ) := by
    congr 1
    rw [hβdef]
    ring
  rw [hθeq] at hgap
  have hsad :
      dedekindSaddlePhase K d q (dedekindSaddle K d q) =
        dedekindSaddlePhase K d q
          ((((dedekindSaddleRadius K d α) ^ 2 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((-2 * α : ℝ) : ℂ)))) := by
    rw [dedekindSaddle, ← hαdef]
    congr 2
    push_cast
    ring_nf
  have hpt :
      dedekindLowerContourPoint K d q θ =
        (((dedekindSaddleRadius K d α) ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (θ : ℂ)) := rfl
  rw [hsad, hpt]
  refine le_trans ?_ hgap
  linarith [remote_gap_le_of_cos_separation (ε := dedekindLocalEpsilon) rfl hℓ0.le
    (Real.sin_nonneg_of_nonneg_of_le_pi hα.1.le (by linarith [Real.pi_pos])) hsep]

private theorem one_div_pi_le_sin_of_half_le {α : ℝ} (h₁ : 1 / 2 ≤ α)
    (h₂ : α < Real.pi / 2) : 1 / Real.pi ≤ Real.sin α := by
  have h := Real.mul_le_sin (x := 1 / 2) (by norm_num) (by linarith)
  have hm : Real.sin (1 / 2) ≤ Real.sin α :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h₂.le h₁
  have heq : 2 / Real.pi * (1 / 2) = 1 / Real.pi := by
    field_simp
  linarith

private theorem remote_gap_large_angle_le {ε q m s : ℝ} (hq : 0 < q)
    (hm : Real.pi ^ 2 / (256 * q) ≤ m) (hs : 1 / Real.pi ^ 2 ≤ s) :
    3 * ε ^ 2 / (2048 * Real.pi ^ 2 * q) ≤ 3 / (8 * Real.pi ^ 2) * ε ^ 2 * m * s := by
  have hc0 : 0 ≤ 3 / (8 * Real.pi ^ 2) * ε ^ 2 := by positivity
  have h1 := mul_le_mul hm hs (by positivity) (le_trans (by positivity) hm)
  have h2 := mul_le_mul_of_nonneg_left h1 hc0
  have heq : 3 * ε ^ 2 / (2048 * Real.pi ^ 2 * q) =
      3 / (8 * Real.pi ^ 2) * ε ^ 2 * (Real.pi ^ 2 / (256 * q) * (1 / Real.pi ^ 2)) := by
    field_simp
    ring
  rw [heq]
  linarith

private theorem dedekind_remote_phase_gap_large_angle
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hcosT : ∀ α ∈ Icc 0 (Real.pi / 2),
      dedekindSaddleQ K d α ≤ dedekindScaleT K d →
      Real.pi * dedekindSaddleRadius K d α / 16 ≤ Real.cos α)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hαlarge : 1 / 2 ≤ dedekindSaddleAngle K d q)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hout : θ ∉ Ioo
      (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
      (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q)) :
    3 * dedekindLocalEpsilon ^ 2 /
        (2048 * Real.pi ^ 2 * q) ≤
      (dedekindSaddlePhase K d q (dedekindSaddle K d q)).re -
      (dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ)).re := by
  have hgen := dedekind_remote_phase_gap_generic K d hd hΛ hq hθ hout
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  set α := dedekindSaddleAngle K d q
  have hq4 := quarter_le_of_dedekind_scale_window K d hd hq
  have hq0 : 0 < q := by linarith
  have hsin : 1 / Real.pi ≤ Real.sin α := one_div_pi_le_sin_of_half_le hαlarge hα.2
  have hcosr : Real.pi * dedekindSaddleRadius K d α / 16 ≤ Real.cos α :=
    hcosT α ⟨hα.1.le, hα.2.le⟩ (hinv.le.trans hq.2)
  have hrq : 1 / Real.sqrt q ≤ dedekindSaddleRadius K d α := by
    have hr := (dedekindSaddleRadius_level_comparison K d
      (by linarith [Real.pi_pos]) ⟨hα.1.le, hα.2.le⟩).1
    rwa [hinv] at hr
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsq2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hsqhalf : 1 / 2 ≤ Real.sqrt q := by nlinarith
  have hcosq : Real.pi / (16 * Real.sqrt q) ≤ Real.cos α := by
    have heq : Real.pi / (16 * Real.sqrt q) =
        Real.pi * (1 / Real.sqrt q) / 16 := by field_simp
    rw [heq]
    have := mul_le_mul_of_nonneg_left hrq Real.pi_pos.le
    linarith
  have hαq : Real.pi / (16 * Real.sqrt q) ≤ α := by
    have : Real.pi / (16 * Real.sqrt q) ≤ Real.pi / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [Real.pi_le_four]
  have hmin : Real.pi / (16 * Real.sqrt q) ≤ min α (Real.cos α) :=
    le_min hαq hcosq
  have hmin0 : 0 ≤ Real.pi / (16 * Real.sqrt q) := by positivity
  have hminsq : Real.pi ^ 2 / (256 * q) ≤ min α (Real.cos α) ^ 2 := by
    have h := pow_le_pow_left₀ hmin0 hmin 2
    have heq : (Real.pi / (16 * Real.sqrt q)) ^ 2 =
        Real.pi ^ 2 / (256 * q) := by
      rw [div_pow, mul_pow, hsq2]
      norm_num
    linarith
  have hsinsq : 1 / Real.pi ^ 2 ≤ Real.sin α ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hsin 2
    rwa [div_pow, one_pow] at h
  exact le_trans (remote_gap_large_angle_le hq0 hminsq hsinsq) hgen

private theorem remote_gap_small_angle_le {ε e α s : ℝ}
    (he : e ^ 2 / 6 ^ 2 ≤ α ^ 4) (hs : (2 / Real.pi * α) ^ 2 ≤ s) :
    3 * ε ^ 2 * e ^ 2 / (2 * Real.pi ^ 4 * 6 ^ 2) ≤
      3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2 * s := by
  have h1 := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2)
  have heq : 3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2 * (2 / Real.pi * α) ^ 2 =
      3 * ε ^ 2 / (2 * Real.pi ^ 4) * α ^ 4 := by
    field_simp
    ring
  have heq2 : 3 * ε ^ 2 * e ^ 2 / (2 * Real.pi ^ 4 * 6 ^ 2) =
      3 * ε ^ 2 / (2 * Real.pi ^ 4) * (e ^ 2 / 6 ^ 2) := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 3 * ε ^ 2 / (2 * Real.pi ^ 4))
  rw [heq] at h1
  rw [heq2]
  linarith

private theorem dedekind_remote_phase_gap_small_angle
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hαsmall : dedekindSaddleAngle K d q < 1 / 2)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hout : θ ∉ Ioo
      (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
      (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q)) :
    3 * dedekindLocalEpsilon ^ 2 * (q - dedekindEdgeQ K d) ^ 2 /
        (2 * Real.pi ^ 4 * 6 ^ 2) ≤
      (dedekindSaddlePhase K d q (dedekindSaddle K d q)).re -
      (dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ)).re := by
  have hgen := dedekind_remote_phase_gap_generic K d hd hΛ hq hθ hout
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  set α := dedekindSaddleAngle K d q
  have hedge : q - dedekindEdgeQ K d ≤ 6 * α ^ 2 := by
    have := dedekindSaddleQ_sub_edge_upper K d hΛ
      ⟨hα.1.le, hαsmall.le⟩
    rwa [hinv] at this
  have hcos : α ≤ Real.cos α := by
    have h := Real.one_sub_sq_div_two_le_cos (x := α)
    nlinarith
  have hmin : min α (Real.cos α) = α := min_eq_left hcos
  have hsin : 2 / Real.pi * α ≤ Real.sin α :=
    Real.mul_le_sin hα.1.le hα.2.le
  have hsinsq : (2 / Real.pi * α) ^ 2 ≤ Real.sin α ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hα.1.le) hsin 2
  have hqe0 : 0 < q - dedekindEdgeQ K d := by linarith [hq.1]
  have hedgesq : (q - dedekindEdgeQ K d) ^ 2 ≤ 6 ^ 2 * α ^ 4 := by
    have := pow_le_pow_left₀ hqe0.le hedge 2
    nlinarith
  have hα4 : (q - dedekindEdgeQ K d) ^ 2 / 6 ^ 2 ≤ α ^ 4 := by
    norm_num at hedgesq ⊢
    linarith
  rw [hmin] at hgen
  exact le_trans (remote_gap_small_angle_le hα4 hsinsq) hgen

/-- The constant `dedekindLocalEpsilon ^ 2 * remoteGapConst 6` in the remote phase gap. -/
noncomputable def dedekindRemoteGapConst : ℝ :=
  dedekindLocalEpsilon ^ 2 * remoteGapConst 6

/-- The remote-gap constant `dedekindRemoteGapConst` is positive. -/
theorem dedekindRemoteGapConst_pos : 0 < dedekindRemoteGapConst := by
  unfold dedekindRemoteGapConst dedekindLocalEpsilon
  exact mul_pos (by norm_num) (remoteGapConst_pos 6)

private theorem remoteGapConst_six_le_small :
    remoteGapConst 6 ≤ 3 / (2 * Real.pi ^ 4 * 6 ^ 2) := by
  rw [remoteGapConst]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  norm_num
  nlinarith [pow_pos Real.pi_pos 4]

private theorem remoteGapConst_six_le_large : remoteGapConst 6 ≤ 3 / (2048 * Real.pi ^ 2) := by
  rw [remoteGapConst]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have hpi2 : Real.pi ^ 2 ≤ Real.pi ^ 4 * max (6 ^ 2) 1 := by
    have h4 : Real.pi ^ 2 ≤ Real.pi ^ 4 :=
      pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) (by norm_num)
    rw [max_eq_left (by norm_num)]
    nlinarith [pow_pos Real.pi_pos 4]
  nlinarith

/-- Eventually in `d`, for every `q ∈ (dedekindEdgeQ K d, dedekindScaleT K d]` and every
`θ ∈ [-π, 0]` outside the local window around `-2 * dedekindSaddleAngle K d q`, the real part of
the phase at the lower contour point is below its value at the saddle by at least
`dedekindRemoteGapConst * min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹`. -/
theorem eventually_dedekindRemotePhase_gap :
    ∀ᶠ d : ℕ in atTop, ∀ q,
      dedekindEdgeQ K d < q →
      q ≤ dedekindScaleT K d →
      ∀ θ ∈ Icc (-Real.pi) 0,
        θ ∉ Ioo
          (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
          (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q) →
        dedekindRemoteGapConst *
            min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹ ≤
          (dedekindSaddlePhase K d q (dedekindSaddle K d q)).re -
          (dedekindSaddlePhase K d q
            (dedekindLowerContourPoint K d q θ)).re := by
  obtain ⟨DΛ, hDΛ⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  obtain ⟨Dc, hDc1, hDc⟩ := eventually_dedekindSaddleCos_radius_comparison K
  filter_upwards [eventually_ge_atTop (max DΛ Dc)] with d hd
  intro q hqe hqT θ hθ hout
  have hdΛ : DΛ ≤ d := (le_max_left _ _).trans hd
  have hdc : Dc ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := hDc1.trans hdc
  have hΛ := hDΛ d hdΛ
  have hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hqe, hqT⟩
  have hq0 : 0 < q := by
    linarith [quarter_le_of_dedekind_scale_window K d hd1 hq]
  have hm0 : 0 ≤ min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹ :=
    le_min (sq_nonneg _) (inv_nonneg.2 hq0.le)
  rcases lt_or_ge (dedekindSaddleAngle K d q) (1 / 2) with hs | hl
  · have h := dedekind_remote_phase_gap_small_angle K d hd1 hΛ hq hs hθ hout
    refine le_trans ?_ h
    have hm := min_le_left ((q - dedekindEdgeQ K d) ^ 2) q⁻¹
    have hc := remoteGapConst_six_le_small
    change dedekindLocalEpsilon ^ 2 * remoteGapConst 6 *
        min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹ ≤ _
    calc
      _ ≤ dedekindLocalEpsilon ^ 2 *
          (3 / (2 * Real.pi ^ 4 * 6 ^ 2)) *
          (q - dedekindEdgeQ K d) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) hm hm0 (by positivity)
      _ = _ := by field_simp
  · have h := dedekind_remote_phase_gap_large_angle K d hd1 hΛ
      (fun α hα hαT => (hDc d hdc α hα hαT).1) hq hl hθ hout
    refine le_trans ?_ h
    have hm := min_le_right ((q - dedekindEdgeQ K d) ^ 2) q⁻¹
    have hc := remoteGapConst_six_le_large
    change dedekindLocalEpsilon ^ 2 * remoteGapConst 6 *
        min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹ ≤ _
    calc
      _ ≤ dedekindLocalEpsilon ^ 2 *
          (3 / (2048 * Real.pi ^ 2)) * q⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) hm hm0 (by positivity)
      _ = _ := by field_simp

end

end RiemannJensen
