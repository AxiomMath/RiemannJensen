module

public import RiemannJensen.Analysis.CountingTail
public import RiemannJensen.Analysis.LocalPhaseThirdBounds
public import RiemannJensen.Analysis.LocalPhaseSign
public import RiemannJensen.Analysis.GaussianAdapter

/-!
# The counting-window estimates at the fixed width `ε = 1/1000`

For the fixed width parameter `ε = 1/1000` the explicit derivatives of the
normalized lower phase satisfy all the local `C³` hypotheses of the
lower-contour estimate, with linear separation constant `c = 1/2` and
derivative bound `Cp = 3/2`. Consequently, at this width the counting-window
lower-contour estimate and oscillatory formula hold under the hypothesis `n_ε ≥ 1`
together with the edge comparison.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- **Local phase data at the fixed width `ε = 1/1000`.**  On the scale window
the explicit derivatives of the normalized lower phase satisfy every local
hypothesis of the lower-contour estimate, with `c = 1/2` and `Cp = 3/2`. -/
theorem fixedWidth_local_phase_data
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase (1 / 1000) d q)
      (analyticLocalPhaseFirst (1 / 1000) d q (y : ℂ)) y) ∧
    (∀ y ∈ Icc (-1:ℝ) 1,
      HasDerivAt (fun t : ℝ => analyticLocalPhaseFirst (1 / 1000) d q (t : ℂ))
        (analyticLocalPhaseSecond (1 / 1000) d q (y : ℂ)) y) ∧
    (∀ y ∈ Icc (-1:ℝ) 1,
      HasDerivAt (fun t : ℝ => analyticLocalPhaseSecond (1 / 1000) d q (t : ℂ))
        (analyticLocalPhaseThird (1 / 1000) d q (y : ℂ)) y) ∧
    analyticLocalPhaseFirst (1 / 1000) d q ((0 : ℝ) : ℂ) = 0 ∧
    analyticLocalPhaseSecond (1 / 1000) d q ((0 : ℝ) : ℂ) =
      -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) ∧
    (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase (1 / 1000) d q y).re ≤ 0) ∧
    (∀ y ∈ Icc (-1:ℝ) 1,
      (1 / 2 : ℝ) * |y| ≤ ‖analyticLocalPhaseFirst (1 / 1000) d q (y : ℂ)‖) ∧
    (∀ y ∈ Icc (-1:ℝ) 1,
      ‖analyticLocalPhaseSecond (1 / 1000) d q (y : ℂ)‖ ≤ (3 / 2 : ℝ)) ∧
    (∀ y ∈ Icc (-1:ℝ) 1,
      ‖analyticLocalPhaseThird (1 / 1000) d q (y : ℂ)‖ ≤ (3 / 2 : ℝ)) := by
  have hlarge := four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ
  have hα := saddle_inverse_on_scale_window d hd hq
  have hsin : 0 < Real.sin (saddleAngle d q) :=
    Real.sin_pos_of_pos_of_lt_pi hα.1
      (hα.2.1.trans (by linarith [Real.pi_pos]))
  have hD : 0 < ‖saddleHessian d q‖ :=
    lt_of_lt_of_le (mul_pos (by norm_num) hsin)
      (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).1
  have h1 := analyticLocalPhaseFirst_zero (ε := 1 / 1000) d hd hq
  have h2 := analyticLocalPhaseSecond_zero (ε := 1 / 1000) d hd hq (by norm_num)
  have hp' := fun y hy => hasDerivAt_analyticLocalPhaseFirst_ofReal d hd hq
    (ε := 1 / 1000) (by norm_num) (by norm_num) (y := y) hy
  have hp'' := fun y hy => hasDerivAt_analyticLocalPhaseSecond_ofReal d hd hq
    (ε := 1 / 1000) (by norm_num) (by norm_num) (y := y) hy
  have h3 : ∀ y : ℝ, ‖analyticLocalPhaseThird (1 / 1000) d q (y : ℂ)‖ ≤ (1 / 2 : ℝ) :=
    fun y => analyticLocalPhaseThird_fixed_le_half d hd hΛ hlarge hq
  have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
  refine ⟨fun y hy => hasDerivAt_lowerNormalizedPhase d hd hq (by norm_num)
      (by norm_num) hy, hp', hp'', by rw [h0]; exact h1, by rw [h0]; exact h2,
    fun y hy => lowerNormalizedPhase_re_nonpos d hd hΛ hq (by norm_num)
      (by norm_num) hy,
    fun y hy => analyticLocalPhaseFirst_fixed_norm_lower d hd hΛ hlarge hq hy,
    ?_, fun y _ => (h3 y).trans (by norm_num)⟩
  intro y hy
  have hsub := Gaussian.uIcc_zero_subset hy
  have hmv := Gaussian.norm_sub_zero_le_of_hasDerivAt
    (h := fun t : ℝ => analyticLocalPhaseSecond (1 / 1000) d q (t : ℂ))
    (h' := fun t : ℝ => analyticLocalPhaseThird (1 / 1000) d q (t : ℂ))
    (y := y) (K := 1 / 2) (fun t ht => hp'' t (hsub ht)) (fun t _ => h3 t)
  have hA : ‖analyticLocalPhaseSecond (1 / 1000) d q ((0 : ℝ) : ℂ)‖ = 1 := by
    rw [h0, h2, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hD, div_self hD.ne']
  have hy1 : |y| ≤ 1 := abs_le.2 hy
  have htri := norm_le_norm_sub_add
    (analyticLocalPhaseSecond (1 / 1000) d q (y : ℂ))
    (analyticLocalPhaseSecond (1 / 1000) d q ((0 : ℝ) : ℂ))
  linarith

/-- **Fixed-width lower-contour estimate on the counting window, conditional on
the edge comparison** `α_q < 1/2 → q - q_edge ≤ K α_q²`. -/
theorem exists_countingWindow_lowerContribution_estimate_of_edge_fixedWidth :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q K : ℝ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d → 0 < K →
      (saddleAngle d q < 1 / 2 → q - edgeQ d ≤ K * saddleAngle d q ^ 2) →
      1 ≤ effectiveN (1 / 1000) d q →
      ‖lowerContribution d q - leadingSaddle d q‖ ≤
        ‖leadingSaddle d q‖ *
          (windowRelConst (1 / 2) (max (4 + 8 * 2 * zetaLogDerivMajorant) (3 / 2)) *
              effectiveN (1 / 1000) d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * ((1 / 1000 : ℝ) ^ 2 * remoteGapConst K *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_lowerContribution_estimate_of_edge
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q K hd hΛ hM hc₀ hcsmall hscale hq hK hedge hn
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  obtain ⟨hp, hp', hp'', hp'0, hp''0, hre, hlower, hp''_bd, hp'''_bd⟩ :=
    fixedWidth_local_phase_data d hd1 hΛ hsc
  exact hest hd hΛ hM hc₀ hcsmall hscale hq (by norm_num) (by norm_num) hK hedge hn
    (by norm_num) (by norm_num) hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd

/-- **Fixed-width oscillatory formula on the counting window, conditional on
the edge comparison.** -/
theorem exists_countingWindow_rescaledJensen_eval_of_edge_fixedWidth :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q K : ℝ},
      2 ≤ d → gammaCoeff d ≠ 0 → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d → 0 < K →
      (saddleAngle d q < 1 / 2 → q - edgeQ d ≤ K * saddleAngle d q ^ 2) →
      1 ≤ effectiveN (1 / 1000) d q →
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
        2 * ‖leadingSaddle d q‖ *
          (windowRelConst (1 / 2) (max (4 + 8 * 2 * zetaLogDerivMajorant) (3 / 2)) *
              effectiveN (1 / 1000) d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * ((1 / 1000 : ℝ) ^ 2 * remoteGapConst K *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_rescaledJensen_eval_of_edge
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q K hd _ hΛ hM hc₀ hcsmall hscale hq hK hedge hn
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  obtain ⟨hp, hp', hp'', hp'0, hp''0, hre, hlower, hp''_bd, hp'''_bd⟩ :=
    fixedWidth_local_phase_data d hd1 hΛ hsc
  exact hest hd hΛ hM hc₀ hcsmall hscale hq (by norm_num) (by norm_num) hK hedge hn
    (by norm_num) (by norm_num) hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd

end RiemannJensen
