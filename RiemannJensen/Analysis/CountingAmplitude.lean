module

public import RiemannJensen.Analysis.CountingZetaDomain
public import RiemannJensen.Analysis.SaddleComparisons
public import RiemannJensen.Analysis.LowerContourAssembly
public import RiemannJensen.Analysis.XiThetaMoments

/-!
# Amplitude bounds and the lower-contour estimate on the counting window

On the counting window `q ∈ [q_edge + M √(log d / d), c₀ T]` the zeta-domain
and large-radius hypotheses of the conditional amplitude and lower-contour
results hold, once `T ≥ 40000 c₀`.  We record the saddle amplitude bounds, the
global amplitude ratio, the `C¹` bounds for the normalized local amplitude and
the lower-contour estimate in this unconditional form.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The counting window lies in the scale window and below `c₀ T`. -/
theorem countingWindow_subset_scale_window
    (d : ℕ) (hd : 2 ≤ d) {M c₀ q : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112) (hq : q ∈ countingWindow M c₀ d) :
    q ∈ Set.Ioc (edgeQ d) (scaleT d) ∧ q ≤ c₀ * scaleT d := by
  have hsqrt : 0 < Real.sqrt (Real.log d / d) :=
    Real.sqrt_pos.2 (div_pos (Real.log_pos (by exact_mod_cast hd)) (by positivity))
  refine ⟨⟨by nlinarith [hq.1, mul_pos hM hsqrt], ?_⟩, hq.2⟩
  have hc₀1 : c₀ ≤ 1 := by nlinarith [Real.pi_le_four]
  nlinarith [hq.2, scaleT_pos d (by omega)]

/-- On the scale window the saddle radius is positive and at most `2`. -/
theorem saddleRadius_pos_le_two_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < saddleRadius d (saddleAngle d q) ∧
      saddleRadius d (saddleAngle d q) ≤ 2 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  have hr := (saddleRadius_pos_and_eq d hd
    ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩).1
  have hmul := saddleRadius_mul_sinRatio_le_two d hd
    (show saddleAngle d q ∈ Set.Icc 0 (Real.pi / 2) from ⟨hα0.le, hαtop.le⟩)
  have hs := one_lt_sinRatio hα0 hαtop.le
  exact ⟨hr, by nlinarith⟩

/-- **Large radius on the counting window.** If `40000 c₀ ≤ T`, then
`R = T r ≥ 200`; moreover `0 < r`, `1 < R` and `R ≤ 2 T`. -/
theorem countingWindow_large_radius
    (d : ℕ) (hd : 2 ≤ d) {M c₀ q : ℝ} (hM : 0 < M) (hc₀ : 0 < c₀)
    (hcsmall : c₀ ≤ Real.pi / 112) (hscale : 40000 * c₀ ≤ scaleT d)
    (hq : q ∈ countingWindow M c₀ d) :
    200 ≤ scaleT d * saddleRadius d (saddleAngle d q) ∧
      0 < saddleRadius d (saddleAngle d q) ∧
      1 < scaleT d * saddleRadius d (saddleAngle d q) ∧
      scaleT d * saddleRadius d (saddleAngle d q) ≤ 2 * scaleT d := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, hqtop⟩ :=
    countingWindow_subset_scale_window d hd hM hcsmall hq
  have hT := scaleT_pos d hd1
  have hroot := sqrt_scale_div_le_scale_mul_saddleRadius d hd1 hsc hc₀ hqtop
  have h200 : (200 : ℝ) ≤ Real.sqrt (scaleT d / c₀) := by
    rw [show (200 : ℝ) = Real.sqrt (200 ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hc₀]
    nlinarith
  obtain ⟨hr, hr2⟩ := saddleRadius_pos_le_two_on_scale_window d hd1 hsc
  refine ⟨h200.trans hroot, hr, by linarith [h200.trans hroot], ?_⟩
  nlinarith

/-- **The `hK` geometry with `K = 2`.** For `0 ≤ ε ≤ 1` on the scale window,
`ℓ R ≤ 2 re w(θ_q + ℓ y)` for all `y ∈ [-1, 1]`. -/
theorem localWidth_mul_radius_le_two_re
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
        2 * (contourW d q (saddleTheta d q + localWidth ε d q * y)).re := by
  intro y hy
  have hr := (saddleRadius_pos_le_two_on_scale_window d hd hq).1
  have hR0 : 0 ≤ scaleT d * saddleRadius d (saddleAngle d q) :=
    mul_nonneg (scaleT_pos d hd).le hr.le
  have hmin0 := (min_angle_cos_pos_on_scale_window d hd hq).le
  have hw0 : 0 ≤ localWidth ε d q := by rw [localWidth]; positivity
  have hwidth : localWidth ε d q ≤ Real.cos (saddleAngle d q) := by
    rw [localWidth]
    have hm := min_le_right (saddleAngle d q) (Real.cos (saddleAngle d q))
    nlinarith
  have ht : |localWidth ε d q * y| ≤ Real.cos (saddleAngle d q) := by
    rw [abs_mul, abs_of_nonneg hw0]
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.2 hy) hw0]
  have hloc := contourW_local_re_ge d q _ hR0 ht
  nlinarith [mul_le_mul_of_nonneg_left hwidth hR0]

/-- On the counting window, the saddle point satisfies `4 ≤ re (1 / 2 + w(θ_q))`, i.e. it lies
in the zeta domain. -/
theorem countingWindow_saddle_zeta_domain
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hq : q ∈ countingWindow M c₀ d) :
    4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re := by
  simpa using countingWindow_local_zeta_domain d hd hlarge (ε := 0) hM
    hcsmall le_rfl zero_le_one hq 0 ⟨by norm_num, by norm_num⟩

/-- **Saddle amplitude nonvanishing on the counting window.** The amplitude at the saddle angle
`θ_q` is nonzero. -/
theorem countingWindow_saddle_amplitude_ne_zero
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hc₀ : 0 < c₀)
    (hcsmall : c₀ ≤ Real.pi / 112) (hscale : 40000 * c₀ ≤ scaleT d)
    (hq : q ∈ countingWindow M c₀ d) :
    amplitude d q (saddleTheta d q) ≠ 0 :=
  saddle_amplitude_ne_zero d q (countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq).1
    (countingWindow_saddle_zeta_domain d hd hlarge hM hcsmall hq)

/-- **Saddle amplitude lower bound on the counting window.**
`amplitudeLowerConst * R ^ (7/4) ≤ ‖a(θ_q)‖`, where `R = T r`. -/
theorem countingWindow_saddle_amplitude_lower
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hc₀ : 0 < c₀)
    (hcsmall : c₀ ≤ Real.pi / 112) (hscale : 40000 * c₀ ≤ scaleT d)
    (hq : q ∈ countingWindow M c₀ d) :
    amplitudeLowerConst *
        (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) ≤
      ‖amplitude d q (saddleTheta d q)‖ :=
  saddle_amplitude_lower d q (countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq).1
    (countingWindow_saddle_zeta_domain d hd hlarge hM hcsmall hq)

/-- **Saddle amplitude upper bound on the counting window.**
`‖a(θ_q)‖ ≤ amplitudeUpperConst * R ^ (7/4)`, where `R = T r`. -/
theorem countingWindow_saddle_amplitude_upper
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hc₀ : 0 < c₀)
    (hcsmall : c₀ ≤ Real.pi / 112) (hscale : 40000 * c₀ ≤ scaleT d)
    (hq : q ∈ countingWindow M c₀ d) :
    ‖amplitude d q (saddleTheta d q)‖ ≤
      amplitudeUpperConst *
        (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) :=
  saddle_amplitude_upper d q (countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq).1
    (countingWindow_saddle_zeta_domain d hd hlarge hM hcsmall hq)

/-- **Global amplitude ratio on the counting window**, with one absolute
constant: `‖a(θ)‖ / ‖a(θ_q)‖ ≤ C √T` on the whole circle. -/
theorem exists_countingWindow_global_amplitude_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d →
      4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d →
      ∀ {M c₀ q : ℝ}, 0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
        40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
        ∀ θ : ℝ, -Real.pi ≤ θ → θ ≤ Real.pi →
          ‖amplitude d q θ‖ / ‖amplitude d q (saddleTheta d q)‖ ≤
            C * Real.sqrt (scaleT d) := by
  obtain ⟨C, hC, hb⟩ := exists_global_amplitude_ratio_sqrt_scaleT 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro d hd hlarge M c₀ q hM hc₀ hcsmall hscale hq θ hθ1 hθ2
  obtain ⟨hR, -, -, hR2⟩ :=
    countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq
  exact hb d q θ hθ1 hθ2 hR hR2 (countingWindow_saddle_zeta_domain d hd hlarge hM hcsmall hq)

/-- **`C¹` bounds for the normalized local amplitude on the counting window**,
with the explicit constant `4 + 16 * zetaLogDerivMajorant`. -/
theorem countingWindow_localAmplitude_C1_bounds
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ ε q : ℝ} (hM : 0 < M) (hc₀ : 0 < c₀)
    (hcsmall : c₀ ≤ Real.pi / 112) (hscale : 40000 * c₀ ≤ scaleT d)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hq : q ∈ countingWindow M c₀ d) :
    (∀ y ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (localAmplitude ε d q) (localAmplitudeDeriv ε d q y) y) ∧
      ContinuousOn (localAmplitudeDeriv ε d q) (Icc (-1 : ℝ) 1) ∧
      (∀ y ∈ Icc (-1 : ℝ) 1,
        ‖localAmplitude ε d q y‖ ≤ 4 + 16 * zetaLogDerivMajorant) ∧
      (∀ y ∈ Icc (-1 : ℝ) 1,
        ‖localAmplitudeDeriv ε d q y‖ ≤ 4 + 16 * zetaLogDerivMajorant) ∧
      localAmplitude ε d q 0 = 1 := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  have h := localAmplitude_C1_bounds ε d q 2
    (countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq).1
    (localWidth_pos_on_scale_window d hd1 hsc hε0).le
    (localWidth_le_one_on_scale_window d hd1 hsc hε0.le hε1)
    (countingWindow_local_zeta_domain d hd hlarge hM hcsmall hε0.le hε1 hq)
    (localWidth_mul_radius_le_two_re d hd1 hsc hε0.le hε1)
  rwa [show (4 : ℝ) + 8 * 2 * zetaLogDerivMajorant = 4 + 16 * zetaLogDerivMajorant by ring] at h

/-- Existential form of `countingWindow_localAmplitude_C1_bounds`: one constant,
uniform in `ε`, `d`, `M`, `c₀` and `q`. -/
theorem exists_countingWindow_localAmplitude_C1_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d →
      4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d →
      ∀ {M c₀ ε q : ℝ}, 0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
        40000 * c₀ ≤ scaleT d → 0 < ε → ε ≤ 1 → q ∈ countingWindow M c₀ d →
        (∀ y ∈ Icc (-1 : ℝ) 1,
            HasDerivAt (localAmplitude ε d q) (localAmplitudeDeriv ε d q y) y) ∧
          ContinuousOn (localAmplitudeDeriv ε d q) (Icc (-1 : ℝ) 1) ∧
          (∀ y ∈ Icc (-1 : ℝ) 1, ‖localAmplitude ε d q y‖ ≤ C) ∧
          (∀ y ∈ Icc (-1 : ℝ) 1, ‖localAmplitudeDeriv ε d q y‖ ≤ C) ∧
          localAmplitude ε d q 0 = 1 :=
  ⟨4 + 16 * zetaLogDerivMajorant, by linarith [zetaLogDerivMajorant_nonneg],
    fun d hd hlarge => countingWindow_localAmplitude_C1_bounds d hd hlarge⟩

/-- `Λ ≥ 24π` implies the zeta-domain scale condition `Λ ≥ 4 (1 + log 2π)`. -/
theorem four_mul_one_add_log_two_pi_le_of_scaleLambda
    {d : ℕ} (hΛ : 24 * Real.pi ≤ scaleLambda d) :
    4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d := by
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
  nlinarith [Real.pi_pos]

/-- **Lower-contour estimate on the counting window.** Under the local phase hypotheses on
`lowerNormalizedPhase`, `1 ≤ effectiveN ε d q` and the tail bound off the local window,
`lowerContribution d q` differs from `leadingSaddle d q` by at most `‖leadingSaddle d q‖` times
a window error of order `effectiveN ε d q ^ (-1/10)` plus the tail term
`π B √(2π d ‖saddleHessian d q‖) e^{-g}`. -/
theorem countingWindow_lowerContribution_estimate
    {d : ℕ} {M c₀ q ε c Cp B g : ℝ} {p' p'' p''' : ℝ → ℂ}
    (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hM : 0 < M) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ Real.pi / 112)
    (hscale : 40000 * c₀ ≤ scaleT d) (hq : q ∈ countingWindow M c₀ d)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 1 ≤ effectiveN ε d q) (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hp : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hp''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp)
    (hp'''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-g)) :
    ‖lowerContribution d q - leadingSaddle d q‖ ≤
      ‖leadingSaddle d q‖ *
        (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
            effectiveN ε d q ^ (-(1:ℝ)/10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) *
            Real.exp (-g)) := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hlarge := four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  obtain ⟨hR, hr, -, -⟩ :=
    countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq
  obtain ⟨h1, h2⟩ := localWindow_contained_lower_semicircle d hd1 hsc hε0.le hε1
  exact lowerContribution_estimate_of_geometry' hd1 hr
    (localWidth_pos_on_scale_window d hd1 hsc hε0)
    (localWidth_le_one_on_scale_window d hd1 hsc hε0.le hε1)
    (saddleHessian_re_pos_on_scale_window d hd1 hΛ hsc) hn hc hCp hR
    (countingWindow_local_zeta_domain d hd hlarge hM hcsmall hε0.le hε1 hq)
    (localWidth_mul_radius_le_two_re d hd1 hsc hε0.le hε1)
    hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd h1 h2 htail

/-- **Oscillatory formula on the counting window.** `(rescaledJensen d).eval (-q)` differs from
`2 * re (leadingSaddle d q)` by at most twice the error bound of
`countingWindow_lowerContribution_estimate`. -/
theorem countingWindow_rescaledJensen_eval_sub_two_re_leadingSaddle_le
    {d : ℕ} {M c₀ q ε c Cp B g : ℝ} {p' p'' p''' : ℝ → ℂ}
    (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hM : 0 < M) (hc₀ : 0 < c₀) (hcsmall : c₀ ≤ Real.pi / 112)
    (hscale : 40000 * c₀ ≤ scaleT d) (hq : q ∈ countingWindow M c₀ d)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 1 ≤ effectiveN ε d q) (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hp : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hp''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp)
    (hp'''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-g)) :
    |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
      2 * ‖leadingSaddle d q‖ *
        (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
            effectiveN ε d q ^ (-(1:ℝ)/10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) *
            Real.exp (-g)) := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨-, hr, hRT, -⟩ :=
    countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq
  exact abs_sub_two_re_le_of_eq_add_star
    (rescaledJensen_eval_eq_lowerContribution_add_star d hd1 q (gammaCoeff_pos d).ne' hr hRT)
    (countingWindow_lowerContribution_estimate hd hΛ hM hc₀ hcsmall hscale hq
      hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd htail)

end RiemannJensen
