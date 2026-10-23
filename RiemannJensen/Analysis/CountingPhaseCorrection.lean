module

public import RiemannJensen.Analysis.LeadingSaddlePolar
public import RiemannJensen.Analysis.CountingZetaDomain
public import RiemannJensen.Analysis.CountingAmplitude

/-!
# Leading-saddle phase on the counting window

On the counting window, the leading saddle contribution has an exact polar form, and the phase
correction is continuous and bounded in absolute value by `8`.

## Main results

* `countingWindow_saddlePhasePoint_zeta_domain`: the saddle point lies in the half-plane
  `4 ≤ re (1 / 2 + w)` throughout the counting window.
* `countingWindow_saddleHessian_re_pos`: the saddle Hessian has positive real part on the
  counting window.
* `countingWindow_leadingSaddle_eq_norm_mul_exp_phase`: the polar form of the leading saddle
  contribution on the counting window.
* `continuousOn_phaseCorrection_countingWindow`: the phase correction is continuous on the
  counting window.
* `countingWindow_abs_phaseCorrection_le_eight`: the phase correction is bounded in absolute
  value by `8` on the counting window.
* `countingWindow_totalPhase_span_lower_of_action_bounds`: a lower bound for the change of the
  total phase between the endpoints of the counting window, in terms of action bounds there.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The saddle point itself is in the zeta half-plane throughout the counting
window. -/
theorem countingWindow_saddlePhasePoint_zeta_domain
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112)
    (hq : q ∈ countingWindow M c₀ d) :
    4 ≤ (1 / 2 + saddlePhasePoint d q).re := by
  simpa [saddlePhasePoint, saddleTheta, localWidth] using
    countingWindow_local_zeta_domain d hd hlarge (ε := 0) hM hcsmall (by norm_num) (by norm_num)
      hq 0 (by simp)

/-- The saddle Hessian has positive real part throughout the counting window. -/
theorem countingWindow_saddleHessian_re_pos
    (d : ℕ) (hd : 2 ≤ d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112)
    (hq : q ∈ countingWindow M c₀ d) :
    0 < (saddleHessian d q).re := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hscale := (countingWindow_subset_scale_window d hd hM hcsmall hq).1
  have hDre := (saddleHessian_re_bounds_on_scale_window d hd1 hΛ hscale).1
  rcases saddle_inverse_on_scale_window d hd1 hscale with ⟨ha, hb, -⟩
  have hs : 0 < Real.sin (saddleAngle d q) :=
    Real.sin_pos_of_pos_of_lt_pi ha (hb.trans (by linarith [Real.pi_pos]))
  nlinarith [sq_pos_of_pos hs]

/-- Exact polar form of the leading saddle contribution on the counting
window, with all zeta, Gamma and Hessian domain conditions discharged. -/
theorem countingWindow_leadingSaddle_eq_norm_mul_exp_phase
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112)
    (hq : q ∈ countingWindow M c₀ d) :
    leadingSaddle d q =
      (‖leadingSaddle d q‖ : ℂ) *
        Complex.exp (Complex.I *
          ((d : ℝ) * saddleAction d q + phaseCorrection d q)) := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hscale := (countingWindow_subset_scale_window d hd hM hcsmall hq).1
  exact leadingSaddle_eq_norm_mul_exp_phase d hd1 hscale
    (countingWindow_saddlePhasePoint_zeta_domain
      d hd hlarge hM hcsmall hq)
    (saddlePhasePoint_mem_grDomain_on_scale_window d hd1 hscale)
    (countingWindow_saddleHessian_re_pos d hd hΛ hM hcsmall hq)

/-- The explicit phase correction is continuous on the complete counting
window. -/
theorem continuousOn_phaseCorrection_countingWindow
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112) :
    ContinuousOn (phaseCorrection d) (countingWindow M c₀ d) := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hsub : countingWindow M c₀ d ⊆ Set.Ioc (edgeQ d) (scaleT d) :=
    fun q hq => (countingWindow_subset_scale_window d hd hM hcsmall hq).1
  have hα : ContinuousOn (saddleAngle d) (countingWindow M c₀ d) :=
    ((continuousOn_saddleAngle_on_branch d hd1).mono fun _ hq =>
      ⟨hq.1.le, (hq.2.trans_lt (scaleT_lt_saddleQ_pi_div_two d hd1)).le⟩).mono hsub
  have hw : ContinuousOn (saddlePhasePoint d) (countingWindow M c₀ d) :=
    continuousOn_saddlePhasePoint d hd1 hα fun q hq => by
      rcases saddle_inverse_on_scale_window d hd1 (hsub hq) with ⟨ha, hb, -⟩
      exact ⟨ha.le, hb.le⟩
  exact continuousOn_phaseCorrection_of_geometric_inputs d hα hw
    (fun _ hq => countingWindow_saddlePhasePoint_zeta_domain d hd hlarge hM hcsmall hq)
    (fun _ hq => saddlePhasePoint_mem_grDomain_on_scale_window d hd1 (hsub hq))
    ((continuousOn_saddleHessian_on_scale_window d hd1).mono hsub)
    (fun _ hq => countingWindow_saddleHessian_re_pos d hd hΛ hM hcsmall hq)

/-- The explicit phase correction has the absolute bound `8` throughout the
complete counting window. -/
theorem countingWindow_abs_phaseCorrection_le_eight
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112)
    (hq : q ∈ countingWindow M c₀ d) :
    |phaseCorrection d q| ≤ 8 := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hscale := (countingWindow_subset_scale_window d hd hM hcsmall hq).1
  rcases saddle_inverse_on_scale_window d hd1 hscale with ⟨ha, hb, -⟩
  exact abs_phaseCorrection_le_eight d ⟨ha.le, hb.le⟩
    (countingWindow_saddlePhasePoint_zeta_domain
      d hd hlarge hM hcsmall hq)
    (saddlePhasePoint_re_nonneg_on_scale_window d hd1 hscale)
    (four_lt_norm_saddlePhasePoint_on_scale_window d hd1 hscale).le
    (countingWindow_saddleHessian_re_pos d hd hΛ hM hcsmall hq)

/-- On a nonempty counting window, if the saddle action is at most `A` at the left endpoint and at
least `B` at the right endpoint, then the total phase increases between the endpoints by at least
`d * (B - A) - 16`. -/
theorem countingWindow_totalPhase_span_lower_of_action_bounds
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ A B : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty :
      edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d)
    (hedge :
      saddleAction d (edgeQ d + M * Real.sqrt (Real.log d / d)) ≤ A)
    (htail : B ≤ saddleAction d (c₀ * scaleT d)) :
    (d : ℝ) * (B - A) - 16 ≤
      ((d : ℝ) * saddleAction d (c₀ * scaleT d) +
          phaseCorrection d (c₀ * scaleT d)) -
        ((d : ℝ) *
            saddleAction d (edgeQ d + M * Real.sqrt (Real.log d / d)) +
          phaseCorrection d
            (edgeQ d + M * Real.sqrt (Real.log d / d))) := by
  have hspan := totalPhase_span_lower_of_eight_bounds d
    (countingWindow_abs_phaseCorrection_le_eight d hd hlarge hΛ hM hcsmall
      (q := edgeQ d + M * Real.sqrt (Real.log d / d)) ⟨le_rfl, hnonempty⟩)
    (countingWindow_abs_phaseCorrection_le_eight d hd hlarge hΛ hM hcsmall
      (q := c₀ * scaleT d) ⟨hnonempty, le_rfl⟩)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hedge hd0,
    mul_le_mul_of_nonneg_left htail hd0]

end RiemannJensen
