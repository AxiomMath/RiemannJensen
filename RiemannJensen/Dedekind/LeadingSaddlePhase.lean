module

public import RiemannJensen.Dedekind.PhaseObjects
public import RiemannJensen.Dedekind.EulerProductBridge
public import RiemannJensen.Dedekind.EulerLogComparison
public import RiemannJensen.Dedekind.ZetaLogDerivative
public import RiemannJensen.Dedekind.ContourWindowGeometry
public import RiemannJensen.Dedekind.SaddleImplicitCalculus
public import RiemannJensen.Dedekind.SaddleHessianEventual
public import RiemannJensen.Dedekind.SaddleActionDerivatives
public import RiemannJensen.Dedekind.ActionEffective

/-!
# Phase estimates for the Dedekind leading saddle term

For a number field `K`, this file identifies `Dedekind.leadingSaddle` with
`dedekindLeadingSaddle` on the zeta range, writes the leading saddle term in polar form, and
establishes uniform bounds, continuity and an endpoint span estimate for its phase on small
counting windows.

## Main results

* `dedekind_phase_leading_eq`: `Dedekind.leadingSaddle` equals `dedekindLeadingSaddle` when
  `4 ≤ (1 / 2 + Dedekind.saddlePoint K d q).re`.
* `dedekind_leading_polar`: polar form of `dedekindLeadingSaddle` with phase
  `d * Dedekind.saddleAction K d q + Dedekind.phaseCorrection K d q`.
* `eventually_dedekind_leading_polar_on_window`: the polar form holds eventually on small
  counting windows.
* `dedekind_phase_correction_bound`: `Dedekind.phaseCorrection` is eventually uniformly bounded
  on small counting windows.
* `dedekind_phase_correction_continuous`: `Dedekind.phaseCorrection` is eventually continuous
  on small counting windows.
* `dedekind_phase_span`: lower bound for the phase increase between the endpoints of a counting
  window.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

@[simp] private theorem phase_scaleT_eq (d : ℕ) :
    Dedekind.scaleT K d = dedekindScaleT K d := rfl
@[simp] private theorem phase_scaleLambda_eq (d : ℕ) :
    Dedekind.scaleLambda K d = dedekindScaleLambda K d := rfl
@[simp] private theorem phase_saddleRadius_eq (d : ℕ) (a : ℝ) :
    Dedekind.saddleRadius K d a = dedekindSaddleRadius K d a := rfl
@[simp] private theorem phase_edgeQ_eq (d : ℕ) :
    Dedekind.edgeQ K d = dedekindEdgeQ K d := rfl
@[simp] private theorem phase_saddleAngle_eq (d : ℕ) (q : ℝ) :
    Dedekind.saddleAngle K d q = dedekindSaddleAngle K d q := rfl
@[simp] private theorem phase_saddle_eq (d : ℕ) (q : ℝ) :
    Dedekind.saddle K d q = dedekindSaddle K d q := rfl
@[simp] private theorem phase_localWidth_eq (d : ℕ) (q : ℝ) :
    Dedekind.localWidth K d q = dedekindLocalWidth K d q := rfl
@[simp] private theorem phase_contourW_eq (d : ℕ) (q t : ℝ) :
    Dedekind.contourW K d q t = dedekindContourW K d q t := rfl
@[simp] private theorem phase_saddleHessian_eq (d : ℕ) (q : ℝ) :
    Dedekind.saddleHessian K d q = dedekindSaddleHessian K d q := rfl
@[simp] private theorem phase_saddleAction_eq (d : ℕ) (q : ℝ) :
    Dedekind.saddleAction K d q = dedekindSaddleAction K d q := rfl
@[simp] private theorem phase_edgeOffset_eq (M : ℝ) (d : ℕ) :
    Dedekind.edgeOffset M d = dedekindEdgeOffset M d := rfl
@[simp] private theorem phase_countingWindow_eq (M c : ℝ) (d : ℕ) :
    Dedekind.countingWindow K M c d = dedekindCountingWindow K M c d := rfl
@[simp] private theorem phase_explicitHessian_eq (L r a : ℝ) :
    Dedekind.explicitSaddleHessianAtLambda L r a = explicitSaddleHessianAtLambda L r a := rfl
@[simp] private theorem phase_cK_eq :
    Dedekind.cK K = dedekindLeadingConstant K := rfl
@[simp] private theorem phase_muK_eq :
    Dedekind.muK K = dedekindPowerExponent K := rfl

@[simp] private theorem phase_gammaRemainder_eq (w : ℂ) :
    Dedekind.dedekindGammaRemainder K w = dedekindGammaRemainder K w := by
  have hsqrt : Complex.sqrt ((2 * Real.pi : ℝ) : ℂ) = (Real.sqrt (2 * Real.pi) : ℂ) :=
    Complex.sqrt_of_nonneg
      (RCLike.nonneg_iff_exists_ofReal.mpr ⟨2 * Real.pi, by positivity, rfl⟩)
  unfold Dedekind.dedekindGammaRemainder dedekindGammaRemainder Dedekind.gammaRemainderReal
    Dedekind.gammaRemainderComplex dedekindGammaRemainderReal dedekindGammaRemainderComplex
  rw [← hsqrt, ← Complex.cpow_eq_pow, ← Complex.cpow_eq_pow]
  push_cast
  rfl

@[simp] private theorem phase_phase_eq (d : ℕ) (q : ℝ) (u : ℂ) :
    Dedekind.phase K d q u = dedekindSaddlePhase K d q u := rfl

private theorem dedekind_eulerLogExp : Dedekind.EulerLogExp K := by
  intro s hs
  rw [Dedekind.analyticDedekindZeta_eq_raw K hs, ← analyticDedekindZeta_eq_raw K s hs]
  simpa [Dedekind.dedekindEulerLog, dedekindEulerLog, dedekindEulerLogTerm,
    add_mul] using dedekindEulerLog_exp K hs

private theorem dedekind_eulerLogBound : Dedekind.EulerLogBound K := by
  intro s hs
  simpa [Dedekind.dedekindEulerLog, dedekindEulerLog, dedekindEulerLogTerm,
    add_mul] using norm_dedekindEulerLog_le_log_riemannZeta K hs

private theorem dedekind_contourZetaDomain : Dedekind.ContourZetaDomain K := by
  unfold Dedekind.ContourZetaDomain
  simpa using dedekind_contour_zeta_domain K

private theorem dedekind_saddleAngleDifferentiable : Dedekind.SaddleAngleDifferentiable K := by
  unfold Dedekind.SaddleAngleDifferentiable
  intro d hd
  rw [show Dedekind.saddleAngle K d = dedekindSaddleAngle K d from
    funext (phase_saddleAngle_eq K d), phase_edgeQ_eq, phase_scaleT_eq]
  exact dedekind_saddle_angle_differentiable K d hd

private theorem dedekind_saddleBranchDifferentiable : Dedekind.SaddleBranchDifferentiable K := by
  unfold Dedekind.SaddleBranchDifferentiable
  intro d hd
  rw [show Dedekind.saddle K d = dedekindSaddle K d from
    funext (phase_saddle_eq K d), phase_edgeQ_eq, phase_scaleT_eq]
  exact dedekind_saddle_branch_differentiable K d hd

private theorem dedekind_saddleInverseRange : Dedekind.SaddleInverseRange K := by
  unfold Dedekind.SaddleInverseRange
  intro d hd q hedge hq
  simpa using dedekindSaddle_inverse_range K d hd (q := q) ⟨hedge, hq⟩

/-- The Euler logarithm `dedekindEulerLog K` is complex differentiable on `1 < re s`. -/
theorem differentiableAt_dedekindEulerLog {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (dedekindEulerLog K) s := by
  obtain ⟨a, ha, hsa⟩ := exists_between hs
  have hsumDiff : DifferentiableAt ℂ
      (fun z : ℂ => ∑' p : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K), dedekindPrimeLogFactor K p z) s :=
    (Complex.differentiableOn_tsum_of_summable_norm (summable_dedekindEulerLogMajorant K ha)
      (fun p z hz =>
        (hasDerivAt_dedekindPrimeLogFactor K p
          (ha.trans hz)).differentiableAt.differentiableWithinAt)
      (isOpen_lt continuous_const continuous_re)
      (fun p z hz => norm_dedekindPrimeLogFactor_le K ha p (le_of_lt hz))
      s hsa).differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hsa)
  exact hsumDiff.congr_of_eventuallyEq (dedekindEulerLog_eventuallyEq_tsum K hs)

/-- The Euler logarithm `dedekindEulerLog K` is continuous on the half-plane `1 < re s`. -/
theorem continuousOn_dedekindEulerLog :
    ContinuousOn (dedekindEulerLog K) {s : ℂ | 1 < s.re} := fun _ hs =>
  (differentiableAt_dedekindEulerLog K hs).continuousAt.continuousWithinAt

private theorem dedekind_eulerLogContinuous : Dedekind.EulerLogContinuous K := by
  unfold Dedekind.EulerLogContinuous
  have heq : Dedekind.dedekindEulerLog K = dedekindEulerLog K := by
    funext s
    simp [Dedekind.dedekindEulerLog, dedekindEulerLog, dedekindEulerLogTerm, add_mul]
  exact heq ▸ continuousOn_dedekindEulerLog K

private theorem dedekind_hessianFormula : Dedekind.HessianFormula K := by
  unfold Dedekind.HessianFormula
  intro d hd q hedge hq
  have hmem : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) :=
    ⟨hedge, hq⟩
  have hrange := dedekindSaddle_inverse_range K d hd hmem
  have h := dedekindSaddleHessian_eq_explicit K d hd
    (α := dedekindSaddleAngle K d q) hrange
  rw [dedekindSaddle_inverse K d hd hmem] at h
  simpa using h

private theorem dedekind_hessianRealBounds : Dedekind.HessianRealBounds K := by
  unfold Dedekind.HessianRealBounds
  obtain ⟨D, hD1, hD⟩ := eventually_dedekindSaddleHessian_re_bounds K
  filter_upwards [eventually_ge_atTop D] with d hd
  intro q hedge hq
  have hd1 : 1 ≤ d := hD1.trans hd
  have hmem : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hedge, hq⟩
  have hrange := dedekindSaddle_inverse_range K d hd1 hmem
  have h := hD d hd (dedekindSaddleAngle K d q) hrange
  rw [dedekindSaddle_inverse K d hd1 hmem] at h
  simpa using h

private theorem dedekind_actionEdge : Dedekind.ActionEdge K := by
  unfold Dedekind.ActionEdge
  intro M c hM hc d hd hL hne
  have hne' : (dedekindCountingWindow K M c d).Nonempty := hne
  rw [dedekindCountingWindow, Set.nonempty_Icc] at hne'
  simpa using dedekindSaddle_action_edge K M c d hM hc hd hL hne'

private theorem dedekind_actionTail : Dedekind.ActionTail K := by
  unfold Dedekind.ActionTail
  obtain ⟨C, q₁, hC, hq₁, h⟩ := dedekindSaddle_action_tail K
  refine ⟨C, q₁, hC, hq₁, ?_⟩
  intro d hd q hq hqT
  have hrpow : q ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt q := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (hq₁.trans_le hq).le]
    norm_num
  rw [hrpow]
  simpa [div_eq_mul_inv] using h d hd q hq hqT

private theorem dedekind_scaleLambdaLower : Dedekind.ScaleLambdaLower K := by
  unfold Dedekind.ScaleLambdaLower
  obtain ⟨D, hD⟩ := eventually_log_le_dedekindScaleLambda K
  filter_upwards [eventually_ge_atTop D] with d hd
  simpa using hD d hd

private theorem dedekind_windowNonempty : Dedekind.WindowNonempty K := by
  unfold Dedekind.WindowNonempty
  intro M c hM hc
  simpa using dedekind_window_nonempty K M c hM hc

/-- If `4 ≤ (1 / 2 + Dedekind.saddlePoint K d q).re`, then `Dedekind.leadingSaddle K d q`
equals `dedekindLeadingSaddle K d q`. -/
theorem dedekind_phase_leading_eq (d : ℕ) (q : ℝ)
    (hZ : 4 ≤ (1 / 2 + Dedekind.saddlePoint K d q).re) :
    Dedekind.leadingSaddle K d q = dedekindLeadingSaddle K d q := by
  have hs : 1 < (1 / 2 + Dedekind.saddlePoint K d q).re := by linarith
  have hs' : 1 < (1 / 2 + Dedekind.contourW K d q
      (-2 * Dedekind.saddleAngle K d q)).re := by
    simpa [Dedekind.saddlePoint] using hs
  have hsroot : 1 < (1 / 2 + dedekindContourW K d q
      (-2 * dedekindSaddleAngle K d q)).re := by simpa using hs'
  have hzD := Dedekind.analyticDedekindZeta_eq_raw K hs'
  have hz := analyticDedekindZeta_eq_raw K
    (1 / 2 + dedekindContourW K d q (-2 * dedekindSaddleAngle K d q)) hsroot
  have hamp : Dedekind.dedekindAmplitude K d q
      (-2 * Dedekind.saddleAngle K d q) =
      dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q) := by
    unfold Dedekind.dedekindAmplitude dedekindAmplitude
    rw [hzD, hz]
    simp only [phase_cK_eq, phase_muK_eq, phase_contourW_eq,
      phase_saddleAngle_eq, phase_gammaRemainder_eq, ← Complex.cpow_eq_pow]
  unfold Dedekind.leadingSaddle dedekindLeadingSaddle
  rw [hamp]
  simp only [phase_phase_eq, phase_saddle_eq, phase_saddleHessian_eq]

/-- If `4 ≤ (1 / 2 + Dedekind.saddlePoint K d q).re`, then `dedekindLeadingSaddle K d q` is
its norm times `exp (i (d * Dedekind.saddleAction K d q + Dedekind.phaseCorrection K d q))`. -/
theorem dedekind_leading_polar (d : ℕ) (q : ℝ)
    (hZ : 4 ≤ (1 / 2 + Dedekind.saddlePoint K d q).re) :
    dedekindLeadingSaddle K d q =
      (‖dedekindLeadingSaddle K d q‖ : ℂ) *
        Complex.exp (Complex.I *
          (((d : ℝ) * Dedekind.saddleAction K d q +
            Dedekind.phaseCorrection K d q : ℝ) : ℂ)) := by
  rw [← dedekind_phase_leading_eq K d q hZ]
  exact Dedekind.leadingSaddle_eq_norm_mul_exp_phase K (dedekind_eulerLogExp K) d q hZ

/-- For counting windows with sufficiently small parameter `c₀`, eventually in `d`, the term
`dedekindLeadingSaddle K d q` at every `q` of the window is its norm times
`exp ((d * Dedekind.saddleAction K d q + Dedekind.phaseCorrection K d q) * I)`. -/
theorem eventually_dedekind_leading_polar_on_window :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ M c₀ : ℝ,
      0 < M → 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ Dedekind.countingWindow K M c₀ d,
        dedekindLeadingSaddle K d q =
          (‖dedekindLeadingSaddle K d q‖ : ℂ) *
            Complex.exp ((((d : ℝ) * Dedekind.saddleAction K d q +
              Dedekind.phaseCorrection K d q : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨c₁, hc₁, hlocal⟩ :=
    Dedekind.eventually_zetaRange_on_window K (dedekind_contourZetaDomain K)
  refine ⟨c₁, hc₁, fun M c₀ hM hc₀ hc₀c₁ => ?_⟩
  filter_upwards [hlocal M c₀ hM hc₀ hc₀c₁] with d hd q hq
  rw [mul_comm _ Complex.I]
  exact dedekind_leading_polar K d q (hd q hq)

/-- For every `M > 0` and sufficiently small `c₀ > 0` there is `C > 0` such that, eventually
in `d`, `|Dedekind.phaseCorrection K d q| ≤ C` on the counting window. -/
theorem dedekind_phase_correction_bound :
    ∀ M : ℝ, 0 < M → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ d : ℕ in atTop, ∀ q ∈ Dedekind.countingWindow K M c₀ d,
          |Dedekind.phaseCorrection K d q| ≤ C :=
  Dedekind.exists_abs_phaseCorrection_le K (dedekind_contourZetaDomain K)
    (dedekind_eulerLogBound K)

/-- For counting windows with sufficiently small parameter `c₀`, eventually in `d`, the phase
correction `Dedekind.phaseCorrection K d` is continuous on the window. -/
theorem dedekind_phase_correction_continuous :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ M c₀ : ℝ,
      0 < M → 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop,
        ContinuousOn (Dedekind.phaseCorrection K d)
          (Dedekind.countingWindow K M c₀ d) :=
  Dedekind.continuousOn_phaseCorrection K (dedekind_contourZetaDomain K)
    (dedekind_eulerLogContinuous K) (dedekind_saddleAngleDifferentiable K)
    (dedekind_saddleBranchDifferentiable K) (dedekind_saddleInverseRange K)
    (dedekind_hessianFormula K) (dedekind_hessianRealBounds K)

/-- For every `M > 0` and sufficiently small `c₀ > 0` there is `C` such that, eventually in
`d`, the phase `d * Dedekind.saddleAction K d q + Dedekind.phaseCorrection K d q` increases
from `q = Dedekind.edgeQ K d + Dedekind.edgeOffset M d` to `q = Dedekind.upperEndpoint K c₀ d`
by at least `π d - C d (Dedekind.upperEndpoint K c₀ d ^ (-1/2) +
Dedekind.edgeOffset M d ^ (3/2)) - C`. -/
theorem dedekind_phase_span :
    ∀ M : ℝ, 0 < M → ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ → ∃ C : ℝ,
        ∀ᶠ d : ℕ in atTop,
          Real.pi * d - C * d *
              (Dedekind.upperEndpoint K c₀ d ^ (-(1 / 2 : ℝ)) +
                Dedekind.edgeOffset M d ^ (3 / 2 : ℝ)) - C ≤
            ((d : ℝ) * Dedekind.saddleAction K d
                (Dedekind.upperEndpoint K c₀ d) +
              Dedekind.phaseCorrection K d (Dedekind.upperEndpoint K c₀ d)) -
            ((d : ℝ) * Dedekind.saddleAction K d
                (Dedekind.edgeQ K d + Dedekind.edgeOffset M d) +
              Dedekind.phaseCorrection K d
                (Dedekind.edgeQ K d + Dedekind.edgeOffset M d)) :=
  Dedekind.phaseSpan_lower K (dedekind_contourZetaDomain K) (dedekind_eulerLogBound K)
    (dedekind_actionEdge K) (dedekind_actionTail K) (dedekind_scaleLambdaLower K)
    (dedekind_windowNonempty K)

end

end RiemannJensen
