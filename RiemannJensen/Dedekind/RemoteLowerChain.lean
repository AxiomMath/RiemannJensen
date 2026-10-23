module

public import RiemannJensen.Dedekind.LocalGaussianAdapter
public import RiemannJensen.Dedekind.AmplitudeBounds

/-!
# Remote error and square-root normalization for the Dedekind saddle

For a number field `K`, this file bounds the remote exponential error on a field-dependent
counting window, identifies the Gaussian main term with the reciprocal square root
`1 / √(2 π d D)` of the saddle Hessian, and estimates the lower semicircle contribution of the
Dedekind saddle contour against the leading saddle term.

## Main definitions

* `dedekindOscillationM`: The edge constant `√((N + 4) / c)` of the counting window.
* `dedekindOscillationC0`: The upper-window constant `c N / (4 π (N + 4))`.

## Main results

* `eventually_dedekind_remote_error`: On the counting window, `d ^ (N + 1)` times the remote
  exponential is eventually at most `d⁻³`.
* `dedekind_principal_root_saddle`: The Gaussian main term at the saddle is `1 / √(2 π d D)`.
* `dedekind_saddle_contour_point`: The saddle is the lower contour point at angle `-2 α`.
* `dedekind_lower_contribution_conditional`: The lower contribution differs from the leading
  saddle term by a relative error controlled by the `C³/C¹` and complementary-arc hypotheses.
-/

@[expose] public section

namespace RiemannJensen

open _root_.Complex Set Filter
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The field-dependent edge constant `√((N + 4) / c)`, where `N` is the degree of `K` and `c`
is `dedekindRemoteGapConst`. -/
def dedekindOscillationM : ℝ :=
  Real.sqrt (((dedekindDegree K : ℝ) + 4) / dedekindRemoteGapConst)

/-- The field-dependent upper-window constant `c N / (4 π (N + 4))`, where `N` is the degree of
`K` and `c` is `dedekindRemoteGapConst`. -/
def dedekindOscillationC0 : ℝ :=
  dedekindRemoteGapConst * (dedekindDegree K : ℝ) /
    (4 * Real.pi * ((dedekindDegree K : ℝ) + 4))

/-- The edge constant `dedekindOscillationM K` is positive. -/
theorem dedekindOscillationM_pos : 0 < dedekindOscillationM K :=
  Real.sqrt_pos.2 (div_pos (by positivity) dedekindRemoteGapConst_pos)

/-- The square of the edge constant `dedekindOscillationM K` is `(N + 4) / c`. -/
theorem sq_dedekindOscillationM :
    dedekindOscillationM K ^ 2 = ((dedekindDegree K : ℝ) + 4) / dedekindRemoteGapConst :=
  Real.sq_sqrt (div_pos (by positivity) dedekindRemoteGapConst_pos).le

/-- The upper-window constant `dedekindOscillationC0 K` is positive. -/
theorem dedekindOscillationC0_pos : 0 < dedekindOscillationC0 K :=
  div_pos (mul_pos dedekindRemoteGapConst_pos (mod_cast dedekindDegree_pos K)) (by positivity)

/-- The edge point `dedekindEdgeQ K d` is nonnegative. -/
theorem dedekindEdgeQ_nonneg (d : ℕ) (hd : 1 ≤ d) : 0 ≤ dedekindEdgeQ K d := by
  have hΛ := dedekindScaleLambda_pos K d hd
  unfold dedekindEdgeQ dedekindSaddleQ saddleQAtLambda
  rw [sinRatio_zero]
  have hr : 0 < saddleRadiusAtLambda (dedekindScaleLambda K d) 0 := by
    simpa [dedekindSaddleRadius] using dedekindSaddleRadius_pos K d hd
      ⟨le_rfl, by positivity⟩
  have hk : 0 < saddleKappa := by
    rw [saddleKappa]
    positivity
  positivity

/-- If `q` lies at least `dedekindOscillationM K * √(log d / d)` above the edge point, then
`(N + 4) log d ≤ d c (q - dedekindEdgeQ K d)²`. -/
theorem log_le_mul_sq_of_oscillationM_le {d : ℕ} {q : ℝ} (hd : (1 : ℝ) < d)
    (ht : dedekindOscillationM K * Real.sqrt (Real.log (d : ℝ) / d) ≤ q - dedekindEdgeQ K d) :
    ((dedekindDegree K : ℝ) + 4) * Real.log d ≤
      d * (dedekindRemoteGapConst * (q - dedekindEdgeQ K d) ^ 2) := by
  have hdpos : (0 : ℝ) < d := by linarith
  have hlogpos : 0 < Real.log (d : ℝ) := Real.log_pos hd
  have hc := dedekindRemoteGapConst_pos
  have hM := dedekindOscillationM_pos K
  have hsq := pow_le_pow_left₀ (by positivity) ht 2
  rw [mul_pow, sq_dedekindOscillationM, Real.sq_sqrt (by positivity)] at hsq
  calc
    ((dedekindDegree K : ℝ) + 4) * Real.log d =
        d * (dedekindRemoteGapConst *
          ((((dedekindDegree K : ℝ) + 4) / dedekindRemoteGapConst) *
            (Real.log d / d))) := by field_simp
    _ ≤ d * (dedekindRemoteGapConst * (q - dedekindEdgeQ K d) ^ 2) := by
      gcongr

/-- If `0 < q ≤ dedekindOscillationC0 K * dedekindScaleT K d` and
`log d ≤ dedekindScaleLambda K d`, then `(N + 4) log d ≤ d c q⁻¹`. -/
theorem log_le_mul_inv_of_le_oscillationC0_mul {d : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq0 : 0 < q)
    (hlog : Real.log d ≤ dedekindScaleLambda K d)
    (hqtop : q ≤ dedekindOscillationC0 K * dedekindScaleT K d) :
    ((dedekindDegree K : ℝ) + 4) * Real.log d ≤ d * (dedekindRemoteGapConst * q⁻¹) := by
  have hc := dedekindRemoteGapConst_pos
  have hN : (0 : ℝ) < dedekindDegree K := mod_cast dedekindDegree_pos K
  have hC0 := dedekindOscillationC0_pos K
  have hT := dedekindScaleT_pos K d hd
  have hprod := dedekindScale_product K d hd
  have htailval :
      d * (dedekindRemoteGapConst * (dedekindOscillationC0 K * dedekindScaleT K d)⁻¹) =
        ((dedekindDegree K : ℝ) + 4) * dedekindScaleLambda K d := by
    unfold dedekindOscillationC0
    field_simp
    nlinarith
  calc
    _ ≤ ((dedekindDegree K : ℝ) + 4) * dedekindScaleLambda K d := by gcongr
    _ = d * (dedekindRemoteGapConst *
        (dedekindOscillationC0 K * dedekindScaleT K d)⁻¹) := htailval.symm
    _ ≤ d * (dedekindRemoteGapConst * q⁻¹) := by gcongr

/-- For all sufficiently large `d` and every `q` in the counting window with constants
`dedekindOscillationM K` and `dedekindOscillationC0 K`, the polynomial loss `d ^ (N + 1)` times
the remote exponential is at most `d⁻³`. -/
theorem eventually_dedekind_remote_error :
    ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ dedekindCountingWindow K (dedekindOscillationM K)
          (dedekindOscillationC0 K) d,
        (d : ℝ) ^ (dedekindDegree K + 1) *
            Real.exp (-(d * (dedekindRemoteGapConst *
              min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹))) ≤
          1 / (d : ℝ) ^ 3 := by
  obtain ⟨DL, hDL⟩ := eventually_log_le_dedekindScaleLambda K
  filter_upwards [eventually_ge_atTop (max DL 2)] with d hd
  intro q hq
  have hd2 : 2 ≤ d := (le_max_right _ _).trans hd
  have hd1 : 1 ≤ d := by lia
  have hdR : (1 : ℝ) < d := mod_cast hd2
  have hdpos : (0 : ℝ) < d := by positivity
  have hlogpos : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  have hM := dedekindOscillationM_pos K
  have hedge0 := dedekindEdgeQ_nonneg K d hd1
  have ht : dedekindOscillationM K *
      Real.sqrt (Real.log (d : ℝ) / d) ≤ q - dedekindEdgeQ K d := by
    have hlo := hq.1
    unfold dedekindCountingWindow dedekindEdgeOffset at hlo
    linarith
  have hsqrt : 0 < Real.sqrt (Real.log (d : ℝ) / d) := by positivity
  have hq0 : 0 < q := by nlinarith [mul_pos hM hsqrt]
  have hqtop : q ≤ dedekindOscillationC0 K * dedekindScaleT K d := by
    simpa [dedekindCountingWindow, dedekindUpperEndpoint] using hq.2
  have hmin : ((dedekindDegree K : ℝ) + 4) * Real.log d ≤
      d * (dedekindRemoteGapConst *
        min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹) := by
    rcases le_total ((q - dedekindEdgeQ K d) ^ 2) q⁻¹ with h | h
    · rw [min_eq_left h]
      exact log_le_mul_sq_of_oscillationM_le K hdR ht
    · rw [min_eq_right h]
      exact log_le_mul_inv_of_le_oscillationC0_mul K hd1 hq0
        (hDL d ((le_max_left _ _).trans hd)) hqtop
  have hexp : Real.exp (-(d * (dedekindRemoteGapConst *
      min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹))) ≤
      ((d : ℝ) ^ (dedekindDegree K + 4))⁻¹ := by
    rw [← Real.exp_log (pow_pos hdpos _), ← Real.exp_neg, Real.log_pow]
    apply Real.exp_le_exp.2
    push_cast
    linarith
  calc
    (d : ℝ) ^ (dedekindDegree K + 1) *
          Real.exp (-(d * (dedekindRemoteGapConst *
            min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹)))
      ≤ (d : ℝ) ^ (dedekindDegree K + 1) *
          ((d : ℝ) ^ (dedekindDegree K + 4))⁻¹ := by gcongr
    _ = 1 / (d : ℝ) ^ 3 := by
      field_simp
      ring

/-- At the Dedekind saddle, with Hessian `D` of positive real part and positive local width
`ℓ`, the Gaussian main term `ℓ (π / ((n / 2) (D / ‖D‖))) ^ (1 / 2) / (2 π)` with effective
size `n = dedekindEffectiveN K d q` equals `1 / √(2 π d D)`. -/
theorem dedekind_principal_root_saddle {d : ℕ} (hd : 0 < d) {q : ℝ}
    (hD : 0 < (dedekindSaddleHessian K d q).re) (hℓ : 0 < dedekindLocalWidth K d q) :
    (dedekindLocalWidth K d q : ℂ) * (((Real.pi : ℂ) /
        ((((dedekindEffectiveN K d q) / 2 : ℝ) : ℂ) *
          (dedekindSaddleHessian K d q /
            (‖dedekindSaddleHessian K d q‖ : ℂ)))) ^ (1 / 2 : ℂ)) /
        (2 * Real.pi) =
      1 / Complex.sqrt
        (2 * Real.pi * d * dedekindSaddleHessian K d q) := by
  simpa [dedekindEffectiveN] using
    gaussian_main_term_normalization hD (dd := (d : ℝ)) (mod_cast hd) hℓ

/-- The saddle is the lower contour point at angle `-2 α`. -/
theorem dedekind_saddle_contour_point (d : ℕ) (q : ℝ) :
    dedekindLowerContourPoint K d q (-2 * dedekindSaddleAngle K d q) =
      dedekindSaddle K d q := by
  unfold dedekindLowerContourPoint dedekindSaddle
  congr 2
  push_cast
  ring

/-- If the amplitude at `θ` is at most `B` times the amplitude at the saddle angle, and the real
part of the phase at `θ` lies at least `g` below its value at the saddle, then the integrand at
`θ` is at most `B ‖a₀‖ exp (d Re H₀) exp (-d g)`. -/
theorem dedekind_tail_pointwise_of_ratio_gap {d : ℕ} {q θ B g : ℝ} (hd : 0 < d)
    (ha : dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q) ≠ 0)
    (hratio : ‖dedekindAmplitude K d q θ /
      dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q)‖ ≤ B)
    (hgap : g ≤
      (dedekindSaddlePhase K d q (dedekindSaddle K d q)).re -
      (dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ)).re) :
    ‖dedekindAmplitude K d q θ *
      Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ))‖ ≤
      B * ‖dedekindAmplitude K d q
        (-2 * dedekindSaddleAngle K d q)‖ *
        Real.exp (d * (dedekindSaddlePhase K d q
          (dedekindSaddle K d q)).re) * Real.exp (-d * g) := by
  have ha0 := norm_pos_iff.mpr ha
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hexp : Real.exp (d * (dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ)).re) ≤
      Real.exp (d * (dedekindSaddlePhase K d q (dedekindSaddle K d q)).re) *
        Real.exp (-d * g) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have hamp : ‖dedekindAmplitude K d q θ‖ ≤
      B * ‖dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q)‖ := by
    rwa [norm_div, div_le_iff₀ ha0] at hratio
  rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, mul_assoc _ (Real.exp _)]
  gcongr
  exact (norm_nonneg _).trans hamp

/-- Under explicit `C³/C¹` bounds on the windowed amplitude and phase and a complementary-arc
bound, the lower contribution of the Dedekind saddle contour differs from the leading saddle term
by at most `‖dedekindLeadingSaddle K d q‖` times
`windowRelConst c C * n ^ (-1 / 10) + π B √(2 π d ‖D‖) exp (-g)`. -/
theorem dedekind_lower_contribution_conditional
    {d : ℕ} (hd : 0 < d) {q ℓ c C B g : ℝ}
    {f' p' p'' p''' : ℝ → ℂ}
    (hℓ : 0 < ℓ)
    (hD : 0 < (dedekindSaddleHessian K d q).re)
    (ha : dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q) ≠ 0)
    (hn : 1 ≤ dedekindEffectiveN K d q)
    (hn_eq : dedekindEffectiveN K d q = d * ‖dedekindSaddleHessian K d q‖ * ℓ ^ 2)
    (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (windowAmp (dedekindAmplitude K d q)
        (-2 * dedekindSaddleAngle K d q) ℓ) (f' y) y)
    (hf'_cont : ContinuousOn f' (Icc (-1 : ℝ) 1))
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (windowPhase
        (fun θ => dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ))
        (-2 * dedekindSaddleAngle K d q) ℓ d
        (dedekindEffectiveN K d q)) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(dedekindSaddleHessian K d q / (‖dedekindSaddleHessian K d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1,
      (windowPhase
        (fun θ => dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ))
        (-2 * dedekindSaddleAngle K d q) ℓ d
        (dedekindEffectiveN K d q) y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hf_bd : ∀ y ∈ Icc (-1 : ℝ) 1,
      ‖windowAmp (dedekindAmplitude K d q)
        (-2 * dedekindSaddleAngle K d q) ℓ y‖ ≤ C)
    (hf'_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖f' y‖ ≤ C)
    (hp''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p'' y‖ ≤ C)
    (hp'''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p''' y‖ ≤ C)
    (hleft : -Real.pi ≤ -2 * dedekindSaddleAngle K d q - ℓ)
    (hright : -2 * dedekindSaddleAngle K d q + ℓ ≤ 0)
    (hint : IntervalIntegrable
      (fun θ => dedekindAmplitude K d q θ *
        Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ))) MeasureTheory.volume
      (-Real.pi) 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * dedekindSaddleAngle K d q - ℓ)
        (-2 * dedekindSaddleAngle K d q + ℓ) →
      ‖dedekindAmplitude K d q θ *
        Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ))‖ ≤
        B * ‖dedekindAmplitude K d q
          (-2 * dedekindSaddleAngle K d q)‖ *
          Real.exp (d * (dedekindSaddlePhase K d q
            (dedekindSaddle K d q)).re) * Real.exp (-g)) :
    ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖ ≤
      ‖dedekindLeadingSaddle K d q‖ *
        (windowRelConst c C * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) +
          Real.pi * B * Real.sqrt
            (2 * Real.pi * d * ‖dedekindSaddleHessian K d q‖) *
            Real.exp (-g)) := by
  have hcore := lower_semicircle_estimate
    (a := dedekindAmplitude K d q)
    (H := fun θ => dedekindSaddlePhase K d q
      (dedekindLowerContourPoint K d q θ))
    (f' := f') (p' := p') (p'' := p'') (p''' := p''')
    (θ₀ := -2 * dedekindSaddleAngle K d q) (ℓ := ℓ) (dd := (d : ℝ))
    (c := c) (C := C) (B := B) (g := g)
    (D := dedekindSaddleHessian K d q)
    hℓ (mod_cast hd) hD ha (by simpa [hn_eq] using hn) hc hC
    hf hf'_cont (by simpa [hn_eq] using hp) hp' hp'' hp'0 hp''0
    (by simpa [hn_eq] using hre) hlower hf_bd hf'_bd hp''_bd hp'''_bd
    hleft hright hint (fun θ hθ hout => by
      simpa only [dedekind_saddle_contour_point K d q] using htail θ hθ hout)
  rw [dedekind_saddle_contour_point K d q] at hcore
  let P : ℂ := (d.factorial : ℂ) / (d : ℂ) ^ d
  let I : ℂ := (1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in (-Real.pi)..0, dedekindAmplitude K d q θ *
      Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ))
  let Z : ℂ := dedekindAmplitude K d q
      (-2 * dedekindSaddleAngle K d q) *
    Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
      (dedekindSaddle K d q)) /
    Complex.sqrt (2 * Real.pi * d * dedekindSaddleHessian K d q)
  have hIz : ‖I - Z‖ ≤ ‖Z‖ *
      (windowRelConst c C * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) +
        Real.pi * B * Real.sqrt
          (2 * Real.pi * d * ‖dedekindSaddleHessian K d q‖) *
          Real.exp (-g)) := by
    simpa [I, Z, hn_eq] using hcore
  have hL : dedekindLowerContribution K d q = P * I := rfl
  have hZ : dedekindLeadingSaddle K d q = P * Z := by
    unfold dedekindLeadingSaddle P Z
    push_cast
    ring
  rw [hL, hZ, ← mul_sub, norm_mul, norm_mul]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hIz (norm_nonneg P)

end

end RiemannJensen
