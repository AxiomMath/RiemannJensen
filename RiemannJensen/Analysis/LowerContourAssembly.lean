module

public import RiemannJensen.Analysis.LowerContourBridge
public import RiemannJensen.Analysis.HessianNormBounds

/-!
# Assembling the lower-contour estimate

The integrability of the lower-contour integrand, the lower-contour estimate
with that hypothesis discharged, the packaging of the complementary-arc term,
the geometric lower bound for the effective Gaussian parameter, and the exact
oscillatory formula `A_d(-q) = 2 Re Z_d(q) + O(|Z_d(q)| E)`.
-/

@[expose] public section

namespace RiemannJensen

open Set MeasureTheory

/-- The lower-contour integrand is interval integrable on `[-π, 0]`. -/
theorem intervalIntegrable_lower_integrand (d : ℕ) (hd : 1 ≤ d) (q : ℝ)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hR : 1 < scaleT d * saddleRadius d (saddleAngle d q)) :
    IntervalIntegrable
      (fun θ => amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ)))
      volume (-Real.pi) 0 := by
  set r := saddleRadius d (saddleAngle d q) with hr_def
  have hpt : ∀ θ : ℝ, circleMap 0 (r ^ 2) θ = lowerContourPoint d q θ := by
    intro θ
    simp only [circleMap, lowerContourPoint, zero_add, hr_def]
    push_cast
    ring_nf
  refine (((continuous_cauchyHalf_integrand d (-q) (pow_pos hr 2)).intervalIntegrable
    (μ := volume) (-Real.pi) 0).const_mul (-Complex.I)).congr fun θ hθ => ?_
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
  have hne : lowerContourPoint d q θ ≠ 0 := hpt θ ▸ circleMap_ne_center (by positivity)
  simp only [deriv_circleMap, smul_eq_mul, hpt]
  rw [← cauchyNumerator_lower_factorization d hd q θ hr hR hθ.1.le hθ.2]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Lower-contour estimate, integrability discharged.** As
`lowerContribution_estimate_of_geometry`, with the integrability hypothesis
proved from `0 < r` and `200 ≤ T r`. -/
theorem lowerContribution_estimate_of_geometry' {d : ℕ} {q ε c Cp K B g : ℝ}
    {p' p'' p''' : ℝ → ℂ} (hd : 1 ≤ d)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hℓ : 0 < localWidth ε d q) (hℓ1 : localWidth ε d q ≤ 1)
    (hD : 0 < (saddleHessian d q).re)
    (hn : 1 ≤ effectiveN ε d q) (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hreW : ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hK : ∀ y ∈ Icc (-1 : ℝ) 1,
      localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
        K * (contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hp''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p'' y‖ ≤ Cp)
    (hp'''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p''' y‖ ≤ Cp)
    (h1 : -Real.pi ≤ -2 * saddleAngle d q - localWidth ε d q)
    (h2 : -2 * saddleAngle d q + localWidth ε d q ≤ 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-g)) :
    ‖lowerContribution d q - leadingSaddle d q‖ ≤
      ‖leadingSaddle d q‖ *
        (windowRelConst c (max (4 + 8 * K * zetaLogDerivMajorant) Cp) *
            effectiveN ε d q ^ (-(1 : ℝ) / 10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) * Real.exp (-g)) :=
  lowerContribution_estimate_of_geometry (by omega) hℓ hℓ1 hD hn hc hCp hR hreW hK hp hp'
    hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd h1 h2
    (intervalIntegrable_lower_integrand d hd q hr (by linarith)) htail

/-- **Tail packaging.** If `0 ≤ K₁`, `B ≤ K₁ √T`, `T ≤ d` and `‖D‖ ≤ K₂`, then
`π B √(2π d ‖D‖) e^{-g} ≤ π K₁ √(2π K₂) d e^{-g}`. -/
theorem tail_term_le {d : ℕ} {T B K₁ K₂ g : ℝ} {D : ℂ}
    (hK₁ : 0 ≤ K₁) (hBK : B ≤ K₁ * Real.sqrt T) (hTd : T ≤ d) (hDK : ‖D‖ ≤ K₂) :
    Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖D‖) * Real.exp (-g) ≤
      Real.pi * K₁ * Real.sqrt (2 * Real.pi * K₂) * d * Real.exp (-g) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsD : Real.sqrt (2 * Real.pi * d * ‖D‖) ≤ Real.sqrt d * Real.sqrt (2 * Real.pi * K₂) := by
    rw [← Real.sqrt_mul hd0, show (d : ℝ) * (2 * Real.pi * K₂) = 2 * Real.pi * d * K₂ by ring]
    gcongr
  calc _ ≤ Real.pi * (K₁ * Real.sqrt d) * (Real.sqrt d * Real.sqrt (2 * Real.pi * K₂)) *
          Real.exp (-g) := by
        gcongr
        exact hBK.trans (by gcongr)
    _ = _ := by
      linear_combination Real.pi * K₁ * Real.sqrt (2 * Real.pi * K₂) * Real.exp (-g) *
        Real.mul_self_sqrt hd0

/-- On the scale window `‖D_{d,q}‖ ≤ 4`. -/
theorem norm_saddleHessian_le_four (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖saddleHessian d q‖ ≤ 4 := by
  have h := (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).2
  nlinarith [Real.sin_le_one (saddleAngle d q)]

/-- **Tail packaging on the scale window.** On the scale window (where `‖D_{d,q}‖ ≤ 4`), the
complementary-arc term is at most `π K₁ √(8π) d e^{-g}`. -/
theorem tail_term_le_on_scale_window {d : ℕ} {q B K₁ g : ℝ}
    (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d) (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hK₁ : 0 ≤ K₁) (hBK : B ≤ K₁ * Real.sqrt (scaleT d)) (hTd : scaleT d ≤ d) :
    Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) * Real.exp (-g) ≤
      Real.pi * K₁ * Real.sqrt (2 * Real.pi * 4) * d * Real.exp (-g) :=
  tail_term_le hK₁ hBK hTd (norm_saddleHessian_le_four d hd hΛ hq)

/-- **Effective parameter, geometric lower bound**:
`n_{ε,d,q} ≥ (3/8) ε² d sin α min(α, cos α)²` on the scale window. -/
theorem effectiveN_ge_geometric (ε : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d) {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    (3 / 8 : ℝ) * ε ^ 2 * d * Real.sin (saddleAngle d q) *
        min (saddleAngle d q) (Real.cos (saddleAngle d q)) ^ 2 ≤
      effectiveN ε d q := by
  unfold effectiveN localWidth
  linarith [mul_le_mul_of_nonneg_left (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).1
    (by positivity :
      (0 : ℝ) ≤ d * (ε ^ 2 * min (saddleAngle d q) (Real.cos (saddleAngle d q)) ^ 2))]

/-- **Generic oscillatory assembly**, real form: if `(A : ℂ) = L + conj L` and
`‖L - Z‖ ≤ ‖Z‖ E`, then `|A - 2 Re Z| ≤ 2 ‖Z‖ E`. -/
theorem abs_sub_two_re_le_of_eq_add_star {A : ℝ} {L Z : ℂ} {E : ℝ}
    (hA : (A : ℂ) = L + star L) (h : ‖L - Z‖ ≤ ‖Z‖ * E) :
    |A - 2 * Z.re| ≤ 2 * ‖Z‖ * E := by
  have hA' : A = 2 * L.re := by exact_mod_cast hA.trans (Complex.add_conj L)
  rw [hA', ← mul_sub, ← Complex.sub_re, abs_mul, abs_two]
  linarith [Complex.abs_re_le_norm (L - Z)]

/-- **Exact oscillatory formula**, conditional form:
under the hypotheses of the lower-contour estimate and `γ(d) ≠ 0`,
`|A_d(-q) - 2 Re Z_d(q)| ≤ 2 |Z_d(q)| (C n^{-1/10} + π B √(2π d |D|) e^{-g})`,
where `C = windowRelConst c (max (4 + 8 K M) Cp)` with `M = zetaLogDerivMajorant`. -/
theorem abs_rescaledJensen_eval_sub_two_re_leadingSaddle_le {d : ℕ} {q ε c Cp K B g : ℝ}
    {p' p'' p''' : ℝ → ℂ} (hd : 1 ≤ d) (hγ : gammaCoeff d ≠ 0)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hℓ : 0 < localWidth ε d q) (hℓ1 : localWidth ε d q ≤ 1)
    (hD : 0 < (saddleHessian d q).re)
    (hn : 1 ≤ effectiveN ε d q) (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hreW : ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hK : ∀ y ∈ Icc (-1 : ℝ) 1,
      localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
        K * (contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hp''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p'' y‖ ≤ Cp)
    (hp'''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p''' y‖ ≤ Cp)
    (h1 : -Real.pi ≤ -2 * saddleAngle d q - localWidth ε d q)
    (h2 : -2 * saddleAngle d q + localWidth ε d q ≤ 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-g)) :
    |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
      2 * ‖leadingSaddle d q‖ *
        (windowRelConst c (max (4 + 8 * K * zetaLogDerivMajorant) Cp) *
            effectiveN ε d q ^ (-(1 : ℝ) / 10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) * Real.exp (-g)) :=
  abs_sub_two_re_le_of_eq_add_star
    (rescaledJensen_eval_eq_lowerContribution_add_star d hd q hγ hr (by linarith))
    (lowerContribution_estimate_of_geometry' hd hr hℓ hℓ1 hD hn hc hCp hR hreW hK hp
      hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd h1 h2 htail)

end RiemannJensen
