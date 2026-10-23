module

public import RiemannJensen.Analysis.CauchyFinal
public import RiemannJensen.Analysis.LowerContourFactorization

/-!
# The lower half of the Cauchy circle integral

The Cauchy circle representation of the rescaled Jensen polynomial splits into
the contributions of the lower and upper semicircles; on the saddle circle the
lower one is exactly `lowerContribution`.
-/

@[expose] public section

namespace RiemannJensen

open Complex MeasureTheory intervalIntegral

/-- The Cauchy integral over the arc `θ ∈ [a, b]` of the circle of radius `ρ`,
with the normalization `d! / (2πi dᵈ)`. -/
noncomputable def cauchyHalf (d : ℕ) (x ρ a b : ℝ) : ℂ :=
  ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
    ∫ θ in a..b, deriv (circleMap 0 ρ) θ •
      (cauchyNumerator d x (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (d + 1))

/-- The Cauchy numerator `cauchyNumerator d x` is continuous. -/
theorem continuous_cauchyNumerator (d : ℕ) (x : ℝ) : Continuous (cauchyNumerator d x) := by
  unfold cauchyNumerator
  exact (differentiable_riemannF.continuous.comp (continuous_const.mul continuous_id)).mul
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id))

/-- The integrand of `cauchyHalf` is continuous in `θ` for a positive radius `ρ`. -/
theorem continuous_cauchyHalf_integrand (d : ℕ) (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => deriv (circleMap 0 ρ) θ •
      (cauchyNumerator d x (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (d + 1)) := by
  have hc : Continuous (circleMap (0 : ℂ) ρ) := continuous_circleMap 0 ρ
  simp only [deriv_circleMap, smul_eq_mul]
  refine (hc.mul continuous_const).mul
    (((continuous_cauchyNumerator d x).comp hc).div (hc.pow _) fun θ => ?_)
  exact pow_ne_zero _ (circleMap_ne_center hρ.ne')

/-- The Cauchy representation split into the lower and upper semicircles. -/
theorem rescaledJensen_eval_eq_cauchyHalf_add (d : ℕ) (hd : 1 ≤ d) (x ρ : ℝ) (hρ : 0 < ρ)
    (hγ : gammaCoeff d ≠ 0) :
    (↑((rescaledJensen d).eval x) : ℂ) =
      cauchyHalf d x ρ (-Real.pi) 0 + cauchyHalf d x ρ 0 Real.pi := by
  rw [cauchy_representation_riemannF d hd x ρ hρ hγ, circleIntegral]
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 ρ) θ •
      (cauchyNumerator d x (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (d + 1)) with hg
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [hg, deriv_circleMap, periodic_circleMap 0 ρ θ]
  have hcont := continuous_cauchyHalf_integrand d x hρ
  have hshift : ∫ θ in (0 : ℝ)..2 * Real.pi, g θ = ∫ θ in (-Real.pi)..Real.pi, g θ := by
    have := hper.intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add] at this
    rw [this]
    congr 1
    ring
  rw [hshift, ← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), mul_add]
  rfl

/-- On the saddle circle `ρ = r²`, the lower half of the Cauchy integral is exactly
`lowerContribution`. -/
theorem cauchyHalf_lower_eq_lowerContribution (d : ℕ) (hd : 1 ≤ d) (q : ℝ)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hR : 1 < scaleT d * saddleRadius d (saddleAngle d q)) :
    cauchyHalf d (-q) ((saddleRadius d (saddleAngle d q)) ^ 2) (-Real.pi) 0 =
      lowerContribution d q := by
  set r := saddleRadius d (saddleAngle d q) with hr_def
  have hpt : ∀ θ : ℝ, circleMap 0 (r ^ 2) θ = lowerContourPoint d q θ := by
    intro θ
    simp only [circleMap, lowerContourPoint, zero_add, hr_def]
    push_cast
    ring_nf
  have hcongr : Set.EqOn
      (fun θ : ℝ => deriv (circleMap 0 (r ^ 2)) θ •
        (cauchyNumerator d (-q) (circleMap 0 (r ^ 2) θ) / (circleMap 0 (r ^ 2) θ) ^ (d + 1)))
      (fun θ : ℝ => Complex.I * (amplitude d q θ *
        Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))))
      (Set.uIcc (-Real.pi) 0) := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    have hne : lowerContourPoint d q θ ≠ 0 := by
      rw [← hpt]; exact circleMap_ne_center (by positivity)
    simp only [deriv_circleMap, smul_eq_mul, hpt]
    rw [← cauchyNumerator_lower_factorization d hd q θ hr hR hθ.1 hθ.2]
    field_simp
    ring
  unfold cauchyHalf lowerContribution
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hdd : (d : ℂ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : d ≠ 0))
  field_simp

/-- The Jensen polynomial at `-q` is the lower contribution plus the upper half
of the Cauchy integral over the saddle circle. -/
theorem rescaledJensen_eval_eq_lowerContribution_add (d : ℕ) (hd : 1 ≤ d) (q : ℝ)
    (hγ : gammaCoeff d ≠ 0)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hR : 1 < scaleT d * saddleRadius d (saddleAngle d q)) :
    (↑((rescaledJensen d).eval (-q)) : ℂ) =
      lowerContribution d q +
        cauchyHalf d (-q) ((saddleRadius d (saddleAngle d q)) ^ 2) 0 Real.pi := by
  rw [rescaledJensen_eval_eq_cauchyHalf_add d hd (-q) _ (pow_pos hr 2) hγ,
    cauchyHalf_lower_eq_lowerContribution d hd q hr hR]

/-- `F` has real Taylor coefficients, so it commutes with conjugation. -/
theorem riemannF_star (z : ℂ) : riemannF (star z) = star (riemannF z) := by
  unfold riemannF
  rw [tsum_star]
  congr 1
  funext j
  simp

/-- The Cauchy numerator commutes with complex conjugation. -/
theorem cauchyNumerator_star (d : ℕ) (x : ℝ) (u : ℂ) :
    cauchyNumerator d x (star u) = star (cauchyNumerator d x u) := by
  unfold cauchyNumerator
  have h1 : ((((scaleT d) ^ 2 : ℝ) : ℂ) * star u) = star ((((scaleT d) ^ 2 : ℝ) : ℂ) * u) := by
    simp
  have h2 : ((((d : ℝ) * x : ℝ) : ℂ) * star u) = star ((((d : ℝ) * x : ℝ) : ℂ) * u) := by
    simp
  rw [h1, h2, riemannF_star]
  simp only [Complex.star_def]
  rw [Complex.exp_conj, map_mul]

private theorem intervalIntegral_star {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    (∫ θ in a..b, star (f θ)) = star (∫ θ in a..b, f θ) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_conj

/-- The upper half of the Cauchy integral is the conjugate of the lower half. -/
theorem cauchyHalf_upper_eq_star_lower (d : ℕ) (x : ℝ) {ρ : ℝ} :
    cauchyHalf d x ρ 0 Real.pi = star (cauchyHalf d x ρ (-Real.pi) 0) := by
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 ρ) θ •
      (cauchyNumerator d x (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (d + 1)) with hg
  have hcm : ∀ θ : ℝ, circleMap 0 ρ (-θ) = star (circleMap 0 ρ θ) := by
    intro θ
    simp only [circleMap, zero_add, Complex.star_def, map_mul, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, Complex.conj_I]
    push_cast
    ring_nf
  have hsym : ∀ θ : ℝ, star (g (-θ)) = -g θ := by
    intro θ
    simp only [hg, deriv_circleMap, smul_eq_mul, hcm, cauchyNumerator_star, star_mul,
      star_div₀, star_pow, star_star]
    rw [show star Complex.I = -Complex.I from Complex.conj_I]
    ring
  have hint : (∫ θ in (0 : ℝ)..Real.pi, g θ) = -star (∫ θ in (-Real.pi)..0, g θ) := by
    have hc := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) (fun θ => star (g θ))
    simp only [hsym, intervalIntegral.integral_neg, neg_zero] at hc
    rw [intervalIntegral_star (by linarith [Real.pi_pos]) (f := g)] at hc
    rw [← hc, neg_neg]
  unfold cauchyHalf
  rw [← hg, hint, star_mul]
  have hK : star ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) =
      -((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) := by
    rw [star_div₀]
    simp only [star_mul, star_pow, star_natCast, star_ofNat, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hK]
  ring

/-- The upper semicircle contributes the conjugate of `lowerContribution`. -/
theorem cauchyHalf_upper_eq_star_lowerContribution (d : ℕ) (hd : 1 ≤ d) (q : ℝ)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hR : 1 < scaleT d * saddleRadius d (saddleAngle d q)) :
    cauchyHalf d (-q) ((saddleRadius d (saddleAngle d q)) ^ 2) 0 Real.pi =
      star (lowerContribution d q) := by
  rw [cauchyHalf_upper_eq_star_lower, cauchyHalf_lower_eq_lowerContribution d hd q hr hR]

/-- The Jensen polynomial at `-q` is `L_d(q) + conj L_d(q) = 2 Re L_d(q)`. -/
theorem rescaledJensen_eval_eq_lowerContribution_add_star (d : ℕ) (hd : 1 ≤ d) (q : ℝ)
    (hγ : gammaCoeff d ≠ 0)
    (hr : 0 < saddleRadius d (saddleAngle d q))
    (hR : 1 < scaleT d * saddleRadius d (saddleAngle d q)) :
    (↑((rescaledJensen d).eval (-q)) : ℂ) =
      lowerContribution d q + star (lowerContribution d q) := by
  rw [rescaledJensen_eval_eq_lowerContribution_add d hd q hγ hr hR,
    cauchyHalf_upper_eq_star_lowerContribution d hd q hr hR]

end RiemannJensen
