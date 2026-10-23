module

public import RiemannJensen.Dedekind.ContourFactorization
public import RiemannJensen.Dedekind.CauchyCanonicalHalves
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Integrability of the canonical lower Dedekind saddle integrand -/

@[expose] public section

namespace RiemannJensen

open Complex Set MeasureTheory intervalIntegral

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The canonical amplitude-phase integrand on the lower saddle semicircle is interval integrable
on `[-π, 0]`. -/
theorem intervalIntegrable_dedekind_lower_integrand_canonical
    {d : ℕ} (hd : 1 ≤ d) (q : ℝ)
    (hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hR : 1 < dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) :
    IntervalIntegrable
      (fun θ => dedekindAmplitude K d q θ *
        Complex.exp ((d : ℂ) * dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ))) volume
      (-Real.pi) 0 := by
  set r := dedekindSaddleRadius K d (dedekindSaddleAngle K d q) with hr_def
  let ρ : ℝ := r ^ 2
  let f : ℂ → ℂ := fun u =>
    dedekindCauchyNumerator (entireDedekindXi K) d (dedekindScaleT K d) (-q) u /
      u ^ (d + 1)
  let g : ℝ → ℂ := fun θ => deriv (circleMap 0 ρ) θ • f (circleMap 0 ρ θ)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hpt : ∀ θ : ℝ, circleMap 0 ρ θ = dedekindLowerContourPoint K d q θ := by
    intro θ
    simp only [circleMap, dedekindLowerContourPoint, zero_add, ρ, hr_def]
    push_cast
    ring_nf
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro θ
    dsimp [g]
    rw [deriv_circleMap, deriv_circleMap]
    have hc := (periodic_circleMap (0 : ℂ) ρ) θ
    rw [hc]
  have hfcont : ContinuousOn f (Metric.sphere 0 ρ) := by
    intro u hu
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      simp only [Metric.mem_sphere, dist_zero_right, norm_zero] at hu
      linarith
    apply ContinuousAt.continuousWithinAt
    dsimp [f, dedekindCauchyNumerator]
    have hlin₁ : ContinuousAt
        (fun v : ℂ => (((dedekindScaleT K d) ^ 2 : ℝ) : ℂ) * v) u :=
      continuousAt_const.mul continuousAt_id
    have hlin₂ : ContinuousAt
        (fun v : ℂ => ((((d : ℝ) * (-q) : ℝ) : ℂ)) * v) u :=
      continuousAt_const.mul continuousAt_id
    have hF : ContinuousAt
        (fun v : ℂ => dedekindF (entireDedekindXi K)
          ((((dedekindScaleT K d) ^ 2 : ℝ) : ℂ) * v)) u :=
      (differentiable_dedekindF (entireDedekindXi_entire K)
        (entireDedekindXi_conj K)).continuous.continuousAt.comp hlin₁
    have hE : ContinuousAt
        (fun v : ℂ => Complex.exp (((((d : ℝ) * (-q) : ℝ) : ℂ)) * v)) u :=
      Complex.continuous_exp.continuousAt.comp hlin₂
    exact (hF.mul hE).div (continuousAt_id.pow _) (pow_ne_zero _ hu0)
  have hfi : CircleIntegrable f 0 ρ :=
    ContinuousOn.circleIntegrable hρ.le hfcont
  have hgi0 : IntervalIntegrable g volume 0 (2 * Real.pi) := by
    simpa [g] using hfi.out
  have hgiall : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    hgper.intervalIntegrable₀ (by positivity) hgi0
  have hint := (hgiall (-Real.pi) 0).const_mul (-Complex.I)
  refine hint.congr fun θ hθ => ?_
  have hθ' : θ ∈ Icc (-Real.pi) 0 := by
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    exact ⟨hθ.1.le, hθ.2⟩
  have hne : dedekindLowerContourPoint K d q θ ≠ 0 := by
    rw [← hpt]
    exact circleMap_ne_center hρ.ne'
  simp only [g, deriv_circleMap, smul_eq_mul, hpt]
  dsimp [f]
  rw [← dedekind_contour_factorization K d hd q hr hR hθ'.1 hθ'.2]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end

end RiemannJensen
