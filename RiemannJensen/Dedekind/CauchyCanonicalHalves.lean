module

public import RiemannJensen.Dedekind.CauchyBridge
public import RiemannJensen.Dedekind.CauchyContourAdapters
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Semicircle halves of the canonical Cauchy integral

For a number field `K`, the rescaled Jensen polynomial of the Dedekind xi function is given by a
Cauchy integral over a circle about the origin. This file splits that circle into its lower and
upper semicircles, shows that the upper contribution is the complex conjugate of the lower one,
and deduces that the value is twice the real part of the lower contribution.

## Main definitions

* `dedekindCauchyHalfK`: The normalized Cauchy arc integral for `K` at the saddle scale.

## Main results

* `dedekindCauchyHalfK_upper_eq_star_lower`: The upper semicircle contribution is the conjugate
  of the lower one.
* `dedekind_cauchy_halves`: The value of the rescaled Jensen polynomial is the sum of the two
  semicircle contributions.
* `dedekind_cauchy_two_re`: The value of the rescaled Jensen polynomial is twice the real part of
  the lower semicircle contribution.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial MeasureTheory intervalIntegral

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The canonical normalized Cauchy arc for a number field. -/
noncomputable def dedekindCauchyHalfK (d : ℕ) (x ρ a b : ℝ) : ℂ :=
  dedekindCauchyHalf (entireDedekindXi K) d (dedekindScaleT K d) x ρ a b

/-- The upper canonical Cauchy semicircle is the conjugate of the lower one. -/
theorem dedekindCauchyHalfK_upper_eq_star_lower (d : ℕ) (x ρ : ℝ) :
    dedekindCauchyHalfK K d x ρ 0 Real.pi =
      star (dedekindCauchyHalfK K d x ρ (-Real.pi) 0) :=
  dedekindCauchyHalf_upper_eq_star_lower (entireDedekindXi K) d (dedekindScaleT K d) x ρ

/-- A circle integral about the origin splits into its lower and upper semicircle integrals. -/
theorem circleIntegral_eq_integral_neg_pi_zero_add_integral_zero_pi {f : ℂ → ℂ} {ρ : ℝ}
    (hf : CircleIntegrable f 0 ρ) :
    (∮ u in C(0, ρ), f u) =
      (∫ θ in (-Real.pi)..0, deriv (circleMap 0 ρ) θ • f (circleMap 0 ρ θ)) +
        ∫ θ in (0 : ℝ)..Real.pi, deriv (circleMap 0 ρ) θ • f (circleMap 0 ρ θ) := by
  let g : ℝ → ℂ := fun θ => deriv (circleMap 0 ρ) θ • f (circleMap 0 ρ θ)
  have hgper : Function.Periodic g (2 * Real.pi) := fun θ => by
    simp only [g, deriv_circleMap, periodic_circleMap (0 : ℂ) ρ θ]
  have hgiall : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    hgper.intervalIntegrable₀ (by positivity) (by simpa [g] using hf.out)
  rw [circleIntegral, show 2 * Real.pi = 0 + 2 * Real.pi by ring,
    hgper.intervalIntegral_add_eq 0 (-Real.pi), show -Real.pi + 2 * Real.pi = Real.pi by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (hgiall (-Real.pi) 0) (hgiall 0 Real.pi)]

/-- The canonical Cauchy integrand for `K` is continuous on every circle of positive radius
about the origin. -/
theorem continuousOn_dedekindCauchyIntegrand (d : ℕ) (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (fun u : ℂ =>
      dedekindCauchyNumerator (entireDedekindXi K) d (dedekindScaleT K d) x u / u ^ (d + 1))
      (Metric.sphere 0 ρ) := by
  have hF :=
    (differentiable_dedekindF (entireDedekindXi_entire K) (entireDedekindXi_conj K)).continuous
  refine ContinuousOn.div (by unfold dedekindCauchyNumerator; fun_prop) (by fun_prop) fun u hu => ?_
  exact pow_ne_zero _ (ne_zero_of_mem_sphere hρ.ne' ⟨u, hu⟩)

/-- The value of the rescaled Jensen polynomial at `x` is the sum of the canonical Cauchy
integrals over the lower and upper semicircles of radius `ρ`. -/
theorem dedekind_cauchy_halves (d : ℕ) (hd : 1 ≤ d) (x ρ : ℝ) (hρ : 0 < ρ) :
    (↑((rescaledDedekindJensenK K d).eval x) : ℂ) =
      dedekindCauchyHalfK K d x ρ (-Real.pi) 0 +
        dedekindCauchyHalfK K d x ρ 0 Real.pi := by
  rw [dedekind_cauchy K d hd x ρ hρ, circleIntegral_eq_integral_neg_pi_zero_add_integral_zero_pi
    (by simpa only [dedekindCauchyNumerator] using
      (continuousOn_dedekindCauchyIntegrand K d x hρ).circleIntegrable hρ.le)]
  simp only [dedekindCauchyHalfK, dedekindCauchyHalf, dedekindCauchyNumerator]
  ring

/-- The value of the rescaled Jensen polynomial at `x` is twice the real part of the canonical
Cauchy integral over the lower semicircle of radius `ρ`. -/
theorem dedekind_cauchy_two_re (d : ℕ) (hd : 1 ≤ d) (x ρ : ℝ) (hρ : 0 < ρ) :
    (↑((rescaledDedekindJensenK K d).eval x) : ℂ) =
      2 * (dedekindCauchyHalfK K d x ρ (-Real.pi) 0).re := by
  rw [dedekind_cauchy_halves K d hd x ρ hρ, dedekindCauchyHalfK_upper_eq_star_lower K]
  refine Complex.ext ?_ ?_ <;> simp [two_mul]

end

end RiemannJensen
