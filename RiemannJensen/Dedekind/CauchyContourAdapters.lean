module

public import RiemannJensen.Dedekind.CauchyRepresentation
public import RiemannJensen.Dedekind.RootCountAdapters
public import RiemannJensen.Analysis.LowerBranch

/-!
# Conjugation symmetry of the Dedekind Cauchy integral

The normalized Cauchy integral of `dedekindCauchyNumerator ξ d T x u / u ^ (d + 1)` over a
circle centred at the origin splits into an upper and a lower arc. Since the square-variable
series has real coefficients, the integrand is conjugation-symmetric, and the upper arc is the
complex conjugate of the lower.

## Main definitions

* `dedekindCauchyHalf`: The normalized Cauchy integral over the arc `θ ∈ [a, b]` of the circle
  of radius `ρ`.

## Main results

* `dedekindF_star`: `dedekindF ξ (star z) = star (dedekindF ξ z)`.
* `dedekindCauchyNumerator_star`: The Cauchy numerator commutes with conjugation.
* `dedekindCauchyHalf_upper_eq_star_lower`: The integral over `[0, π]` is the conjugate of the
  integral over `[-π, 0]`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial MeasureTheory intervalIntegral

noncomputable section

/-- A normalized arc of the Dedekind Cauchy integral. -/
noncomputable def dedekindCauchyHalf (ξ : ℂ → ℂ) (d : ℕ)
    (T x ρ a b : ℝ) : ℂ :=
  ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
    ∫ θ in a..b, deriv (circleMap 0 ρ) θ •
      (dedekindCauchyNumerator ξ d T x (circleMap 0 ρ θ) /
        (circleMap 0 ρ θ) ^ (d + 1))

/-- The square-variable series has real coefficients. -/
theorem dedekindF_star (ξ : ℂ → ℂ) (z : ℂ) :
    dedekindF ξ (star z) = star (dedekindF ξ z) := by
  unfold dedekindF
  rw [tsum_star]
  congr 1
  funext j
  simp

/-- Conjugation symmetry of the exact Cauchy numerator. -/
theorem dedekindCauchyNumerator_star (ξ : ℂ → ℂ) (d : ℕ)
    (T x : ℝ) (u : ℂ) :
    dedekindCauchyNumerator ξ d T x (star u) =
      star (dedekindCauchyNumerator ξ d T x u) := by
  unfold dedekindCauchyNumerator
  have h1 : (((T ^ 2 : ℝ) : ℂ) * star u) =
      star (((T ^ 2 : ℝ) : ℂ) * u) := by simp
  have h2 : ((((d : ℝ) * x : ℝ) : ℂ) * star u) =
      star ((((d : ℝ) * x : ℝ) : ℂ) * u) := by simp
  rw [h1, h2, dedekindF_star]
  simp only [Complex.star_def]
  rw [Complex.exp_conj, map_mul]

private theorem intervalIntegral_star' {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) :
    (∫ θ in a..b, star (f θ)) = star (∫ θ in a..b, f θ) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_conj

/-- The upper half of the circle integral is the conjugate of the lower half. -/
theorem dedekindCauchyHalf_upper_eq_star_lower (ξ : ℂ → ℂ) (d : ℕ)
    (T x ρ : ℝ) :
    dedekindCauchyHalf ξ d T x ρ 0 Real.pi =
      star (dedekindCauchyHalf ξ d T x ρ (-Real.pi) 0) := by
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 ρ) θ •
      (dedekindCauchyNumerator ξ d T x (circleMap 0 ρ θ) /
        (circleMap 0 ρ θ) ^ (d + 1)) with hg
  have hcm : ∀ θ : ℝ, circleMap 0 ρ (-θ) = star (circleMap 0 ρ θ) := by
    intro θ
    simp only [circleMap, zero_add, Complex.star_def, map_mul,
      Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    push_cast
    ring_nf
  have hsym : ∀ θ : ℝ, star (g (-θ)) = -g θ := by
    intro θ
    simp only [hg, deriv_circleMap, smul_eq_mul, hcm,
      dedekindCauchyNumerator_star, star_mul, star_div₀, star_pow, star_star]
    rw [show star Complex.I = -Complex.I from Complex.conj_I]
    ring
  have hint : (∫ θ in (0 : ℝ)..Real.pi, g θ) =
      -star (∫ θ in (-Real.pi)..0, g θ) := by
    have hc := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi)
      (fun θ => star (g θ))
    simp only [hsym, intervalIntegral.integral_neg, neg_zero] at hc
    rw [intervalIntegral_star' (by linarith [Real.pi_pos]) (f := g)] at hc
    rw [← hc, neg_neg]
  unfold dedekindCauchyHalf
  rw [← hg, hint, star_mul]
  have hK : star ((d.factorial : ℂ) /
      ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) =
      -((d.factorial : ℂ) /
        ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) := by
    rw [star_div₀]
    simp only [star_mul, star_pow, star_natCast, star_ofNat,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hK]
  ring

end

end RiemannJensen
