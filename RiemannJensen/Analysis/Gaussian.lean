module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Exponential estimates on the left half-plane and complex Gaussian integrals

On the closed left half-plane the complex exponential has norm at most one and is one-Lipschitz.
This file records these estimates, their scaled forms for phases of the form `n * p y`, and the
complex Gaussian integral with parameter `(n / 2) * A`.

## Main results

* `norm_exp_sub_exp_le`: `‖exp z₁ - exp z₀‖ ≤ ‖z₁ - z₀‖` when `z₀.re ≤ 0` and `z₁.re ≤ 0`.
* `norm_exp_phase_sub_quadratic_le`: a bound `n K |y|³` on the difference of two exponentiated
  phases whose difference is at most `K |y|³`.
* `integral_normalized_complex_gaussian`: the integral of `exp (-(n / 2) A x²)` over `ℝ` equals
  `(π / ((n / 2) A)) ^ (1 / 2)`.
-/

@[expose] public section

namespace RiemannJensen

namespace Gaussian

open Complex

/-- On the closed left half-plane, the complex exponential has norm at most one. -/
theorem norm_exp_le_one_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) : ‖Complex.exp z‖ ≤ 1 := by
  simpa [Complex.norm_exp] using hz

/-- The line segment joining two points of the closed left half-plane remains there. -/
theorem re_lineMap_nonpos {z₀ z₁ : ℂ} (hz₀ : z₀.re ≤ 0) (hz₁ : z₁.re ≤ 0)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (((1 - t : ℝ) : ℂ) * z₀ + (t : ℂ) * z₁).re ≤ 0 := by
  rw [add_re, re_ofReal_mul, re_ofReal_mul]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht₁) hz₀,
    mul_nonpos_of_nonneg_of_nonpos ht₀ hz₁]

/-- Multiplying by a left-half-plane exponential cannot increase the norm. -/
theorem norm_mul_exp_le_norm_of_re_nonpos {w z : ℂ} (hz : z.re ≤ 0) :
    ‖w * Complex.exp z‖ ≤ ‖w‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_exp_le_one_of_re_nonpos hz)

/-- The exponential map is one-Lipschitz when restricted to the closed left half-plane. -/
theorem norm_exp_sub_exp_le {z₀ z₁ : ℂ} (hz₀ : z₀.re ≤ 0) (hz₁ : z₁.re ≤ 0) :
    ‖Complex.exp z₁ - Complex.exp z₀‖ ≤ ‖z₁ - z₀‖ := by
  let g : ℝ → ℂ := fun t => Complex.exp ((((1 - t : ℝ) : ℂ) * z₀) + (t : ℂ) * z₁)
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((z₁ - z₀) * g t) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ) * z₀ + (s : ℂ) * z₁)
        (z₁ - z₀) t := by
      convert ((h1.const_sub 1).mul_const z₀).add (h1.mul_const z₁) using 1
      · ext s
        simp
      · ring
    exact (((Complex.hasDerivAt_exp _).comp t hlin).congr_deriv (mul_comm _ _)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖(z₁ - z₀) * g t‖ ≤ ‖z₁ - z₀‖ := fun t ht =>
    norm_mul_exp_le_norm_of_re_nonpos (re_lineMap_nonpos hz₀ hz₁ ht.1 ht.2.le)
  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hg hbound

/-- For `z₀`, `z₁` in the closed left half-plane and `0 ≤ n`,
`‖exp (n z₁) - exp (n z₀)‖ ≤ n ‖z₁ - z₀‖`. -/
theorem norm_exp_mul_sub_exp_mul_le {z₀ z₁ : ℂ} (hz₀ : z₀.re ≤ 0) (hz₁ : z₁.re ≤ 0)
    {n : ℝ} (hn : 0 ≤ n) :
    ‖Complex.exp ((n : ℂ) * z₁) - Complex.exp ((n : ℂ) * z₀)‖ ≤ n * ‖z₁ - z₀‖ := by
  have h := norm_exp_sub_exp_le (z₀ := (n : ℂ) * z₀) (z₁ := (n : ℂ) * z₁)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos hn hz₀)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos hn hz₁)
  rwa [← mul_sub, norm_mul, norm_real, Real.norm_of_nonneg hn] at h

/-- If `p y` and `q y` lie in the closed left half-plane, `0 ≤ n`, and `‖p y - q y‖ ≤ K |y|³`,
then `‖exp (n p y) - exp (n q y)‖ ≤ n K |y|³`. -/
theorem norm_exp_phase_sub_quadratic_le {p q : ℝ → ℂ} {K n y : ℝ}
    (hp : (p y).re ≤ 0) (hq : (q y).re ≤ 0) (hn : 0 ≤ n)
    (happrox : ‖p y - q y‖ ≤ K * |y| ^ 3) :
    ‖Complex.exp ((n : ℂ) * p y) - Complex.exp ((n : ℂ) * q y)‖ ≤ n * K * |y| ^ 3 := by
  calc
    _ ≤ n * ‖p y - q y‖ := norm_exp_mul_sub_exp_mul_le hq hp hn
    _ ≤ n * (K * |y| ^ 3) := mul_le_mul_of_nonneg_left happrox hn
    _ = n * K * |y| ^ 3 := by ring

/-- If `‖g y‖ ≤ C` on `Set.uIoc (-η) η` with `0 ≤ η`, then the interval integral of `g` over
`[-η, η]` has norm at most `C * (2 * η)`. -/
theorem norm_intervalIntegral_le_two_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {η C : ℝ} (hη : 0 ≤ η) (hg : ∀ y ∈ Set.uIoc (-η) η, ‖g y‖ ≤ C) :
    ‖∫ y in (-η)..η, g y‖ ≤ C * (2 * η) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae (Filter.Eventually.of_forall hg)
  rwa [sub_neg_eq_add, abs_of_nonneg (add_nonneg hη hη), ← two_mul] at h

/-- For `0 < A.re` and `0 < n`, the integral of `exp (-(n / 2) A x²)` over `ℝ` equals
`(π / ((n / 2) A)) ^ (1 / 2)`, with the principal branch of the complex power. -/
theorem integral_normalized_complex_gaussian {A : ℂ} (hA : 0 < A.re) {n : ℝ} (hn : 0 < n) :
    (∫ x : ℝ, Complex.exp (-(((n / 2 : ℝ) : ℂ) * A) * (x : ℂ) ^ 2)) =
      ((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^ (1 / 2 : ℂ) :=
  integral_gaussian_complex (by simpa using mul_pos (half_pos hn) hA)

end Gaussian

end RiemannJensen
