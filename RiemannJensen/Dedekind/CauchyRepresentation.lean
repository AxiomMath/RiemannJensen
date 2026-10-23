module

public import RiemannJensen.Dedekind.Foundation
public import RiemannJensen.Analysis.CauchyRepresentation
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Cauchy coefficient representation for Dedekind Jensen polynomials

For a function `ξ` and a scale `T`, the rescaled reciprocal Jensen polynomial attached to the
square-variable series `dedekindF ξ` is expressed as a Cauchy integral over a circle about the
origin. The representation holds whenever `dedekindF ξ` is entire with Taylor jet
`dedekindGammaCoeff ξ`, and both properties are proved for every entire `ξ` satisfying
`ξ (star s) = star (ξ s)`.

## Main definitions

* `rescaledDedekindReciprocal`: The padded reciprocal polynomial in the saddle normalization.
* `dedekindCauchyNumerator`: The entire numerator of the Cauchy integral.

## Main results

* `dedekind_cauchy_representation_of_jet`: The Cauchy representation, given that
  `dedekindF ξ` is entire with Taylor jet `dedekindGammaCoeff ξ`.
* `differentiable_dedekindF`: `dedekindF ξ` is entire.
* `iteratedDeriv_dedekindF_zero`: The Taylor jet of `dedekindF ξ` is `dedekindGammaCoeff ξ`.
* `dedekind_cauchy_representation`: The Cauchy representation for an entire,
  conjugation-symmetric `ξ`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial Metric

section Generic

variable (ξ : ℂ → ℂ)

/-- The degree-`d` padded reciprocal in the saddle normalization at scale `T`,
`(T^2/d)^d R_d(d X / T^2)`. -/
noncomputable def rescaledDedekindReciprocal (d : ℕ) (T : ℝ) : ℝ[X] :=
  C ((T ^ 2 / (d : ℝ)) ^ d) *
    (dedekindReciprocal ξ d).comp (C ((d : ℝ) / T ^ 2) * X)

/-- The entire numerator of the degree-`d` Dedekind Cauchy integral. -/
noncomputable def dedekindCauchyNumerator (d : ℕ) (T x : ℝ) (u : ℂ) : ℂ :=
  dedekindF ξ ((T ^ 2 : ℝ) * u) * Complex.exp (((d : ℝ) * x : ℝ) * u)

/-- Finite-sum evaluation of the rescaled padded reciprocal. -/
theorem eval_rescaledDedekindReciprocal (d : ℕ) (hd : 1 ≤ d) (T : ℝ)
    (hT : T ≠ 0) (x : ℝ) :
    (rescaledDedekindReciprocal ξ d T).eval x =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℝ) * dedekindGammaCoeff ξ j * ((T ^ 2 / (d : ℝ)) ^ j) *
          x ^ (d - j) := by
  rw [rescaledDedekindReciprocal, eval_mul, eval_C, eval_comp, eval_mul, eval_C,
    eval_X, eval_dedekindReciprocal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_add_one_iff] at hj
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hpow : (T ^ 2 / d) ^ d * (d / T ^ 2 * x) ^ (d - j) = (T ^ 2 / d) ^ j * x ^ (d - j) := by
    rw [show (T ^ 2 / d) ^ d = (T ^ 2 / d) ^ j * (T ^ 2 / d) ^ (d - j) by
      rw [← pow_add, Nat.add_sub_cancel' hj], mul_pow, div_pow, div_pow]
    field_simp
    rw [← mul_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hT)]
  linear_combination ((d.choose j : ℝ) * dedekindGammaCoeff ξ j) * hpow

/-- The `d`-th derivative at the origin of the Dedekind numerator is `d^d`
times the rescaled reciprocal, given the Taylor jet of `dedekindF ξ`. -/
theorem iteratedDeriv_dedekindCauchyNumerator_zero
    (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : T ≠ 0) (x : ℝ)
    (hF : Differentiable ℂ (dedekindF ξ))
    (hjet : ∀ j ≤ d, iteratedDeriv j (dedekindF ξ) 0 = (dedekindGammaCoeff ξ j : ℂ)) :
    iteratedDeriv d (dedekindCauchyNumerator ξ d T x) 0 =
      (d : ℂ) ^ d * (↑((rescaledDedekindReciprocal ξ d T).eval x) : ℂ) := by
  have hscaled : Differentiable ℂ
      (fun u : ℂ => dedekindF ξ (((T ^ 2 : ℝ) : ℂ) * u)) :=
    hF.comp (by fun_prop)
  rw [show dedekindCauchyNumerator ξ d T x = fun u : ℂ =>
      dedekindF ξ (((T ^ 2 : ℝ) : ℂ) * u) *
        Complex.exp (((d : ℝ) * x : ℝ) * u) by rfl,
    iteratedDeriv_fun_mul hscaled.contDiff.contDiffAt (by fun_prop),
    eval_rescaledDedekindReciprocal ξ d hd T hT x]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_add_one_iff] at hj
  rw [iteratedDeriv_comp_const_mul hF.contDiff]
  simp only [mul_zero]
  rw [hjet j hj, iteratedDeriv_cexp_const_mul]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  have hD0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hpow : ((T : ℂ) ^ 2) ^ j * ((d : ℂ) * (x : ℂ)) ^ (d - j) =
      (d : ℂ) ^ d * ((T : ℂ) ^ 2 / d) ^ j * (x : ℂ) ^ (d - j) := by
    rw [show (d : ℂ) ^ d = (d : ℂ) ^ j * (d : ℂ) ^ (d - j) by
      rw [← pow_add, Nat.add_sub_cancel' hj], div_pow, mul_pow]
    field_simp
  linear_combination ((d.choose j : ℂ) * (dedekindGammaCoeff ξ j : ℂ)) * hpow

/-- Exact Cauchy representation of the rescaled Dedekind reciprocal, for any
candidate `ξ` whose square-variable series is entire with the expected jet. -/
theorem dedekind_cauchy_representation_of_jet
    (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : T ≠ 0) (x ρ : ℝ) (hρ : 0 < ρ)
    (hF : Differentiable ℂ (dedekindF ξ))
    (hjet : ∀ j ≤ d, iteratedDeriv j (dedekindF ξ) 0 = (dedekindGammaCoeff ξ j : ℂ)) :
    (↑((rescaledDedekindReciprocal ξ d T).eval x) : ℂ) =
      ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ), dedekindCauchyNumerator ξ d T x u / u ^ (d + 1)) := by
  have hnum : Differentiable ℂ (dedekindCauchyNumerator ξ d T x) := by
    unfold dedekindCauchyNumerator
    exact (hF.comp (by fun_prop)).mul (by fun_prop)
  rw [cauchy_circle_normalized d hd ρ hρ _ hnum.differentiableOn,
    iteratedDeriv_dedekindCauchyNumerator_zero ξ d hd T hT x hF hjet]
  have hd0 : (d : ℂ) ^ d ≠ 0 := pow_ne_zero d (by exact_mod_cast (Nat.ne_of_gt hd))
  field_simp

end Generic

/-- The scalar power series whose sum is `dedekindF ξ`. -/
private noncomputable def dedekindFSeries (ξ : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    fun j : ℕ ↦ (dedekindGammaCoeff ξ j : ℂ) / (j.factorial : ℂ)

private theorem dedekindF_eq_series_sum (ξ : ℂ → ℂ) :
    dedekindF ξ = (dedekindFSeries ξ).sum := by
  funext z
  rw [dedekindF]
  change _ = FormalMultilinearSeries.ofScalarsSum _ z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

section Analytic

variable {ξ : ℂ → ℂ} (hξ : Differentiable ℂ ξ) (hconj : ∀ s : ℂ, ξ (star s) = star (ξ s))

include hξ hconj

omit hconj in
private theorem centered_entire : Differentiable ℂ (centeredDedekindFunction ξ) :=
  hξ.comp ((differentiable_const (1 / 2 : ℂ)).add differentiable_id)

omit hξ in
private theorem iteratedDeriv_centered_star : ∀ n : ℕ,
    (starRingEnd ℂ ∘ iteratedDeriv n (centeredDedekindFunction ξ) ∘ starRingEnd ℂ) =
      iteratedDeriv n (centeredDedekindFunction ξ) := by
  intro n
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero]
      funext w
      simp only [Function.comp_apply, centeredDedekindFunction]
      have hs := hconj (1 / 2 + w)
      rw [Complex.star_def] at hs
      rw [show (1 / 2 : ℂ) + (starRingEnd ℂ) w = (starRingEnd ℂ) (1 / 2 + w) by
        rw [map_add, map_div₀, map_one, map_ofNat], hs]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      calc
        (starRingEnd ℂ ∘ deriv (iteratedDeriv n (centeredDedekindFunction ξ)) ∘
            starRingEnd ℂ) =
            deriv (starRingEnd ℂ ∘ iteratedDeriv n (centeredDedekindFunction ξ) ∘
              starRingEnd ℂ) :=
          deriv_conj_conj.symm
        _ = deriv (iteratedDeriv n (centeredDedekindFunction ξ)) := congrArg deriv ih

omit hξ in
private theorem iteratedDeriv_centered_zero_im (n : ℕ) :
    (iteratedDeriv n (centeredDedekindFunction ξ) 0).im = 0 := by
  have h := congrFun (iteratedDeriv_centered_star hconj n) 0
  simp only [Function.comp_apply, map_zero] at h
  exact Complex.conj_eq_iff_im.mp h

omit hξ in
/-- The normalized even Taylor coefficient of the centered completed function
is the coefficient of `dedekindF`. -/
theorem centered_even_taylorCoeff (j : ℕ) :
    ((2 * j).factorial : ℂ)⁻¹ * iteratedDeriv (2 * j) (centeredDedekindFunction ξ) 0 =
      (dedekindGammaCoeff ξ j : ℂ) / (j.factorial : ℂ) := by
  have hd : iteratedDeriv (2 * j) (centeredDedekindFunction ξ) 0 =
      (iteratedDeriv (2 * j) (centeredDedekindFunction ξ) 0).re :=
    Complex.ext (by simp) (by simp [iteratedDeriv_centered_zero_im hconj])
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [hd, dedekindGammaCoeff]
  push_cast
  field_simp

private theorem summable_dedekindFCoeff_mul_pow (z : ℂ) :
    Summable fun j : ℕ ↦
      (dedekindGammaCoeff ξ j : ℂ) / (j.factorial : ℂ) * z ^ j := by
  obtain ⟨w, rfl⟩ := Complex.isSquare z
  let a : ℕ → ℂ := fun n ↦
    (n.factorial : ℂ)⁻¹ • w ^ n • iteratedDeriv n (centeredDedekindFunction ξ) 0
  have ht : HasSum a ((centeredDedekindFunction ξ) w) := by
    simpa only [a, sub_zero] using
      Complex.hasSum_taylorSeries_of_entire (centered_entire hξ) 0 w
  have he : Summable (fun k ↦ a (2 * k)) :=
    ht.summable.comp_injective (i := fun k : ℕ ↦ 2 * k) fun _ _ h ↦
      Nat.mul_left_cancel (by norm_num) h
  convert he using 1
  funext j
  rw [show a (2 * j) =
      (((2 * j).factorial : ℂ)⁻¹ * iteratedDeriv (2 * j) (centeredDedekindFunction ξ) 0) *
        w ^ (2 * j) by
      simp [a, smul_eq_mul, mul_comm, mul_left_comm]]
  rw [centered_even_taylorCoeff hconj, pow_mul, pow_two]

private theorem dedekindFSeries_radius : (dedekindFSeries ξ).radius = ⊤ := by
  apply (dedekindFSeries ξ).radius_eq_top_of_summable_norm
  intro r
  have h := (summable_dedekindFCoeff_mul_pow hξ hconj (r : ℂ)).norm
  simpa [dedekindFSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul] using h

/-- The square-variable Dedekind series of an entire, conjugation-symmetric
`ξ` is entire. -/
theorem differentiable_dedekindF : Differentiable ℂ (dedekindF ξ) := by
  rw [dedekindF_eq_series_sum]
  have hp := (dedekindFSeries ξ).hasFPowerSeriesOnBall
    (by simp [dedekindFSeries_radius hξ hconj])
  intro z
  exact (hp.analyticAt_of_mem
    (by simp [dedekindFSeries_radius hξ hconj])).differentiableAt

/-- The Taylor jet of `dedekindF ξ` at the origin is `dedekindGammaCoeff ξ`. -/
theorem iteratedDeriv_dedekindF_zero (j : ℕ) :
    iteratedDeriv j (dedekindF ξ) 0 = (dedekindGammaCoeff ξ j : ℂ) := by
  have hp : HasFPowerSeriesOnBall (dedekindF ξ) (dedekindFSeries ξ) 0 ⊤ := by
    rw [dedekindF_eq_series_sum]
    simpa only [dedekindFSeries_radius hξ hconj] using
      (dedekindFSeries ξ).hasFPowerSeriesOnBall (by simp [dedekindFSeries_radius hξ hconj])
  have h := hp.factorial_smul (1 : ℂ) j
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h]
  simp only [dedekindFSeries, FormalMultilinearSeries.ofScalars_apply_eq, one_pow]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_eq_mul]
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp [hj]

/-- Exact Cauchy representation of the rescaled Dedekind reciprocal polynomial, for an entire
conjugation-symmetric completed function `ξ`, any nonzero scale `T` and any radius `ρ > 0`. -/
theorem dedekind_cauchy_representation (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : T ≠ 0)
    (x ρ : ℝ) (hρ : 0 < ρ) :
    (↑((rescaledDedekindReciprocal ξ d T).eval x) : ℂ) =
      ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ), dedekindCauchyNumerator ξ d T x u / u ^ (d + 1)) :=
  dedekind_cauchy_representation_of_jet ξ d hd T hT x ρ hρ
    (differentiable_dedekindF hξ hconj)
    (fun j _ => iteratedDeriv_dedekindF_zero hξ hconj j)

end Analytic

end RiemannJensen
