module

public import RiemannJensen.Analysis.Scale
public import RiemannJensen.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact coefficient and Cauchy representations

This file expresses the rescaled reciprocal Jensen polynomial `rescaledJensen d` as a normalized
Cauchy circle integral of `cauchyNumerator d x`, assuming that `riemannF` is entire and has the
coefficients `gammaCoeff j` as its Taylor coefficients at the origin.

## Main definitions

* `cauchyNumerator`: The entire numerator of the degree-`d` Cauchy integral.
* `rescaledJensenSum`: The finite coefficient sum evaluating the rescaled reciprocal Jensen
  polynomial.
* `derivativeJensenSum`: The derivative convolution attached to the numerator.

## Main results

* `eval_rescaledJensen_eq_sum`: Evaluation of `rescaledJensen d` as `rescaledJensenSum`.
* `cauchy_circle_normalized`: Cauchy's formula for the `d`-th derivative at the origin, in the
  normalization used here.
* `cauchy_representation_of_riemannF_jet`: The circle-integral representation of
  `rescaledJensen d`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial MeasureTheory Metric
open scoped Interval

/-- The entire numerator occurring in the degree-`d` Cauchy integral. -/
noncomputable def cauchyNumerator (d : ℕ) (x : ℝ) (u : ℂ) : ℂ :=
  riemannF (((scaleT d) ^ 2 : ℝ) * u) *
    Complex.exp (((d : ℝ) * x : ℝ) * u)

/-- The finite coefficient sum evaluating the rescaled reciprocal Jensen polynomial. -/
noncomputable def rescaledJensenSum (d : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1),
    (d.choose j : ℝ) * gammaCoeff j *
      (((scaleT d) ^ 2 / (d : ℝ)) ^ j) * x ^ (d - j)

/-- Reversing a genuine degree-`d` Jensen polynomial gives the coefficient
formula below. -/
theorem eval_reciprocalJensen_eq_sum (d : ℕ) (hγ : gammaCoeff d ≠ 0) (x : ℝ) :
    (reciprocalJensen d).eval x =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℝ) * gammaCoeff j * x ^ (d - j) := by
  classical
  unfold reciprocalJensen
  rw [Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le ((Polynomial.reverse_natDegree_le _).trans
      (natDegree_jensenPolynomial_le d))) x]
  simp only [Polynomial.coeff_reverse]
  rw [natDegree_jensenPolynomial d hγ, ← Finset.sum_range_reflect
    (fun j => (d.choose j : ℝ) * gammaCoeff j * x ^ (d - j)) (d + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hk
  rw [Polynomial.revAt_le hk, coeff_jensenPolynomial]
  have e : d + 1 - 1 - k = d - k := by omega
  simp only [Nat.sub_le, ite_true, e, Nat.sub_sub_self hk]

/-- Exact finite-sum evaluation of the rescaled reciprocal Jensen polynomial. -/
theorem eval_rescaledJensen_eq_sum (d : ℕ) (hd : 1 ≤ d)
    (hγ : gammaCoeff d ≠ 0) (x : ℝ) :
    (rescaledJensen d).eval x = rescaledJensenSum d x := by
  rw [eval_rescaledJensen, eval_reciprocalJensen_eq_sum d hγ]
  unfold rescaledJensenSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hj
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hT0 : scaleT d ≠ 0 :=
    ne_of_gt (lt_trans (by positivity) (scaleT_gt_base d hd))
  let a : ℝ := (scaleT d) ^ 2 / (d : ℝ)
  let b : ℝ := (d : ℝ) / (scaleT d) ^ 2
  have hab : a * b = 1 := by
    dsimp [a, b]
    field_simp
  have hpow : a ^ d * (b * x) ^ (d - j) = a ^ j * x ^ (d - j) := by
    rw [show a ^ d = a ^ j * a ^ (d - j) by rw [← pow_add, Nat.add_sub_cancel' hj],
      mul_pow]
    calc
      (a ^ j * a ^ (d - j)) * (b ^ (d - j) * x ^ (d - j)) =
          a ^ j * (a * b) ^ (d - j) * x ^ (d - j) := by
            rw [mul_pow]
            ring
      _ = a ^ j * x ^ (d - j) := by simp [hab]
  dsimp [a, b] at hpow
  linear_combination ((d.choose j : ℝ) * gammaCoeff j) * hpow

/-- The unnormalized derivative convolution attached to the numerator. -/
noncomputable def derivativeJensenSum (d : ℕ) (x B : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    (d.choose j : ℂ) * (gammaCoeff j : ℂ) * (B : ℂ) ^ j *
      (((d : ℝ) * x : ℝ) : ℂ) ^ (d - j)

/-- If an entire function has the prescribed derivatives at the origin, the
`d`-th derivative of its product with the exponential is the finite Jensen
convolution. -/
theorem iteratedDeriv_mul_cexp_at_zero
    (d : ℕ) (x B : ℝ) (f : ℂ → ℂ)
    (hf : ContDiffAt ℂ d f 0)
    (hjet : ∀ j ≤ d, iteratedDeriv j f 0 = (gammaCoeff j : ℂ) * (B : ℂ) ^ j) :
    iteratedDeriv d (fun u : ℂ => f u * Complex.exp (((d : ℝ) * x : ℝ) * u)) 0 =
      derivativeJensenSum d x B := by
  rw [iteratedDeriv_fun_mul hf (by fun_prop)]
  unfold derivativeJensenSum
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hj
  rw [hjet j hj, iteratedDeriv_cexp_const_mul]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  ring

/-- The derivative convolution is exactly `d^d` times the rescaled
reciprocal Jensen sum. -/
theorem derivativeJensenSum_scale_eq
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    derivativeJensenSum d x ((scaleT d) ^ 2) =
      (d : ℂ) ^ d * (rescaledJensenSum d x : ℂ) := by
  unfold derivativeJensenSum rescaledJensenSum
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hj
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  let D : ℂ := (d : ℂ)
  let B : ℂ := ((scaleT d : ℂ) ^ 2)
  have hD0 : D ≠ 0 := hd0
  have hpow : B ^ j * (D * (x : ℂ)) ^ (d - j) =
      D ^ d * (B / D) ^ j * (x : ℂ) ^ (d - j) := by
    rw [show D ^ d = D ^ j * D ^ (d - j) by rw [← pow_add, Nat.add_sub_cancel' hj],
      div_pow, mul_pow]
    field_simp
  dsimp [B, D] at hpow
  linear_combination ((d.choose j : ℂ) * (gammaCoeff j : ℂ)) * hpow

/-- If the scaled copy of `riemannF` has the prescribed Taylor jet at the origin, the `d`-th
derivative of `cauchyNumerator d x` at the origin is `d ^ d` times the rescaled reciprocal
Jensen polynomial at `x`. -/
theorem iteratedDeriv_cauchyNumerator_at_zero_of_jet
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hγ : gammaCoeff d ≠ 0)
    (hf : ContDiffAt ℂ d
      (fun u : ℂ => riemannF (((scaleT d) ^ 2 : ℝ) * u)) 0)
    (hjet : ∀ j ≤ d,
      iteratedDeriv j (fun u : ℂ => riemannF (((scaleT d) ^ 2 : ℝ) * u)) 0 =
        (gammaCoeff j : ℂ) * (((scaleT d) ^ 2 : ℝ) : ℂ) ^ j) :
    iteratedDeriv d (cauchyNumerator d x) 0 =
      (d : ℂ) ^ d * (↑((rescaledJensen d).eval x) : ℂ) := by
  rw [show cauchyNumerator d x = fun u : ℂ =>
      riemannF (((scaleT d) ^ 2 : ℝ) * u) *
        Complex.exp (((d : ℝ) * x : ℝ) * u) by rfl,
    iteratedDeriv_mul_cexp_at_zero d x ((scaleT d) ^ 2) _ hf hjet,
    derivativeJensenSum_scale_eq d hd x, eval_rescaledJensen_eq_sum d hd hγ x]

/-- Cauchy's formula for the `d`-th derivative at the origin of a function differentiable on
a closed disc, in the scalar normalization used in this file. -/
theorem cauchy_circle_normalized
    (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ) (hρ : 0 < ρ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (closedBall 0 ρ)) :
    ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ), g u / u ^ (d + 1)) =
      iteratedDeriv d g 0 / (d : ℂ) ^ d := by
  have hc :
      (∮ u : ℂ in C(0, ρ), g u / u ^ (d + 1)) =
        ((2 : ℂ) * Real.pi * Complex.I / (d.factorial : ℂ)) *
          iteratedDeriv d g 0 := by
    simpa [div_eq_mul_inv, mul_comm] using hg.circleIntegral_one_div_sub_center_pow_smul hρ d
  rw [hc]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hfac : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt Real.pi_pos
  field_simp

/-- The circle-integral representation of the rescaled reciprocal Jensen polynomial, given
differentiability of the numerator and the value of its `d`-th derivative at the origin. -/
theorem cauchy_representation_of_iteratedDeriv
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ (cauchyNumerator d x) (closedBall 0 ρ))
    (hderiv : iteratedDeriv d (cauchyNumerator d x) 0 =
      (d : ℂ) ^ d * (↑((rescaledJensen d).eval x) : ℂ)) :
    (↑((rescaledJensen d).eval x) : ℂ) =
      ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ), cauchyNumerator d x u / u ^ (d + 1)) := by
  rw [cauchy_circle_normalized d hd ρ hρ (cauchyNumerator d x) hg, hderiv]
  have hd0 : (d : ℂ) ^ d ≠ 0 := pow_ne_zero d (by exact_mod_cast (Nat.ne_of_gt hd))
  field_simp

/-- The circle-integral representation of the rescaled reciprocal Jensen polynomial, for
entire `riemannF` with nonvanishing top coefficient and Taylor coefficients `gammaCoeff j`
at the origin. -/
theorem cauchy_representation_of_riemannF_jet
    (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hγ : gammaCoeff d ≠ 0)
    (hF : Differentiable ℂ riemannF)
    (hjet : ∀ j ≤ d, iteratedDeriv j riemannF 0 = (gammaCoeff j : ℂ)) :
    (↑((rescaledJensen d).eval x) : ℂ) =
      ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ), cauchyNumerator d x u / u ^ (d + 1)) := by
  have hscaled : Differentiable ℂ
      (fun u : ℂ => riemannF (((scaleT d) ^ 2 : ℝ) * u)) := hF.comp (by fun_prop)
  have hscaledJet : ∀ j ≤ d,
      iteratedDeriv j (fun u : ℂ => riemannF (((scaleT d) ^ 2 : ℝ) * u)) 0 =
        (gammaCoeff j : ℂ) * (((scaleT d) ^ 2 : ℝ) : ℂ) ^ j := by
    intro j hj
    rw [iteratedDeriv_comp_const_mul hF.contDiff]
    simp only [mul_zero]
    rw [hjet j hj]
    ring
  have hnum : Differentiable ℂ (cauchyNumerator d x) := by
    unfold cauchyNumerator
    exact hscaled.mul (by fun_prop)
  exact cauchy_representation_of_iteratedDeriv d hd x ρ hρ hnum.differentiableOn
    (iteratedDeriv_cauchyNumerator_at_zero_of_jet d hd x hγ hscaled.contDiff.contDiffAt
      hscaledJet)

end RiemannJensen
