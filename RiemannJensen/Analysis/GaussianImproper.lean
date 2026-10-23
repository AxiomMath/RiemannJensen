module

public import RiemannJensen.Analysis.GaussianFull
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tail estimates for complex Gaussian integrals

For a complex coefficient `b` with `0 < b.re`, this file evaluates the integral of
`exp (-b * x ^ 2)` over `(η, ∞)` by integration by parts and bounds its tails in terms of `‖b‖`
and `η`, and applies these bounds to the scaled Gaussian `exp (n * (-A * y ^ 2 / 2))`.

## Main results

* `integral_Ioi_complex_gaussian_eq`: Integration by parts for a complex Gaussian on `(η, ∞)`.
* `norm_integral_Ioi_complex_gaussian_le`: The tail on `(η, ∞)` is at most
  `2 * ((2 * ‖b‖)⁻¹ * η⁻¹)` in norm.
* `constant_scaled_complex_gaussian_tail_at_cutoff`: The truncated scaled Gaussian integral
  over `[-gaussianCutoff n, gaussianCutoff n]` approximates the full one to within
  `4 * C * n ^ (-3 / 5)`.
-/

@[expose] public section

namespace RiemannJensen

namespace Gaussian

open Complex Set MeasureTheory intervalIntegral
open Filter
open scoped Topology

/-- The elementary improper reciprocal-square integral. -/
theorem integral_Ioi_inv_sq {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ in Set.Ioi η, (x ^ 2)⁻¹) = η⁻¹ := by
  have heq : (∫ x : ℝ in Set.Ioi η, (x ^ 2)⁻¹) =
      ∫ x : ℝ in Set.Ioi η, x ^ (-2 : ℝ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.rpow_neg (le_of_lt (hη.trans hx)), Real.rpow_two]
  rw [heq, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hη,
    show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- For `η > 0`, the function `x ↦ (x ^ 2)⁻¹` is integrable on `(η, ∞)`. -/
theorem integrableOn_Ioi_inv_sq {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Ioi η) := by
  apply (integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-2 : ℝ) < -1) hη).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.rpow_neg (le_of_lt (hη.trans hx)), Real.rpow_two]

/-- For `n > 0` and `0 < A.re`, the integral over `ℝ` of `exp (n * (-A * y ^ 2 / 2))` equals
`(π / ((n / 2) * A)) ^ (1 / 2)`. -/
theorem whole_scaled_complex_gaussian {A : ℂ} {n : ℝ}
    (hn : 0 < n) (hA : 0 < A.re) :
    (∫ y : ℝ, Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))) =
      (((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^ (1 / 2 : ℂ)) := by
  have hb : 0 < ((((n : ℂ) * A / 2).re)) := by
    norm_num [div_re, mul_re]
    exact mul_pos hn hA
  rw [show (((n / 2 : ℝ) : ℂ) * A) = (n : ℂ) * A / 2 by push_cast; ring]
  convert integral_gaussian_complex hb using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  congr 1
  ring

/-- For `0 < b.re` and `η > 0`, `x ↦ exp (-b * x ^ 2) / (2 * b * x ^ 2)` is integrable on
`(η, ∞)`. -/
theorem integrableOn_Ioi_complex_gaussian_remainder {b : ℂ} {η : ℝ}
    (hb : 0 < b.re) (hη : 0 < η) :
    IntegrableOn
      (fun x : ℝ => Complex.exp (-b * (x : ℂ)^2) / (2 * b * (x : ℂ)^2)) (Ioi η) := by
  have h : IntegrableOn
      (fun x : ℝ => Complex.exp (-b * (x : ℂ)^2) * (((x^2)⁻¹ : ℝ) : ℂ)) (Ioi η) := by
    apply (integrableOn_Ioi_inv_sq hη).ofReal.bdd_mul
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_cexp_neg_mul_sq b x]
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  refine IntegrableOn.congr_fun (h.mul_const (2 * b)⁻¹) (fun x hx => ?_) measurableSet_Ioi
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hη.trans hx).ne'
  push_cast
  field_simp [Complex.ne_zero_of_re_pos hb, hxC]

/-- For `0 < b.re`, `exp (-b * x ^ 2)` tends to `0` as `x → ∞`. -/
theorem tendsto_cexp_neg_mul_sq_atTop {b : ℂ} (hb : 0 < b.re) :
    Tendsto (fun x : ℝ => Complex.exp (-b * (x : ℂ)^2)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_cexp_neg_mul_sq b]
  exact Real.tendsto_exp_atBot.comp
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
      (neg_lt_zero.mpr hb))

/-- The derivative of `t ↦ exp (-b * t ^ 2)` is `-2 * b * x * exp (-b * x ^ 2)`. -/
theorem hasDerivAt_cexp_neg_mul_sq (b : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-b * (t : ℂ)^2))
      (-2 * b * (x : ℂ) * Complex.exp (-b * (x : ℂ)^2)) x := by
  have H := ((hasDerivAt_id x).ofReal_comp.pow 2).mul_const (-b)
  have H' :
      HasDerivAt (fun t : ℝ => Complex.exp (((t : ℂ)^2) * (-b)))
        (Complex.exp (((x : ℂ)^2) * (-b)) *
          (((2 : ℂ) * (x : ℂ)) * (-b))) x := by
    simpa only [id_eq, Pi.pow_apply, Nat.cast_ofNat, pow_one, mul_one,
      Nat.reduceSub, ofReal_one] using H.cexp
  convert H' using 1 <;> ring_nf

/-- Integration by parts for a complex Gaussian on a positive half-line. -/
theorem integral_Ioi_complex_gaussian_eq {b : ℂ} {η : ℝ}
    (hb : 0 < b.re) (hη : 0 < η) :
    (∫ x : ℝ in Set.Ioi η, Complex.exp (-b * (x : ℂ)^2)) =
      Complex.exp (-b * (η : ℂ)^2) / (2 * b * (η : ℂ)) -
        ∫ x : ℝ in Set.Ioi η,
          Complex.exp (-b * (x : ℂ)^2) / (2 * b * (x : ℂ)^2) := by
  let u : ℝ → ℂ := fun x => (((x⁻¹ : ℝ) : ℂ)) * (-(2 * b)⁻¹)
  let u' : ℝ → ℂ := fun x => (((-1 / x^2 : ℝ) : ℂ)) * (-(2 * b)⁻¹)
  let v : ℝ → ℂ := fun x => Complex.exp (-b * (x : ℂ)^2)
  let v' : ℝ → ℂ := fun x =>
    (-2 * b * (x : ℂ)) * Complex.exp (-b * (x : ℂ)^2)
  have hb0 : b ≠ 0 := Complex.ne_zero_of_re_pos hb
  have hu : ∀ x ∈ Ioi η, HasDerivAt u (u' x) x := fun x hx =>
    ((hasDerivAt_id x).inv (ne_of_gt (hη.trans hx))).ofReal_comp.mul_const _
  have hv : ∀ x ∈ Ioi η, HasDerivAt v (v' x) x := fun x _ => hasDerivAt_cexp_neg_mul_sq b x
  have e₁ : EqOn (fun x : ℝ => Complex.exp (-b * (x : ℂ)^2))
      (fun x => u x * v' x) (Ioi η) := by
    intro x hx
    have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hη.trans hx).ne'
    dsimp [u, v']
    push_cast
    field_simp [hb0, hxC]
  have e₂ : EqOn (fun x : ℝ => Complex.exp (-b * (x : ℂ)^2) / (2 * b * (x : ℂ)^2))
      (fun x => u' x * v x) (Ioi η) := by
    intro x hx
    have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hη.trans hx).ne'
    dsimp [u', v]
    push_cast
    field_simp [hb0, hxC]
  have huv' : IntegrableOn (u * v') (Ioi η) :=
    (integrable_cexp_neg_mul_sq hb).integrableOn.congr_fun e₁ measurableSet_Ioi
  have hu'v : IntegrableOn (u' * v) (Ioi η) :=
    (integrableOn_Ioi_complex_gaussian_remainder hb hη).congr_fun e₂ measurableSet_Ioi
  have hzero : Tendsto (u * v) (𝓝[>] η) (𝓝 (u η * v η)) := by
    have hc : ContinuousAt (u * v) η := by
      simp only [u, v]
      fun_prop (disch := positivity)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have hue : Tendsto
        (fun x : ℝ => (((x⁻¹ : ℝ) : ℂ)) * (-(2 * b)⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.ofReal.mul_const (-(2 * b)⁻¹) :
        Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ) * (-(2 * b)⁻¹)) atTop _)
    change Tendsto (fun x => u x * v x) atTop (𝓝 0)
    dsimp [u, v]
    simpa using hue.mul (tendsto_cexp_neg_mul_sq_atTop hb)
  have H := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hu hv huv' hu'v hzero hinfty
  rw [← setIntegral_congr_fun measurableSet_Ioi e₁,
    ← setIntegral_congr_fun measurableSet_Ioi e₂] at H
  have hboundary :
      -(u η * v η) = Complex.exp (-b * (η : ℂ)^2) / (2 * b * (η : ℂ)) := by
    dsimp [u, v]
    have hηC : (η : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hη)
    push_cast
    field_simp [hb0, hηC]
  rwa [zero_sub, hboundary] at H

/-- For `0 < b.re` and `η > 0`, the norm of the integral over `(η, ∞)` of
`exp (-b * x ^ 2) / (2 * b * x ^ 2)` is at most `(2 * ‖b‖)⁻¹ * η⁻¹`. -/
lemma norm_integral_Ioi_complex_gaussian_remainder {b : ℂ} {η : ℝ}
    (hb : 0 < b.re) (hη : 0 < η) :
    ‖∫ x : ℝ in Ioi η,
        Complex.exp (-b * (x : ℂ)^2) / (2 * b * (x : ℂ)^2)‖ ≤
      (2 * ‖b‖)⁻¹ * η⁻¹ := by
  have hdom : ∀ᵐ x : ℝ ∂volume.restrict (Ioi η),
      ‖Complex.exp (-b * (x : ℂ)^2) / (2 * b * (x : ℂ)^2)‖ ≤
        (2 * ‖b‖)⁻¹ * (x^2)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_div, norm_mul, norm_mul, norm_ofNat,
      norm_cexp_neg_mul_sq b x, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_pos (hη.trans hx), ← mul_inv, ← one_div]
    gcongr
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have h := MeasureTheory.norm_integral_le_of_norm_le
    ((integrableOn_Ioi_inv_sq hη).const_mul ((2 * ‖b‖)⁻¹)) hdom
  rwa [MeasureTheory.integral_const_mul, integral_Ioi_inv_sq hη] at h

/-- For `0 < b.re` and `η > 0`, the norm of the integral of `exp (-b * x ^ 2)` over `(η, ∞)` is
at most `2 * ((2 * ‖b‖)⁻¹ * η⁻¹)`. -/
theorem norm_integral_Ioi_complex_gaussian_le {b : ℂ} {η : ℝ}
    (hb : 0 < b.re) (hη : 0 < η) :
    ‖∫ x : ℝ in Ioi η, Complex.exp (-b * (x : ℂ)^2)‖ ≤
      2 * ((2 * ‖b‖)⁻¹ * η⁻¹) := by
  have hboundary :
      ‖Complex.exp (-b * (η : ℂ)^2) / (2 * b * (η : ℂ))‖ ≤
        (2 * ‖b‖)⁻¹ * η⁻¹ := by
    rw [norm_div, norm_mul, norm_mul, norm_ofNat,
      norm_cexp_neg_mul_sq b η, norm_real, Real.norm_eq_abs, abs_of_pos hη, ← mul_inv,
      ← one_div]
    gcongr
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg η])
  rw [integral_Ioi_complex_gaussian_eq hb hη]
  exact (norm_sub_le _ _).trans <|
    (add_le_add hboundary (norm_integral_Ioi_complex_gaussian_remainder hb hη)).trans_eq
      (two_mul _).symm

/-- For `0 < b.re` and `η ≥ 0`, the integral of `exp (-b * x ^ 2)` over the complement of
`(-η, η]` is twice its integral over `(η, ∞)`. -/
lemma integral_complex_gaussian_compl_eq_two_Ioi {b : ℂ} {η : ℝ}
    (hb : 0 < b.re) (hη : 0 ≤ η) :
    (∫ x : ℝ in (Ioc (-η) η)ᶜ, Complex.exp (-b * (x : ℂ)^2)) =
      2 * ∫ x : ℝ in Ioi η, Complex.exp (-b * (x : ℂ)^2) := by
  have hg := integrable_cexp_neg_mul_sq hb
  rw [compl_Ioc, setIntegral_union (Iic_disjoint_Ioi (neg_le_self hη)) measurableSet_Ioi
    hg.integrableOn hg.integrableOn, two_mul]
  congr 1
  rw [← neg_neg η, ← integral_comp_neg_Iic, neg_neg]
  simp

/-- Uniform two-sided tail estimate for a complex Gaussian. -/
theorem norm_central_sub_whole_complex_gaussian_le {b : ℂ} {η : ℝ}
    (hb : 0 < b.re) (hη : 0 < η) :
    ‖(∫ x in (-η)..η, Complex.exp (-b * (x : ℂ)^2)) -
        ∫ x : ℝ, Complex.exp (-b * (x : ℂ)^2)‖ ≤
      4 * ((2 * ‖b‖)⁻¹ * η⁻¹) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-b * (x : ℂ)^2)
  have hg : Integrable g := integrable_cexp_neg_mul_sq hb
  have hadd := integral_add_compl (s := Ioc (-η) η) measurableSet_Ioc hg
  rw [intervalIntegral.integral_of_le (neg_le_self hη.le)]
  change ‖(∫ x in Ioc (-η) η, g x) - ∫ x, g x‖ ≤ _
  have heq :
      (∫ x in Ioc (-η) η, g x) - ∫ x, g x =
        -(∫ x in (Ioc (-η) η)ᶜ, g x) := by
    rw [← hadd]
    abel
  rw [heq, norm_neg, show (∫ x in (Ioc (-η) η)ᶜ, g x) =
      2 * ∫ x in Ioi η, g x from
    integral_complex_gaussian_compl_eq_two_Ioi hb hη.le, norm_mul, norm_ofNat]
  have h := norm_integral_Ioi_complex_gaussian_le hb hη
  nlinarith

/-- Scaled form of the two-sided tail estimate. -/
theorem norm_central_sub_whole_scaled_complex_gaussian_le
    {A : ℂ} {n η : ℝ} (hn : 0 < n) (hη : 0 < η)
    (hA_norm : ‖A‖ = 1) (hA_re : 0 < A.re) :
    ‖(∫ y in (-η)..η,
          Complex.exp ((n : ℂ) * (-A * (y : ℂ)^2) / 2)) -
        ∫ y : ℝ, Complex.exp ((n : ℂ) * (-A * (y : ℂ)^2) / 2)‖ ≤
      4 * (n * η)⁻¹ := by
  let b : ℂ := (((n / 2 : ℝ) : ℂ) * A)
  have hb : 0 < b.re := by
    dsimp [b]
    norm_num [mul_re]
    exact mul_pos (half_pos hn) hA_re
  have hbn : ‖b‖ = n / 2 := by
    dsimp [b]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hn),
      hA_norm, mul_one]
  have h := norm_central_sub_whole_complex_gaussian_le hb hη
  have heq :
      (fun y : ℝ => Complex.exp (-b * (y : ℂ)^2)) =
        fun y : ℝ => Complex.exp ((n : ℂ) * (-A * (y : ℂ)^2) / 2) := by
    funext y
    congr 1
    dsimp [b]
    push_cast
    ring
  rw [heq, hbn] at h
  exact h.trans_eq (by field_simp)

/-- Uniform tail estimate after multiplying by the value of the amplitude at
the saddle. -/
theorem constant_scaled_complex_gaussian_tail_le
    {f : ℝ → ℂ} {A : ℂ} {n C η : ℝ}
    (hn : 0 < n) (hη : 0 < η) (hC : 0 ≤ C)
    (hA_norm : ‖A‖ = 1) (hA_re : 0 < A.re) (hf0 : ‖f 0‖ ≤ C) :
    ‖(∫ y in (-η)..η,
          f 0 * Complex.exp ((n : ℂ) * (-A * (y : ℂ)^2) / 2)) -
        f 0 * (((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^
          (1 / 2 : ℂ))‖ ≤
      4 * C * (n * η)⁻¹ := by
  have hwhole_eq :
      (∫ y : ℝ, Complex.exp ((n : ℂ) * (-A * ((y : ℂ)^2) / 2))) =
        ∫ y : ℝ, Complex.exp ((n : ℂ) * (-A * (y : ℂ)^2) / 2) := by
    simp only [mul_div_assoc]
  rw [← whole_scaled_complex_gaussian hn hA_re, hwhole_eq,
    intervalIntegral.integral_const_mul, ← mul_sub, norm_mul, mul_comm 4 C, mul_assoc]
  exact mul_le_mul hf0 (norm_central_sub_whole_scaled_complex_gaussian_le hn hη hA_norm hA_re)
    (norm_nonneg _) hC

/-- For `n ≥ 1`, `‖A‖ = 1`, `0 < A.re` and `‖f 0‖ ≤ C`, the integral of
`f 0 * exp (n * (-A * y ^ 2 / 2))` over `[-gaussianCutoff n, gaussianCutoff n]` differs from
`f 0 * (π / ((n / 2) * A)) ^ (1 / 2)` by at most `4 * C * n ^ (-3 / 5)`. -/
theorem constant_scaled_complex_gaussian_tail_at_cutoff
    {f : ℝ → ℂ} {A : ℂ} {n C : ℝ}
    (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hA_norm : ‖A‖ = 1) (hA_re : 0 < A.re) (hf0 : ‖f 0‖ ≤ C) :
    ‖(∫ y in (-(gaussianCutoff n))..(gaussianCutoff n),
          f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ)^2) / 2))) -
        f 0 * (((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^
          (1 / 2 : ℂ))‖ ≤
      (4 * C) * n ^ (-(3 : ℝ) / 5) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have h := constant_scaled_complex_gaussian_tail_le
    (f := f) hn0 (gaussianCutoff_pos hn0) hC hA_norm hA_re hf0
  rw [inv_scale_mul_cutoff hn0] at h
  simpa only [mul_assoc, mul_div_assoc] using h

end Gaussian

end RiemannJensen
