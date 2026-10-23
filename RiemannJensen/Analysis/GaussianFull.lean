module

public import RiemannJensen.Analysis.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform complex Gaussian estimate

For a phase `p` close to the quadratic `-A y² / 2` on a window around `0`, the integral of
`f y * exp (n * p y)` over the window is compared with the corresponding Gaussian integral. At
the cutoff `n ^ (-2/5)` the error is of order `n ^ (-3/5)`, with an explicit constant.

## Main definitions

* `gaussianCutoff`: The cutoff `n ^ (-2/5)`.

## Main results

* `central_complex_gaussian_error`: The error on the window `[-η, η]` is at most
  `(C * (n * C * η ^ 3) + C * η) * (2 * η)`.
* `central_complex_gaussian_error_at_cutoff`: At `η = gaussianCutoff n`, the error is at most
  `(2 * C ^ 2 + 2 * C) * n ^ (-3/5)`.
* `uniform_complex_gaussian_estimate_of_tail_estimates`: Given bounds on the two tail
  contributions, the integral over `[-1, 1]` differs from `f 0 * (π / ((n / 2) * A)) ^ (1/2)` by
  an explicit multiple of `n ^ (-3/5)`.
-/

@[expose] public section

namespace RiemannJensen

namespace Gaussian

open Complex Set MeasureTheory intervalIntegral

/-- The cutoff `n ^ (-2/5)`. -/
noncomputable def gaussianCutoff (n : ℝ) : ℝ := n ^ (-(2 : ℝ) / 5)

/-- For `0 < n`, `gaussianCutoff n` is positive. -/
lemma gaussianCutoff_pos {n : ℝ} (hn : 0 < n) : 0 < gaussianCutoff n :=
  Real.rpow_pos_of_pos hn _

/-- For `1 ≤ n`, `gaussianCutoff n ≤ 1`. -/
lemma gaussianCutoff_le_one {n : ℝ} (hn : 1 ≤ n) : gaussianCutoff n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)

/-- For `0 < n`, `n * gaussianCutoff n = n ^ (3/5)`. -/
lemma gaussianCutoff_mul_scale {n : ℝ} (hn : 0 < n) :
    n * gaussianCutoff n = n ^ ((3 : ℝ) / 5) := by
  rw [gaussianCutoff, show (3 : ℝ) / 5 = 1 + -(2 : ℝ) / 5 by norm_num,
    Real.rpow_add hn, Real.rpow_one]

/-- For `0 < n`, `n * gaussianCutoff n ^ 4 = n ^ (-3/5)`. -/
lemma scale_mul_cutoff_pow_four {n : ℝ} (hn : 0 < n) :
    n * gaussianCutoff n ^ 4 = n ^ (-(3 : ℝ) / 5) := by
  rw [gaussianCutoff, ← Real.rpow_natCast, ← Real.rpow_mul hn.le,
    show -(3 : ℝ) / 5 = 1 + -(2 : ℝ) / 5 * (4 : ℕ) by norm_num, Real.rpow_add hn, Real.rpow_one]

/-- For `1 ≤ n`, `gaussianCutoff n ^ 2 ≤ n ^ (-3/5)`. -/
lemma cutoff_sq_le_error_scale {n : ℝ} (hn : 1 ≤ n) :
    gaussianCutoff n ^ 2 ≤ n ^ (-(3 : ℝ) / 5) := by
  rw [gaussianCutoff, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ n)]
  exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

/-- For `0 < n`, `(n * gaussianCutoff n)⁻¹ = n ^ (-3/5)`. -/
lemma inv_scale_mul_cutoff {n : ℝ} (hn : 0 < n) :
    (n * gaussianCutoff n)⁻¹ = n ^ (-(3 : ℝ) / 5) := by
  rw [gaussianCutoff_mul_scale hn, ← Real.rpow_neg hn.le]
  congr 1
  ring

/-- If `p` and `-A y² / 2` have nonpositive real part on `[-η, η]`, differ by at most
`C * |y| ^ 3` there, and `‖f y‖ ≤ C` and `‖f y - f 0‖ ≤ C * |y|`, then the integrals of
`f y * exp (n * p y)` and `f 0 * exp (n * (-A y² / 2))` over `[-η, η]` differ by at most
`(C * (n * C * η ^ 3) + C * η) * (2 * η)`. The bound is uniform in `A`. -/
theorem central_complex_gaussian_error {p f : ℝ → ℂ} {A : ℂ} {n C η : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hp : ∀ y ∈ Set.uIoc (-η) η, (p y).re ≤ 0)
    (hq : ∀ y ∈ Set.uIoc (-η) η, (-A * ((y : ℂ) ^ 2) / 2).re ≤ 0)
    (hpq : ∀ y ∈ Set.uIoc (-η) η,
      ‖p y - (-A * ((y : ℂ) ^ 2) / 2)‖ ≤ C * |y| ^ 3)
    (hf : ∀ y ∈ Set.uIoc (-η) η, ‖f y‖ ≤ C)
    (hf0 : ∀ y ∈ Set.uIoc (-η) η, ‖f y - f 0‖ ≤ C * |y|)
    (hi₁ : IntervalIntegrable (fun y => f y * Complex.exp ((n : ℂ) * p y)) volume (-η) η)
    (hi₂ : IntervalIntegrable
      (fun y => f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2)))
      volume (-η) η) :
    ‖(∫ y in (-η)..η, f y * Complex.exp ((n : ℂ) * p y)) -
        ∫ y in (-η)..η,
          f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))‖ ≤
      (C * (n * C * η ^ 3) + C * η) * (2 * η) := by
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  apply norm_intervalIntegral_le_two_mul hη
  intro y hy
  have hyabs : |y| ≤ η := by
    rw [Set.uIoc_of_le (neg_le_self hη)] at hy
    exact abs_le.2 ⟨hy.1.le, hy.2⟩
  have hexp := norm_exp_phase_sub_quadratic_le
    (q := fun y => -A * ((y : ℂ) ^ 2) / 2) (K := C) (y := y)
    (hp y hy) (hq y hy) hn (hpq y hy)
  calc
    ‖f y * Complex.exp ((n : ℂ) * p y) -
        f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))‖
        = ‖f y * (Complex.exp ((n : ℂ) * p y) -
              Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))) +
            (f y - f 0) *
              Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))‖ := by ring_nf
    _ ≤ ‖f y‖ * ‖Complex.exp ((n : ℂ) * p y) -
              Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))‖ +
            ‖(f y - f 0) *
              Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))‖ :=
          (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ C * (n * C * |y| ^ 3) + C * |y| := by
          apply add_le_add
          · exact mul_le_mul (hf y hy) hexp (norm_nonneg _) hC
          · refine (norm_mul_exp_le_norm_of_re_nonpos ?_).trans (hf0 y hy)
            rw [re_ofReal_mul]
            exact mul_nonpos_of_nonneg_of_nonpos hn (hq y hy)
    _ ≤ C * (n * C * η ^ 3) + C * η := by gcongr

/-- With `η = gaussianCutoff n` and `1 ≤ n`, the error in `central_complex_gaussian_error` is at
most `(2 * C ^ 2 + 2 * C) * n ^ (-3/5)`. -/
theorem central_complex_gaussian_error_at_cutoff {p f : ℝ → ℂ} {A : ℂ} {n C : ℝ}
    (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hp : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n), (p y).re ≤ 0)
    (hq : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      (-A * ((y : ℂ) ^ 2) / 2).re ≤ 0)
    (hpq : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      ‖p y - (-A * ((y : ℂ) ^ 2) / 2)‖ ≤ C * |y| ^ 3)
    (hf : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n), ‖f y‖ ≤ C)
    (hf0 : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      ‖f y - f 0‖ ≤ C * |y|)
    (hi₁ : IntervalIntegrable (fun y => f y * Complex.exp ((n : ℂ) * p y)) volume
      (-(gaussianCutoff n)) (gaussianCutoff n))
    (hi₂ : IntervalIntegrable
      (fun y => f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))) volume
      (-(gaussianCutoff n)) (gaussianCutoff n)) :
    ‖(∫ y in (-(gaussianCutoff n))..(gaussianCutoff n),
          f y * Complex.exp ((n : ℂ) * p y)) -
        ∫ y in (-(gaussianCutoff n))..(gaussianCutoff n),
          f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))‖ ≤
      (2 * C ^ 2 + 2 * C) * n ^ (-(3 : ℝ) / 5) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  calc
    _ ≤ (C * (n * C * gaussianCutoff n ^ 3) + C * gaussianCutoff n) *
          (2 * gaussianCutoff n) :=
      central_complex_gaussian_error hn0.le hC (gaussianCutoff_pos hn0).le hp hq hpq hf hf0
        hi₁ hi₂
    _ = 2 * C ^ 2 * (n * gaussianCutoff n ^ 4) +
          2 * C * gaussianCutoff n ^ 2 := by ring
    _ ≤ 2 * C ^ 2 * n ^ (-(3 : ℝ) / 5) +
          2 * C * n ^ (-(3 : ℝ) / 5) := by
      gcongr
      · exact (scale_mul_cutoff_pow_four hn0).le
      · exact cutoff_sq_le_error_scale hn
    _ = (2 * C ^ 2 + 2 * C) * n ^ (-(3 : ℝ) / 5) := by ring

/-- Given bounds of order `n ^ (-3/5)` on the difference between the integrals of
`f y * exp (n * p y)` over `[-1, 1]` and over the cutoff window, and on the difference between
the Gaussian integral over the cutoff window and `f 0 * (π / ((n / 2) * A)) ^ (1/2)`, the
integral over `[-1, 1]` differs from `f 0 * (π / ((n / 2) * A)) ^ (1/2)` by at most
`(2 * C ^ 2 + 6 * C + 6 * C / c + 2 * C ^ 2 / c ^ 2) * n ^ (-3/5)`. -/
theorem uniform_complex_gaussian_estimate_of_tail_estimates
    {p f : ℝ → ℂ} {A : ℂ} {n c C : ℝ}
    (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hp : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n), (p y).re ≤ 0)
    (hq : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      (-A * ((y : ℂ) ^ 2) / 2).re ≤ 0)
    (hpq : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      ‖p y - (-A * ((y : ℂ) ^ 2) / 2)‖ ≤ C * |y| ^ 3)
    (hf : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n), ‖f y‖ ≤ C)
    (hf0 : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      ‖f y - f 0‖ ≤ C * |y|)
    (hi₁ : IntervalIntegrable (fun y => f y * Complex.exp ((n : ℂ) * p y)) volume
      (-(gaussianCutoff n)) (gaussianCutoff n))
    (hi₂ : IntervalIntegrable
      (fun y => f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))) volume
      (-(gaussianCutoff n)) (gaussianCutoff n))
    (hphaseTail :
      ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
        ∫ y in (-(gaussianCutoff n))..(gaussianCutoff n),
          f y * Complex.exp ((n : ℂ) * p y)‖ ≤
        (6 * C / c + 2 * C ^ 2 / c ^ 2) * n ^ (-(3 : ℝ) / 5))
    (hgaussianTail :
      ‖(∫ y in (-(gaussianCutoff n))..(gaussianCutoff n),
          f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))) -
        f 0 * (((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^ (1 / 2 : ℂ))‖ ≤
        (4 * C) * n ^ (-(3 : ℝ) / 5)) :
    ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
        f 0 * (((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^ (1 / 2 : ℂ))‖ ≤
      (2 * C ^ 2 + 6 * C + 6 * C / c + 2 * C ^ 2 / c ^ 2) *
        n ^ (-(3 : ℝ) / 5) := by
  refine ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hphaseTail
    ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add (central_complex_gaussian_error_at_cutoff hn hC hp hq hpq hf hf0 hi₁ hi₂)
        hgaussianTail)))).trans_eq ?_
  ring

end Gaussian

end RiemannJensen
