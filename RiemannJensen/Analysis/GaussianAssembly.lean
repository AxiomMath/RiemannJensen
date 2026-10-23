module

public import RiemannJensen.Analysis.GaussianTails
public import RiemannJensen.Analysis.GaussianImproper

/-!
# Uniform complex Gaussian estimate

A uniform estimate for perturbed complex-Gaussian integrals, obtained by combining the
central-window estimate, nonstationary phase on the outer intervals, and the oscillatory
complex-Gaussian tail estimate.

## Main results

* `uniform_complex_gaussian_estimate`: The integral of `f y * exp (n * p y)` over `[-1, 1]`
  differs from its complex-Gaussian approximation by `O(n ^ (-3 / 5))`, uniformly in the data.
-/

@[expose] public section

namespace RiemannJensen

namespace Gaussian

open Complex Set MeasureTheory intervalIntegral

/-- The uniform perturbed complex-Gaussian estimate: if `p` is close to `-A y ^ 2 / 2` near `0`,
`p'` is bounded below by `c * |y|` away from `0`, and `f`, `f'`, `p''` are bounded by `C`, then
`∫ y in -1..1, f y * exp (n * p y)` differs from `f 0 * (π / ((n / 2) * A)) ^ (1 / 2)` by at
most `(2 * C ^ 2 + 6 * C + 6 * C / c + 2 * C ^ 2 / c ^ 2) * n ^ (-3 / 5)`. -/
theorem uniform_complex_gaussian_estimate
    {f f' p p' p'' : ℝ → ℂ} {A : ℂ} {n c C : ℝ}
    (hn : 1 ≤ n) (hc : 0 < c) (hC : 0 ≤ C)
    (hA_norm : ‖A‖ = 1) (hA_re : 0 < A.re)
    (hp : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n), (p y).re ≤ 0)
    (hq : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      (-A * ((y : ℂ) ^ 2) / 2).re ≤ 0)
    (hpq : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      ‖p y - (-A * ((y : ℂ) ^ 2) / 2)‖ ≤ C * |y| ^ 3)
    (hf : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n), ‖f y‖ ≤ C)
    (hf0 : ∀ y ∈ Set.uIoc (-(gaussianCutoff n)) (gaussianCutoff n),
      ‖f y - f 0‖ ≤ C * |y|)
    (hi_mid : IntervalIntegrable (fun y => f y * Complex.exp ((n : ℂ) * p y)) volume
      (-(gaussianCutoff n)) (gaussianCutoff n))
    (hi_gaussian : IntervalIntegrable
      (fun y => f 0 * Complex.exp ((n : ℂ) * (-A * ((y : ℂ) ^ 2) / 2))) volume
      (-(gaussianCutoff n)) (gaussianCutoff n))
    (hf_zero : ‖f 0‖ ≤ C)
    (hf_deriv_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      HasDerivAt f (f' y) y)
    (hp_deriv_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      HasDerivAt p (p' y) y)
    (hpp_deriv_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      HasDerivAt p' (p'' y) y)
    (hp_re_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), (p y).re ≤ 0)
    (hf_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), ‖f y‖ ≤ C)
    (hfp_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), ‖f' y‖ ≤ C)
    (hpp_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), ‖p'' y‖ ≤ C)
    (hlower_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      c * |y| ≤ ‖p' y‖)
    (hu_neg : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n)
      volume (-1) (-(gaussianCutoff n)))
    (hv_neg : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y))
      volume (-1) (-(gaussianCutoff n)))
    (hf_deriv_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1,
      HasDerivAt f (f' y) y)
    (hp_deriv_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1,
      HasDerivAt p (p' y) y)
    (hpp_deriv_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1,
      HasDerivAt p' (p'' y) y)
    (hp_re_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, (p y).re ≤ 0)
    (hf_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, ‖f y‖ ≤ C)
    (hfp_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, ‖f' y‖ ≤ C)
    (hpp_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, ‖p'' y‖ ≤ C)
    (hlower_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, c * |y| ≤ ‖p' y‖)
    (hu_pos : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n)
      volume (gaussianCutoff n) 1)
    (hv_pos : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y))
      volume (gaussianCutoff n) 1)
    (hi_neg : IntervalIntegrable
      (fun y => f y * Complex.exp ((n : ℂ) * p y))
      volume (-1) (-(gaussianCutoff n)))
    (hi_pos : IntervalIntegrable
      (fun y => f y * Complex.exp ((n : ℂ) * p y))
      volume (gaussianCutoff n) 1) :
    ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
        f 0 * (((Real.pi : ℂ) / (((n / 2 : ℝ) : ℂ) * A)) ^ (1 / 2 : ℂ))‖ ≤
      (2 * C ^ 2 + 6 * C + 6 * C / c + 2 * C ^ 2 / c ^ 2) *
        n ^ (-(3 : ℝ) / 5) :=
  uniform_complex_gaussian_estimate_of_tail_estimates
    hn hC hp hq hpq hf hf0 hi_mid hi_gaussian
    (phase_tail_at_gaussianCutoff hn hc hC
      hf_deriv_neg hp_deriv_neg hpp_deriv_neg hp_re_neg hf_neg hfp_neg hpp_neg
      hlower_neg hu_neg hv_neg hf_deriv_pos hp_deriv_pos hpp_deriv_pos hp_re_pos
      hf_pos hfp_pos hpp_pos hlower_pos hu_pos hv_pos hi_neg hi_mid hi_pos)
    (constant_scaled_complex_gaussian_tail_at_cutoff (f := f) hn hC hA_norm hA_re hf_zero)

end Gaussian

end RiemannJensen
