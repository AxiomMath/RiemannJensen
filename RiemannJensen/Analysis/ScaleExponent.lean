module

public import RiemannJensen.Analysis.SaddleDefinitions

/-!
# Exact exponential scaling on the lower branch

With `T = scaleT d` and `Λ = scaleLambda d`, the exponent
`(T / 2) √u (log (T / 2π) - 1 + (log u) / 2)` equals `π d √u (1 + (log u) / Λ)`, where `√u` and
`log u` are the lower branches `lowerSqrt` and `lowerLog`.

## Main results

* `scale_exponent_lower_branch`: The scaling identity for an arbitrary `u : ℂ`.
* `scale_exponent_lower_circle`: The same identity for `u = r ^ 2 * exp (I * θ)` with
  `-π ≤ θ ≤ 0`, with both lower branches evaluated explicitly.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- For `d ≥ 1` and `u : ℂ`, `(T / 2) * lowerSqrt u * (log (T / 2π) - 1 + lowerLog u / 2)` equals
`π d * lowerSqrt u * (1 + lowerLog u / Λ)`, where `T = scaleT d` and `Λ = scaleLambda d`. -/
theorem scale_exponent_lower_branch (d : ℕ) (hd : 1 ≤ d) (u : ℂ) :
    (((scaleT d / 2 : ℝ) : ℂ) * lowerSqrt u) *
        ((((Real.log (scaleT d / (2 * Real.pi)) - 1 : ℝ) : ℂ) +
          lowerLog u / 2)) =
      (((Real.pi * d : ℝ) : ℂ) * lowerSqrt u) *
        (1 + lowerLog u / (scaleLambda d : ℂ)) := by
  have hΛ : scaleLambda d ≠ 0 := (scaleLambda_pos d hd).ne'
  have hprod : (scaleT d : ℂ) * (scaleLambda d : ℂ) = 4 * (Real.pi : ℂ) * (d : ℂ) := by
    exact_mod_cast scaleT_mul_scaleLambda d hd
  rw [← scaleLambda_div_two d]
  push_cast
  field_simp [hΛ]
  linear_combination (lowerSqrt u * (scaleLambda d + lowerLog u)) * hprod

/-- The same scaling identity after evaluating both lower branches on the
closed lower circular arc. -/
theorem scale_exponent_lower_circle (d : ℕ) (hd : 1 ≤ d)
    {r θ : ℝ} (hr : 0 < r) (hθlower : -Real.pi ≤ θ) (hθupper : θ ≤ 0) :
    (((scaleT d / 2 : ℝ) : ℂ) *
        ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2))) *
      ((((Real.log (scaleT d / (2 * Real.pi)) - 1 : ℝ) : ℂ) +
        (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ)) / 2)) =
    (((Real.pi * d : ℝ) : ℂ) *
        ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2))) *
      (1 + ((((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ))) /
        (scaleLambda d : ℂ)) := by
  have h := scale_exponent_lower_branch d hd (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * θ))
  rwa [lowerSqrt_sq_mul_exp_I_mul hr hθlower hθupper,
    lowerLog_sq_mul_exp_I_mul hr hθlower hθupper] at h

end RiemannJensen
