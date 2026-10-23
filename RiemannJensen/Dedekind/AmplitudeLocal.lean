module

public import RiemannJensen.Dedekind.GammaLogDerivative
public import RiemannJensen.Dedekind.ArchimedeanRemainder
public import RiemannJensen.Dedekind.EulerLogBounds
public import RiemannJensen.Dedekind.ContourFactorization

/-!
# Exact Gamma identities and local Dedekind amplitude facts

This file records the exact quotient identities behind the two archimedean
Gamma factors and the unconditional nonvanishing criterion for the contour
amplitude once its point lies in the Euler-product and large-Gamma sectors.
-/

@[expose] public section

namespace RiemannJensen

open Complex
open scoped ComplexOrder

private theorem complex_sqrt_two_pi_eq_exp :
    Complex.sqrt ((2 : ℂ) * Real.pi) = Complex.exp ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  have hnonneg : 0 ≤ (((2 * Real.pi : ℝ) : ℂ)) :=
    RCLike.nonneg_iff_exists_ofReal.mpr ⟨2 * Real.pi, by positivity, rfl⟩
  rw [show (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
    Complex.sqrt_of_nonneg hnonneg]
  exact GammaSector.sqrt_two_pi_eq

/-- The real Gamma factor at `1 / 2 + w`, for `w ≠ 0`, as the power `π ^ (-(1 / 2 + w) / 2)` times
the remainder `dedekindGammaRemainderReal w` times the Stirling main term
`√(2π) (w / 2) ^ (w / 2 - 1 / 4) exp (-w / 2)`. -/
theorem dedekindGammaR_exact {w : ℂ} (hw : w ≠ 0) :
    dedekindGammaR (1 / 2 + w) =
      (Real.pi : ℂ) ^ (-(1 / 2 + w) / 2) *
        (dedekindGammaRemainderReal w *
          (Complex.sqrt (2 * Real.pi) *
            Complex.cpow (w / 2) (w / 2 - 1 / 4) *
            Complex.exp (-w / 2))) := by
  have hden : Complex.sqrt (2 * Real.pi) *
      Complex.cpow (w / 2) (w / 2 - 1 / 4) * Complex.exp (-w / 2) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero sqrt_two_mul_pi_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hw (by norm_num)))))
      (Complex.exp_ne_zero _)
  have hgamma : Complex.Gamma ((1 / 2 + w) / 2) =
      dedekindGammaRemainderReal w *
        (Complex.sqrt (2 * Real.pi) *
          Complex.cpow (w / 2) (w / 2 - 1 / 4) * Complex.exp (-w / 2)) := by
    rw [dedekindGammaRemainderReal, div_mul_cancel₀ _ hden]
    congr 1
    ring
  rw [dedekindGammaR_eq, hgamma]

/-- The complex Gamma factor at `1 / 2 + w`, for `w ≠ 0`, as `2 (2π) ^ (-(1 / 2 + w))` times the
remainder `dedekindGammaRemainderComplex w` times the Stirling main term `√(2π) w ^ w exp (-w)`. -/
theorem dedekindGammaC_exact {w : ℂ} (hw : w ≠ 0) :
    dedekindGammaC (1 / 2 + w) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(1 / 2 + w)) *
        (dedekindGammaRemainderComplex w *
          (Complex.sqrt (2 * Real.pi) * Complex.cpow w w *
            Complex.exp (-w))) := by
  have hden : Complex.sqrt (2 * Real.pi) * Complex.cpow w w *
      Complex.exp (-w) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero sqrt_two_mul_pi_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hw)))
      (Complex.exp_ne_zero _)
  have hgamma : Complex.Gamma (1 / 2 + w) =
      dedekindGammaRemainderComplex w *
        (Complex.sqrt (2 * Real.pi) * Complex.cpow w w *
          Complex.exp (-w)) := by
    rw [dedekindGammaRemainderComplex, div_mul_cancel₀ _ hden, add_comm]
  rw [dedekindGammaC_eq, hgamma]

/-- Collected form of `dedekindGammaR_exact` in a principal logarithmic coordinate `w = exp z`.
The first exponential is `2^(3/4) π^(1/4)` and `exp (-z/4)` is the chosen `w^(-1/4)`. -/
theorem dedekindGammaR_exact_collected {z w : ℂ} (hwz : w = Complex.exp z)
    (hz1 : -Real.pi < z.im) (hz2 : z.im ≤ Real.pi) :
    dedekindGammaR (1 / 2 + w) =
      Complex.exp (((3 / 4 * Real.log 2 + 1 / 4 * Real.log Real.pi : ℝ) : ℂ)) *
        Complex.exp (-z / 4) *
        Complex.exp (w / 2 *
          (z - ((Real.log (2 * Real.pi) : ℝ) : ℂ) - 1)) *
        dedekindGammaRemainderReal w := by
  have hw0 : w ≠ 0 := hwz ▸ Complex.exp_ne_zero z
  have hw2 : w / 2 = Complex.exp (z - ((Real.log 2 : ℝ) : ℂ)) := by
    rw [Complex.exp_sub, ← hwz, ← Complex.ofReal_exp, Real.exp_log two_pos]
    push_cast
    ring
  have hlogw2 : Complex.log (w / 2) = z - ((Real.log 2 : ℝ) : ℂ) := by
    rw [hw2, Complex.log_exp (by rwa [Complex.sub_im, Complex.ofReal_im, sub_zero])
      (by rwa [Complex.sub_im, Complex.ofReal_im, sub_zero])]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpipow : (Real.pi : ℂ) ^ (-(1 / 2 + w) / 2) =
      Complex.exp (((Real.log Real.pi : ℝ) : ℂ) * (-(1 / 2 + w) / 2)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpi.ne'),
      Complex.ofReal_log hpi.le]
  have hcw2 : Complex.cpow (w / 2) (w / 2 - 1 / 4) =
      Complex.exp ((z - ((Real.log 2 : ℝ) : ℂ)) * (w / 2 - 1 / 4)) := by
    change (w / 2) ^ (w / 2 - 1 / 4) = _
    rw [Complex.cpow_def_of_ne_zero (div_ne_zero hw0 (by norm_num)), hlogw2]
  rw [dedekindGammaR_exact hw0, hpipow, complex_sqrt_two_pi_eq_exp, hcw2]
  calc
    _ = dedekindGammaRemainderReal w * Complex.exp
        (((Real.log Real.pi : ℝ) : ℂ) * (-(1 / 2 + w) / 2) +
          ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
          (z - ((Real.log 2 : ℝ) : ℂ)) * (w / 2 - 1 / 4) + (-w / 2)) := by
        rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
        ring
    _ = dedekindGammaRemainderReal w * Complex.exp
        ((((3 / 4 * Real.log 2 + 1 / 4 * Real.log Real.pi : ℝ) : ℂ)) +
          (-z / 4) + w / 2 *
            (z - ((Real.log (2 * Real.pi) : ℝ) : ℂ) - 1)) := by
        congr 2
        rw [Real.log_mul two_ne_zero hpi.ne']
        push_cast
        ring
    _ = _ := by
        rw [Complex.exp_add, Complex.exp_add]
        ring

/-- Collected form of `dedekindGammaC_exact` in a principal logarithmic coordinate `w = exp z`. -/
theorem dedekindGammaC_exact_collected {z w : ℂ} (hwz : w = Complex.exp z)
    (hz1 : -Real.pi < z.im) (hz2 : z.im ≤ Real.pi) :
    dedekindGammaC (1 / 2 + w) =
      2 * Complex.exp (w *
        (z - ((Real.log (2 * Real.pi) : ℝ) : ℂ) - 1)) *
        dedekindGammaRemainderComplex w := by
  have hw0 : w ≠ 0 := hwz ▸ Complex.exp_ne_zero z
  have hlogw : Complex.log w = z := by rw [hwz, Complex.log_exp hz1 hz2]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pipow : (2 * (Real.pi : ℂ)) ^ (-(1 / 2 + w)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * (-(1 / 2 + w))) := by
    rw [Complex.cpow_def_of_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hpi.ne')),
      Complex.ofReal_log (by positivity)]
    push_cast
    ring_nf
  have hww : Complex.cpow w w = Complex.exp (z * w) := by
    change w ^ w = _
    rw [Complex.cpow_def_of_ne_zero hw0, hlogw]
  rw [dedekindGammaC_exact hw0, h2pipow, complex_sqrt_two_pi_eq_exp, hww]
  calc
    _ = 2 * dedekindGammaRemainderComplex w * Complex.exp
        (((Real.log (2 * Real.pi) : ℝ) : ℂ) * (-(1 / 2 + w)) +
          ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + z * w + (-w)) := by
        rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
        ring
    _ = 2 * dedekindGammaRemainderComplex w * Complex.exp
        (w * (z - ((Real.log (2 * Real.pi) : ℝ) : ℂ) - 1)) := by
        congr 2
        push_cast
        ring
    _ = _ := by ring

/-- The real part of `dedekindContourW K d q θ` is `T r cos (θ / 2)`, with `T` the scale and `r`
the saddle radius at the saddle angle. -/
theorem dedekindContourW_re (K : Type) [Field K] [NumberField K] (d : ℕ) (q θ : ℝ) :
    (dedekindContourW K d q θ).re =
      dedekindScaleT K d *
        dedekindSaddleRadius K d (dedekindSaddleAngle K d q) *
        Real.cos (θ / 2) := by
  rw [dedekindContourW, Complex.mul_re]
  simp [Complex.exp_re, Complex.exp_im]

/-- The contour variable has constant modulus along its angular circle when
its scale and radius are nonnegative. -/
theorem norm_dedekindContourW (K : Type) [Field K] [NumberField K] {d : ℕ} {q θ : ℝ}
    (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) :
    ‖dedekindContourW K d q θ‖ =
      dedekindScaleT K d *
        dedekindSaddleRadius K d (dedekindSaddleAngle K d q) := by
  rw [dedekindContourW, norm_mul, Complex.norm_real, Complex.norm_exp]
  have he : (Complex.I * (θ : ℂ) / 2).re = 0 := by simp
  rw [he, Real.exp_zero, mul_one,
    Real.norm_of_nonneg (mul_nonneg hT hr)]

/-- There is `W > 0` such that the Dedekind amplitude is nonzero at every contour point `w` with
`|arg w| ≤ 2π / 3`, `W ≤ ‖w‖` and `1 < re (1 / 2 + w)`. -/
theorem exists_dedekindAmplitude_ne_zero_of_large_sector (K : Type) [Field K] [NumberField K] :
    ∃ W : ℝ, 0 < W ∧
      ∀ d : ℕ, ∀ q θ : ℝ,
        |Complex.arg (dedekindContourW K d q θ)| ≤ 2 * Real.pi / 3 →
        W ≤ ‖dedekindContourW K d q θ‖ →
        1 < (1 / 2 + dedekindContourW K d q θ).re →
        dedekindAmplitude K d q θ ≠ 0 := by
  obtain ⟨W, hW, hgamma⟩ := GammaSector.dedekindGammaRemainder_near_one K
  refine ⟨W, hW, fun d q θ harg hnorm hs => ?_⟩
  have hw0 : dedekindContourW K d q θ ≠ 0 :=
    norm_ne_zero_iff.mp (hW.trans_le hnorm).ne'
  have hconst : dedekindLeadingConstant K ≠ 0 := (dedekindLeadingConstant_pos (K := K)).ne'
  have hzeta : analyticDedekindZeta K
      (1 / 2 + dedekindContourW K d q θ) ≠ 0 := by
    rw [← dedekindEulerLog_exp K hs]
    exact Complex.exp_ne_zero _
  exact dedekindAmplitude_ne_zero K hconst hw0 hzeta (hgamma _ harg hnorm).2

end RiemannJensen
