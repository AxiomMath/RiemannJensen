module

public import RiemannJensen.Dedekind.FieldSaddleDefinitions
public import RiemannJensen.Analysis.GammaRemainderBounds

/-!
# Dedekind archimedean remainder in the right half-plane

The real-place Stirling quotient `dedekindGammaRemainderReal` coincides with
`GammaCore.gammaCoreRemainder`, so it satisfies an explicit `O(1/|w|)` estimate. The real-place,
complex-place and mixed archimedean remainders are nonzero in the closed right half-plane, and so
is the Dedekind contour amplitude under nonvanishing of its factors.

## Main definitions

* `normalizedDedekindLocalAmplitude`: The Dedekind amplitude at a point of the local window,
  divided by its value at the saddle.

## Main results

* `dedekindGammaRemainderReal_eq_gammaCore`: `dedekindGammaRemainderReal` equals
  `GammaCore.gammaCoreRemainder`.
* `norm_dedekindGammaRemainderReal_sub_one_le`: `‖dedekindGammaRemainderReal w - 1‖ ≤ 64 / ‖w‖`
  for `0 ≤ re w` and `4 ≤ ‖w‖`.
* `dedekindGammaRemainder_ne_zero_of_re_nonneg`: The mixed archimedean remainder is nonzero for
  `0 ≤ re w` and `4 ≤ ‖w‖`.
* `dedekindAmplitude_ne_zero`: The Dedekind contour amplitude is nonzero when its factors are.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set
open scoped ComplexOrder

noncomputable section

variable (K : Type) [Field K] [NumberField K]


private theorem complex_sqrt_two_pi_eq_real :
    Complex.sqrt ((2 * Real.pi : ℝ) : ℂ) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
  have hnonneg : 0 ≤ (((2 * Real.pi : ℝ) : ℂ)) :=
    RCLike.nonneg_iff_exists_ofReal.mpr
      ⟨2 * Real.pi, by positivity, rfl⟩
  rw [Complex.sqrt_of_nonneg hnonneg]
  norm_num

/-- The real-place Stirling quotient `dedekindGammaRemainderReal` equals
`GammaCore.gammaCoreRemainder`. -/
theorem dedekindGammaRemainderReal_eq_gammaCore (w : ℂ) :
    dedekindGammaRemainderReal w = GammaCore.gammaCoreRemainder w := by
  unfold dedekindGammaRemainderReal GammaCore.gammaCoreRemainder
  rw [show (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
    complex_sqrt_two_pi_eq_real]
  have hcpow : Complex.cpow (w / 2) (w / 2 - 1 / 4) =
      (w / 2) ^ (w / 2 - 1 / 4) := rfl
  rw [hcpow]

/-- Explicit `O(1/|w|)` estimate for the shifted real-place quotient. -/
theorem norm_dedekindGammaRemainderReal_sub_one_le
    {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    ‖dedekindGammaRemainderReal w - 1‖ ≤ 64 / ‖w‖ := by
  rw [dedekindGammaRemainderReal_eq_gammaCore]
  exact GammaCore.norm_gammaCoreRemainder_sub_one_le hw hw4

/-- The shifted real-place quotient is nonzero on `GammaCore.grDomain`. -/
theorem dedekindGammaRemainderReal_ne_zero
    {w : ℂ} (hw : w ∈ GammaCore.grDomain) :
    dedekindGammaRemainderReal w ≠ 0 := by
  rw [dedekindGammaRemainderReal_eq_gammaCore]
  exact GammaCore.gammaCoreRemainder_ne_zero hw

/-- The shifted real-place quotient is nonzero in the closed right half-plane when `|w| ≥ 4`. -/
theorem dedekindGammaRemainderReal_ne_zero_of_re_nonneg
    {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    dedekindGammaRemainderReal w ≠ 0 :=
  dedekindGammaRemainderReal_ne_zero
    (GammaCore.subset_grDomain hw hw4)

/-- The shifted complex-place quotient is nonzero in the closed right
half-plane away from the origin. -/
theorem dedekindGammaRemainderComplex_ne_zero
    {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) :
    dedekindGammaRemainderComplex w ≠ 0 := by
  unfold dedekindGammaRemainderComplex
  apply div_ne_zero
  · apply Complex.Gamma_ne_zero_of_re_pos
    norm_num [div_re]
    linarith
  · apply mul_ne_zero
    · have hsqrt : Complex.sqrt (2 * (Real.pi : ℂ)) ≠ 0 := by
        rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
          complex_sqrt_two_pi_eq_real]
        exact ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
      exact mul_ne_zero hsqrt
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hw0))
    · exact Complex.exp_ne_zero _

/-- The full mixed archimedean remainder is nonzero throughout the closed
right half-plane when `|w| ≥ 4`. -/
theorem dedekindGammaRemainder_ne_zero_of_re_nonneg
    {w : ℂ} (hw : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) :
    dedekindGammaRemainder K w ≠ 0 := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖w‖ ≠ 0)
  unfold dedekindGammaRemainder
  exact mul_ne_zero
    (mul_ne_zero
      (gammaPolarCorrection_ne_zero (by linarith))
      (pow_ne_zero _ (dedekindGammaRemainderReal_ne_zero_of_re_nonneg hw hw4)))
    (pow_ne_zero _ (dedekindGammaRemainderComplex_ne_zero hw hw0))

/-- The Dedekind contour amplitude is nonzero when the leading constant, the contour point, the
Dedekind zeta value and the archimedean remainder are all nonzero. -/
theorem dedekindAmplitude_ne_zero
    {d : ℕ} {q θ : ℝ}
    (hconst : dedekindLeadingConstant K ≠ 0)
    (hw : dedekindContourW K d q θ ≠ 0)
    (hzeta : analyticDedekindZeta K
      (1 / 2 + dedekindContourW K d q θ) ≠ 0)
    (hgamma : dedekindGammaRemainder K
      (dedekindContourW K d q θ) ≠ 0) :
    dedekindAmplitude K d q θ ≠ 0 := by
  unfold dedekindAmplitude
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (ofReal_ne_zero.mpr hconst)
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hw)))
      hzeta)
    hgamma

/-- The Dedekind amplitude at angle `-2 θ₀ + δ y`, divided by its value at `-2 θ₀`, where `θ₀` is
`dedekindSaddleAngle` and `δ` is `dedekindLocalWidth`. -/
noncomputable def normalizedDedekindLocalAmplitude
    (d : ℕ) (q y : ℝ) : ℂ :=
  dedekindAmplitude K d q
      (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y) /
    dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q)

/-- The normalized local amplitude equals one at the saddle whenever the
saddle amplitude is nonzero. -/
theorem normalizedDedekindLocalAmplitude_zero
    {d : ℕ} {q : ℝ}
    (hamp : dedekindAmplitude K d q
      (-2 * dedekindSaddleAngle K d q) ≠ 0) :
    normalizedDedekindLocalAmplitude K d q 0 = 1 := by
  unfold normalizedDedekindLocalAmplitude
  norm_num
  simpa only [neg_mul] using hamp

end

end RiemannJensen
