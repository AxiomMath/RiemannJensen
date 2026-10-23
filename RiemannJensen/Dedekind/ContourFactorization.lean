module

public import RiemannJensen.Dedekind.CauchyContourAdapters
public import RiemannJensen.Dedekind.FieldSaddleDefinitions
public import RiemannJensen.Dedekind.ScaleLemmas
public import RiemannJensen.Dedekind.CauchyCanonicalHalves

/-!
# Dedekind contour factorization and the lower-half bridge

On the lower circle `u = r² e^{iθ}`, `-π ≤ θ ≤ 0`, with `w = T r e^{iθ/2}`,
the Dedekind Cauchy integrand factors exactly as
`F_K(T² u) e^{-d q u} u^{-d} = a(θ) e^{d h_q(u)}`, and consequently the lower half of the Cauchy
integral on that circle is the lower saddle contribution.

The completed function `ξ`, the continued zeta function `ζ`, the scale `T`
and the radius `r` are parameters.  The analytic inputs enter as hypotheses:
`ξ` is entire, symmetric under `s ↦ 1 - s` and under conjugation, and equals
the completed product `½ s (s-1) Δ^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ(s)` on
`Re s > 0`, `s ≠ 1`; the scale satisfies the level equation
`N T / (2π) (log (T / a_K) - 1) = d`.
-/

@[expose] public section

namespace RiemannJensen

open Complex MeasureTheory intervalIntegral

section Constants

variable (K : Type) [Field K] [NumberField K]

private theorem dedekindScaleA_pos_cf : 0 < dedekindScaleA K := by
  unfold dedekindScaleA
  exact mul_pos (by positivity)
    (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)

/-- The logarithmic scale `Λ = 2 (log (T / a_K) - 1)` at scale `T`. -/
noncomputable def dedekindLambdaAt (T : ℝ) : ℝ :=
  2 * (Real.log (T / dedekindScaleA K) - 1)

/-- The scaled contour argument `w = T r e^{iθ/2}`. -/
noncomputable def dedekindContourWAt (T r θ : ℝ) : ℂ :=
  ((T * r : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)

/-- The point `r² e^{iθ}` of the saddle circle. -/
noncomputable def dedekindLowerPointAt (r θ : ℝ) : ℂ :=
  ((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))

/-- The contour amplitude `a(θ) = c_K w^{μ_K} ζ(1/2 + w) g_K(w)`. -/
noncomputable def dedekindAmplitudeAt (ζ : ℂ → ℂ) (T r θ : ℝ) : ℂ :=
  (dedekindLeadingConstant K : ℂ) * dedekindContourWAt T r θ ^ (dedekindPowerExponent K : ℂ) *
    ζ (1 / 2 + dedekindContourWAt T r θ) *
    dedekindGammaRemainder K (dedekindContourWAt T r θ)

/-- The lower saddle contribution
`L = d!/dᵈ · (1/2π) ∫_{-π}^0 a(θ) e^{d h_q(r² e^{iθ})} dθ`. -/
noncomputable def dedekindLowerContributionAt (ζ : ℂ → ℂ) (d : ℕ) (T r q : ℝ) : ℂ :=
  ((d.factorial : ℂ) / (d : ℂ) ^ d) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in (-Real.pi)..0, dedekindAmplitudeAt K ζ T r θ *
      Complex.exp ((d : ℂ) *
        saddlePhaseAtLambda (dedekindLambdaAt K T) q (dedekindLowerPointAt r θ)))

end Constants

section SquareRoot

variable {ξ : ℂ → ℂ} (hξ : Differentiable ℂ ξ) (hconj : ∀ s : ℂ, ξ (star s) = star (ξ s))
  (hfe : ∀ s : ℂ, ξ (1 - s) = ξ s)

include hξ hconj hfe

/-- The square-variable series is the centered completed function after
substituting a square: `F(w²) = ξ(1/2 + w)`. -/
theorem dedekindF_sq (w : ℂ) : dedekindF ξ (w ^ 2) = ξ (1 / 2 + w) := by
  have hcent : Differentiable ℂ (centeredDedekindFunction ξ) :=
    hξ.comp ((differentiable_const (1 / 2 : ℂ)).add differentiable_id)
  have hodd : ∀ n : ℕ, iteratedDeriv (2 * n + 1) (centeredDedekindFunction ξ) 0 = 0 := by
    intro n
    have heven : (fun z : ℂ => centeredDedekindFunction ξ (-z)) =
        centeredDedekindFunction ξ := by
      funext z
      simp only [centeredDedekindFunction]
      rw [← hfe]
      ring_nf
    have h := congrFun (congrArg (iteratedDeriv (2 * n + 1)) heven) 0
    rw [iteratedDeriv_comp_neg, neg_zero,
      (Odd.neg_one_pow ⟨n, rfl⟩ : (-1 : ℂ) ^ (2 * n + 1) = -1), neg_one_smul] at h
    linear_combination -h / 2
  let a : ℕ → ℂ := fun n ↦
    (n.factorial : ℂ)⁻¹ • w ^ n • iteratedDeriv n (centeredDedekindFunction ξ) 0
  have ht : HasSum a (centeredDedekindFunction ξ w) := by
    simpa only [a, sub_zero] using Complex.hasSum_taylorSeries_of_entire hcent 0 w
  have hs : Summable a := ht.summable
  have he : Summable (fun k ↦ a (2 * k)) :=
    hs.comp_injective fun _ _ h => Nat.mul_left_cancel two_pos h
  have ho : Summable (fun k ↦ a (2 * k + 1)) :=
    hs.comp_injective fun _ _ h => Nat.mul_left_cancel two_pos (Nat.add_right_cancel h)
  change _ = centeredDedekindFunction ξ w
  unfold dedekindF
  calc
    (∑' j : ℕ, (dedekindGammaCoeff ξ j : ℂ) / (j.factorial : ℂ) * (w ^ 2) ^ j) =
        ∑' j : ℕ, a (2 * j) := by
      refine tsum_congr fun j => ?_
      rw [show a (2 * j) =
        (((2 * j).factorial : ℂ)⁻¹ * iteratedDeriv (2 * j) (centeredDedekindFunction ξ) 0) *
          w ^ (2 * j) by
            simp [a, smul_eq_mul, mul_comm, mul_left_comm]]
      rw [centered_even_taylorCoeff hconj, pow_mul]
    _ = ∑' n : ℕ, a n := by
      rw [← tsum_even_add_odd he ho]
      simp [a, hodd]
    _ = centeredDedekindFunction ξ w := ht.tsum_eq

end SquareRoot

section Factorization

variable (K : Type) [Field K] [NumberField K]

/-- For a positive real base, `x ^ s = exp (log x * s)`. -/
theorem ofReal_cpow_eq_exp_log_mul {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp (((Real.log x : ℝ) : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

/-- The square root of `2π` as an exponential: `√(2π) = exp (log (2π) / 2)`. -/
theorem sqrt_two_mul_pi_eq_exp :
    Complex.sqrt (2 * Real.pi) = Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * 2⁻¹) := by
  rw [Complex.sqrt, Complex.cpow_def_of_ne_zero
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')),
    Complex.ofReal_log (by positivity)]
  push_cast
  ring_nf

/-- The square root of `2π` does not vanish. -/
theorem sqrt_two_mul_pi_ne_zero : Complex.sqrt (2 * Real.pi) ≠ 0 := by
  simp [sqrt_two_mul_pi_eq_exp]

/-- The factor `2 (2π)^s` as a single exponential. -/
theorem two_mul_two_pi_cpow_eq_exp (s : ℂ) :
    2 * (2 * (Real.pi : ℂ)) ^ s =
      Complex.exp (((Real.log 2 : ℝ) : ℂ) + ((Real.log (2 * Real.pi) : ℝ) : ℂ) * s) := by
  have htwo : (2 : ℂ) = Complex.exp ((Real.log 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log two_pos]
    norm_num
  have h2pi : (2 * (Real.pi : ℂ)) ^ s =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * s) := by
    rw [← ofReal_cpow_eq_exp_log_mul (by positivity)]
    push_cast
    ring_nf
  rw [Complex.exp_add, ← htwo, h2pi]

/-- The leading constant `c_K` is positive. -/
theorem dedekindLeadingConstant_pos : 0 < dedekindLeadingConstant K := by
  unfold dedekindLeadingConstant
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos Real.pi_pos _))
    (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)

/-- The logarithm of the leading constant `c_K`. -/
theorem log_dedekindLeadingConstant : Real.log (dedekindLeadingConstant K) =
    (3 * (dedekindRealPlaces K : ℝ) / 4 + (dedekindComplexPlaces K : ℝ) - 1) * Real.log 2 +
      (dedekindRealPlaces K : ℝ) / 4 * Real.log Real.pi +
      1 / 4 * Real.log (dedekindDiscriminantAbs K) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hΔ : 0 < dedekindDiscriminantAbs K := dedekindDiscriminantAbs_pos K
  unfold dedekindLeadingConstant
  change Real.log
      ((2 : ℝ) ^ (3 * (dedekindRealPlaces K : ℝ) / 4 + (dedekindComplexPlaces K : ℝ) - 1) *
        Real.pi ^ ((dedekindRealPlaces K : ℝ) / 4) *
        dedekindDiscriminantAbs K ^ (1 / 4 : ℝ)) = _
  rw [Real.log_mul
        (mul_ne_zero (Real.rpow_pos_of_pos two_pos _).ne' (Real.rpow_pos_of_pos hpi _).ne')
        (Real.rpow_pos_of_pos hΔ _).ne',
    Real.log_mul (Real.rpow_pos_of_pos two_pos _).ne' (Real.rpow_pos_of_pos hpi _).ne',
    Real.log_rpow two_pos, Real.log_rpow hpi, Real.log_rpow hΔ]

/-- The logarithm of the gamma scale `a_K = 2π |Δ_K|^{-1/N}`. -/
theorem log_dedekindScaleA : Real.log (dedekindScaleA K) =
    Real.log 2 + Real.log Real.pi +
      -(1 / (dedekindDegree K : ℝ)) * Real.log (dedekindDiscriminantAbs K) := by
  have hΔ : 0 < dedekindDiscriminantAbs K := dedekindDiscriminantAbs_pos K
  unfold dedekindScaleA
  change Real.log (2 * Real.pi * dedekindDiscriminantAbs K ^ (-(1 / (dedekindDegree K : ℝ)))) = _
  rw [Real.log_mul (mul_ne_zero two_ne_zero Real.pi_pos.ne') (Real.rpow_pos_of_pos hΔ _).ne',
    Real.log_mul two_ne_zero Real.pi_pos.ne', Real.log_rpow hΔ]

/-- The Gamma-power main factor of the completed product at `w = e^z`, written
as `c_K w^{μ_K}` times the Stirling exponential `exp ((N/2) w (z - log a_K - 1))`. -/
theorem dedekind_main_factor_eq {z w : ℂ} (hwz : w = Complex.exp z)
    (hz1 : -Real.pi < z.im) (hz2 : z.im ≤ Real.pi)
    (hz21 : -Real.pi < (z - ((Real.log 2 : ℝ) : ℂ)).im)
    (hz22 : (z - ((Real.log 2 : ℝ) : ℂ)).im ≤ Real.pi) :
    (w ^ 2 / 2) * (dedekindDiscriminantAbs K : ℂ) ^ ((1 / 2 + w) / 2) *
        ((Real.pi : ℂ) ^ (-(1 / 2 + w) / 2) *
          (Complex.sqrt (2 * Real.pi) * Complex.cpow (w / 2) (w / 2 - 1 / 4) *
            Complex.exp (-w / 2))) ^ dedekindRealPlaces K *
        (2 * (2 * (Real.pi : ℂ)) ^ (-(1 / 2 + w)) *
          (Complex.sqrt (2 * Real.pi) * Complex.cpow w w * Complex.exp (-w))) ^
          dedekindComplexPlaces K =
      (dedekindLeadingConstant K : ℂ) * w ^ (dedekindPowerExponent K : ℂ) *
        Complex.exp (((dedekindDegree K : ℝ) : ℂ) / 2 * w *
          (z - ((Real.log (dedekindScaleA K) : ℝ) : ℂ) - 1)) := by
  have hsig : (dedekindDegree K : ℂ) =
      (dedekindRealPlaces K : ℂ) + 2 * (dedekindComplexPlaces K : ℂ) := by
    rw [← dedekind_signature K]
    push_cast
    ring
  have hw0 : w ≠ 0 := hwz ▸ Complex.exp_ne_zero z
  have hlogw : Complex.log w = z := by rw [hwz, Complex.log_exp hz1 hz2]
  have hw2 : w / 2 = Complex.exp (z - ((Real.log 2 : ℝ) : ℂ)) := by
    rw [Complex.exp_sub, ← hwz, ← Complex.ofReal_exp, Real.exp_log two_pos]
    push_cast
    ring
  have hcw2 : Complex.cpow (w / 2) (w / 2 - 1 / 4) =
      Complex.exp ((z - ((Real.log 2 : ℝ) : ℂ)) * (w / 2 - 1 / 4)) := by
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero (div_ne_zero hw0 two_ne_zero), hw2,
      Complex.log_exp hz21 hz22]
  have hww : Complex.cpow w w = Complex.exp (z * w) := by
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hw0, hlogw]
  have hwmu : w ^ (dedekindPowerExponent K : ℂ) =
      Complex.exp (z * (dedekindPowerExponent K : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hw0, hlogw]
  have hsq : w ^ 2 / 2 = Complex.exp (2 * z - ((Real.log 2 : ℝ) : ℂ)) := by
    rw [Complex.exp_sub, hwz, ← Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log two_pos]
    push_cast
    ring_nf
  have hc : (dedekindLeadingConstant K : ℂ) =
      Complex.exp ((Real.log (dedekindLeadingConstant K) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (dedekindLeadingConstant_pos K)]
  rw [hsq, ofReal_cpow_eq_exp_log_mul (dedekindDiscriminantAbs_pos K),
    ofReal_cpow_eq_exp_log_mul Real.pi_pos, sqrt_two_mul_pi_eq_exp, hcw2,
    two_mul_two_pi_cpow_eq_exp, hww, hwmu, hc]
  simp only [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  rw [log_dedekindLeadingConstant, log_dedekindScaleA, Real.log_mul two_ne_zero Real.pi_pos.ne',
    dedekindPowerExponent]
  have hN0 : (dedekindDegree K : ℂ) ≠ 0 := by exact_mod_cast (dedekindDegree_pos K).ne'
  push_cast
  field_simp
  rw [hsig]
  ring

/-- The real Gamma factor at `(1/2 + w)/2` splits off the Stirling remainder `g_ℝ(w)`. -/
theorem Gamma_half_eq_dedekindGammaRemainderReal {w : ℂ} (hw : w ≠ 0) :
    Complex.Gamma ((1 / 2 + w) / 2) = dedekindGammaRemainderReal w *
      (Complex.sqrt (2 * Real.pi) * Complex.cpow (w / 2) (w / 2 - 1 / 4) *
        Complex.exp (-w / 2)) := by
  have hD : Complex.sqrt (2 * Real.pi) * Complex.cpow (w / 2) (w / 2 - 1 / 4) *
      Complex.exp (-w / 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero sqrt_two_mul_pi_ne_zero ?_) (Complex.exp_ne_zero _)
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero (div_ne_zero hw two_ne_zero)]
    exact Complex.exp_ne_zero _
  rw [dedekindGammaRemainderReal, div_mul_cancel₀ _ hD]
  congr 1
  ring

/-- The complex Gamma factor at `1/2 + w` splits off the Stirling remainder `g_ℂ(w)`. -/
theorem Gamma_eq_dedekindGammaRemainderComplex {w : ℂ} (hw : w ≠ 0) :
    Complex.Gamma (1 / 2 + w) = dedekindGammaRemainderComplex w *
      (Complex.sqrt (2 * Real.pi) * Complex.cpow w w * Complex.exp (-w)) := by
  have hD : Complex.sqrt (2 * Real.pi) * Complex.cpow w w * Complex.exp (-w) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero sqrt_two_mul_pi_ne_zero ?_) (Complex.exp_ne_zero _)
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hw]
    exact Complex.exp_ne_zero _
  rw [dedekindGammaRemainderComplex, div_mul_cancel₀ _ hD, add_comm]

variable {ξ ζ : ℂ → ℂ}

/-- The completed product at `1/2 + w`, `w = e^z`, is the contour amplitude times the Stirling
exponential `exp ((N/2) w (z - log a_K - 1))`. -/
theorem dedekind_completed_product_eq {z w : ℂ} (hwz : w = Complex.exp z)
    (hz1 : -Real.pi < z.im) (hz2 : z.im ≤ Real.pi)
    (hz21 : -Real.pi < (z - ((Real.log 2 : ℝ) : ℂ)).im)
    (hz22 : (z - ((Real.log 2 : ℝ) : ℂ)).im ≤ Real.pi) :
    (1 / 2 + w) * (1 / 2 + w - 1) / 2 * (dedekindDiscriminantAbs K : ℂ) ^ ((1 / 2 + w) / 2) *
        dedekindGammaR (1 / 2 + w) ^ dedekindRealPlaces K *
        dedekindGammaC (1 / 2 + w) ^ dedekindComplexPlaces K * ζ (1 / 2 + w) =
      (dedekindLeadingConstant K : ℂ) * w ^ (dedekindPowerExponent K : ℂ) * ζ (1 / 2 + w) *
        dedekindGammaRemainder K w *
        Complex.exp (((dedekindDegree K : ℝ) : ℂ) / 2 * w *
          (z - ((Real.log (dedekindScaleA K) : ℝ) : ℂ) - 1)) := by
  have hw0 : w ≠ 0 := hwz ▸ Complex.exp_ne_zero z
  have hss : (1 / 2 + w) * ((1 / 2 + w) - 1) / 2 = (w ^ 2 / 2) * (1 - 1 / (4 * w ^ 2)) := by
    field_simp
    ring
  rw [dedekindGammaR_eq, dedekindGammaC_eq, Gamma_half_eq_dedekindGammaRemainderReal hw0,
    Gamma_eq_dedekindGammaRemainderComplex hw0, hss, dedekindGammaRemainder]
  linear_combination ((1 - 1 / (4 * w ^ 2)) * dedekindGammaRemainderReal w ^ dedekindRealPlaces K *
      dedekindGammaRemainderComplex w ^ dedekindComplexPlaces K * ζ (1 / 2 + w)) *
    dedekind_main_factor_eq K hwz hz1 hz2 hz21 hz22

/-- On the closed lower half-circle with `T r > 1`, the shifted point `1/2 + w` lies in
`Re s > 0` and differs from `1`. -/
theorem dedekindContourWAt_half_add {T r θ : ℝ} (hT : 0 < T) (hr : 0 < r) (hR : 1 < T * r)
    (hθ1 : -Real.pi ≤ θ) (hθ2 : θ ≤ 0) :
    0 < (1 / 2 + dedekindContourWAt T r θ).re ∧ 1 / 2 + dedekindContourWAt T r θ ≠ 1 := by
  have heI : Complex.exp (Complex.I * (θ : ℂ) / 2) =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hnw : ‖dedekindContourWAt T r θ‖ = T * r := by
    rw [dedekindContourWAt, norm_mul, Complex.norm_real, heI, Complex.norm_exp_ofReal_mul_I,
      mul_one, Real.norm_of_nonneg (by positivity)]
  refine ⟨?_, fun h => ?_⟩
  · rw [Complex.add_re, dedekindContourWAt, Complex.re_ofReal_mul, heI,
      Complex.exp_ofReal_mul_I_re]
    norm_num
    positivity
  · rw [show dedekindContourWAt T r θ = 1 / 2 by linear_combination h] at hnw
    norm_num at hnw
    linarith

/-- The `d`-th power of the lower circle point `r² e^{iθ}` as an exponential. -/
theorem dedekindLowerPointAt_pow {r : ℝ} (hr : 0 < r) (θ : ℝ) (d : ℕ) :
    dedekindLowerPointAt r θ ^ d =
      Complex.exp ((d : ℂ) * (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ))) := by
  rw [Complex.exp_nat_mul, Complex.exp_add, ← Complex.ofReal_exp, dedekindLowerPointAt,
    show 2 * Real.log r = Real.log (r ^ 2) by norm_num [Real.log_pow],
    Real.exp_log (by positivity)]

/-- On the level `N T / (2π) (log (T / a_K) - 1) = d`, the Stirling exponent at
`w = T r e^{iθ/2}` is `d` times the square-root part of the saddle phase. -/
theorem dedekind_level_exponent_eq (d : ℕ) (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T)
    (hlevel : (dedekindDegree K : ℝ) * T / (2 * Real.pi) *
      (Real.log (T / dedekindScaleA K) - 1) = d) (r θ : ℝ) :
    ((dedekindDegree K : ℝ) : ℂ) / 2 * dedekindContourWAt T r θ *
        (((Real.log T + Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ) / 2 -
          ((Real.log (dedekindScaleA K) : ℝ) : ℂ) - 1) =
      (d : ℂ) * ((2 * saddleKappa : ℝ) * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)) +
        ((2 * saddleKappa / dedekindLambdaAt K T : ℝ) : ℂ) *
          ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2)) *
          (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ))) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  set Λ := dedekindLambdaAt K T with hΛ_def
  have hΛ0 : Λ ≠ 0 := by
    intro h0
    have : Real.log (T / dedekindScaleA K) - 1 = 0 := by
      rw [hΛ_def, dedekindLambdaAt] at h0
      linarith
    rw [this, mul_zero] at hlevel
    exact hd0 hlevel.symm
  have hlev : (d : ℝ) = (dedekindDegree K : ℝ) * T * Λ / (4 * Real.pi) := by
    rw [← hlevel, hΛ_def, dedekindLambdaAt]
    field_simp
    ring
  have hlogT : ((Real.log T : ℝ) : ℂ) =
      (Λ : ℂ) / 2 + 1 + ((Real.log (dedekindScaleA K) : ℝ) : ℂ) := by
    have h : Λ = 2 * (Real.log T - Real.log (dedekindScaleA K) - 1) := by
      rw [hΛ_def, dedekindLambdaAt, Real.log_div hT.ne' (dedekindScaleA_pos_cf K).ne']
    rw [h]
    push_cast
    ring
  have hΛ0c : (Λ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΛ0
  have hdc : (d : ℂ) = ((dedekindDegree K : ℝ) : ℂ) * T * Λ / (4 * Real.pi) := by
    exact_mod_cast hlev
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [hdc, dedekindContourWAt, saddleKappa_eq]
  push_cast
  rw [hlogT]
  field_simp
  ring

/-- **Exact contour factorization**. On the closed lower circle `u = r² e^{iθ}`, `-π ≤ θ ≤ 0`,
with `T r > 1` and `T` on the level `N T / (2π) (log (T / a_K) - 1) = d`,
`F_K(T² u) e^{-d q u} / uᵈ = a(θ) e^{d h_q(u)}`. -/
theorem dedekindCauchyNumerator_lower_factorization
    (hξ : Differentiable ℂ ξ) (hconj : ∀ s : ℂ, ξ (star s) = star (ξ s))
    (hfe : ∀ s : ℂ, ξ (1 - s) = ξ s)
    (hprod : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      ξ s = s * (s - 1) / 2 * (dedekindDiscriminantAbs K : ℂ) ^ (s / 2) *
        dedekindGammaR s ^ dedekindRealPlaces K *
        dedekindGammaC s ^ dedekindComplexPlaces K * ζ s)
    (d : ℕ) (hd : 1 ≤ d) {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (hR : 1 < T * r)
    (hlevel : (dedekindDegree K : ℝ) * T / (2 * Real.pi) *
      (Real.log (T / dedekindScaleA K) - 1) = d)
    (q : ℝ) {θ : ℝ} (hθ1 : -Real.pi ≤ θ) (hθ2 : θ ≤ 0) :
    dedekindCauchyNumerator ξ d T (-q) (dedekindLowerPointAt r θ) /
        (dedekindLowerPointAt r θ) ^ d =
      dedekindAmplitudeAt K ζ T r θ *
        Complex.exp ((d : ℂ) *
          saddlePhaseAtLambda (dedekindLambdaAt K T) q (dedekindLowerPointAt r θ)) := by
  obtain ⟨hs, hs1⟩ := dedekindContourWAt_half_add hT hr hR hθ1 hθ2
  set u := dedekindLowerPointAt r θ with hu_def
  set w := dedekindContourWAt T r θ with hw_def
  have hw : w = ((T * r : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) := rfl
  have hu : u = ((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := rfl
  have he : Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ) / 2) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hTu : ((T ^ 2 : ℝ) : ℂ) * u = w ^ 2 := by
    rw [hu, hw, he]
    push_cast
    ring
  set z : ℂ := ((Real.log T + Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ) / 2 with hz
  have hzim : z.im = θ / 2 := by simp [z]
  have hzim₂ : (z - ((Real.log 2 : ℝ) : ℂ)).im = θ / 2 := by
    rw [Complex.sub_im, hzim, Complex.ofReal_im, sub_zero]
  have hwz : w = Complex.exp z := by
    rw [hw, hz, Complex.exp_add, ← Complex.ofReal_exp, ← Real.log_mul hT.ne' hr.ne',
      Real.exp_log (mul_pos hT hr)]
  have hsqu : lowerSqrt u = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ) / 2) :=
    lowerSqrt_sq_mul_exp_I_mul hr hθ1 hθ2
  have hlogu : lowerLog u = ((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ) :=
    lowerLog_sq_mul_exp_I_mul hr hθ1 hθ2
  have hud : u ^ d =
      Complex.exp ((d : ℂ) * (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ))) :=
    dedekindLowerPointAt_pow hr θ d
  have hscale : ((dedekindDegree K : ℝ) : ℂ) / 2 * w *
      (z - ((Real.log (dedekindScaleA K) : ℝ) : ℂ) - 1) =
      (d : ℂ) * ((2 * saddleKappa : ℝ) * lowerSqrt u +
        ((2 * saddleKappa / dedekindLambdaAt K T : ℝ) : ℂ) * lowerSqrt u * lowerLog u) := by
    rw [hsqu, hlogu]
    exact dedekind_level_exponent_eq K d hd hT hlevel r θ
  have hph : (d : ℂ) * saddlePhaseAtLambda (dedekindLambdaAt K T) q u =
      (((d : ℝ) * -q : ℝ) : ℂ) * u +
        (d : ℂ) * ((2 * saddleKappa : ℝ) * lowerSqrt u +
          ((2 * saddleKappa / dedekindLambdaAt K T : ℝ) : ℂ) * lowerSqrt u * lowerLog u) -
        (d : ℂ) * lowerLog u := by
    rw [saddlePhaseAtLambda]
    push_cast
    ring
  rw [dedekindCauchyNumerator, hTu, dedekindF_sq hξ hconj hfe, hprod _ hs hs1,
    dedekind_completed_product_eq K hwz (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
    hscale, dedekindAmplitudeAt, ← hw_def, hph, Complex.exp_sub, Complex.exp_add, hud, hlogu]
  have hE : Complex.exp ((d : ℂ) * (((2 * Real.log r : ℝ) : ℂ) + Complex.I * (θ : ℂ))) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

/-- On the circle `ρ = r²` with `T r > 1`, the lower half of the Cauchy integral at `x = -q` is
the lower saddle contribution. -/
theorem dedekindCauchyHalf_lower_eq_lowerContribution
    (hξ : Differentiable ℂ ξ) (hconj : ∀ s : ℂ, ξ (star s) = star (ξ s))
    (hfe : ∀ s : ℂ, ξ (1 - s) = ξ s)
    (hprod : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      ξ s = s * (s - 1) / 2 * (dedekindDiscriminantAbs K : ℂ) ^ (s / 2) *
        dedekindGammaR s ^ dedekindRealPlaces K *
        dedekindGammaC s ^ dedekindComplexPlaces K * ζ s)
    (d : ℕ) (hd : 1 ≤ d) {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (hR : 1 < T * r)
    (hlevel : (dedekindDegree K : ℝ) * T / (2 * Real.pi) *
      (Real.log (T / dedekindScaleA K) - 1) = d) (q : ℝ) :
    dedekindCauchyHalf ξ d T (-q) (r ^ 2) (-Real.pi) 0 =
      dedekindLowerContributionAt K ζ d T r q := by
  have hpt (θ : ℝ) : circleMap 0 (r ^ 2) θ = dedekindLowerPointAt r θ := by
    simp only [circleMap, dedekindLowerPointAt, zero_add]
    push_cast
    ring_nf
  have hcongr : Set.EqOn
      (fun θ : ℝ => deriv (circleMap 0 (r ^ 2)) θ •
        (dedekindCauchyNumerator ξ d T (-q) (circleMap 0 (r ^ 2) θ) /
          (circleMap 0 (r ^ 2) θ) ^ (d + 1)))
      (fun θ : ℝ => Complex.I * (dedekindAmplitudeAt K ζ T r θ *
        Complex.exp ((d : ℂ) *
          saddlePhaseAtLambda (dedekindLambdaAt K T) q (dedekindLowerPointAt r θ))))
      (Set.uIcc (-Real.pi) 0) := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    have hne : dedekindLowerPointAt r θ ≠ 0 :=
      hpt θ ▸ circleMap_ne_center (by positivity)
    simp only [deriv_circleMap, smul_eq_mul, hpt]
    rw [← dedekindCauchyNumerator_lower_factorization K hξ hconj hfe hprod d hd hT hr hR
      hlevel q hθ.1 hθ.2]
    field_simp
    ring
  unfold dedekindCauchyHalf dedekindLowerContributionAt
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdd : (d : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  field_simp

end Factorization

section Canonical

variable (K : Type) [Field K] [NumberField K]

/-- The point on the canonical lower saddle circle at angle `θ`. -/
noncomputable def dedekindLowerContourPoint (d : ℕ) (q θ : ℝ) : ℂ :=
  ((dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^ 2 : ℝ) *
    Complex.exp (Complex.I * (θ : ℂ))

/-- The canonical lower saddle contribution of the Dedekind contour. -/
noncomputable def dedekindLowerContribution (d : ℕ) (q : ℝ) : ℂ :=
  ((d.factorial : ℂ) / (d : ℂ) ^ d) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in (-Real.pi)..0, dedekindAmplitude K d q θ *
      Complex.exp ((d : ℂ) *
        dedekindSaddlePhase K d q (dedekindLowerContourPoint K d q θ)))

/-- On the lower saddle contour of the canonical Dedekind data, the Cauchy numerator divided by
`uᵈ` equals the amplitude times `exp (d h_q(u))`. -/
theorem dedekind_contour_factorization
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hR : 1 < dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    {θ : ℝ} (hθ1 : -Real.pi ≤ θ) (hθ2 : θ ≤ 0) :
    dedekindCauchyNumerator (entireDedekindXi K) d (dedekindScaleT K d) (-q)
          (dedekindLowerContourPoint K d q θ) /
        (dedekindLowerContourPoint K d q θ) ^ d =
      dedekindAmplitude K d q θ *
        Complex.exp ((d : ℂ) *
          dedekindSaddlePhase K d q
            (dedekindLowerContourPoint K d q θ)) :=
  dedekindCauchyNumerator_lower_factorization K (entireDedekindXi_entire K)
    (entireDedekindXi_conj K)
    (entireDedekindXi_functional K) (entireDedekindXi_eq_product_of_pos_re K) d hd
    (dedekindScaleT_pos K d hd) hr hR (dedekindScaleT_level K d hd) q hθ1 hθ2

/-- The Cauchy half-integral over `θ ∈ [-π, 0]` on the canonical saddle circle, at `x = -q`,
equals the lower saddle contribution. -/
theorem dedekind_lower_half_bridge
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hR : 1 < dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) :
    dedekindCauchyHalfK K d (-q) (dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2)
        (-Real.pi) 0 =
      dedekindLowerContribution K d q :=
  dedekindCauchyHalf_lower_eq_lowerContribution K (entireDedekindXi_entire K)
    (entireDedekindXi_conj K)
    (entireDedekindXi_functional K) (entireDedekindXi_eq_product_of_pos_re K) d hd
    (dedekindScaleT_pos K d hd) hr hR (dedekindScaleT_level K d hd) q

/-- The upper half of the canonical Cauchy integral is the conjugate of the lower saddle
contribution. -/
theorem dedekind_conjugate_contributions
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hR : 1 < dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) :
    dedekindCauchyHalfK K d (-q) (dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2)
        0 Real.pi =
      star (dedekindLowerContribution K d q) := by
  rw [dedekindCauchyHalfK_upper_eq_star_lower K,
    dedekind_lower_half_bridge K d hd q hr hR]

/-- The rescaled Jensen polynomial evaluated at `-q` is twice the real part of the lower saddle
contribution. -/
theorem dedekind_cauchy_two_re_lowerContribution
    (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hR : 1 < dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) :
    (↑((rescaledDedekindJensenK K d).eval (-q)) : ℂ) =
      2 * (dedekindLowerContribution K d q).re := by
  rw [dedekind_cauchy_two_re K d hd (-q)
      (dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2)
      (sq_pos_of_pos hr),
    dedekind_lower_half_bridge K d hd q hr hR]

end Canonical

end RiemannJensen
