module

public import RiemannJensen.Analysis.AmplitudeLocal
public import RiemannJensen.Analysis.ZetaEulerBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact Stirling factorization and global amplitude bounds

We prove the exact complex Stirling factorization of `ξ(1/2 + w)`, two-sided
bounds for the amplitude at points with `re (1/2 + w) ≥ 4`, a bound for the
amplitude on the whole saddle circle, the resulting amplitude ratio, and the
real-part bound on the local arc.
-/

@[expose] public section

namespace RiemannJensen

/-! ### Exact Stirling factorization -/

/-- The Gamma main factor of `centeredXi` in closed form, for every `w ≠ 0`. -/
theorem xi_main_factor_eq_of_ne_zero {w : ℂ} (hw0 : w ≠ 0) :
    (w ^ 2 / 2) * Complex.cpow Real.pi (-(1 / 2 + w) / 2) * gammaMainDenominator w =
      Complex.cpow (Real.pi / 2) (1 / 4) * Complex.cpow w (7 / 4) *
        Complex.exp ((w / 2) * (Complex.log (w / (2 * Real.pi)) - 1)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  set L : ℂ := Complex.log w
  have hwL : w = Complex.exp L := (Complex.exp_log hw0).symm
  have hlogdiv : ∀ c : ℝ, 0 < c → Complex.log (w / c) = L - ((Real.log c : ℝ) : ℂ) := by
    intro c hc
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.log_mul_ofReal _ (inv_pos.2 hc) _ hw0,
      Real.log_inv]
    push_cast
    ring
  have hlog2 : Complex.log (w / 2) = L - ((Real.log 2 : ℝ) : ℂ) := by
    simpa using hlogdiv 2 two_pos
  have hlog2pi : Complex.log (w / (2 * Real.pi)) = L - ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
    simpa using hlogdiv (2 * Real.pi) (by positivity)
  have hsq : w ^ 2 = Complex.exp (2 * L) := by
    rw [hwL, ← Complex.exp_nat_mul]
    norm_num
  have hhalf : (2 : ℂ)⁻¹ = Complex.exp (-((Real.log 2 : ℝ) : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log two_pos]
    push_cast
    ring
  have hcpi : ∀ s : ℂ, Complex.cpow Real.pi s =
      Complex.exp (((Real.log Real.pi : ℝ) : ℂ) * s) := by
    intro s
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hpi0, Complex.ofReal_log hpi.le]
  have hcpi2 : Complex.cpow (Real.pi / 2) (1 / 4) =
      Complex.exp (((Real.log (Real.pi / 2) : ℝ) : ℂ) * (1 / 4)) := by
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero (div_ne_zero hpi0 two_ne_zero),
      Complex.ofReal_log (by positivity)]
    push_cast
    ring_nf
  have hcw : Complex.cpow w (7 / 4) = Complex.exp (L * (7 / 4)) := by
    rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hw0]
  have hsqrt : Complex.sqrt (2 * Real.pi) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * 2⁻¹) := by
    rw [Complex.sqrt, Complex.cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hpi0),
      Complex.ofReal_log (by positivity)]
    push_cast
    ring_nf
  have hcw2 : (w / 2) ^ (w / 2 - 1 / 4) =
      Complex.exp ((L - ((Real.log 2 : ℝ) : ℂ)) * (w / 2 - 1 / 4)) := by
    rw [Complex.cpow_def_of_ne_zero (div_ne_zero hw0 two_ne_zero), hlog2]
  unfold gammaMainDenominator
  rw [div_eq_mul_inv (w ^ 2), hsq, hhalf, hcpi, hcpi2, hcw, hsqrt, Complex.cpow_eq_pow,
    hcw2, hlog2pi]
  simp only [← Complex.exp_add]
  congr 1
  rw [Real.log_mul two_ne_zero hpi.ne', Real.log_div hpi.ne' two_ne_zero]
  push_cast
  ring

/-- **Exact complex Stirling factorization**: for `w ≠ 0`, `re (1/2 + w) > 0` and `w ≠ 1/2`,
`ξ(1/2+w) = (π/2)^{1/4} w^{7/4} e^{(w/2)(Log(w/2π) - 1)} ζ(1/2+w) g(w)`. -/
theorem centeredXi_eq_stirling_of_ne_zero {w : ℂ} (hw0 : w ≠ 0)
    (hs : 0 < (1 / 2 + w).re) (hw1 : w ≠ 1 / 2) :
    centeredXi w =
      Complex.cpow (Real.pi / 2) (1 / 4) * Complex.cpow w (7 / 4) *
        Complex.exp ((w / 2) * (Complex.log (w / (2 * Real.pi)) - 1)) *
        riemannZeta (1 / 2 + w) * gammaRemainder w := by
  rw [centeredXi_eq_gammaRemainder hw0 hs fun h => hw1 (by linear_combination h),
    xi_main_factor_eq_of_ne_zero hw0]

/-- **Exact complex Stirling factorization** in the right half-plane
(`re w > 0`, `w ≠ 1/2`; the excluded point is the pole of zeta at `s = 1`). -/
theorem centeredXi_eq_stirling {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1 / 2) :
    centeredXi w =
      Complex.cpow (Real.pi / 2) (1 / 4) * Complex.cpow w (7 / 4) *
        Complex.exp ((w / 2) * (Complex.log (w / (2 * Real.pi)) - 1)) *
        riemannZeta (1 / 2 + w) * gammaRemainder w :=
  centeredXi_eq_stirling_of_ne_zero (fun h => by simp [h] at hw)
    (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith) hw1

/-! ### The contour variable -/

/-- The real part of the contour point `contourW d q θ` is `R cos (θ / 2)`, where
`R = scaleT d * saddleRadius d (saddleAngle d q)`. -/
theorem contourW_re (d : ℕ) (q θ : ℝ) :
    (contourW d q θ).re =
      scaleT d * saddleRadius d (saddleAngle d q) * Real.cos (θ / 2) := by
  unfold contourW
  rw [Complex.re_ofReal_mul, show Complex.I * (θ : ℂ) / 2 = ((θ / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_ofReal_mul_I_re]

/-! ### Two-sided amplitude bounds where `re (1/2 + w) ≥ 4` -/

/-- The constant `c` in the lower bound `c * R^{7/4} ≤ ‖amplitude d q θ‖` on the contour
points of radius `R ≥ 200` where `re (1/2 + w) ≥ 4`. -/
noncomputable def amplitudeLowerConst : ℝ :=
  ‖amplitudeConst‖ * (3 / 4) * (67 / 100)

/-- The constant `C` in the upper bound `‖amplitude d q θ‖ ≤ C * R^{7/4}` on the contour
points of radius `R ≥ 200` where `re (1/2 + w) ≥ 4`. -/
noncomputable def amplitudeUpperConst : ℝ :=
  ‖amplitudeConst‖ * (4 / 3) * (133 / 100)

/-- The lower amplitude constant is positive. -/
theorem amplitudeLowerConst_pos : 0 < amplitudeLowerConst := by
  have := norm_pos_iff.mpr amplitudeConst_ne_zero
  unfold amplitudeLowerConst
  positivity

/-- The upper amplitude constant is positive. -/
theorem amplitudeUpperConst_pos : 0 < amplitudeUpperConst := by
  have := norm_pos_iff.mpr amplitudeConst_ne_zero
  unfold amplitudeUpperConst
  positivity

/-- The amplitude does not vanish at a contour point `w` of radius `R ≥ 200` with
`re (1/2 + w) ≥ 4`. -/
theorem amplitude_ne_zero_of_four_le_re (d : ℕ) (q θ : ℝ)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hre : 4 ≤ (1 / 2 + contourW d q θ).re) :
    amplitude d q θ ≠ 0 := by
  obtain ⟨-, hW0, -, -, hz0, hg0, -⟩ := local_point_facts hre
    (by rw [norm_contourW d q θ (by linarith)]; linarith)
  rw [amplitude_eq_const_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero amplitudeConst_ne_zero
    ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hW0)) hz0) hg0

/-- At a contour point `w` of radius `R ≥ 200` with `re (1/2 + w) ≥ 4`, the amplitude
satisfies `amplitudeLowerConst * R^{7/4} ≤ ‖a(θ)‖ ≤ amplitudeUpperConst * R^{7/4}`. -/
theorem amplitude_bounds_of_four_le_re (d : ℕ) (q θ : ℝ)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hre : 4 ≤ (1 / 2 + contourW d q θ).re) :
    amplitudeLowerConst * (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) ≤
        ‖amplitude d q θ‖ ∧
      ‖amplitude d q θ‖ ≤
        amplitudeUpperConst * (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) := by
  set R := scaleT d * saddleRadius d (saddleAngle d q)
  have hRpos : 0 < R := by linarith
  have hn : ‖contourW d q θ‖ = R := norm_contourW d q θ hRpos.le
  obtain ⟨-, -, -, -, -, -, hre0⟩ := local_point_facts hre (by rw [hn]; linarith)
  have hg := gammaRemainder_norm_bounds hre0 (by rwa [hn])
  set X := ‖amplitudeConst‖ * R ^ (7 / 4 : ℝ) with hX
  have hXpos : 0 < X := mul_pos (norm_pos_iff.mpr amplitudeConst_ne_zero) (by positivity)
  rw [norm_amplitude d q θ hRpos]
  have hlo : amplitudeLowerConst * R ^ (7 / 4 : ℝ) = X * ((3 / 4) * (67 / 100)) := by
    rw [amplitudeLowerConst, hX]
    ring
  have hhi : amplitudeUpperConst * R ^ (7 / 4 : ℝ) = X * ((4 / 3) * (133 / 100)) := by
    rw [amplitudeUpperConst, hX]
    ring
  rw [hlo, hhi, mul_assoc X]
  exact ⟨mul_le_mul_of_nonneg_left (mul_le_mul (three_fourths_le_norm_riemannZeta hre) hg.1
      (by norm_num) (norm_nonneg _)) hXpos.le,
    mul_le_mul_of_nonneg_left (mul_le_mul (norm_riemannZeta_le_four_thirds hre) hg.2
      (norm_nonneg _) (by norm_num)) hXpos.le⟩

/-- **Saddle amplitude nonvanishing** (given the local zeta domain at the saddle). -/
theorem saddle_amplitude_ne_zero (d : ℕ) (q : ℝ)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hre : 4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re) :
    amplitude d q (saddleTheta d q) ≠ 0 :=
  amplitude_ne_zero_of_four_le_re d q _ hR hre

/-- **Saddle amplitude lower bound** (given the local zeta domain at the saddle). -/
theorem saddle_amplitude_lower (d : ℕ) (q : ℝ)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hre : 4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re) :
    amplitudeLowerConst * (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) ≤
      ‖amplitude d q (saddleTheta d q)‖ :=
  (amplitude_bounds_of_four_le_re d q _ hR hre).1

/-- **Saddle amplitude upper bound** (given the local zeta domain at the saddle). -/
theorem saddle_amplitude_upper (d : ℕ) (q : ℝ)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hre : 4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re) :
    ‖amplitude d q (saddleTheta d q)‖ ≤
      amplitudeUpperConst * (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) :=
  (amplitude_bounds_of_four_le_re d q _ hR hre).2

/-! ### The whole circle -/

/-- **Whole-circle amplitude bound**: on the closed circle `-π ≤ θ ≤ π` of radius
`R = scaleT d * saddleRadius d (saddleAngle d q) ≥ 200`,
`‖a(θ)‖ ≤ C₁ R^{7/4} √(1/2 + R)` with an absolute `C₁`. -/
theorem exists_amplitude_circle_bound :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (d : ℕ) (q θ : ℝ), -Real.pi ≤ θ → θ ≤ Real.pi →
      200 ≤ scaleT d * saddleRadius d (saddleAngle d q) →
      ‖amplitude d q θ‖ ≤
        C₁ * (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) *
          Real.sqrt (1 / 2 + scaleT d * saddleRadius d (saddleAngle d q)) := by
  obtain ⟨C, hC, hζ⟩ := exists_global_riemannZeta_sqrt_bound
  have hA := norm_pos_iff.mpr amplitudeConst_ne_zero
  refine ⟨‖amplitudeConst‖ * C * (133 / 100), by positivity, ?_⟩
  intro d q θ hθ1 hθ2 hR
  set R := scaleT d * saddleRadius d (saddleAngle d q)
  have hRpos : 0 < R := by linarith
  set w := contourW d q θ with hw
  have hn : ‖w‖ = R := norm_contourW d q θ hRpos.le
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hre0 : 0 ≤ w.re := by rw [hw, contourW_re]; positivity
  have hsre : 1 / 2 ≤ (1 / 2 + w).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hs_lo : R - 1 / 2 ≤ ‖1 / 2 + w‖ := by
    have := norm_sub_norm_le w (-(1 / 2 : ℂ))
    rwa [norm_neg, hhalf, hn, sub_neg_eq_add, add_comm] at this
  have hs_hi : ‖1 / 2 + w‖ ≤ 1 / 2 + R := by
    have := norm_add_le (1 / 2 : ℂ) w
    rwa [hhalf, hn] at this
  have hz : ‖riemannZeta (1 / 2 + w)‖ ≤ C * Real.sqrt (1 / 2 + R) :=
    (hζ (1 / 2 + w) hsre (by linarith)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs_hi) hC.le)
  have hg := gammaRemainder_norm_bounds hre0 (by rwa [hn])
  rw [norm_amplitude d q θ hRpos]
  calc ‖amplitudeConst‖ * R ^ (7 / 4 : ℝ) * ‖riemannZeta (1 / 2 + w)‖ *
        ‖gammaRemainder w‖
      = (‖amplitudeConst‖ * R ^ (7 / 4 : ℝ)) *
          (‖riemannZeta (1 / 2 + w)‖ * ‖gammaRemainder w‖) := by ring
    _ ≤ (‖amplitudeConst‖ * R ^ (7 / 4 : ℝ)) * (C * Real.sqrt (1 / 2 + R) * (133 / 100)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hz hg.2 (norm_nonneg _) (by positivity))
          (by positivity)
    _ = ‖amplitudeConst‖ * C * (133 / 100) * R ^ (7 / 4 : ℝ) * Real.sqrt (1 / 2 + R) := by
        ring

/-- **Whole-circle amplitude ratio**, square-root-of-radius form. -/
theorem exists_global_amplitude_ratio :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (d : ℕ) (q θ : ℝ), -Real.pi ≤ θ → θ ≤ Real.pi →
      200 ≤ scaleT d * saddleRadius d (saddleAngle d q) →
      4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re →
      ‖amplitude d q θ‖ / ‖amplitude d q (saddleTheta d q)‖ ≤
        C₂ * Real.sqrt (1 / 2 + scaleT d * saddleRadius d (saddleAngle d q)) := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_amplitude_circle_bound
  have hc := amplitudeLowerConst_pos
  refine ⟨C₁ / amplitudeLowerConst, by positivity, fun d q θ hθ1 hθ2 hR hre => ?_⟩
  set R := scaleT d * saddleRadius d (saddleAngle d q)
  have hRpos : 0 < R := by linarith
  have hlow := saddle_amplitude_lower d q hR hre
  rw [div_le_iff₀ ((mul_pos hc (by positivity)).trans_le hlow)]
  calc ‖amplitude d q θ‖ ≤ C₁ * R ^ (7 / 4 : ℝ) * Real.sqrt (1 / 2 + R) :=
        hb d q θ hθ1 hθ2 hR
    _ = C₁ / amplitudeLowerConst * Real.sqrt (1 / 2 + R) *
          (amplitudeLowerConst * R ^ (7 / 4 : ℝ)) := by
        field_simp
    _ ≤ C₁ / amplitudeLowerConst * Real.sqrt (1 / 2 + R) *
          ‖amplitude d q (saddleTheta d q)‖ :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **Whole-circle amplitude ratio**, `T_d^{1/2}` form: when the radius is
bounded, `R ≤ K T_d`, the ratio is at most `C₂ √T_d`. -/
theorem exists_global_amplitude_ratio_sqrt_scaleT (K : ℝ) (hK : 0 ≤ K) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (d : ℕ) (q θ : ℝ), -Real.pi ≤ θ → θ ≤ Real.pi →
      200 ≤ scaleT d * saddleRadius d (saddleAngle d q) →
      scaleT d * saddleRadius d (saddleAngle d q) ≤ K * scaleT d →
      4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re →
      ‖amplitude d q θ‖ / ‖amplitude d q (saddleTheta d q)‖ ≤
        C₂ * Real.sqrt (scaleT d) := by
  obtain ⟨C₂, hC₂, hb⟩ := exists_global_amplitude_ratio
  refine ⟨C₂ * Real.sqrt (2 * (K + 1)), by positivity, ?_⟩
  intro d q θ hθ1 hθ2 hR hRK hre
  set R := scaleT d * saddleRadius d (saddleAngle d q)
  set T := scaleT d
  have hT0 : 0 ≤ T := by nlinarith
  have hle : 1 / 2 + R ≤ 2 * (K + 1) * T := by nlinarith
  calc _ ≤ C₂ * Real.sqrt (1 / 2 + R) := hb d q θ hθ1 hθ2 hR hre
    _ ≤ C₂ * (Real.sqrt (2 * (K + 1)) * Real.sqrt T) :=
        mul_le_mul_of_nonneg_left
          ((Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_mul' _ hT0)) hC₂.le
    _ = C₂ * Real.sqrt (2 * (K + 1)) * Real.sqrt T := by ring

/-! ### The real part on the local arc -/

/-- **Local contour real-part bound**: for an angular displacement `|t| ≤ cos α_q` from the saddle
`θ_q = -2 α_q`, `re w(θ_q + t) ≥ R cos α_q / 2`. -/
theorem contourW_local_re_ge (d : ℕ) (q t : ℝ)
    (hR : 0 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (ht : |t| ≤ Real.cos (saddleAngle d q)) :
    scaleT d * saddleRadius d (saddleAngle d q) * Real.cos (saddleAngle d q) / 2 ≤
      (contourW d q (saddleTheta d q + t)).re := by
  set α := saddleAngle d q with hα
  rw [contourW_re, saddleTheta, ← hα, show (-2 * α + t) / 2 = -(α - t / 2) by ring,
    Real.cos_neg]
  have hlip := Real.abs_cos_sub_cos_le (α - t / 2) α
  rw [show α - t / 2 - α = -(t / 2) by ring, abs_neg, abs_div, abs_two] at hlip
  have hc : Real.cos α / 2 ≤ Real.cos (α - t / 2) := by
    linarith [neg_abs_le (Real.cos (α - t / 2) - Real.cos α)]
  linarith [mul_le_mul_of_nonneg_left hc hR]

/-- **Local zeta domain** from the real-part bound: if moreover `R cos α_q ≥ 7`,
then `re (1/2 + w(θ_q + t)) ≥ 4`. -/
theorem contourW_local_zeta_domain (d : ℕ) (q t : ℝ)
    (hR : 0 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (ht : |t| ≤ Real.cos (saddleAngle d q))
    (h7 : 7 ≤ scaleT d * saddleRadius d (saddleAngle d q) * Real.cos (saddleAngle d q)) :
    4 ≤ (1 / 2 + contourW d q (saddleTheta d q + t)).re := by
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
  linarith [contourW_local_re_ge d q t hR ht]

end RiemannJensen
