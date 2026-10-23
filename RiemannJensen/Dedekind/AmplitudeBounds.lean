module

public import RiemannJensen.Dedekind.ContourWindowGeometry
public import RiemannJensen.Dedekind.ContinuationStripBounds
public import RiemannJensen.Dedekind.ZetaLogDerivative
public import RiemannJensen.Dedekind.GammaLogDerivative

/-!
# Quantitative bounds for the Dedekind saddle amplitude

Bounds for the contour amplitude `dedekindAmplitude K d q θ` of a number field `K`: two-sided
estimates at the lower saddle point, a ratio bound on the whole lower semicircle, and uniform
bounds for the normalized local amplitude and its logarithmic derivative.

## Main definitions

* `dedekindLocalAmplitudeLogDeriv`: The logarithmic derivative expression of the normalized
  amplitude along the local angular coordinate.

## Main results

* `norm_dedekindAmplitude_eq`: The norm of the amplitude is the product of the leading
  constant, a real power, the zeta factor and the Gamma remainder.
* `dedekind_saddle_amplitude_lower`, `dedekind_saddle_amplitude_upper`: Two-sided bounds for
  the amplitude at the lower saddle point.
* `dedekind_global_amplitude_ratio`: On the lower semicircle the amplitude is at most a
  constant times `T_d ^ [K : ℚ]` times its saddle value.
* `dedekind_local_amplitude_bound`: The normalized local amplitude is uniformly bounded.
* `dedekind_local_amplitude_C1_conditional`: Under real-part control, the logarithmic
  derivative expression is uniformly bounded.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- Exact norm factorization of the contour amplitude. -/
theorem norm_dedekindAmplitude_eq {d : ℕ} {q θ : ℝ} (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) :
    ‖dedekindAmplitude K d q θ‖ =
      dedekindLeadingConstant K *
        (dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
          dedekindPowerExponent K *
      ‖analyticDedekindZeta K (1 / 2 + dedekindContourW K d q θ)‖ *
        ‖dedekindGammaRemainder K (dedekindContourW K d q θ)‖ := by
  rw [dedekindAmplitude, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (dedekindLeadingConstant_pos K).le, Complex.cpow_eq_pow,
    Complex.norm_cpow_real, norm_dedekindContourW K hT hr]

/-- Pointwise lower amplitude estimate from lower bounds for its zeta and
Gamma factors. -/
theorem norm_dedekindAmplitude_lower_of_factors
    {d : ℕ} {q θ Z G : ℝ}
    (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hZ : Z ≤ ‖analyticDedekindZeta K (1 / 2 + dedekindContourW K d q θ)‖)
    (hG : G ≤ ‖dedekindGammaRemainder K (dedekindContourW K d q θ)‖) (hG0 : 0 ≤ G) :
    dedekindLeadingConstant K * Z * G *
        (dedekindScaleT K d *
          dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
            dedekindPowerExponent K ≤
      ‖dedekindAmplitude K d q θ‖ := by
  rw [norm_dedekindAmplitude_eq K hT hr]
  have hp : 0 ≤ (dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
        dedekindPowerExponent K := Real.rpow_nonneg (mul_nonneg hT hr) _
  have hcp := mul_nonneg (dedekindLeadingConstant_pos K).le hp
  calc
    _ = dedekindLeadingConstant K *
          (dedekindScaleT K d *
            dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
              dedekindPowerExponent K * Z * G := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hZ hcp) hG hG0
      (mul_nonneg hcp (norm_nonneg _))

/-- Pointwise upper amplitude estimate from upper bounds for its zeta and
Gamma factors. -/
theorem norm_dedekindAmplitude_upper_of_factors
    {d : ℕ} {q θ Z G : ℝ}
    (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hZ : ‖analyticDedekindZeta K (1 / 2 + dedekindContourW K d q θ)‖ ≤ Z)
    (hG : ‖dedekindGammaRemainder K (dedekindContourW K d q θ)‖ ≤ G) :
    ‖dedekindAmplitude K d q θ‖ ≤
      dedekindLeadingConstant K * Z * G *
        (dedekindScaleT K d *
          dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
            dedekindPowerExponent K := by
  rw [norm_dedekindAmplitude_eq K hT hr]
  have hp : 0 ≤ (dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
        dedekindPowerExponent K := Real.rpow_nonneg (mul_nonneg hT hr) _
  have hcp := mul_nonneg (dedekindLeadingConstant_pos K).le hp
  calc
    _ ≤ dedekindLeadingConstant K *
          (dedekindScaleT K d *
            dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
              dedekindPowerExponent K * Z * G :=
      mul_le_mul (mul_le_mul_of_nonneg_left hZ hcp) hG (norm_nonneg _)
        (mul_nonneg hcp ((norm_nonneg _).trans hZ))
    _ = _ := by ring

/-- Above the edge and below the scale, the saddle radius at the saddle angle is positive. -/
theorem dedekindSaddleRadius_pos_of_edgeQ_lt {d : ℕ} (hd1 : 1 ≤ d) {q : ℝ}
    (hedge : dedekindEdgeQ K d < q) (hqT : q ≤ dedekindScaleT K d) :
    0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q) := by
  have hα := dedekindSaddle_inverse_range K d hd1 ⟨hedge, hqT⟩
  exact dedekindSaddleRadius_pos K d hd1 ⟨hα.1.le, hα.2.le⟩

private theorem half_le_norm_and_norm_le_three_halves {g : ℂ} (h : ‖g - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖g‖ ∧ ‖g‖ ≤ 3 / 2 := by
  have h₁ := norm_sub_norm_le (1 : ℂ) g
  have h₂ := norm_sub_norm_le g 1
  rw [norm_one, norm_sub_rev] at h₁
  rw [norm_one] at h₂
  constructor <;> linarith

private theorem le_pi_div_mul_div_of_mul_le {a c₀ q T : ℝ} (ha : 0 ≤ a) (hq : 0 < q)
    (hT : 0 ≤ T) (hqc : q ≤ c₀ * T) (hac : a * c₀ ≤ Real.pi / 32) :
    a ≤ Real.pi / 32 * T / q := by
  rw [le_div_iff₀ hq]
  calc
    a * q ≤ a * (c₀ * T) := by gcongr
    _ ≤ Real.pi / 32 * T := by nlinarith

/-- Two-sided zeta and Gamma factor bounds at every point of the local window around the lower
saddle point, for `c₀` below the field-dependent threshold. -/
theorem dedekind_local_factor_bounds {W c₀ : ℝ} (hW : 0 < W)
    (hnear : ∀ w : ℂ, |Complex.arg w| ≤ 2 * Real.pi / 3 → W ≤ ‖w‖ →
      ‖dedekindGammaRemainder K w - 1‖ ≤ 1 / 2 ∧ dedekindGammaRemainder K w ≠ 0)
    (hcpi : c₀ ≤ Real.pi / 128) (hcW : c₀ ≤ Real.pi / (64 * W)) {d : ℕ} (hd1 : 1 ≤ d)
    (hlocal : ∀ q : ℝ, dedekindEdgeQ K d < q → q ≤ dedekindScaleT K d →
      ∀ θ ∈ Icc (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
          (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q),
        Real.pi / 32 * dedekindScaleT K d / q ≤ (dedekindContourW K d q θ).re)
    {q : ℝ} (hedge : dedekindEdgeQ K d < q) (hqc : q ≤ c₀ * dedekindScaleT K d)
    {y : ℝ} (hy : |y| ≤ 1) :
    Real.exp (-dedekindEulerLogMajorant K 4) ≤ ‖analyticDedekindZeta K (1 / 2 +
        dedekindContourW K d q (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ∧
      ‖analyticDedekindZeta K (1 / 2 +
        dedekindContourW K d q (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ≤
        Real.exp (dedekindEulerLogMajorant K 4) ∧
      (1 / 2 : ℝ) ≤ ‖dedekindGammaRemainder K
        (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ∧
      ‖dedekindGammaRemainder K
        (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ≤
        3 / 2 := by
  have hT := dedekindScaleT_pos K d hd1
  have hqT : q ≤ dedekindScaleT K d :=
    hqc.trans (mul_le_of_le_one_left hT.le (by linarith [Real.pi_lt_four]))
  have hα := dedekindSaddle_inverse_range K d hd1 ⟨hedge, hqT⟩
  have hαcc : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hwidth : 0 ≤ dedekindLocalWidth K d q := by
    unfold dedekindLocalWidth dedekindLocalEpsilon
    exact mul_nonneg (by norm_num)
      (le_min hαcc.1 (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hαcc.1], hαcc.2⟩))
  have hθmem :
      -2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y ∈
        Icc (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
          (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q) := by
    rw [abs_le] at hy
    constructor <;> nlinarith
  have hqpos : 0 < q := by
    have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd1 hαcc
    rw [dedekindSaddle_inverse K d hd1 ⟨hedge, hqT⟩] at hqr
    nlinarith [sq_nonneg (dedekindSaddleRadius K d (dedekindSaddleAngle K d q))]
  let w := dedekindContourW K d q
    (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y)
  have hrebase : Real.pi / 32 * dedekindScaleT K d / q ≤ w.re := hlocal q hedge hqT _ hθmem
  have hreW : W ≤ w.re := by
    rw [le_div_iff₀ (by positivity)] at hcW
    linarith [le_pi_div_mul_div_of_mul_le (a := 2 * W) (by positivity) hqpos hT.le hqc
      (by linarith)]
  have hre4 : 4 ≤ (1 / 2 + w).re := by
    have := le_pi_div_mul_div_of_mul_le (a := 4) (by norm_num) hqpos hT.le hqc (by linarith)
    norm_num [add_re]
    linarith
  have hwnorm : W ≤ ‖w‖ := hreW.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hwarg : |Complex.arg w| ≤ 2 * Real.pi / 3 :=
    (Complex.abs_arg_le_pi_div_two_iff.mpr (hW.le.trans hreW)).trans
      (by linarith [Real.pi_pos])
  have hg := half_le_norm_and_norm_le_three_halves (hnear w hwarg hwnorm).1
  exact ⟨exp_neg_majorant_four_le_analyticDedekindZeta_norm K hre4,
    analyticDedekindZeta_norm_le_exp_majorant_four K hre4, hg.1, hg.2⟩

/-- There is `c₁ ∈ (0, 1]` such that for `0 < c₀ ≤ c₁`, eventually in `d`, the zeta and Gamma
factors on the local arc around the lower saddle point are bounded above and below by explicit
constants. -/
theorem exists_dedekind_local_factor_bounds :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ, dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ∀ y : ℝ, |y| ≤ 1 →
          Real.exp (-dedekindEulerLogMajorant K 4) ≤ ‖analyticDedekindZeta K (1 / 2 +
              dedekindContourW K d q
                (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ∧
            ‖analyticDedekindZeta K (1 / 2 + dedekindContourW K d q
                (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ≤
              Real.exp (dedekindEulerLogMajorant K 4) ∧
            (1 / 2 : ℝ) ≤ ‖dedekindGammaRemainder K (dedekindContourW K d q
                (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ∧
            ‖dedekindGammaRemainder K (dedekindContourW K d q
                (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))‖ ≤ 3 / 2 := by
  obtain ⟨W, hW, hnear⟩ := GammaSector.dedekindGammaRemainder_near_one K
  refine ⟨min (Real.pi / 128) (Real.pi / (64 * W)), lt_min (by positivity) (by positivity),
    (min_le_left _ _).trans (by linarith [Real.pi_lt_four] : Real.pi / 128 ≤ 1),
    fun c₀ hc₀ hc₀c₁ => ?_⟩
  filter_upwards [dedekind_contour_local_re K, eventually_ge_atTop 1] with d hlocal hd1
  intro q hedge hqc y hy
  exact dedekind_local_factor_bounds K hW hnear (hc₀c₁.trans (min_le_left _ _))
    (hc₀c₁.trans (min_le_right _ _)) hd1 hlocal hedge hqc hy

/-- There is `c₁ ∈ (0, 1]` such that for `0 < c₀ ≤ c₁`, eventually in `d`, the zeta and Gamma
factors at the lower saddle point are bounded above and below by explicit constants. -/
theorem exists_dedekind_saddle_factor_bounds :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ, dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        Real.exp (-dedekindEulerLogMajorant K 4) ≤
            ‖analyticDedekindZeta K
              (1 / 2 + dedekindContourW K d q (-2 * dedekindSaddleAngle K d q))‖ ∧
          ‖analyticDedekindZeta K
              (1 / 2 + dedekindContourW K d q (-2 * dedekindSaddleAngle K d q))‖ ≤
            Real.exp (dedekindEulerLogMajorant K 4) ∧
          (1 / 2 : ℝ) ≤
            ‖dedekindGammaRemainder K (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q))‖ ∧
          ‖dedekindGammaRemainder K (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q))‖ ≤
            3 / 2 := by
  obtain ⟨c₁, hc₁, hc₁one, hl⟩ := exists_dedekind_local_factor_bounds K
  refine ⟨c₁, hc₁, hc₁one, fun c₀ hc₀ hc₀c₁ => ?_⟩
  filter_upwards [hl c₀ hc₀ hc₀c₁] with d hd q hedge hqc
  simpa only [mul_zero, add_zero] using hd q hedge hqc 0 (by simp)

/-- For small enough `c₀`, eventually in `d`, the amplitude at the lower saddle point is
bounded below by a constant times `(T_d * r_d) ^ dedekindPowerExponent K`, where `r_d` is the
saddle radius. -/
theorem dedekind_saddle_amplitude_lower :
    ∃ c₁ c : ℝ, 0 < c₁ ∧ 0 < c ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        c * (dedekindScaleT K d *
          dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
            dedekindPowerExponent K ≤
          ‖dedekindAmplitude K d q
            (-2 * dedekindSaddleAngle K d q)‖ := by
  obtain ⟨c₁, hc₁, hc₁one, hfac⟩ := exists_dedekind_saddle_factor_bounds K
  refine ⟨c₁, dedekindLeadingConstant K * Real.exp (-dedekindEulerLogMajorant K 4) * (1 / 2),
    hc₁, mul_pos (mul_pos (dedekindLeadingConstant_pos K) (Real.exp_pos _)) (by norm_num),
    fun c₀ hc₀ hc₀c₁ => ?_⟩
  filter_upwards [hfac c₀ hc₀ hc₀c₁, eventually_ge_atTop 1] with d hd hd1
  intro q hedge hqc
  have hT := dedekindScaleT_pos K d hd1
  have hqT : q ≤ dedekindScaleT K d :=
    hqc.trans (mul_le_of_le_one_left hT.le (hc₀c₁.trans hc₁one))
  exact norm_dedekindAmplitude_lower_of_factors K hT.le
    (dedekindSaddleRadius_pos_of_edgeQ_lt K hd1 hedge hqT).le (hd q hedge hqc).1
    (hd q hedge hqc).2.2.1 (by norm_num)

/-- For small enough `c₀`, eventually in `d`, the amplitude at the lower saddle point is
bounded above by a constant times `(T_d * r_d) ^ dedekindPowerExponent K`, where `r_d` is the
saddle radius. -/
theorem dedekind_saddle_amplitude_upper :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ‖dedekindAmplitude K d q
            (-2 * dedekindSaddleAngle K d q)‖ ≤
          C * (dedekindScaleT K d *
            dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
              dedekindPowerExponent K := by
  obtain ⟨c₁, hc₁, hc₁one, hfac⟩ := exists_dedekind_saddle_factor_bounds K
  refine ⟨c₁, dedekindLeadingConstant K * Real.exp (dedekindEulerLogMajorant K 4) * (3 / 2),
    hc₁, mul_pos (mul_pos (dedekindLeadingConstant_pos K) (Real.exp_pos _)) (by norm_num),
    fun c₀ hc₀ hc₀c₁ => ?_⟩
  filter_upwards [hfac c₀ hc₀ hc₀c₁, eventually_ge_atTop 1] with d hd hd1
  intro q hedge hqc
  have hT := dedekindScaleT_pos K d hd1
  have hqT : q ≤ dedekindScaleT K d :=
    hqc.trans (mul_le_of_le_one_left hT.le (hc₀c₁.trans hc₁one))
  exact norm_dedekindAmplitude_upper_of_factors K hT.le
    (dedekindSaddleRadius_pos_of_edgeQ_lt K hd1 hedge hqT).le (hd q hedge hqc).2.1
    (hd q hedge hqc).2.2.2

/-- Bound for the ratio of the amplitude at `θ` to its value at the lower saddle point, from
lower bounds for the saddle factors and upper bounds for the factors at `θ`. -/
theorem norm_dedekindAmplitude_div_saddle_le_of_factors
    {d : ℕ} {q θ : ℝ} {z₀ g₀ Z G : ℝ}
    (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hTr : 0 < dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hz₀ : 0 < z₀) (hg₀ : 0 < g₀)
    (hzs : z₀ ≤ ‖analyticDedekindZeta K
      (1 / 2 + dedekindContourW K d q
        (-2 * dedekindSaddleAngle K d q))‖)
    (hgs : g₀ ≤ ‖dedekindGammaRemainder K
      (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q))‖)
    (hzθ : ‖analyticDedekindZeta K
      (1 / 2 + dedekindContourW K d q θ)‖ ≤ Z)
    (hgθ : ‖dedekindGammaRemainder K
      (dedekindContourW K d q θ)‖ ≤ G) :
    ‖dedekindAmplitude K d q θ /
      dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q)‖ ≤
        (Z * G) / (z₀ * g₀) := by
  have hscale : 0 <
      dedekindLeadingConstant K * z₀ * g₀ *
        (dedekindScaleT K d *
          dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
            dedekindPowerExponent K :=
    mul_pos (mul_pos (mul_pos (dedekindLeadingConstant_pos K) hz₀) hg₀)
      (Real.rpow_pos_of_pos hTr _)
  rw [norm_div]
  calc
    _ ≤ (dedekindLeadingConstant K * Z * G *
          (dedekindScaleT K d *
            dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
              dedekindPowerExponent K) /
        (dedekindLeadingConstant K * z₀ * g₀ *
          (dedekindScaleT K d *
            dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^
              dedekindPowerExponent K) :=
      div_le_div₀ (mul_nonneg (mul_nonneg (mul_nonneg (dedekindLeadingConstant_pos K).le
        ((norm_nonneg _).trans hzθ)) ((norm_nonneg _).trans hgθ)) (Real.rpow_nonneg hTr.le _))
        (norm_dedekindAmplitude_upper_of_factors K hT hr hzθ hgθ) hscale
        (norm_dedekindAmplitude_lower_of_factors K hT hr hzs hgs hg₀.le)
    _ = (Z * G) / (z₀ * g₀) := by
      field_simp [(dedekindLeadingConstant_pos K).ne',
        hz₀.ne', hg₀.ne', (Real.rpow_pos_of_pos hTr _).ne']

private theorem le_mul_of_one_le_mul_sq {W c₀ T q r : ℝ} (hW : 0 ≤ W) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hqr : 1 ≤ q * r ^ 2) (hqc : q ≤ c₀ * T) (hTW : W ^ 2 * c₀ ≤ T) :
    W ≤ T * r := by
  refine (sq_le_sq₀ hW (mul_nonneg hT hr)).mp ?_
  calc
    W ^ 2 ≤ W ^ 2 * (c₀ * T * r ^ 2) :=
      le_mul_of_one_le_right (sq_nonneg W)
        (hqr.trans (mul_le_mul_of_nonneg_right hqc (sq_nonneg r)))
    _ = (W ^ 2 * c₀) * (T * r ^ 2) := by ring
    _ ≤ T * (T * r ^ 2) := mul_le_mul_of_nonneg_right hTW (mul_nonneg hT (sq_nonneg r))
    _ = (T * r) ^ 2 := by ring

/-- A polynomial bound for the zeta factor at `1 / 2 + w` from the global zeta bound, when `w`
lies in the right half-plane with `4 ≤ ‖w‖ ≤ 2 * T`. -/
theorem norm_analyticDedekindZeta_half_add_le {Cζ : ℝ} (hCζ : 0 ≤ Cζ)
    (hzeta : ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖analyticDedekindZeta K s‖ ≤ Cζ * ‖s‖ ^ dedekindDegree K)
    {w : ℂ} {T : ℝ} (hwre : 0 ≤ w.re) (hw4 : 4 ≤ ‖w‖) (hwT : ‖w‖ ≤ 2 * T) :
    ‖analyticDedekindZeta K (1 / 2 + w)‖ ≤ Cζ * (4 * T) ^ dedekindDegree K := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hsre : (1 / 2 : ℝ) ≤ (1 / 2 + w).re := by simpa using hwre
  have hlow : 2 ≤ ‖(1 / 2 : ℂ) + w‖ := by
    have h := norm_sub_norm_le w (-(1 / 2 : ℂ))
    rw [norm_neg, hhalf, sub_neg_eq_add] at h
    rw [add_comm]
    linarith
  have hup : ‖(1 / 2 : ℂ) + w‖ ≤ 4 * T := by
    have h := norm_add_le (1 / 2 : ℂ) w
    rw [hhalf] at h
    linarith
  exact (hzeta _ hsre hlow).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hup _) hCζ)

/-- On the lower semicircle `-π ≤ θ ≤ 0` the contour point lies in the closed right half-plane. -/
theorem dedekindContourW_re_nonneg {d : ℕ} {q θ : ℝ} (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hθlo : -Real.pi ≤ θ) (hθhi : θ ≤ 0) : 0 ≤ (dedekindContourW K d q θ).re := by
  rw [dedekindContourW_re]
  exact mul_nonneg (mul_nonneg hT hr) (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)

/-- If `q ≤ c₀ T_d` and `W ^ 2 c₀ ≤ T_d`, every contour point has norm at least `W`. -/
theorem le_norm_dedekindContourW {W c₀ : ℝ} (hW : 0 ≤ W) {d : ℕ} (hd1 : 1 ≤ d) {q : ℝ}
    (hedge : dedekindEdgeQ K d < q) (hqT : q ≤ dedekindScaleT K d)
    (hqc : q ≤ c₀ * dedekindScaleT K d) (hTW : W ^ 2 * c₀ ≤ dedekindScaleT K d) (θ : ℝ) :
    W ≤ ‖dedekindContourW K d q θ‖ := by
  have hT := dedekindScaleT_pos K d hd1
  have hα := dedekindSaddle_inverse_range K d hd1 ⟨hedge, hqT⟩
  have hαcc : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hrpos := dedekindSaddleRadius_pos K d hd1 hαcc
  have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd1 hαcc
  rw [dedekindSaddle_inverse K d hd1 ⟨hedge, hqT⟩] at hqr
  exact (le_mul_of_one_le_mul_sq hW hT.le hrpos.le hqr hqc hTW).trans_eq
    (norm_dedekindContourW K hT.le hrpos.le).symm

/-- On the lower semicircle the ratio of the amplitude to its value at the lower saddle point
is at most a constant times `T_d ^ [K : ℚ]`. -/
theorem dedekind_global_amplitude_ratio :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ∀ θ : ℝ, -Real.pi ≤ θ → θ ≤ 0 →
          ‖dedekindAmplitude K d q θ /
            dedekindAmplitude K d q
              (-2 * dedekindSaddleAngle K d q)‖ ≤
            C * dedekindScaleT K d ^ dedekindDegree K := by
  obtain ⟨Cζ, hCζ, hzeta⟩ := dedekind_zeta_global K
  obtain ⟨W₀, hW₀, hgamma⟩ := GammaSector.dedekindGammaRemainder_near_one K
  obtain ⟨cS, hcS, hcSone, hsaddle⟩ := exists_dedekind_saddle_factor_bounds K
  let W : ℝ := max W₀ 4
  have hW : 0 < W := hW₀.trans_le (le_max_left _ _)
  have hbase : 0 < dedekindScaleA K * Real.exp 1 := mul_pos (mul_pos (mul_pos two_pos
    Real.pi_pos) (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)) (Real.exp_pos _)
  let c₁ : ℝ := min cS (dedekindScaleA K * Real.exp 1 / W ^ 2)
  let C : ℝ :=
    (Cζ * 4 ^ dedekindDegree K * (3 / 2)) /
      (Real.exp (-dedekindEulerLogMajorant K 4) * (1 / 2))
  refine ⟨c₁, C, lt_min hcS (div_pos hbase (sq_pos_of_pos hW)),
    div_pos (by positivity) (by positivity), fun c₀ hc₀ hc₀c₁ => ?_⟩
  have hc₀one : c₀ ≤ 1 := hc₀c₁.trans ((min_le_left _ _).trans hcSone)
  filter_upwards [hsaddle c₀ hc₀ (hc₀c₁.trans (min_le_left _ _)),
    eventually_ge_atTop 1] with d hs hd1
  intro q hedge hqc θ hθlo hθhi
  have hT := dedekindScaleT_pos K d hd1
  have hqT : q ≤ dedekindScaleT K d := hqc.trans (mul_le_of_le_one_left hT.le hc₀one)
  have hα := dedekindSaddle_inverse_range K d hd1 ⟨hedge, hqT⟩
  have hrpos := dedekindSaddleRadius_pos_of_edgeQ_lt K hd1 hedge hqT
  have hTW : W ^ 2 * c₀ < dedekindScaleT K d :=
    calc
      W ^ 2 * c₀ ≤ W ^ 2 * (dedekindScaleA K * Real.exp 1 / W ^ 2) :=
        mul_le_mul_of_nonneg_left (hc₀c₁.trans (min_le_right _ _)) (sq_nonneg W)
      _ = dedekindScaleA K * Real.exp 1 := by field_simp [hW.ne']
      _ < _ := dedekindScaleT_gt_base K d hd1
  have hWw := le_norm_dedekindContourW K hW.le hd1 hedge hqT hqc hTW.le θ
  have hwre := dedekindContourW_re_nonneg K hT.le hrpos.le hθlo hθhi
  have hwarg : |Complex.arg (dedekindContourW K d q θ)| ≤ 2 * Real.pi / 3 :=
    (Complex.abs_arg_le_pi_div_two_iff.mpr hwre).trans (by linarith [Real.pi_pos])
  have hr2 : dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ≤ 2 :=
    saddleRadiusAtLambda_le_two (dedekindScaleLambda_pos K d hd1).le ⟨hα.1.le, hα.2.le⟩
  have hzupper :=
    norm_analyticDedekindZeta_half_add_le K hCζ.le hzeta (T := dedekindScaleT K d) hwre
    ((le_max_right W₀ 4).trans hWw)
    ((norm_dedekindContourW K hT.le hrpos.le).trans_le
      (by linarith [mul_le_mul_of_nonneg_left hr2 hT.le]))
  calc
    _ ≤ (Cζ * (4 * dedekindScaleT K d) ^ dedekindDegree K * (3 / 2)) /
        (Real.exp (-dedekindEulerLogMajorant K 4) * (1 / 2)) :=
      norm_dedekindAmplitude_div_saddle_le_of_factors K hT.le hrpos.le (mul_pos hT hrpos)
        (Real.exp_pos _) (by norm_num) (hs q hedge hqc).1 (hs q hedge hqc).2.2.1 hzupper
        (half_le_norm_and_norm_le_three_halves
          (hgamma _ hwarg ((le_max_left W₀ 4).trans hWw)).1).2
    _ = C * dedekindScaleT K d ^ dedekindDegree K := by
      dsimp [C]
      rw [mul_pow]
      ring

/-- For small enough `c₀`, eventually in `d`, the normalized local amplitude is bounded by a
constant uniformly for `|y| ≤ 1`. -/
theorem dedekind_local_amplitude_bound :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ∀ y : ℝ, |y| ≤ 1 →
          ‖normalizedDedekindLocalAmplitude K d q y‖ ≤ C := by
  obtain ⟨c₁, hc₁, hc₁one, hl⟩ := exists_dedekind_local_factor_bounds K
  refine ⟨c₁, (Real.exp (dedekindEulerLogMajorant K 4) * (3 / 2)) /
      (Real.exp (-dedekindEulerLogMajorant K 4) * (1 / 2)), hc₁, by positivity,
    fun c₀ hc₀ hc₀c₁ => ?_⟩
  filter_upwards [hl c₀ hc₀ hc₀c₁, eventually_ge_atTop 1] with d hd hd1
  intro q hedge hqc y hy
  have hT := dedekindScaleT_pos K d hd1
  have hqT : q ≤ dedekindScaleT K d :=
    hqc.trans (mul_le_of_le_one_left hT.le (hc₀c₁.trans hc₁one))
  have hrpos := dedekindSaddleRadius_pos_of_edgeQ_lt K hd1 hedge hqT
  have hs := hd q hedge hqc 0 (by simp)
  simp only [mul_zero, add_zero] at hs
  have hf := hd q hedge hqc y hy
  unfold normalizedDedekindLocalAmplitude
  exact norm_dedekindAmplitude_div_saddle_le_of_factors K hT.le hrpos.le (mul_pos hT hrpos)
    (Real.exp_pos _) (by norm_num) hs.1 hs.2.2.1 hf.2.1 hf.2.2.2

/-- The logarithmic derivative expression for the normalized Dedekind
amplitude along the local angular coordinate. -/
def dedekindLocalAmplitudeLogDeriv (d : ℕ) (q y : ℝ) : ℂ :=
  let ℓ := dedekindLocalWidth K d q
  let w := dedekindContourW K d q
    (-2 * dedekindSaddleAngle K d q + ℓ * y)
  Complex.I * (ℓ : ℂ) / 2 *
    ((dedekindPowerExponent K : ℂ) +
      w * (deriv (analyticDedekindZeta K) (1 / 2 + w) /
        analyticDedekindZeta K (1 / 2 + w)) +
      w * deriv (dedekindGammaLog K) w)

private theorem mul_mul_le_of_le_div_sq {ℓ x g C : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (hx : 1 ≤ x) (hC : 0 ≤ C) (hg : g ≤ C / x ^ 2) : ℓ * x * g ≤ C := by
  calc
    ℓ * x * g ≤ ℓ * x * (C / x ^ 2) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg hℓ0 (by linarith))
    _ = ℓ * C / x := by field_simp [ne_of_gt (zero_lt_one.trans_le hx)]
    _ ≤ C := by
      rw [div_le_iff₀ (zero_lt_one.trans_le hx)]
      nlinarith [mul_le_mul_of_nonneg_right hℓ1 hC]

private theorem mul_norm_ofReal_add_mul_add_mul_le {ℓ p A B : ℝ} {w a b : ℂ} (hℓ1 : ℓ ≤ 1)
    (hℓ0 : 0 ≤ ℓ) (ha : ℓ * ‖w‖ * ‖a‖ ≤ A) (hb : ℓ * ‖w‖ * ‖b‖ ≤ B) :
    ℓ * ‖(p : ℂ) + w * a + w * b‖ ≤ |p| + A + B := by
  calc
    ℓ * ‖(p : ℂ) + w * a + w * b‖ ≤ ℓ * (‖(p : ℂ)‖ + ‖w * a‖ + ‖w * b‖) := by
      gcongr
      exact norm_add₃_le
    _ = ℓ * |p| + ℓ * ‖w‖ * ‖a‖ + ℓ * ‖w‖ * ‖b‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ |p| + A + B := by linarith [mul_le_of_le_one_left (abs_nonneg p) hℓ1]

/-- If a local point lies in the Euler-product half-plane and its angular speed is controlled
by its real part, then the logarithmic derivative expression is uniformly bounded. -/
theorem dedekind_local_amplitude_C1_conditional :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ (d : ℕ) (q y : ℝ),
        let ℓ := dedekindLocalWidth K d q
        let w := dedekindContourW K d q
          (-2 * dedekindSaddleAngle K d q + ℓ * y)
        0 ≤ ℓ → ℓ ≤ 1 → 4 ≤ (1 / 2 + w).re →
        max 1 W ≤ ‖w‖ → ℓ * ‖w‖ ≤ (1 / 2 + w).re →
          ‖dedekindLocalAmplitudeLogDeriv K d q y‖ ≤ C := by
  obtain ⟨Cγ, W, hCγ, hW, hgamma⟩ := norm_deriv_dedekindGammaLog_le K
  let C : ℝ := (|dedekindPowerExponent K| + dedekindLogDerivWeightedConstant K + Cγ) / 2
  refine ⟨C, W, div_pos (add_pos (add_pos_of_nonneg_of_pos (abs_nonneg _)
    (dedekindLogDerivWeightedConstant_pos K)) hCγ) two_pos, hW, fun d q y => ?_⟩
  intro ℓ w hℓ0 hℓ1 hsre hwlarge hspeed
  have hw1 : 1 ≤ ‖w‖ := (le_max_left _ _).trans hwlarge
  have hwW : W ≤ ‖w‖ := (le_max_right _ _).trans hwlarge
  have hwre : 0 ≤ w.re := by
    norm_num [add_re] at hsre
    linarith
  have hz := analyticDedekindZeta_logDeriv_weighted K (x := ℓ * ‖w‖) (A := 1) hsre
    zero_le_one (by rwa [one_mul])
  have hsum := mul_norm_ofReal_add_mul_add_mul_le (p := dedekindPowerExponent K) hℓ1 hℓ0
    (hz.trans_eq (mul_one _))
    (mul_mul_le_of_le_div_sq hℓ0 hℓ1 hw1 hCγ.le
      (hgamma w (Complex.abs_arg_le_pi_div_two_iff.mpr hwre) hwW))
  rw [dedekindLocalAmplitudeLogDeriv, norm_mul, norm_div, norm_mul, norm_I, Complex.norm_real,
    Real.norm_of_nonneg hℓ0, norm_ofNat]
  dsimp [C]
  nlinarith

end

end RiemannJensen
