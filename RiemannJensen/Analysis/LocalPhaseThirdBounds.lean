module

public import RiemannJensen.Analysis.LocalPhaseTaylor
public import RiemannJensen.Analysis.HessianNormBounds
public import RiemannJensen.Analysis.SaddleCosineComparison

/-! # Quantitative reduction for the normalized local third derivative -/

@[expose] public section

namespace RiemannJensen

open Set

/-- The analytic local arc has constant modulus, equal to the squared saddle radius. -/
theorem norm_analyticLocalArc_real
    (ε : ℝ) (d : ℕ) (q y : ℝ) :
    ‖analyticLocalArc ε d q (y : ℂ)‖ =
      saddleRadius d (saddleAngle d q) ^ 2 := by
  simp [analyticLocalArc, saddle, Complex.norm_exp, Complex.norm_real]

/-- On the scale window the saddle radius lies in `(0, 2]`. -/
theorem saddleRadius_pos_and_le_two_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < saddleRadius d (saddleAngle d q) ∧ saddleRadius d (saddleAngle d q) ≤ 2 := by
  have hα := saddle_inverse_on_scale_window d hd hq
  exact ⟨(saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2.1.le⟩).1,
    saddleRadius_le_two d hd ⟨hα.1.le, hα.2.1.le⟩⟩

/-- The analytic square root has the expected radius norm along the real
local coordinate. -/
theorem norm_analyticLowerSqrt_localArc
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖analyticLowerSqrt (analyticLocalArc ε d q (y : ℂ))‖ =
      saddleRadius d (saddleAngle d q) := by
  have hr := (saddleRadius_pos_and_le_two_on_scale_window d hd hq).1
  rw [analyticLowerSqrt, Complex.norm_exp, Complex.div_re]
  norm_num
  rw [Complex.log_re, norm_analyticLocalArc_real, Real.log_pow]
  norm_num
  convert Real.exp_log hr using 2
  ring

/-- A scale-sized bound for the logarithm all along the local arc. -/
theorem norm_log_analyticLocalArc_le_scaleLambda
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q ε y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖Complex.log (analyticLocalArc ε d q (y : ℂ))‖ ≤
      (19 / 24 : ℝ) * scaleLambda d := by
  let r := saddleRadius d (saddleAngle d q)
  obtain ⟨hr, hr2⟩ : 0 < r ∧ r ≤ 2 := saddleRadius_pos_and_le_two_on_scale_window d hd hq
  have hlo : -(3 * scaleLambda d / 8) ≤ Real.log r :=
    saddleRadius_log_lower_on_scale_window d hd hlarge hq
  have hupp : Real.log r ≤ Real.log 2 := Real.log_le_log hr hr2
  have hlog2 : Real.log 2 ≤ 3 * scaleLambda d / 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [Real.pi_gt_three]
  have habslog : |Real.log r| ≤ 3 * scaleLambda d / 8 := by
    rw [abs_le]
    exact ⟨by linarith, hupp.trans hlog2⟩
  have hre : (Complex.log (analyticLocalArc ε d q (y : ℂ))).re =
      2 * Real.log r := by
    rw [Complex.log_re, norm_analyticLocalArc_real]
    simp [r]
  have him : |(Complex.log (analyticLocalArc ε d q (y : ℂ))).im| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩
  calc
    _ ≤ |(Complex.log (analyticLocalArc ε d q (y : ℂ))).re| +
        |(Complex.log (analyticLocalArc ε d q (y : ℂ))).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 3 * scaleLambda d / 4 + Real.pi := by
      rw [hre, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith
    _ ≤ (19 / 24 : ℝ) * scaleLambda d := by nlinarith

/-- The level term appearing in the first analytic derivative is uniformly
bounded after multiplication by the local-arc modulus. -/
theorem q_mul_norm_analyticLocalArc_le_two
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 2 * Real.pi ≤ scaleLambda d)
    {q ε y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    q * ‖analyticLocalArc ε d q (y : ℂ)‖ ≤ 2 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  rw [norm_analyticLocalArc_real]
  have hb := saddleQ_radius_sq_bounds d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hb
  have hΛ0 := scaleLambda_pos d hd
  have hfrac : 2 * Real.pi / scaleLambda d ≤ 1 :=
    (div_le_one hΛ0).2 hΛ
  linarith

/-- A norm bound for the third derivative of the normalized local phase in terms of the
dimensionless bracket of analytic phase derivatives along the local arc. -/
theorem norm_analyticLocalPhaseThird_le
    (ε : ℝ) (d : ℕ) (q y : ℝ)
    (hD : 0 < ‖saddleHessian d q‖) (hℓ : 0 < localWidth ε d q) :
    ‖analyticLocalPhaseThird ε d q (y : ℂ)‖ ≤
      localWidth ε d q / ‖saddleHessian d q‖ *
        (‖analyticPhaseDeriv3 d (analyticLocalArc ε d q (y : ℂ))‖ *
            ‖analyticLocalArc ε d q (y : ℂ)‖ ^ 3 +
          3 * ‖analyticPhaseDeriv2 d (analyticLocalArc ε d q (y : ℂ))‖ *
            ‖analyticLocalArc ε d q (y : ℂ)‖ ^ 2 +
          ‖analyticPhaseDeriv d q (analyticLocalArc ε d q (y : ℂ))‖ *
            ‖analyticLocalArc ε d q (y : ℂ)‖) := by
  let u := analyticLocalArc ε d q (y : ℂ)
  let ℓ := localWidth ε d q
  have hden : 0 < ‖saddleHessian d q‖ * ℓ ^ 2 := mul_pos hD (sq_pos_of_pos hℓ)
  change ‖(analyticPhaseDeriv3 d u * (u * (Complex.I * (ℓ : ℂ))) ^ 3 +
      3 * analyticPhaseDeriv2 d u * (u * (Complex.I * (ℓ : ℂ))) ^ 2 *
        (Complex.I * (ℓ : ℂ)) +
      analyticPhaseDeriv d q u * (u * (Complex.I * (ℓ : ℂ)) ^ 3)) /
        (((‖saddleHessian d q‖ * ℓ ^ 2 : ℝ) : ℂ))‖ ≤
    ℓ / ‖saddleHessian d q‖ *
      (‖analyticPhaseDeriv3 d u‖ * ‖u‖ ^ 3 +
        3 * ‖analyticPhaseDeriv2 d u‖ * ‖u‖ ^ 2 +
        ‖analyticPhaseDeriv d q u‖ * ‖u‖)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hden.le]
  apply (div_le_iff₀ hden).2
  calc
    _ ≤ ‖analyticPhaseDeriv3 d u * (u * (Complex.I * (ℓ : ℂ))) ^ 3‖ +
          ‖3 * analyticPhaseDeriv2 d u * (u * (Complex.I * (ℓ : ℂ))) ^ 2 *
              (Complex.I * (ℓ : ℂ))‖ +
          ‖analyticPhaseDeriv d q u * (u * (Complex.I * (ℓ : ℂ)) ^ 3)‖ :=
      norm_add₃_le
    _ = (ℓ / ‖saddleHessian d q‖ *
        (‖analyticPhaseDeriv3 d u‖ * ‖u‖ ^ 3 +
          3 * ‖analyticPhaseDeriv2 d u‖ * ‖u‖ ^ 2 +
          ‖analyticPhaseDeriv d q u‖ * ‖u‖)) *
          (‖saddleHessian d q‖ * ℓ ^ 2) := by
      simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real]
      norm_num
      rw [abs_of_pos hℓ]
      field_simp [hD.ne', hℓ.ne']
      ring

/-- The saddle Hessian does not vanish on the scale window. -/
theorem saddleHessian_norm_pos_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < ‖saddleHessian d q‖ := by
  have hα := saddle_inverse_on_scale_window d hd hq
  have hs := Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.1.trans (by linarith [Real.pi_pos]))
  exact lt_of_lt_of_le (mul_pos (by norm_num) hs)
    (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).1

/-- A bound `‖log u‖ ≤ 19Λ/24` gives `(π/Λ) ‖log u‖ ≤ 19π/24`. -/
theorem pi_div_mul_le_of_le {Λ L : ℝ} (hΛ0 : 0 < Λ) (hlog : L ≤ (19 / 24 : ℝ) * Λ) :
    Real.pi / Λ * L ≤ 19 * Real.pi / 24 := by
  have hh := mul_le_mul_of_nonneg_left hlog (div_nonneg Real.pi_pos.le hΛ0.le)
  field_simp [hΛ0.ne'] at hh ⊢
  nlinarith [Real.pi_pos]

/-- The local-width to Hessian ratio is at most an absolute multiple of `ε`. -/
theorem localWidth_div_hessianNorm_le
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) (hε : 0 ≤ ε) :
    localWidth ε d q / ‖saddleHessian d q‖ ≤ (16 / 3 : ℝ) * ε := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  have hD := (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).1
  have hsin : 0 < Real.sin (saddleAngle d q) :=
    Real.sin_pos_of_pos_of_lt_pi hα0 (hαtop.trans (by linarith [Real.pi_pos]))
  have hmin : min (saddleAngle d q) (Real.cos (saddleAngle d q)) ≤
      2 * Real.sin (saddleAngle d q) :=
    (min_le_left _ _).trans (by linarith [half_mul_le_sin ⟨hα0.le, hαtop.le⟩])
  rw [localWidth]
  apply (div_le_iff₀ (lt_of_lt_of_le (mul_pos (by norm_num) hsin) hD)).2
  have hm0 : 0 ≤ min (saddleAngle d q) (Real.cos (saddleAngle d q)) :=
    le_min hα0.le (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩)
  nlinarith [mul_le_mul_of_nonneg_left hmin hε]

/-- The dimensionless analytic-derivative bracket controlling the normalized
third derivative. -/
noncomputable def localThirdBracket (ε : ℝ) (d : ℕ) (q y : ℝ) : ℝ :=
  let u := analyticLocalArc ε d q (y : ℂ)
  ‖analyticPhaseDeriv3 d u‖ * ‖u‖ ^ 3 +
    3 * ‖analyticPhaseDeriv2 d u‖ * ‖u‖ ^ 2 +
    ‖analyticPhaseDeriv d q u‖ * ‖u‖

/-- Once the dimensionless bracket has an absolute bound, the normalized
third derivative is `O(ε)` with a completely explicit constant. -/
theorem norm_analyticLocalPhaseThird_le_of_bracket
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε K y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε : 0 < ε)
    (hbracket : localThirdBracket ε d q y ≤ K) :
    ‖analyticLocalPhaseThird ε d q (y : ℂ)‖ ≤ (16 / 3 : ℝ) * ε * K := by
  have hb0 : 0 ≤ localThirdBracket ε d q y := by
    unfold localThirdBracket
    positivity
  calc
    _ ≤ localWidth ε d q / ‖saddleHessian d q‖ * localThirdBracket ε d q y :=
      norm_analyticLocalPhaseThird_le ε d q y
        (saddleHessian_norm_pos_on_scale_window d hd hΛ hq)
        (localWidth_pos_on_scale_window d hd hq hε)
    _ ≤ (16 / 3 : ℝ) * ε * K :=
      mul_le_mul (localWidth_div_hessianNorm_le d hd hΛ hq hε.le) hbracket hb0 (by positivity)

/-- With `ε = 1/1000`, the target `1/2` bound follows already from the
coarse absolute bracket bound `30`. -/
theorem norm_analyticLocalPhaseThird_le_half_of_bracket_thirty
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hbracket : localThirdBracket (1 / 1000 : ℝ) d q y ≤ 30) :
    ‖analyticLocalPhaseThird (1 / 1000 : ℝ) d q (y : ℂ)‖ ≤ (1 / 2 : ℝ) := by
  have h := norm_analyticLocalPhaseThird_le_of_bracket d hd hΛ hq
    (by norm_num : (0 : ℝ) < 1 / 1000) hbracket
  norm_num at h ⊢
  linarith

/-- The third analytic derivative, multiplied by the cube of the local
radius, is uniformly bounded. -/
theorem analyticPhaseDeriv3_mul_localArc_norm_le_eight
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q ε y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖analyticPhaseDeriv3 d (analyticLocalArc ε d q (y : ℂ))‖ *
        ‖analyticLocalArc ε d q (y : ℂ)‖ ^ 3 ≤ 8 := by
  let u := analyticLocalArc ε d q (y : ℂ)
  let r := saddleRadius d (saddleAngle d q)
  let Λ := scaleLambda d
  obtain ⟨hr, hr2⟩ : 0 < r ∧ r ≤ 2 := saddleRadius_pos_and_le_two_on_scale_window d hd hq
  have hΛ0 : 0 < Λ := scaleLambda_pos d hd
  have hu : ‖u‖ = r ^ 2 := norm_analyticLocalArc_real ε d q y
  have hu0 : 0 < ‖u‖ := by
    rw [hu]
    positivity
  have hs : ‖analyticLowerSqrt u‖ = r := norm_analyticLowerSqrt_localArc d hd hq
  have hlog : ‖Complex.log u‖ ≤ (19 / 24 : ℝ) * Λ :=
    norm_log_analyticLocalArc_le_scaleLambda d hd hΛ hlarge hq
  have hk : Real.pi / Λ ≤ (1 / 24 : ℝ) := (div_le_iff₀ hΛ0).2 (by nlinarith [Real.pi_pos])
  let a : ℂ := 3 * (Real.pi : ℂ) * analyticLowerSqrt u / 8
  let b : ℂ := 3 * ((Real.pi / Λ : ℝ) : ℂ) *
    analyticLowerSqrt u * Complex.log u / 8
  let c : ℂ := ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt u / 4
  have ha : ‖a‖ ≤ 3 := by
    dsimp [a]
    simp only [norm_div, norm_mul, Complex.norm_real]
    norm_num
    rw [hs]
    nlinarith [Real.pi_le_four]
  have hb : ‖b‖ ≤ 2 := by
    dsimp [b]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg Real.pi_pos.le hΛ0.le)]
    norm_num
    rw [hs]
    have hp1 := mul_le_mul_of_nonneg_right (pi_div_mul_le_of_le hΛ0 hlog) hr.le
    have hp2 := mul_le_mul_of_nonneg_left hr2
      (by positivity : 0 ≤ 19 * Real.pi / 24)
    nlinarith [hp1, hp2, Real.pi_lt_d2]
  have hc : ‖c‖ ≤ 1 / 48 := by
    dsimp [c]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg Real.pi_pos.le hΛ0.le)]
    norm_num
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_right hk hr.le]
  have hnum : ‖(-2 : ℂ) + a + b - c‖ ≤ 8 := by
    have h₁ := norm_sub_le ((-2 : ℂ) + a + b) c
    have h₂ := norm_add_le ((-2 : ℂ) + a) b
    have h₃ := norm_add_le (-2 : ℂ) a
    norm_num at h₃
    linarith
  rw [analyticPhaseDeriv3, norm_div, norm_pow]
  change ‖(-2 : ℂ) + a + b - c‖ / ‖u‖ ^ 3 * ‖u‖ ^ 3 ≤ 8
  rw [div_mul_cancel₀ _ (pow_ne_zero 3 hu0.ne')]
  exact hnum

/-- The second analytic derivative has a uniform scale-invariant bound on
the local arc. -/
theorem analyticPhaseDeriv2_mul_localArc_norm_le_four
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q ε y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖analyticPhaseDeriv2 d (analyticLocalArc ε d q (y : ℂ))‖ *
        ‖analyticLocalArc ε d q (y : ℂ)‖ ^ 2 ≤ 4 := by
  let u := analyticLocalArc ε d q (y : ℂ)
  let r := saddleRadius d (saddleAngle d q)
  let Λ := scaleLambda d
  obtain ⟨hr, hr2⟩ : 0 < r ∧ r ≤ 2 := saddleRadius_pos_and_le_two_on_scale_window d hd hq
  have hΛ0 : 0 < Λ := scaleLambda_pos d hd
  have hu : ‖u‖ = r ^ 2 := norm_analyticLocalArc_real ε d q y
  have hu0 : 0 < ‖u‖ := by
    rw [hu]
    positivity
  have hs : ‖analyticLowerSqrt u‖ = r :=
    norm_analyticLowerSqrt_localArc d hd hq
  have hlog : ‖Complex.log u‖ ≤ (19 / 24 : ℝ) * Λ :=
    norm_log_analyticLocalArc_le_scaleLambda d hd hΛ hlarge hq
  let a : ℂ := (Real.pi : ℂ) * analyticLowerSqrt u / 4
  let b : ℂ := ((Real.pi / Λ : ℝ) : ℂ) *
    analyticLowerSqrt u * Complex.log u / 4
  have ha : ‖a‖ ≤ 8 / 5 := by
    dsimp [a]
    simp only [norm_div, norm_mul, Complex.norm_real]
    norm_num
    rw [hs]
    nlinarith [Real.pi_lt_d2]
  have hb : ‖b‖ ≤ 5 / 4 := by
    dsimp [b]
    simp only [norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg Real.pi_pos.le hΛ0.le)]
    norm_num
    rw [hs]
    have hp1 := mul_le_mul_of_nonneg_right (pi_div_mul_le_of_le hΛ0 hlog) hr.le
    have hp2 := mul_le_mul_of_nonneg_left hr2
      (by positivity : 0 ≤ 19 * Real.pi / 24)
    nlinarith [hp1, hp2, Real.pi_lt_d2]
  have hnum : ‖(1 : ℂ) - a - b‖ ≤ 4 := by
    linarith [norm_sub_le ((1 : ℂ) - a) b, norm_sub_le (1 : ℂ) a, norm_one (α := ℂ)]
  rw [analyticPhaseDeriv2, norm_div, norm_pow]
  change ‖(1 : ℂ) - a - b‖ / ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤ 4
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hu0.ne')]
  exact hnum

/-- The logarithmic term of the first analytic derivative, multiplied by the
local-arc modulus, is uniformly bounded at large scale. -/
theorem norm_pi_div_mul_sqrt_log_add_mul_le {Λ : ℝ} {s u : ℂ}
    (hΛ : 24 * Real.pi ≤ Λ) (hu0 : 0 < ‖u‖) (hs : ‖s‖ ≤ 2)
    (hlog : ‖Complex.log u‖ ≤ (19 / 24 : ℝ) * Λ) :
    ‖((Real.pi / Λ : ℝ) : ℂ) * ((s / (2 * u)) * Complex.log u + s / u)‖ * ‖u‖ ≤
      8 / 3 := by
  have hΛ0 : 0 < Λ := by linarith [Real.pi_pos]
  calc
    _ ≤ (Real.pi / Λ) * (‖s / (2 * u)‖ * ‖Complex.log u‖ + ‖s / u‖) * ‖u‖ := by
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg Real.pi_pos.le hΛ0.le), ← norm_mul]
      gcongr
      exact norm_add_le _ _
    _ = (Real.pi / Λ) * ‖s‖ * (‖Complex.log u‖ / 2 + 1) := by
      simp only [norm_div, norm_mul]
      norm_num
      field_simp [hu0.ne']
    _ ≤ 8 / 3 := by
      have hk : Real.pi / Λ ≤ 1 / 24 := (div_le_iff₀ hΛ0).2 (by nlinarith [Real.pi_pos])
      have hp1 := mul_le_mul_of_nonneg_right (pi_div_mul_le_of_le hΛ0 hlog) (norm_nonneg s)
      have hp2 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 19 * Real.pi / 24)
      have hk1 := mul_le_mul_of_nonneg_right hk (norm_nonneg s)
      have hk2 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (1 / 24 : ℝ))
      nlinarith [hp1, hp2, hk1, hk2, Real.pi_lt_d2]

/-- The first analytic derivative has a uniform scale-invariant bound on the
local arc. -/
theorem analyticPhaseDeriv_mul_localArc_norm_le_nine
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q ε y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖analyticPhaseDeriv d q (analyticLocalArc ε d q (y : ℂ))‖ *
        ‖analyticLocalArc ε d q (y : ℂ)‖ ≤ 9 := by
  let u := analyticLocalArc ε d q (y : ℂ)
  let r := saddleRadius d (saddleAngle d q)
  let Λ := scaleLambda d
  obtain ⟨hr, hr2⟩ : 0 < r ∧ r ≤ 2 := saddleRadius_pos_and_le_two_on_scale_window d hd hq
  have hΛ0 : 0 < Λ := scaleLambda_pos d hd
  have hu : ‖u‖ = r ^ 2 := norm_analyticLocalArc_real ε d q y
  have hu0 : 0 < ‖u‖ := by
    rw [hu]
    positivity
  have hs : ‖analyticLowerSqrt u‖ = r :=
    norm_analyticLowerSqrt_localArc d hd hq
  have hlog : ‖Complex.log u‖ ≤ (19 / 24 : ℝ) * Λ :=
    norm_log_analyticLocalArc_le_scaleLambda d hd hΛ hlarge hq
  have hqterm : q * ‖u‖ ≤ 2 := q_mul_norm_analyticLocalArc_le_two
    d hd (by linarith [Real.pi_pos]) hq
  have hq0 : 0 ≤ q := by
    have hα := saddle_inverse_on_scale_window d hd hq
    have hp := one_le_saddleQ_mul_radius_sq d hd ⟨hα.1.le, hα.2.1.le⟩
    rw [hα.2.2] at hp
    nlinarith [sq_nonneg r]
  let a : ℂ := (Real.pi : ℂ) * (analyticLowerSqrt u / (2 * u))
  let b : ℂ := ((Real.pi / Λ : ℝ) : ℂ) *
    ((analyticLowerSqrt u / (2 * u)) * Complex.log u +
      analyticLowerSqrt u / u)
  let c : ℂ := 1 / u
  have ha : ‖a‖ * ‖u‖ ≤ 16 / 5 := by
    dsimp [a]
    simp only [norm_mul, norm_div, Complex.norm_real]
    norm_num
    rw [hs]
    field_simp [hu0.ne']
    nlinarith [Real.pi_lt_d2]
  have hb : ‖b‖ * ‖u‖ ≤ 8 / 3 :=
    norm_pi_div_mul_sqrt_log_add_mul_le hΛ hu0 (hs.le.trans hr2) hlog
  have hc : ‖c‖ * ‖u‖ = 1 := by
    dsimp [c]
    rw [norm_div]
    norm_num
    exact inv_mul_cancel₀ hu0.ne'
  have ht : ‖(-(q : ℂ) + a + b) - c‖ ≤ q + ‖a‖ + ‖b‖ + ‖c‖ := by
    have h₁ := norm_sub_le (-(q : ℂ) + a + b) c
    have h₂ := norm_add_le (-(q : ℂ) + a) b
    have h₃ := norm_add_le (-(q : ℂ)) a
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hq0] at h₃
    linarith
  have hmul := mul_le_mul_of_nonneg_right ht (norm_nonneg u)
  rw [add_mul, add_mul, add_mul] at hmul
  rw [analyticPhaseDeriv]
  change ‖(-(q : ℂ) + a + b) - c‖ * ‖u‖ ≤ 9
  nlinarith [hmul]

/-- The dimensionless bracket in the normalized third derivative is bounded
by an absolute constant throughout the scale window. -/
theorem localThirdBracket_le_thirty
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q ε y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    localThirdBracket ε d q y ≤ 30 := by
  unfold localThirdBracket
  have h3 := analyticPhaseDeriv3_mul_localArc_norm_le_eight
    d hd hΛ hlarge (q := q) (ε := ε) (y := y) hq
  have h2 := analyticPhaseDeriv2_mul_localArc_norm_le_four
    d hd hΛ hlarge (q := q) (ε := ε) (y := y) hq
  have h1 := analyticPhaseDeriv_mul_localArc_norm_le_nine
    d hd hΛ hlarge (q := q) (ε := ε) (y := y) hq
  linarith

/-- For the fixed absolute width parameter `1/1000`, the normalized local
phase has third derivative at most `1/2` on the whole real local arc. -/
theorem analyticLocalPhaseThird_fixed_le_half
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    ‖analyticLocalPhaseThird (1 / 1000 : ℝ) d q (y : ℂ)‖ ≤
      (1 / 2 : ℝ) :=
  norm_analyticLocalPhaseThird_le_half_of_bracket_thirty d hd hΛ hq
    (localThirdBracket_le_thirty d hd hΛ hlarge hq)

/-- The fixed-width normalized phase derivative separates linearly from zero
on the normalized interval. -/
theorem analyticLocalPhaseFirst_fixed_norm_lower
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q y : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    (1 / 2 : ℝ) * |y| ≤
      ‖analyticLocalPhaseFirst (1 / 1000 : ℝ) d q (y : ℂ)‖ :=
  analyticLocalPhaseFirst_norm_lower d hd hq (by norm_num) (by norm_num)
    (saddleHessian_norm_pos_on_scale_window d hd hΛ hq)
    (fun _ _ => analyticLocalPhaseThird_fixed_le_half d hd hΛ hlarge hq) hy

end RiemannJensen
