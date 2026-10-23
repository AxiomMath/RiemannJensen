module

public import RiemannJensen.Analysis.CountingWholeWindow
public import RiemannJensen.Analysis.CountingEffectiveN
public import RiemannJensen.Analysis.XiThetaMoments

/-!
# Eventual lower-contour estimate and oscillatory formula

For all large `d`, uniformly on a fixed counting window, the lower-contour
contribution is the leading saddle term up to a relative error
`K₀ n^{-1/10} + C d e^{-c d m(q)}` with `m(q) = min((q - q_edge)², q⁻¹)`, and the
reciprocal Jensen polynomial at `-q` is `2 Re Z_d(q)` up to twice that.

With the window constants `M = 1`, `c₀ = eventualCountingC0` the remote term
`d e^{-c d m(q)}` need not tend to zero, because `c` is tiny: at the lower end
`m(q) = log d / d` and the term is `d^{1 - c}`.  For the simplified
`O(|Z| (log d)^{-1/10})` form we therefore use the constants
`oscillationM = √(4 / c)` and `oscillationC0 = c / (32 π)`, for which the
remote term is at most `d^{-3}`.

## Main definitions

* `oscillationM`: The edge constant `√(4 / c)` of the oscillation window.
* `oscillationC0`: The upper constant `c / (32 π)` of the oscillation window.

## Main results

* `exists_eventually_countingWindow_lowerContribution_of`: The eventual lower-contour estimate
  on a fixed counting window.
* `exists_eventually_lowerContribution_log`: The lower-contour estimate with relative error
  `O((log d)^{-1/10})` on the oscillation window.
* `exists_eventually_oscillation`: The oscillatory formula
  `A_d(-q) = 2 Re Z_d(q) + O(|Z_d(q)| (log d)^{-1/10})` on the oscillation window.
-/

@[expose] public section

namespace RiemannJensen

open Filter

/-- The relative-error constant of the local window estimate for the phase data
at the fixed width `ε = 1/1000`. -/
noncomputable def lowerRelConst : ℝ :=
  windowRelConst (1 / 2) (max (4 + 8 * 2 * zetaLogDerivMajorant) (3 / 2))

/-- The constant `lowerRelConst` is nonnegative. -/
theorem lowerRelConst_nonneg : 0 ≤ lowerRelConst := by
  have hC : (0 : ℝ) < max (4 + 8 * 2 * zetaLogDerivMajorant) (3 / 2) :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  unfold lowerRelConst windowRelConst gaussianErrorConst
  positivity

/-- The remote-gap exponent `c = ε² · remoteGapConst 6` at `ε = 1/1000`. -/
noncomputable def remoteExpConst : ℝ :=
  (1 / 1000 : ℝ) ^ 2 * remoteGapConst 6

/-- The remote-gap exponent `remoteExpConst` is positive. -/
theorem remoteExpConst_pos : 0 < remoteExpConst := by
  have := remoteGapConst_pos 6
  unfold remoteExpConst
  positivity

/-- The remote-gap exponent `remoteExpConst` is at most `1`. -/
theorem remoteExpConst_le_one : remoteExpConst ≤ 1 := by
  have hden : 1 ≤ 2048 * Real.pi ^ 4 * max ((6 : ℝ) ^ 2) 1 := by
    nlinarith [one_le_pow₀ (n := 4) (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi),
      (le_max_right _ _ : (1 : ℝ) ≤ max ((6 : ℝ) ^ 2) 1)]
  have hg : remoteGapConst 6 ≤ 3 := by
    unfold remoteGapConst
    exact div_le_self (by norm_num) hden
  unfold remoteExpConst
  nlinarith [remoteGapConst_pos 6]

/-- The edge constant of the oscillation window: `c M² = 4`. -/
noncomputable def oscillationM : ℝ := Real.sqrt (4 / remoteExpConst)

/-- The upper constant of the oscillation window: `c₀ = c / (32 π)`. -/
noncomputable def oscillationC0 : ℝ := remoteExpConst / (32 * Real.pi)

/-- `oscillationM ^ 2 = 4 / remoteExpConst`. -/
theorem oscillationM_sq : oscillationM ^ 2 = 4 / remoteExpConst := by
  unfold oscillationM
  exact Real.sq_sqrt (div_nonneg (by norm_num) remoteExpConst_pos.le)

/-- The edge constant `oscillationM` is at least `1`. -/
theorem one_le_oscillationM : 1 ≤ oscillationM := by
  unfold oscillationM
  rw [Real.one_le_sqrt, le_div_iff₀ remoteExpConst_pos]
  linarith [remoteExpConst_le_one]

/-- The upper constant `oscillationC0` is positive. -/
theorem oscillationC0_pos : 0 < oscillationC0 := by
  have := remoteExpConst_pos
  unfold oscillationC0
  positivity

/-- The upper constant `oscillationC0` is at most `π / 224`. -/
theorem oscillationC0_le : oscillationC0 ≤ Real.pi / 224 := by
  have hc := remoteExpConst_le_one
  have hpi := Real.pi_gt_three
  unfold oscillationC0
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- For `d ≥ 1`, the edge point `edgeQ d` is nonnegative. -/
theorem edgeQ_nonneg (d : ℕ) (hd : 1 ≤ d) : 0 ≤ edgeQ d := by
  have hrpos := (saddleRadius_pos_and_eq d hd
    (show (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])).1
  have hΛ := scaleLambda_pos d hd
  rw [edgeQ, saddleQ, sinRatio_zero]
  have := Real.pi_pos
  positivity

/-- The logarithm of the natural numbers tends to infinity. -/
theorem tendsto_log_natCast_atTop :
    Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- For `d ≥ 1` with `2 ≤ log d`, `log d ≤ 2 Λ_d`. -/
theorem log_le_two_mul_scaleLambda {d : ℕ} (hd : 1 ≤ d) (hlog : 2 ≤ Real.log (d : ℝ)) :
    Real.log (d : ℝ) ≤ 2 * scaleLambda d := by
  linarith [log_nat_sub_one_le_scaleLambda d hd]

/-- For `0 ≤ x ≤ 1` and `1 ≤ M`, `x ≤ (M √x) √(M √x)`. -/
theorem le_mul_sqrt_mul_sqrt_sqrt {x M : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hM : 1 ≤ M) :
    x ≤ (M * Real.sqrt x) * Real.sqrt (M * Real.sqrt x) := by
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs1 : Real.sqrt x ≤ 1 := by simpa using Real.sqrt_le_sqrt hx1
  have hxs : x ≤ Real.sqrt x := by nlinarith [Real.sq_sqrt hx0]
  have hMs : Real.sqrt x ≤ M * Real.sqrt x := by nlinarith
  calc x ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) := by
        nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxs) hs0, Real.sq_sqrt hx0]
    _ ≤ _ := mul_le_mul hMs (Real.sqrt_le_sqrt hMs) (Real.sqrt_nonneg _) (by positivity)

/-- If `0 < d` and `4 log d ≤ t`, then `exp (-t) ≤ (d ^ 4)⁻¹`. -/
theorem exp_neg_le_inv_pow_four {d t : ℝ} (hd : 0 < d) (h : 4 * Real.log d ≤ t) :
    Real.exp (-t) ≤ (d ^ 4)⁻¹ := by
  rw [← Real.exp_log (pow_pos hd 4), ← Real.exp_neg, Real.log_pow]
  exact Real.exp_le_exp.2 (by push_cast; linarith)

/-- For `d ≥ 1` with `2 ≤ log d` and `0 < c₀` with `8 π c₀ ≤ 1`, `log d ≤ d / (c₀ T_d)`. -/
theorem log_le_div_mul_scaleT {d : ℕ} {c₀ : ℝ} (hd : 1 ≤ d) (hlog : 2 ≤ Real.log (d : ℝ))
    (hc₀ : 0 < c₀) (h8 : 8 * Real.pi * c₀ ≤ 1) :
    Real.log (d : ℝ) ≤ d / (c₀ * scaleT d) := by
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd)
  have hprod := scaleT_mul_scaleLambda d hd
  rw [le_div_iff₀ (by positivity)]
  have h1 : Real.log d * (c₀ * scaleT d) ≤ 2 * scaleLambda d * (c₀ * scaleT d) :=
    mul_le_mul_of_nonneg_right (log_le_two_mul_scaleLambda hd hlog) (by positivity)
  have h2 : 2 * scaleLambda d * (c₀ * scaleT d) = 8 * Real.pi * c₀ * d := by
    linear_combination (2 * c₀) * hprod
  nlinarith [mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- For `d ≥ 1` with `2 ≤ log d` and `0 < q ≤ oscillationC0 · T_d`, `4 log d ≤ d c q⁻¹`. -/
theorem four_log_le_mul_remoteExpConst_inv {d : ℕ} {q : ℝ} (hd : 1 ≤ d)
    (hlog : 2 ≤ Real.log (d : ℝ)) (hq0 : 0 < q) (hq : q ≤ oscillationC0 * scaleT d) :
    4 * Real.log d ≤ d * (remoteExpConst * q⁻¹) := by
  have hc := remoteExpConst_pos
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd)
  have hprod := scaleT_mul_scaleLambda d hd
  have hval : d * (remoteExpConst * (oscillationC0 * scaleT d)⁻¹) = 8 * scaleLambda d := by
    rw [oscillationC0]
    field_simp
    linear_combination (-8 : ℝ) * hprod
  have hmono : d * (remoteExpConst * (oscillationC0 * scaleT d)⁻¹) ≤
      d * (remoteExpConst * q⁻¹) := by gcongr
  linarith [log_le_two_mul_scaleLambda hd hlog]

/-- For a fixed edge constant `M ≥ 1` and upper constant `0 < c₀ ≤ π/224`, the
effective parameter is eventually at least `(ε²/3000) log d` on the whole
counting window, at `ε = 1/1000`. -/
theorem eventually_effectiveN_countingWindow_log_lower_of
    {M c₀ : ℝ} (hM : 1 ≤ M) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ Real.pi / 224) :
    ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow M c₀ d,
        ((1 / 1000 : ℝ) ^ 2 / 3000) * Real.log d ≤
          effectiveN (1 / 1000 : ℝ) d q := by
  filter_upwards [tendsto_atTop.1 tendsto_scaleLambda_atTop (24 * Real.pi),
    tendsto_atTop.1 tendsto_log_natCast_atTop 2, eventually_ge_atTop (2 : ℕ)]
    with d hΛ hlog2 hd
  intro q hq
  have hdpos : (0 : ℝ) < d := by positivity
  set x := Real.log (d : ℝ) / d with hxdef
  have hedge :
      ((1 / 1000 : ℝ) ^ 2 / 3000) * Real.log d ≤
        ((1 / 1000 : ℝ) ^ 2 / 96) * d *
          (M * Real.sqrt x) * Real.sqrt (M * Real.sqrt x) := by
    have hdx : (d : ℝ) * x = Real.log d := by
      rw [hxdef]
      field_simp
    have hm := mul_le_mul_of_nonneg_left
      (le_mul_sqrt_mul_sqrt_sqrt (by positivity)
        ((div_le_one hdpos).2 ((Real.log_le_sub_one_of_pos hdpos).trans (by linarith))) hM)
      (by positivity : (0 : ℝ) ≤ ((1 / 1000 : ℝ) ^ 2 / 96) * d)
    nlinarith [Real.log_pos (show (1 : ℝ) < d by exact_mod_cast hd)]
  have htail :
      ((1 / 1000 : ℝ) ^ 2 / 3000) * Real.log d ≤
        ((1 / 1000 : ℝ) ^ 2 / 3000) * d / (c₀ * scaleT d) := by
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (log_le_div_mul_scaleT (by omega) hlog2 hc₀ (by nlinarith [Real.pi_pos, Real.pi_le_four]))
      (by norm_num : (0 : ℝ) ≤ (1 / 1000 : ℝ) ^ 2 / 3000)
  exact (le_min hedge htail).trans
    (effectiveN_countingWindow_lower (1 / 1000 : ℝ) d hd hΛ (by linarith)
      (by linarith [Real.pi_pos]) hq)

/-- For all large `d`, uniformly on the counting window with the oscillation constants,
`d e^{-c d m(q)} ≤ d^{-3}`. -/
theorem eventually_remote_error_oscillation :
    ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow oscillationM oscillationC0 d,
        (d : ℝ) * Real.exp (-(d * (remoteExpConst *
            min ((q - edgeQ d) ^ 2) q⁻¹))) ≤ 1 / (d : ℝ) ^ 3 := by
  filter_upwards [tendsto_atTop.1 tendsto_log_natCast_atTop 2, eventually_ge_atTop (2 : ℕ)]
    with d hlog2 hd
  intro q hq
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hdpos : (0 : ℝ) < d := by positivity
  have hc := remoteExpConst_pos
  have hMpos : 0 < oscillationM := one_pos.trans_le one_le_oscillationM
  set x := Real.log (d : ℝ) / d with hxdef
  have hx0 : 0 < x := div_pos (Real.log_pos (by exact_mod_cast hd)) hdpos
  have ht : oscillationM * Real.sqrt x ≤ q - edgeQ d := by linarith [hq.1]
  have hq0 : 0 < q := by nlinarith [mul_pos hMpos (Real.sqrt_pos.2 hx0), edgeQ_nonneg d hd1]
  have hA : 4 * Real.log d ≤ d * (remoteExpConst * (q - edgeQ d) ^ 2) := by
    have hval : (oscillationM * Real.sqrt x) ^ 2 = 4 / remoteExpConst * x := by
      rw [mul_pow, oscillationM_sq, Real.sq_sqrt hx0.le]
    have hval2 : d * (remoteExpConst * (4 / remoteExpConst * x)) =
        4 * Real.log d := by
      rw [hxdef]
      field_simp
    rw [← hval2, ← hval]
    gcongr
  have hmin : 4 * Real.log d ≤
      d * (remoteExpConst * min ((q - edgeQ d) ^ 2) q⁻¹) := by
    rw [mul_min_of_nonneg _ _ hc.le, mul_min_of_nonneg _ _ hdpos.le]
    exact le_min hA (four_log_le_mul_remoteExpConst_inv hd1 hlog2 hq0 hq.2)
  exact (mul_le_mul_of_nonneg_left (exp_neg_le_inv_pow_four hdpos hmin) hdpos.le).trans_eq
    (by field_simp)

/-- If `0 < a`, `0 < L` and `a L ≤ n`, then `n^{-1/10} ≤ a^{-1/10} L^{-1/10}`. -/
theorem rpow_neg_tenth_le_of_mul_le {a L n : ℝ} (ha : 0 < a) (hL : 0 < L)
    (h : a * L ≤ n) :
    n ^ (-(1:ℝ)/10) ≤ a ^ (-(1:ℝ)/10) * L ^ (-(1:ℝ)/10) := by
  rw [← Real.mul_rpow ha.le hL.le]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) h (by norm_num)

/-- `d^{-3} ≤ (log d)^{-1/10}` once `log d ≥ 1`. -/
theorem one_div_cube_le_log_rpow {d : ℕ} (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log (d : ℝ)) :
    1 / (d : ℝ) ^ 3 ≤ Real.log (d : ℝ) ^ (-(1:ℝ)/10) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have h1 : Real.log (d : ℝ) ^ (-(1:ℝ)) ≤ Real.log (d : ℝ) ^ (-(1:ℝ)/10) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have hlogle : Real.log (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    linarith [Real.log_le_sub_one_of_pos hdpos, le_self_pow₀ hdR (show 3 ≠ 0 by norm_num)]
  exact (one_div_le_one_div_of_le (by linarith) hlogle).trans ((one_div _).le.trans h1)

/-- For `M ≥ 1` and `0 < c₀ ≤ π/224`, eventually `d ≥ 2`, `Λ_d ≥ 24π`, `T_d ≥ 40000 c₀`, and
`n_{1/1000} ≥ 1` on the counting window. -/
theorem eventually_countingWindow_estimate_hyps
    {M c₀ : ℝ} (hM : 1 ≤ M) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ Real.pi / 224) :
    ∀ᶠ d : ℕ in atTop,
      2 ≤ d ∧ 24 * Real.pi ≤ scaleLambda d ∧ 40000 * c₀ ≤ scaleT d ∧
        ∀ q ∈ countingWindow M c₀ d, 1 ≤ effectiveN (1 / 1000) d q := by
  filter_upwards [eventually_effectiveN_countingWindow_log_lower_of hM hc₀ hc₀le,
    tendsto_atTop.1 tendsto_scaleLambda_atTop (24 * Real.pi),
    tendsto_atTop.1 tendsto_scaleT_atTop (40000 * c₀),
    tendsto_atTop.1 tendsto_log_natCast_atTop 3000000000, eventually_ge_atTop (2 : ℕ)]
    with d hn hΛ hT hlog hd
  refine ⟨hd, hΛ, hT, fun q hq => le_trans ?_ (hn q hq)⟩
  norm_num
  linarith

/-- **Lower-contour estimate**, eventual form for fixed `M ≥ 1`, `0 < c₀ ≤ π/224`: for all
large `d`, uniformly on `I_d`, `L_d(q) = Z_d(q)(1 + O(n^{-1/10}) + O(d e^{-c d m(q)}))`. -/
theorem exists_eventually_countingWindow_lowerContribution_of
    {M c₀ : ℝ} (hM : 1 ≤ M) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ Real.pi / 224) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow M c₀ d,
        ‖lowerContribution d q - leadingSaddle d q‖ ≤
          ‖leadingSaddle d q‖ *
            (lowerRelConst * effectiveN (1 / 1000) d q ^ (-(1:ℝ)/10) +
              C * d * Real.exp (-(d * (remoteExpConst *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_lowerContribution_estimate_fixedWidth
  refine ⟨Real.pi * C * Real.sqrt (2 * Real.pi * 4), by positivity, ?_⟩
  filter_upwards [eventually_countingWindow_estimate_hyps hM hc₀ hc₀le]
    with d ⟨hd, hΛ, hT, hn⟩
  intro q hq
  exact hest hd hΛ (by linarith) hc₀ (by linarith [Real.pi_pos]) hT hq (hn q hq)

/-- **Oscillatory formula**, eventual un-simplified form for fixed `M ≥ 1`, `0 < c₀ ≤ π/224`:
for all large `d`, uniformly on `I_d`, `A_d(-q) = 2 Re Z_d(q)` up to
`2 |Z_d(q)| (O(n^{-1/10}) + O(d e^{-c d m(q)}))`. -/
theorem exists_eventually_countingWindow_rescaledJensen_eval_of
    {M c₀ : ℝ} (hM : 1 ≤ M) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ Real.pi / 224) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow M c₀ d,
        |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
          2 * ‖leadingSaddle d q‖ *
            (lowerRelConst * effectiveN (1 / 1000) d q ^ (-(1:ℝ)/10) +
              C * d * Real.exp (-(d * (remoteExpConst *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_rescaledJensen_eval_fixedWidth
  refine ⟨Real.pi * C * Real.sqrt (2 * Real.pi * 4), by positivity, ?_⟩
  filter_upwards [eventually_countingWindow_estimate_hyps hM hc₀ hc₀le]
    with d ⟨hd, hΛ, hT, hn⟩
  intro q hq
  exact hest hd (gammaCoeff_pos d).ne' hΛ (by linarith) hc₀
    (by linarith [Real.pi_pos]) hT hq (hn q hq)

/-- On the oscillation window, for all large `d`, the relative error
`K₀ n^{-1/10} + C d e^{-c d m(q)}` is at most `(K₀ a^{-1/10} + C) (log d)^{-1/10}`
with `a = ε²/3000` at `ε = 1/1000`. -/
theorem eventually_oscillation_error_le_log_rpow {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow oscillationM oscillationC0 d,
        lowerRelConst * effectiveN (1 / 1000) d q ^ (-(1:ℝ)/10) +
            C * d * Real.exp (-(d * (remoteExpConst * min ((q - edgeQ d) ^ 2) q⁻¹))) ≤
          (lowerRelConst * ((1 / 1000 : ℝ) ^ 2 / 3000) ^ (-(1:ℝ)/10) + C) *
            Real.log d ^ (-(1:ℝ)/10) := by
  filter_upwards [eventually_effectiveN_countingWindow_log_lower_of
      one_le_oscillationM oscillationC0_pos oscillationC0_le,
    eventually_remote_error_oscillation, tendsto_atTop.1 tendsto_log_natCast_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with d hn hrem hlog hd
  intro q hq
  have hn' := rpow_neg_tenth_le_of_mul_le (by norm_num) (by linarith) (hn q hq)
  have hr := (hrem q hq).trans (one_div_cube_le_log_rpow hd hlog)
  rw [mul_assoc C]
  nlinarith [mul_le_mul_of_nonneg_left hn' lowerRelConst_nonneg, mul_le_mul_of_nonneg_left hr hC]

/-- **Lower-contour estimate**, simplified: on the oscillation window,
`L_d(q) = Z_d(q)(1 + O((log d)^{-1/10}))` uniformly for all large `d`. -/
theorem exists_eventually_lowerContribution_log :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow oscillationM oscillationC0 d,
        ‖lowerContribution d q - leadingSaddle d q‖ ≤
          C * ‖leadingSaddle d q‖ * Real.log d ^ (-(1:ℝ)/10) := by
  obtain ⟨C, hC, hev⟩ := exists_eventually_countingWindow_lowerContribution_of
    one_le_oscillationM oscillationC0_pos oscillationC0_le
  have hK := lowerRelConst_nonneg
  refine ⟨lowerRelConst * ((1 / 1000 : ℝ) ^ 2 / 3000) ^ (-(1:ℝ)/10) + C, by positivity, ?_⟩
  filter_upwards [hev, eventually_oscillation_error_le_log_rpow hC.le] with d h1 hsum q hq
  exact (h1 q hq).trans
    ((mul_le_mul_of_nonneg_left (hsum q hq) (norm_nonneg _)).trans_eq (by ring))

/-- **Oscillatory formula**: for all large `d`, uniformly on the counting window with the
oscillation constants, `A_d(-q) = 2 Re Z_d(q) + O(|Z_d(q)| (log d)^{-1/10})`. -/
theorem exists_eventually_oscillation :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ countingWindow oscillationM oscillationC0 d,
        |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
          C * ‖leadingSaddle d q‖ * Real.log d ^ (-(1:ℝ)/10) := by
  obtain ⟨C, hC, hev⟩ := exists_eventually_countingWindow_rescaledJensen_eval_of
    one_le_oscillationM oscillationC0_pos oscillationC0_le
  have hK := lowerRelConst_nonneg
  refine ⟨2 * (lowerRelConst * ((1 / 1000 : ℝ) ^ 2 / 3000) ^ (-(1:ℝ)/10) + C),
    by positivity, ?_⟩
  filter_upwards [hev, eventually_oscillation_error_le_log_rpow hC.le] with d h1 hsum q hq
  exact (h1 q hq).trans ((mul_le_mul_of_nonneg_left (hsum q hq)
    (by positivity : (0 : ℝ) ≤ 2 * ‖leadingSaddle d q‖)).trans_eq (by ring))

end RiemannJensen
