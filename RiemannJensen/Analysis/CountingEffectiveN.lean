module

public import RiemannJensen.Analysis.EffectiveNBounds
public import RiemannJensen.Analysis.CountingAmplitude
public import RiemannJensen.Analysis.CountingWindowEventually

/-! # Effective Gaussian size on the counting window -/

@[expose] public section

namespace RiemannJensen

/-- On `countingWindow M c₀ d`, `effectiveN ε d q` is at least the minimum of the edge bound
`(ε²/96) · d · τ · √τ` with `τ = M √(log d / d)` and the tail bound
`(ε²/3000) · d / (c₀ · scaleT d)`. -/
theorem effectiveN_countingWindow_lower (ε : ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hq : q ∈ countingWindow M c₀ d) :
    min ((ε ^ 2 / 96) * d * (M * Real.sqrt (Real.log d / d)) *
          Real.sqrt (M * Real.sqrt (Real.log d / d)))
        ((ε ^ 2 / 3000) * d / (c₀ * scaleT d)) ≤ effectiveN ε d q := by
  let τ := M * Real.sqrt (Real.log d / d)
  let t := q - edgeQ d
  let Q := c₀ * scaleT d
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hscale, hqtop⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith [hscale.1]
  have hτt : τ ≤ t := by
    dsimp [τ, t, countingWindow] at *
    linarith [hq.1]
  have hq0 : 0 < q := by
    obtain ⟨ha, hb, hinv⟩ := saddle_inverse_on_scale_window d hd1 hscale
    have hqr := one_le_saddleQ_mul_radius_sq d hd1 ⟨ha.le, hb.le⟩
    rw [hinv] at hqr
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (sq_nonneg (saddleRadius d (saddleAngle d q)))
    linarith
  have htail : (ε ^ 2 / 3000) * d / Q ≤ (ε ^ 2 / 3000) * d / q :=
    div_le_div_of_nonneg_left (by positivity) hq0 (by simpa [Q] using hqtop)
  have hedge : (ε ^ 2 / 96) * d * (τ * Real.sqrt τ) ≤
      (ε ^ 2 / 96) * d * (t * Real.sqrt t) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hτt (Real.sqrt_le_sqrt hτt) (Real.sqrt_nonneg τ) ht0) (by positivity)
  have hmin := min_le_min hedge htail
  have hwhole := effectiveN_scale_window_lower ε d hd1 hΛ
    (four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ) hscale
  dsimp [τ, t, Q] at hmin ⊢
  simpa only [mul_assoc] using
    hmin.trans (by simpa [mul_assoc] using hwhole)

/-- On `[0, 1]`, `x ≤ √x · √√x`. -/
theorem le_sqrt_mul_sqrt_sqrt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  have hs1 : Real.sqrt x ≤ 1 := by simpa using Real.sqrt_le_sqrt hx1
  have hs_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hxs : x ≤ Real.sqrt x := by nlinarith [Real.sqrt_nonneg x]
  nlinarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxs) (Real.sqrt_nonneg x)]

/-- Once `2 ≤ log d`, the tail scale `d / (eventualCountingC0 * scaleT d)` dominates `log d`. -/
theorem log_le_div_eventualCountingC0_mul_scaleT {d : ℕ} (hd1 : 1 ≤ d)
    (hlog2 : 2 ≤ Real.log (d : ℝ)) :
    Real.log (d : ℝ) ≤ d / (eventualCountingC0 * scaleT d) := by
  have hlogpos : 0 < Real.log (d : ℝ) := by linarith
  have hΛlog : Real.log (d : ℝ) / 2 ≤ scaleLambda d := by
    have hlower := log_nat_sub_one_le_scaleLambda d hd1
    nlinarith
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd1)
  have hprod := scaleT_mul_scaleLambda d hd1
  have hpi2 : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_pos, Real.pi_le_four]
  rw [eventualCountingC0]
  have hid :
      d / ((Real.pi / 224) * scaleT d) =
        56 * scaleLambda d / Real.pi ^ 2 := by
    field_simp [Real.pi_ne_zero, hT.ne']
    nlinarith
  rw [hid, le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
  have hmul := mul_le_mul_of_nonneg_left hpi2 hlogpos.le
  nlinarith

/-- For the fixed local width and fixed admissible upper-window constant, the effective parameter
is eventually bounded below by an explicit multiple of `log d` everywhere on the counting
window. -/
theorem eventually_effectiveN_countingWindow_log_lower_fixed :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∀ q ∈ countingWindow 1 eventualCountingC0 d,
        (((1 / 1000 : ℝ) ^ 2 / 3000) * Real.log d ≤
          effectiveN (1 / 1000 : ℝ) d q) := by
  have hlogtop : Filter.Tendsto
      (fun d : ℕ => Real.log (d : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_countingWindow_numerics 1 (by norm_num),
    Filter.tendsto_atTop.1 hlogtop 2] with d hn hlog2 q hq
  obtain ⟨hd, -, hcsmall, hΛ, -, -, -, hlogpos, hlogle, -⟩ := hn
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hwin := effectiveN_countingWindow_lower (1 / 1000 : ℝ) d hd hΛ
    (M := 1) (c₀ := eventualCountingC0)
    (by norm_num) hcsmall hq
  let x := Real.log (d : ℝ) / d
  have hdpos : (0 : ℝ) < d := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := (div_le_one hdpos).2 hlogle
  have hedge :
      (((1 / 1000 : ℝ) ^ 2 / 3000) * Real.log d) ≤
        ((1 / 1000 : ℝ) ^ 2 / 96) * d *
          (Real.sqrt (Real.log d / d)) *
          Real.sqrt (Real.sqrt (Real.log d / d)) := by
    have hm := mul_le_mul_of_nonneg_left (le_sqrt_mul_sqrt_sqrt hx0 hx1) hdpos.le
    dsimp [x] at hm
    field_simp [hdpos.ne'] at hm ⊢
    nlinarith [hlogpos]
  have htail : ((1 / 1000 : ℝ) ^ 2 / 3000) * Real.log d ≤
      ((1 / 1000 : ℝ) ^ 2 / 3000) * d / (eventualCountingC0 * scaleT d) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (log_le_div_eventualCountingC0_mul_scaleT hd1 hlog2) (by norm_num)
  exact (le_min hedge htail).trans (by simpa [mul_assoc] using hwin)

/-- There is a threshold `D` beyond which the effective Gaussian parameter is at least one
uniformly on the eventual counting window. -/
theorem exists_effectiveN_countingWindow_one_threshold :
    ∃ D : ℕ, ∀ d ≥ D, ∀ q ∈ countingWindow 1 eventualCountingC0 d,
      1 ≤ effectiveN (1 / 1000 : ℝ) d q := by
  have hlogtop : Filter.Tendsto
      (fun d : ℕ => Real.log (d : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rw [← Filter.eventually_atTop]
  filter_upwards [eventually_effectiveN_countingWindow_log_lower_fixed,
    Filter.tendsto_atTop.1 hlogtop 3000000000] with d heffective hlog q hq
  refine le_trans ?_ (heffective q hq)
  norm_num
  linarith

end RiemannJensen
