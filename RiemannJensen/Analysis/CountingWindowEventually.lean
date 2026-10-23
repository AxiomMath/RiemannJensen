module

public import RiemannJensen.Analysis.CountingActionBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Eventual numerical hypotheses for the counting window

We fix the constant `eventualCountingC0 = π / 224` and show that, for every
`M > 0`, the numerical hypotheses on the degree `d` needed for the counting window
`[edgeQ d + M √(log d / d), c₀ · scaleT d]` hold for all sufficiently large `d`.

## Main definitions

* `eventualCountingC0`: The constant `π / 224`.

## Main results

* `tendsto_scaleLambda_atTop`: `scaleLambda d` tends to infinity with `d`.
* `tendsto_scaleT_atTop`: `scaleT d` tends to infinity with `d`.
* `eventually_countingWindow_numerics`: The numerical hypotheses on `d` hold eventually.
* `eventually_countingWindow_nonempty_of`: For all `M, c₀ > 0`, eventually
  `edgeQ d + M √(log d / d) ≤ c₀ · scaleT d`.
* `exists_eventual_countingWindow_totalPhase_span_lower_of`: Eventual lower bound for the
  increase of the total phase across the counting window.
-/

@[expose] public section

namespace RiemannJensen

open Filter Set

/-- The constant `π / 224`. -/
noncomputable def eventualCountingC0 : ℝ := Real.pi / 224

/-- The constant `eventualCountingC0` is positive. -/
theorem eventualCountingC0_pos : 0 < eventualCountingC0 := by
  unfold eventualCountingC0
  positivity

/-- The constant `eventualCountingC0` is at most `π / 112`. -/
theorem eventualCountingC0_le : eventualCountingC0 ≤ Real.pi / 112 := by
  unfold eventualCountingC0
  linarith [Real.pi_pos]

/-- Once `Λ ≥ 2π`, the edge level is bounded by the absolute constant `2`. -/
theorem edgeQ_le_two (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 2 * Real.pi ≤ scaleLambda d) :
    edgeQ d ≤ 2 := by
  have hrpos := (saddleRadius_pos_and_eq d hd
    (show (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])).1
  have hinv1 : (saddleRadius d 0)⁻¹ ≤ 1 :=
    (inv_le_one₀ hrpos).2 (one_le_saddleRadius_zero d hd)
  have hΛpos := scaleLambda_pos d hd
  have hfrac : Real.pi / scaleLambda d ≤ 1 / 2 := by
    rw [div_le_iff₀ hΛpos]
    linarith
  rw [edgeQ, saddleQ, sinRatio_zero]
  nlinarith [sq_nonneg ((saddleRadius d 0)⁻¹), (inv_pos.2 hrpos).le,
    mul_le_mul hinv1 hfrac
      (div_nonneg Real.pi_pos.le hΛpos.le) (by norm_num : (0 : ℝ) ≤ 1)]

/-- The logarithmic scale tends to infinity with the degree. -/
theorem tendsto_scaleLambda_atTop :
    Tendsto (fun d : ℕ => scaleLambda d) atTop atTop := by
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_atTop.1 hlog (b + 1),
    eventually_ge_atTop (1 : ℕ)] with d hdlog hd
  have hlower := log_nat_sub_one_le_scaleLambda d hd
  linarith

/-- The gamma scale itself tends to infinity with the degree. -/
theorem tendsto_scaleT_atTop :
    Tendsto (fun d : ℕ => scaleT d) atTop atTop :=
  ((Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ 1
      (tendsto_scaleLambda_atTop.atTop_div_const two_pos))).const_mul_atTop
      (by positivity : 0 < 2 * Real.pi)).congr'
    ((eventually_ge_atTop 1).mono fun d hd => (scaleT_eq_exp_scaleLambda d hd).symm)

/-- For fixed `M > 0` and `c₀ > 0`, eventually
`edgeQ d + M √(log d / d) ≤ c₀ · scaleT d`. -/
theorem eventually_countingWindow_nonempty_of
    (M c₀ : ℝ) (hM : 0 < M) (hc₀ : 0 < c₀) :
    ∀ᶠ d : ℕ in atTop,
      edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d := by
  filter_upwards [
    tendsto_atTop.1 tendsto_scaleLambda_atTop (2 * Real.pi),
    tendsto_atTop.1 tendsto_scaleT_atTop ((2 + M) / c₀),
    eventually_ge_atTop (2 : ℕ)] with d hΛ hT hd
  have hdpos : (0 : ℝ) < d := by positivity
  have hratio : Real.log (d : ℝ) / d ≤ 1 :=
    (div_le_one hdpos).2 ((Real.log_le_sub_one_of_pos hdpos).trans (by linarith))
  have hsqrt : Real.sqrt (Real.log d / d) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hratio
  have hedge : edgeQ d ≤ 2 := edgeQ_le_two d (by omega) hΛ
  have hright : 2 + M ≤ c₀ * scaleT d := by
    simpa [mul_comm] using (div_le_iff₀ hc₀).1 hT
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hM.le]

/-- For fixed `M > 0`, the listed numerical inequalities on `d`, `scaleLambda d`,
`scaleT d` and the constant `eventualCountingC0` hold for all sufficiently large `d`. -/
theorem eventually_countingWindow_numerics (M : ℝ) (hM : 0 < M) :
    ∀ᶠ d : ℕ in atTop,
      2 ≤ d ∧
      0 < eventualCountingC0 ∧
      eventualCountingC0 ≤ Real.pi / 112 ∧
      24 * Real.pi ≤ scaleLambda d ∧
      4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d ∧
      40000 * eventualCountingC0 ≤ scaleT d ∧
      49 ≤ scaleT d ∧
      0 < Real.log (d : ℝ) ∧
      Real.log (d : ℝ) ≤ d ∧
      edgeQ d + M * Real.sqrt (Real.log d / d) ≤
        eventualCountingC0 * scaleT d := by
  filter_upwards [
    tendsto_atTop.1 tendsto_scaleLambda_atTop (24 * Real.pi),
    tendsto_atTop.1 tendsto_scaleT_atTop (40000 * eventualCountingC0),
    tendsto_atTop.1 tendsto_scaleT_atTop 49,
    eventually_countingWindow_nonempty_of M _ hM eventualCountingC0_pos,
    eventually_ge_atTop (2 : ℕ)] with d hΛ hT40000 hT49 hwin hd
  exact ⟨hd, eventualCountingC0_pos, eventualCountingC0_le,
    hΛ, four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ, hT40000, hT49,
    Real.log_pos (by exact_mod_cast hd),
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith), hwin⟩

/-- For fixed `M > 0` and `c₀ > 0`, there is a degree `D` such that for all `d ≥ D`,
`edgeQ d + M √(log d / d) ≤ c₀ · scaleT d`. -/
theorem exists_countingWindow_nonempty_threshold_of
    (M c₀ : ℝ) (hM : 0 < M) (hc₀ : 0 < c₀) :
    ∃ D : ℕ, ∀ d ≥ D,
      edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d :=
  eventually_atTop.1 (eventually_countingWindow_nonempty_of M c₀ hM hc₀)

/-- For fixed `M > 0` and `0 < c₀ ≤ π / 112`, for all sufficiently large `d` the total
phase `d · saddleAction d q + phaseCorrection d q` increases from
`q = edgeQ d + M √(log d / d)` to `q = c₀ · scaleT d` by at least the stated amount. -/
theorem exists_eventual_countingWindow_totalPhase_span_lower_of
    (M c₀ : ℝ) (hM : 0 < M) (hc₀ : 0 < c₀)
    (hcsmall : c₀ ≤ Real.pi / 112) :
    ∃ D : ℕ, ∀ d ≥ D,
      (d : ℝ) *
            ((Real.pi -
                12 * Real.sqrt 2 / Real.sqrt (c₀ * scaleT d)) -
              (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
                (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3) -
          16 ≤
        ((d : ℝ) * saddleAction d (c₀ * scaleT d) +
            phaseCorrection d (c₀ * scaleT d)) -
          ((d : ℝ) *
                saddleAction d
                  (edgeQ d + M * Real.sqrt (Real.log d / d)) +
            phaseCorrection d
              (edgeQ d + M * Real.sqrt (Real.log d / d))) := by
  refine eventually_atTop.1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_atTop.1 tendsto_scaleLambda_atTop (24 * Real.pi),
    eventually_countingWindow_nonempty_of M c₀ hM hc₀] with d hd hΛ hwin
  exact countingWindow_totalPhase_span_lower d hd hΛ hM hcsmall hwin

end RiemannJensen
