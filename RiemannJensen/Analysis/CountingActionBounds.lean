module

public import RiemannJensen.Analysis.CountingPhaseCorrection
public import RiemannJensen.Analysis.EdgeQuadratic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Numerical saddle-action bounds on the counting window

Lower bounds for `saddleAction` at the tail endpoint `c₀ * scaleT d` of a counting window
(`countingWindow_tail_saddleAction_lower`), upper bounds at the edge endpoint
`edgeQ d + M * √(log d / d)` (`countingWindow_edge_saddleAction_upper`, via the quadratic
comparison `countingWindow_edge_saddleAngle_le_sqrt`), and the resulting lower bound on the
total phase span across the window (`countingWindow_totalPhase_span_lower`).
-/

@[expose] public section

namespace RiemannJensen

/-- On the scale window, the saddle action is at least `π - 12 * √2 / √q`. -/
theorem pi_sub_twelve_sqrt_two_div_sqrt_le_saddleAction
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    Real.pi - 12 * Real.sqrt 2 / Real.sqrt q ≤ saddleAction d q := by
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlarge2 : 2 * (1 + Real.log 2) ≤ scaleLambda d := by
    nlinarith [Real.two_le_pi]
  rcases saddle_inverse_on_scale_window d hd hq with ⟨ha, hb, -⟩
  have hr : 0 < saddleRadius d (saddleAngle d q) :=
    (saddleRadius_pos_and_eq d hd ⟨by linarith [Real.pi_pos], hb.le⟩).1
  have hrup := saddleRadius_le_sqrt_two_div_sqrt_on_scale_window
    d hd (by linarith [Real.pi_pos]) hq
  have hcosup := cos_le_pi_mul_radius_div_two d hd hlarge2 hq
  have hcos0 : 0 ≤ Real.cos (saddleAngle d q) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb.le⟩
  have hj := Real.mul_le_sin (x := Real.pi / 2 - saddleAngle d q) (by linarith) (by linarith)
  rw [Real.sin_pi_div_two_sub] at hj
  have hj' : 2 * (Real.pi / 2 - saddleAngle d q) ≤ Real.pi * Real.cos (saddleAngle d q) := by
    calc
      2 * (Real.pi / 2 - saddleAngle d q)
          = Real.pi * (2 / Real.pi * (Real.pi / 2 - saddleAngle d q)) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ Real.pi * Real.cos (saddleAngle d q) := by gcongr
  have hmain :
      2 * saddleAngle d q - Real.sin (2 * saddleAngle d q) ≤ saddleAction d q := by
    rw [saddleAction_eq_on_scale_window d hd hq]
    exact le_add_of_nonneg_right (mul_nonneg
      (div_nonneg (by positivity) (scaleLambda_pos d hd).le)
      (sub_nonneg.mpr (self_mul_cos_lt_sin ha hb.le).le))
  rw [Real.sin_two_mul] at hmain
  have hdiv : 12 * Real.sqrt 2 / Real.sqrt q = 12 * (Real.sqrt 2 / Real.sqrt q) := by ring
  nlinarith [mul_le_mul_of_nonneg_right (Real.sin_le_one (saddleAngle d q)) hcos0,
    mul_le_mul_of_nonneg_right Real.pi_div_two_le_two hr.le,
    mul_le_mul_of_nonneg_right Real.pi_div_two_le_two hcos0]

/-- At the tail endpoint `c₀ * scaleT d` of a nonempty counting window,
`π - 12 * √2 / √(c₀ * scaleT d) ≤ saddleAction d (c₀ * scaleT d)`. -/
theorem countingWindow_tail_saddleAction_lower
    (d : ℕ) (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty : edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d) :
    Real.pi - 12 * Real.sqrt 2 / Real.sqrt (c₀ * scaleT d) ≤
      saddleAction d (c₀ * scaleT d) :=
  pi_sub_twelve_sqrt_two_div_sqrt_le_saddleAction d (hd.trans' (by norm_num)) hΛ
    (countingWindow_subset_scale_window d hd hM hcsmall ⟨hnonempty, le_rfl⟩).1

/-- At the edge `edgeQ d + t` of a nonempty counting window, with `t = M * √(log d / d)`,
a bound `saddleAngle d (edgeQ d + t) ≤ C * √t` gives
`saddleAction d (edgeQ d + t) ≤ (3 / 2) * C ^ 3 * (√t) ^ 3`. -/
theorem countingWindow_edge_saddleAction_upper_of_saddleAngle_le_sqrt
    (d : ℕ) (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ C : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty : edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d)
    (hangle : saddleAngle d (edgeQ d + M * Real.sqrt (Real.log d / d)) ≤
      C * Real.sqrt (M * Real.sqrt (Real.log d / d))) :
    saddleAction d (edgeQ d + M * Real.sqrt (Real.log d / d)) ≤
      (3 / 2 : ℝ) * C ^ 3 * (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 := by
  rcases saddle_inverse_on_scale_window d (by omega)
    (countingWindow_subset_scale_window d hd hM hcsmall ⟨le_rfl, hnonempty⟩).1 with
    ⟨ha, hb, hinv⟩
  calc
    _ ≤ _ := hinv ▸ saddleAction_saddleQ_le_three_halves_cube d (by omega) hΛ ⟨ha.le, hb.le⟩
    _ ≤ (3 / 2 : ℝ) * (C * Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 := by gcongr
    _ = _ := by ring

/-- At the edge `edgeQ d + t` of a nonempty counting window, with `t = M * √(log d / d)`,
`saddleAngle d (edgeQ d + t) ≤ √50 * √t`. -/
theorem countingWindow_edge_saddleAngle_le_sqrt
    (d : ℕ) (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty : edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d) :
    saddleAngle d (edgeQ d + M * Real.sqrt (Real.log d / d)) ≤
      Real.sqrt 50 * Real.sqrt (M * Real.sqrt (Real.log d / d)) := by
  set t := M * Real.sqrt (Real.log d / d)
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  rcases saddle_inverse_on_scale_window d hd1
    (countingWindow_subset_scale_window d hd hM hcsmall ⟨le_rfl, hnonempty⟩).1 with
    ⟨ha, hb, hinv⟩
  have hquad := saddleQ_sub_edge_lower d hd1 hΛ ⟨ha.le, hb.le⟩
  rw [hinv] at hquad
  have hsq : (Real.sqrt 50 * Real.sqrt t) ^ 2 = 50 * t := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  nlinarith [show 0 ≤ Real.sqrt 50 * Real.sqrt t by positivity]

/-- At the edge `edgeQ d + t` of a nonempty counting window, with `t = M * √(log d / d)`,
`saddleAction d (edgeQ d + t) ≤ (3 / 2) * (√50) ^ 3 * (√t) ^ 3`. -/
theorem countingWindow_edge_saddleAction_upper
    (d : ℕ) (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty : edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d) :
    saddleAction d (edgeQ d + M * Real.sqrt (Real.log d / d)) ≤
      (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 * (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 :=
  countingWindow_edge_saddleAction_upper_of_saddleAngle_le_sqrt
    d hd hΛ hM hcsmall hnonempty
      (countingWindow_edge_saddleAngle_le_sqrt d hd hΛ hM hcsmall hnonempty)

/-- On a nonempty counting window, a bound `saddleAngle d (edgeQ d + t) ≤ C * √t`
(with `t = M * √(log d / d)`) makes the total phase increase from the edge to the tail
by at least `d * ((π - 12 * √2 / √(c₀ * scaleT d)) - (3 / 2) * C ^ 3 * (√t) ^ 3) - 16`. -/
theorem countingWindow_totalPhase_span_lower_of_edge_saddleAngle_le_sqrt
    (d : ℕ) (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ C : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty : edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d)
    (hangle : saddleAngle d (edgeQ d + M * Real.sqrt (Real.log d / d)) ≤
      C * Real.sqrt (M * Real.sqrt (Real.log d / d))) :
    (d : ℝ) * ((Real.pi - 12 * Real.sqrt 2 / Real.sqrt (c₀ * scaleT d)) -
        (3 / 2 : ℝ) * C ^ 3 * (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3) - 16 ≤
      ((d : ℝ) * saddleAction d (c₀ * scaleT d) + phaseCorrection d (c₀ * scaleT d)) -
        ((d : ℝ) * saddleAction d (edgeQ d + M * Real.sqrt (Real.log d / d)) +
          phaseCorrection d (edgeQ d + M * Real.sqrt (Real.log d / d))) :=
  countingWindow_totalPhase_span_lower_of_action_bounds
    d hd (four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ) (by linarith [Real.pi_pos])
    hM hcsmall hnonempty
    (countingWindow_edge_saddleAction_upper_of_saddleAngle_le_sqrt
      d hd hΛ hM hcsmall hnonempty hangle)
    (countingWindow_tail_saddleAction_lower d hd hΛ hM hcsmall hnonempty)

/-- On a nonempty counting window, with `t = M * √(log d / d)`, the total phase increases
from the edge to the tail by at least
`d * ((π - 12 * √2 / √(c₀ * scaleT d)) - (3 / 2) * (√50) ^ 3 * (√t) ^ 3) - 16`. -/
theorem countingWindow_totalPhase_span_lower
    (d : ℕ) (hd : 2 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {M c₀ : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112)
    (hnonempty : edgeQ d + M * Real.sqrt (Real.log d / d) ≤ c₀ * scaleT d) :
    (d : ℝ) * ((Real.pi - 12 * Real.sqrt 2 / Real.sqrt (c₀ * scaleT d)) -
        (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 * (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3) -
          16 ≤
      ((d : ℝ) * saddleAction d (c₀ * scaleT d) + phaseCorrection d (c₀ * scaleT d)) -
        ((d : ℝ) * saddleAction d (edgeQ d + M * Real.sqrt (Real.log d / d)) +
          phaseCorrection d (edgeQ d + M * Real.sqrt (Real.log d / d))) :=
  countingWindow_totalPhase_span_lower_of_action_bounds
    d hd (four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ) (by linarith [Real.pi_pos])
    hM hcsmall hnonempty (countingWindow_edge_saddleAction_upper d hd hΛ hM hcsmall hnonempty)
    (countingWindow_tail_saddleAction_lower d hd hΛ hM hcsmall hnonempty)

end RiemannJensen
