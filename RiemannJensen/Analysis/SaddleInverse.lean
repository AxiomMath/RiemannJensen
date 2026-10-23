module

public import RiemannJensen.Analysis.SaddleGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Endpoint and inversion of the saddle branch

This file records the exact right endpoint of the radial saddle, proves that
the corresponding `q`-endpoint reaches the gamma scale, and develops the
continuity needed to invert the complete saddle branch.
-/

@[expose] public section

namespace RiemannJensen

open Set Filter
open scoped Topology

/-- The continuous quotient used in `saddleQ` is the reciprocal of `sinc`. -/
theorem sinRatio_eq_inv_sinc (x : ℝ) :
    sinRatio x = (Real.sinc x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [sinRatio_of_ne hx, Real.sinc_of_ne_zero hx]
    field_simp

/-- The sine ratio is continuous on the complete saddle interval. -/
theorem continuousOn_sinRatio :
    ContinuousOn sinRatio (Set.Icc 0 (Real.pi / 2)) := by
  rw [show sinRatio = fun x => (Real.sinc x)⁻¹ from funext sinRatio_eq_inv_sinc]
  apply Real.continuous_sinc.continuousOn.fun_inv₀
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hxpos
  · simp
  · rw [Real.sinc_of_ne_zero hxpos.ne']
    exact (div_pos
      (Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2, Real.pi_pos]))
      hxpos).ne'

/-- The function `alphaCot` is continuous on `[0, π / 2]`. -/
theorem continuousOn_alphaCot :
    ContinuousOn alphaCot (Set.Icc 0 (Real.pi / 2)) := by
  have hid : alphaCot = fun x => sinRatio x * Real.cos x := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [alphaCot_of_ne hx, sinRatio_of_ne hx]
      ring
  rw [hid]
  exact continuousOn_sinRatio.mul Real.continuous_cos.continuousOn

/-- At the right endpoint `π / 2`, the saddle radius equals `2 * π / scaleT d`. -/
theorem saddleRadius_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    saddleRadius d (Real.pi / 2) = 2 * Real.pi / scaleT d := by
  apply saddleRadius_eq_of_radialEquation d
      (saddleRadialCoeff_nonneg d hd (by
        constructor <;> linarith [Real.pi_pos]))
  · exact div_pos (mul_pos (by norm_num) Real.pi_pos)
      (lt_trans (by positivity) (scaleT_gt_base d hd))
  · have hT : 0 < scaleT d :=
      lt_trans (by positivity) (scaleT_gt_base d hd)
    have hlog :
        Real.log (2 * Real.pi / scaleT d) =
          -(scaleLambda d / 2) - 1 := by
      rw [show 2 * Real.pi / scaleT d =
          (scaleT d / (2 * Real.pi))⁻¹ by field_simp]
      rw [Real.log_inv, scaleLambda_div_two]
      ring
    rw [radialEquation, saddleRadialCoeff, saddleRadialConst, Real.cos_pi_div_two,
      alphaCot_of_ne (by positivity : Real.pi / 2 ≠ 0), Real.cos_pi_div_two,
      Real.sin_pi_div_two, hlog]
    field_simp
    ring

/-- Exact formula for the `q`-coordinate at the right endpoint. -/
theorem saddleQ_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    saddleQ d (Real.pi / 2) =
      (scaleT d / (2 * Real.pi)) ^ 2 +
        (Real.pi / scaleLambda d) * (Real.pi / 2) *
          (scaleT d / (2 * Real.pi)) := by
  rw [saddleQ, saddleRadius_pi_div_two d hd,
    sinRatio_of_ne (by positivity : Real.pi / 2 ≠ 0), Real.sin_pi_div_two]
  have hT : scaleT d ≠ 0 :=
    (lt_trans (by positivity) (scaleT_gt_base d hd)).ne'
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- For `1 ≤ d`, `4 * (scaleLambda d / 2) < scaleT d / (2 * π)`. -/
theorem four_mul_scaleLambda_div_two_lt_scale_ratio
    (d : ℕ) (hd : 1 ≤ d) :
    4 * (scaleLambda d / 2) < scaleT d / (2 * Real.pi) := by
  have hx : 0 < scaleT d / (2 * Real.pi) :=
    div_pos (lt_trans (by positivity) (scaleT_gt_base d hd)) (by positivity)
  have hlog4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hbase := Real.log_le_sub_one_of_pos (div_pos hx four_pos)
  rw [scaleLambda_div_two, ← div_mul_cancel₀ (scaleT d / (2 * Real.pi)) four_ne_zero,
    Real.log_mul (by positivity) four_ne_zero]
  linarith

/-- The right endpoint of the saddle branch lies beyond `scaleT`. -/
theorem scaleT_lt_saddleQ_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    scaleT d < saddleQ d (Real.pi / 2) := by
  rw [saddleQ_pi_div_two d hd]
  let x := scaleT d / (2 * Real.pi)
  let L := scaleLambda d / 2
  have hx : 0 < x := div_pos (lt_trans (by positivity) (scaleT_gt_base d hd)) (by positivity)
  have hL : 0 < L := half_pos (scaleLambda_pos d hd)
  have hcomp : 4 * L < x := by
    simpa [x, L] using four_mul_scaleLambda_div_two_lt_scale_ratio d hd
  have hpi : 0 < Real.pi := Real.pi_pos
  have hΛ : scaleLambda d = 2 * L := by
    dsimp [L]
    ring
  have hT : scaleT d = 2 * Real.pi * x := by
    dsimp [x]
    field_simp
  rw [hΛ, hT]
  have hamgm : 2 * Real.pi * x < x ^ 2 + Real.pi ^ 2 * x / (4 * L) := by
    have hfrac : Real.pi ^ 2 < Real.pi ^ 2 * x / (4 * L) := by
      rw [lt_div_iff₀ (by positivity : 0 < 4 * L)]
      nlinarith [sq_pos_of_pos Real.pi_pos]
    nlinarith [sq_nonneg (x - Real.pi)]
  convert hamgm using 1; field_simp; ring

/-- The reciprocal coefficient varies continuously with the angle. -/
theorem continuousOn_saddleRadialCoeff (d : ℕ) :
    ContinuousOn (saddleRadialCoeff d) (Set.Icc 0 (Real.pi / 2)) := by
  unfold saddleRadialCoeff
  fun_prop

/-- The constant coefficient in the radial equation varies continuously with
its angle, including at the removable endpoint. -/
theorem continuousOn_saddleRadialConst (d : ℕ) :
    ContinuousOn (saddleRadialConst d) (Set.Icc 0 (Real.pi / 2)) := by
  unfold saddleRadialConst
  exact (continuousOn_alphaCot.sub continuousOn_const).sub continuousOn_const

/-- For fixed `r`, the radial equation of the saddle varies continuously with
its angle. -/
theorem continuousOn_radialEquation_saddle (d : ℕ) (r : ℝ) :
    ContinuousOn (fun β => radialEquation (saddleRadialCoeff d β) (saddleRadialConst d β) r)
      (Set.Icc 0 (Real.pi / 2)) := by
  unfold radialEquation
  exact (((continuousOn_saddleRadialCoeff d).div_const r).add
    (continuousOn_saddleRadialConst d)).sub continuousOn_const

/-- A point where the radial equation is positive lies below its root. -/
theorem lt_of_radialEquation_pos {A B lo r : ℝ} (hA : 0 ≤ A) (hlo : 0 < lo) (hr : 0 < r)
    (hroot : radialEquation A B r = 0) (hpos : 0 < radialEquation A B lo) : lo < r := by
  by_contra hn
  rcases (not_lt.1 hn).eq_or_lt with rfl | hlt
  · linarith
  · linarith [radialEquation_strictAntiOn (B := B) hA hr hlo hlt]

/-- A point where the radial equation is negative lies above its root. -/
theorem lt_of_radialEquation_neg {A B hi r : ℝ} (hA : 0 ≤ A) (hhi : 0 < hi) (hr : 0 < r)
    (hroot : radialEquation A B r = 0) (hneg : radialEquation A B hi < 0) : r < hi := by
  by_contra hn
  rcases (not_lt.1 hn).eq_or_lt with rfl | hlt
  · linarith
  · linarith [radialEquation_strictAntiOn (B := B) hA hhi hr hlt]

/-- Continuity of the positive root of the radial equation along the full
closed saddle interval. -/
theorem continuousOn_saddleRadius (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (saddleRadius d) (Set.Icc 0 (Real.pi / 2)) := by
  intro α hα
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  obtain ⟨hr₀, hr₀eq⟩ := saddleRadius_pos_and_eq d hd hαfull
  set r₀ := saddleRadius d α
  obtain ⟨e, he, heε, her⟩ : ∃ e, 0 < e ∧ e < ε ∧ e < r₀ :=
    ⟨min (ε / 2) (r₀ / 2), lt_min (half_pos hε) (half_pos hr₀),
      min_lt_of_left_lt (half_lt_self hε), min_lt_of_right_lt (half_lt_self hr₀)⟩
  have hlo : 0 < r₀ - e := by linarith
  have hhi : 0 < r₀ + e := by linarith
  have hanti := radialEquation_strictAntiOn (B := saddleRadialConst d α)
    (saddleRadialCoeff_nonneg d hd hαfull)
  have hevlo : ∀ᶠ β in 𝓝[Set.Icc 0 (Real.pi / 2)] α,
      0 < radialEquation (saddleRadialCoeff d β) (saddleRadialConst d β) (r₀ - e) :=
    continuousOn_radialEquation_saddle d _ α hα
      (Ioi_mem_nhds (by linarith [hanti hlo hr₀ (sub_lt_self r₀ he)]))
  have hevhi : ∀ᶠ β in 𝓝[Set.Icc 0 (Real.pi / 2)] α,
      radialEquation (saddleRadialCoeff d β) (saddleRadialConst d β) (r₀ + e) < 0 :=
    continuousOn_radialEquation_saddle d _ α hα
      (Iio_mem_nhds (by linarith [hanti hr₀ hhi (lt_add_of_pos_right r₀ he)]))
  filter_upwards [self_mem_nhdsWithin, hevlo, hevhi] with β hβ hβlo hβhi
  have hβfull : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩
  obtain ⟨hrβ, hrβeq⟩ := saddleRadius_pos_and_eq d hd hβfull
  have hcβ := saddleRadialCoeff_nonneg d hd hβfull
  have h₁ := lt_of_radialEquation_pos hcβ hlo hrβ hrβeq hβlo
  have h₂ := lt_of_radialEquation_neg hcβ hhi hrβ hrβeq hβhi
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The saddle parameter is continuous on the full closed angle interval. -/
theorem continuousOn_saddleQ (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (saddleQ d) (Set.Icc 0 (Real.pi / 2)) := by
  unfold saddleQ
  have hrne : ∀ x ∈ Set.Icc 0 (Real.pi / 2), saddleRadius d x ≠ 0 := by
    intro x hx
    exact (saddleRadius_pos_and_eq d hd
      ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩).1.ne'
  have hinv := (continuousOn_saddleRadius d hd).fun_inv₀ hrne
  exact (hinv.pow 2).add ((continuousOn_const.mul continuousOn_sinRatio).mul hinv)

/-- Every parameter between the two endpoint values has a unique generalized
inverse angle, and evaluation at that angle recovers the parameter. -/
theorem saddleQ_saddleAngle_of_mem (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Icc (edgeQ d) (saddleQ d (Real.pi / 2))) :
    saddleAngle d q ∈ Set.Icc 0 (Real.pi / 2) ∧
      saddleQ d (saddleAngle d q) = q := by
  obtain ⟨α, hα, rfl⟩ := intermediate_value_Icc (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    (continuousOn_saddleQ d hd) (by simpa [edgeQ] using hq)
  rw [saddleAngle_saddleQ d hd hα]
  exact ⟨hα, rfl⟩

/-- The recovered angle is the unique angle on the saddle interval with the
given `q`-coordinate. -/
theorem saddleAngle_eq_of_saddleQ_eq (d : ℕ) (hd : 1 ≤ d) {q α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hq : saddleQ d α = q) :
    saddleAngle d q = α := by
  rw [← hq]
  exact saddleAngle_saddleQ d hd hα

/-- On the range `edgeQ < q ≤ scaleT`, the inverse angle lies in the
open saddle interval and exactly parameterizes `q`. -/
theorem saddle_inverse_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < saddleAngle d q ∧ saddleAngle d q < Real.pi / 2 ∧
      saddleQ d (saddleAngle d q) = q := by
  have htop := scaleT_lt_saddleQ_pi_div_two d hd
  have hmem : q ∈ Set.Icc (edgeQ d) (saddleQ d (Real.pi / 2)) :=
    ⟨hq.1.le, (hq.2.trans_lt htop).le⟩
  rcases saddleQ_saddleAngle_of_mem d hd hmem with ⟨hangle, hinv⟩
  have hpos : 0 < saddleAngle d q := by
    by_contra hn
    have hz : saddleAngle d q = 0 := le_antisymm (le_of_not_gt hn) hangle.1
    have heq : edgeQ d = q := by
      rw [edgeQ, ← hinv, hz]
    linarith [hq.1]
  have hlt : saddleAngle d q < Real.pi / 2 := by
    by_contra hn
    have hz : saddleAngle d q = Real.pi / 2 :=
      le_antisymm hangle.2 (le_of_not_gt hn)
    have heq : saddleQ d (Real.pi / 2) = q := by
      simpa [hz] using hinv
    exact (not_lt_of_ge hq.2) (htop.trans_eq heq)
  exact ⟨hpos, hlt, hinv⟩

end RiemannJensen
