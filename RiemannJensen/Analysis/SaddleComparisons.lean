module

public import RiemannJensen.Analysis.SaddleBounds
public import RiemannJensen.Analysis.SaddleInverse

/-!
# Radius--level comparisons on the inverse saddle branch

For a level `q` in the scale window `(edgeQ d, scaleT d]`, the saddle radius
`saddleRadius d (saddleAngle d q)` is comparable to `1 / √q`, with absolute constants.

## Main results

* `inv_sqrt_le_saddleRadius_on_scale_window`: `1 / √q ≤ saddleRadius d (saddleAngle d q)`.
* `saddleRadius_le_sqrt_two_div_sqrt_on_scale_window`: if `2π ≤ scaleLambda d`, then
  `saddleRadius d (saddleAngle d q) ≤ √2 / √q`.
* `sqrt_scale_div_le_scale_mul_saddleRadius`: if `q ≤ c₀ T` with `T = scaleT d`, then
  `√(T / c₀) ≤ T · saddleRadius d (saddleAngle d q)`.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- Every level in the scale window is positive. -/
theorem pos_of_mem_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) : 0 < q := by
  obtain ⟨hα0, hαtop, hinv⟩ := saddle_inverse_on_scale_window d hd hq
  have hp := one_le_saddleQ_mul_radius_sq d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hp
  by_contra hn
  nlinarith [sq_nonneg (saddleRadius d (saddleAngle d q))]

/-- On the scale window, the saddle radius is bounded below by the reciprocal square
root of its level. -/
theorem inv_sqrt_le_saddleRadius_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    1 / Real.sqrt q ≤ saddleRadius d (saddleAngle d q) := by
  obtain ⟨hα0, hαtop, hinv⟩ := saddle_inverse_on_scale_window d hd hq
  have hr := (saddleRadius_pos_and_eq d hd ⟨by linarith [Real.pi_pos], hαtop.le⟩).1
  have hp := one_le_saddleQ_mul_radius_sq d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hp
  have hq0 := pos_of_mem_scale_window d hd hq
  have hprod2 : 1 ≤ (saddleRadius d (saddleAngle d q) * Real.sqrt q) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hq0.le, mul_comm]
  rw [div_le_iff₀ (Real.sqrt_pos.2 hq0)]
  nlinarith [Real.sqrt_nonneg q, mul_nonneg hr.le (Real.sqrt_nonneg q)]

/-- If `2π ≤ scaleLambda d`, the saddle radius at level `q` is at most `√2 / √q` throughout
the scale window. -/
theorem saddleRadius_le_sqrt_two_div_sqrt_on_scale_window (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 2 * Real.pi ≤ scaleLambda d) {q : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    saddleRadius d (saddleAngle d q) ≤ Real.sqrt 2 / Real.sqrt q := by
  obtain ⟨hα0, hαtop, hinv⟩ := saddle_inverse_on_scale_window d hd hq
  have hb := saddleQ_radius_sq_bounds d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hb
  have hfrac : 2 * Real.pi / scaleLambda d ≤ 1 := (div_le_one (scaleLambda_pos d hd)).2 hΛ
  have hq0 := pos_of_mem_scale_window d hd hq
  rw [le_div_iff₀ (Real.sqrt_pos.2 hq0)]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt hq0.le, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- If `0 < c₀` and the level `q` in the scale window satisfies `q ≤ c₀ T`, where `T = scaleT d`,
then `√(T / c₀) ≤ T r` for the saddle radius `r` at level `q`. -/
theorem sqrt_scale_div_le_scale_mul_saddleRadius (d : ℕ) (hd : 1 ≤ d) {q c₀ : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hc₀ : 0 < c₀) (hqtop : q ≤ c₀ * scaleT d) :
    Real.sqrt (scaleT d / c₀) ≤ scaleT d * saddleRadius d (saddleAngle d q) := by
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd)
  have hq0 := pos_of_mem_scale_window d hd hq
  calc
    Real.sqrt (scaleT d / c₀) ≤ scaleT d / Real.sqrt q := by
      refine Real.sqrt_le_iff.2 ⟨div_nonneg hT.le (Real.sqrt_nonneg q), ?_⟩
      rw [div_pow, Real.sq_sqrt hq0.le, div_le_div_iff₀ hc₀ hq0]
      nlinarith
    _ ≤ scaleT d * saddleRadius d (saddleAngle d q) := by
      rw [← mul_one_div]
      exact mul_le_mul_of_nonneg_left (inv_sqrt_le_saddleRadius_on_scale_window d hd hq) hT.le

end RiemannJensen
