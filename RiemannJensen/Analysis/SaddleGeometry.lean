module

public import RiemannJensen.Analysis.SaddleTrig
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Monotonicity and inversion of the saddle parameters

This file proves that `α / sin α`, with its removable value at zero, is strictly
increasing, hence that `saddleQ` is strictly increasing while `saddleRadius`
is strictly decreasing.  The generalized inverse `saddleAngle` is then shown
to recover every angle in the closed saddle interval.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The unextended quotient `x / sin x`. -/
noncomputable def rawSinRatio (x : ℝ) : ℝ := x / Real.sin x

/-- Derivative of `x / sin x` away from zeros of sine. -/
theorem hasDerivAt_rawSinRatio {x : ℝ} (hs : Real.sin x ≠ 0) :
    HasDerivAt rawSinRatio
      ((Real.sin x - x * Real.cos x) / Real.sin x ^ 2) x :=
  ((hasDerivAt_id x).div (Real.hasDerivAt_sin x) hs).congr_deriv (by simp)

/-- For `0 < x ≤ π / 2`, `x * cos x < sin x`. -/
theorem self_mul_cos_lt_sin {x : ℝ} (hx : 0 < x)
    (hxtop : x ≤ Real.pi / 2) :
    x * Real.cos x < Real.sin x := by
  rcases hxtop.eq_or_lt with htop | htop
  · subst x
    simp
  · rw [← lt_div_iff₀ (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htop⟩),
      ← Real.tan_eq_sin_div_cos]
    exact Real.lt_tan hx htop

/-- The raw sine ratio is continuous on the positive saddle interval. -/
theorem continuousOn_rawSinRatio :
    ContinuousOn rawSinRatio (Set.Ioc 0 (Real.pi / 2)) := by
  intro x hx
  have hs : Real.sin x ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_lt (by linarith [Real.pi_pos]))).ne'
  exact (continuousAt_id.div Real.continuous_sin.continuousAt hs).continuousWithinAt

/-- Away from zero, `x / sin x` is strictly increasing. -/
theorem rawSinRatio_strictMonoOn :
    StrictMonoOn rawSinRatio (Set.Ioc 0 (Real.pi / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (Real.pi / 2))
    continuousOn_rawSinRatio
  intro x hx
  have hmem := interior_subset hx
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hmem.1 (hmem.2.trans_lt (by linarith [Real.pi_pos]))
  rw [(hasDerivAt_rawSinRatio hsin.ne').deriv]
  exact div_pos (sub_pos.2 (self_mul_cos_lt_sin hmem.1 hmem.2)) (pow_pos hsin 2)

/-- The removable endpoint value `1` is strictly smaller than every later
value of the sine ratio. -/
theorem one_lt_sinRatio {α : ℝ} (hα : 0 < α) (hαtop : α ≤ Real.pi / 2) :
    1 < sinRatio α := by
  rw [sinRatio_of_ne hα.ne']
  have hsin : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα (hαtop.trans_lt (by linarith [Real.pi_pos]))
  exact (one_lt_div hsin).2 (Real.sin_lt hα)

/-- The continuously extended sine ratio is strictly increasing on the full
closed saddle interval. -/
theorem sinRatio_strictMonoOn :
    StrictMonoOn sinRatio (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  rcases hx.1.eq_or_lt with hzero | hxpos
  · subst x
    simpa using one_lt_sinRatio hxy hy.2
  · rw [sinRatio_of_ne hxpos.ne', sinRatio_of_ne (hxpos.trans hxy).ne']
    exact rawSinRatio_strictMonoOn ⟨hxpos, hx.2⟩
      ⟨hxpos.trans hxy, hy.2⟩ hxy

/-- The sine ratio is positive throughout the saddle interval. -/
theorem sinRatio_pos_of_mem {α : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    0 < sinRatio α := by
  rcases hα.1.eq_or_lt with hzero | hpos
  · subst α
    simp
  · exact zero_lt_one.trans (one_lt_sinRatio hpos hα.2)

/-- The saddle radius is positive on the closed saddle interval. -/
theorem saddleRadius_pos_of_mem_Icc (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) : 0 < saddleRadius d α :=
  (saddleRadius_pos_and_eq d hd ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩).1

/-- The inverse saddle radius strictly increases with the angle. -/
theorem saddleRadius_inv_strictMonoOn (d : ℕ) (hd : 1 ≤ d) :
    StrictMonoOn (fun α => (saddleRadius d α)⁻¹)
      (Set.Icc 0 (Real.pi / 2)) := fun _ hα _ hβ hαβ =>
  (inv_lt_inv₀ (saddleRadius_pos_of_mem_Icc d hd hα)
    (saddleRadius_pos_of_mem_Icc d hd hβ)).2 (saddleRadius_strictAntiOn d hd hα hβ hαβ)

/-- The parameter `q` is strictly increasing with the saddle angle. -/
theorem saddleQ_strictMonoOn (d : ℕ) (hd : 1 ≤ d) :
    StrictMonoOn (saddleQ d) (Set.Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  have hinv := saddleRadius_inv_strictMonoOn d hd hα hβ hαβ
  have hinvα := inv_pos.2 (saddleRadius_pos_of_mem_Icc d hd hα)
  have hprod : sinRatio α * (saddleRadius d α)⁻¹ ≤
      sinRatio β * (saddleRadius d β)⁻¹ :=
    mul_le_mul (sinRatio_strictMonoOn hα hβ hαβ).le hinv.le hinvα.le
      (sinRatio_pos_of_mem hβ).le
  have hc : 0 ≤ Real.pi / scaleLambda d :=
    (div_pos Real.pi_pos (scaleLambda_pos d hd)).le
  simp only [saddleQ]
  nlinarith [mul_le_mul_of_nonneg_left hprod hc,
    pow_lt_pow_left₀ hinv hinvα.le two_ne_zero]

/-- On the saddle interval, `saddleQ d α * saddleRadius d α ^ 2` equals
`1 + (π / scaleLambda d) * sinRatio α * saddleRadius d α`. -/
theorem saddleQ_mul_radius_sq (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleQ d α * saddleRadius d α ^ 2 =
      1 + (Real.pi / scaleLambda d) * sinRatio α * saddleRadius d α := by
  rw [saddleQ]
  field_simp [(saddleRadius_pos_of_mem_Icc d hd hα).ne', (scaleLambda_pos d hd).ne']

/-- On the saddle interval, `1 ≤ saddleQ d α * saddleRadius d α ^ 2`. -/
theorem one_le_saddleQ_mul_radius_sq (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    1 ≤ saddleQ d α * saddleRadius d α ^ 2 := by
  rw [saddleQ_mul_radius_sq d hd hα]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg
    (div_pos Real.pi_pos (scaleLambda_pos d hd)).le (sinRatio_pos_of_mem hα).le)
    (saddleRadius_pos_of_mem_Icc d hd hα).le)

/-- On the image of the saddle branch, the generalized inverse recovers the
angle exactly. -/
theorem saddleAngle_saddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Icc 0 (Real.pi / 2)) :
    saddleAngle d (saddleQ d α) = α := by
  have hset :
      {β : ℝ | 0 ≤ β ∧ β ≤ Real.pi / 2 ∧ saddleQ d α ≤ saddleQ d β} =
        Set.Icc α (Real.pi / 2) := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    refine ⟨fun ⟨hβ0, hβtop, hq⟩ => ?_, fun ⟨hαβ, hβtop⟩ => ?_⟩
    · exact ⟨((saddleQ_strictMonoOn d hd).le_iff_le hα ⟨hβ0, hβtop⟩).1 hq, hβtop⟩
    · exact ⟨hα.1.trans hαβ, hβtop,
        ((saddleQ_strictMonoOn d hd).le_iff_le hα ⟨hα.1.trans hαβ, hβtop⟩).2 hαβ⟩
  rw [saddleAngle, hset, csInf_Icc hα.2]

end RiemannJensen
