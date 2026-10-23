module

public import RiemannJensen.Analysis.SaddleRadial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Trigonometric monotonicity for the saddle branch

This file proves, including the removable endpoint at zero, that both
`cos α` and the continuous extension `α cot α` strictly decrease on
`[0, π / 2]`.  These facts make the radial coefficients strictly decrease
and hence make the saddle radius strictly decrease with the angle.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The unextended expression `x cot x`, used away from zero. -/
noncomputable def rawAlphaCot (x : ℝ) : ℝ :=
  x * Real.cos x / Real.sin x

/-- The derivative of `x cot x` away from the zeros of sine. -/
theorem hasDerivAt_rawAlphaCot {x : ℝ} (hs : Real.sin x ≠ 0) :
    HasDerivAt rawAlphaCot
      ((Real.sin x * Real.cos x - x) / Real.sin x ^ 2) x := by
  unfold rawAlphaCot
  have h := (hasDerivAt_id x).mul (Real.hasDerivAt_cos x)
  have hq := h.div (Real.hasDerivAt_sin x) hs
  change HasDerivAt (id * Real.cos / Real.sin)
    ((Real.sin x * Real.cos x - x) / Real.sin x ^ 2) x
  apply hq.congr_deriv
  simp only [id_eq]
  congr 1
  rw [Pi.mul_apply]
  simp only [id_eq, one_mul, mul_neg]
  rw [show (Real.cos x + -(x * Real.sin x)) * Real.sin x -
      x * Real.cos x * Real.cos x =
      Real.sin x * Real.cos x -
        x * (Real.sin x ^ 2 + Real.cos x ^ 2) by ring,
    Real.sin_sq_add_cos_sq]
  ring

/-- The raw expression is continuous on the positive half of the saddle
angle interval. -/
theorem continuousOn_rawAlphaCot :
    ContinuousOn rawAlphaCot (Set.Ioc 0 (Real.pi / 2)) := by
  intro x hx
  have hxpi : x < Real.pi := lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])
  have hs : Real.sin x ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hx.1 hxpi).ne'
  exact (((continuousAt_id.mul Real.continuous_cos.continuousAt).div
    Real.continuous_sin.continuousAt hs).continuousWithinAt)

/-- The numerator in the derivative of `x cot x` is strictly negative on the
positive saddle-angle interval. -/
theorem sin_mul_cos_sub_self_neg {x : ℝ} (hx : 0 < x)
    (hxtop : x ≤ Real.pi / 2) :
    Real.sin x * Real.cos x - x < 0 := by
  have hsin_lt : Real.sin x < x := Real.sin_lt hx
  have hsin_nonneg : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.le (by linarith [hxtop, Real.pi_pos])
  have hmul : Real.sin x * Real.cos x ≤ Real.sin x := by
    simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one x) hsin_nonneg
  linarith

/-- Away from zero, `x cot x` is strictly decreasing. -/
theorem rawAlphaCot_strictAntiOn :
    StrictAntiOn rawAlphaCot (Set.Ioc 0 (Real.pi / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (Real.pi / 2))
    continuousOn_rawAlphaCot
  intro x hx
  have hmem := interior_subset hx
  have hxpos : 0 < x := hmem.1
  have hxpi : x < Real.pi := lt_of_le_of_lt hmem.2 (by linarith [Real.pi_pos])
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
  rw [(hasDerivAt_rawAlphaCot hsin.ne').deriv]
  exact div_neg_of_neg_of_pos (sin_mul_cos_sub_self_neg hxpos hmem.2)
    (sq_pos_of_pos hsin)

/-- The endpoint value at zero is strictly larger than every subsequent value
of `α cot α` on the saddle interval. -/
theorem alphaCot_lt_one {α : ℝ} (hα : 0 < α) (hαtop : α ≤ Real.pi / 2) :
    alphaCot α < 1 := by
  have hαne : α ≠ 0 := ne_of_gt hα
  rw [alphaCot_of_ne hαne]
  have hpi : α < Real.pi := lt_of_le_of_lt hαtop (by linarith [Real.pi_pos])
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hpi
  apply (div_lt_one hsin).2
  rcases hαtop.eq_or_lt with htop | htop
  · subst α
    simp
  · have hcos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htop⟩
    have htan := Real.lt_tan hα htop
    rw [Real.tan_eq_sin_div_cos] at htan
    exact (lt_div_iff₀ hcos).1 htan

/-- The continuous extension `α cot α` is strictly decreasing on the complete
closed saddle-angle interval, including both endpoints. -/
theorem alphaCot_strictAntiOn :
    StrictAntiOn alphaCot (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  rcases hx.1.eq_or_lt with hzero | hxpos
  · subst x
    simpa using alphaCot_lt_one (lt_of_le_of_lt hx.1 hxy) hy.2
  · have hxne : x ≠ 0 := ne_of_gt hxpos
    have hyne : y ≠ 0 := ne_of_gt (hxpos.trans hxy)
    rw [alphaCot_of_ne hxne, alphaCot_of_ne hyne]
    exact rawAlphaCot_strictAntiOn ⟨hxpos, hx.2⟩
      ⟨hxpos.trans hxy, hy.2⟩ hxy

/-- Cosine is strictly decreasing on the saddle-angle interval. -/
theorem cos_strictAntiOn_saddle :
    StrictAntiOn Real.cos (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hx.1 hy.2 hxy

/-- The reciprocal coefficient in the radial equation strictly decreases with
the saddle angle. -/
theorem saddleRadialCoeff_strictAntiOn (d : ℕ) (hd : 1 ≤ d) :
    StrictAntiOn (saddleRadialCoeff d) (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  simp only [saddleRadialCoeff]
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left (cos_strictAntiOn_saddle hx hy hxy)
      (scaleLambda_pos d hd)) (by positivity)

/-- The constant coefficient in the radial equation strictly decreases with
the saddle angle. -/
theorem saddleRadialConst_strictAntiOn (d : ℕ) :
    StrictAntiOn (saddleRadialConst d) (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  simp only [saddleRadialConst]
  linarith [alphaCot_strictAntiOn hx hy hxy]

/-- The saddle radius strictly decreases as the angle increases. -/
theorem saddleRadius_strictAntiOn (d : ℕ) (hd : 1 ≤ d) :
    StrictAntiOn (saddleRadius d) (Set.Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hβfull : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩
  have hcoeff := saddleRadialCoeff_strictAntiOn d hd hα hβ hαβ
  have hconst := saddleRadialConst_strictAntiOn d hα hβ hαβ
  have hle : saddleRadius d β ≤ saddleRadius d α :=
    saddleRadius_le_of_coeff_le d hd hβfull hαfull hcoeff.le hconst.le
  refine lt_of_le_of_ne hle ?_
  intro heqr
  have hαeq := (saddleRadius_pos_and_eq d hd hαfull).2
  have hβeq := (saddleRadius_pos_and_eq d hd hβfull).2
  have hrpos := (saddleRadius_pos_and_eq d hd hαfull).1
  have hdiv : saddleRadialCoeff d β / saddleRadius d α <
      saddleRadialCoeff d α / saddleRadius d α :=
    (div_lt_div_iff_of_pos_right hrpos).2 hcoeff
  rw [heqr] at hβeq
  unfold radialEquation at hαeq hβeq
  linarith

end RiemannJensen
