module

public import RiemannJensen.Analysis.CircleGap
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Integrating a uniform curvature bound

A concave function whose derivative vanishes at a point has its maximum there, and a function
with nonpositive second derivative on the interior of a convex set is concave. Consequently, if
`x ↦ f x + c / 2 * (x - a)^2` has nonpositive second derivative and `f' a = 0`, then
`c / 2 * (x - a)^2 ≤ f a - f x`. Applied to the real part of the circle phase in the coordinate
`z = cos β`, with the curvature bound `G'' ≤ -3`, this gives a quadratic gap with constant `3/2`.

## Main results

* `ConcaveOn.le_of_hasDerivAt_zero`: a stationary point of a concave function is a maximum.
* `quadratic_gap_of_second_deriv_nonpos`: a nonpositive second derivative of the shifted function
  gives the quadratic gap `c / 2 * (x - a)^2 ≤ f a - f x`.
* `circleRealPhaseZ_quadratic_gap`: the quadratic gap `3/2 * (z - cos α)^2` for the real
  circle phase on `[0, 1]`.

## Implementation notes

The derivative hypotheses are `HasDerivWithinAt` on the interior of the domain, since the
derivatives of the `arccos` coordinate exist only for `-1 < z < 1`; continuity covers the
endpoints.
-/

@[expose] public section

namespace RiemannJensen

/-! ## Concavity and quadratic gaps -/

/-- A stationary point of a concave function is a global maximum on its convexity set. -/
theorem _root_.ConcaveOn.le_of_hasDerivAt_zero {D : Set ℝ} {f : ℝ → ℝ} {a x : ℝ}
    (hf : ConcaveOn ℝ D f) (ha : a ∈ D) (hx : x ∈ D) (hfa : HasDerivAt f 0 a) : f x ≤ f a := by
  rcases lt_trichotomy x a with hxa | hxa | hax
  · have hs := hf.le_slope_of_hasDerivAt hx ha hxa hfa
    rw [slope_def_field] at hs
    have hnum : 0 ≤ f a - f x := by simpa using (le_div_iff₀ (sub_pos.mpr hxa)).mp hs
    linarith
  · simp [hxa]
  · have hs := hf.slope_le_of_hasDerivAt ha hx hax hfa
    rw [slope_def_field] at hs
    have hnum : f x - f a ≤ 0 := by simpa using (div_le_iff₀ (sub_pos.mpr hax)).mp hs
    linarith

/-- A twice differentiable function with nonpositive second derivative and a
stationary point has its maximum at that point, where the derivatives are taken on the interior
of the convex set. -/
theorem le_of_second_deriv_nonpos_at_stationary {D : Set ℝ} (hD : Convex ℝ D)
    {f f' f'' : ℝ → ℝ} {a x : ℝ} (hf : ContinuousOn f D)
    (hf' : ∀ y ∈ interior D, HasDerivWithinAt f (f' y) (interior D) y)
    (hf'' : ∀ y ∈ interior D, HasDerivWithinAt f' (f'' y) (interior D) y)
    (hf''_nonpos : ∀ y ∈ interior D, f'' y ≤ 0) (ha : a ∈ D) (hx : x ∈ D)
    (hfa : HasDerivAt f 0 a) : f x ≤ f a :=
  (concaveOn_of_hasDerivWithinAt2_nonpos hD hf hf' hf'' hf''_nonpos).le_of_hasDerivAt_zero ha hx hfa

/-- If `y ↦ f y + c / 2 * (y - a)^2` is concave on `D` and `f' a = 0`, then
`c / 2 * (x - a)^2 ≤ f a - f x` for `x ∈ D`. -/
theorem quadratic_gap_of_concave_shift {D : Set ℝ} {f : ℝ → ℝ} {a x c : ℝ}
    (hconc : ConcaveOn ℝ D (fun y => f y + c / 2 * (y - a) ^ 2))
    (ha : a ∈ D) (hx : x ∈ D) (hfa : HasDerivAt f 0 a) :
    c / 2 * (x - a) ^ 2 ≤ f a - f x := by
  have hquad : HasDerivAt (fun y : ℝ => c / 2 * (y - a) ^ 2) 0 a :=
    ((((hasDerivAt_id a).sub_const a).pow 2).const_mul (c / 2)).congr_deriv (by simp)
  have hmax := hconc.le_of_hasDerivAt_zero ha hx ((hfa.add hquad).congr_deriv (by simp))
  simp only [sub_self] at hmax
  linarith

/-- If `F y = f y + c / 2 * (y - a)^2` on a convex set `D`, `F` has first and second derivatives
`F'` and `F''` on the interior with `F'' ≤ 0`, and `f' a = 0`, then
`c / 2 * (x - a)^2 ≤ f a - f x` for `x ∈ D`. -/
theorem quadratic_gap_of_second_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D)
    {f F F' F'' : ℝ → ℝ} {a x c : ℝ} (hF : ContinuousOn F D)
    (hF' : ∀ y ∈ interior D, HasDerivWithinAt F (F' y) (interior D) y)
    (hF'' : ∀ y ∈ interior D, HasDerivWithinAt F' (F'' y) (interior D) y)
    (hF''_nonpos : ∀ y ∈ interior D, F'' y ≤ 0)
    (hshift : ∀ y ∈ D, F y = f y + c / 2 * (y - a) ^ 2)
    (ha : a ∈ D) (hx : x ∈ D) (hfa : HasDerivAt f 0 a) :
    c / 2 * (x - a) ^ 2 ≤ f a - f x :=
  quadratic_gap_of_concave_shift
    ((concaveOn_of_hasDerivWithinAt2_nonpos hD hF hF' hF'' hF''_nonpos).congr hshift) ha hx hfa

/-! ## The arc term and its derivatives -/

/-- The term `arccos z * √(1 - z ^ 2)`, the only non-polynomial term of the circle phase in the
coordinate `z`. -/
noncomputable def circleArc (z : ℝ) : ℝ :=
  Real.arccos z * Real.sqrt (1 - z ^ 2)

/-- First derivative of `circleArc` on `(-1,1)`. -/
noncomputable def circleArcDeriv (z : ℝ) : ℝ :=
  -1 - z * Real.arccos z / Real.sqrt (1 - z ^ 2)

/-- Second derivative of `circleArc` on `(-1,1)`. -/
noncomputable def circleArcSecond (z : ℝ) : ℝ :=
  -(Real.arccos z - z * Real.sqrt (1 - z ^ 2)) /
    Real.sqrt (1 - z ^ 2) ^ 3

/-- The arccosine--square-root product is continuous. -/
theorem continuous_circleArc : Continuous circleArc :=
  Real.continuous_arccos.mul
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))

/-- Derivative of the arccosine--square-root product in the open unit
interval. -/
theorem hasDerivAt_circleArc {z : ℝ} (hz : z ∈ Set.Ioo (-1) 1) :
    HasDerivAt circleArc (circleArcDeriv z) z := by
  have harg : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hs : Real.sqrt (1 - z ^ 2) ≠ 0 := (Real.sqrt_pos.2 harg).ne'
  have hacos : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - z ^ 2))) z :=
    Real.hasDerivAt_arccos (by linarith [hz.1]) (by linarith [hz.2])
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * z) z :=
    ((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2)).congr_deriv
      (by simp)
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      ((-2 * z) / (2 * Real.sqrt (1 - z ^ 2))) z :=
    hinner.sqrt harg.ne'
  refine (hacos.mul hsqrt).congr_deriv ?_
  rw [circleArcDeriv]
  field_simp [hs]
  ring

/-- Derivative of `circleArcDeriv`, hence the second derivative of
`circleArc`, in the open unit interval. -/
theorem hasDerivAt_circleArcDeriv {z : ℝ} (hz : z ∈ Set.Ioo (-1) 1) :
    HasDerivAt circleArcDeriv (circleArcSecond z) z := by
  have harg : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hs : Real.sqrt (1 - z ^ 2) ≠ 0 := (Real.sqrt_pos.2 harg).ne'
  have hacos : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - z ^ 2))) z :=
    Real.hasDerivAt_arccos (by linarith [hz.1]) (by linarith [hz.2])
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * z) z :=
    ((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2)).congr_deriv
      (by simp)
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      ((-2 * z) / (2 * Real.sqrt (1 - z ^ 2))) z :=
    hinner.sqrt harg.ne'
  have hnum : HasDerivAt (fun y : ℝ => y * Real.arccos y)
      (Real.arccos z + z * (-(1 / Real.sqrt (1 - z ^ 2)))) z :=
    ((hasDerivAt_id z).mul hacos).congr_deriv (by simp)
  have hfull : HasDerivAt
      (fun y : ℝ => -1 - y * Real.arccos y / Real.sqrt (1 - y ^ 2))
      (0 - ((Real.arccos z + z * (-(1 / Real.sqrt (1 - z ^ 2)))) *
          Real.sqrt (1 - z ^ 2) -
        (z * Real.arccos z) *
          ((-2 * z) / (2 * Real.sqrt (1 - z ^ 2)))) /
        Real.sqrt (1 - z ^ 2) ^ 2) z :=
    (hasDerivAt_const z (-1 : ℝ)).sub (hnum.div hsqrt hs)
  refine hfull.congr_deriv ?_
  have hs2 : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt harg.le
  rw [circleArcSecond]
  field_simp [hs]
  linear_combination (-Real.arccos z) * hs2

/-- The real part of the paper's circle phase in the coordinate `z = cos β`.
Here `α` fixes the saddle radius and `z` is the running circle coordinate. -/
noncomputable def circleRealPhaseZ (d : ℕ) (α z : ℝ) : ℝ :=
  let r := saddleRadius d α
  let q := saddleQ d α;
  -q * r ^ 2 * (2 * z ^ 2 - 1) +
    Real.pi * r * (1 + 2 * Real.log r / scaleLambda d) * z -
    (2 * Real.pi * r / scaleLambda d) * circleArc z -
    2 * Real.log r

/-- The first derivative of the real-coordinate circle phase. -/
noncomputable def circleRealPhaseZDeriv (d : ℕ) (α z : ℝ) : ℝ :=
  -4 * saddleQ d α * saddleRadius d α ^ 2 * z +
    Real.pi * saddleRadius d α *
      (1 + 2 * Real.log (saddleRadius d α) / scaleLambda d) -
    (2 * Real.pi * saddleRadius d α / scaleLambda d) * circleArcDeriv z

/-- The second derivative of the real-coordinate circle phase. -/
noncomputable def circleRealPhaseZSecond (d : ℕ) (α z : ℝ) : ℝ :=
  -4 * saddleQ d α * saddleRadius d α ^ 2 -
    (2 * Real.pi * saddleRadius d α / scaleLambda d) * circleArcSecond z

/-- First derivative formula for the circle phase in the open unit interval. -/
theorem hasDerivAt_circleRealPhaseZ (d : ℕ) (α : ℝ) {z : ℝ} (hz : z ∈ Set.Ioo (-1) 1) :
    HasDerivAt (circleRealPhaseZ d α) (circleRealPhaseZDeriv d α z) z := by
  have harc := hasDerivAt_circleArc hz
  have h := ((((hasDerivAt_const z
      (-saddleQ d α * saddleRadius d α ^ 2)).mul
        ((((hasDerivAt_id z).pow 2).const_mul 2).sub_const 1)).add
      ((hasDerivAt_id z).const_mul
        (Real.pi * saddleRadius d α *
          (1 + 2 * Real.log (saddleRadius d α) / scaleLambda d)))).sub
      (harc.const_mul (2 * Real.pi * saddleRadius d α / scaleLambda d))).sub_const
        (2 * Real.log (saddleRadius d α))
  refine h.congr_deriv ?_
  simp only [circleRealPhaseZDeriv, id]
  push_cast
  ring

/-- Second derivative formula for the circle phase in the open unit
interval. -/
theorem hasDerivAt_circleRealPhaseZDeriv (d : ℕ) (α : ℝ) {z : ℝ} (hz : z ∈ Set.Ioo (-1) 1) :
    HasDerivAt (circleRealPhaseZDeriv d α) (circleRealPhaseZSecond d α z) z := by
  have harc := hasDerivAt_circleArcDeriv hz
  have h := (((hasDerivAt_id z).const_mul
      (-4 * saddleQ d α * saddleRadius d α ^ 2)).add_const
        (Real.pi * saddleRadius d α *
          (1 + 2 * Real.log (saddleRadius d α) / scaleLambda d))).sub
      (harc.const_mul (2 * Real.pi * saddleRadius d α / scaleLambda d))
  refine h.congr_deriv ?_
  simp only [circleRealPhaseZSecond]
  ring

/-! ## Evaluation at `z = cos β` -/

/-- For `β ∈ [0, π/2]`, the square root in the real coordinate is exactly the sine of the
angle. -/
theorem sqrt_one_sub_cos_sq {β : ℝ} (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.sqrt (1 - Real.cos β ^ 2) = Real.sin β :=
  (Real.sin_eq_sqrt_one_sub_cos_sq hβ.1 (hβ.2.trans (by linarith [Real.pi_pos]))).symm

/-- At `z = cos β`, the real-coordinate second derivative is exactly the
model curvature `circleModelCurvature d α β`. -/
theorem circleRealPhaseZSecond_cos (d : ℕ) (α : ℝ) {β : ℝ} (hβ : β ∈ Set.Ioc 0 (Real.pi / 2)) :
    circleRealPhaseZSecond d α (Real.cos β) = circleModelCurvature d α β := by
  have hβcc : β ∈ Set.Icc 0 (Real.pi / 2) := ⟨hβ.1.le, hβ.2⟩
  have harccos : Real.arccos (Real.cos β) = β :=
    Real.arccos_cos hβ.1.le (hβ.2.trans (by linarith [Real.pi_pos]))
  have hsqrt := sqrt_one_sub_cos_sq hβcc
  rw [circleRealPhaseZSecond, circleModelCurvature, circleArcSecond,
    harccos, hsqrt, circleCurvatureQuotient, ite_eq_right hβ.1.ne']
  ring

/-- At `z = cos β` with `0 < β ≤ π / 2`, the second derivative of the real-coordinate circle phase
is at most `-3`. -/
theorem circleRealPhaseZSecond_cos_le_neg_three
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α β : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hβ : β ∈ Set.Ioc 0 (Real.pi / 2)) :
    circleRealPhaseZSecond d α (Real.cos β) ≤ -3 := by
  rw [circleRealPhaseZSecond_cos d α hβ]
  exact circleModelCurvature_le_neg_three d hd hΛ hα ⟨hβ.1.le, hβ.2⟩

/-- The circle phase is stationary at its saddle coordinate `cos α`. -/
theorem circleRealPhaseZDeriv_cos_eq_zero (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 (Real.pi / 2)) :
    circleRealPhaseZDeriv d α (Real.cos α) = 0 := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2⟩
  have hαfull : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hrpos := (saddleRadius_pos_and_eq d hd hαfull).1
  have hΛpos := scaleLambda_pos d hd
  have hs : Real.sin α ≠ 0 := by
    have hpi : α < Real.pi := lt_of_le_of_lt hα.2 (by linarith [Real.pi_pos])
    exact (Real.sin_pos_of_pos_of_lt_pi hα.1 hpi).ne'
  have harccos : Real.arccos (Real.cos α) = α :=
    Real.arccos_cos hα.1.le (hα.2.trans (by linarith [Real.pi_pos]))
  have hsqrt := sqrt_one_sub_cos_sq hαcc
  have hrad := saddleRadius_characterization d hd hαfull
  have hq := saddleQ_mul_radius_sq d hd hαcc
  rw [circleRealPhaseZDeriv, circleArcDeriv, harccos, hsqrt]
  rw [show -4 * saddleQ d α * saddleRadius d α ^ 2 * Real.cos α =
      -4 * (saddleQ d α * saddleRadius d α ^ 2) * Real.cos α by ring,
    hq]
  rw [alphaCot_of_ne hα.1.ne'] at hrad
  rw [sinRatio_of_ne hα.1.ne']
  field_simp [hrpos.ne', hΛpos.ne', Real.pi_ne_zero, hs] at hrad ⊢
  linear_combination (-1 : ℝ) * hrad

/-- The real circle phase has vanishing derivative at its saddle coordinate `cos α`. -/
theorem hasDerivAt_circleRealPhaseZ_cos_eq_zero (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 (Real.pi / 2)) :
    HasDerivAt (circleRealPhaseZ d α) 0 (Real.cos α) := by
  refine (hasDerivAt_circleRealPhaseZ d α ⟨?_, ?_⟩).congr_deriv
    (circleRealPhaseZDeriv_cos_eq_zero d hd hα)
  · linarith [Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩]
  · simpa using Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show α ∈ Set.Icc 0 Real.pi from ⟨hα.1.le, hα.2.trans (by linarith [Real.pi_pos])⟩) hα.1

/-! ## The quadratic gap for the circle phase -/

/-- The real circle phase is continuous in its real coordinate. -/
theorem continuous_circleRealPhaseZ (d : ℕ) (α : ℝ) :
    Continuous (circleRealPhaseZ d α) := by
  have harc := continuous_circleArc
  unfold circleRealPhaseZ
  fun_prop

/-- For `z ∈ (0, 1)`, the second derivative of the real circle phase is at most `-3`. -/
theorem circleRealPhaseZSecond_le_neg_three
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α z : ℝ} (hα : α ∈ Set.Icc 0 (Real.pi / 2))
    (hz : z ∈ Set.Ioo 0 1) :
    circleRealPhaseZSecond d α z ≤ -3 := by
  rw [← Real.cos_arccos (by linarith [hz.1]) hz.2.le]
  exact circleRealPhaseZSecond_cos_le_neg_three d hd hΛ hα
    ⟨Real.arccos_pos.2 hz.2, (Real.arccos_lt_pi_div_two.2 hz.1).le⟩

/-- The quadratic gap `3/2 * (z - cos α)^2 ≤ G (cos α) - G z` for the real circle phase `G` in the
coordinate `z = cos β`, for `z ∈ [0, 1]`. -/
theorem circleRealPhaseZ_quadratic_gap
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {α z : ℝ} (hα : α ∈ Set.Ioc 0 (Real.pi / 2))
    (hz : z ∈ Set.Icc 0 1) :
    (3 / 2 : ℝ) * (z - Real.cos α) ^ 2 ≤
      circleRealPhaseZ d α (Real.cos α) - circleRealPhaseZ d α z := by
  let a := Real.cos α
  let G := circleRealPhaseZ d α
  let F : ℝ → ℝ := fun y => G y + (3 / 2 : ℝ) * (y - a) ^ 2
  let F' : ℝ → ℝ := fun y => circleRealPhaseZDeriv d α y + 3 * (y - a)
  let F'' : ℝ → ℝ := fun y => circleRealPhaseZSecond d α y + 3
  have ha : a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩, Real.cos_le_one α⟩
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    ((continuous_circleRealPhaseZ d α).add
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))).continuousOn
  have hderiv : ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F (F' y) (interior (Set.Icc (0 : ℝ) 1)) y := by
    intro y hy
    rw [interior_Icc] at hy ⊢
    have hG := hasDerivAt_circleRealPhaseZ d α ⟨by linarith [hy.1], hy.2⟩
    have hquad : HasDerivAt (fun t : ℝ => (3 / 2 : ℝ) * (t - a) ^ 2)
        (3 * (y - a)) y :=
      ((((hasDerivAt_id y).sub_const a).pow 2).const_mul (3 / 2 : ℝ)).congr_deriv
        (by simp only [id]; ring)
    exact (hG.add hquad).hasDerivWithinAt
  have hderiv2 : ∀ y ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F' (F'' y) (interior (Set.Icc (0 : ℝ) 1)) y := by
    intro y hy
    rw [interior_Icc] at hy ⊢
    have hG := hasDerivAt_circleRealPhaseZDeriv d α ⟨by linarith [hy.1], hy.2⟩
    have hlin : HasDerivAt (fun t : ℝ => 3 * (t - a)) 3 y :=
      (((hasDerivAt_id y).sub_const a).const_mul 3).congr_deriv (by ring)
    exact (hG.add hlin).hasDerivWithinAt
  have hnonpos : ∀ y ∈ interior (Set.Icc (0 : ℝ) 1), F'' y ≤ 0 := by
    intro y hy
    rw [interior_Icc] at hy
    dsimp only [F'']
    have hcurv := circleRealPhaseZSecond_le_neg_three d hd hΛ
      ⟨hα.1.le, hα.2⟩ hy
    linarith
  have hshift : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      F y = G y + 3 / 2 * (y - a) ^ 2 := fun _ _ => rfl
  exact quadratic_gap_of_second_deriv_nonpos (convex_Icc 0 1)
    hcont hderiv hderiv2 hnonpos hshift ha hz (hasDerivAt_circleRealPhaseZ_cos_eq_zero d hd hα)

end RiemannJensen
