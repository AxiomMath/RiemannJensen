module

public import RiemannJensen.Analysis.HessianNormBounds
public import RiemannJensen.Analysis.LowerContour

/-!
# Elementary geometry of the normalized local window

For `q` in the scale window `Set.Ioc (edgeQ d) (scaleT d)`, this file proves positivity of the
local half-width `localWidth ε d q`, containment of the local interval around
`-2 * saddleAngle d q` in the lower semicircle, positivity of the real part of the saddle
Hessian.

## Main results

* `localWidth_pos_on_scale_window`: the local half-width is positive.
* `localWidth_le_one_on_scale_window`: for `ε ≤ 1`, the local half-width is at most one.
* `localWindow_contained_lower_semicircle`: the local interval lies in `[-π, 0]`.
* `localWindow_contained_open_lower_semicircle`: for `ε < 1`, it lies in `(-π, 0)`.
* `saddleHessian_re_pos_on_scale_window`: the real part of `saddleHessian d q` is positive.
-/

@[expose] public section

namespace RiemannJensen

/-- Both distances used in the local width are positive on the inverse saddle
branch. -/
theorem min_angle_cos_pos_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < min (saddleAngle d q) (Real.cos (saddleAngle d q)) := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, _⟩
  exact lt_min hα0 (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hα0, Real.pi_pos], hαtop⟩)

/-- Positivity of the chosen local half-width. -/
theorem localWidth_pos_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) (hε : 0 < ε) :
    0 < localWidth ε d q := by
  rw [localWidth]
  exact mul_pos hε (min_angle_cos_pos_on_scale_window d hd hq)

/-- For `0 ≤ ε ≤ 1`, the local half-width `localWidth ε d q` is at most one. -/
theorem localWidth_le_one_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    localWidth ε d q ≤ 1 := by
  have hmin : min (saddleAngle d q) (Real.cos (saddleAngle d q)) ≤ 1 :=
    (min_le_right _ _).trans (Real.cos_le_one _)
  have hmin0 := (min_angle_cos_pos_on_scale_window d hd hq).le
  rw [localWidth]
  nlinarith

/-- For `α ≤ π / 2`, the cosine of `α` is at most the distance to `π / 2`. -/
theorem cos_le_pi_div_two_sub {α : ℝ} (hα : α ≤ Real.pi / 2) :
    Real.cos α ≤ Real.pi / 2 - α := by
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_le (by linarith)

/-- The normalized local interval stays inside the closed lower semicircle. -/
theorem localWindow_contained_lower_semicircle
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -Real.pi ≤ -2 * saddleAngle d q - localWidth ε d q ∧
      -2 * saddleAngle d q + localWidth ε d q ≤ 0 := by
  obtain ⟨hα0, hαtop, _⟩ := saddle_inverse_on_scale_window d hd hq
  let α := saddleAngle d q
  have hmin0 := (min_angle_cos_pos_on_scale_window d hd hq).le
  have hℓα : localWidth ε d q ≤ α := by
    rw [localWidth]
    have hm := min_le_left α (Real.cos α)
    nlinarith
  have hcosdist : Real.cos α ≤ Real.pi / 2 - α := cos_le_pi_div_two_sub hαtop.le
  have hℓdist : localWidth ε d q ≤ Real.pi / 2 - α := by
    rw [localWidth]
    have hm := min_le_right α (Real.cos α)
    nlinarith
  constructor <;> dsimp [α] at * <;> linarith

/-- Under a strict width choice, the local interval is contained in the open
lower semicircle. -/
theorem localWindow_contained_open_lower_semicircle
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    -Real.pi < -2 * saddleAngle d q - localWidth ε d q ∧
      -2 * saddleAngle d q + localWidth ε d q < 0 := by
  obtain ⟨hα0, hαtop, _⟩ := saddle_inverse_on_scale_window d hd hq
  let α := saddleAngle d q
  have hmin0 := min_angle_cos_pos_on_scale_window d hd hq
  have hℓα : localWidth ε d q < α := by
    rw [localWidth]
    have hm := min_le_left α (Real.cos α)
    nlinarith
  have hcosdist : Real.cos α ≤ Real.pi / 2 - α := cos_le_pi_div_two_sub hαtop.le
  have hℓdist : localWidth ε d q < Real.pi / 2 - α := by
    rw [localWidth]
    have hm := min_le_right α (Real.cos α)
    nlinarith
  constructor <;> dsimp [α] at * <;> linarith

/-- The real part of `saddleHessian d q` is positive on the scale window. -/
theorem saddleHessian_re_pos_on_scale_window
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < (saddleHessian d q).re := by
  have hb := saddleHessian_re_bounds_on_scale_window d hd
    (by linarith [Real.pi_pos] : 4 * Real.pi ≤ scaleLambda d) hq
  obtain ⟨ha, hαtop, _⟩ := saddle_inverse_on_scale_window d hd hq
  have hs := Real.sin_pos_of_pos_of_lt_pi ha (hαtop.trans (by linarith [Real.pi_pos]))
  nlinarith [sq_pos_of_pos hs]

end RiemannJensen
