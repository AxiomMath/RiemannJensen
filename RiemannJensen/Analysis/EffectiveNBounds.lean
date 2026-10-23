module

public import RiemannJensen.Analysis.EdgeQuadratic
public import RiemannJensen.Analysis.LocalWindowGeometry
public import RiemannJensen.Analysis.SaddleCosineComparison

/-! # Quantitative lower bounds for the effective Gaussian parameter -/

@[expose] public section

namespace RiemannJensen

open Set

/-- Geometric lower bound for an arbitrary fixed local-width parameter. -/
theorem effectiveN_geometric
    (ε : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    (3 / 8 : ℝ) * ε ^ 2 * d * Real.sin (saddleAngle d q) *
        (min (saddleAngle d q) (Real.cos (saddleAngle d q))) ^ 2 ≤
      effectiveN ε d q := by
  rw [effectiveN, localWidth]
  calc
    _ = d * ((3 / 8 : ℝ) * Real.sin (saddleAngle d q)) *
        (ε ^ 2 * (min (saddleAngle d q) (Real.cos (saddleAngle d q))) ^ 2) := by ring
    _ ≤ d * ‖saddleHessian d q‖ *
        (ε ^ 2 * (min (saddleAngle d q) (Real.cos (saddleAngle d q))) ^ 2) := by
      gcongr
      exact (saddleHessian_norm_bounds_on_scale_window d hd hΛ hq).1
    _ = _ := by ring

/-- Near the edge, the effective parameter is bounded below by the `3/2`
power of the edge displacement, written without real powers as `t * √t`. -/
theorem effectiveN_edge_lower
    (ε : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hsmall : saddleAngle d q ≤ 1 / 2) :
    (ε ^ 2 / 96) * d * (q - edgeQ d) *
        Real.sqrt (q - edgeQ d) ≤ effectiveN ε d q := by
  let α := saddleAngle d q
  let t := q - edgeQ d
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hαsmall : α ∈ Set.Icc 0 (1 / 2 : ℝ) := ⟨hα0.le, hsmall⟩
  have ht0 : 0 ≤ t := by linarith [hq.1]
  have hcos : α ≤ Real.cos α := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hsin : α / 2 ≤ Real.sin α := by
    nlinarith [half_mul_le_sin (β := α) ⟨hα0.le, hαtop.le⟩]
  have hedge := saddleQ_sub_edge_upper d hd hΛ hαsmall
  rw [hinv] at hedge
  have ht : t ≤ 6 * α ^ 2 := by simpa [t] using hedge
  have hsqrt : Real.sqrt t ≤ 3 * α := by
    nlinarith [Real.sqrt_nonneg t, Real.sq_sqrt ht0, sq_nonneg (Real.sqrt t - 3 * α)]
  have htsqrt : t * Real.sqrt t ≤ 18 * α ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg t),
      mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ 6 * α ^ 2)]
  have hgeom := effectiveN_geometric ε d hd hΛ hq
  rw [min_eq_left hcos] at hgeom
  have hεd : 0 ≤ ε ^ 2 * d := by positivity
  have hgeom' : (3 / 16 : ℝ) * ε ^ 2 * d * α ^ 3 ≤ effectiveN ε d q := by
    nlinarith [mul_le_mul_of_nonneg_left hsin hεd]
  have hmul := mul_le_mul_of_nonneg_left htsqrt hεd
  dsimp [α, t] at hgeom' hmul ⊢
  nlinarith

/-- Away from the edge, the effective parameter is bounded below by an
absolute multiple of `ε² d / q`. -/
theorem effectiveN_tail_lower
    (ε : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hbig : 1 / 2 ≤ saddleAngle d q) :
    (ε ^ 2 / 3000) * d / q ≤ effectiveN ε d q := by
  let α := saddleAngle d q
  let r := saddleRadius d α
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hαpi : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα0.le, hαtop.le⟩
  have hcos0 : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hαtop.le⟩
  have hsin : (1 / 4 : ℝ) ≤ Real.sin α := by nlinarith [half_mul_le_sin hαpi]
  have hmin : Real.cos α / 2 ≤ min α (Real.cos α) :=
    le_min (by nlinarith [Real.cos_le_one α]) (by linarith)
  have hr : 0 < r := (saddleRadius_pos_and_eq d hd ⟨by linarith, hαtop.le⟩).1
  have hqr := one_le_saddleQ_mul_radius_sq d hd hαpi
  rw [hinv] at hqr
  have hq0 : 0 < q := by
    by_contra hn
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (sq_nonneg r)]
  have hcosr : Real.pi * r / 16 ≤ Real.cos α := by
    simpa [α, r] using pi_mul_radius_div_sixteen_le_cos d hd hlarge hq
  have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hqcos : (1 / 64 : ℝ) ≤ q * Real.cos α ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi * r / 16) hcosr 2
    nlinarith [mul_le_mul_of_nonneg_left hsq hq0.le, mul_nonneg hq0.le (sq_nonneg r),
      mul_le_mul_of_nonneg_left hqr (by norm_num : (0 : ℝ) ≤ 1 / 64)]
  have hεd : 0 ≤ ε ^ 2 * d := by positivity
  have hgeom' : (3 / 128 : ℝ) * ε ^ 2 * d * Real.cos α ^ 2 ≤ effectiveN ε d q :=
    calc
      (3 / 128 : ℝ) * ε ^ 2 * d * Real.cos α ^ 2 =
          (3 / 8 : ℝ) * ε ^ 2 * d * (1 / 4 : ℝ) * (Real.cos α / 2) ^ 2 := by ring
      _ ≤ (3 / 8 : ℝ) * ε ^ 2 * d * Real.sin α * (min α (Real.cos α)) ^ 2 := by gcongr
      _ ≤ effectiveN ε d q := effectiveN_geometric ε d hd hΛ hq
  rw [div_le_iff₀ hq0]
  nlinarith [mul_le_mul_of_nonneg_right hgeom' hq0.le, mul_le_mul_of_nonneg_left hqcos hεd]

/-- On the entire scale window, the effective parameter is bounded below by the minimum of
`ε² d (q - edgeQ d) √(q - edgeQ d) / 96` and `ε² d / (3000 q)`. -/
theorem effectiveN_scale_window_lower
    (ε : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ scaleLambda d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    min
        ((ε ^ 2 / 96) * d * (q - edgeQ d) *
          Real.sqrt (q - edgeQ d))
        ((ε ^ 2 / 3000) * d / q) ≤
      effectiveN ε d q := by
  by_cases hsmall : saddleAngle d q ≤ 1 / 2
  · exact (min_le_left _ _).trans
      (effectiveN_edge_lower ε d hd hΛ hq hsmall)
  · exact (min_le_right _ _).trans
      (effectiveN_tail_lower ε d hd hΛ hlarge hq (le_of_not_ge hsmall))

end RiemannJensen
