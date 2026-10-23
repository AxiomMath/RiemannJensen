module

public import RiemannJensen.Dedekind.SaddleHessianAdapters

/-!
# Eventual Dedekind saddle and Hessian bounds

For a number field `K`, the saddle radius, edge level, circle phase and saddle Hessian at the
Dedekind logarithmic scale `dedekindScaleLambda K d` satisfy explicit bounds for every
sufficiently large degree `d`.

## Main results

* `eventually_const_le_dedekindScaleLambda`: `dedekindScaleLambda K d` eventually exceeds every
  real constant.
* `eventually_dedekindSaddleRadius_level_comparison`: the saddle radius is eventually comparable
  to `1 / √(dedekindSaddleQ K d α)`.
* `eventually_dedekindSaddleCos_radius_comparison`: `cos α` is eventually comparable to the
  saddle radius on the saddle branch.
* `eventually_dedekindEdgeQ_le_two`: the edge level is eventually at most `2`.
* `eventually_dedekindSaddleQ_sub_edge_lower`, `eventually_dedekindSaddleQ_sub_edge_upper`:
  quadratic bounds on the saddle level minus the edge level.
* `eventually_dedekindCircleRealPhaseZSecond_le_neg_three`: the circle phase is eventually
  uniformly concave in `z`.
* `eventually_dedekindSaddlePhase_circle_quadratic_gap`: a quadratic gap for the real part of
  the saddle phase along the saddle circle.
* `eventually_dedekindSaddleHessian_re_bounds`, `eventually_dedekindSaddleHessian_norm_bounds`:
  bounds on the real part and the norm of the saddle Hessian.
-/

@[expose] public section

namespace RiemannJensen

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- Every fixed real lower bound is eventually dominated by the Dedekind
logarithmic scale. -/
theorem eventually_const_le_dedekindScaleLambda (C : ℝ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, C ≤ dedekindScaleLambda K d := by
  obtain ⟨D₁, hD₁⟩ := eventually_log_le_dedekindScaleLambda K
  obtain ⟨D₂, hD₂⟩ := exists_nat_ge (Real.exp C)
  refine ⟨max (max D₁ D₂) 1, le_max_right _ _, fun d hd => ?_⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact ((Real.le_log_iff_exp_le hdpos).2
    (hD₂.trans (by exact_mod_cast (by omega : D₂ ≤ d)))).trans (hD₁ d (by omega))

/-- If `4 (1 + log (dedekindScaleA K)) ≤ dedekindScaleLambda K d`, then the logarithm of the
Dedekind scale coordinate `dedekindScaleT K d` is at most `3/4` of `dedekindScaleLambda K d`. -/
theorem log_dedekindScaleT_le_three_mul_lambda_div_four (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d) :
    Real.log (dedekindScaleT K d) ≤ 3 * dedekindScaleLambda K d / 4 := by
  have hA : 0 < dedekindScaleA K := by
    unfold dedekindScaleA
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)
  have hcoord := dedekindScaleLambda_div_two K d
  rw [Real.log_div (dedekindScaleT_pos K d hd).ne' hA.ne'] at hcoord
  linarith

/-- For all sufficiently large `d` and all `α ∈ [0, π/2]`, the Dedekind saddle radius lies
between `1 / √q` and `√2 / √q`, where `q = dedekindSaddleQ K d α`. -/
theorem eventually_dedekindSaddleRadius_level_comparison :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      1 / Real.sqrt (dedekindSaddleQ K d α) ≤ dedekindSaddleRadius K d α ∧
        dedekindSaddleRadius K d α ≤
          Real.sqrt 2 / Real.sqrt (dedekindSaddleQ K d α) := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  refine ⟨max D₀ 1, le_max_right _ _, fun d hd α hα => ?_⟩
  have := hD₀ d (by omega)
  exact dedekindSaddleRadius_level_comparison K d (by linarith [Real.pi_pos]) hα

/-- For all sufficiently large `d` and all `α ∈ [0, π/2]` with
`dedekindSaddleQ K d α ≤ dedekindScaleT K d`, the Dedekind saddle radius `r` satisfies
`π r / 16 ≤ cos α ≤ π r / 2`. -/
theorem eventually_dedekindSaddleCos_radius_comparison :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      dedekindSaddleQ K d α ≤ dedekindScaleT K d →
        Real.pi * dedekindSaddleRadius K d α / 16 ≤ Real.cos α ∧
          Real.cos α ≤ Real.pi * dedekindSaddleRadius K d α / 2 := by
  obtain ⟨D, hD1, hD⟩ := eventually_const_le_dedekindScaleLambda K
    (max (2 * (1 + Real.log 2)) (4 * (1 + Real.log (dedekindScaleA K))))
  refine ⟨D, hD1, fun d hd α hα hq => ?_⟩
  have hC := max_le_iff.1 (hD d hd)
  exact dedekindSaddleCos_radius_comparison K d hC.1 (dedekindScaleT_pos K d (hD1.trans hd))
    (log_dedekindScaleT_le_three_mul_lambda_div_four K d (hD1.trans hd) hC.2) hα hq

/-- For all sufficiently large `d`, the Dedekind edge level `dedekindEdgeQ K d` is at most `2`. -/
theorem eventually_dedekindEdgeQ_le_two :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, dedekindEdgeQ K d ≤ 2 := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  refine ⟨max D₀ 1, le_max_right _ _, fun d hd => ?_⟩
  have := hD₀ d (by omega)
  exact dedekindEdgeQ_le_two K d (by linarith [Real.pi_pos])

/-- For all sufficiently large `d` and all `α ∈ [0, π/2]`,
`α ^ 2 / 50 ≤ dedekindSaddleQ K d α - dedekindEdgeQ K d`. -/
theorem eventually_dedekindSaddleQ_sub_edge_lower :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      α ^ 2 / 50 ≤ dedekindSaddleQ K d α - dedekindEdgeQ K d := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  exact ⟨max D₀ 1, le_max_right _ _, fun d hd α hα =>
    dedekindSaddleQ_sub_edge_lower K d (hD₀ d (by omega)) hα⟩

/-- For all sufficiently large `d` and all `α ∈ [0, 1/2]`,
`dedekindSaddleQ K d α - dedekindEdgeQ K d ≤ 6 * α ^ 2`. -/
theorem eventually_dedekindSaddleQ_sub_edge_upper :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Icc 0 (1 / 2 : ℝ),
      dedekindSaddleQ K d α - dedekindEdgeQ K d ≤ 6 * α ^ 2 := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  exact ⟨max D₀ 1, le_max_right _ _, fun d hd α hα =>
    dedekindSaddleQ_sub_edge_upper K d (hD₀ d (by omega)) hα⟩

/-- For all sufficiently large `d`, all `α ∈ [0, π/2]` and all `z ∈ (0, 1)`, the second
`z`-derivative `circleRealPhaseZSecondAtLambda` of the real circle phase at the Dedekind scale is
at most `-3`. -/
theorem eventually_dedekindCircleRealPhaseZSecond_le_neg_three :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      ∀ z ∈ Set.Ioo 0 1,
        circleRealPhaseZSecondAtLambda (dedekindScaleLambda K d) α z ≤ -3 := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  exact ⟨max D₀ 1, le_max_right _ _, fun d hd α hα z hz =>
    dedekindCircleRealPhaseZSecond_le_neg_three K d (hD₀ d (by omega)) hα hz⟩

/-- For all sufficiently large `d`, all `α ∈ (0, π/2]` and all `β ∈ [0, π/2]`, with `r` the
Dedekind saddle radius at `α`, the real part of the Dedekind saddle phase at level
`dedekindSaddleQ K d α` is at least `(3/2) (cos β - cos α) ^ 2` larger at `r ^ 2 e^{-2iα}` than
at `r ^ 2 e^{-2iβ}`. -/
theorem eventually_dedekindSaddlePhase_circle_quadratic_gap :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Ioc 0 (Real.pi / 2),
      ∀ β ∈ Set.Icc 0 (Real.pi / 2),
      (3 / 2 : ℝ) * (Real.cos β - Real.cos α) ^ 2 ≤
        (dedekindSaddlePhase K d (dedekindSaddleQ K d α)
          ((((dedekindSaddleRadius K d α) ^ 2 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((-2 * α : ℝ) : ℂ))))).re -
        (dedekindSaddlePhase K d (dedekindSaddleQ K d α)
          ((((dedekindSaddleRadius K d α) ^ 2 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((-2 * β : ℝ) : ℂ))))).re := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  exact ⟨max D₀ 1, le_max_right _ _, fun d hd α hα β hβ =>
    dedekindSaddlePhase_circle_quadratic_gap K d (hD₀ d (by omega)) hα hβ⟩

/-- For all sufficiently large `d` and all `α ∈ (0, π/2)`, the real part of the Dedekind saddle
Hessian at level `dedekindSaddleQ K d α` lies between `sin α ^ 2` and `2 sin α ^ 2`. -/
theorem eventually_dedekindSaddleHessian_re_bounds :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin α ^ 2 ≤
          (dedekindSaddleHessian K d (dedekindSaddleQ K d α)).re ∧
        (dedekindSaddleHessian K d (dedekindSaddleQ K d α)).re ≤
          2 * Real.sin α ^ 2 := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  refine ⟨max D₀ 1, le_max_right _ _, fun d hd α hα => ?_⟩
  have := hD₀ d (by omega)
  exact dedekindSaddleHessian_re_bounds K d (by omega) (by linarith [Real.pi_pos]) hα

/-- For all sufficiently large `d` and all `α ∈ (0, π/2)`, the norm of the Dedekind saddle
Hessian at level `dedekindSaddleQ K d α` lies between `(3/8) sin α` and `4 sin α`. -/
theorem eventually_dedekindSaddleHessian_norm_bounds :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D, ∀ α ∈ Set.Ioo 0 (Real.pi / 2),
      (3 / 8 : ℝ) * Real.sin α ≤
          ‖dedekindSaddleHessian K d (dedekindSaddleQ K d α)‖ ∧
        ‖dedekindSaddleHessian K d (dedekindSaddleQ K d α)‖ ≤
          4 * Real.sin α := by
  obtain ⟨D₀, hD₀⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  exact ⟨max D₀ 1, le_max_right _ _, fun d hd α hα =>
    dedekindSaddleHessian_norm_bounds K d (by omega) (hD₀ d (by omega)) hα⟩

end

end RiemannJensen
