module

public import RiemannJensen.Analysis.LowerBranch
public import RiemannJensen.Analysis.Scale
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Definitions for the saddle-point geometry

This file defines the phase of the Cauchy integral along the lower branch, the saddle points of
that phase, and the quantities attached to them.

## Main definitions

* `sinRatio`, `alphaCot`: the functions `α / sin α` and `α cot α`, extended continuously at `0`.
* `phase`: the lower-branch phase in the Cauchy integral.
* `saddleRadius`, `saddleQ`, `saddleAngle`: the radial coordinate, the `q`-coordinate and the
  angle of the saddle point.
* `edgeQ`: the value of `q` at which the two saddle points coalesce.
* `saddle`: the lower saddle point.
* `saddleHessian`, `localWidth`, `effectiveN`, `saddleAction`: the second-derivative coefficient,
  the local width, the effective Gaussian parameter and the real action at the saddle.

## Implementation notes

The quotients `α / sin α` and `α cos α / sin α` are used at `α = 0` through their continuous
extensions, so they are defined by cases rather than through Lean's total division, which would
give `0` there.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set

/-- The function `α / sin α`, extended continuously by `1` at `α = 0`. -/
noncomputable def sinRatio (α : ℝ) : ℝ :=
  if α = 0 then 1 else α / Real.sin α

/-- The function `α cot α`, extended continuously by `1` at `α = 0`. -/
noncomputable def alphaCot (α : ℝ) : ℝ :=
  if α = 0 then 1 else α * Real.cos α / Real.sin α

/-- `sinRatio 0 = 1`. -/
@[simp] theorem sinRatio_zero : sinRatio 0 = 1 := by
  simp [sinRatio]

/-- `alphaCot 0 = 1`. -/
@[simp] theorem alphaCot_zero : alphaCot 0 = 1 := by
  simp [alphaCot]

/-- Away from the origin, `sinRatio α = α / sin α`. -/
theorem sinRatio_of_ne {α : ℝ} (hα : α ≠ 0) :
    sinRatio α = α / Real.sin α := by
  simp [sinRatio, hα]

/-- Away from the origin, `alphaCot α = α cos α / sin α`. -/
theorem alphaCot_of_ne {α : ℝ} (hα : α ≠ 0) :
    alphaCot α = α * Real.cos α / Real.sin α := by
  simp [alphaCot, hα]

/-- The exact lower-branch phase in the Cauchy integral. -/
noncomputable def phase (d : ℕ) (q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) * u + (Real.pi : ℂ) * lowerSqrt u +
    ((Real.pi / scaleLambda d : ℝ) : ℂ) * lowerSqrt u * lowerLog u -
    lowerLog u

/-- The radial saddle coordinate, encoded as the least positive point where the decreasing radial
equation crosses zero. -/
noncomputable def saddleRadius (d : ℕ) (α : ℝ) : ℝ :=
  sInf {r : ℝ |
    0 < r ∧
      scaleLambda d * Real.cos α / ((Real.pi / 2) * r) + alphaCot α ≤
        scaleLambda d / 2 + 1 + Real.log r}

/-- The `q`-coordinate corresponding to a saddle angle. -/
noncomputable def saddleQ (d : ℕ) (α : ℝ) : ℝ :=
  (saddleRadius d α)⁻¹ ^ 2 +
    (Real.pi / scaleLambda d) * sinRatio α * (saddleRadius d α)⁻¹

/-- The coalescence edge of the two saddle points. -/
noncomputable def edgeQ (d : ℕ) : ℝ :=
  saddleQ d 0

/-- Generalized inverse of the saddle parameter on `[0, π / 2]`. -/
noncomputable def saddleAngle (d : ℕ) (q : ℝ) : ℝ :=
  sInf {α : ℝ |
    0 ≤ α ∧ α ≤ Real.pi / 2 ∧ q ≤ saddleQ d α}

/-- The lower saddle point. -/
noncomputable def saddle (d : ℕ) (q : ℝ) : ℂ :=
  ((saddleRadius d (saddleAngle d q)) ^ 2 : ℝ) *
    Complex.exp (-2 * Complex.I * (saddleAngle d q : ℂ))

/-- The angular second-derivative coefficient at the saddle. -/
noncomputable def saddleHessian (d : ℕ) (q : ℝ) : ℂ :=
  saddle d q ^ 2 * iteratedDeriv 2 (phase d q) (saddle d q)

/-- Width of the local saddle interval for a chosen positive small parameter `ε`. -/
noncomputable def localWidth (ε : ℝ) (d : ℕ) (q : ℝ) : ℝ :=
  ε * min (saddleAngle d q) (Real.cos (saddleAngle d q))

/-- The effective Gaussian parameter for a chosen local-width constant. -/
noncomputable def effectiveN (ε : ℝ) (d : ℕ) (q : ℝ) : ℝ :=
  d * ‖saddleHessian d q‖ * localWidth ε d q ^ 2

/-- The real action controlling the oscillation. -/
noncomputable def saddleAction (d : ℕ) (q : ℝ) : ℝ :=
  (phase d q (saddle d q)).im

end RiemannJensen
