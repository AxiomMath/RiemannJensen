module

public import RiemannJensen.Analysis.SaddleDefinitions

/-!
# Field-independent saddle geometry

The saddle geometry of Dedekind zeta functions depends on the number field only through a
positive logarithmic scale `Λ`. This file defines the saddle phase, radius, level and edge as
functions of `Λ`, and identifies them at `Λ = scaleLambda d` with `phase`, `saddleRadius`,
`saddleQ` and `edgeQ`.

## Main definitions

* `saddleKappa`: The constant `κ = π / 2`.
* `saddlePhaseAtLambda`: The lower-branch saddle phase at scale `Λ`.
* `saddleRadialAtLambda`: The radial saddle equation at scale `Λ`, as left side minus right side.
* `saddleRadiusAtLambda`: The saddle radius at scale `Λ` and angle `α`.
* `saddleQAtLambda`: The saddle level at scale `Λ` and angle `α`.
* `edgeQAtLambda`: The coalescence edge of the two saddles at scale `Λ`.

## Main results

* `saddlePhaseAtLambda_scaleLambda`: `saddlePhaseAtLambda (scaleLambda d) = phase d`.
* `saddleRadiusAtLambda_scaleLambda`: `saddleRadiusAtLambda (scaleLambda d) = saddleRadius d`.
* `saddleQAtLambda_scaleLambda`: `saddleQAtLambda (scaleLambda d) = saddleQ d`.
* `edgeQAtLambda_scaleLambda`: `edgeQAtLambda (scaleLambda d) = edgeQ d`.
-/

@[expose] public section

namespace RiemannJensen

/-- The universal saddle constant `κ = π / 2`. -/
noncomputable def saddleKappa : ℝ := Real.pi / 2

/-- The lower-branch saddle phase at logarithmic scale `Λ`:
`-q u + 2κ √u + (2κ / Λ) √u log u - log u`, with the lower branches of `√` and `log`. -/
noncomputable def saddlePhaseAtLambda (Λ q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) * u + (2 * saddleKappa : ℝ) * lowerSqrt u +
    (((2 * saddleKappa / Λ : ℝ) : ℂ) * lowerSqrt u * lowerLog u) -
    lowerLog u

/-- The radial saddle equation at logarithmic scale `Λ` and angle `α`, written as left side
minus right side: `Λ cos α / (κ r) + α cot α - (Λ / 2 + 1 + log r)`. -/
noncomputable def saddleRadialAtLambda (Λ α r : ℝ) : ℝ :=
  Λ * Real.cos α / (saddleKappa * r) + alphaCot α -
    (Λ / 2 + 1 + Real.log r)

/-- The saddle radius at logarithmic scale `Λ` and angle `α`: the infimum of the positive `r`
at which `saddleRadialAtLambda Λ α r ≤ 0`. -/
noncomputable def saddleRadiusAtLambda (Λ α : ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ saddleRadialAtLambda Λ α r ≤ 0}

/-- The saddle level at logarithmic scale `Λ` and angle `α`: `r⁻¹ ^ 2 + (2κ / Λ) sinRatio α r⁻¹`,
where `r = saddleRadiusAtLambda Λ α`. -/
noncomputable def saddleQAtLambda (Λ α : ℝ) : ℝ :=
  (saddleRadiusAtLambda Λ α)⁻¹ ^ 2 +
    (2 * saddleKappa / Λ) * sinRatio α *
      (saddleRadiusAtLambda Λ α)⁻¹

/-- The coalescence edge of the two saddles at logarithmic scale `Λ`. -/
noncomputable def edgeQAtLambda (Λ : ℝ) : ℝ :=
  saddleQAtLambda Λ 0

/-- The saddle constant `saddleKappa` equals `π / 2`. -/
@[simp] theorem saddleKappa_eq : saddleKappa = Real.pi / 2 := rfl

/-- The saddle constant `saddleKappa` is positive. -/
theorem saddleKappa_pos : 0 < saddleKappa := by
  rw [saddleKappa_eq]; positivity

/-- The radial saddle equation at angle `0`. -/
@[simp] theorem saddleRadialAtLambda_zero_angle (Λ r : ℝ) :
    saddleRadialAtLambda Λ 0 r =
      Λ / (saddleKappa * r) + 1 - (Λ / 2 + 1 + Real.log r) := by
  simp [saddleRadialAtLambda]

/-- The edge `edgeQAtLambda Λ` is the saddle level at angle `0`. -/
@[simp] theorem edgeQAtLambda_eq (Λ : ℝ) :
    edgeQAtLambda Λ = saddleQAtLambda Λ 0 := rfl

/-- At `Λ = scaleLambda d` the saddle phase is `phase d`. -/
theorem saddlePhaseAtLambda_scaleLambda (d : ℕ) (q : ℝ) (u : ℂ) :
    saddlePhaseAtLambda (scaleLambda d) q u = phase d q u := by
  simp only [saddlePhaseAtLambda, saddleKappa, phase]
  push_cast
  ring

/-- At `Λ = scaleLambda d` the saddle radius is `saddleRadius d`. -/
theorem saddleRadiusAtLambda_scaleLambda (d : ℕ) (α : ℝ) :
    saddleRadiusAtLambda (scaleLambda d) α = saddleRadius d α := by
  simp only [saddleRadiusAtLambda, saddleRadius, saddleRadialAtLambda, saddleKappa, sub_nonpos]

/-- At `Λ = scaleLambda d` the saddle level is `saddleQ d`. -/
theorem saddleQAtLambda_scaleLambda (d : ℕ) (α : ℝ) :
    saddleQAtLambda (scaleLambda d) α = saddleQ d α := by
  rw [saddleQAtLambda, saddleQ, saddleRadiusAtLambda_scaleLambda, saddleKappa]
  ring

/-- At `Λ = scaleLambda d` the coalescence edge is `edgeQ d`. -/
theorem edgeQAtLambda_scaleLambda (d : ℕ) :
    edgeQAtLambda (scaleLambda d) = edgeQ d := by
  simp [edgeQAtLambda, edgeQ, saddleQAtLambda_scaleLambda]

end RiemannJensen
