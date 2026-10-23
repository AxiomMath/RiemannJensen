module

public import RiemannJensen.Dedekind.GeometryDefs
public import RiemannJensen.Dedekind.ScaleData
public import RiemannJensen.Dedekind.XiConsequences
public import RiemannJensen.Dedekind.ContinuedZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Field-dependent Dedekind saddle definitions

This file specializes the field-independent logarithmic saddle geometry to the scale of a
number field `K`: the saddle scale `dedekindScaleT`, the saddle phase and its lower saddle, the
Stirling remainders, the leading saddle contribution, and the window on which phase crossings
are counted.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Polynomial

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The degree-dependent Dedekind saddle scale. -/
noncomputable def dedekindScaleT (d : ℕ) : ℝ :=
  sInf {t : ℝ |
    dedekindScaleA K * Real.exp 1 < t ∧
      (d : ℝ) ≤ (dedekindDegree K : ℝ) * t / (2 * Real.pi) *
        (Real.log (t / dedekindScaleA K) - 1)}

/-- Twice the logarithmic coordinate of the Dedekind saddle scale. -/
noncomputable def dedekindScaleLambda (d : ℕ) : ℝ :=
  2 * (Real.log (dedekindScaleT K d / dedekindScaleA K) - 1)

/-- The degree-padded reciprocal in the Dedekind saddle normalization. -/
noncomputable def rescaledDedekindJensenK (d : ℕ) : ℝ[X] :=
  C (((dedekindScaleT K d) ^ 2 / (d : ℝ)) ^ d) *
    (dedekindReciprocalK K d).comp
      (C ((d : ℝ) / (dedekindScaleT K d) ^ 2) * X)

/-- The Dedekind saddle phase at degree `d` and parameter `q`. -/
noncomputable def dedekindSaddlePhase (d : ℕ) (q : ℝ) (u : ℂ) : ℂ :=
  saddlePhaseAtLambda (dedekindScaleLambda K d) q u

/-- The positive radial coordinate, totalized as an infimum. -/
noncomputable def dedekindSaddleRadius (d : ℕ) (α : ℝ) : ℝ :=
  saddleRadiusAtLambda (dedekindScaleLambda K d) α

/-- The saddle parameter corresponding to an angle. -/
noncomputable def dedekindSaddleQ (d : ℕ) (α : ℝ) : ℝ :=
  saddleQAtLambda (dedekindScaleLambda K d) α

/-- The coalescence edge of the two Dedekind saddles. -/
noncomputable def dedekindEdgeQ (d : ℕ) : ℝ :=
  dedekindSaddleQ K d 0

/-- The generalized inverse saddle angle on the closed lower quadrant. -/
noncomputable def dedekindSaddleAngle (d : ℕ) (q : ℝ) : ℝ :=
  sInf {α : ℝ |
    0 ≤ α ∧ α ≤ Real.pi / 2 ∧ q ≤ dedekindSaddleQ K d α}

/-- The lower Dedekind saddle. -/
noncomputable def dedekindSaddle (d : ℕ) (q : ℝ) : ℂ :=
  ((dedekindSaddleRadius K d (dedekindSaddleAngle K d q)) ^ 2 : ℝ) *
    Complex.exp (-2 * Complex.I * (dedekindSaddleAngle K d q : ℂ))

/-- The angular second-derivative coefficient at the Dedekind saddle. -/
noncomputable def dedekindSaddleHessian (d : ℕ) (q : ℝ) : ℂ :=
  dedekindSaddle K d q ^ 2 *
    iteratedDeriv 2 (dedekindSaddlePhase K d q) (dedekindSaddle K d q)

/-- The local angular width about a Dedekind saddle. -/
noncomputable def dedekindLocalWidth (d : ℕ) (q : ℝ) : ℝ :=
  dedekindLocalEpsilon *
    min (dedekindSaddleAngle K d q)
      (Real.cos (dedekindSaddleAngle K d q))

/-- The normalized shifted real-Gamma Stirling remainder. -/
noncomputable def dedekindGammaRemainderReal (w : ℂ) : ℂ :=
  Complex.Gamma (w / 2 + 1 / 4) /
    (Complex.sqrt (2 * Real.pi) *
      Complex.cpow (w / 2) (w / 2 - 1 / 4) *
      Complex.exp (-w / 2))

/-- The normalized shifted complex-Gamma Stirling remainder. -/
noncomputable def dedekindGammaRemainderComplex (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1 / 2) /
    (Complex.sqrt (2 * Real.pi) * Complex.cpow w w * Complex.exp (-w))

/-- The combined Dedekind archimedean Stirling remainder. -/
noncomputable def dedekindGammaRemainder (w : ℂ) : ℂ :=
  (1 - 1 / (4 * w ^ 2)) *
    dedekindGammaRemainderReal w ^ dedekindRealPlaces K *
    dedekindGammaRemainderComplex w ^ dedekindComplexPlaces K

/-- The point of the original `w`-contour corresponding to angle `θ`. -/
noncomputable def dedekindContourW (d : ℕ) (q θ : ℝ) : ℂ :=
  (dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) : ℝ) *
    Complex.exp (Complex.I * (θ : ℂ) / 2)

/-- The nonexponential amplitude on the Dedekind saddle circle. -/
noncomputable def dedekindAmplitude (d : ℕ) (q θ : ℝ) : ℂ :=
  (dedekindLeadingConstant K : ℂ) *
    Complex.cpow (dedekindContourW K d q θ) (dedekindPowerExponent K) *
    analyticDedekindZeta K (1 / 2 + dedekindContourW K d q θ) *
    dedekindGammaRemainder K (dedekindContourW K d q θ)

/-- The real saddle action controlling oscillation. -/
noncomputable def dedekindSaddleAction (d : ℕ) (q : ℝ) : ℝ :=
  (dedekindSaddlePhase K d q (dedekindSaddle K d q)).im

/-- The effective Gaussian parameter on the local saddle arc. -/
noncomputable def dedekindEffectiveN (d : ℕ) (q : ℝ) : ℝ :=
  d * ‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2

/-- The principal lower-saddle contribution. -/
noncomputable def dedekindLeadingSaddle (d : ℕ) (q : ℝ) : ℂ :=
  ((d.factorial : ℂ) / (d : ℂ) ^ d) *
    (dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q) *
      Complex.exp ((d : ℂ) *
        dedekindSaddlePhase K d q (dedekindSaddle K d q))) /
    Complex.sqrt (2 * Real.pi * d * dedekindSaddleHessian K d q)

/-- The upper endpoint of the phase-counting window. -/
noncomputable def dedekindUpperEndpoint (c₀ : ℝ) (d : ℕ) : ℝ :=
  c₀ * dedekindScaleT K d

/-- The closed interval on which phase crossings are counted. -/
noncomputable def dedekindCountingWindow (M c₀ : ℝ) (d : ℕ) : Set ℝ :=
  Set.Icc
    (dedekindEdgeQ K d + dedekindEdgeOffset M d)
    (dedekindUpperEndpoint K c₀ d)

/-- The Dedekind saddle phase is `-q u + 2κ √u + (2κ / Λ) √u log u - log u`, where
`κ = saddleKappa`, `Λ = dedekindScaleLambda K d`, and `√u`, `log u` are `lowerSqrt u` and
`lowerLog u`. -/
@[simp] theorem dedekindSaddlePhase_eq (d : ℕ) (q : ℝ) (u : ℂ) :
    dedekindSaddlePhase K d q u =
      -(q : ℂ) * u + (2 * saddleKappa : ℝ) * lowerSqrt u +
        (((2 * saddleKappa / dedekindScaleLambda K d : ℝ) : ℂ) *
          lowerSqrt u * lowerLog u) - lowerLog u := by
  rfl

/-- The coalescence edge is the saddle parameter at angle `0`. -/
@[simp] theorem dedekindEdgeQ_eq (d : ℕ) :
    dedekindEdgeQ K d = dedekindSaddleQ K d 0 := rfl

end

end RiemannJensen
