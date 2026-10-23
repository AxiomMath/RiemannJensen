module

public import RiemannJensen.Dedekind.Foundation

/-!
# Elementary field-dependent constants for the Dedekind saddle analysis

This module records the constants that do not depend on the analytic
continuation of the Dedekind zeta function.  Real powers are written
explicitly with `Real.rpow`.
-/

@[expose] public section

namespace RiemannJensen

variable (K : Type*) [Field K] [NumberField K]

/-- The positive constant `a_K = 2π Δ_K^{-1/N}` used to define the
Dedekind saddle scale. -/
noncomputable def dedekindScaleA : ℝ :=
  2 * Real.pi *
    Real.rpow (dedekindDiscriminantAbs K)
      (-(1 / (dedekindDegree K : ℝ)))

/-- The fixed local-width constant used throughout the saddle argument. -/
noncomputable def dedekindLocalEpsilon : ℝ := 1 / 1000

/-- The power of the saddle variable in the Dedekind amplitude. -/
noncomputable def dedekindPowerExponent : ℝ :=
  2 - (dedekindRealPlaces K : ℝ) / 4

/-- The field-dependent leading constant in the exact Dedekind
archimedean factorization. -/
noncomputable def dedekindLeadingConstant : ℝ :=
  Real.rpow 2
      (3 * (dedekindRealPlaces K : ℝ) / 4 +
        (dedekindComplexPlaces K : ℝ) - 1) *
    Real.rpow Real.pi ((dedekindRealPlaces K : ℝ) / 4) *
    Real.rpow (dedekindDiscriminantAbs K) (1 / 4)

/-- The offset from the coalescence edge used in the counting window. -/
noncomputable def dedekindEdgeOffset (M : ℝ) (d : ℕ) : ℝ :=
  M * Real.sqrt (Real.log d / d)

end RiemannJensen
