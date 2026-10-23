module

public import RiemannJensen.Dedekind.CauchyRepresentation
public import RiemannJensen.Dedekind.CompletedZetaAdapter
public import RiemannJensen.Dedekind.ScaleLemmas

/-!
# Field-level Cauchy representation for Dedekind Jensen polynomials

For a number field `K`, the rescaled Dedekind Jensen polynomial `rescaledDedekindJensenK K d` is
expressed as a Cauchy integral over a circle, at the completed Dedekind xi-function
`entireDedekindXi K` and the saddle scale `dedekindScaleT K d`.

## Main results

* `dedekind_cauchy`: Cauchy representation of `rescaledDedekindJensenK K d` at the completed
  Dedekind xi-function `entireDedekindXi K` and the saddle scale `dedekindScaleT K d`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial

variable (K : Type) [Field K] [NumberField K]

/-- Cauchy representation of `rescaledDedekindJensenK K d` at the completed Dedekind xi-function
`entireDedekindXi K` and the saddle scale `dedekindScaleT K d`. -/
theorem dedekind_cauchy (d : ℕ) (hd : 1 ≤ d) (x ρ : ℝ) (hρ : 0 < ρ) :
    (↑((rescaledDedekindJensenK K d).eval x) : ℂ) =
      ((d.factorial : ℂ) / ((2 : ℂ) * Real.pi * Complex.I * (d : ℂ) ^ d)) *
        (∮ u : ℂ in C(0, ρ),
          dedekindF (entireDedekindXi K) (((dedekindScaleT K d) ^ 2 : ℝ) * u) *
              Complex.exp (((d : ℝ) * x : ℝ) * u) /
            u ^ (d + 1)) := by
  simpa [rescaledDedekindJensenK, rescaledDedekindReciprocal,
    dedekindReciprocalK, dedekindCauchyNumerator] using
    (dedekind_cauchy_representation (entireDedekindXi_entire K)
      (entireDedekindXi_conj K) d hd (dedekindScaleT K d) (dedekindScaleT_pos K d hd).ne' x ρ hρ)

end RiemannJensen
