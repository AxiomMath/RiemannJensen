module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Jensen polynomials of the Riemann and Dedekind xi functions

The Taylor coefficients of the Riemann xi function and of the completed Dedekind xi function
of a number field at the symmetry point `1 / 2`, the associated Jensen polynomials, and the
counts of their nonreal and negative real roots.

## Main definitions

* `riemannXi`: Riemann's entire xi function.
* `jensenPolynomial`: The degree-`d` Jensen polynomial of Riemann xi.
* `nonrealJensenRootCount`: The number of nonreal roots of `jensenPolynomial d`.
* `negativeJensenRootCount`: The number of distinct negative real roots of `jensenPolynomial d`.
* `IsDedekindZetaContinuation`: Analytic continuations of the Dedekind zeta function.
* `dedekindXi`: The completed Dedekind xi function of a number field.
* `dedekindJensenK`: The degree-`d` Dedekind Jensen polynomial of a number field.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial

/-- Riemann's entire xi function, `ξ(s) = (s (s - 1) Λ₀(s) + 1) / 2`, where `Λ₀` is
Mathlib's entire part of the completed Riemann zeta function. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The xi function centered at the symmetry point `1 / 2`. -/
noncomputable def centeredXi (w : ℂ) : ℂ :=
  riemannXi (1 / 2 + w)

/-- The coefficient `γ(j)` in `ξ(1 / 2 + w) = ∑ j, γ(j) / j! * w ^ (2 * j)`, read off
from the `2j`-th derivative of the centered xi function at `0`. -/
noncomputable def gammaCoeff (j : ℕ) : ℝ :=
  ((j.factorial : ℝ) / ((2 * j).factorial : ℝ)) *
    (iteratedDeriv (2 * j) centeredXi 0).re

/-- The degree-`d` Jensen polynomial `∑_{j ≤ d} (d choose j) γ(j) X ^ j` of Riemann xi. -/
noncomputable def jensenPolynomial (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1),
    C ((d.choose j : ℝ) * gammaCoeff j) * X ^ j

/-- The number of nonreal roots of a real polynomial, counted with algebraic multiplicity
in its complex root multiset. -/
noncomputable def nonrealRootCount (p : ℝ[X]) : ℕ :=
  ((p.map Complex.ofRealHom).roots.filter fun z : ℂ => z.im ≠ 0).card

/-- The number of nonreal roots of the degree-`d` Riemann Jensen polynomial. -/
noncomputable def nonrealJensenRootCount (d : ℕ) : ℕ :=
  nonrealRootCount (jensenPolynomial d)

/-- The number of distinct negative real roots of a real polynomial (the zero polynomial
has none). -/
noncomputable def negativeDistinctRootCount (p : ℝ[X]) : ℕ :=
  (p.roots.toFinset.filter fun x : ℝ => x < 0).card

/-- The number of distinct negative real roots of the degree-`d` Riemann Jensen
polynomial. -/
noncomputable def negativeJensenRootCount (d : ℕ) : ℕ :=
  negativeDistinctRootCount (jensenPolynomial d)

/-- A function `ξ : ℂ → ℂ` centered at `1 / 2`. -/
noncomputable def centeredDedekindFunction (ξ : ℂ → ℂ) (w : ℂ) : ℂ :=
  ξ (1 / 2 + w)

/-- The real coefficient `(j! / (2j)!) · Re ξ^{(2j)}(1 / 2)` attached to `ξ`. -/
noncomputable def dedekindGammaCoeff (ξ : ℂ → ℂ) (j : ℕ) : ℝ :=
  ((j.factorial : ℝ) / ((2 * j).factorial : ℝ)) *
    (iteratedDeriv (2 * j) (centeredDedekindFunction ξ) 0).re

/-- The degree-`d` Jensen polynomial attached to the coefficients of `ξ`. -/
noncomputable def dedekindJensen (ξ : ℂ → ℂ) (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1),
    C ((d.choose j : ℝ) * dedekindGammaCoeff ξ j) * X ^ j

/-- The number of distinct negative real roots of the degree-`d` Jensen polynomial
attached to `ξ`. -/
noncomputable def dedekindNegativeRootCount (ξ : ℂ → ℂ) (d : ℕ) : ℕ :=
  negativeDistinctRootCount (dedekindJensen ξ d)

/-- `f : ℂ → ℂ` is an analytic continuation of the Dedekind zeta function `ζ_K` of the number
field `K`: it is holomorphic on `ℂ \ {1}` and equals the Dirichlet series `ζ_K(s)` for
`Re s > 1`. The construction of such a continuation is missing in Mathlib but supplied in this
repository. -/
structure IsDedekindZetaContinuation (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ) :
    Prop where
  differentiableOn : DifferentiableOn ℂ f {1}ᶜ
  eq_dedekindZeta : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s

/-- The Dedekind zeta function `ζ_K` of `K`, continued analytically to `ℂ \ {1}`. -/
noncomputable def continuedDedekindZeta (K : Type) [Field K] [NumberField K] : ℂ → ℂ :=
  Classical.epsilon (IsDedekindZetaContinuation K)

/-- The completed Dedekind zeta function
`Λ_K(s) = |Δ_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)`, where `r₁` and `r₂` are the numbers of
real and complex places of `K`. -/
noncomputable def completedDedekindZeta (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2) *
    Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K *
    continuedDedekindZeta K s

/-- The completed Dedekind xi function `ξ_K(s) = s (s - 1) Λ_K(s) / 2`. It agrees with the
entire xi function of `K` except at `1` and at the non-positive integers, where the Gamma
factors have poles. -/
noncomputable def dedekindXi (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  s * (s - 1) * completedDedekindZeta K s / 2

/-- The degree-`d` Dedekind Jensen polynomial of the number field `K`. -/
noncomputable def dedekindJensenK (K : Type) [Field K] [NumberField K] (d : ℕ) : ℝ[X] :=
  dedekindJensen (dedekindXi K) d

/-- The number of distinct negative real roots of the degree-`d` Dedekind Jensen
polynomial of `K`. -/
noncomputable def dedekindNegativeRootCountK (K : Type) [Field K] [NumberField K] (d : ℕ) :
    ℕ :=
  dedekindNegativeRootCount (dedekindXi K) d

end RiemannJensen
