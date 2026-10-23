module

public import RiemannJensen.Dedekind.ContinuedZeta
public import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Dedekind Euler logarithm

The logarithm of the Euler product of the Dedekind zeta function of a number field `K`, as the
double series `∑_𝔭 ∑_{m ≥ 1} N(𝔭)^{-ms} / m` over the height-one primes of `𝓞 K`. The
natural-number index `m` below represents the positive exponent `m + 1`.

## Main definitions

* `dedekindEulerLogTerm`: The summand `N(𝔭)^{-(m+1)s} / (m + 1)`.
* `dedekindEulerLog`: The double series for `1 < re s`, and `0` otherwise.

## Main results

* `two_le_absNorm_heightOne`: A height-one prime has absolute norm at least two.
* `analyticDedekindZeta_eq_dirichletSeries`: For `1 < re s`, `analyticDedekindZeta K s` equals
  `NumberField.dedekindZeta K s`.
-/

@[expose] public section

namespace RiemannJensen

open Complex NumberField IsDedekindDomain

noncomputable section

/-- One summand in the prime-ideal logarithm, with the natural index `m`
representing the positive integer `m + 1`. -/
def dedekindEulerLogTerm (K : Type) [Field K] [NumberField K] (s : ℂ)
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ) : ℂ :=
  ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s) /
    ((m + 1 : ℕ) : ℂ)

/-- The Dedekind Euler logarithm.  It is totalized by zero outside its
half-plane of absolute convergence. -/
def dedekindEulerLog (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  if 1 < s.re then
    ∑' p : HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∑' m : ℕ, dedekindEulerLogTerm K s p m
  else 0

/-- For `1 < re s`, `dedekindEulerLog K s` is the double series of `dedekindEulerLogTerm`. -/
@[simp] theorem dedekindEulerLog_of_one_lt_re
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : 1 < s.re) :
    dedekindEulerLog K s =
      ∑' p : HeightOneSpectrum (NumberField.RingOfIntegers K),
        ∑' m : ℕ, dedekindEulerLogTerm K s p m := by
  rw [dedekindEulerLog, ite_eq_left hs]

/-- For `re s ≤ 1`, `dedekindEulerLog K s` is zero. -/
@[simp] theorem dedekindEulerLog_of_re_le_one
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : s.re ≤ 1) : dedekindEulerLog K s = 0 := by
  rw [dedekindEulerLog, ite_eq_right (not_lt.mpr hs)]

/-- A height-one prime of `𝓞 K` has absolute norm at least two. -/
theorem two_le_absNorm_heightOne
    (K : Type) [Field K] [NumberField K]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    2 ≤ Ideal.absNorm p.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm p

/-- For `1 < re s`, `analyticDedekindZeta K s` equals the Dirichlet series
`NumberField.dedekindZeta K s`. -/
theorem analyticDedekindZeta_eq_dirichletSeries
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : 1 < s.re) :
    analyticDedekindZeta K s = NumberField.dedekindZeta K s :=
  analyticDedekindZeta_eq_raw K s hs

end

end RiemannJensen
