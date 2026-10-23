module

public import RiemannJensen.Xi
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Algebraic foundations for Dedekind Jensen polynomials

This module records the number-field data already available in Mathlib and
builds the purely algebraic part of the Dedekind Jensen-polynomial
construction from an arbitrary candidate completed function `ξ : ℂ → ℂ`.
It deliberately does **not** define an analytic continuation of the Dedekind
zeta function: Mathlib's `NumberField.dedekindZeta` is the underlying
Dirichlet `LSeries`, not such a continuation.
-/

@[expose] public section

namespace RiemannJensen

open Complex Polynomial

section NumberFieldData

variable (K : Type*) [Field K] [NumberField K]

/-- The degree `[K : ℚ]` of a number field. -/
noncomputable def dedekindDegree : ℕ := Module.finrank ℚ K

/-- The number of real infinite places of a number field. -/
noncomputable def dedekindRealPlaces : ℕ := NumberField.InfinitePlace.nrRealPlaces K

/-- The number of complex infinite places of a number field. -/
noncomputable def dedekindComplexPlaces : ℕ := NumberField.InfinitePlace.nrComplexPlaces K

/-- The absolute value `Δ_K` of the discriminant of a number field, as a real number. -/
noncomputable def dedekindDiscriminantAbs : ℝ :=
  |(NumberField.discr K : ℝ)|

/-- The signature identity `r₁ + 2 r₂ = [K : ℚ]`. -/
theorem dedekind_signature :
    dedekindRealPlaces K + 2 * dedekindComplexPlaces K = dedekindDegree K :=
  NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

/-- Every number field has positive degree. -/
theorem dedekindDegree_pos : 0 < dedekindDegree K :=
  Module.finrank_pos

/-- The absolute discriminant is strictly positive. -/
theorem dedekindDiscriminantAbs_pos : 0 < dedekindDiscriminantAbs K := by
  rw [dedekindDiscriminantAbs, abs_pos]
  exact_mod_cast NumberField.discr_ne_zero K

/-- The Dedekind zeta function of `K` as the Dirichlet series `NumberField.dedekindZeta`,
without analytic continuation. -/
noncomputable def rawDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

end NumberFieldData

/-- Deligne's real archimedean Gamma factor. -/
noncomputable def dedekindGammaR (s : ℂ) : ℂ := Complex.Gammaℝ s

/-- Deligne's complex archimedean Gamma factor, with its leading factor `2`. -/
noncomputable def dedekindGammaC (s : ℂ) : ℂ := Complex.Gammaℂ s

/-- `dedekindGammaR s = π ^ (-s / 2) * Γ(s / 2)`. -/
@[simp] theorem dedekindGammaR_eq (s : ℂ) :
    dedekindGammaR s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
  Complex.Gammaℝ_def s

/-- `dedekindGammaC s = 2 * (2π) ^ (-s) * Γ(s)`. -/
@[simp] theorem dedekindGammaC_eq (s : ℂ) :
    dedekindGammaC s = 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s :=
  Complex.Gammaℂ_def s

section JensenData

/-- The power series `∑ j, γ_j / j! * z ^ j` in the square variable, where `γ_j` are the
coefficients `dedekindGammaCoeff ξ j` of a candidate completed function `ξ`. -/
noncomputable def dedekindF (ξ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, (dedekindGammaCoeff ξ j : ℂ) / (j.factorial : ℂ) * z ^ j

/-- The formal-degree-`d` reciprocal.  Unlike `Polynomial.reverse`, this is
padded to the prescribed degree even if the top Taylor coefficients vanish. -/
noncomputable def dedekindReciprocal (ξ : ℂ → ℂ) (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1),
    C ((d.choose j : ℝ) * dedekindGammaCoeff ξ j) * X ^ (d - j)

/-- Coefficients of the Dedekind Jensen polynomial. -/
theorem coeff_dedekindJensen (ξ : ℂ → ℂ) (d j : ℕ) :
    (dedekindJensen ξ d).coeff j =
      if j ≤ d then (d.choose j : ℝ) * dedekindGammaCoeff ξ j else 0 := by
  simp only [dedekindJensen, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (d + 1)) j]
  simp [Finset.mem_range]

/-- The prescribed formal degree bounds the actual natural degree. -/
theorem natDegree_dedekindJensen_le (ξ : ℂ → ℂ) (d : ℕ) :
    (dedekindJensen ξ d).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_dedekindJensen]
  simp [Nat.not_le_of_lt hn]

/-- A nonzero Taylor coefficient in range makes the Jensen polynomial
nonzero. -/
theorem dedekindJensen_ne_zero_of_coeff_ne_zero (ξ : ℂ → ℂ) {m d : ℕ} (hmd : m ≤ d)
    (hm : dedekindGammaCoeff ξ m ≠ 0) : dedekindJensen ξ d ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff m) hzero
  rw [coeff_dedekindJensen, ite_eq_left hmd, Polynomial.coeff_zero] at hcoeff
  have hchoose : (d.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmd).ne'
  exact hm ((mul_eq_zero.mp hcoeff).resolve_left hchoose)

/-- Once one Taylor coefficient is nonzero, every Jensen polynomial of at
least that index is nonzero. -/
theorem eventually_dedekindJensen_ne_zero_of_coeff_ne_zero (ξ : ℂ → ℂ)
    {m : ℕ} (hm : dedekindGammaCoeff ξ m ≠ 0) :
    ∀ d ≥ m, dedekindJensen ξ d ≠ 0 :=
  fun _ hd => dedekindJensen_ne_zero_of_coeff_ne_zero ξ hd hm

/-- A single nonzero Taylor coefficient supplies an explicit eventual
nonvanishing threshold. -/
theorem exists_eventually_dedekindJensen_ne_zero (ξ : ℂ → ℂ)
    (hξ : ∃ m, dedekindGammaCoeff ξ m ≠ 0) :
    ∃ D, ∀ d ≥ D, dedekindJensen ξ d ≠ 0 := by
  obtain ⟨m, hm⟩ := hξ
  exact ⟨m, eventually_dedekindJensen_ne_zero_of_coeff_ne_zero ξ hm⟩

/-- Evaluation of the Dedekind Jensen polynomial as its defining finite sum. -/
theorem eval_dedekindJensen (ξ : ℂ → ℂ) (d : ℕ) (x : ℝ) :
    (dedekindJensen ξ d).eval x =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℝ) * dedekindGammaCoeff ξ j * x ^ j := by
  simp only [dedekindJensen, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluation of the degree-padded reciprocal polynomial. -/
theorem eval_dedekindReciprocal (ξ : ℂ → ℂ) (d : ℕ) (x : ℝ) :
    (dedekindReciprocal ξ d).eval x =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℝ) * dedekindGammaCoeff ξ j * x ^ (d - j) := by
  simp only [dedekindReciprocal, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- For `x ≠ 0`, the padded reciprocal evaluates to `x ^ d * (dedekindJensen ξ d).eval x⁻¹`. -/
theorem eval_dedekindReciprocal_eq (ξ : ℂ → ℂ) (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (dedekindReciprocal ξ d).eval x =
      x ^ d * (dedekindJensen ξ d).eval x⁻¹ := by
  rw [eval_dedekindReciprocal, eval_dedekindJensen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [pow_sub₀ x hx (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  ring

end JensenData

end RiemannJensen
