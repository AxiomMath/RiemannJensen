module

public import RiemannJensen.Xi
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Elementary facts about the Riemann Jensen polynomials

Algebraic and root-counting facts about the Jensen polynomials. In particular, sufficiently many
distinct negative roots force a corresponding upper bound on the number of roots which are not
real.
-/

@[expose] public section

namespace RiemannJensen

open Polynomial

/-- The coefficient of `X ^ j` in the degree-`d` Jensen polynomial. -/
theorem coeff_jensenPolynomial (d j : ℕ) :
    (jensenPolynomial d).coeff j = if j ≤ d then (d.choose j : ℝ) * gammaCoeff j else 0 := by
  classical
  simp only [jensenPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (d + 1)) j]
  simp [Finset.mem_range]

/-- The coefficient of `X ^ d` in `jensenPolynomial d` is `gammaCoeff d`. -/
theorem coeff_jensenPolynomial_self (d : ℕ) : (jensenPolynomial d).coeff d = gammaCoeff d := by
  simp [coeff_jensenPolynomial]

/-- The Jensen polynomial indexed by `d` has natural degree at most `d`. -/
theorem natDegree_jensenPolynomial_le (d : ℕ) : (jensenPolynomial d).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_jensenPolynomial]
  simp [Nat.not_le_of_lt hn]

/-- If `gammaCoeff d ≠ 0`, then `jensenPolynomial d` has natural degree exactly `d`. -/
theorem natDegree_jensenPolynomial (d : ℕ) (hgamma : gammaCoeff d ≠ 0) :
    (jensenPolynomial d).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_jensenPolynomial_le d)
  simpa [coeff_jensenPolynomial_self] using hgamma

/-- If `gammaCoeff d ≠ 0`, the leading coefficient of `jensenPolynomial d` is `gammaCoeff d`. -/
theorem leadingCoeff_jensenPolynomial (d : ℕ) (hgamma : gammaCoeff d ≠ 0) :
    (jensenPolynomial d).leadingCoeff = gammaCoeff d := by
  rw [Polynomial.leadingCoeff, natDegree_jensenPolynomial d hgamma, coeff_jensenPolynomial_self]

/-- The number of distinct negative roots is at most the number of real roots counted with
multiplicity. -/
theorem negativeDistinctRootCount_le_card_roots (p : ℝ[X]) :
    negativeDistinctRootCount p ≤ p.roots.card := by
  unfold negativeDistinctRootCount
  exact (Finset.card_filter_le _ _).trans p.roots.toFinset_card_le

/-- Real roots of a real polynomial, with their real multiplicities, embed in
its complex root multiset and land in the zero-imaginary-part filter. -/
theorem card_real_roots_le_card_complex_real_roots (p : ℝ[X]) :
    p.roots.card ≤
      ((p.map Complex.ofRealHom).roots.filter fun z : ℂ => z.im = 0).card := by
  classical
  have hr : p.roots.map Complex.ofRealHom ≤
      ((p.map Complex.ofRealHom).roots.filter fun z : ℂ => z.im = 0) := by
    refine Multiset.le_filter.mpr
      ⟨Polynomial.map_roots_le_of_injective p Complex.ofReal_injective, fun z hz => ?_⟩
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hz
    simp
  simpa using Multiset.card_le_card hr

/-- The complex roots split into roots with zero imaginary part and nonreal
roots. -/
theorem card_complex_roots_eq_real_add_nonreal (p : ℝ[X]) :
    (p.map Complex.ofRealHom).roots.card =
      ((p.map Complex.ofRealHom).roots.filter fun z : ℂ => z.im = 0).card +
        nonrealRootCount p := by
  classical
  simpa [nonrealRootCount, Multiset.countP_eq_card_filter] using
    Multiset.card_eq_countP_add_countP (fun z : ℂ => z.im = 0) (p.map Complex.ofRealHom).roots

/-- Distinct negative roots plus nonreal roots never exceed the degree. -/
theorem negativeDistinctRootCount_add_nonrealRootCount_le_natDegree (p : ℝ[X]) :
    negativeDistinctRootCount p + nonrealRootCount p ≤ p.natDegree := by
  rw [← IsAlgClosed.card_roots_map_eq_natDegree_of_injective (f := Complex.ofRealHom) p
      Complex.ofReal_injective,
    card_complex_roots_eq_real_add_nonreal]
  exact Nat.add_le_add_right
    ((negativeDistinctRootCount_le_card_roots p).trans
      (card_real_roots_le_card_complex_real_roots p)) _

/-- If a polynomial of natural degree at most `d` has at least `d - E`
distinct negative roots, then it has at most `E` nonreal roots.

The hypothesis is written without truncated subtraction, as `d ≤ n + E`;
this is the form naturally supplied by the analytic root count. -/
theorem nonrealRootCount_le_of_natDegree_le_of_many_negative {p : ℝ[X]} {d E : ℕ}
    (hdeg : p.natDegree ≤ d) (hmany : d ≤ negativeDistinctRootCount p + E) :
    nonrealRootCount p ≤ E := by
  have := negativeDistinctRootCount_add_nonrealRootCount_le_natDegree p
  omega

/-- If a real polynomial of natural degree at most `d` has at least `d - E` distinct negative
roots, for a real `E`, then it has at most `E` nonreal roots. -/
theorem nonrealRootCount_cast_le_of_natDegree_le_of_many_negative {p : ℝ[X]} {d : ℕ} {E : ℝ}
    (hdeg : p.natDegree ≤ d) (hmany : (d : ℝ) - E ≤ (negativeDistinctRootCount p : ℝ)) :
    (nonrealRootCount p : ℝ) ≤ E := by
  have htotal : (negativeDistinctRootCount p : ℝ) + nonrealRootCount p ≤ d := by
    exact_mod_cast (negativeDistinctRootCount_add_nonrealRootCount_le_natDegree p).trans hdeg
  linarith

/-- If the degree-`d` Jensen polynomial has at least `d - E` distinct negative roots, then it
has at most `E` nonreal roots. -/
theorem nonrealJensenRootCount_le_of_many_negative {d E : ℕ}
    (hmany : d ≤ negativeJensenRootCount d + E) : nonrealJensenRootCount d ≤ E :=
  nonrealRootCount_le_of_natDegree_le_of_many_negative (natDegree_jensenPolynomial_le d) hmany

/-- If the degree-`d` Jensen polynomial has at least `d - E` distinct negative roots, for a
real `E`, then it has at most `E` nonreal roots. -/
theorem nonrealJensenRootCount_cast_le_of_many_negative {d : ℕ} {E : ℝ}
    (hmany : (d : ℝ) - E ≤ (negativeJensenRootCount d : ℝ)) :
    (nonrealJensenRootCount d : ℝ) ≤ E :=
  nonrealRootCount_cast_le_of_natDegree_le_of_many_negative (natDegree_jensenPolynomial_le d)
    hmany

end RiemannJensen
