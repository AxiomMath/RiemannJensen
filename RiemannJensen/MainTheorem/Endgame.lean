module

public import RiemannJensen.Polynomial

/-!
# Nonreal roots of Jensen polynomials from a negative-root bound

If every coefficient `gammaCoeff d` with `2 ≤ d` is positive and the number of distinct negative
roots of the degree-`d` Jensen polynomial is at least `d - C √(d log d)`, then the number of its
nonreal roots is at most `C √(d log d)`, with the same constant `C`.

## Main results

* `riemannJensen_main_of_negative_root_bound`: a uniform lower bound for the distinct negative
  roots, together with positivity of `gammaCoeff d`, gives both the upper bound for the nonreal
  roots and the lower bound for the negative roots with a common constant.
-/

@[expose] public section

namespace RiemannJensen

/-- If `gammaCoeff d > 0` for all `d ≥ 2` and, for some `C > 0`, the number of distinct negative
roots of the degree-`d` Jensen polynomial is at least `d - C √(d log d)` for all `d ≥ 2`, then
for some `C > 0` the number of nonreal roots is at most `C √(d log d)` and the number of distinct
negative roots is at least `d - C √(d log d)`, for all `d ≥ 2`. -/
theorem riemannJensen_main_of_negative_root_bound
    (_hgamma : ∀ d : ℕ, 2 ≤ d → 0 < gammaCoeff d)
    (hroots : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) := by
  rcases hroots with ⟨C, hC, hroots⟩
  refine ⟨C, hC, ?_⟩
  intro d hd
  have hnegative := hroots d hd
  refine ⟨?_, hnegative⟩
  exact nonrealJensenRootCount_cast_le_of_many_negative hnegative

end RiemannJensen
