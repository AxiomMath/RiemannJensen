module

public import RiemannJensen.MainTheorem.Main

/-!
# Almost all zeros of Riemann Jensen polynomials are real

There is a constant `C > 0` such that for every `d ≥ 2` the degree-`d` Jensen polynomial of the
Riemann xi function has at most `C √(d log d)` nonreal roots and at least `d - C √(d log d)`
distinct negative real roots.

## Main results

* `riemannJensen_main`: The nonreal root count is at most `C √(d log d)` and the negative root
  count is at least `d - C √(d log d)`, for all `d ≥ 2`.
-/

@[expose] public section

namespace RiemannJensen

/-- There is a constant `C > 0` such that for every `d ≥ 2`, `nonrealJensenRootCount d` is at
most `C √(d log d)` and `negativeJensenRootCount d` is at least `d - C √(d log d)`. -/
theorem riemannJensen_main :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :=
  riemannJensen_main_from_countingWindow

end RiemannJensen
