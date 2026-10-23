module

public import RiemannJensen.MainTheorem.Counting
public import RiemannJensen.MainTheorem.Endgame
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Removing the large-degree cutoff

A lower bound `d - C₀ √(d log d)` on the number of distinct negative roots of the Jensen
polynomial of degree `d`, valid for all `d` beyond some threshold, extends to all `d ≥ 2` after
enlarging the constant. Combined with positivity of the coefficients, this gives both clauses of
the main theorem uniformly from degree two onward.

## Main results

* `uniform_negative_root_bound_of_eventually`: an eventual lower bound on
  `negativeJensenRootCount d` holds for every `d ≥ 2` with a larger constant.
* `riemannJensen_main_of_eventual_negative_root_bound`: an eventual lower bound on
  `negativeJensenRootCount d` and positivity of `gammaCoeff` give both bounds of the main theorem
  for every `d ≥ 2`.
* `riemannJensen_main_of_eventual_nat_loss`: the same conclusion from an eventual natural-number
  loss of size at most `C₀ √(d log d)`.
-/

@[expose] public section

namespace RiemannJensen

/-- If `d ≤ negativeJensenRootCount d + K` and `K ≤ E`, then
`d - E ≤ negativeJensenRootCount d`. -/
theorem negativeJensenRootCount_cast_lower_of_nat_loss
    {d K : ℕ} {E : ℝ}
    (hcount : d ≤ negativeJensenRootCount d + K)
    (hloss : (K : ℝ) ≤ E) :
    (d : ℝ) - E ≤ (negativeJensenRootCount d : ℝ) := by
  have hcountR : (d : ℝ) ≤ (negativeJensenRootCount d : ℝ) + K := by
    exact_mod_cast hcount
  linarith

/-- If `n ≤ negativeJensenRootCount d` and `d - E ≤ n`, then
`d - E ≤ negativeJensenRootCount d`. -/
theorem negativeJensenRootCount_cast_lower_of_count
    {d n : ℕ} {E : ℝ}
    (hcount : n ≤ negativeJensenRootCount d)
    (hloss : (d : ℝ) - E ≤ n) :
    (d : ℝ) - E ≤ (negativeJensenRootCount d : ℝ) :=
  hloss.trans (by exact_mod_cast hcount)

/-- If `d ≤ negativeJensenRootCount d + K d` and `K d ≤ C₀ √(d log d)` for all `d ≥ D`, then
`d - C₀ √(d log d) ≤ negativeJensenRootCount d` for all `d ≥ D`. -/
theorem eventual_negative_root_bound_of_nat_loss
    (K : ℕ → ℕ) {C₀ : ℝ} {D : ℕ}
    (hcount : ∀ d : ℕ, D ≤ d → d ≤ negativeJensenRootCount d + K d)
    (hloss : ∀ d : ℕ, D ≤ d →
      (K d : ℝ) ≤ C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) :
    ∀ d : ℕ, D ≤ d →
      (d : ℝ) - C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ) :=
  fun d hd => negativeJensenRootCount_cast_lower_of_nat_loss (hcount d hd) (hloss d hd)

/-- For every integer `d ≥ 2`, the scale `sqrt (d log d)` is at least one. -/
theorem one_le_sqrt_nat_mul_log_nat {d : ℕ} (hd : 2 ≤ d) :
    1 ≤ Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : Real.log 2 ≤ Real.log (d : ℝ) := Real.log_le_log (by norm_num) hdR
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (d : ℝ) := by linarith [Real.log_two_gt_d9]
  exact Real.one_le_sqrt.mpr (by nlinarith)

/-- A large-degree lower bound for negative Jensen roots extends to every
`d ≥ 2` after enlarging its positive constant. -/
theorem uniform_negative_root_bound_of_eventually
    {C₀ : ℝ} {D : ℕ} (hC₀ : 0 < C₀)
    (hlarge : ∀ d : ℕ, D ≤ d →
      (d : ℝ) - C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ) := by
  refine ⟨max C₀ D, hC₀.trans_le (le_max_left _ _), fun d hd => ?_⟩
  by_cases hD : D ≤ d
  · have hbase := hlarge d hD
    have hsqrt : 0 ≤ Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := Real.sqrt_nonneg _
    have hcoef : C₀ ≤ max C₀ (D : ℝ) := le_max_left _ _
    nlinarith
  · have hdDR : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast (not_le.mp hD).le
    have hCD : (D : ℝ) ≤ max C₀ (D : ℝ) := le_max_right _ _
    have hsqrt := one_le_sqrt_nat_mul_log_nat hd
    have hnonneg : (0 : ℝ) ≤ negativeJensenRootCount d := by positivity
    nlinarith

/-- A square-root-sized natural loss beyond a cutoff is absorbed into one
positive constant valid for every degree at least two. -/
theorem uniform_negative_root_bound_of_eventually_nat_loss
    (K : ℕ → ℕ) {C₀ : ℝ} {D : ℕ} (hC₀ : 0 < C₀)
    (hcount : ∀ d : ℕ, D ≤ d → d ≤ negativeJensenRootCount d + K d)
    (hloss : ∀ d : ℕ, D ≤ d →
      (K d : ℝ) ≤ C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ) :=
  uniform_negative_root_bound_of_eventually hC₀
    (eventual_negative_root_bound_of_nat_loss K hcount hloss)

/-- If the coefficients `gammaCoeff d` are positive for `d ≥ 2` and
`d - C₀ √(d log d) ≤ negativeJensenRootCount d` for all `d ≥ D`, then for some `C > 0` and every
`d ≥ 2`, `nonrealJensenRootCount d ≤ C √(d log d)` and
`d - C √(d log d) ≤ negativeJensenRootCount d`. -/
theorem riemannJensen_main_of_eventual_negative_root_bound
    (hgamma : ∀ d : ℕ, 2 ≤ d → 0 < gammaCoeff d)
    {C₀ : ℝ} {D : ℕ} (hC₀ : 0 < C₀)
    (hlarge : ∀ d : ℕ, D ≤ d →
      (d : ℝ) - C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :=
  riemannJensen_main_of_negative_root_bound hgamma
    (uniform_negative_root_bound_of_eventually hC₀ hlarge)

/-- Coefficient positivity and an eventual square-root-sized natural loss imply
the full two-clause conclusion, uniformly from degree two onward. -/
theorem riemannJensen_main_of_eventual_nat_loss
    (hgamma : ∀ d : ℕ, 2 ≤ d → 0 < gammaCoeff d)
    (K : ℕ → ℕ) {C₀ : ℝ} {D : ℕ} (hC₀ : 0 < C₀)
    (hcount : ∀ d : ℕ, D ≤ d → d ≤ negativeJensenRootCount d + K d)
    (hloss : ∀ d : ℕ, D ≤ d →
      (K d : ℝ) ≤ C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :=
  riemannJensen_main_of_negative_root_bound hgamma
    (uniform_negative_root_bound_of_eventually_nat_loss K hC₀ hcount hloss)

end RiemannJensen
