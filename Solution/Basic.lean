module

public import RiemannJensen.Dedekind.FinalUnconditional
public import RiemannJensen.MainTheorem.Solution

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace RiemannJensen.Challenge

/-- **Existence.** The Dedekind zeta function of every number field `K` has an analytic
continuation to `ℂ \ {1}`. -/
theorem exists_isDedekindZetaContinuation (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, IsDedekindZetaContinuation K f :=
  RiemannJensen.exists_isDedekindZetaContinuation K

/-- **Uniqueness.** Two analytic continuations of the Dedekind zeta function of `K` agree on
`ℂ \ {1}`. -/
theorem isDedekindZetaContinuation_unique (K : Type) [Field K] [NumberField K]
    {f g : ℂ → ℂ} (hf : IsDedekindZetaContinuation K f)
    (hg : IsDedekindZetaContinuation K g) :
    ∀ s : ℂ, s ≠ 1 → f s = g s :=
  RiemannJensen.isDedekindZetaContinuation_unique K hf hg

/-- **Almost all Dedekind Jensen zeros are negative real.** For every number field `K` there
is `C > 0` such that, for all large `d`, the degree-`d` Dedekind Jensen polynomial of `K` is
nonzero and has at least `d - C √(d log d)` distinct negative real roots. -/
theorem dedekind_thm_main (K : Type) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      dedekindJensenK K d ≠ 0 ∧
        (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
          (dedekindNegativeRootCountK K d : ℝ) :=
  RiemannJensen.dedekind_thm_main K

/-- **The Riemann case.** There is `C > 0` such that, for every `d ≥ 2`, the degree-`d`
Riemann Jensen polynomial has at most `C √(d log d)` nonreal roots and at least
`d - C √(d log d)` distinct negative real roots. -/
theorem riemannJensen_main :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) :=
  RiemannJensen.riemannJensen_main

end RiemannJensen.Challenge
