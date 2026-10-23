module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Elementary uniqueness bridges for analytic continuations

This file proves uniqueness and conjugation-symmetry statements for holomorphic functions on
open connected domains, in particular on the punctured plane `ℂ \ {1}`.

## Main results

* `holomorphic_eqOn_of_open_agreement`: two holomorphic functions on an open connected domain
  agreeing on a nonempty open subdomain agree on the whole domain.
* `puncturedPlane_isPreconnected`: the complex plane with one point removed is preconnected.
* `continuation_unique_off_one`: holomorphic functions on `ℂ \ {1}` agreeing on `re s > 1`
  agree on `ℂ \ {1}`.
* `conjugation_symmetry_off_one`: a holomorphic function on `ℂ \ {1}` that commutes with
  conjugation on `re s > 1` commutes with conjugation on `ℂ \ {1}`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- Two holomorphic functions on an open connected domain which agree on a
nonempty open subdomain agree on the whole domain. -/
theorem holomorphic_eqOn_of_open_agreement
    (U V : Set ℂ) (f g : ℂ → ℂ)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfg : Set.EqOn f g V) : Set.EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := hVne
  exact ((Complex.analyticOnNhd_iff_differentiableOn hU).mpr hf)
    |>.eqOn_of_preconnected_of_eventuallyEq
      ((Complex.analyticOnNhd_iff_differentiableOn hU).mpr hg) hUc (hVU hz₀)
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hz₀) hfg)

/-- The complex plane with one point removed is preconnected. -/
theorem puncturedPlane_isPreconnected (a : ℂ) :
    IsPreconnected ({a}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank (by simp) a).isPreconnected

/-- Two functions holomorphic on `ℂ \ {1}` which agree on the half-plane `re s > 1` agree on
`ℂ \ {1}`. -/
theorem continuation_unique_off_one
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) :
    Set.EqOn f g ({1}ᶜ : Set ℂ) :=
  holomorphic_eqOn_of_open_agreement _ {s : ℂ | 1 < s.re} f g isOpen_compl_singleton
    (puncturedPlane_isPreconnected 1) (isOpen_lt continuous_const Complex.continuous_re)
    ⟨2, by norm_num⟩ (fun s hs hs1 => by simp_all) hf hg hfg

/-- If `f` is holomorphic on `ℂ \ {1}`, then so is `z ↦ star (f (star z))`. -/
theorem conjugate_reflection_differentiableOn_off_one
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ)) :
    DifferentiableOn ℂ (fun z => star (f (star z))) ({1}ᶜ : Set ℂ) := by
  intro z hz
  have hzstar : star z ∈ ({1}ᶜ : Set ℂ) := by
    simpa [map_eq_one_iff _ (starRingEnd ℂ).injective] using hz
  exact (differentiableAt_conj_conj_iff.mpr
    ((hf _ hzstar).differentiableAt (isOpen_compl_singleton.mem_nhds hzstar)))
    |>.differentiableWithinAt

/-- If `f` is holomorphic on `ℂ \ {1}` and satisfies `f (star s) = star (f s)` on the half-plane
`re s > 1`, then it satisfies this identity for every `s ≠ 1`. -/
theorem conjugation_symmetry_off_one
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hright : ∀ s : ℂ, 1 < s.re → f (star s) = star (f s)) :
    ∀ s : ℂ, s ≠ 1 → f (star s) = star (f s) := by
  have heq := continuation_unique_off_one _ f
    (conjugate_reflection_differentiableOn_off_one f hf) hf fun s hs => by
      simpa using congrArg star (hright s hs)
  intro s hs
  simpa using (heq (show star s ≠ 1 from
    (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hs)).symm

end RiemannJensen
