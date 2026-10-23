module

public import RiemannJensen.Analysis.AmplitudeDefinitions
public import RiemannJensen.Analysis.LowerBranch
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Exact xi amplitude factorization

We prove exact algebraic identities expressing the centered xi function `centeredXi` through the
Gamma function and the Riemann zeta function, and through the factor `gammaRemainder` multiplied
by its normalizing denominator `gammaMainDenominator`.

## Main definitions

* `gammaMainDenominator`: the factor `√(2π) (w/2)^(w/2 - 1/4) e^(-w/2)`.

## Main results

* `riemannXi_eq_gamma_zeta`: for `0 < re s` and `s ≠ 1`,
  `ξ(s) = s(s-1)/2 · π^(-s/2) Γ(s/2) ζ(s)`.
* `centeredXi_eq_gamma_zeta`: the same identity for `centeredXi`.
* `centeredXi_eq_gammaRemainder`: the factorization of `centeredXi` through `gammaRemainder`.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The factor `√(2π) (w/2)^(w/2 - 1/4) e^(-w/2)`, the denominator in the definition of
`gammaRemainder`. -/
noncomputable def gammaMainDenominator (w : ℂ) : ℂ :=
  Complex.sqrt (2 * Real.pi) *
    Complex.cpow (w / 2) (w / 2 - 1 / 4) *
    Complex.exp (-w / 2)

/-- `gammaMainDenominator w` is nonzero for `w ≠ 0`. -/
theorem gammaMainDenominator_ne_zero {w : ℂ} (hw : w ≠ 0) : gammaMainDenominator w ≠ 0 := by
  have hsqrt : Complex.sqrt (2 * Real.pi) ≠ 0 := by
    simp [Complex.sqrt, Real.pi_ne_zero]
  exact mul_ne_zero (mul_ne_zero hsqrt
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hw two_ne_zero))))
    (Complex.exp_ne_zero _)

/-- For `w ≠ 0`, `gammaRemainder w * gammaMainDenominator w` equals
`(1 - 1 / (4 w²)) Γ(w/2 + 1/4)`. -/
theorem gammaRemainder_mul_gammaMainDenominator {w : ℂ} (hw : w ≠ 0) :
    gammaRemainder w * gammaMainDenominator w =
      (1 - 1 / (4 * w ^ 2)) * Complex.Gamma (w / 2 + 1 / 4) := by
  unfold gammaRemainder gammaMainDenominator
  exact div_mul_cancel₀ _ (gammaMainDenominator_ne_zero hw)

/-- For `s ≠ 0` and `s ≠ 1`, `ξ(s) = s(s-1) Λ(s) / 2`, where `Λ` is `completedRiemannZeta`. -/
theorem riemannXi_eq_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp [hs0, hs1]
  ring

/-- The completed zeta is the product of zeta with Deligne's real Gamma factor in the open right
half-plane. -/
theorem completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = riemannZeta s * s.Gammaℝ := by
  rw [riemannZeta_def_of_ne_zero (by rintro rfl; simp at hs)]
  exact (div_mul_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hs)).symm

/-- For `0 < re s` and `s ≠ 1`, `ξ(s) = s(s-1)/2 · π^(-s/2) Γ(s/2) ζ(s)`. -/
theorem riemannXi_eq_gamma_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s =
      (s * (s - 1) / 2) *
        Complex.cpow Real.pi (-s / 2) * Complex.Gamma (s / 2) *
        riemannZeta s := by
  rw [riemannXi_eq_completedRiemannZeta (by rintro rfl; simp at hs) hs1,
    completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ hs,
    Complex.Gammaℝ_def]
  simp only [Complex.cpow_eq_pow]
  ring

/-- For `0 < re (1/2 + w)` and `1/2 + w ≠ 1`,
`centeredXi w = (w² - 1/4)/2 · π^(-(1/2 + w)/2) Γ(w/2 + 1/4) ζ(1/2 + w)`. -/
theorem centeredXi_eq_gamma_zeta {w : ℂ} (hs : 0 < (1 / 2 + w).re) (hs1 : 1 / 2 + w ≠ 1) :
    centeredXi w =
      ((w ^ 2 - 1 / 4) / 2) *
        Complex.cpow Real.pi (-(1 / 2 + w) / 2) *
        Complex.Gamma (w / 2 + 1 / 4) *
        riemannZeta (1 / 2 + w) := by
  rw [centeredXi, riemannXi_eq_gamma_zeta hs hs1,
    show (1 / 2 + w) / 2 = w / 2 + 1 / 4 by ring]
  ring

/-- The exact factorization of `centeredXi w` as
`w²/2 · π^(-(1/2 + w)/2) · gammaMainDenominator w · ζ(1/2 + w) · gammaRemainder w`. -/
theorem centeredXi_eq_gammaRemainder {w : ℂ} (hw : w ≠ 0) (hs : 0 < (1 / 2 + w).re)
    (hs1 : 1 / 2 + w ≠ 1) :
    centeredXi w =
      (w ^ 2 / 2) * Complex.cpow Real.pi (-(1 / 2 + w) / 2) *
        gammaMainDenominator w * riemannZeta (1 / 2 + w) *
        gammaRemainder w := by
  rw [centeredXi_eq_gamma_zeta hs hs1]
  linear_combination (norm := (field_simp; ring))
    (-(w ^ 2 / 2) * Complex.cpow Real.pi (-(1 / 2 + w) / 2) * riemannZeta (1 / 2 + w)) *
      gammaRemainder_mul_gammaMainDenominator hw

end RiemannJensen
