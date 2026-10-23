module

public import RiemannJensen.Dedekind.CompletedZetaPackageSource
public import RiemannJensen.Dedekind.Foundation
public import RiemannJensen.Dedekind.ContinuationBridges

/-!
# The entire completed Dedekind xi-function

For a number field `K`, `entireDedekindXi K` is an entire function equal to
`s * (s - 1) * Λ_K s / 2` away from `s = 0, 1`, where `Λ_K` is the completed Dedekind zeta
function constructed in `RiemannJensen.Dedekind.CompletedZetaPackageSource`. This file proves
that it satisfies the functional equation `ξ_K (1 - s) = ξ_K s`, commutes with complex
conjugation, is given by the product of gamma factors and the Dedekind zeta series for
`1 < re s`, and is not identically zero.

## Main definitions

* `rawDedekindXi`: An entire function equal to `s (s - 1) Λ_K(s)` off `{0, 1}`.
* `entireDedekindXi`: Half of `rawDedekindXi`.

## Main results

* `entireDedekindXi_entire`: `entireDedekindXi K` is entire.
* `entireDedekindXi_functional`: `entireDedekindXi K (1 - s) = entireDedekindXi K s`.
* `entireDedekindXi_eq_product_of_one_lt_re`: The product formula for `entireDedekindXi K s`
  when `1 < re s`.
* `entireDedekindXi_conj`: `entireDedekindXi K` commutes with complex conjugation.
* `entireDedekindXi_ne_zero`: `entireDedekindXi K` is not identically zero.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set
open P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT
open Gapsw80T9ClassSumA1Closure
  (gapsw80_t9_completedDedekindZeta gapsw80_t9_completedDedekindZeta_FE)
open Gapsw80T10DedekindZetaBridgeA1Discharge (gapsw80_t10_completedDedekindZeta_eq_T1)
open Gapsw80T16XiRightHalfBoundProof (gapsw80_t16_B1_closed)
open Gapsw80T36D1appXiEndpointResidueProof (gapsw80_t36_D1app_closed)

noncomputable section

/-- The completed Dedekind zeta function `Λ_K` of `K`, holomorphic on `ℂ \ {0, 1}`. -/
abbrev packageCompletedZeta (K : Type) [Field K] [NumberField K] : ℂ → ℂ :=
  gapsw80_t9_completedDedekindZeta K

/-- `Λ_K(s) = |Δ_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` for `1 < re s`. -/
theorem packageCompletedZeta_eq_product (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) :
    packageCompletedZeta K s =
      (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2) *
        Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K *
        NumberField.dedekindZeta K s :=
  gapsw80_t10_completedDedekindZeta_eq_T1 K hs

/-- An entire function equal to `s (s - 1) Λ_K(s)` off `{0, 1}`. -/
def rawDedekindXi (K : Type) [Field K] [NumberField K] : ℂ → ℂ :=
  Classical.choose (gapsw80_t16_B1_closed K)

/-- `rawDedekindXi K` is entire. -/
theorem rawDedekindXi_entire (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (rawDedekindXi K) :=
  (Classical.choose_spec (gapsw80_t16_B1_closed K)).1

/-- `rawDedekindXi K s = s (s - 1) Λ_K(s)` for `s ≠ 0, 1`. -/
theorem rawDedekindXi_eq (K : Type) [Field K] [NumberField K] (s : ℂ) (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    rawDedekindXi K s = s * (s - 1) * packageCompletedZeta K s :=
  (Classical.choose_spec (gapsw80_t16_B1_closed K)).2.1 s hs0 hs1

/-- The entire completed Dedekind xi-function, equal to `s (s - 1) Λ_K(s) / 2` off `{0, 1}`. -/
def entireDedekindXi (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * rawDedekindXi K s

/-- The entire completed Dedekind xi-function is half of `rawDedekindXi`. -/
theorem entireDedekindXi_def (K : Type) [Field K] [NumberField K] (s : ℂ) :
    entireDedekindXi K s = (1 / 2 : ℂ) * rawDedekindXi K s :=
  rfl

/-- The completed Dedekind xi-function is entire. -/
theorem entireDedekindXi_entire
    (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (entireDedekindXi K) :=
  (differentiable_const (1 / 2 : ℂ)).mul (rawDedekindXi_entire K)

private theorem rawDedekindXi_functional_away
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rawDedekindXi K (1 - s) = rawDedekindXi K s := by
  rw [rawDedekindXi_eq K (1 - s) (sub_ne_zero.mpr hs1.symm) (fun h => hs0 (sub_eq_self.mp h)),
    rawDedekindXi_eq K s hs0 hs1, packageCompletedZeta,
    gapsw80_t9_completedDedekindZeta_FE K hs0 hs1]
  ring

/-- The completed Dedekind functional equation, including the two removable
points. -/
theorem entireDedekindXi_functional
    (K : Type) [Field K] [NumberField K] (s : ℂ) :
    entireDedekindXi K (1 - s) = entireDedekindXi K s := by
  have heq : Set.EqOn (fun z : ℂ => rawDedekindXi K (1 - z)) (rawDedekindXi K) Set.univ := by
    refine holomorphic_eqOn_of_open_agreement
      Set.univ {z : ℂ | 1 < z.re}
      (fun z : ℂ => rawDedekindXi K (1 - z)) (rawDedekindXi K)
      isOpen_univ isPreconnected_univ
      (isOpen_lt continuous_const Complex.continuous_re)
      ⟨2, by norm_num⟩ (fun _ _ => Set.mem_univ _)
      ((rawDedekindXi_entire K).comp
        ((differentiable_const 1).sub differentiable_id)).differentiableOn
      (rawDedekindXi_entire K).differentiableOn fun z hz => ?_
    exact rawDedekindXi_functional_away K z (by rintro rfl; norm_num at hz)
      (by rintro rfl; norm_num at hz)
  exact congrArg ((1 / 2 : ℂ) * ·) (heq (Set.mem_univ s))

/-- For `1 < re s`, `entireDedekindXi K s` equals `s (s - 1) / 2` times the discriminant factor,
the archimedean gamma factors and the Dedekind zeta series. -/
theorem entireDedekindXi_eq_product_of_one_lt_re
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : 1 < s.re) :
    entireDedekindXi K s =
      (s * (s - 1) / 2) *
        (dedekindDiscriminantAbs K : ℂ) ^ (s / 2) *
        dedekindGammaR s ^ dedekindRealPlaces K *
        dedekindGammaC s ^ dedekindComplexPlaces K *
        rawDedekindZeta K s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  rw [entireDedekindXi_def, rawDedekindXi_eq K s hs0 hs1,
    packageCompletedZeta_eq_product K s hs, dedekindDiscriminantAbs,
    dedekindGammaR, dedekindGammaC, dedekindRealPlaces, dedekindComplexPlaces, rawDedekindZeta,
    show (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)) = (((|NumberField.discr K| : ℤ) : ℂ)) by
      norm_cast]
  ring

/-- The raw Dirichlet series commutes with conjugation in its half-plane of
absolute convergence. -/
theorem rawDedekindZeta_conj_of_one_lt_re
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : 1 < s.re) :
    rawDedekindZeta K (star s) = star (rawDedekindZeta K s) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  rw [rawDedekindZeta, NumberField.dedekindZeta, LSeries]
  calc
    ∑' n : ℕ, LSeries.term
        (fun n => Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n})
        (star s) n =
        ∑' n : ℕ, star (LSeries.term
          (fun n => Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n})
          s n) := by
      apply tsum_congr
      intro n
      rw [LSeries.term_of_ne_zero' (star_ne_zero.mpr hs0), LSeries.term_of_ne_zero' hs0]
      change _ = (starRingEnd ℂ) (_ / _)
      rw [map_div₀ (starRingEnd ℂ)]
      congr 1
      · simp
      · have hnarg : Complex.arg (n : ℂ) ≠ Real.pi := by
          rw [Complex.natCast_arg]
          exact Real.pi_ne_zero.symm
        change (n : ℂ) ^ (starRingEnd ℂ) s =
          (starRingEnd ℂ) ((n : ℂ) ^ s)
        rw [Complex.cpow_conj _ _ hnarg, Complex.conj_natCast]
    _ = star (∑' n : ℕ, LSeries.term
          (fun n => Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n})
          s n) := tsum_star.symm

private theorem dedekindGammaR_conj (s : ℂ) :
    dedekindGammaR (star s) = star (dedekindGammaR s) := by
  rw [dedekindGammaR, dedekindGammaR, Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have harg : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  simp only [star_def, map_mul, ← Complex.Gamma_conj, map_div₀, map_ofNat]
  rw [show -(starRingEnd ℂ) s / 2 = starRingEnd ℂ (-s / 2) by
      rw [map_div₀, map_neg, map_ofNat],
    Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

private theorem dedekindGammaC_conj (s : ℂ) :
    dedekindGammaC (star s) = star (dedekindGammaC s) := by
  rw [dedekindGammaC, dedekindGammaC, Complex.Gammaℂ_def, Complex.Gammaℂ_def]
  have harg : ((2 : ℂ) * (Real.pi : ℝ)).arg ≠ Real.pi := by
    rw [show (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  simp only [star_def, map_mul, ← Complex.Gamma_conj, map_ofNat]
  rw [← map_neg, Complex.cpow_conj _ _ harg, map_mul, map_ofNat, Complex.conj_ofReal]

/-- The completed Dedekind xi-function commutes with conjugation for `1 < re s`. -/
private theorem entireDedekindXi_conj_of_one_lt_re
    (K : Type) [Field K] [NumberField K]
    (s : ℂ) (hs : 1 < s.re) :
    entireDedekindXi K (star s) = star (entireDedekindXi K s) := by
  rw [entireDedekindXi_eq_product_of_one_lt_re K (star s) (by simpa using hs),
    entireDedekindXi_eq_product_of_one_lt_re K s hs]
  have harg : Complex.arg (dedekindDiscriminantAbs K : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (dedekindDiscriminantAbs_pos K).le]
    exact Real.pi_ne_zero.symm
  have hpow :
      (dedekindDiscriminantAbs K : ℂ) ^ ((star s) / 2) =
        star ((dedekindDiscriminantAbs K : ℂ) ^ (s / 2)) := by
    have h := Complex.cpow_conj
      (dedekindDiscriminantAbs K : ℂ) (s / 2) harg
    rwa [map_div₀ (starRingEnd ℂ), map_ofNat, Complex.conj_ofReal] at h
  rw [hpow, dedekindGammaR_conj, dedekindGammaC_conj,
    rawDedekindZeta_conj_of_one_lt_re K s hs]
  change _ = (starRingEnd ℂ) (_ * _)
  simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat, map_pow,
    starRingEnd_apply]

/-- The completed Dedekind xi-function commutes with complex conjugation. -/
theorem entireDedekindXi_conj
    (K : Type) [Field K] [NumberField K] (s : ℂ) :
    entireDedekindXi K (star s) = star (entireDedekindXi K s) := by
  have heq :
      Set.EqOn (fun z => star (entireDedekindXi K (star z))) (entireDedekindXi K) Set.univ := by
    refine holomorphic_eqOn_of_open_agreement
      Set.univ {z : ℂ | 1 < z.re} _ (entireDedekindXi K)
      isOpen_univ isPreconnected_univ
      (isOpen_lt continuous_const Complex.continuous_re)
      ⟨2, by norm_num⟩ (fun _ _ => Set.mem_univ _)
      (fun z _ => (differentiableAt_conj_conj_iff.mpr
        (entireDedekindXi_entire K (star z))).differentiableWithinAt)
      (entireDedekindXi_entire K).differentiableOn fun z hz => ?_
    simpa only [star_star] using congrArg star (entireDedekindXi_conj_of_one_lt_re K z hz)
  simpa only [star_star] using congrArg star (heq (Set.mem_univ s))

/-- The completed Dedekind xi-function is not identically zero. -/
theorem entireDedekindXi_ne_zero
    (K : Type) [Field K] [NumberField K] :
    entireDedekindXi K ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [entireDedekindXi_def, Pi.zero_apply] at h0
  exact (gapsw80_t36_D1app_closed K (rawDedekindXi K) (rawDedekindXi_entire K)
    (rawDedekindXi_eq K)).1
    ((mul_eq_zero.mp h0).resolve_left (by norm_num))

end

end RiemannJensen
