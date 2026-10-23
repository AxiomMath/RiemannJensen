module

public import RiemannJensen.Dedekind.ContinuedZeta
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Elementary consequences of the completed Dedekind xi package

This module specializes the field-independent coefficient and polynomial
definitions to the verified completed xi-function.
-/

@[expose] public section

namespace RiemannJensen

open Polynomial

noncomputable section

/-- The completed Dedekind xi-function centered at `1 / 2`. -/
def centeredDedekindXi (K : Type) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  entireDedekindXi K (1 / 2 + w)

/-- The Taylor coefficients attached to a number field. -/
def dedekindGammaCoeffK (K : Type) [Field K] [NumberField K] (j : ℕ) : ℝ :=
  dedekindGammaCoeff (entireDedekindXi K) j

/-- The square-variable entire series attached to a number field. -/
def dedekindFK (K : Type) [Field K] [NumberField K] (z : ℂ) : ℂ :=
  dedekindF (entireDedekindXi K) z

/-- The degree-padded reciprocal Dedekind Jensen polynomial. -/
def dedekindReciprocalK (K : Type) [Field K] [NumberField K] (d : ℕ) : ℝ[X] :=
  dedekindReciprocal (entireDedekindXi K) d

/-- `dedekindReciprocalK K` is `dedekindReciprocal` of the completed xi-function. -/
theorem dedekindReciprocalK_eq (K : Type) [Field K] [NumberField K] (d : ℕ) :
    dedekindReciprocalK K d = dedekindReciprocal (entireDedekindXi K) d :=
  rfl

/-- The centered completed function is entire. -/
theorem centeredDedekindXi_entire (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (centeredDedekindXi K) :=
  (entireDedekindXi_entire K).comp ((differentiable_const (1 / 2 : ℂ)).add differentiable_id)

/-- The functional equation is evenness after centering. -/
theorem centeredDedekindXi_even (K : Type) [Field K] [NumberField K] (w : ℂ) :
    centeredDedekindXi K (-w) = centeredDedekindXi K w := by
  rw [centeredDedekindXi, centeredDedekindXi]
  convert entireDedekindXi_functional K (1 / 2 + w) using 2
  ring

/-- Centering preserves conjugation symmetry. -/
theorem centeredDedekindXi_conj (K : Type) [Field K] [NumberField K] (w : ℂ) :
    centeredDedekindXi K (star w) = star (centeredDedekindXi K w) := by
  rw [centeredDedekindXi, centeredDedekindXi, ← entireDedekindXi_conj]
  congr 1
  simp

private theorem iteratedDeriv_centeredDedekindXi_conj (K : Type) [Field K] [NumberField K] :
    ∀ n : ℕ,
      (starRingEnd ℂ ∘ iteratedDeriv n (centeredDedekindXi K) ∘
          starRingEnd ℂ) =
        iteratedDeriv n (centeredDedekindXi K) := by
  intro n
  induction n with
  | zero =>
      funext w
      simpa [Complex.star_def] using congrArg (starRingEnd ℂ) (centeredDedekindXi_conj K w)
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact deriv_conj_conj.symm.trans (congrArg deriv ih)

/-- Every Taylor derivative at the center is real. -/
theorem iteratedDeriv_centeredDedekindXi_zero_im (K : Type) [Field K] [NumberField K] (n : ℕ) :
    (iteratedDeriv n (centeredDedekindXi K) 0).im = 0 := by
  have h := congrFun (iteratedDeriv_centeredDedekindXi_conj K n) 0
  simp only [Function.comp_apply, map_zero] at h
  exact Complex.conj_eq_iff_im.mp h

/-- Every odd derivative at the origin of the centered function vanishes. -/
theorem iteratedDeriv_centeredDedekindXi_odd (K : Type) [Field K] [NumberField K] (n : ℕ) :
    iteratedDeriv (2 * n + 1) (centeredDedekindXi K) 0 = 0 := by
  have h := congrFun (congrArg (iteratedDeriv (2 * n + 1))
    (funext (centeredDedekindXi_even K))) 0
  rw [iteratedDeriv_comp_neg, neg_zero, (Odd.neg_one_pow ⟨n, rfl⟩ : (-1 : ℂ) ^ (2 * n + 1) = -1),
    neg_one_smul] at h
  linear_combination -h / 2

/-- The normalized even Taylor coefficient is the coefficient used in
`dedekindFK`. -/
theorem centeredDedekindXi_even_taylorCoeff (K : Type) [Field K] [NumberField K] (j : ℕ) :
    ((2 * j).factorial : ℂ)⁻¹ *
        iteratedDeriv (2 * j) (centeredDedekindXi K) 0 =
      (dedekindGammaCoeffK K j : ℂ) / (j.factorial : ℂ) := by
  have hd : iteratedDeriv (2 * j) (centeredDedekindXi K) 0 =
      (iteratedDeriv (2 * j) (centeredDedekindXi K) 0).re :=
    Complex.ext (by simp) (by simp [iteratedDeriv_centeredDedekindXi_zero_im])
  have hj : (j.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero j
  rw [hd]
  unfold dedekindGammaCoeffK dedekindGammaCoeff
  rw [show centeredDedekindFunction (entireDedekindXi K) =
      centeredDedekindXi K by rfl]
  push_cast
  field_simp

private theorem hasSum_taylor_centeredDedekindXi (K : Type) [Field K] [NumberField K] (w : ℂ) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • w ^ n •
      iteratedDeriv n (centeredDedekindXi K) 0) (centeredDedekindXi K w) := by
  simpa only [sub_zero] using
    Complex.hasSum_taylorSeries_of_entire (centeredDedekindXi_entire K) 0 w

private theorem taylor_term_two_mul_centeredDedekindXi
    (K : Type) [Field K] [NumberField K] (w : ℂ) (j : ℕ) :
    ((2 * j).factorial : ℂ)⁻¹ • w ^ (2 * j) •
        iteratedDeriv (2 * j) (centeredDedekindXi K) 0 =
      (dedekindGammaCoeffK K j : ℂ) / (j.factorial : ℂ) * (w ^ 2) ^ j := by
  rw [← centeredDedekindXi_even_taylorCoeff, ← pow_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Substituting a square in `dedekindFK` recovers the centered xi-function. -/
theorem dedekindFK_sq (K : Type) [Field K] [NumberField K] (w : ℂ) :
    dedekindFK K (w ^ 2) = centeredDedekindXi K w := by
  let a : ℕ → ℂ := fun n =>
    (n.factorial : ℂ)⁻¹ • w ^ n • iteratedDeriv n (centeredDedekindXi K) 0
  have ht : HasSum a (centeredDedekindXi K w) := hasSum_taylor_centeredDedekindXi K w
  calc
    dedekindFK K (w ^ 2) = ∑' j : ℕ, a (2 * j) :=
      tsum_congr fun j => (taylor_term_two_mul_centeredDedekindXi K w j).symm
    _ = ∑' n : ℕ, a n := by
      rw [← tsum_even_add_odd (ht.summable.comp_injective (mul_right_injective₀ two_ne_zero))
        (ht.summable.comp_injective ((add_left_injective 1).comp
          (mul_right_injective₀ two_ne_zero)))]
      simp [a, iteratedDeriv_centeredDedekindXi_odd]
    _ = centeredDedekindXi K w := ht.tsum_eq

private def dedekindFKCoeff (K : Type) [Field K] [NumberField K] (j : ℕ) : ℂ :=
  (dedekindGammaCoeffK K j : ℂ) / (j.factorial : ℂ)

private def dedekindFKSeries (K : Type) [Field K] [NumberField K] :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (dedekindFKCoeff K)

private theorem summable_dedekindFKCoeff_mul_pow (K : Type) [Field K] [NumberField K] (z : ℂ) :
    Summable fun j : ℕ => dedekindFKCoeff K j * z ^ j := by
  obtain ⟨w, rfl⟩ := Complex.isSquare z
  refine ((hasSum_taylor_centeredDedekindXi K w).summable.comp_injective
    (mul_right_injective₀ two_ne_zero)).congr fun j => ?_
  rw [← pow_two]
  exact taylor_term_two_mul_centeredDedekindXi K w j

private theorem dedekindFKSeries_radius (K : Type) [Field K] [NumberField K] :
    (dedekindFKSeries K).radius = ⊤ :=
  (dedekindFKSeries K).radius_eq_top_of_summable_norm fun r => by
    simpa [dedekindFKSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul] using
      (summable_dedekindFKCoeff_mul_pow K (r : ℂ)).norm

private theorem dedekindFK_eq_series_sum (K : Type) [Field K] [NumberField K] :
    dedekindFK K = (dedekindFKSeries K).sum := by
  funext z
  rw [dedekindFK, dedekindF]
  change (∑' j : ℕ, (dedekindGammaCoeffK K j : ℂ) /
      (j.factorial : ℂ) * z ^ j) =
    FormalMultilinearSeries.ofScalarsSum (dedekindFKCoeff K) z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [dedekindFKCoeff, smul_eq_mul]

/-- The square-variable series `dedekindFK` is entire. -/
theorem dedekindFK_entire (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (dedekindFK K) := by
  rw [dedekindFK_eq_series_sum]
  exact fun z => (((dedekindFKSeries K).hasFPowerSeriesOnBall
    (by simp [dedekindFKSeries_radius K])).analyticAt_of_mem
    (by simp [dedekindFKSeries_radius K])).differentiableAt

/-- The square-variable entire function is not identically zero. -/
theorem dedekindFK_ne_zero (K : Type) [Field K] [NumberField K] :
    dedekindFK K ≠ 0 := by
  intro hF
  apply entireDedekindXi_ne_zero K
  funext s
  have h := congrFun hF ((s - 1 / 2) ^ 2)
  rw [Pi.zero_apply, dedekindFK_sq] at h
  simpa [centeredDedekindXi] using h

/-- The Dedekind Jensen polynomials are eventually nonzero, without a
central-value hypothesis. -/
theorem eventually_dedekindJensenK_ne_zero (K : Type) [Field K] [NumberField K] :
    ∃ D : ℕ, ∀ d ≥ D, dedekindJensenK K d ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, dedekindGammaCoeff (entireDedekindXi K) j ≠ 0 := by
    by_contra h
    push Not at h
    apply dedekindFK_ne_zero K
    funext z
    simp [dedekindFK, dedekindF, h]
  obtain ⟨D, hD⟩ := exists_eventually_dedekindJensen_ne_zero (entireDedekindXi K) ⟨j, hj⟩
  exact ⟨D, fun d hd => by simpa [dedekindJensenK_eq] using hD d hd⟩

/-- Evaluation of the padded reciprocal away from zero. -/
theorem eval_dedekindReciprocalK_eq (K : Type) [Field K] [NumberField K] (d : ℕ) {x : ℝ}
    (hx : x ≠ 0) :
    (dedekindReciprocalK K d).eval x =
      x ^ d * (dedekindJensenK K d).eval x⁻¹ := by
  simpa [dedekindReciprocalK_eq, dedekindJensenK_eq] using
    eval_dedekindReciprocal_eq (entireDedekindXi K) d hx

end

end RiemannJensen
