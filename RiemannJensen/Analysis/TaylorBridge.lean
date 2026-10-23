module

public import RiemannJensen.Xi
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The Taylor bridge from xi to its square-root model

This file proves the coefficient-level facts needed to identify the defining series of `riemannF`
with the even Taylor series of `centeredXi`: the functions `riemannXi` and `centeredXi` commute
with complex conjugation, the odd derivatives of `centeredXi` at the origin vanish, and its Taylor
derivatives there are real.
-/

@[expose] public section

namespace RiemannJensen

open Complex

private theorem riemannZeta_star_aux (s : ℂ) :
    riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conj s

private theorem gammaR_star_aux (s : ℂ) :
    (star s).Gammaℝ = star s.Gammaℝ := by
  rw [Complex.star_def]
  have hpi : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  have h := cpow_conj (Real.pi : ℂ) (-s / 2) hpi
  rw [conj_ofReal] at h
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Gamma_conj, ← h]
  congr 2 <;> simp [map_div₀, map_neg, map_ofNat]

private theorem completedRiemannZeta_star_of_re_pos_aux (s : ℂ)
    (hs : 0 < s.re) :
    completedRiemannZeta (star s) = star (completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := ne_of_apply_ne Complex.re (by simpa using ne_of_gt hs)
  have hss0 : star s ≠ 0 := star_ne_zero.mpr hs0
  have hg : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hgs : (star s).Gammaℝ ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simpa using hs)
  have h := (eq_div_iff hg).mp (riemannZeta_def_of_ne_zero hs0)
  have hstar := (eq_div_iff hgs).mp (riemannZeta_def_of_ne_zero hss0)
  rw [← hstar, riemannZeta_star_aux, gammaR_star_aux, Complex.star_def, ← map_mul]
  exact congrArg (starRingEnd ℂ) h

private theorem completedRiemannZeta_star_aux (s : ℂ) :
    completedRiemannZeta (star s) = star (completedRiemannZeta s) := by
  rcases lt_or_ge 0 s.re with hs | hs
  · exact completedRiemannZeta_star_of_re_pos_aux s hs
  · have h1 : 0 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    have hcs : star (1 - s) = 1 - star s := by simp
    have h := completedRiemannZeta_star_of_re_pos_aux (1 - s) h1
    rwa [hcs, completedRiemannZeta_one_sub, completedRiemannZeta_one_sub] at h

private theorem completedRiemannZeta₀_star_aux (s : ℂ) :
    completedRiemannZeta₀ (star s) = star (completedRiemannZeta₀ s) := by
  have h := completedRiemannZeta_star_aux s
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq] at h
  rw [Complex.star_def] at h ⊢
  simp only [map_sub, map_div₀, map_one] at h
  linear_combination h

/-- Riemann's xi function commutes with complex conjugation. -/
theorem riemannXi_star (s : ℂ) : riemannXi (star s) = star (riemannXi s) := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_star_aux, Complex.star_def]
  simp only [map_div₀, map_add, map_mul, map_sub, map_one, map_ofNat]

/-- The centered xi function commutes with complex conjugation. -/
theorem centeredXi_star (w : ℂ) : centeredXi (star w) = star (centeredXi w) := by
  unfold centeredXi
  rw [← riemannXi_star]
  congr 1
  rw [Complex.star_def]
  simp only [map_add, map_div₀, map_one, map_ofNat]

/-- Every odd derivative at the origin of the even function `centeredXi`
vanishes. -/
theorem iteratedDeriv_centeredXi_odd (n : ℕ) :
    iteratedDeriv (2 * n + 1) centeredXi 0 = 0 := by
  have heven : (fun z : ℂ ↦ centeredXi (-z)) = centeredXi :=
    funext centeredXi_neg
  have h := congrFun (congrArg (iteratedDeriv (2 * n + 1)) heven) 0
  rw [iteratedDeriv_comp_neg] at h
  simp only [neg_zero] at h
  have hpow : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    simp
  rw [hpow, neg_one_smul] at h
  linear_combination -h / 2

private theorem iteratedDeriv_centeredXi_star : ∀ n : ℕ,
    (starRingEnd ℂ ∘ iteratedDeriv n centeredXi ∘ starRingEnd ℂ) =
      iteratedDeriv n centeredXi := by
  intro n
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero]
      funext w
      simp only [Function.comp_apply]
      have hs := centeredXi_star w
      rw [Complex.star_def] at hs
      rw [hs]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      calc
        (starRingEnd ℂ ∘ deriv (iteratedDeriv n centeredXi) ∘ starRingEnd ℂ) =
            deriv (starRingEnd ℂ ∘ iteratedDeriv n centeredXi ∘ starRingEnd ℂ) :=
          deriv_conj_conj.symm
        _ = deriv (iteratedDeriv n centeredXi) := congrArg deriv ih

/-- Every Taylor derivative of `centeredXi` at the real point zero is real. -/
theorem iteratedDeriv_centeredXi_zero_im (n : ℕ) :
    (iteratedDeriv n centeredXi 0).im = 0 := by
  have h := congrFun (iteratedDeriv_centeredXi_star n) 0
  simp only [Function.comp_apply, map_zero] at h
  exact Complex.conj_eq_iff_im.mp h

/-- In particular, the even Taylor derivatives used in `gammaCoeff` are real. -/
theorem iteratedDeriv_centeredXi_even_im (n : ℕ) :
    (iteratedDeriv (2 * n) centeredXi 0).im = 0 :=
  iteratedDeriv_centeredXi_zero_im (2 * n)

/-- The normalized even Taylor coefficient is exactly the coefficient used in
`riemannF`. -/
theorem centeredXi_even_taylorCoeff (j : ℕ) :
    ((2 * j).factorial : ℂ)⁻¹ * iteratedDeriv (2 * j) centeredXi 0 =
      (gammaCoeff j : ℂ) / (j.factorial : ℂ) := by
  have hd : iteratedDeriv (2 * j) centeredXi 0 =
      (iteratedDeriv (2 * j) centeredXi 0).re := by
    apply Complex.ext
    · simp
    · simp [iteratedDeriv_centeredXi_even_im]
  have hj : (j.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have h2j : ((2 * j).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j)
  rw [hd]
  unfold gammaCoeff
  push_cast
  field_simp [hj, h2j]

private theorem hasSum_riemannF_sq (w : ℂ) :
    HasSum (fun j : ℕ ↦ (gammaCoeff j : ℂ) / (j.factorial : ℂ) * (w ^ 2) ^ j)
      (centeredXi w) := by
  have hinj : Function.Injective (2 * · : ℕ → ℕ) := fun _ _ h ↦ by simpa using h
  have ht : HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ • w ^ n • iteratedDeriv n centeredXi 0)
      (centeredXi w) := by
    simpa only [sub_zero] using
      Complex.hasSum_taylorSeries_of_entire differentiable_centeredXi 0 w
  refine ((hinj.hasSum_iff fun n hn ↦ ?_).mpr ht).congr_fun fun j ↦ ?_
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact absurd ⟨k, rfl⟩ hn
    · simp [iteratedDeriv_centeredXi_odd]
  · rw [← centeredXi_even_taylorCoeff, ← pow_mul]
    simp only [Function.comp_apply, smul_eq_mul]
    ring

/-- The square-root series is the centered xi function after substituting a
square. -/
theorem riemannF_sq (w : ℂ) : riemannF (w ^ 2) = centeredXi w :=
  (hasSum_riemannF_sq w).tsum_eq

private noncomputable def riemannFCoeff (j : ℕ) : ℂ :=
  (gammaCoeff j : ℂ) / (j.factorial : ℂ)

private noncomputable def riemannFSeries :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ riemannFCoeff

private theorem summable_riemannFCoeff_mul_pow (z : ℂ) :
    Summable fun j : ℕ ↦ riemannFCoeff j * z ^ j := by
  obtain ⟨w, rfl⟩ := Complex.isSquare z
  simpa [riemannFCoeff, pow_two] using (hasSum_riemannF_sq w).summable

/-- The formal scalar series defining `riemannF` has infinite radius of
convergence. -/
private theorem riemannFSeries_radius :
    riemannFSeries.radius = ⊤ := by
  apply riemannFSeries.radius_eq_top_of_summable_norm
  intro r
  have h := (summable_riemannFCoeff_mul_pow (r : ℂ)).norm
  simpa [riemannFSeries, FormalMultilinearSeries.ofScalars_norm, norm_mul] using h

/-- `riemannF` is the sum of its associated formal multilinear series. -/
private theorem riemannF_eq_series_sum :
    riemannF = riemannFSeries.sum := by
  funext z
  rw [riemannF]
  change (∑' j : ℕ, (gammaCoeff j : ℂ) / (j.factorial : ℂ) * z ^ j) =
    FormalMultilinearSeries.ofScalarsSum riemannFCoeff z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  rfl

/-- The square-root model of Riemann's xi function is entire. -/
theorem differentiable_riemannF : Differentiable ℂ riemannF := by
  rw [riemannF_eq_series_sum]
  have hp := riemannFSeries.hasFPowerSeriesOnBall
    (by simp [riemannFSeries_radius])
  intro z
  exact (hp.analyticAt_of_mem (by simp [riemannFSeries_radius])).differentiableAt

/-- The Taylor jet of `riemannF` at the origin is the coefficient sequence
`gammaCoeff`. -/
theorem iteratedDeriv_riemannF_zero (j : ℕ) :
    iteratedDeriv j riemannF 0 = (gammaCoeff j : ℂ) := by
  have hp : HasFPowerSeriesOnBall riemannF riemannFSeries 0 ⊤ := by
    rw [riemannF_eq_series_sum]
    simpa only [riemannFSeries_radius] using
      riemannFSeries.hasFPowerSeriesOnBall
        (by simp [riemannFSeries_radius])
  have h := hp.factorial_smul (1 : ℂ) j
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h]
  simp only [riemannFSeries, riemannFCoeff,
    FormalMultilinearSeries.ofScalars_apply_eq, one_pow]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_eq_mul]
  have hj : (j.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  field_simp [hj]

end RiemannJensen
