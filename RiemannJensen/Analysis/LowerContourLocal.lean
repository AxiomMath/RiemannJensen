module

public import RiemannJensen.Analysis.GaussianAdapter
public import RiemannJensen.Analysis.GaussianNormalization

/-!
# The local saddle window of the lower contour

A generic form of the local saddle evaluation: on an interval `[θ₀ - ℓ, θ₀ + ℓ]`
the substitution `θ = θ₀ + ℓ y` turns `∫ a(θ) e^{d H(θ)} dθ` into
`ℓ a(θ₀) e^{d H(θ₀)} ∫_{-1}^{1} f(y) e^{n p(y)} dy`, and the uniform Gaussian
estimate then gives the main term `a(θ₀) e^{d H(θ₀)} / √(2π d D)` with relative
error `O(n^{-1/10})`, where `n = d ‖D‖ ℓ²`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set MeasureTheory intervalIntegral

/-- The normalized amplitude on the window: `f(y) = a(θ₀ + ℓ y) / a(θ₀)`. -/
noncomputable def windowAmp (a : ℝ → ℂ) (θ₀ ℓ : ℝ) (y : ℝ) : ℂ :=
  a (θ₀ + ℓ * y) / a θ₀

/-- The normalized phase on the window: `p(y) = d (H(θ₀ + ℓ y) - H(θ₀)) / n`. -/
noncomputable def windowPhase (H : ℝ → ℂ) (θ₀ ℓ dd n : ℝ) (y : ℝ) : ℂ :=
  (H (θ₀ + ℓ * y) - H θ₀) * (dd : ℂ) / (n : ℂ)

/-- The normalized amplitude equals `1` at the window centre `y = 0`. -/
theorem windowAmp_zero {a : ℝ → ℂ} {θ₀ ℓ : ℝ} (ha : a θ₀ ≠ 0) :
    windowAmp a θ₀ ℓ 0 = 1 := by
  simp [windowAmp, ha]

/-- The normalized phase vanishes at the window centre `y = 0`. -/
theorem windowPhase_zero (H : ℝ → ℂ) (θ₀ ℓ dd n : ℝ) :
    windowPhase H θ₀ ℓ dd n 0 = 0 := by
  simp [windowPhase]

/-- The exact change of variables `θ = θ₀ + ℓ y` on the local window. -/
theorem integral_window_change {a H : ℝ → ℂ} {θ₀ ℓ dd n : ℝ} (hn : n ≠ 0)
    (ha : a θ₀ ≠ 0) :
    ∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ), a θ * Complex.exp ((dd : ℂ) * H θ) =
      (ℓ : ℂ) * (a θ₀ * Complex.exp ((dd : ℂ) * H θ₀)) *
        ∫ y in (-1:ℝ)..1, windowAmp a θ₀ ℓ y *
          Complex.exp ((n : ℂ) * windowPhase H θ₀ ℓ dd n y) := by
  have h := intervalIntegral.smul_integral_comp_mul_add
    (fun θ => a θ * Complex.exp ((dd : ℂ) * H θ)) ℓ θ₀ (a := -1) (b := 1)
  rw [show ℓ * (-1) + θ₀ = θ₀ - ℓ by ring, show ℓ * 1 + θ₀ = θ₀ + ℓ by ring] at h
  rw [← h, ← intervalIntegral.integral_const_mul, Complex.real_smul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  have hn' : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hE : (n : ℂ) * windowPhase H θ₀ ℓ dd n y =
      (dd : ℂ) * H (θ₀ + ℓ * y) - (dd : ℂ) * H θ₀ := by
    unfold windowPhase
    field_simp
  simp only [windowAmp]
  rw [hE, Complex.exp_sub, show ℓ * y + θ₀ = θ₀ + ℓ * y by ring]
  have he : Complex.exp ((dd : ℂ) * H θ₀) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The Gaussian error constant `2C² + 6C + 6C/c + 2C²/c²` of
`Gaussian.gaussian_estimate_of_C3_C1`. -/
noncomputable def gaussianErrorConst (c C : ℝ) : ℝ :=
  2 * C ^ 2 + 6 * C + 6 * C / c + 2 * C ^ 2 / c ^ 2

/-- The relative error constant of the local window estimate: the Gaussian error
constant divided by `√(2π)`. -/
noncomputable def windowRelConst (c C : ℝ) : ℝ :=
  gaussianErrorConst c C / Real.sqrt (2 * Real.pi)

/-- For `n > 0`, `√(2π / n) / √(2π) · n^{-1/10} = n^{-3/5}`. -/
lemma sqrt_div_sqrt_mul_rpow {n : ℝ} (hn : 0 < n) :
    Real.sqrt (2 * Real.pi / n) / Real.sqrt (2 * Real.pi) * n ^ (-(1:ℝ)/10) =
      n ^ (-(3:ℝ)/5) := by
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.sqrt_div (by positivity), div_div_cancel_left' hpi.ne', Real.sqrt_eq_rpow,
    ← Real.rpow_neg hn.le, ← Real.rpow_add hn]
  norm_num

/-- **Local window estimate.** With `n = d ‖D‖ ℓ²`, `A = D / ‖D‖`, the normalized
amplitude `f = windowAmp a θ₀ ℓ` and phase `p = windowPhase H θ₀ ℓ d n`, the `C³`/`C¹`
hypotheses of the uniform Gaussian estimate give
`(2π)⁻¹ ∫_{θ₀-ℓ}^{θ₀+ℓ} a e^{dH} = Z (1 + O(n^{-1/10}))` with
`Z = a(θ₀) e^{d H(θ₀)} / √(2π d D)`. -/
theorem local_window_estimate {a H f' p' p'' p''' : ℝ → ℂ} {θ₀ ℓ dd c C : ℝ} {D : ℂ}
    (hℓ : 0 < ℓ) (hdd : 0 < dd) (hD : 0 < D.re) (ha : a θ₀ ≠ 0)
    (hn : 1 ≤ dd * ‖D‖ * ℓ ^ 2) (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (windowAmp a θ₀ ℓ) (f' y) y)
    (hf'_cont : ContinuousOn f' (Icc (-1:ℝ) 1))
    (hp : ∀ y ∈ Icc (-1:ℝ) 1,
      HasDerivAt (windowPhase H θ₀ ℓ dd (dd * ‖D‖ * ℓ ^ 2)) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0) (hp''0 : p'' 0 = -(D / (‖D‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1:ℝ) 1, (windowPhase H θ₀ ℓ dd (dd * ‖D‖ * ℓ ^ 2) y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hf_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖windowAmp a θ₀ ℓ y‖ ≤ C)
    (hf'_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖f' y‖ ≤ C)
    (hp''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ C)
    (hp'''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ C) :
    ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ), a θ * Complex.exp ((dd : ℂ) * H θ)) -
        a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)‖ ≤
      ‖a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)‖ *
        windowRelConst c C * (dd * ‖D‖ * ℓ ^ 2) ^ (-(1:ℝ)/10) := by
  set n : ℝ := dd * ‖D‖ * ℓ ^ 2
  set A : ℂ := D / (‖D‖ : ℂ)
  set X : ℂ := a θ₀ * Complex.exp ((dd : ℂ) * H θ₀)
  set I : ℂ := ∫ y in (-1:ℝ)..1, windowAmp a θ₀ ℓ y *
    Complex.exp ((n : ℂ) * windowPhase H θ₀ ℓ dd n y)
  set G : ℂ := ((Real.pi:ℂ) / (((n/2:ℝ):ℂ) * A)) ^ (1/2:ℂ)
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hAn : ‖A‖ = 1 := norm_div_norm_eq_one hD
  have hAre : 0 < A.re := re_div_norm_pos hD
  have hgauss := Gaussian.gaussian_estimate_of_C3_C1 (A := A) (n := n) hn hc hC hAn hAre hf
    hf'_cont hp hp' hp'' (windowPhase_zero H θ₀ ℓ dd n) hp'0 hp''0 hre hlower hf_bd hf'_bd
    hp''_bd hp'''_bd
  rw [windowAmp_zero ha, one_mul] at hgauss
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hXs : X / Complex.sqrt (2 * Real.pi * dd * D) = X * ((ℓ : ℂ) / (2 * Real.pi)) * G := by
    rw [div_eq_mul_one_div, ← gaussian_main_term_normalization hD hdd hℓ]
    ring
  have hdiff : (1 / (2 * (Real.pi : ℂ))) *
        (∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ), a θ * Complex.exp ((dd : ℂ) * H θ)) -
        X / Complex.sqrt (2 * Real.pi * dd * D) =
      X * ((ℓ : ℂ) / (2 * Real.pi)) * (I - G) := by
    rw [integral_window_change hn0.ne' ha, hXs]
    field_simp
    ring
  have hl : ‖(ℓ : ℂ) / (2 * Real.pi)‖ = ℓ / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos, abs_of_pos hℓ]
  rw [hdiff, hXs, norm_mul _ (I - G), norm_mul _ G, norm_mul X,
    Gaussian.norm_gaussian_main_term hn0 hAn hAre, hl]
  calc ‖X‖ * (ℓ / (2 * Real.pi)) * ‖I - G‖
      ≤ ‖X‖ * (ℓ / (2 * Real.pi)) * (gaussianErrorConst c C * n ^ (-(3:ℝ)/5)) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = ‖X‖ * (ℓ / (2 * Real.pi)) * Real.sqrt (2 * Real.pi / n) * windowRelConst c C *
          n ^ (-(1:ℝ)/10) := by
        rw [← sqrt_div_sqrt_mul_rpow hn0, windowRelConst]
        ring

/-- The modulus of the principal square root. -/
theorem norm_csqrt (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  rw [Complex.sqrt, show (2⁻¹ : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real, Real.sqrt_eq_rpow]

/-- For `d ≥ 0`, `‖2π d D‖ = 2π d ‖D‖`. -/
theorem norm_two_pi_mul (dd : ℝ) (hdd : 0 ≤ dd) (D : ℂ) :
    ‖(2 * Real.pi * dd * D : ℂ)‖ = 2 * Real.pi * dd * ‖D‖ := by
  simp [abs_of_pos Real.pi_pos, abs_of_nonneg hdd]

/-- The modulus of the saddle main term `a(θ₀) e^{d H(θ₀)} / √(2π d D)`. -/
theorem norm_window_main_term {a H : ℝ → ℂ} {θ₀ dd : ℝ} (hdd : 0 ≤ dd) (D : ℂ) :
    ‖a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)‖ =
      ‖a θ₀‖ * Real.exp (dd * (H θ₀).re) / Real.sqrt (2 * Real.pi * dd * ‖D‖) := by
  rw [norm_div, norm_mul, norm_csqrt, norm_two_pi_mul dd hdd, Complex.norm_exp,
    Complex.re_ofReal_mul]

/-- **Tail bound.** If the integrand is bounded by `M` on `[-π, 0]` outside the
open window `(θ₀ - ℓ, θ₀ + ℓ) ⊆ [-π, 0]`, the two remaining pieces contribute at
most `π M`. -/
theorem tail_integral_bound {F : ℝ → ℂ} {θ₀ ℓ M : ℝ}
    (h1 : -Real.pi ≤ θ₀ - ℓ) (h2 : θ₀ + ℓ ≤ 0) (hℓ : 0 ≤ ℓ)
    (hF : ∀ θ ∈ Icc (-Real.pi) 0, θ ∉ Ioo (θ₀ - ℓ) (θ₀ + ℓ) → ‖F θ‖ ≤ M) :
    ‖(∫ θ in (-Real.pi)..(θ₀ - ℓ), F θ) + ∫ θ in (θ₀ + ℓ)..0, F θ‖ ≤ Real.pi * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hF (-Real.pi) ⟨le_rfl, by linarith [Real.pi_pos]⟩ (fun h => by linarith [h.1]))
  have hA : ‖∫ θ in (-Real.pi)..(θ₀ - ℓ), F θ‖ ≤ M * |θ₀ - ℓ - -Real.pi| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [uIoc_of_le h1] at hθ
    exact hF θ ⟨hθ.1.le, by linarith [hθ.2]⟩ (fun h => by linarith [h.1, hθ.2])
  have hB : ‖∫ θ in (θ₀ + ℓ)..0, F θ‖ ≤ M * |0 - (θ₀ + ℓ)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [uIoc_of_le h2] at hθ
    exact hF θ ⟨by linarith [hθ.1], hθ.2⟩ (fun h => by linarith [h.2, hθ.1])
  rw [abs_of_nonneg (by linarith)] at hA hB
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ M * (θ₀ - ℓ - -Real.pi) + M * (0 - (θ₀ + ℓ)) := add_le_add hA hB
    _ ≤ Real.pi * M := by nlinarith

/-- The tail bound relative to the main term: with
`M = B ‖a(θ₀)‖ e^{d Re H(θ₀)} e^{-g}`, the remaining integral is at most
`‖Z‖ π B √(2π d ‖D‖) e^{-g}`. -/
theorem tail_integral_relative_bound {a H : ℝ → ℂ} {θ₀ ℓ dd B g : ℝ} {D : ℂ}
    (hdd : 0 < dd) (hD : D ≠ 0)
    (h1 : -Real.pi ≤ θ₀ - ℓ) (h2 : θ₀ + ℓ ≤ 0) (hℓ : 0 ≤ ℓ)
    (hF : ∀ θ ∈ Icc (-Real.pi) 0, θ ∉ Ioo (θ₀ - ℓ) (θ₀ + ℓ) →
      ‖a θ * Complex.exp ((dd : ℂ) * H θ)‖ ≤
        B * ‖a θ₀‖ * Real.exp (dd * (H θ₀).re) * Real.exp (-g)) :
    ‖(∫ θ in (-Real.pi)..(θ₀ - ℓ), a θ * Complex.exp ((dd : ℂ) * H θ)) +
        ∫ θ in (θ₀ + ℓ)..0, a θ * Complex.exp ((dd : ℂ) * H θ)‖ ≤
      ‖a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)‖ *
        (Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) * Real.exp (-g)) := by
  refine (tail_integral_bound h1 h2 hℓ hF).trans (le_of_eq ?_)
  rw [norm_window_main_term hdd.le]
  have hs : 0 < Real.sqrt (2 * Real.pi * dd * ‖D‖) :=
    Real.sqrt_pos.mpr (by have := norm_pos_iff.mpr hD; positivity)
  field_simp

/-- Splitting an interval integral over `[a, b]` into a window `[u, v]` and the two tails. -/
theorem integral_eq_window_add_tails {F : ℝ → ℂ} {a b u v : ℝ}
    (hint : IntervalIntegrable F volume a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (∫ θ in a..b, F θ) =
      (∫ θ in u..v, F θ) + ((∫ θ in a..u, F θ) + ∫ θ in v..b, F θ) := by
  have hsub : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable F volume x y :=
    fun x y hx hxy hy => hint.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc hx hy)
  rw [← integral_add_adjacent_intervals (hsub _ _ le_rfl hau (by linarith))
      (hsub _ _ hau (by linarith) le_rfl),
    ← integral_add_adjacent_intervals (hsub _ _ hau huv (by linarith))
      (hsub _ _ (by linarith) hvb le_rfl)]
  ring

/-- **Lower semicircle estimate (generic form).** The local window estimate plus
the tail bound: `(2π)⁻¹ ∫_{-π}^{0} a e^{dH} = Z (1 + O(n^{-1/10}) + O(√(2π d‖D‖) e^{-g}))`
with explicit constants, where `Z = a(θ₀) e^{d H(θ₀)} / √(2π d D)` and
`n = d ‖D‖ ℓ²`. -/
theorem lower_semicircle_estimate {a H f' p' p'' p''' : ℝ → ℂ} {θ₀ ℓ dd c C B g : ℝ} {D : ℂ}
    (hℓ : 0 < ℓ) (hdd : 0 < dd) (hD : 0 < D.re) (ha : a θ₀ ≠ 0)
    (hn : 1 ≤ dd * ‖D‖ * ℓ ^ 2) (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (windowAmp a θ₀ ℓ) (f' y) y)
    (hf'_cont : ContinuousOn f' (Icc (-1:ℝ) 1))
    (hp : ∀ y ∈ Icc (-1:ℝ) 1,
      HasDerivAt (windowPhase H θ₀ ℓ dd (dd * ‖D‖ * ℓ ^ 2)) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0) (hp''0 : p'' 0 = -(D / (‖D‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1:ℝ) 1, (windowPhase H θ₀ ℓ dd (dd * ‖D‖ * ℓ ^ 2) y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hf_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖windowAmp a θ₀ ℓ y‖ ≤ C)
    (hf'_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖f' y‖ ≤ C)
    (hp''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ C)
    (hp'''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ C)
    (h1 : -Real.pi ≤ θ₀ - ℓ) (h2 : θ₀ + ℓ ≤ 0)
    (hint : IntervalIntegrable (fun θ => a θ * Complex.exp ((dd : ℂ) * H θ)) volume
      (-Real.pi) 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0, θ ∉ Ioo (θ₀ - ℓ) (θ₀ + ℓ) →
      ‖a θ * Complex.exp ((dd : ℂ) * H θ)‖ ≤
        B * ‖a θ₀‖ * Real.exp (dd * (H θ₀).re) * Real.exp (-g)) :
    ‖(1 / (2 * (Real.pi : ℂ))) *
        (∫ θ in (-Real.pi)..0, a θ * Complex.exp ((dd : ℂ) * H θ)) -
        a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)‖ ≤
      ‖a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)‖ *
        (windowRelConst c C * (dd * ‖D‖ * ℓ ^ 2) ^ (-(1:ℝ)/10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) * Real.exp (-g)) := by
  set Z : ℂ := a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) / Complex.sqrt (2 * Real.pi * dd * D)
  have hD0 : D ≠ 0 := fun h => by simp [h] at hD
  have hloc := local_window_estimate hℓ hdd hD ha hn hc hC hf hf'_cont hp hp' hp'' hp'0 hp''0
    hre hlower hf_bd hf'_bd hp''_bd hp'''_bd
  have htl := tail_integral_relative_bound (B := B) (g := g) hdd hD0 h1 h2 hℓ.le htail
  have hnorm2pi : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  have hT0 : 0 ≤ ‖Z‖ * (Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) * Real.exp (-g)) :=
    (norm_nonneg _).trans htl
  rw [integral_eq_window_add_tails hint h1 (by linarith) h2, mul_add, add_sub_right_comm]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ‖Z‖ * windowRelConst c C * (dd * ‖D‖ * ℓ ^ 2) ^ (-(1:ℝ)/10) +
          1 / (2 * Real.pi) *
            (‖Z‖ * (Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) * Real.exp (-g))) := by
        refine add_le_add hloc ?_
        rw [norm_mul, hnorm2pi]
        exact mul_le_mul_of_nonneg_left htl (by positivity)
    _ ≤ _ := by
        have : 1 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [Real.two_le_pi]
        nlinarith

end RiemannJensen
