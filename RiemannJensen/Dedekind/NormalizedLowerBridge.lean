module

public import RiemannJensen.Dedekind.RemoteLowerChain

/-!
# Normalized Gaussian estimates on the contour window

A Gaussian estimate for the integral over `[-1, 1]` of the rescaled amplitude and phase transfers,
through the affine change of variables `θ = θ₀ + ℓ y`, to the local contour window
`[θ₀ - ℓ, θ₀ + ℓ]`, and from there to the lower semicircle and the Dedekind lower contribution.

## Main results

* `local_window_estimate_of_normalized`: the normalized Gaussian estimate gives the saddle-point
  estimate on the unnormalized local window.
* `lower_semicircle_estimate_of_normalized`: the lower-semicircle estimate with the local input in
  normalized Gaussian form.
* `dedekind_lower_contribution_of_normalized`: the Dedekind lower contribution estimate from a
  normalized Gaussian estimate and a complementary-arc estimate.
-/

@[expose] public section

namespace RiemannJensen

open Set MeasureTheory intervalIntegral

noncomputable section

/-- The normalized Gaussian estimate, transported through the exact affine
change of variables to the unnormalized local contour window. -/
theorem local_window_estimate_of_normalized
    {a H : ℝ → ℂ} {θ₀ ℓ dd n E : ℝ} {D : ℂ}
    (hℓ : 0 < ℓ) (hdd : 0 < dd) (hD : 0 < D.re)
    (ha : a θ₀ ≠ 0)
    (hn : n = dd * ‖D‖ * ℓ ^ 2)
    (hgauss :
      ‖(∫ y in (-1 : ℝ)..1,
          windowAmp a θ₀ ℓ y *
            Complex.exp ((n : ℂ) * windowPhase H θ₀ ℓ dd n y)) -
          (((Real.pi : ℂ) /
            (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ ≤
        ‖(((Real.pi : ℂ) /
            (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ * E) :
    ‖(1 / (2 * (Real.pi : ℂ))) *
          (∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ),
            a θ * Complex.exp ((dd : ℂ) * H θ)) -
        a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) /
          Complex.sqrt (2 * Real.pi * dd * D)‖ ≤
      ‖a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) /
          Complex.sqrt (2 * Real.pi * dd * D)‖ * E := by
  let X : ℂ := a θ₀ * Complex.exp ((dd : ℂ) * H θ₀)
  let I : ℂ := ∫ y in (-1 : ℝ)..1,
    windowAmp a θ₀ ℓ y *
      Complex.exp ((n : ℂ) * windowPhase H θ₀ ℓ dd n y)
  let G : ℂ := ((Real.pi : ℂ) /
    (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ)
  have hnorm :
      (ℓ : ℂ) * G / (2 * Real.pi) =
        1 / Complex.sqrt (2 * Real.pi * dd * D) := by
    subst n
    exact gaussian_main_term_normalization hD hdd hℓ
  have hcov := integral_window_change
    (a := a) (H := H) (θ₀ := θ₀) (ℓ := ℓ) (dd := dd) (n := n)
    (hn ▸ (mul_pos (mul_pos hdd (norm_pos_iff.2 (Complex.ne_zero_of_re_pos hD)))
      (pow_pos hℓ 2)).ne') ha
  have hXs :
      X / Complex.sqrt (2 * Real.pi * dd * D) =
        X * ((ℓ : ℂ) / (2 * Real.pi)) * G := by
    rw [div_eq_mul_one_div, ← hnorm]
    ring
  have hdiff :
      (1 / (2 * (Real.pi : ℂ))) *
          (∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ),
            a θ * Complex.exp ((dd : ℂ) * H θ)) -
        X / Complex.sqrt (2 * Real.pi * dd * D) =
      X * ((ℓ : ℂ) / (2 * Real.pi)) * (I - G) := by
    rw [hcov, hXs]
    field_simp [Real.pi_ne_zero]
    ring
  change ‖_ - X / Complex.sqrt (2 * Real.pi * dd * D)‖ ≤
    ‖X / Complex.sqrt (2 * Real.pi * dd * D)‖ * E
  rw [hdiff, hXs]
  simp only [norm_mul]
  have hg : ‖I - G‖ ≤ ‖G‖ * E := by simpa [I, G] using hgauss
  exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (by ring)

/-- Splitting an interval integral over `[a, b]` into the middle piece `[u, v]` and the two
outer pieces. -/
theorem intervalIntegral_eq_add_add_of_le {F : ℝ → ℂ} {a b u v : ℝ}
    (hF : IntervalIntegrable F volume a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    ∫ θ in a..b, F θ =
      (∫ θ in u..v, F θ) + ((∫ θ in a..u, F θ) + ∫ θ in v..b, F θ) := by
  have hsub : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable F volume x y :=
    fun x y hx hxy hy => hF.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc hx hy)
  rw [← integral_add_adjacent_intervals (hsub _ _ le_rfl hau (huv.trans hvb))
      (hsub _ _ hau (huv.trans hvb) le_rfl),
    ← integral_add_adjacent_intervals (hsub _ _ hau huv hvb)
      (hsub _ _ (hau.trans huv) hvb le_rfl)]
  ring

/-- The lower-semicircle estimate with the local input supplied directly in
normalized Gaussian form. -/
theorem lower_semicircle_estimate_of_normalized
    {a H : ℝ → ℂ} {θ₀ ℓ dd n E B g : ℝ} {D : ℂ}
    (hℓ : 0 < ℓ) (hdd : 0 < dd) (hD : 0 < D.re)
    (ha : a θ₀ ≠ 0)
    (hn : n = dd * ‖D‖ * ℓ ^ 2)
    (hgauss :
      ‖(∫ y in (-1 : ℝ)..1,
          windowAmp a θ₀ ℓ y *
            Complex.exp ((n : ℂ) * windowPhase H θ₀ ℓ dd n y)) -
          (((Real.pi : ℂ) /
            (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ ≤
        ‖(((Real.pi : ℂ) /
            (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ * E)
    (hleft : -Real.pi ≤ θ₀ - ℓ) (hright : θ₀ + ℓ ≤ 0)
    (hint : IntervalIntegrable
      (fun θ => a θ * Complex.exp ((dd : ℂ) * H θ))
      volume (-Real.pi) 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (θ₀ - ℓ) (θ₀ + ℓ) →
      ‖a θ * Complex.exp ((dd : ℂ) * H θ)‖ ≤
        B * ‖a θ₀‖ * Real.exp (dd * (H θ₀).re) * Real.exp (-g)) :
    ‖(1 / (2 * (Real.pi : ℂ))) *
          (∫ θ in (-Real.pi)..0,
            a θ * Complex.exp ((dd : ℂ) * H θ)) -
        a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) /
          Complex.sqrt (2 * Real.pi * dd * D)‖ ≤
      ‖a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) /
          Complex.sqrt (2 * Real.pi * dd * D)‖ *
        (E + Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) *
          Real.exp (-g)) := by
  let F : ℝ → ℂ := fun θ =>
    a θ * Complex.exp ((dd : ℂ) * H θ)
  let Z : ℂ := a θ₀ * Complex.exp ((dd : ℂ) * H θ₀) /
    Complex.sqrt (2 * Real.pi * dd * D)
  have hloc := local_window_estimate_of_normalized hℓ hdd hD ha hn hgauss
  have htail' := tail_integral_relative_bound
    (D := D) (B := B) (g := g) hdd (Complex.ne_zero_of_re_pos hD) hleft hright hℓ.le htail
  change ‖(1 / (2 * (Real.pi : ℂ))) * (∫ θ in (-Real.pi)..0, F θ) - Z‖ ≤
    ‖Z‖ * (E + Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) *
      Real.exp (-g))
  change ‖(1 / (2 * (Real.pi : ℂ))) *
      (∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ), F θ) - Z‖ ≤ ‖Z‖ * E at hloc
  change ‖(∫ θ in (-Real.pi)..(θ₀ - ℓ), F θ) +
      ∫ θ in (θ₀ + ℓ)..0, F θ‖ ≤
    ‖Z‖ * (Real.pi * B * Real.sqrt (2 * Real.pi * dd * ‖D‖) *
      Real.exp (-g)) at htail'
  rw [intervalIntegral_eq_add_add_of_le (F := F) hint hleft (by linarith) hright, mul_add,
    add_sub_right_comm]
  calc
    _ ≤ ‖(1 / (2 * (Real.pi : ℂ))) *
          (∫ θ in (θ₀ - ℓ)..(θ₀ + ℓ), F θ) - Z‖ +
        ‖(1 / (2 * (Real.pi : ℂ))) *
          ((∫ θ in (-Real.pi)..(θ₀ - ℓ), F θ) +
            ∫ θ in (θ₀ + ℓ)..0, F θ)‖ :=
      norm_add_le _ _
    _ ≤ ‖Z‖ * E +
        (1 / (2 * Real.pi)) *
          (‖Z‖ * (Real.pi * B *
            Real.sqrt (2 * Real.pi * dd * ‖D‖) * Real.exp (-g))) := by
      refine add_le_add hloc ?_
      rw [norm_mul, show ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) by
        simp [abs_of_pos Real.pi_pos]]
      exact mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ ‖Z‖ * (E + Real.pi * B *
        Real.sqrt (2 * Real.pi * dd * ‖D‖) * Real.exp (-g)) := by
      rw [mul_add]
      refine add_le_add le_rfl (mul_le_of_le_one_left ((norm_nonneg _).trans htail') ?_)
      rw [div_le_one (by positivity)]
      linarith [Real.two_le_pi]

/-- The rescaled phase on the Dedekind local window is the Dedekind local phase. -/
theorem windowPhase_dedekind_eq_dedekindLocalPhase
    (K : Type) [Field K] [NumberField K] {d : ℕ} (hd : 0 < d) (q : ℝ) :
    windowPhase (fun θ => dedekindSaddlePhase K d q (dedekindLowerContourPoint K d q θ))
        (-2 * dedekindSaddleAngle K d q) (dedekindLocalWidth K d q) d
        (dedekindEffectiveN K d q) =
      dedekindLocalPhase K d q := by
  funext y
  have hpoint :
      dedekindLowerContourPoint K d q
          (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y) =
        dedekindSaddle K d q *
          Complex.exp (Complex.I * (dedekindLocalWidth K d q : ℂ) * (y : ℂ)) := by
    unfold dedekindLowerContourPoint dedekindSaddle
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold windowPhase dedekindLocalPhase
  simp only
  rw [hpoint, dedekind_saddle_contour_point K d q]
  unfold dedekindEffectiveN
  push_cast
  rw [show (d : ℂ) * (‖dedekindSaddleHessian K d q‖ : ℂ) *
      (dedekindLocalWidth K d q : ℂ) ^ 2 =
      (d : ℂ) * ((‖dedekindSaddleHessian K d q‖ : ℂ) *
        (dedekindLocalWidth K d q : ℂ) ^ 2) by ring, mul_comm _ (d : ℂ)]
  exact mul_div_mul_left _ _ (by exact_mod_cast hd.ne')

/-- Canonical Dedekind lower contribution from a normalized Gaussian estimate
and a complementary-arc estimate. -/
theorem dedekind_lower_contribution_of_normalized
    (K : Type) [Field K] [NumberField K]
    {d : ℕ} (hd : 0 < d) {q E B g : ℝ}
    (hℓ : 0 < dedekindLocalWidth K d q)
    (hD : 0 < (dedekindSaddleHessian K d q).re)
    (ha : dedekindAmplitude K d q
      (-2 * dedekindSaddleAngle K d q) ≠ 0)
    (hgauss :
      let n := dedekindEffectiveN K d q
      let D := dedekindSaddleHessian K d q
      let f := normalizedDedekindLocalAmplitude K d q
      let p := dedekindLocalPhase K d q
      ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
          (((Real.pi : ℂ) /
            (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ ≤
        ‖(((Real.pi : ℂ) /
            (((n / 2 : ℝ) : ℂ) * (D / (‖D‖ : ℂ)))) ^ (1 / 2 : ℂ))‖ * E)
    (hleft : -Real.pi ≤
      -2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
    (hright :
      -2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q ≤ 0)
    (hint : IntervalIntegrable
      (fun θ => dedekindAmplitude K d q θ *
        Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ)))
      volume (-Real.pi) 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo
        (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
        (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q) →
      ‖dedekindAmplitude K d q θ *
        Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
          (dedekindLowerContourPoint K d q θ))‖ ≤
        B * ‖dedekindAmplitude K d q
          (-2 * dedekindSaddleAngle K d q)‖ *
          Real.exp (d * (dedekindSaddlePhase K d q
            (dedekindSaddle K d q)).re) * Real.exp (-g)) :
    ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖ ≤
      ‖dedekindLeadingSaddle K d q‖ *
        (E + Real.pi * B *
          Real.sqrt (2 * Real.pi * d *
            ‖dedekindSaddleHessian K d q‖) * Real.exp (-g)) := by
  let a : ℝ → ℂ := dedekindAmplitude K d q
  let H : ℝ → ℂ := fun θ =>
    dedekindSaddlePhase K d q (dedekindLowerContourPoint K d q θ)
  let θ₀ : ℝ := -2 * dedekindSaddleAngle K d q
  let ℓ : ℝ := dedekindLocalWidth K d q
  let n : ℝ := dedekindEffectiveN K d q
  let D : ℂ := dedekindSaddleHessian K d q
  have hcore := lower_semicircle_estimate_of_normalized
    (a := a) (H := H) (θ₀ := θ₀) (ℓ := ℓ)
    (dd := (d : ℝ)) (n := n) (D := D) (E := E) (B := B) (g := g)
    hℓ (Nat.cast_pos.mpr hd) hD ha
    rfl
    (by
      rw [windowPhase_dedekind_eq_dedekindLocalPhase K hd q]
      exact hgauss)
    hleft hright hint (by
      intro θ hθ hout
      rw [show H θ₀ = dedekindSaddlePhase K d q (dedekindSaddle K d q) from
        congrArg (dedekindSaddlePhase K d q) (dedekind_saddle_contour_point K d q)]
      exact htail θ hθ hout)
  dsimp [a, H, θ₀, ℓ, n, D] at hcore
  rw [dedekind_saddle_contour_point K d q] at hcore
  let P : ℂ := (d.factorial : ℂ) / (d : ℂ) ^ d
  let I : ℂ := (1 / (2 * (Real.pi : ℂ))) *
    ∫ θ in (-Real.pi)..0, dedekindAmplitude K d q θ *
      Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
        (dedekindLowerContourPoint K d q θ))
  let Z : ℂ := dedekindAmplitude K d q
      (-2 * dedekindSaddleAngle K d q) *
    Complex.exp (((d : ℝ) : ℂ) * dedekindSaddlePhase K d q
      (dedekindSaddle K d q)) /
    Complex.sqrt (2 * Real.pi * d * dedekindSaddleHessian K d q)
  have hIz : ‖I - Z‖ ≤ ‖Z‖ *
      (E + Real.pi * B * Real.sqrt
        (2 * Real.pi * d * ‖dedekindSaddleHessian K d q‖) *
          Real.exp (-g)) := by
    simpa [a, H, θ₀, ℓ, n, D, I, Z] using hcore
  have hZ : dedekindLeadingSaddle K d q = P * Z := by
    unfold dedekindLeadingSaddle P Z
    push_cast
    ring
  rw [show dedekindLowerContribution K d q = P * I from rfl, hZ, ← mul_sub, norm_mul, norm_mul]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hIz (norm_nonneg P)

end

end RiemannJensen
