module

public import Mathlib
public import RiemannJensen.Dedekind.CompletedZetaPackageSource
public import RiemannJensen.Dedekind.PrimesOverCard

/-!
# Polynomial bounds for the Dedekind zeta function in vertical strips

For a number field `K` of degree `N = [K : ℚ]`, we bound a continuation `f` of the Dedekind zeta
function `ζ_K` by `C * (1 + |Im s|) ^ N` on the line `Re s = -1/2`, on the strip
`-1/2 ≤ Re s ≤ 3/2` away from the pole, and on the half-plane `Re s ≥ 1/2` away from the pole.
The left line follows from the functional equation of the completed zeta function `Λ_K` and the
Euler-product bound on `Re s = 3/2`; the strip follows by a Phragmén–Lindelöf argument applied to
`(s - 1) ζ_K(s) / (s - 2)`, using an a priori Gaussian bound `B * exp (C * (Im s) ^ 2)` for the
entire function `(s - 1) ζ_K(s)`.

## Main results

* `NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq`: an entire
  extension of `(s - 1) ζ_K(s)` is bounded by `B * exp (C * (Im s) ^ 2)` in every vertical strip.
* `exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero`
  (in the namespace `NumberField`): `(s - 1) ζ_K(s)` extends to an entire function, nonzero at
  `1`, vanishing at `-2 (n + 1)`.
* `PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip`: the
  Phragmén–Lindelöf principle in a vertical strip with polynomial boundary bounds.
* `NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta`: the Euler product of `ζ_K`
  for `Re s > 1`.
* `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt`: `∑_𝔭 N(𝔭) ^ (-σ)`
  converges for `σ > 1`.
* `EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp`: a bound for the norm of an
  Euler product with coefficients of norm at most `1`.
* `AntRHScratch.left_line`, `AntRHScratch.right_line`, `AntRHScratch.strip`,
  `AntRHScratch.global`: bounds for a continuation of `ζ_K` on `Re s = -1/2`, on `Re s = 3/2`,
  on the strip `-1/2 ≤ Re s ≤ 3/2` and on the half-plane `Re s ≥ 1/2`.
-/

@[expose] public section

section

set_option backward.isDefEq.respectTransparency.types false

/-- There is a function `Λ`, differentiable off `{0, 1}`, satisfying `Λ (1 - s) = Λ s`, equal to
`|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ζ_K(s)` for `Re s > 1`, such that every entire `ξ` with
`ξ s = s (s - 1) Λ s` off `{0, 1}` is nonzero at `0` and `1`, and some such `ξ` has order at
most one: `log ‖ξ s‖ ≤ C ‖s‖ log ‖s‖` for `‖s‖ ≥ 2`. -/
theorem NumberField.exists_completedDedekindZeta_package_core
    (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
          Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) →
        ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) := by
  obtain ⟨Λ, hdiff, hfe, hprod, hgrowth, hend, _⟩ :=
    P2MW.S_NumberField_exists_completedDedekindZeta_package.solution K
  exact ⟨Λ, hdiff, hfe, hprod, hgrowth, hend⟩

end

set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq

set_option autoImplicit false

noncomputable section

open NumberField Complex Filter Set
open scoped Topology Real

namespace R4Z2a

/-- `‖sin z‖ ≤ exp |Im z|`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by simp [Complex.norm_exp]
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by simp [Complex.norm_exp]
  have hle1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hle2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; simp
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by rw [h1, h2]; linarith

/-- For `Re w > 0`, `‖Γ(w)‖ ≤ Γ(Re w)`. -/
theorem norm_Gamma_le_real_Gamma (w : ℂ) (hw : 0 < w.re) : ‖Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Complex.GammaIntegral, Real.Gamma_eq_integral hw]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx', sub_re, one_re]

/-- If `|Im w| ≥ 1`, then `‖Γ(w)‖ ≤ ‖Γ(w + m)‖` for every natural number `m`. -/
theorem norm_Gamma_le_norm_Gamma_add_nat (w : ℂ) (hw : 1 ≤ |w.im|) (m : ℕ) :
    ‖Gamma w‖ ≤ ‖Gamma (w + m)‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : w + m ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at hw; norm_num at hw
    have hnorm : 1 ≤ ‖w + m‖ := by
      calc (1 : ℝ) ≤ |w.im| := hw
        _ = |(w + m).im| := by simp
        _ ≤ ‖w + m‖ := abs_im_le_norm _
    have hstep : Gamma (w + (m + 1 : ℕ)) = (w + m) * Gamma (w + m) := by
      rw [show w + ((m + 1 : ℕ) : ℂ) = (w + m) + 1 by push_cast; ring]
      exact Complex.Gamma_add_one _ hne
    rw [hstep, norm_mul]
    exact ih.trans (le_mul_of_one_le_left (norm_nonneg _) hnorm)

/-- For `1 ≤ x ≤ X`, `Γ(x) ≤ max 1 Γ(X)`. -/
theorem real_Gamma_le_max (x X : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ X) : Real.Gamma x ≤ max 1 (Real.Gamma X) := by
  have hX : 1 ≤ X := h1.trans h2
  have hseg : x ∈ segment ℝ (1 : ℝ) X := by rw [segment_eq_Icc hX]; exact ⟨h1, h2⟩
  have h := Real.convexOn_Gamma.le_on_segment (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (show X ∈ Set.Ioi (0 : ℝ) from lt_of_lt_of_le one_pos hX) hseg
  rwa [Real.Gamma_one] at h

/-- On the strip `a ≤ Re s ≤ b` with `|Im s| ≥ 1`, `‖Γ(s)⁻¹‖ ≤ B exp (π |Im s|)` for some
`B > 0`. -/
theorem norm_inv_Gamma_le (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(Gamma s)⁻¹‖ ≤ B * Real.exp (Real.pi * |s.im|) := by
  set m : ℕ := Nat.ceil b with hm
  set X : ℝ := 1 + m - a with hX
  refine ⟨max 1 (Real.Gamma X), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro s hsa hsb hsi
  have hmb : b ≤ m := Nat.le_ceil b
  have him0 : s.im ≠ 0 := by
    intro h; rw [h] at hsi; norm_num at hsi

  have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff, not_exists]
    intro k hk
    have := congrArg Complex.im hk
    simp at this
    exact him0 this
  have hΓ : Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n h => ?_
    have := congrArg Complex.im h
    simp at this
    exact him0 this

  have hπ0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
    have h1 : Gamma s * (Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi) = 1 := by
      rw [← mul_div_assoc, ← mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
      field_simp
    exact (eq_inv_of_mul_eq_one_right h1).symm

  have h1s_im : 1 ≤ |(1 - s).im| := by simpa using hsi
  have hshift := norm_Gamma_le_norm_Gamma_add_nat (1 - s) h1s_im m
  have hre : (1 - s + m).re = 1 + m - s.re := by simp; ring
  have hre_pos : 0 < (1 - s + m).re := by rw [hre]; linarith
  have hreal := norm_Gamma_le_real_Gamma (1 - s + m) hre_pos
  rw [hre] at hreal
  have hmax := real_Gamma_le_max (1 + m - s.re) X (by linarith) (by rw [hX]; linarith)
  have hΓ1s : ‖Gamma (1 - s)‖ ≤ max 1 (Real.Gamma X) := hshift.trans (hreal.trans hmax)

  have hsinle : ‖Complex.sin (Real.pi * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
    have := norm_sin_le_exp_abs_im (Real.pi * s)
    have him : |((Real.pi : ℂ) * s).im| = Real.pi * |s.im| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rwa [him] at this
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  exact (div_le_self (by positivity) (by linarith [Real.pi_gt_three])).trans
    (mul_le_mul hΓ1s hsinle (norm_nonneg _) (zero_le_one.trans (le_max_left _ _)))

/-- `f` satisfies `‖f s‖ ≤ B exp (C (Im s) ^ 2)` for some `B, C ≥ 0` on the strip
`a ≤ Re s ≤ b` with `|Im s| ≥ 2`. -/
def GaussBdd (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
    ‖f s‖ ≤ B * Real.exp (C * s.im ^ 2)

/-- The product of two functions satisfying `GaussBdd a b` satisfies `GaussBdd a b`. -/
theorem GaussBdd.mul {a b : ℝ} {f g : ℂ → ℂ} (hf : GaussBdd a b f) (hg : GaussBdd a b g) :
    GaussBdd a b (fun s => f s * g s) := by
  obtain ⟨B₁, C₁, hB₁, hC₁, h₁⟩ := hf
  obtain ⟨B₂, C₂, hB₂, hC₂, h₂⟩ := hg
  refine ⟨B₁ * B₂, C₁ + C₂, mul_nonneg hB₁ hB₂, add_nonneg hC₁ hC₂, fun s hsa hsb hsi => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  calc ‖f s‖ * ‖g s‖ ≤ (B₁ * Real.exp (C₁ * s.im ^ 2)) * (B₂ * Real.exp (C₂ * s.im ^ 2)) :=
        mul_le_mul (h₁ s hsa hsb hsi) (h₂ s hsa hsb hsi) (norm_nonneg _) (by positivity)
    _ = B₁ * B₂ * (Real.exp (C₁ * s.im ^ 2) * Real.exp (C₂ * s.im ^ 2)) := by ring

/-- A natural power of a function satisfying `GaussBdd a b` satisfies `GaussBdd a b`. -/
theorem GaussBdd.pow {a b : ℝ} {f : ℂ → ℂ} (hf : GaussBdd a b f) (n : ℕ) :
    GaussBdd a b (fun s => f s ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, zero_le_one, le_rfl, fun s _ _ _ => by simp⟩
  | succ n ih =>
    simpa [pow_succ] using ih.mul hf

/-- A function bounded by a constant on the relevant part of the strip satisfies `GaussBdd a b`. -/
theorem gaussBdd_of_norm_le {a b : ℝ} {f : ℂ → ℂ} (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| → ‖f s‖ ≤ M) : GaussBdd a b f :=
  ⟨M, 0, hM, le_rfl, fun s hsa hsb hsi => by simpa using h s hsa hsb hsi⟩

/-- `|t| ≤ 1 + t ^ 2`. -/
theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1)]

/-- A function bounded by `M exp (c |Im s|)` with `M, c ≥ 0` on the relevant part of the strip
satisfies `GaussBdd a b`. -/
theorem gaussBdd_of_norm_le_exp {a b : ℝ} {f : ℂ → ℂ} (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (h : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| → ‖f s‖ ≤ M * Real.exp (c * |s.im|)) :
    GaussBdd a b f := by
  refine ⟨M * Real.exp c, c, by positivity, hc, fun s hsa hsb hsi => ?_⟩
  refine (h s hsa hsb hsi).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
  have := abs_le_one_add_sq s.im
  nlinarith

section ident

variable (K : Type) [Field K] [NumberField K]

/-- The absolute value `|d_K|` of the discriminant of `K`, as a real number. -/
def absDiscr : ℝ := ((|NumberField.discr K| : ℤ) : ℝ)

/-- `|d_K| > 0`. -/
theorem absDiscr_pos : 0 < absDiscr K := by
  unfold absDiscr
  exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)

/-- The complex cast of `|d_K|` is the complex cast of `absDiscr K`. -/
theorem intCast_abs_discr_eq_ofReal_absDiscr :
    (((|NumberField.discr K| : ℤ)) : ℂ) = (absDiscr K : ℂ) := by
  unfold absDiscr; exact (Complex.ofReal_intCast _).symm

/-- `|d_K| ≥ 1`. -/
theorem one_le_absDiscr : 1 ≤ absDiscr K := by
  unfold absDiscr
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

/-- The function `(|d_K| ^ (s / 2))⁻¹ (Γ_ℝ(s)⁻¹) ^ r₁ (Γ_ℂ(s)⁻¹) ^ r₂`, the reciprocal of the
archimedean and discriminant factors of the completed Dedekind zeta function. -/
def invGammaFactor (s : ℂ) : ℂ :=
  ((absDiscr K : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K

/-- `invGammaFactor K` is entire. -/
theorem differentiable_invGammaFactor : Differentiable ℂ (invGammaFactor K) := by
  unfold invGammaFactor
  refine ((Differentiable.inv ?_ ?_).mul (differentiable_Gammaℝ_inv.pow _)).mul
    (differentiable_Gammaℂ_inv.pow _)
  · exact Differentiable.const_cpow (differentiable_id.div_const 2)
      (Or.inl (ofReal_ne_zero.mpr (absDiscr_pos K).ne'))
  · intro s
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr (absDiscr_pos K).ne')

/-- The complement of `{0, 1}` in `ℂ` is open. -/
theorem isOpen_compl01 : IsOpen ({(0 : ℂ), 1}ᶜ : Set ℂ) :=
  (Set.toFinite _).isClosed.isOpen_compl

/-- The complement of `{0, 1}` in `ℂ` is preconnected. -/
theorem isPreconnected_compl01 : IsPreconnected ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
  have hc : ({(0 : ℂ), 1} : Set ℂ).Countable := (Set.toFinite _).countable
  have hr : 1 < Module.rank ℝ ℂ := by simp
  exact (hc.isConnected_compl_of_one_lt_rank hr).isPreconnected

/-- For `Re s > 1`, `ζ_K(s) = Λ(s) invGammaFactor K s` where `Λ` is the completed Dedekind zeta
function. -/
theorem dedekindZeta_eq_mul_invGammaFactor (Λ : ℂ → ℂ)
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = Λ s * invGammaFactor K s := by
  have hs0 : 0 < s.re := by linarith
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hΓℂ : Gammaℂ s ≠ 0 := by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs0)
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hD : (absDiscr K : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr (absDiscr_pos K).ne')
  rw [hΛeq s hs, intCast_abs_discr_eq_ofReal_absDiscr]
  unfold invGammaFactor
  set r₁ : ℕ := NumberField.InfinitePlace.nrRealPlaces K
  set r₂ : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  have e1 : (absDiscr K : ℂ) ^ (s / 2) * ((absDiscr K : ℂ) ^ (s / 2))⁻¹ = 1 := mul_inv_cancel₀ hD
  have e2 : Gammaℝ s ^ r₁ * (Gammaℝ s)⁻¹ ^ r₁ = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hΓℝ, one_pow]
  have e3 : Gammaℂ s ^ r₂ * (Gammaℂ s)⁻¹ ^ r₂ = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hΓℂ, one_pow]
  calc dedekindZeta K s
      = dedekindZeta K s *
          ((absDiscr K : ℂ) ^ (s / 2) * ((absDiscr K : ℂ) ^ (s / 2))⁻¹) *
          (Gammaℝ s ^ r₁ * (Gammaℝ s)⁻¹ ^ r₁) * (Gammaℂ s ^ r₂ * (Gammaℂ s)⁻¹ ^ r₂) := by
        rw [e1, e2, e3]; ring
    _ = ((absDiscr K : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ * dedekindZeta K s) *
          (((absDiscr K : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) := by ring

/-- An entire extension `R` of `(s - 1) ζ_K(s)` equals `(s - 1) Λ(s) invGammaFactor K s` off
`{0, 1}`. -/
theorem R_eq (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s)
    (Λ : ℂ → ℂ) (hΛd : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) :
    Set.EqOn R (fun s => (s - 1) * Λ s * invGammaFactor K s) ({(0 : ℂ), 1}ᶜ) := by
  set g : ℂ → ℂ := fun s => (s - 1) * Λ s * invGammaFactor K s with hg
  have hRan : AnalyticOnNhd ℂ R ({(0 : ℂ), 1}ᶜ) := hR.differentiableOn.analyticOnNhd isOpen_compl01
  have hgd : DifferentiableOn ℂ g ({(0 : ℂ), 1}ᶜ) :=
    (((differentiable_id.sub_const 1).differentiableOn).mul hΛd).mul
      (differentiable_invGammaFactor K).differentiableOn
  have hgan : AnalyticOnNhd ℂ g ({(0 : ℂ), 1}ᶜ) := hgd.analyticOnNhd isOpen_compl01
  have h2mem : (2 : ℂ) ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  have hagree : ∀ s : ℂ, 1 < s.re → R s = g s := fun s hs => by
    rw [hRζ s hs, dedekindZeta_eq_mul_invGammaFactor K Λ hΛeq hs]
    exact (mul_assoc _ _ _).symm
  have hev : R =ᶠ[𝓝 (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)) hagree
  exact hRan.eqOn_of_preconnected_of_eventuallyEq hgan isPreconnected_compl01 h2mem hev

end ident

section pieces

variable (K : Type) [Field K] [NumberField K]

/-- On the strip `a ≤ Re s ≤ b`, `‖s‖ ≤ |a| + |b| + |Im s|`. -/
theorem norm_le_of_strip {a b : ℝ} (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖s‖ ≤ (|a| + |b|) + |s.im| := by
  have hre : |s.re| ≤ |a| + |b| := by
    rcases le_or_gt 0 s.re with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a]
    · rw [abs_of_neg h]; linarith [neg_le_abs a, abs_nonneg b]
  linarith [norm_le_abs_re_add_abs_im s]

/-- `s ↦ (|d_K| ^ (s / 2))⁻¹` satisfies `GaussBdd a b`. -/
theorem gaussBdd_D_inv (a b : ℝ) : GaussBdd a b (fun s => ((absDiscr K : ℂ) ^ (s / 2))⁻¹) := by
  refine gaussBdd_of_norm_le ((absDiscr K) ^ ((|a| + |b|) / 2))
    (Real.rpow_nonneg (absDiscr_pos K).le _) ?_
  intro s hsa hsb _
  rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos (absDiscr_pos K),
    ← Real.rpow_neg (absDiscr_pos K).le]
  refine Real.rpow_le_rpow_of_exponent_le (one_le_absDiscr K) ?_
  rw [show (s / 2).re = s.re / 2 by simp]
  have hre : -s.re ≤ |a| + |b| := by linarith [neg_abs_le a, le_abs_self b, abs_nonneg b, abs_nonneg a]
  linarith

/-- `s ↦ Γ_ℝ(s)⁻¹` satisfies `GaussBdd a b`. -/
theorem gaussBdd_Gammaℝ_inv (a b : ℝ) : GaussBdd a b (fun s => (Gammaℝ s)⁻¹) := by
  obtain ⟨B, hB, hΓ⟩ := norm_inv_Gamma_le (a / 2) (b / 2)
  set P : ℝ := Real.pi ^ ((|a| + |b|) / 2) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg Real.pi_pos.le _
  refine gaussBdd_of_norm_le_exp (P * B) (Real.pi / 2) (by positivity) (by positivity) ?_
  intro s hsa hsb hsi
  have hs2 : (s / 2).re = s.re / 2 := by simp
  have hs2i : (s / 2).im = s.im / 2 := by simp
  have h1 : a / 2 ≤ (s / 2).re := by rw [hs2]; linarith
  have h2 : (s / 2).re ≤ b / 2 := by rw [hs2]; linarith
  have h3 : 1 ≤ |(s / 2).im| := by rw [hs2i, abs_div, abs_two]; linarith
  have hΓs := hΓ (s / 2) h1 h2 h3
  rw [hs2i, abs_div, abs_two] at hΓs
  rw [Gammaℝ_def, mul_inv, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_neg Real.pi_pos.le]
  have hexp : (-(-s / 2)).re ≤ (|a| + |b|) / 2 := by
    have : (-(-s / 2)).re = s.re / 2 := by simp [neg_div]
    rw [this]
    linarith [le_abs_self b, abs_nonneg a]
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpow : Real.pi ^ (-(-s / 2)).re ≤ P := Real.rpow_le_rpow_of_exponent_le hπ1 hexp
  calc Real.pi ^ (-(-s / 2)).re * ‖(Gamma (s / 2))⁻¹‖ ≤ P * (B * Real.exp (Real.pi * (|s.im| / 2))) :=
        mul_le_mul hpow hΓs (norm_nonneg _) hP0
    _ = P * B * Real.exp (Real.pi / 2 * |s.im|) := by ring_nf

/-- `s ↦ Γ_ℂ(s)⁻¹` satisfies `GaussBdd a b`. -/
theorem gaussBdd_Gammaℂ_inv (a b : ℝ) : GaussBdd a b (fun s => (Gammaℂ s)⁻¹) := by
  obtain ⟨B, hB, hΓ⟩ := norm_inv_Gamma_le a b
  set P : ℝ := (2 * Real.pi) ^ (|a| + |b|) with hP
  have h2π1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h2π0 : (0 : ℝ) < 2 * Real.pi := by linarith
  have hP0 : 0 ≤ P := Real.rpow_nonneg h2π0.le _
  refine gaussBdd_of_norm_le_exp (P * B) Real.pi (by positivity) Real.pi_pos.le ?_
  intro s hsa hsb hsi
  have hΓs := hΓ s hsa hsb (by linarith)
  have hcast : ((2 : ℂ) * (Real.pi : ℝ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, norm_inv, hcast,
    Complex.norm_cpow_eq_rpow_re_of_pos h2π0, ← Real.rpow_neg h2π0.le]
  have hexp : -(-s).re ≤ |a| + |b| := by
    have : -(-s).re = s.re := by simp
    rw [this]; linarith [le_abs_self b, abs_nonneg a]
  have hpow : (2 * Real.pi) ^ (-(-s).re) ≤ P := Real.rpow_le_rpow_of_exponent_le h2π1 hexp
  have h2 : ‖(2 : ℂ)‖⁻¹ ≤ 1 := by norm_num
  calc ‖(2 : ℂ)‖⁻¹ * (2 * Real.pi) ^ (-(-s).re) * ‖(Gamma s)⁻¹‖
      ≤ 1 * P * (B * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul (mul_le_mul h2 hpow (Real.rpow_nonneg h2π0.le _) zero_le_one) hΓs (norm_nonneg _)
          (by positivity)
    _ = P * B * Real.exp (Real.pi * |s.im|) := by ring

/-- `invGammaFactor K` satisfies `GaussBdd a b`. -/
theorem gaussBdd_invGammaFactor (a b : ℝ) : GaussBdd a b (invGammaFactor K) := by
  unfold invGammaFactor
  exact ((gaussBdd_D_inv K a b).mul ((gaussBdd_Gammaℝ_inv a b).pow _)).mul
    ((gaussBdd_Gammaℂ_inv a b).pow _)

/-- `s ↦ s⁻¹` satisfies `GaussBdd a b`. -/
theorem gaussBdd_inv (a b : ℝ) : GaussBdd a b (fun s : ℂ => s⁻¹) := by
  refine gaussBdd_of_norm_le 1 zero_le_one fun s _ _ hsi => ?_
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (by linarith [hsi.trans (abs_im_le_norm s)])

/-- A function with `log ‖ξ s‖ ≤ C ‖s‖ log ‖s‖` for `‖s‖ ≥ 2` satisfies `GaussBdd a b`. -/
theorem gaussBdd_of_order_one (a b : ℝ) (ξ : ℂ → ℂ) (C : ℝ)
    (hξ : ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) : GaussBdd a b ξ := by
  set M : ℝ := |a| + |b| with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨Real.exp (2 * |C| * M ^ 2), 2 * |C|, (Real.exp_pos _).le, by positivity, ?_⟩
  intro s hsa hsb hsi
  have hs2 : (2 : ℝ) ≤ ‖s‖ := hsi.trans (abs_im_le_norm s)
  have hs0 : 0 < ‖s‖ := by linarith
  have hlog := hξ s hs2
  have hlogs : Real.log ‖s‖ ≤ ‖s‖ := by linarith [Real.log_le_sub_one_of_pos hs0]
  have hlogs0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have h1 : C * ‖s‖ * Real.log ‖s‖ ≤ |C| * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log ‖s‖ ≤ |C| * ‖s‖ * Real.log ‖s‖ := by
          apply mul_le_mul_of_nonneg_right _ hlogs0
          exact mul_le_mul_of_nonneg_right (le_abs_self C) hs0.le
      _ ≤ |C| * ‖s‖ * ‖s‖ := mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = |C| * ‖s‖ ^ 2 := by ring
  have hns : ‖s‖ ≤ M + |s.im| := norm_le_of_strip s hsa hsb
  have h2 : ‖s‖ ^ 2 ≤ 2 * M ^ 2 + 2 * s.im ^ 2 := by
    have hsq : ‖s‖ ^ 2 ≤ (M + |s.im|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hns 2
    have := sq_abs s.im
    nlinarith [sq_nonneg (M - |s.im|)]
  by_cases hξ0 : ξ s = 0
  · rw [hξ0, norm_zero]; positivity
  · have hpos : 0 < ‖ξ s‖ := norm_pos_iff.mpr hξ0
    rw [← Real.exp_log hpos, ← Real.exp_add, Real.exp_le_exp]
    have h3 : |C| * ‖s‖ ^ 2 ≤ |C| * (2 * M ^ 2 + 2 * s.im ^ 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    nlinarith

end pieces

section main

variable (K : Type) [Field K] [NumberField K]

/-- The rectangle `[a, b] × [-2, 2]` in `ℂ` is compact. -/
theorem isCompact_rect (a b : ℝ) : IsCompact (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc a b).reProdIm (Metric.isBounded_Icc _ _))

/-- An entire extension `R` of `(s - 1) ζ_K(s)` satisfies `‖R s‖ ≤ B exp (C (Im s) ^ 2)` on the
strip `a ≤ Re s ≤ b`. -/
theorem main (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) := by
  obtain ⟨Λ, hΛd, -, hΛeq, ⟨ξ, hξd, hξeq, Cξ, hξgr⟩, -⟩ := NumberField.exists_completedDedekindZeta_package_core K

  have hRid := R_eq K R hR hRζ Λ hΛd hΛeq
  have hRξ : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
      R s = ξ s * s⁻¹ * invGammaFactor K s := by
    intro s _ _ hsi
    have him0 : s.im ≠ 0 := by intro h; rw [h] at hsi; norm_num at hsi
    have hs0 : s ≠ 0 := by intro h; apply him0; rw [h]; simp
    have hs1 : s ≠ 1 := by intro h; apply him0; rw [h]; simp
    have hmem : s ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hs0, hs1⟩
    have h := hRid hmem
    simp only at h
    rw [h, hξeq s hs0 hs1]
    field_simp

  have hG : GaussBdd a b (fun s => ξ s * s⁻¹ * invGammaFactor K s) :=
    ((gaussBdd_of_order_one a b ξ Cξ hξgr).mul (gaussBdd_inv a b)).mul (gaussBdd_invGammaFactor K a b)
  obtain ⟨B₁, C₁, hB₁, hC₁, hG₁⟩ := hG

  obtain ⟨B₀, hB₀⟩ := (isCompact_rect a b).exists_bound_of_continuousOn hR.continuous.continuousOn
  refine ⟨max B₀ B₁, C₁, fun s hsa hsb => ?_⟩
  have hexp1 : 1 ≤ Real.exp (C₁ * s.im ^ 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt 2 |s.im| with hbig | hsmall
  · rw [hRξ s hsa hsb hbig]
    calc ‖ξ s * s⁻¹ * invGammaFactor K s‖ ≤ B₁ * Real.exp (C₁ * s.im ^ 2) := hG₁ s hsa hsb hbig
      _ ≤ max B₀ B₁ * Real.exp (C₁ * s.im ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hmem : s ∈ (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) := by
      refine ⟨⟨hsa, hsb⟩, ?_⟩
      have := abs_lt.mp hsmall
      exact ⟨this.1.le, this.2.le⟩
    have h0 := hB₀ s hmem
    have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans h0
    exact (h0.trans (le_max_left _ _)).trans
      (le_mul_of_one_le_right (hB₀0.trans (le_max_left _ _)) hexp1)

end main

end R4Z2a

end

/-- An entire extension `R` of `(s - 1) ζ_K(s)` satisfies `‖R s‖ ≤ B exp (C (Im s) ^ 2)` on the
strip `a ≤ Re s ≤ b`. -/
theorem solution
    (K : Type) [Field K] [NumberField K] (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) :=
  R4Z2a.main K R hR hRζ a b

end S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq

end P2MW


section

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-- An entire extension `R` of `(s - 1) ζ_K(s)` satisfies `‖R s‖ ≤ B exp (C (Im s) ^ 2)` on every
vertical strip `a ≤ Re s ≤ b`. -/
theorem NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
    (K : Type) [Field K] [NumberField K] (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) := by
  p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq.solution

end


set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero

set_option autoImplicit false

open IsDedekindDomain NumberField

/-- There is an entire `E` with `s E(s) = Γℝ(s)⁻¹`, `E 1 ≠ 0` and `E (-2 (n + 1)) = 0`. -/
theorem exists_mul_eq_Gammaℝ_inv :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ (∀ s : ℂ, s * E s = (Complex.Gammaℝ s)⁻¹) ∧ E 1 ≠ 0 ∧
      ∀ n : ℕ, E (-2 * (n + 1)) = 0 := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨fun s => ((Real.pi : ℝ) : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2 + 1))⁻¹ / 2,
    ?_, ?_, ?_, ?_⟩
  · refine Differentiable.div_const (Differentiable.mul ?_ ?_) 2
    · exact (differentiable_id.div_const 2).const_cpow (Or.inl hπ)
    · exact Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const 2).add_const 1)
  · intro s
    simp only []
    rw [Complex.Gammaℝ_def, mul_inv, ← Complex.cpow_neg, neg_div, neg_neg,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s / 2)]
    ring
  · simp only []
    refine div_ne_zero (mul_ne_zero ?_ ?_) two_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
    · refine inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos ?_)
      simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
      norm_num
  · intro n
    simp only []
    have h : (-2 * ((n : ℂ) + 1)) / 2 + 1 = -(n : ℂ) := by ring
    rw [h, Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero, zero_div]

/-- A number field has at least one infinite place. -/
theorem one_le_nrRealPlaces_add_nrComplexPlaces (K : Type) [Field K] [NumberField K] :
    1 ≤ InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

/-- If `s * e = g` and `1 ≤ n`, then `s * (e * g ^ (n - 1) * b) = g ^ n * b`. -/
theorem mul_mul_pow_pred_mul {s e g b : ℂ} {n : ℕ} (hn : 1 ≤ n) (h : s * e = g) :
    s * (e * g ^ (n - 1) * b) = g ^ n * b := by
  rw [← mul_assoc, ← mul_assoc, h, ← pow_succ', Nat.sub_add_cancel hn]

/-- `(s - 1) ζ_K(s)` extends to an entire function `R` with `R 1 ≠ 0` and
`R (-2 (n + 1)) = 0` for every natural number `n`. -/
theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ R 1 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) ∧
      ∀ n : ℕ, R (-2 * (n + 1)) = 0 := by
  obtain ⟨Λ, -, -, hΛeq, ⟨ξ, hξd, hξeq, -⟩, hξne⟩ := NumberField.exists_completedDedekindZeta_package_core K
  have hξ1 : ξ 1 ≠ 0 := (hξne ξ hξd hξeq).2
  have hD : (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 :=
    Int.cast_ne_zero.mpr (abs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hDs : ∀ s : ℂ, (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := fun s =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl hD)
  obtain ⟨E, hEd, hEmul, hE1, hE0⟩ := exists_mul_eq_Gammaℝ_inv
  refine ⟨fun s => ξ s * ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹ *
      (E s * (Complex.Gammaℝ s)⁻¹ ^
        (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) *
        (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K), ?_, ?_, ?_, ?_⟩
  · refine (hξd.mul (Differentiable.inv ?_ hDs)).mul
      ((hEd.mul (Complex.differentiable_Gammaℝ_inv.pow _)).mul
        ((Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)).pow _))
    exact (differentiable_id.div_const 2).const_cpow (Or.inl hD)
  · simp only []
    refine mul_ne_zero (mul_ne_zero hξ1 (inv_ne_zero (hDs 1))) (mul_ne_zero (mul_ne_zero hE1 ?_) ?_)
    · exact pow_ne_zero _ (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simp)))
    · exact pow_ne_zero _ (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)))
  · intro s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs
    have hs1 : s ≠ 1 := by
      rintro rfl
      norm_num at hs
    have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hΓ1 : Complex.Gammaℝ (s + 1) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
    simp only []
    calc _ = (s - 1) * Λ s * ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹ *
        (s * (E s * (Complex.Gammaℝ s)⁻¹ ^
          (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) *
          (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K)) := by
          rw [hξeq s hs0 hs1]; ring
      _ = (s - 1) * dedekindZeta K s *
          ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2) * ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹) *
          (Complex.Gammaℝ s * (Complex.Gammaℝ s)⁻¹) ^
            (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K) *
          (Complex.Gammaℝ (s + 1) * (Complex.Gammaℝ (s + 1))⁻¹) ^ InfinitePlace.nrComplexPlaces K := by
          rw [mul_mul_pow_pred_mul (one_le_nrRealPlaces_add_nrComplexPlaces K) (hEmul s),
            hΛeq s hs, ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
          ring
      _ = _ := by
          rw [mul_inv_cancel₀ (hDs s), mul_inv_cancel₀ hΓ, mul_inv_cancel₀ hΓ1, one_pow, one_pow, mul_one,
            mul_one, mul_one]
  · intro n
    simp only [hE0 n, zero_mul, mul_zero]

end S_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero

end P2MW


section

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

/-- `(s - 1) ζ_K(s)` extends to an entire function `R` with `R 1 ≠ 0` and
`R (-2 (n + 1)) = 0` for every natural number `n`. -/
theorem NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
    (K : Type) [Field K] [NumberField K] :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ R 1 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) ∧
      ∀ n : ℕ, R (-2 * (n + 1)) = 0 := by
  p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero.solution

end


set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip

set_option autoImplicit false

open Complex Set Filter Topology

namespace R4PLpoly

/-- For `a ≤ Re z`, `(1 + |Im z|) / 2 ≤ ‖z + (1 - a)‖`. -/
theorem norm_shift_lower {a : ℝ} (z : ℂ) (hza : a ≤ z.re) :
    (1 + |z.im|) / 2 ≤ ‖z + ((1 - a : ℝ) : ℂ)‖ := by
  set w : ℂ := z + ((1 - a : ℝ) : ℂ) with hw
  have hre : 1 ≤ w.re := by simp only [hw, add_re, ofReal_re]; linarith
  have him : w.im = z.im := by simp [hw]
  have h1 : (1 : ℝ) ≤ ‖w‖ := le_trans hre (Complex.re_le_norm w)
  have h2 : |z.im| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
  linarith

/-- For `a ≤ Re z ≤ b`, `‖z + (1 - a)‖ ≤ (1 + (b - a)) (1 + |Im z|)`. -/
theorem norm_shift_upper {a b : ℝ} (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖z + ((1 - a : ℝ) : ℂ)‖ ≤ (1 + (b - a)) * (1 + |z.im|) := by
  set w : ℂ := z + ((1 - a : ℝ) : ℂ) with hw
  have hre : 1 ≤ w.re ∧ w.re ≤ 1 + (b - a) := by
    simp only [hw, add_re, ofReal_re]; constructor <;> linarith
  have him : w.im = z.im := by simp [hw]
  have hab : 0 ≤ b - a := by linarith
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ = w.re + |z.im| := by rw [him, abs_of_pos (by linarith)]
    _ ≤ (1 + (b - a)) + |z.im| := by linarith
    _ ≤ (1 + (b - a)) * (1 + |z.im|) := by nlinarith [abs_nonneg z.im]

/-- For `a - 1 < Re z`, `z + (1 - a) ≠ 0`. -/
theorem shift_ne_zero {a : ℝ} (z : ℂ) (hza : a - 1 < z.re) : z + ((1 - a : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, ofReal_re, zero_re] at this
  linarith

/-- For `a - 1 < Re z`, `z + (1 - a)` lies in the slit plane. -/
theorem shift_mem_slitPlane {a : ℝ} (z : ℂ) (hza : a - 1 < z.re) :
    z + ((1 - a : ℝ) : ℂ) ∈ slitPlane := by
  refine Or.inl ?_
  simp only [add_re, ofReal_re]
  linarith

/-- `z ↦ (z + (1 - a)) ^ (-α)` is differentiable on a neighbourhood of the closed strip
`a ≤ Re z ≤ b`. -/
theorem diffContOnCl_inv_shift_cpow {a b : ℝ} (hab : a < b) (α : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ => ((z + ((1 - a : ℝ) : ℂ)) ^ (α : ℂ))⁻¹)
      (Complex.re ⁻¹' Set.Ioo a b) := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => ((z + ((1 - a : ℝ) : ℂ)) ^ (α : ℂ))⁻¹)
      {w : ℂ | a - 1 < w.re} := by
    intro w hw
    have hw' : a - 1 < w.re := hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (z + ((1 - a : ℝ) : ℂ)) ^ (α : ℂ)) w :=
      DifferentiableAt.cpow (differentiableAt_id.add_const _) (differentiableAt_const _)
        (shift_mem_slitPlane w hw')
    have h2 : (w + ((1 - a : ℝ) : ℂ)) ^ (α : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (shift_ne_zero w hw')
    exact (h1.inv h2).differentiableWithinAt
  refine DifferentiableOn.diffContOnCl (hdiff.mono ?_)
  rw [closure_preimage_re, closure_Ioo hab.ne]
  intro w hw
  simp only [mem_preimage, mem_Icc] at hw
  change a - 1 < w.re
  linarith [hw.1]

/-- For `a ≤ Re w`, `0 ≤ M` and `x ≤ M (1 + |Im w|) ^ α`, `‖w + (1 - a)‖ ^ (-α) x ≤ 2 ^ α M`. -/
theorem inv_norm_shift_rpow_mul_le {a α M x : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M) (w : ℂ)
    (hwa : a ≤ w.re) (hx : x ≤ M * (1 + |w.im|) ^ α) :
    (‖w + ((1 - a : ℝ) : ℂ)‖ ^ α)⁻¹ * x ≤ (2 : ℝ) ^ α * M := by
  have hlow := norm_shift_lower w hwa
  set r := ‖w + ((1 - a : ℝ) : ℂ)‖ with hr
  have hpos1 : 0 < 1 + |w.im| := by positivity
  have hpos : 0 < r := lt_of_lt_of_le (by positivity) hlow
  have hpowpos : 0 < r ^ α := Real.rpow_pos_of_pos hpos α
  have hkey : (1 + |w.im|) ^ α ≤ (2 : ℝ) ^ α * r ^ α := by
    rw [← Real.mul_rpow (by norm_num) hpos.le]
    exact Real.rpow_le_rpow hpos1.le (by linarith) hα
  calc (r ^ α)⁻¹ * x ≤ (r ^ α)⁻¹ * (M * (1 + |w.im|) ^ α) :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hpowpos.le)
    _ ≤ (r ^ α)⁻¹ * (M * ((2 : ℝ) ^ α * r ^ α)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpowpos.le)
        exact mul_le_mul_of_nonneg_left hkey hM
    _ = (2 : ℝ) ^ α * M := by field_simp

/-- For `a ≤ Re z ≤ b`, `0 ≤ x` and `‖z + (1 - a)‖ ^ (-α) x ≤ 2 ^ α M`,
`x ≤ (2 (1 + (b - a))) ^ α M (1 + |Im z|) ^ α`. -/
theorem le_of_inv_norm_shift_rpow_mul_le {a b α M x : ℝ} (hα : 0 ≤ α) (z : ℂ) (hza : a ≤ z.re)
    (hzb : z.re ≤ b) (hx0 : 0 ≤ x) (hx : (‖z + ((1 - a : ℝ) : ℂ)‖ ^ α)⁻¹ * x ≤ (2 : ℝ) ^ α * M) :
    x ≤ (2 * (1 + (b - a))) ^ α * M * (1 + |z.im|) ^ α := by
  set r := ‖z + ((1 - a : ℝ) : ℂ)‖ with hr
  have hpos : 0 < r := norm_pos_iff.mpr (shift_ne_zero z (by linarith))
  have hpowpos : 0 < r ^ α := Real.rpow_pos_of_pos hpos α
  have hpow_up : r ^ α ≤ (1 + (b - a)) ^ α * (1 + |z.im|) ^ α := by
    rw [← Real.mul_rpow (by linarith) (by positivity)]
    exact Real.rpow_le_rpow hpos.le (norm_shift_upper z hza hzb) hα
  have h1ba : (0 : ℝ) ≤ (1 + (b - a)) ^ α := Real.rpow_nonneg (by linarith) α
  calc x = r ^ α * ((r ^ α)⁻¹ * x) := by rw [← mul_assoc, mul_inv_cancel₀ hpowpos.ne', one_mul]
    _ ≤ ((1 + (b - a)) ^ α * (1 + |z.im|) ^ α) * ((2 : ℝ) ^ α * M) :=
        mul_le_mul hpow_up hx (mul_nonneg (inv_nonneg.mpr hpowpos.le) hx0)
          (mul_nonneg h1ba (Real.rpow_nonneg (by positivity) α))
    _ = (2 * (1 + (b - a))) ^ α * M * (1 + |z.im|) ^ α := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
        ring

/-- Phragmén–Lindelöf in the strip `a ≤ Re z ≤ b`: a function of growth at most
`exp (B exp (c |Im z|))` with `c < π / (b - a)`, bounded by `M (1 + |Im z|) ^ α` on both edges,
is bounded by `C M (1 + |Im z|) ^ α` on the closed strip, with `C` depending only on `a, b, α`. -/
theorem main (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α := by
  refine ⟨(2 * (1 + (b - a))) ^ α, Real.rpow_pos_of_pos (by linarith) α, ?_⟩
  intro f M hM hfd hgrowth hle_a hle_b z hza hzb
  set c₀ : ℂ := ((1 - a : ℝ) : ℂ) with hc₀
  set g : ℂ → ℂ := fun z => ((z + c₀) ^ (α : ℂ))⁻¹ with hg
  set F : ℂ → ℂ := fun z => g z * f z with hF
  have hnorm_pow : ∀ w : ℂ, ‖(w + c₀) ^ (α : ℂ)‖ = ‖w + c₀‖ ^ α := fun w => norm_cpow_real _ _
  have hg_norm : ∀ w : ℂ, ‖g w‖ = (‖w + c₀‖ ^ α)⁻¹ := fun w => by
    simp only [hg, norm_inv, hnorm_pow]
  have hg_dc : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) := diffContOnCl_inv_shift_cpow hab α
  have hF_dc : DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b) := hg_dc.smul hfd
  have hg_le_one : ∀ w : ℂ, a ≤ w.re → ‖g w‖ ≤ 1 := by
    intro w hwa
    have hre : 1 ≤ (w + c₀).re := by
      simp only [hc₀, add_re, ofReal_re]
      linarith
    rw [hg_norm]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow (hre.trans (Complex.re_le_norm _)) hα)
  have hbdry : ∀ w : ℂ, a ≤ w.re → ‖f w‖ ≤ M * (1 + |w.im|) ^ α → ‖F w‖ ≤ (2 : ℝ) ^ α * M := by
    intro w hwa hfw
    rw [hF, norm_mul, hg_norm]
    exact inv_norm_shift_rpow_mul_le hα hM w hwa hfw
  have hFa : ∀ w : ℂ, w.re = a → ‖F w‖ ≤ (2 : ℝ) ^ α * M :=
    fun w hw => hbdry w hw.symm.le (hle_a w hw)
  have hFb : ∀ w : ℂ, w.re = b → ‖F w‖ ≤ (2 : ℝ) ^ α * M :=
    fun w hw => hbdry w (by rw [hw]; exact hab.le) (hle_b w hw)
  have hFgrowth : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      F =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    obtain ⟨c, hc, B, hB⟩ := hgrowth
    refine ⟨c, hc, B, Asymptotics.IsBigO.of_bound 1 ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    simp only [mem_preimage, mem_Ioo] at hw
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hF, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hg_le_one w hw.1.le)).trans (hB w hw.1 hw.2)
  have hPL : ‖F z‖ ≤ (2 : ℝ) ^ α * M :=
    PhragmenLindelof.vertical_strip hF_dc hFgrowth hFa hFb hza hzb
  rw [hF, norm_mul, hg_norm] at hPL
  exact le_of_inv_norm_shift_rpow_mul_le hα z hza hzb (norm_nonneg _) hPL

end R4PLpoly

/-- Phragmén–Lindelöf in the strip `a ≤ Re z ≤ b`: a function of growth at most
`exp (B exp (c |Im z|))` with `c < π / (b - a)`, bounded by `M (1 + |Im z|) ^ α` on both edges,
is bounded by `C M (1 + |Im z|) ^ α` on the closed strip, with `C` depending only on `a, b, α`. -/
theorem solution
    (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α :=
  R4PLpoly.main a b α hab hα

end S_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip

end P2MW


section

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-- Phragmén–Lindelöf in the strip `a ≤ Re z ≤ b`: a function of growth at most
`exp (B exp (c |Im z|))` with `c < π / (b - a)`, bounded by `M (1 + |Im z|) ^ α` on both edges,
is bounded by `C M (1 + |Im z|) ^ α` on the closed strip, with `C` depending only on `a, b, α`. -/
theorem PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
    (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α := by
  p2m_exact_reverting @_root_.P2MW.S_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip.solution

end


set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta

set_option autoImplicit false

noncomputable section

open NumberField Filter Complex IsDedekindDomain
open scoped Topology Classical

namespace Ws41

namespace EulerZeta

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The number of ideals of `𝓞 K` of absolute norm `n`. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- `ζ_K` is the L-series of `idealCount K`. -/
theorem dedekindZeta_eq_LSeries (z : ℂ) :
    dedekindZeta K z = LSeries (fun n => (idealCount K n : ℂ)) z := rfl

/-- There are finitely many ideals of `𝓞 K` of a given absolute norm. -/
scoped instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- Exactly one ideal, the zero ideal, has absolute norm `0`. -/
theorem idealCount_zero : idealCount K 0 = 1 := by
  rw [idealCount]
  have : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_eq_zero_iff.mpr rfl⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp I.2) }
  exact Nat.card_unique

/-- `(∑_{k = 1}^n idealCount K k) / n` tends to the residue of `ζ_K` at `1`. -/
theorem tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue]
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = idealCount K 0 from (idealCount_zero K).symm,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le)]
  simp only [idealCount]
  rw [← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- `∑_{k = 1}^n idealCount K k = O(n)`. -/
theorem isBigO_sum_idealCount :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  have h1 : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop] fun n => (n : ℝ) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ (tendsto_sum_idealCount_div K)
    filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (Nat.cast_ne_zero.mpr hn)
  exact h1.congr_right fun n => (Real.rpow_one _).symm

/-- The L-series of `idealCount K` converges for `Re z > 1`. -/
theorem LSeriesSummable_idealCount {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) z := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    (isBigO_sum_idealCount K) (fun n => Nat.cast_nonneg _) zero_le_one hz
  simpa only [Complex.ofReal_natCast] using h

/-- The sum of a constant `c` over the ideals of absolute norm `n` is `idealCount K n • c`. -/
theorem tsum_fiber_const {M : Type} [AddCommMonoid M] [TopologicalSpace M] [T2Space M] (n : ℕ) (c : M) :
    ∑' _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, c = idealCount K n • c := by
  have : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, idealCount, Nat.card_eq_fintype_card]

/-- `∑_I N(I) ^ (-σ)` over the ideals of `𝓞 K` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  rw [← e.summable_iff]
  have hnn : ∀ p, 0 ≤ ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) p := fun p =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) ⟨n, c⟩ = (n : ℝ) ^ (-σ) := fun n c => by
    simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun n => ?_, ?_⟩
  · exact Summable.of_finite
  · simp_rw [hfib, tsum_fiber_const, nsmul_eq_mul]
    have hL : Summable fun n => ‖LSeries.term (fun n => (idealCount K n : ℂ)) σ n‖ :=
      summable_norm_iff.mpr (LSeriesSummable_idealCount K (z := σ) (by simpa using hσ))
    refine hL.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (by linarith : σ ≠ 0)), mul_zero]
    · rw [Complex.norm_natCast, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- `∑_I ‖N(I) ^ (-z)‖` over the ideals of `𝓞 K` converges for `Re z > 1`. -/
theorem summable_norm_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)‖ := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  refine (summable_absNorm_rpow K hz).congr fun I => ?_
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow hz0, norm_zero,
      Real.zero_rpow (neg_ne_zero.mpr (by linarith : z.re ≠ 0))]
  · rw [Complex.norm_natCast_cpow_of_pos h, Complex.neg_re]

/-- `∑_I N(I) ^ (-z)` over the ideals of `𝓞 K` converges for `Re z > 1`. -/
theorem summable_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) :=
  (summable_norm_absNorm_cpow K hz).of_norm

/-- For `Re z > 1`, `∑_I N(I) ^ (-z) = ζ_K(z)`, the sum running over the ideals of `𝓞 K`. -/
theorem tsum_absNorm_cpow_eq_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
    ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) = dedekindZeta K z := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  have hs : Summable ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) :=
    e.summable_iff.mpr (summable_absNorm_cpow K hz)
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) ⟨n, c⟩ = (n : ℂ) ^ (-z) :=
    fun n c => by simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  rw [← e.tsum_eq, show (fun c => (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) (e c))
      = (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e from rfl, hs.tsum_sigma,
    dedekindZeta_eq_LSeries, LSeries]
  refine tsum_congr fun n => ?_
  simp_rw [hfib]
  rw [tsum_fiber_const, nsmul_eq_mul, LSeries.term_def]
  split_ifs with h0
  · rw [h0, Nat.cast_zero, Complex.zero_cpow hz0, mul_zero]
  · rw [Complex.cpow_neg, div_eq_mul_inv]

/-- The prime ideals of `𝓞 K`, as a subtype. -/
abbrev Primes : Type u := {Q : Ideal (𝓞 K) // Prime Q}

/-- The nonzero ideals of `𝓞 K` all of whose prime divisors lie in `T`. -/
def primeSet (T : Finset (Primes K)) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ 0 ∧ ∀ Q : Primes K, Q.1 ∣ I → Q ∈ T}

/-- The only nonzero ideal with no prime divisor is `⊤`. -/
theorem primeSet_empty : primeSet K ∅ = {⊤} := by
  ext I
  simp only [primeSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hI0, hprime⟩
    by_contra hne
    have hnu : ¬IsUnit I := fun h => hne (Ideal.isUnit_iff.mp h)
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_factors hI0 hnu
    exact absurd (hprime ⟨P, UniqueFactorizationMonoid.prime_of_factor P hP⟩
      (UniqueFactorizationMonoid.dvd_of_mem_factors hP)) (Finset.notMem_empty _)
  · rintro rfl
    refine ⟨?_, fun Q hdvd => ?_⟩
    · intro h
      rw [← Ideal.one_eq_top] at h
      exact one_ne_zero h
    · exact absurd (Ideal.isUnit_iff.mpr (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))) Q.2.not_isUnit

/-- A prime ideal of `𝓞 K` has absolute norm at least `2`. -/
theorem two_le_absNorm (Q : Primes K) : 2 ≤ Ideal.absNorm Q.1 := by
  have h0 : Ideal.absNorm Q.1 ≠ 0 := fun h =>
    Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm Q.1 ≠ 1 := fun h =>
    Q.2.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

/-- For `Re s > 0` and a prime ideal `Q`, `‖N(Q) ^ (-s)‖ < 1`. -/
theorem norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    ‖((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have h2 := two_le_absNorm K Q
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h1 : (1 : ℝ) < (Ideal.absNorm Q.1 : ℕ) := by exact_mod_cast h2
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

/-- `(m ^ k) ^ v = (m ^ v) ^ k` for natural numbers `m, k` and complex `v`. -/
theorem cpow_pow_natCast (m k : ℕ) (v : ℂ) :
    ((m ^ k : ℕ) : ℂ) ^ v = (((m : ℕ) : ℂ) ^ v) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- Multiplying an ideal of `primeSet K T` by a power of `P` lands in `primeSet K (insert P T)`. -/
theorem pow_mul_mem_primeSet_insert (P : Primes K) {T : Finset (Primes K)} (k : ℕ)
    {c : Ideal (𝓞 K)} (hc : c ∈ primeSet K T) : P.1 ^ k * c ∈ primeSet K (insert P T) := by
  obtain ⟨hc0, hcmem⟩ := hc
  refine ⟨mul_ne_zero (pow_ne_zero k P.2.ne_zero) hc0, fun Q hdvd => ?_⟩
  rcases (Prime.dvd_mul Q.2).mp hdvd with hQP | hQc
  · obtain rfl : Q = P := Subtype.ext
      (associated_iff_eq.mp (Prime.associated_of_dvd Q.2 P.2 (Q.2.dvd_of_dvd_pow hQP)))
    exact Finset.mem_insert_self Q T
  · exact Finset.mem_insert_of_mem (hcmem Q hQc)

/-- For `P ∉ T`, `c ∈ primeSet K T` and `k ≤ k'`, `P ^ k * c = P ^ k' * c'` forces `k = k'` and
`c = c'`. -/
theorem eq_of_pow_mul_eq_pow_mul {P : Primes K} {T : Finset (Primes K)} (hPT : P ∉ T)
    {k k' : ℕ} {c c' : Ideal (𝓞 K)} (hc : c ∈ primeSet K T) (hkk : k ≤ k')
    (h : P.1 ^ k * c = P.1 ^ k' * c') : k = k' ∧ c = c' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
  rw [pow_add, mul_assoc] at h
  have hcc : c = P.1 ^ d * c' := mul_left_cancel₀ (pow_ne_zero k P.2.ne_zero) h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero, one_mul] at hcc
    exact ⟨by simp, hcc⟩
  · exact absurd (hc.2 P (hcc ▸ dvd_mul_of_dvd_left (dvd_pow_self P.1 hd.ne') c')) hPT

/-- For `P ∉ T`, `(k, c) ↦ P ^ k * c` is a bijection
`ℕ × primeSet K T → primeSet K (insert P T)`. -/
theorem bijective_pow_mul_primeSet_insert {P : Primes K} {T : Finset (Primes K)} (hPT : P ∉ T) :
    Function.Bijective fun kc : ℕ × primeSet K T =>
      (⟨P.1 ^ kc.1 * kc.2.1, pow_mul_mem_primeSet_insert K P kc.1 kc.2.2⟩ :
        primeSet K (insert P T)) := by
  constructor
  · rintro ⟨k, c⟩ ⟨k', c'⟩ hab
    have hval : P.1 ^ k * c.1 = P.1 ^ k' * c'.1 := congrArg Subtype.val hab
    rcases le_total k k' with hkk | hkk
    · obtain ⟨h1, h2⟩ := eq_of_pow_mul_eq_pow_mul K hPT c.2 hkk hval
      exact Prod.ext h1 (Subtype.ext h2)
    · obtain ⟨h1, h2⟩ := eq_of_pow_mul_eq_pow_mul K hPT c'.2 hkk hval.symm
      exact Prod.ext h1.symm (Subtype.ext h2.symm)
  · rintro ⟨J, hJ0, hJmem⟩
    have hfin : FiniteMultiplicity P.1 J := FiniteMultiplicity.of_not_isUnit P.2.not_isUnit hJ0
    obtain ⟨c, hc, hPc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact hJ0 hc
    have hcmem : c ∈ primeSet K T := by
      refine ⟨hc0, fun Q hQc => ?_⟩
      rcases Finset.mem_insert.mp (hJmem Q (hc ▸ dvd_mul_of_dvd_right hQc _)) with rfl | hQT
      · exact absurd hQc hPc
      · exact hQT
    exact ⟨⟨multiplicity P.1 J, ⟨c, hcmem⟩⟩, Subtype.ext hc.symm⟩

/-- For `Re s > 1` and `P ∉ T`, adjoining `P` to `T` multiplies `∑_{I ∈ primeSet K T} N(I) ^ (-s)`
by the Euler factor `(1 - N(P) ^ (-s))⁻¹`. -/
theorem tsum_primeSet_insert {s : ℂ} (hs : 1 < s.re) (P : Primes K)
    {T : Finset (Primes K)} (hPT : P ∉ T) :
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  let e := Equiv.ofBijective _ (bijective_pow_mul_primeSet_insert K hPT)
  have hgeo : Summable (fun k : ℕ => ‖(((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k‖) :=
    (summable_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)).norm
  have hsub : Summable (fun J : primeSet K T => ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖) :=
    (summable_norm_absNorm_cpow K hs).subtype _
  calc
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
        = ∑' kc : ℕ × primeSet K T,
            ((Ideal.absNorm (e kc).1 : ℕ) : ℂ) ^ (-s) :=
      (e.tsum_eq
        (fun I : primeSet K (insert P T) => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))).symm
    _ = ∑' kc : ℕ × primeSet K T,
          ((((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ kc.1
            * ((Ideal.absNorm kc.2.1 : ℕ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun kc => ?_
      have hval : (e kc).1 = P.1 ^ kc.1 * kc.2.1 := rfl
      rw [hval, map_mul, map_pow, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, cpow_pow_natCast]
    _ = (∑' k : ℕ, (((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k)
          * ∑' J : primeSet K T, ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) :=
      (tsum_mul_tsum_of_summable_norm hgeo hsub).symm
    _ = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
      rw [tsum_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)]

/-- For `Re s > 1`, `∑_{I ∈ primeSet K T} N(I) ^ (-s) = ∏_{P ∈ T} (1 - N(P) ^ (-s))⁻¹`. -/
theorem tsum_primeSet_eq_prod {s : ℂ} (hs : 1 < s.re) (T : Finset (Primes K)) :
    ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
    rw [primeSet_empty,
      tsum_singleton ⊤ (fun J : Ideal (𝓞 K) => ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)),
      Finset.prod_empty, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow]
  | insert P T hPT ih =>
    rw [tsum_primeSet_insert K hs P hPT, Finset.prod_insert hPT, ih]

/-- A nonzero ideal whose prime factors all lie in `T` belongs to `primeSet K T`. -/
theorem mem_primeSet_of_factors {I : Ideal (𝓞 K)} (hI : I ≠ 0) {T : Finset (Primes K)}
    (hT : ∀ Q : Primes K, Q.1 ∈ UniqueFactorizationMonoid.factors I → Q ∈ T) :
    I ∈ primeSet K T := by
  refine ⟨hI, fun Q hdvd => ?_⟩
  obtain ⟨R, hR, hQR⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI Q.2.irreducible hdvd
  exact hT Q (associated_iff_eq.mp hQR ▸ hR)

/-- For an absolutely summable `f` with `f 0 = 0`, the sums of `f` over `primeSet K T` tend to
`∑' I, f I` as `T` runs through the finite sets of primes. -/
theorem tendsto_tsum_primeSet_of_summable {f : Ideal (𝓞 K) → ℂ}
    (hf : Summable fun I => ‖f I‖) (hf0 : f 0 = 0) :
    Tendsto (fun T : Finset (Primes K) => ∑' I : primeSet K T, f I) atTop (𝓝 (∑' I, f I)) := by
  have hfs : Summable f := hf.of_norm
  have htail : Tendsto (fun F : Finset (Ideal (𝓞 K)) =>
      ∑' I, ((↑F : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I) atTop (𝓝 0) := by
    refine (tendsto_tsum_compl_atTop_zero (fun I => ‖f I‖)).congr fun F => ?_
    exact tsum_subtype ((↑F : Set (Ideal (𝓞 K)))ᶜ) (fun I => ‖f I‖)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F₀, hF₀⟩ := Metric.tendsto_atTop.mp htail ε hε
  refine ⟨F₀.biUnion (fun I =>
      ((UniqueFactorizationMonoid.factors I).toFinset).subtype Prime), fun T hT => ?_⟩
  have hin : ∀ I ∈ F₀, I ≠ 0 → I ∈ primeSet K T := by
    intro I hI hI0
    refine mem_primeSet_of_factors K hI0 fun Q hQ => hT ?_
    exact Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_subtype.mpr (Multiset.mem_toFinset.mpr hQ)⟩
  have hdom : ∀ I : Ideal (𝓞 K), ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I
      ≤ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I := by
    intro I
    by_cases hI0 : I = 0
    · have hfI : ‖f I‖ = 0 := by rw [hI0, hf0, norm_zero]
      calc ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I
          ≤ ‖f I‖ := Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => norm_nonneg _)
        _ = 0 := hfI
        _ ≤ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
          Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    · by_cases hmem : I ∈ primeSet K T
      · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
        exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
      · have hIF : I ∈ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ) :=
          Set.mem_compl fun h => hmem (hin I (Finset.mem_coe.mp h) hI0)
        rw [Set.indicator_of_mem (Set.mem_compl hmem), Set.indicator_of_mem hIF]
  have hbound := hF₀ F₀ le_rfl
  rw [Real.dist_0_eq_abs, abs_of_nonneg (tsum_nonneg fun I =>
    Set.indicator_nonneg (fun _ _ => norm_nonneg _) I)] at hbound
  have hsplit := hfs.tsum_subtype_add_tsum_subtype_compl (primeSet K T)
  rw [dist_eq_norm, show (∑' I : primeSet K T, f I) - ∑' I, f I = -∑' I : ↥(primeSet K T)ᶜ, f I by
    rw [← hsplit]; ring, norm_neg]
  calc ‖∑' I : ↥(primeSet K T)ᶜ, f I‖
      ≤ ∑' I : ↥(primeSet K T)ᶜ, ‖f I‖ := norm_tsum_le_tsum_norm (hf.subtype _)
    _ = ∑' I, ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I :=
      tsum_subtype ((primeSet K T)ᶜ) (fun I => ‖f I‖)
    _ ≤ ∑' I, ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
      Summable.tsum_le_tsum hdom (hf.indicator _) (hf.indicator _)
    _ < ε := hbound

/-- The Euler product `∏_P (1 - N(P) ^ (-s))⁻¹` over the prime ideals of `𝓞 K` converges to
`ζ_K(s)` for `Re s > 1`. -/
theorem hasProd_primes {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : Primes K => (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) := by
  have hsz : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  have h := tendsto_tsum_primeSet_of_summable K
    (f := fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s))
    (summable_norm_absNorm_cpow K hs)
    (by show ((Ideal.absNorm (0 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0
        rw [map_zero, Nat.cast_zero, Complex.zero_cpow hsz])
  rw [tsum_absNorm_cpow_eq_dedekindZeta K hs] at h
  show Tendsto _ atTop _
  exact h.congr fun T => tsum_primeSet_eq_prod K hs T

/-- The height-one spectrum of `𝓞 K` is equivalent to its set of prime ideals. -/
def primesEquiv : HeightOneSpectrum (𝓞 K) ≃ Primes K where
  toFun v := ⟨v.asIdeal, v.prime⟩
  invFun Q := ⟨Q.1, Ideal.isPrime_of_prime Q.2, fun h => Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact h)⟩
  left_inv v := rfl
  right_inv Q := rfl

end Ws41.EulerZeta

p2m_reactivate "P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.Ws41 P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.Ws41.EulerZeta"
p2m_reactivate "P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.Ws41"

end

p2m_reactivate "P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.Ws41 P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.Ws41.EulerZeta"

open IsDedekindDomain NumberField in
/-- The Euler product of `ζ_K(s)` over the height-one spectrum of `𝓞 K`, for `Re s > 1`. -/
theorem solution (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) :=
  (Ws41.EulerZeta.primesEquiv K).hasProd_iff.mpr (Ws41.EulerZeta.hasProd_primes K hs)

end S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta

end P2MW


section

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

/-- The Euler product of `ζ_K(s)` over the height-one spectrum of `𝓞 K`, for `Re s > 1`. -/
theorem NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  p2m_exact_reverting @_root_.P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.solution

end


set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt

set_option autoImplicit false

open NumberField IsDedekindDomain

/-- At most `[F : ℚ]` places of `𝓞 F` in `T` lie over the same rational prime. -/
theorem card_filter_eq_le_finrank (F : Type) [Field F] [NumberField F]
    {p : HeightOneSpectrum (𝓞 F) → ℕ} (hp : ∀ v, (p v).Prime)
    (hmem : ∀ v, ((p v : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (v₀ : HeightOneSpectrum (𝓞 F)) :
    (T.filter fun v => p v = p v₀).card ≤ Module.finrank ℚ F := by
  have hqZ : Prime ((p v₀ : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (hp v₀)
  have hq0 : Ideal.span {((p v₀ : ℕ) : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hqZ.ne_zero
  have hqmax : (Ideal.span {((p v₀ : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hqZ.ne_zero).mpr hqZ).isMaximal hq0
  refine (Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal ?_ ?_).trans
    (RiemannJensen.card_primesOverFinset_le_finrank F hq0)
  · intro v hv
    have hv' : (p v : ℕ) = p v₀ := (Finset.mem_filter.mp hv).2
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
    refine ⟨v.isPrime, ⟨?_⟩⟩
    refine hqmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hv']
    exact hmem v
  · intro v₁ _ v₂ _ h
    exact HeightOneSpectrum.ext h

/-- `∑_v N(v) ^ (-σ)` over the height-one spectrum of `𝓞 F` converges for `σ > 1`. -/
theorem solution
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p n : ℕ, 0 < n ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal ∧
      p.Prime ∧ Ideal.absNorm v.asIdeal = p ^ n := fun v => by
    have : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    exact Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  choose p n hn hmem hp hN using hex
  have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) ≤ ((p v : ℕ) : ℝ) ^ (-σ) := by
    intro v
    refine Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (hp v).pos) ?_ (by linarith)
    rw [hN v]
    exact_mod_cast Nat.le_self_pow (hn v).ne' (p v)
  have hnat : Summable fun m : ℕ => (m : ℝ) ^ (-σ) := Real.summable_nat_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := (Module.finrank ℚ F : ℝ) * ∑' m : ℕ, (m : ℝ) ^ (-σ))
    (fun v => by positivity) (fun T => ?_)
  calc ∑ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)
      ≤ ∑ v ∈ T, ((p v : ℕ) : ℝ) ^ (-σ) := Finset.sum_le_sum fun v _ => hterm v
    _ = ∑ q ∈ T.image p, ∑ v ∈ T.filter (fun v => p v = q), ((p v : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem p hv) _).symm
    _ ≤ ∑ q ∈ T.image p, (Module.finrank ℚ F : ℝ) * (q : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨v₀, -, rfl⟩ := Finset.mem_image.mp hq
        calc ∑ v ∈ T.filter (fun v => p v = p v₀), ((p v : ℕ) : ℝ) ^ (-σ)
            = ∑ v ∈ T.filter (fun v => p v = p v₀), ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [(Finset.mem_filter.mp hv).2]
          _ = ((T.filter fun v => p v = p v₀).card : ℝ) * ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Module.finrank ℚ F : ℝ) * ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              gcongr
              exact card_filter_eq_le_finrank F hp hmem T v₀
    _ = (Module.finrank ℚ F : ℝ) * ∑ q ∈ T.image p, (q : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑' m : ℕ, (m : ℝ) ^ (-σ) := by
        gcongr
        exact hnat.sum_le_tsum _ (fun m _ => by positivity)

end S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt

end P2MW


section

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

/-- `∑_v N(v) ^ (-σ)` over the height-one spectrum of `𝓞 F` converges for `σ > 1`. -/
theorem NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  p2m_exact_reverting @_root_.P2MW.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.solution

end


set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp

set_option autoImplicit false

open Complex

namespace R4EulerDom

/-- If `∑ ‖a i‖` converges and every `‖a i‖ < 1`, then
`‖∏' i, (1 - a i)⁻¹‖ = exp (∑' i, Re (-log (1 - a i)))`. -/
theorem norm_tprod_inv_one_sub_eq_exp {ι : Type*} (a : ι → ℂ) (ha : Summable fun i => ‖a i‖)
    (ha1 : ∀ i, ‖a i‖ < 1) :
    ‖∏' i, (1 - a i)⁻¹‖ = Real.exp (∑' i, (-log (1 - a i)).re) := by
  have hne : ∀ i, 1 - a i ≠ 0 := fun i h => (ha1 i).ne (by rw [← sub_eq_zero.mp h, norm_one])
  have hsum : Summable fun i => -log (1 - a i) := ha.of_norm.clog_one_sub.neg
  have H := hsum.hasSum.cexp.tprod_eq
  have hcongr : (cexp ∘ fun i => -log (1 - a i)) = fun i => (1 - a i)⁻¹ := by
    funext i
    simp only [Function.comp_apply, exp_neg, exp_log (hne i)]
  rw [hcongr] at H
  rw [H, norm_exp, re_tsum hsum]

/-- For `‖a‖ ≤ 1 / 2`, `‖-log (1 - a)‖ ≤ 2 ‖a‖`. -/
theorem norm_neg_log_one_sub_le {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) : ‖-log (1 - a)‖ ≤ 2 * ‖a‖ := by
  rw [norm_neg, sub_eq_add_neg]
  have h := Complex.norm_log_one_add_half_le_self (z := -a) (by rwa [norm_neg])
  rw [norm_neg] at h
  linarith [norm_nonneg a]

/-- For a positive natural number `n`, `‖n ^ (-s)‖ = n ^ (-Re s)`. -/
theorem norm_natCast_cpow_neg (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [norm_natCast_cpow_of_pos hn]; simp

/-- For `N i ≥ 2`, `‖c i‖ ≤ 1`, `Re s ≥ 1` and `∑ N i ^ (-Re s)` convergent,
`‖∏' i, (1 - c i N i ^ (-s))⁻¹‖ ≤ exp (2 ∑' i, N i ^ (-Re s))`. -/
theorem main {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) := by
  have hN0 : ∀ i, 0 < N i := fun i => by have := hN i; omega
  set a : ι → ℂ := fun i => c i * ((N i : ℕ) : ℂ) ^ (-s) with ha_def
  have ha_le : ∀ i, ‖a i‖ ≤ ((N i : ℕ) : ℝ) ^ (-s.re) := fun i => by
    show ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, norm_natCast_cpow_neg _ (hN0 i)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hc i)
  have hpow_half : ∀ i, ((N i : ℕ) : ℝ) ^ (-s.re) ≤ 1 / 2 := fun i => by
    have h2 : (2 : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hN i
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    have h1 : (2 : ℝ) ≤ ((N i : ℕ) : ℝ) ^ s.re := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ s.re := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
        _ ≤ ((N i : ℕ) : ℝ) ^ s.re := Real.rpow_le_rpow (by norm_num) h2 (by linarith)
    rw [one_div]
    exact inv_anti₀ (by norm_num) h1
  have ha_half : ∀ i, ‖a i‖ ≤ 1 / 2 := fun i => (ha_le i).trans (hpow_half i)
  have ha_lt : ∀ i, ‖a i‖ < 1 := fun i => (ha_half i).trans_lt (by norm_num)
  have ha_sum : Summable fun i => ‖a i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) ha_le hsum
  rw [show (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) = fun i => (1 - a i)⁻¹ from rfl,
    norm_tprod_inv_one_sub_eq_exp a ha_sum ha_lt, Real.exp_le_exp]

  have hlog_le : ∀ i, ‖-log (1 - a i)‖ ≤ 2 * ((N i : ℕ) : ℝ) ^ (-s.re) := fun i =>
    (norm_neg_log_one_sub_le (ha_half i)).trans (by linarith [ha_le i])
  have hlog_sum : Summable fun i => ‖-log (1 - a i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hlog_le (hsum.mul_left 2)
  have hre_sum : Summable fun i => (-log (1 - a i)).re :=
    (hlog_sum.of_norm).mapL Complex.reCLM
  calc ∑' i, (-log (1 - a i)).re ≤ ∑' i, ‖-log (1 - a i)‖ :=
        Summable.tsum_le_tsum (fun i => (re_le_norm _)) hre_sum hlog_sum
    _ ≤ ∑' i, 2 * ((N i : ℕ) : ℝ) ^ (-s.re) :=
        Summable.tsum_le_tsum hlog_le hlog_sum (hsum.mul_left 2)
    _ = 2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re) := tsum_mul_left

end R4EulerDom

/-- For `N i ≥ 2`, `‖c i‖ ≤ 1`, `Re s ≥ 1` and `∑ N i ^ (-Re s)` convergent,
`‖∏' i, (1 - c i N i ^ (-s))⁻¹‖ ≤ exp (2 ∑' i, N i ^ (-Re s))`. -/
theorem solution
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) :=
  R4EulerDom.main N hN c hc s hs hsum

end S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp

end P2MW


section

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-- For `N i ≥ 2`, `‖c i‖ ≤ 1`, `Re s ≥ 1` and `∑ N i ^ (-Re s)` convergent,
`‖∏' i, (1 - c i N i ^ (-s))⁻¹‖ ≤ exp (2 ∑' i, N i ^ (-Re s))`. -/
theorem EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) := by
  p2m_exact_reverting @_root_.P2MW.S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp.solution

end


/-! ## Dedekind-zeta bounds with the exact exponent `N = [K : ℚ]` -/

namespace AntRHScratch

open NumberField IsDedekindDomain Complex Filter Set
open scoped Topology ComplexConjugate
open P2MW.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq.R4Z2a
  (absDiscr absDiscr_pos intCast_abs_discr_eq_ofReal_absDiscr invGammaFactor
    differentiable_invGammaFactor isOpen_compl01 isPreconnected_compl01
    dedekindZeta_eq_mul_invGammaFactor)

section Gamma

/-- On the line `Re s = -1/2`, `1 - s = conj (s + 2)`. -/
theorem one_sub_eq_conj (s : ℂ) (hs : s.re = -1 / 2) : 1 - s = conj (s + 2) := by
  apply Complex.ext
  · simp [hs]; norm_num
  · simp

/-- On the line `Re s = -1/2`, `s ≠ 0`. -/
theorem ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : s ≠ 0 := fun h => by
  norm_num [h] at hs

/-- On the line `Re s = -1/2`, `s + 1 ≠ 0`. -/
theorem add_one_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : s + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [hs] at this

/-- On the line `Re s = -1/2`, `s ≠ 1`. -/
theorem ne_one_of_re (s : ℂ) (hs : s.re = -1 / 2) : s ≠ 1 := fun h => by
  norm_num [h] at hs

/-- On the line `Re s = -1/2`, `Γ_ℝ(s) ≠ 0`. -/
theorem Gammaℝ_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h
  have := congrArg Complex.re h
  simp [hs] at this
  have h3 : (4 : ℝ) * n = 1 := by linarith
  have h4 : (4 * n : ℕ) = 1 := by exact_mod_cast h3
  omega

/-- On the line `Re s = -1/2`, `Γ(s) ≠ 0`. -/
theorem Gamma_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m h => ?_
  have := congrArg Complex.re h
  simp [hs] at this
  have h2 : (2 : ℝ) * m = 1 := by linarith
  have h3 : (2 * m : ℕ) = 1 := by exact_mod_cast h2
  omega

/-- On the line `Re s = -1/2`, `Γ_ℂ(s) ≠ 0`. -/
theorem Gammaℂ_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re s hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  left
  exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- On the line `Re s = -1/2`, `‖Γ_ℝ(1 - s)‖ = ‖Γ_ℝ(s)‖ ‖s‖ / (2π)`. -/
theorem norm_Gammaℝ_one_sub (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℝ (1 - s)‖ = ‖Gammaℝ s‖ * ‖s‖ / (2 * Real.pi) := by
  rw [one_sub_eq_conj s hs, Gammaℝ_conj, Complex.norm_conj, Gammaℝ_add_two (ne_zero_of_re s hs)]
  rw [norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.norm_ofNat]
  ring

/-- On the line `Re s = -1/2`, `‖Γ_ℂ(1 - s)‖ = ‖Γ_ℂ(s)‖ ‖s‖ ‖s + 1‖ / (2π) ^ 2`. -/
theorem norm_Gammaℂ_one_sub (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℂ (1 - s)‖ = ‖Gammaℂ s‖ * ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 := by
  rw [one_sub_eq_conj s hs, Gammaℂ_conj, Complex.norm_conj]
  have h1 : s + 2 = (s + 1) + 1 := by ring
  rw [h1, Gammaℂ_add_one (add_one_ne_zero_of_re s hs), Gammaℂ_add_one (ne_zero_of_re s hs)]
  rw [norm_div, norm_div, norm_mul, norm_div, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.norm_ofNat]
  ring

/-- On the line `Re s = -1/2`, `‖s‖ ≤ 1 + |Im s|`. -/
theorem norm_le_one_add_abs_im_of_re (s : ℂ) (hs : s.re = -1 / 2) : ‖s‖ ≤ 1 + |s.im| :=
  calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
    _ = 1 / 2 + |s.im| := by rw [hs]; norm_num
    _ ≤ 1 + |s.im| := by linarith

/-- On the line `Re s = -1/2`, `‖s + 1‖ ≤ 1 + |Im s|`. -/
theorem norm_add_one_le_one_add_abs_im_of_re (s : ℂ) (hs : s.re = -1 / 2) :
    ‖s + 1‖ ≤ 1 + |s.im| :=
  calc ‖s + 1‖ ≤ |(s + 1).re| + |(s + 1).im| := norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + |s.im| := by rw [add_re, one_re, hs, add_im, one_im, add_zero]; norm_num
    _ ≤ 1 + |s.im| := by linarith

/-- On the line `Re s = -1/2`, `‖Γ_ℝ(1 - s)‖ ‖Γ_ℝ(s)⁻¹‖ ≤ 1 + |Im s|`. -/
theorem norm_Gammaℝ_one_sub_mul_norm_inv_le (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℝ (1 - s)‖ * ‖(Gammaℝ s)⁻¹‖ ≤ 1 + |s.im| := by
  have hΓ := Gammaℝ_ne_zero_of_re s hs
  rw [norm_Gammaℝ_one_sub s hs, norm_inv]
  have : ‖Gammaℝ s‖ * ‖s‖ / (2 * Real.pi) * ‖Gammaℝ s‖⁻¹ = ‖s‖ / (2 * Real.pi) := by
    field_simp
  rw [this]
  exact (div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])).trans
    (norm_le_one_add_abs_im_of_re s hs)

/-- On the line `Re s = -1/2`, `‖Γ_ℂ(1 - s)‖ ‖Γ_ℂ(s)⁻¹‖ ≤ (1 + |Im s|) ^ 2`. -/
theorem norm_Gammaℂ_one_sub_mul_norm_inv_le (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℂ (1 - s)‖ * ‖(Gammaℂ s)⁻¹‖ ≤ (1 + |s.im|) ^ 2 := by
  have hΓ := Gammaℂ_ne_zero_of_re s hs
  rw [norm_Gammaℂ_one_sub s hs, norm_inv]
  have : ‖Gammaℂ s‖ * ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 * ‖Gammaℂ s‖⁻¹ =
      ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 := by
    field_simp
  rw [this]
  have hπ2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  calc ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 ≤ ‖s‖ * ‖s + 1‖ / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos hπ2
    _ ≤ (1 + |s.im|) * (1 + |s.im|) := by
        rw [div_one]
        exact mul_le_mul (norm_le_one_add_abs_im_of_re s hs)
          (norm_add_one_le_one_add_abs_im_of_re s hs) (norm_nonneg _)
          (by linarith [abs_nonneg s.im])
    _ = (1 + |s.im|) ^ 2 := (sq _).symm

end Gamma

variable (K : Type) [Field K] [NumberField K]

/-- A height-one prime of `𝓞 K` has absolute norm at least `2`. -/
theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

/-- The constant `exp (2 ∑_v N(v) ^ (-3/2))`, the sum running over the height-one spectrum of
`𝓞 K`. -/
noncomputable def dedekindZetaBound : ℝ :=
  Real.exp (2 * ∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

/-- `dedekindZetaBound K > 0`. -/
theorem dedekindZetaBound_pos : 0 < dedekindZetaBound K := Real.exp_pos _

/-- For `Re s ≥ 3/2`, `‖ζ_K(s)‖ ≤ dedekindZetaBound K`. -/
theorem norm_dedekindZeta_le (s : ℂ) (hs : 3 / 2 ≤ s.re) :
    ‖dedekindZeta K s‖ ≤ dedekindZetaBound K := by
  have hs1 : 1 < s.re := by linarith
  have hprod := (_root_.NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs1).tprod_eq
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
    _root_.NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs1
  have h := _root_.EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) (two_le_absNorm K)
    (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) s hs1.le hsum
  simp only [one_mul] at h
  rw [← hprod]
  refine h.trans ?_
  unfold dedekindZetaBound
  rw [Real.exp_le_exp]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Summable.tsum_le_tsum (fun v => ?_) hsum
    (_root_.NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K (by norm_num))
  have h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have := two_le_absNorm K v
    exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

/-- On the line `Re s = -1/2`, `‖d_K ^ ((1 - s) / 2)‖ ‖(d_K ^ (s / 2))⁻¹‖ = d_K`. -/
theorem norm_absDiscr_cpow_one_sub_mul_norm_inv (s : ℂ) (hs : s.re = -1 / 2) :
    ‖(absDiscr K : ℂ) ^ ((1 - s) / 2)‖ * ‖((absDiscr K : ℂ) ^ (s / 2))⁻¹‖ = absDiscr K := by
  rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos (absDiscr_pos K),
    Complex.norm_cpow_eq_rpow_re_of_pos (absDiscr_pos K)]
  have h1 : ((1 - s) / 2).re = 3 / 4 := by
    rw [show ((1 - s) / 2).re = (1 - s).re / 2 by simp, sub_re, one_re, hs]
    norm_num
  have h2 : (s / 2).re = -(1 / 4) := by
    rw [show (s / 2).re = s.re / 2 by simp, hs]
    norm_num
  rw [h1, h2, ← Real.rpow_neg (absDiscr_pos K).le, neg_neg, ← Real.rpow_add (absDiscr_pos K)]
  norm_num

variable {K}

/-- A continuation of `ζ_K` equals `Λ_K` times the inverse gamma factor off `{0, 1}`. -/
theorem f_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s)
    (Λ : ℂ → ℂ) (hΛd : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) :
    Set.EqOn f (fun s => Λ s * invGammaFactor K s) ({(0 : ℂ), 1}ᶜ) := by
  have hsub : ({(0 : ℂ), 1}ᶜ : Set ℂ) ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, not_or] at hz
    exact hz.2
  have hfan : AnalyticOnNhd ℂ f ({(0 : ℂ), 1}ᶜ) := (hf.mono hsub).analyticOnNhd isOpen_compl01
  have hgan : AnalyticOnNhd ℂ (fun s => Λ s * invGammaFactor K s) ({(0 : ℂ), 1}ᶜ) :=
    (hΛd.mul (differentiable_invGammaFactor K).differentiableOn).analyticOnNhd isOpen_compl01
  have h2mem : (2 : ℂ) ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  have hagree : ∀ s : ℂ, 1 < s.re → f s = Λ s * invGammaFactor K s := fun s hs =>
    (hfζ s hs).trans (dedekindZeta_eq_mul_invGammaFactor K Λ hΛeq hs)
  have hev : f =ᶠ[𝓝 (2 : ℂ)] (fun s => Λ s * invGammaFactor K s) :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)) hagree
  exact hfan.eqOn_of_preconnected_of_eventuallyEq hgan isPreconnected_compl01 h2mem hev

/-- If `f` is differentiable off `1` and agrees with `ζ_K` on `Re s > 1`, and `R` is an entire
extension of `(s - 1) ζ_K(s)`, then `(s - 1) f(s) = R(s)` for all `s ≠ 1`. -/
theorem sub_one_mul_eq_of_continuation
    {f R : ℂ → ℂ} (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * dedekindZeta K s) :
    ∀ s : ℂ, s ≠ 1 → (s - 1) * f s = R s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hg : AnalyticOnNhd ℂ (fun s => (s - 1) * f s) ({1}ᶜ : Set ℂ) :=
    ((differentiableOn_id.sub_const 1).mul hf).analyticOnNhd hU
  have hR' : AnalyticOnNhd ℂ R ({1}ᶜ : Set ℂ) := hR.differentiableOn.analyticOnNhd hU
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : (fun s => (s - 1) * f s) =ᶠ[𝓝 (2 : ℂ)] R := by
    have hV : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    rw [hfζ s hs, hRζ s hs]
  intro s hs
  exact hg.eqOn_of_preconnected_of_eventuallyEq hR' hconn h2 hev hs

/-- `t ^ 2 ≤ 4 exp |t|`. -/
theorem sq_le_four_mul_exp_abs (t : ℝ) : t ^ 2 ≤ 4 * Real.exp |t| := by
  have h1 : |t| / 2 + 1 ≤ Real.exp (|t| / 2) := Real.add_one_le_exp _
  have h0 : 0 ≤ |t| / 2 + 1 := by positivity
  have h2 : (|t| / 2 + 1) ^ 2 ≤ Real.exp (|t| / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : Real.exp (|t| / 2) ^ 2 = Real.exp |t| := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h4 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  nlinarith [abs_nonneg t, h2, h3, h4]

/-- A Gaussian bound `max B 1 exp (max C 0 t ^ 2)` is dominated by `exp (B' exp |t|)` for some
`B'`. -/
theorem gaussian_le_doubleExp (B C : ℝ) :
    ∃ B' : ℝ, ∀ t : ℝ,
      max B 1 * Real.exp (max C 0 * t ^ 2) ≤ Real.exp (B' * Real.exp (1 * |t|)) := by
  refine ⟨Real.log (max B 1) + 4 * max C 0, fun t => ?_⟩
  have hB1 : 1 ≤ max B 1 := le_max_right _ _
  have hB0 : 0 < max B 1 := one_pos.trans_le hB1
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hlog : 0 ≤ Real.log (max B 1) := Real.log_nonneg hB1
  have he1 : 1 ≤ Real.exp (1 * |t|) := by rw [one_mul]; exact Real.one_le_exp (abs_nonneg t)
  have hrew : max B 1 * Real.exp (max C 0 * t ^ 2) =
      Real.exp (Real.log (max B 1) + max C 0 * t ^ 2) := by
    rw [Real.exp_add, Real.exp_log hB0]
  rw [hrew, Real.exp_le_exp]
  have h1 : Real.log (max B 1) ≤ Real.log (max B 1) * Real.exp (1 * |t|) :=
    le_mul_of_one_le_right hlog he1
  have h2 : max C 0 * t ^ 2 ≤ 4 * max C 0 * Real.exp (1 * |t|) := by
    rw [one_mul]
    have := sq_le_four_mul_exp_abs t
    nlinarith
  nlinarith

/-- For `Re z ≤ 3/2`, `‖z - 1‖ ≤ ‖z - 2‖`. -/
theorem norm_sub_one_le_norm_sub_two (z : ℂ) (hz : z.re ≤ 3 / 2) : ‖z - 1‖ ≤ ‖z - 2‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero, re_ofNat, im_ofNat]
  nlinarith

/-- A function `f` differentiable off `1` and agreeing with `ζ_K` on `Re s > 1` satisfies
`‖f s‖ ≤ C (1 + |Im s|) ^ [K : ℚ]` on the line `Re s = -1/2`. -/
theorem left_line {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) :
    ∃ C : ℝ, ∀ s : ℂ, s.re = -1 / 2 →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ Module.finrank ℚ K := by
  obtain ⟨Λ, hΛd, hFE, hΛeq, -, -⟩ := _root_.NumberField.exists_completedDedekindZeta_package_core K
  obtain ⟨r₁, hr₁⟩ : ∃ r : ℕ, NumberField.InfinitePlace.nrRealPlaces K = r := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r : ℕ, NumberField.InfinitePlace.nrComplexPlaces K = r := ⟨_, rfl⟩
  have hN : Module.finrank ℚ K = r₁ + 2 * r₂ := by
    rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K, hr₁, hr₂]
  refine ⟨absDiscr K * dedekindZetaBound K, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := ne_zero_of_re s hs
  have hs1 : s ≠ 1 := ne_one_of_re s hs
  have hsmem : s ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩
  have hfeq : f s = Λ s * invGammaFactor K s := f_eq hf hfζ Λ hΛd hΛeq hsmem
  have hΛs : Λ s = Λ (1 - s) := (hFE s hs0 hs1).symm
  have h1s : 1 < (1 - s).re := by rw [sub_re, one_re, hs]; norm_num
  have h1s' : 3 / 2 ≤ (1 - s).re := by rw [sub_re, one_re, hs]; norm_num
  have hΛ1s : Λ (1 - s) = (absDiscr K : ℂ) ^ ((1 - s) / 2) * Gammaℝ (1 - s) ^ r₁ *
      Gammaℂ (1 - s) ^ r₂ * dedekindZeta K (1 - s) := by
    rw [hΛeq (1 - s) h1s, intCast_abs_discr_eq_ofReal_absDiscr, hr₁, hr₂]
  have hinv : invGammaFactor K s =
      ((absDiscr K : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂ := by
    unfold invGammaFactor; rw [hr₁, hr₂]
  have hζ := norm_dedekindZeta_le K (1 - s) h1s'
  set dA : ℝ := ‖(absDiscr K : ℂ) ^ ((1 - s) / 2)‖ with hdA
  set dB : ℝ := ‖((absDiscr K : ℂ) ^ (s / 2))⁻¹‖ with hdB
  set gA : ℝ := ‖Gammaℝ (1 - s)‖ with hgA
  set gB : ℝ := ‖(Gammaℝ s)⁻¹‖ with hgB
  set cA : ℝ := ‖Gammaℂ (1 - s)‖ with hcA
  set cB : ℝ := ‖(Gammaℂ s)⁻¹‖ with hcB
  set z : ℝ := ‖dedekindZeta K (1 - s)‖ with hz
  have hnorm : ‖f s‖ = (dA * dB) * (gA * gB) ^ r₁ * (cA * cB) ^ r₂ * z := by
    rw [hfeq, hΛs, hΛ1s, hinv]
    simp only [norm_mul, norm_pow]
    rw [mul_pow, mul_pow]
    ring
  rw [hnorm, norm_absDiscr_cpow_one_sub_mul_norm_inv K s hs, hN]
  calc absDiscr K * (gA * gB) ^ r₁ * (cA * cB) ^ r₂ * z
      ≤ absDiscr K * (1 + |s.im|) ^ r₁ * ((1 + |s.im|) ^ 2) ^ r₂ * dedekindZetaBound K := by
        have h3 : (gA * gB) ^ r₁ ≤ (1 + |s.im|) ^ r₁ :=
          pow_le_pow_left₀ (by positivity) (norm_Gammaℝ_one_sub_mul_norm_inv_le s hs) r₁
        have h4 : (cA * cB) ^ r₂ ≤ ((1 + |s.im|) ^ 2) ^ r₂ :=
          pow_le_pow_left₀ (by positivity) (norm_Gammaℂ_one_sub_mul_norm_inv_le s hs) r₂
        have hDK := (absDiscr_pos K).le
        have hMK := (dedekindZetaBound_pos K).le
        gcongr
    _ = absDiscr K * dedekindZetaBound K * (1 + |s.im|) ^ (r₁ + 2 * r₂) := by
        rw [← pow_mul, pow_add]; ring

/-- A function agreeing with `ζ_K` on `Re s > 1` is bounded on the line `Re s = 3/2`. -/
theorem right_line {f : ℂ → ℂ} (hfζ : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) :
    ∃ C : ℝ, ∀ s : ℂ, s.re = 3 / 2 → ‖f s‖ ≤ C :=
  ⟨dedekindZetaBound K, fun s hs => by
    rw [hfζ s (by rw [hs]; norm_num)]
    exact norm_dedekindZeta_le K s hs.ge⟩

/-- For `Re z ≤ 3/2`, `1/2 ≤ ‖z - 2‖`. -/
theorem one_half_le_norm_sub_two (z : ℂ) (hz : z.re ≤ 3 / 2) : 1 / 2 ≤ ‖z - 2‖ :=
  calc (1 / 2 : ℝ) ≤ |(z - 2).re| := by
        rw [abs_of_neg (by simp; linarith)]; simp; linarith
    _ ≤ ‖z - 2‖ := Complex.abs_re_le_norm _

/-- For `Re z ≤ 3/2`, `z - 2 ≠ 0`. -/
theorem sub_two_ne_zero_of_re_le (z : ℂ) (hz : z.re ≤ 3 / 2) : z - 2 ≠ 0 :=
  norm_pos_iff.mp (by linarith [one_half_le_norm_sub_two z hz])

/-- `2 x ≤ max (2 B) 1 exp (max C 0 t ^ 2)` whenever `x ≤ B exp (C t ^ 2)`. -/
theorem two_mul_le_max_mul_exp {x B C t : ℝ} (hx : x ≤ B * Real.exp (C * t ^ 2)) :
    2 * x ≤ max (2 * B) 1 * Real.exp (max C 0 * t ^ 2) := by
  have he : Real.exp (C * t ^ 2) ≤ Real.exp (max C 0 * t ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have hmax : 0 < max (2 * B) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc 2 * x ≤ (2 * B) * Real.exp (C * t ^ 2) := by linarith
    _ ≤ max (2 * B) 1 * Real.exp (C * t ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max (2 * B) 1 * Real.exp (max C 0 * t ^ 2) := mul_le_mul_of_nonneg_left he hmax.le

/-- If `(z - 1) x = r` and `Re z ≤ 3/2`, then `‖r / (z - 2)‖ ≤ ‖x‖`. -/
theorem norm_div_sub_two_le {z x r : ℂ} (hz : z.re ≤ 3 / 2) (hx : (z - 1) * x = r) :
    ‖r / (z - 2)‖ ≤ ‖x‖ := by
  rw [← hx, norm_div, norm_mul,
    div_le_iff₀ (norm_pos_iff.mpr (sub_two_ne_zero_of_re_le z hz))]
  exact (mul_le_mul_of_nonneg_right (norm_sub_one_le_norm_sub_two z hz)
    (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- For entire `R`, `R z / (z - 2)` is `DiffContOnCl` on the strip `-1/2 < Re z < 3/2`. -/
theorem diffContOnCl_div_sub_two {R : ℂ → ℂ} (hR : Differentiable ℂ R) :
    DiffContOnCl ℂ (fun z => R z / (z - 2)) (Complex.re ⁻¹' Set.Ioo (-1 / 2) (3 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hcl : closure (Complex.re ⁻¹' Set.Ioo (-1 / 2 : ℝ) (3 / 2)) ⊆ {z : ℂ | z.re ≤ 3 / 2} :=
    closure_minimal (fun z hz => le_of_lt hz.2) (isClosed_le continuous_re continuous_const)
  exact (hR.differentiableOn.div (differentiableOn_id.sub_const 2)
    fun z hz => sub_two_ne_zero_of_re_le z hz).mono hcl

/-- A Gaussian bound on `R` in the strip `-1/2 ≤ Re z ≤ 3/2` gives the Phragmén–Lindelöf growth
condition for `R z / (z - 2)`. -/
theorem exists_growth_div_sub_two {R : ℂ → ℂ} {B C : ℝ}
    (hBC : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → ‖R z‖ ≤ B * Real.exp (C * z.im ^ 2)) :
    ∃ c : ℝ, c < Real.pi / (3 / 2 - -1 / 2) ∧ ∃ B' : ℝ, ∀ z : ℂ,
      -1 / 2 < z.re → z.re < 3 / 2 → ‖R z / (z - 2)‖ ≤ Real.exp (B' * Real.exp (c * |z.im|)) := by
  obtain ⟨B', hB'⟩ := gaussian_le_doubleExp (2 * B) C
  refine ⟨1, ?_, B', fun z hz1 hz2 => ?_⟩
  · rw [show (3 / 2 - -1 / 2 : ℝ) = 2 by norm_num, lt_div_iff₀ (by norm_num)]
    linarith [Real.pi_gt_three]
  have h2 := one_half_le_norm_sub_two z hz2.le
  have hgz : ‖R z / (z - 2)‖ ≤ 2 * ‖R z‖ := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (R z)]
  exact hgz.trans ((two_mul_le_max_mul_exp (hBC z hz1.le hz2.le)).trans (hB' z.im))

/-- If `(s - 1) x = r`, `‖s‖ ≥ 2` and `Re s ≤ 3/2`, then `‖x‖ ≤ 2 ‖r / (s - 2)‖`. -/
theorem norm_le_two_mul_norm_div_sub_two {s x r : ℂ} (hs : 2 ≤ ‖s‖) (hre : s.re ≤ 3 / 2)
    (hx : (s - 1) * x = r) : ‖x‖ ≤ 2 * ‖r / (s - 2)‖ := by
  have hsub1 : 1 ≤ ‖s - 1‖ := by
    have := norm_sub_norm_le s 1
    rw [norm_one] at this
    linarith
  have hsub2 : ‖s - 2‖ ≤ 2 * ‖s - 1‖ :=
    calc ‖s - 2‖ = ‖(s - 1) - 1‖ := by ring_nf
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖s - 1‖ := by rw [norm_one]; linarith
  have h2pos : 0 < ‖s - 2‖ := norm_pos_iff.mpr (sub_two_ne_zero_of_re_le s hre)
  have hkey : ‖s - 1‖ * ‖x‖ = ‖r / (s - 2)‖ * ‖s - 2‖ := by
    rw [← hx, norm_div, norm_mul, div_mul_cancel₀ _ h2pos.ne']
  have : ‖s - 1‖ * ‖x‖ ≤ ‖s - 1‖ * (2 * ‖r / (s - 2)‖) := by
    rw [hkey]
    nlinarith [norm_nonneg (r / (s - 2))]
  exact le_of_mul_le_mul_left this (by linarith)

/-- A function `f` differentiable off `1` and agreeing with `ζ_K` on `Re s > 1` satisfies
`‖f s‖ ≤ C (1 + |Im s|) ^ [K : ℚ]` on the strip `-1/2 ≤ Re s ≤ 3/2` with `‖s‖ ≥ 2`. -/
theorem strip {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) :
    ∃ C : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ ‖s‖ →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ Module.finrank ℚ K := by
  set N : ℕ := Module.finrank ℚ K
  obtain ⟨CL, hL⟩ := left_line hf hfζ
  obtain ⟨R, hR, -, hRζ, -⟩ :=
    _root_.NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  have hfR := sub_one_mul_eq_of_continuation hf hfζ hR hRζ
  obtain ⟨B, C2, hBC⟩ :=
    _root_.NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
      K R hR hRζ (-1 / 2) (3 / 2)
  obtain ⟨Cp, -, hPL⟩ :=
    _root_.PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
      (-1 / 2) (3 / 2) (N : ℝ) (by norm_num) (Nat.cast_nonneg _)
  set M : ℝ := max CL 0 + dedekindZetaBound K
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (dedekindZetaBound_pos K).le
  set g : ℂ → ℂ := fun z => R z / (z - 2)
  have hgf : ∀ z : ℂ, z.re ≤ 3 / 2 → z ≠ 1 → ‖g z‖ ≤ ‖f z‖ := fun z hz hz1 =>
    norm_div_sub_two_le hz (hfR z hz1)
  have hgrowth : ∃ c : ℝ, c < Real.pi / (3 / 2 - -1 / 2) ∧ ∃ B' : ℝ, ∀ z : ℂ,
      -1 / 2 < z.re → z.re < 3 / 2 → ‖g z‖ ≤ Real.exp (B' * Real.exp (c * |z.im|)) :=
    exists_growth_div_sub_two hBC
  have hleft : ∀ z : ℂ, z.re = -1 / 2 → ‖g z‖ ≤ M * (1 + |z.im|) ^ (N : ℝ) := by
    intro z hz
    have hz1 : z ≠ 1 := ne_one_of_re z hz
    rw [Real.rpow_natCast]
    calc ‖g z‖ ≤ ‖f z‖ := hgf z (by rw [hz]; norm_num) hz1
      _ ≤ CL * (1 + |z.im|) ^ N := hL z hz
      _ ≤ max CL 0 * (1 + |z.im|) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ M * (1 + |z.im|) ^ N :=
          mul_le_mul_of_nonneg_right (by linarith [(dedekindZetaBound_pos K).le]) (by positivity)
  have hright : ∀ z : ℂ, z.re = 3 / 2 → ‖g z‖ ≤ M * (1 + |z.im|) ^ (N : ℝ) := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    have hfz : ‖f z‖ ≤ dedekindZetaBound K := by
      rw [hfζ z (by rw [hz]; norm_num)]; exact norm_dedekindZeta_le K z hz.ge
    exact ((hgf z hz.le hz1).trans (by linarith [le_max_right CL 0])).trans
      (le_mul_of_one_le_right hM0
        (Real.one_le_rpow (by linarith [abs_nonneg z.im]) (Nat.cast_nonneg _)))
  refine ⟨2 * (Cp * M), fun s hs1 hs2 hs => ?_⟩
  have hgs := hPL g M hM0 (diffContOnCl_div_sub_two hR) hgrowth hleft hright s hs1 hs2
  rw [Real.rpow_natCast] at hgs
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  calc ‖f s‖ ≤ 2 * ‖g s‖ := norm_le_two_mul_norm_div_sub_two hs hs2 (hfR s hs1')
    _ ≤ 2 * (Cp * M * (1 + |s.im|) ^ N) := by linarith
    _ = 2 * (Cp * M) * (1 + |s.im|) ^ N := by ring

/-- A function `f` differentiable off `1` and agreeing with `ζ_K` on `Re s > 1` satisfies
`‖f s‖ ≤ C (1 + |Im s|) ^ [K : ℚ]` on the half-plane `Re s ≥ 1/2` with `‖s‖ ≥ 2`. -/
theorem global {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hfζ : ∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ Module.finrank ℚ K := by
  obtain ⟨Cs, hCs⟩ := strip hf hfζ
  refine ⟨max Cs (dedekindZetaBound K), fun s hs1 hs2 => ?_⟩
  have hpow : (1 : ℝ) ≤ (1 + |s.im|) ^ Module.finrank ℚ K :=
    one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases le_or_gt s.re (3 / 2) with h | h
  · calc ‖f s‖ ≤ Cs * (1 + |s.im|) ^ Module.finrank ℚ K := hCs s (by linarith) h hs2
      _ ≤ max Cs (dedekindZetaBound K) * (1 + |s.im|) ^ Module.finrank ℚ K :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · rw [hfζ s (by linarith)]
    exact ((norm_dedekindZeta_le K s h.le).trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right ((dedekindZetaBound_pos K).le.trans (le_max_right _ _)) hpow)

end AntRHScratch
