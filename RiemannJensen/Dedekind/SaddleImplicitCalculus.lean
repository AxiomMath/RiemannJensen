module

public import RiemannJensen.Dedekind.SaddleActionDerivatives
public import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-! # Implicit calculus for the Dedekind saddle branch -/

@[expose] public section

namespace RiemannJensen

open Set Filter
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private noncomputable def openSaddleRadial (Λ α r : ℝ) : ℝ :=
  Λ * Real.cos α / (saddleKappa * r) + α * Real.cos α / Real.sin α -
    Λ / 2 - 1 - Real.log r

/-- The partial derivative in `α` of the radial saddle equation
`Λ cos α / (κ r) + α cos α / sin α - Λ / 2 - 1 - log r`. -/
noncomputable def openSaddleRadialDerivAlpha (Λ α r : ℝ) : ℝ :=
  -Λ * Real.sin α / (saddleKappa * r) +
    (Real.sin α * Real.cos α - α) / Real.sin α ^ 2

/-- The partial derivative in `r` of the radial saddle equation
`Λ cos α / (κ r) + α cos α / sin α - Λ / 2 - 1 - log r`. -/
noncomputable def openSaddleRadialDerivRadius (Λ α r : ℝ) : ℝ :=
  -Λ * Real.cos α / (saddleKappa * r ^ 2) - 1 / r

private theorem sin_pos_of_mem_Ioo_zero_pi_div_two {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.sin α :=
  Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2, Real.pi_pos])

private theorem cos_pos_of_mem_Ioo_zero_pi_div_two {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.cos α :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩

private theorem hasStrictDerivAt_sinRatio {α : ℝ} (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    HasStrictDerivAt sinRatio ((Real.sin α - α * Real.cos α) / Real.sin α ^ 2) α := by
  have hraw := (hasStrictDerivAt_id α).div (Real.hasStrictDerivAt_sin α)
    (sin_pos_of_mem_Ioo_zero_pi_div_two hα).ne'
  have enez : ∀ᶠ x in 𝓝 α, x ≠ 0 := continuousAt_id.eventually_ne hα.1.ne'
  refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [enez] with x hx
    rw [sinRatio_of_ne hx]
    rfl
  · simp [id]

private theorem hasDerivAt_openSaddleRadial_alpha {Λ α r : ℝ}
    (hα : Real.sin α ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun β => openSaddleRadial Λ β r)
      (openSaddleRadialDerivAlpha Λ α r) α := by
  unfold openSaddleRadial openSaddleRadialDerivAlpha
  have h₁ := ((hasDerivAt_const α Λ).mul (Real.hasDerivAt_cos α)).div_const
      (saddleKappa * r)
  have h₂ := ((hasDerivAt_id α).mul (Real.hasDerivAt_cos α)).div
      (Real.hasDerivAt_sin α) hα
  have h := (((h₁.add h₂).sub_const (Λ / 2)).sub_const 1).sub_const (Real.log r)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, id_eq]
  · simp only [Pi.mul_apply, id_eq]
    field_simp
    rw [show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by
      nlinarith [Real.cos_sq_add_sin_sq α]]
    ring

private theorem hasDerivAt_openSaddleRadial_radius {Λ α r : ℝ}
    (hr : r ≠ 0) :
    HasDerivAt (fun t => openSaddleRadial Λ α t)
      (openSaddleRadialDerivRadius Λ α r) r := by
  unfold openSaddleRadial openSaddleRadialDerivRadius
  have h₁ := (hasDerivAt_const r (Λ * Real.cos α / saddleKappa)).div
      (hasDerivAt_id r) hr
  have h := (((h₁.add_const (α * Real.cos α / Real.sin α)).sub_const
    (Λ / 2)).sub_const 1).sub (Real.hasDerivAt_log hr)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    simp only [Pi.div_apply, Pi.sub_apply, id_eq]
    rw [div_eq_mul_inv]
    ring
  · simp only [id_eq]
    field_simp
    ring

private theorem openSaddleRadialDerivRadius_neg {Λ α r : ℝ}
    (hΛ : 0 < Λ) (hα : α ∈ Ioo 0 (Real.pi / 2)) (hr : 0 < r) :
    openSaddleRadialDerivRadius Λ α r < 0 := by
  unfold openSaddleRadialDerivRadius
  have hc := cos_pos_of_mem_Ioo_zero_pi_div_two hα
  have hκ := saddleKappa_pos
  rw [neg_mul, neg_div]
  linarith [show 0 < Λ * Real.cos α / (saddleKappa * r ^ 2) by positivity, one_div_pos.2 hr]

private theorem openSaddleRadialDerivAlpha_neg {Λ α r : ℝ}
    (hΛ : 0 < Λ) (hα : α ∈ Ioo 0 (Real.pi / 2)) (hr : 0 < r) :
    openSaddleRadialDerivAlpha Λ α r < 0 := by
  have hsin := sin_pos_of_mem_Ioo_zero_pi_div_two hα
  unfold openSaddleRadialDerivAlpha
  have hfirst : -Λ * Real.sin α / (saddleKappa * r) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hΛ) hsin)
      (mul_pos saddleKappa_pos hr)
  have hsecond : (Real.sin α * Real.cos α - α) / Real.sin α ^ 2 < 0 :=
    div_neg_of_neg_of_pos (sin_mul_cos_sub_self_neg hα.1 hα.2.le) (sq_pos_of_pos hsin)
  linarith

private noncomputable def openSaddleRadialFDerivAlpha (Λ α r : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (openSaddleRadialDerivAlpha Λ α r)

private noncomputable def openSaddleRadialFDerivRadius (Λ α r : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (openSaddleRadialDerivRadius Λ α r)

private theorem continuousAt_uncurry_openSaddleRadialFDerivAlpha {Λ α r : ℝ}
    (hsin : Real.sin α ≠ 0) (hr : r ≠ 0) :
    ContinuousAt (Function.uncurry (openSaddleRadialFDerivAlpha Λ)) (α, r) :=
  (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp
    (f := fun v : ℝ × ℝ => openSaddleRadialDerivAlpha Λ v.1 v.2) (by
      unfold openSaddleRadialDerivAlpha
      fun_prop (disch := simp [hsin, hr]))

private theorem continuousAt_uncurry_openSaddleRadialFDerivRadius {Λ α r : ℝ}
    (hr : r ≠ 0) :
    ContinuousAt (Function.uncurry (openSaddleRadialFDerivRadius Λ)) (α, r) :=
  (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp
    (f := fun v : ℝ × ℝ => openSaddleRadialDerivRadius Λ v.1 v.2) (by
      unfold openSaddleRadialDerivRadius
      fun_prop (disch := simp [hr]))

private theorem isInvertible_openSaddleRadialFDerivRadius {Λ α r : ℝ}
    (h : openSaddleRadialDerivRadius Λ α r ≠ 0) :
    (openSaddleRadialFDerivRadius Λ α r).IsInvertible :=
  ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h), by
    ext
    simp [openSaddleRadialFDerivRadius]⟩

private theorem openSaddleRadial_dedekindSaddleRadius_eq_zero (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    openSaddleRadial (dedekindScaleLambda K d) α (dedekindSaddleRadius K d α) = 0 := by
  have hchar := dedekindSaddleRadius_characterization K d hd ⟨hα.1.le, hα.2.le⟩
  rw [show alphaCot α = α * Real.cos α / Real.sin α by
    rw [alphaCot_of_ne hα.1.ne']] at hchar
  rw [saddleKappa] at hchar
  dsimp [openSaddleRadial]
  linarith

/-- The infimum-defined Dedekind saddle radius is strictly differentiable at every
angle in `(0, π / 2)`. -/
theorem exists_hasStrictDerivAt_dedekindSaddleRadius (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    ∃ r' : ℝ, HasStrictDerivAt (dedekindSaddleRadius K d) r' α := by
  let Λ := dedekindScaleLambda K d
  let r := dedekindSaddleRadius K d α
  have hΛ : 0 < Λ := dedekindScaleLambda_pos K d hd
  have hαcc : α ∈ Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd hαcc
  have hsin : Real.sin α ≠ 0 := (sin_pos_of_mem_Ioo_zero_pi_div_two hα).ne'
  let f : ℝ → ℝ → ℝ := openSaddleRadial Λ
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := openSaddleRadialFDerivAlpha Λ
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := openSaddleRadialFDerivRadius Λ
  have eSin : ∀ᶠ v : ℝ × ℝ in 𝓝 (α, r), Real.sin v.1 ≠ 0 :=
    ((Real.continuous_sin.continuousAt.comp continuousAt_fst).eventually_ne hsin)
  have eRad : ∀ᶠ v : ℝ × ℝ in 𝓝 (α, r), v.2 ≠ 0 :=
    continuousAt_snd.eventually_ne hr.ne'
  have df₁ : ∀ᶠ v : ℝ × ℝ in 𝓝 (α, r),
      HasFDerivAt (fun x => f x v.2) (f₁ v.1 v.2) v.1 := by
    filter_upwards [eSin, eRad] with v hvSin hvRad
    exact (hasDerivAt_openSaddleRadial_alpha hvSin hvRad).hasFDerivAt
  have df₂ : ∀ᶠ v : ℝ × ℝ in 𝓝 (α, r),
      HasFDerivAt (fun x => f v.1 x) (f₂ v.1 v.2) v.2 := by
    filter_upwards [eRad] with v hvRad
    exact (hasDerivAt_openSaddleRadial_radius hvRad).hasFDerivAt
  have cf₁ : ContinuousAt (Function.uncurry f₁) (α, r) :=
    continuousAt_uncurry_openSaddleRadialFDerivAlpha hsin hr.ne'
  have cf₂ : ContinuousAt (Function.uncurry f₂) (α, r) :=
    continuousAt_uncurry_openSaddleRadialFDerivRadius hr.ne'
  have if₂ : (f₂ α r).IsInvertible :=
    isInvertible_openSaddleRadialFDerivRadius (openSaddleRadialDerivRadius_neg hΛ hα hr).ne
  let ψ := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  have eψpos : ∀ᶠ β in 𝓝 α, 0 < ψ β :=
    (tendsto_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).eventually (Ioi_mem_nhds hr)
  have hbase : f α r = 0 := openSaddleRadial_dedekindSaddleRadius_eq_zero K d hd hα
  have eψeq : ∀ᶠ β in 𝓝 α, dedekindSaddleRadius K d β = ψ β := by
    filter_upwards [eψpos, Ioo_mem_nhds hα.1 hα.2,
      eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂]
      with β hψpos hβ hEq
    apply dedekindSaddleRadius_eq_of_radial K
      (dedekindSaddleRadialCoeff_nonneg K d hd ⟨hβ.1.le, hβ.2.le⟩) hψpos
    rw [saddleRadialAtLambda, show alphaCot β = β * Real.cos β / Real.sin β by
      rw [alphaCot_of_ne hβ.1.ne']]
    have hzero : f β (ψ β) = 0 := hEq.trans hbase
    dsimp [f, Λ, openSaddleRadial] at hzero
    rw [saddleKappa]
    linarith
  exact ⟨_, ((hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂)
    |>.congr_of_eventuallyEq (eψeq.mono fun _ h => h.symm)).hasStrictDerivAt⟩

/-- The infimum-defined radius is differentiable throughout the open branch. -/
theorem differentiableAt_dedekindSaddleRadius (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (dedekindSaddleRadius K d) α :=
  (exists_hasStrictDerivAt_dedekindSaddleRadius K d hd hα).choose_spec.hasDerivAt.differentiableAt

/-- Exact derivative of the implicit saddle radius on the open angle interval. -/
theorem hasDerivAt_dedekindSaddleRadius (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (dedekindSaddleRadius K d)
      (-openSaddleRadialDerivAlpha (dedekindScaleLambda K d) α
          (dedekindSaddleRadius K d α) /
        openSaddleRadialDerivRadius (dedekindScaleLambda K d) α
          (dedekindSaddleRadius K d α)) α := by
  let Λ := dedekindScaleLambda K d
  let R := dedekindSaddleRadius K d
  let r := R α
  let r' := deriv R α
  have hR : HasDerivAt R r' α := (differentiableAt_dedekindSaddleRadius K d hd hα).hasDerivAt
  have hr : 0 < r := by
    simpa [r, R] using dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hsin : Real.sin α ≠ 0 := (sin_pos_of_mem_Ioo_zero_pi_div_two hα).ne'
  have hcalc : HasDerivAt (fun β => openSaddleRadial Λ β (R β))
      (openSaddleRadialDerivAlpha Λ α r +
        openSaddleRadialDerivRadius Λ α r * r') α := by
    unfold openSaddleRadial openSaddleRadialDerivAlpha openSaddleRadialDerivRadius
    have hterm₁ := (((hasDerivAt_const α Λ).mul (Real.hasDerivAt_cos α)).div
      ((hasDerivAt_const α saddleKappa).mul hR)
      (mul_ne_zero saddleKappa_pos.ne' hr.ne'))
    have hterm₂ := ((hasDerivAt_id α).mul (Real.hasDerivAt_cos α)).div
      (Real.hasDerivAt_sin α) hsin
    have hlog := (Real.hasDerivAt_log hr.ne').comp α hR
    have h := (((hterm₁.add hterm₂).sub_const (Λ / 2)).sub_const 1).sub hlog
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, id_eq]
    rw [show R α = r by rfl]
    field_simp
    rw [show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by
      nlinarith [Real.cos_sq_add_sin_sq α]]
    ring
  have ezero : ∀ᶠ β in 𝓝 α, openSaddleRadial Λ β (R β) = 0 := by
    filter_upwards [Ioo_mem_nhds hα.1 hα.2] with β hβ
      using openSaddleRadial_dedekindSaddleRadius_eq_zero K d hd hβ
  have heqderiv : openSaddleRadialDerivAlpha Λ α r +
      openSaddleRadialDerivRadius Λ α r * r' = 0 :=
    hcalc.unique ((hasDerivAt_const α 0).congr_of_eventuallyEq ezero)
  refine hR.congr_deriv ?_
  apply (eq_div_iff (openSaddleRadialDerivRadius_neg
    (by simpa [Λ] using dedekindScaleLambda_pos K d hd) hα hr).ne).2
  dsimp [Λ, r, R] at heqderiv ⊢
  linarith

/-- The Dedekind saddle level has a strictly positive derivative on the open
angle branch. -/
theorem exists_pos_hasDerivAt_dedekindSaddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    ∃ q' : ℝ, 0 < q' ∧ HasDerivAt (dedekindSaddleQ K d) q' α := by
  let Λ := dedekindScaleLambda K d
  let R := dedekindSaddleRadius K d
  let r := R α
  let rp := -openSaddleRadialDerivAlpha Λ α r /
    openSaddleRadialDerivRadius Λ α r
  have hΛ : 0 < Λ := dedekindScaleLambda_pos K d hd
  have hr : 0 < r := by
    simpa [r, R] using dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hsin : 0 < Real.sin α := sin_pos_of_mem_Ioo_zero_pi_div_two hα
  have hrp : rp < 0 := div_neg_of_pos_of_neg (neg_pos.2 (openSaddleRadialDerivAlpha_neg hΛ hα hr))
    (openSaddleRadialDerivRadius_neg hΛ hα hr)
  have hR : HasDerivAt R rp α := by
    simpa [Λ, R, r, rp] using hasDerivAt_dedekindSaddleRadius K d hd hα
  let g := r⁻¹
  let gp := -rp / r ^ 2
  have hg : HasDerivAt (fun β => (R β)⁻¹) gp α := hR.inv hr.ne'
  have hgp : 0 < gp := div_pos (neg_pos.2 hrp) (sq_pos_of_pos hr)
  let sp := (Real.sin α - α * Real.cos α) / Real.sin α ^ 2
  have hs : HasDerivAt sinRatio sp α := (hasStrictDerivAt_sinRatio hα).hasDerivAt
  have hsp : 0 < sp := by
    dsimp [sp]
    have hcos := cos_pos_of_mem_Ioo_zero_pi_div_two hα
    have htan := Real.lt_tan hα.1 hα.2
    have htanmul := Real.tan_mul_cos hcos.ne'
    have hnum : 0 < Real.sin α - α * Real.cos α := by
      nlinarith [mul_lt_mul_of_pos_right htan hcos]
    exact div_pos hnum (sq_pos_of_pos hsin)
  have hspos : 0 < sinRatio α := sinRatio_pos_of_mem ⟨hα.1.le, hα.2.le⟩
  let c := 2 * saddleKappa / Λ
  have hc : 0 < c := div_pos (mul_pos two_pos saddleKappa_pos) hΛ
  let q' := 2 * g * gp + c * (sp * g + sinRatio α * gp)
  have hqpos : 0 < q' := by
    have hgpos : 0 < g := by dsimp [g]; positivity
    dsimp [q']
    positivity
  refine ⟨q', hqpos, ?_⟩
  unfold dedekindSaddleQ saddleQAtLambda
  change HasDerivAt (fun β => (R β)⁻¹ ^ 2 + c * sinRatio β * (R β)⁻¹) q' α
  refine ((hg.pow 2).add (((hasDerivAt_const α c).mul hs).mul hg)).congr_deriv ?_
  dsimp [q', g]
  ring

/-- The Dedekind saddle level has a strictly positive strict derivative on the
open angle branch. -/
theorem exists_pos_hasStrictDerivAt_dedekindSaddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) :
    ∃ q' : ℝ, 0 < q' ∧ HasStrictDerivAt (dedekindSaddleQ K d) q' α := by
  obtain ⟨q', hq', hq⟩ := exists_pos_hasDerivAt_dedekindSaddleQ K d hd hα
  let R := dedekindSaddleRadius K d
  obtain ⟨r', hR'⟩ := exists_hasStrictDerivAt_dedekindSaddleRadius K d hd hα
  have hr : R α ≠ 0 :=
    (dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩).ne'
  let c := 2 * saddleKappa / dedekindScaleLambda K d
  have hg := (hasStrictDerivAt_inv hr).comp α hR'
  have hstrict :=
    (hg.pow 2).add (((hasStrictDerivAt_const α c).mul (hasStrictDerivAt_sinRatio hα)).mul hg)
  refine ⟨q', hq', ?_⟩
  unfold dedekindSaddleQ saddleQAtLambda at hq ⊢
  change HasDerivAt
      (fun β => (R β)⁻¹ ^ 2 + c * sinRatio β * (R β)⁻¹) q' α at hq
  change HasStrictDerivAt
      (fun β => (R β)⁻¹ ^ 2 + c * sinRatio β * (R β)⁻¹) q' α
  exact hstrict.congr_deriv (hstrict.hasDerivAt.unique hq)

/-- The inverse saddle angle is differentiable throughout the open scale window. -/
theorem dedekind_saddle_angle_differentiable :
    ∀ d : ℕ, 1 ≤ d →
      DifferentiableOn ℝ (dedekindSaddleAngle K d)
        (Ioo (dedekindEdgeQ K d) (dedekindScaleT K d)) := by
  intro d hd q hq
  let α := dedekindSaddleAngle K d q
  have hqoc : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) :=
    ⟨hq.1, hq.2.le⟩
  have hα : α ∈ Ioo 0 (Real.pi / 2) := by
    simpa [α] using dedekindSaddle_inverse_range K d hd hqoc
  have hinv : dedekindSaddleQ K d α = q := by
    simpa [α] using dedekindSaddle_inverse K d hd hqoc
  obtain ⟨q', hq'pos, hQ⟩ :=
    exists_pos_hasStrictDerivAt_dedekindSaddleQ K d hd hα
  have hq'ne : q' ≠ 0 := hq'pos.ne'
  let ψ := hQ.localInverse (dedekindSaddleQ K d) q' α hq'ne
  have hψstrict : HasStrictDerivAt ψ q'⁻¹ q := by
    simpa [ψ, hinv] using hQ.to_localInverse hq'ne
  have eψinv : ∀ᶠ y in 𝓝 q, dedekindSaddleQ K d (ψ y) = y := by
    simpa [ψ, hinv] using hQ.eventually_right_inverse hq'ne
  have hψq : ψ q = α := by
    simpa [ψ, hinv] using (hQ.eventually_left_inverse hq'ne).self_of_nhds
  have eψrange : ∀ᶠ y in 𝓝 q, ψ y ∈ Ioo 0 (Real.pi / 2) :=
    hψstrict.hasDerivAt.continuousAt.eventually (by
      rw [hψq]
      exact Ioo_mem_nhds hα.1 hα.2)
  have eψeq : ∀ᶠ y in 𝓝 q, ψ y = dedekindSaddleAngle K d y := by
    filter_upwards [eψinv, eψrange, Ioo_mem_nhds hq.1 hq.2] with y hyψinv hyψrange hywin
    have hyoc : y ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) :=
      ⟨hywin.1, hywin.2.le⟩
    have hyrange := dedekindSaddle_inverse_range K d hd hyoc
    have hyinv := dedekindSaddle_inverse K d hd hyoc
    exact (dedekindSaddleQ_strictMonoOn K d hd).injOn
      ⟨hyψrange.1.le, hyψrange.2.le⟩
      ⟨hyrange.1.le, hyrange.2.le⟩
      (hyψinv.trans hyinv.symm)
  exact (hψstrict.congr_of_eventuallyEq eψeq).hasDerivAt.differentiableAt.differentiableWithinAt

/-- The complex saddle point is differentiable throughout the open scale window. -/
theorem dedekind_saddle_branch_differentiable :
    ∀ d : ℕ, 1 ≤ d →
      DifferentiableOn ℝ (dedekindSaddle K d)
        (Ioo (dedekindEdgeQ K d) (dedekindScaleT K d)) := by
  intro d hd q hq
  have hangle : DifferentiableAt ℝ (dedekindSaddleAngle K d) q :=
    (dedekind_saddle_angle_differentiable K d hd q hq).differentiableAt
      (Ioo_mem_nhds hq.1 hq.2)
  have hrange := dedekindSaddle_inverse_range K d hd ⟨hq.1, hq.2.le⟩
  have hradius : DifferentiableAt ℝ
      (fun y => dedekindSaddleRadius K d (dedekindSaddleAngle K d y)) q :=
    (differentiableAt_dedekindSaddleRadius K d hd hrange).comp q hangle
  apply DifferentiableAt.differentiableWithinAt
  unfold dedekindSaddle
  fun_prop

end

end RiemannJensen
