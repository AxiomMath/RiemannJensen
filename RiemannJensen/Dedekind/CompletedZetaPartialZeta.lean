module

public import RiemannJensen.Dedekind.CompletedZetaHeckeKernel

/-!
# Partial zeta functions as Mellin transforms

The Mellin transform of the Hecke theta kernel of an ideal class, computed place by place
through the Gamma integral, identifies it with the completed partial zeta function of that class.

## Main definitions

* `gapsw80_t8_partialDedekindZeta`: the partial Dedekind zeta function of an ideal class.
-/

@[expose] public section

namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

section

namespace FLT

namespace Gapsw80T8MellinGammaPartialZeta

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"
p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"
p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation
open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel
open FLT.Gapsw80T6TraceDualBridge FLT.Gapsw80T7ClosedFEWeakPair

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Asymptotics.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"
p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

/-- For `a > 0` and `0 < β.re`,
`∫ τ in Set.Ioi 0, τ ^ (β - 1) * exp (-(a * τ)) = a ^ (-β) * Complex.Gamma β`. -/
theorem gapsw80_t8_mellin_expNeg_eq_Gamma {a : ℝ} (ha : 0 < a) {β : ℂ} (hβ : 0 < β.re) :
    ∫ τ in Set.Ioi (0:ℝ), (τ : ℂ) ^ (β - 1) * cexp (-(a * τ : ℝ))
      = ((a : ℝ) : ℂ) ^ (-β) * Complex.Gamma β := by
  have hm := mellin_comp_mul_left (E := ℂ) (fun t ↦ cexp (-(t:ℝ))) β ha
  simp only [mellin, smul_eq_mul] at hm
  refine hm.trans ?_
  rw [Complex.Gamma_eq_integral hβ, Complex.GammaIntegral]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.ofReal_exp, Complex.ofReal_neg, mul_comm]

/-- For `a > 0` and `s : ℂ`, `(π * a) ^ (-(s/2)) * Complex.Gamma (s/2) = Gammaℝ s * a ^ (-(s/2))`.
-/
theorem gapsw80_t8_gammaFactor_isReal {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((π * a : ℝ) : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2)
      = Gammaℝ s * ((a:ℝ):ℂ) ^ (-(s/2)) := by
  rw [Gammaℝ_def, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg ha.le, neg_div]
  ring

/-- For `s : ℂ`, `2 * (2 * π) ^ (-s) * 2 ^ (s - 1) = π ^ (-s)`. -/
theorem gapsw80_t8_gammaℂ_norm_const (s : ℂ) :
    (2:ℂ) * ((2 * π : ℝ) : ℂ) ^ (-s) * (2:ℂ) ^ (s - 1) = ((π:ℝ):ℂ) ^ (-s) := by
  have h2ne : ((2:ℝ):ℂ) ≠ 0 := by norm_num
  rw [show ((2*π:ℝ):ℂ) = ((2:ℝ):ℂ) * ((π:ℝ):ℂ) from by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_nonneg,
    show (2:ℂ) = ((2:ℝ):ℂ) from by norm_num]
  calc ((2:ℝ):ℂ) * (((2:ℝ):ℂ)^(-s) * ((π:ℝ):ℂ)^(-s)) * ((2:ℝ):ℂ)^(s-1)
      = (((2:ℝ):ℂ)^(s-1) * ((2:ℝ):ℂ)^(-s) * ((2:ℝ):ℂ)) * ((π:ℝ):ℂ)^(-s) := by ring
    _ = ((2:ℝ):ℂ)^(s-1 + -s) * ((2:ℝ):ℂ) * ((π:ℝ):ℂ)^(-s) := by
        rw [Complex.cpow_add _ _ h2ne]
    _ = ((π:ℝ):ℂ)^(-s) := by
        rw [show s - 1 + -s = (-1:ℂ) from by ring, Complex.cpow_neg_one,
          inv_mul_cancel₀ h2ne, one_mul]

/-- For `a > 0` and `s : ℂ`,
`(π * a) ^ (-s) * Complex.Gamma s = Gammaℂ s * 2 ^ (s - 1) * a ^ (-s)`. -/
theorem gapsw80_t8_gammaFactor_isComplex {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((π * a : ℝ) : ℂ) ^ (-s) * Complex.Gamma s
      = Gammaℂ s * (2:ℂ) ^ (s - 1) * ((a:ℝ):ℂ) ^ (-s) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg ha.le,
    Gammaℂ_def]
  calc ((π:ℝ):ℂ)^(-s) * ((a:ℝ):ℂ)^(-s) * Complex.Gamma s
      = ((2:ℂ) * ((2*π:ℝ):ℂ)^(-s) * (2:ℂ)^(s-1)) * ((a:ℝ):ℂ)^(-s) * Complex.Gamma s := by
        rw [gapsw80_t8_gammaℂ_norm_const]
    _ = 2 * (2 * (π:ℂ))^(-s) * Complex.Gamma s * (2:ℂ)^(s-1) * ((a:ℝ):ℂ)^(-s) := by
        rw [show ((2*π:ℝ):ℂ) = 2 * (π:ℂ) from by push_cast; ring]; ring

/-- For real `a ≥ 0`, `n : ℕ` and `z : ℂ`, `(a ^ n) ^ z = a ^ (n * z)` with complex powers. -/
theorem gapsw80_t8_ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (z : ℂ) :
    (((a : ℝ) : ℂ) ^ n) ^ z = ((a : ℝ) : ℂ) ^ ((n : ℂ) * z) := by
  have harg : (n : ℝ) * Complex.arg ((a:ℝ):ℂ) = 0 := by
    rw [Complex.arg_ofReal_of_nonneg ha, mul_zero]
  exact (Complex.cpow_nat_mul' (x := ((a:ℝ):ℂ)) (n := n)
    (harg ▸ neg_lt_zero.mpr Real.pi_pos) (harg ▸ Real.pi_nonneg) z).symm

/-- For real `a ≥ 0` and `z : ℂ`, `(Real.sqrt a) ^ z = a ^ (z / 2)` with complex powers. -/
theorem gapsw80_t8_ofReal_sqrt_cpow {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    ((Real.sqrt a : ℝ) : ℂ) ^ z = ((a : ℝ) : ℂ) ^ (z / 2) := by
  have key := gapsw80_t8_ofReal_pow_cpow (Real.sqrt_nonneg a) 2 (z / 2)
  rw [show (((Real.sqrt a : ℝ):ℂ))^(2:ℕ) = ((a:ℝ):ℂ) by
        rw [← Complex.ofReal_pow, Real.sq_sqrt ha],
      show ((2:ℕ):ℂ) * (z/2) = z by push_cast; ring] at key
  exact key.symm

/-- For a finset `s` and real `a i ≥ 0` on `s`, the complex power `z` of the real product
`∏ i ∈ s, a i` equals `∏ i ∈ s, (a i) ^ z`. -/
theorem gapsw80_t8_prod_ofReal_cpow {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (z : ℂ) :
    ((∏ i ∈ s, a i : ℝ) : ℂ) ^ z = ∏ i ∈ s, ((a i : ℝ) : ℂ) ^ z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha j (Finset.mem_cons_self j s))
        (Finset.prod_nonneg fun i hi => ha i (Finset.mem_cons_of_mem hi)),
      ih (fun i hi => ha i (Finset.mem_cons_of_mem hi))]

/-- The map sending `(t, u) : ℝ × logSpace K` to the point of `realSpace K` whose `w`-coordinate is
`t * gapsw80_t7_unitPart K u w`. -/
noncomputable def gapsw80_t8_placeParam (p : ℝ × logSpace K) : realSpace K :=
  fun w ↦ p.1 * gapsw80_t7_unitPart K p.2 w

/-- If `0 < p.1`, then every coordinate `gapsw80_t8_placeParam K p w` is positive. -/
theorem gapsw80_t8_placeParam_pos {p : ℝ × logSpace K} (hp : 0 < p.1) (w : InfinitePlace K) :
    0 < gapsw80_t8_placeParam K p w :=
  mul_pos hp (unitPart_pos K p.2 w)

/-- For `t > 0` and `u : logSpace K`, `∏ w, gapsw80_t8_placeParam K (t, u) w ^ w.mult = t ^ nK K`.
-/
theorem gapsw80_t8_prod_placeParam_pow_mult {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    ∏ w : InfinitePlace K, gapsw80_t8_placeParam K (t, u) w ^ w.mult = t ^ nK K := by
  have key : ∀ w, gapsw80_t8_placeParam K (t, u) w
      = gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u) w := fun w => by
    rw [gapsw80_t7_yParam_mkParam_factor K ht u w]; rfl
  simp_rw [key]
  exact (gapsw80_t5_prod_yParam_mkParam K _ u).trans (exp_half_log_pow_two_n K ht)

/-- The map `p ↦ gapsw80_t5_mkParam K p.1 p.2` from `ℝ × logSpace K` to `realSpace K` is measure
preserving for the volume measures. -/
theorem gapsw80_t8_mkParam_measurePreserving :
    MeasurePreserving (fun p : ℝ × logSpace K => gapsw80_t5_mkParam K p.1 p.2)
      volume volume := by

  have heq : (fun p : ℝ × logSpace K => gapsw80_t5_mkParam K p.1 p.2)
      = ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).symm
        ∘ Prod.map
          ⇑(MeasurableEquiv.piUnique (fun _ : {w : InfinitePlace K // w = w₀} => ℝ)).symm
          id := by
    funext p; funext w
    unfold gapsw80_t5_mkParam
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      MeasurableEquiv.piEquivPiSubtypeProd_symm_apply,
      MeasurableEquiv.piUnique_symm_apply]
    by_cases hw : w = w₀
    · subst hw; simp only [dite_eq_left]; rfl
    · simp only [dite_eq_right hw]
  rw [heq, Measure.volume_eq_prod ℝ (logSpace K)]
  refine (volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K => ℝ) (· = w₀)).symm.comp ?_
  have hp := (volume_preserving_piUnique (fun _ : {w : InfinitePlace K // w = w₀} => ℝ)).symm.prod
    (MeasurePreserving.id (volume : Measure (logSpace K)))
  convert hp
  rw [Measure.volume_eq_prod]
  congr!

/-- For `h : ℝ → ENNReal`,
`∫⁻ r, h r = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (2 * t)⁻¹ * h (Real.log t / 2)`. -/
theorem gapsw80_t8_lintegral_comp_halflog {h : ℝ → ENNReal} :
    ∫⁻ r, h r = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * t)⁻¹ * h (Real.log t / 2) := by
  have himg : (fun t : ℝ => Real.log t / 2) '' Set.Ioi (0:ℝ) = Set.univ :=
    Set.eq_univ_of_forall fun r => ⟨Real.exp (2 * r), Real.exp_pos _, by
      show Real.log (Real.exp (2 * r)) / 2 = r; rw [Real.log_exp]; ring⟩
  have hinj : Set.InjOn (fun t : ℝ => Real.log t / 2) (Set.Ioi 0) := fun t₁ h₁ t₂ h₂ heq => by
    have hlog : Real.log t₁ = Real.log t₂ := by linarith [heq]
    exact (Real.exp_log h₁).symm.trans (hlog ▸ Real.exp_log h₂)
  have hder : ∀ t ∈ Set.Ioi (0:ℝ), HasFDerivWithinAt (fun t => Real.log t / 2)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * t)⁻¹) (Set.Ioi 0) t := fun t ht => by
    have : HasDerivAt (fun t => Real.log t / 2) (2 * t)⁻¹ t := by
      rw [mul_inv, mul_comm, ← div_eq_mul_inv]
      exact (Real.hasDerivAt_log (ne_of_gt ht)).div_const 2
    exact this.hasFDerivAt.hasFDerivWithinAt
  conv_lhs => rw [← setLIntegral_univ, ← himg]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_Ioi hder hinj h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  congr 2
  simp_rw [ContinuousLinearMap.det, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
    abs_of_pos (inv_pos.mpr (mul_pos two_pos ht'))]

/-- For measurable `G : realSpace K → ENNReal`, `∫⁻ c, G c` equals the lower integral over
`Set.Ioi 0 ×ˢ Set.univ` of
`ENNReal.ofReal (2 * p.1)⁻¹ * G (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2)`. -/
theorem gapsw80_t8_setLIntegral_mkParam_halflog {G : realSpace K → ENNReal}
    (hG : Measurable G) :
    ∫⁻ c, G c
      = ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
          ENNReal.ofReal (2 * p.1)⁻¹ * G (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2) := by

  have hGm : Measurable (fun p : ℝ × logSpace K => G (gapsw80_t5_mkParam K p.1 p.2)) :=
    hG.comp (gapsw80_t8_mkParam_measurePreserving K).measurable
  have hGm' : Measurable (fun p : ℝ × logSpace K =>
      ENNReal.ofReal (2 * p.1)⁻¹ * G (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_fst).inv).mul
      (hGm.comp (((Real.measurable_log.comp measurable_fst).div_const 2).prodMk measurable_snd))
  have hh : Measurable (fun r : ℝ => ∫⁻ u : logSpace K, G (gapsw80_t5_mkParam K r u)) :=
    hGm.lintegral_prod_right'
  rw [← (gapsw80_t8_mkParam_measurePreserving K).lintegral_comp hG, Measure.volume_eq_prod,
    lintegral_prod _ hGm.aemeasurable, setLIntegral_prod _ hGm'.aemeasurable]
  dsimp only
  rw [gapsw80_t8_lintegral_comp_halflog]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [setLIntegral_univ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The image of `expMapBasis` on all of `realSpace K` is the set of `τ` with `0 < τ w` for every
place `w`. -/
theorem gapsw80_t8_expMapBasis_image_univ :
    expMapBasis '' (Set.univ : Set (realSpace K)) = {τ : realSpace K | ∀ w, 0 < τ w} := by
  ext τ
  refine ⟨fun ⟨c, _, hc⟩ w => hc ▸ expMapBasis_pos c w, fun hτ => ?_⟩

  exact ⟨expMapBasis.symm τ, Set.mem_univ _, expMapBasis.right_inv (Set.mem_univ_pi.mpr hτ)⟩

/-- The continuous linear map on `realSpace K` whose `w`-component is `h ↦ 2 * σ w * h w`, i.e. the
derivative at `σ` of coordinatewise squaring. -/
abbrev gapsw80_t8_fderiv_sq (σ : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * σ w)).comp (.proj w)

/-- The coordinatewise squaring map `σ' ↦ (w ↦ σ' w ^ 2)` on `realSpace K` has Fréchet derivative
`gapsw80_t8_fderiv_sq K σ` at `σ`. -/
theorem gapsw80_t8_hasFDerivAt_sq (σ : realSpace K) :
    HasFDerivAt (fun σ' : realSpace K => fun w => σ' w ^ 2) (gapsw80_t8_fderiv_sq K σ) σ := by
  simp only [hasFDerivAt_pi', ContinuousLinearMap.proj_pi]
  intro w
  have hd : HasDerivAt (fun x : ℝ => x ^ 2) (2 * σ w) (σ w) := by
    simpa using hasDerivAt_pow 2 (σ w)
  exact hd.hasFDerivAt.comp (f := fun σ' : realSpace K => σ' w) σ (hasFDerivAt_apply w σ)

open _root_.ContinuousLinearMap _root_.P2MW.S_NumberField_exists_completedDedekindZeta_package.ContinuousLinearMap in
/-- The absolute determinant of `gapsw80_t8_fderiv_sq K σ` equals
`2 ^ (nrRealPlaces K + nrComplexPlaces K) * ∏ w, |σ w|`. -/
theorem gapsw80_t8_abs_det_fderiv_sq (σ : realSpace K) :
    |(gapsw80_t8_fderiv_sq K σ).det|
      = 2 ^ (nrRealPlaces K + nrComplexPlaces K) * ∏ w : InfinitePlace K, |σ w| := by
  simp only [gapsw80_t8_fderiv_sq, ContinuousLinearMap.det, coe_pi]
  erw [LinearMap.det_pi]
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, smulRight_apply,
    one_apply_eq_self, one_smul, Finset.abs_prod, abs_mul, abs_pow, abs_two,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- For `g : realSpace K → ENNReal`, the lower integral of `g` over the positive orthant
equals `2 ^ (nrRealPlaces K + nrComplexPlaces K)` times the lower integral over the positive
orthant of `(∏ w, ENNReal.ofReal (σ w)) * g (fun w => σ w ^ 2)`. -/
theorem gapsw80_t8_setLIntegral_sq_pos {g : realSpace K → ENNReal} :
    ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w}, g τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K) *
        ∫⁻ σ in {σ : realSpace K | ∀ w, 0 < σ w},
          (∏ w : InfinitePlace K, ENNReal.ofReal (σ w)) * g (fun w => σ w ^ 2) := by
  set P : Set (realSpace K) := {σ | ∀ w, 0 < σ w}
  have hPmeas : MeasurableSet P := by
    rw [show P = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from Set.ext fun σ => by
      simp [P]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have himg : (fun σ : realSpace K => fun w => σ w ^ 2) '' P = P := by
    refine Set.ext fun τ => ⟨fun ⟨σ, hσ, hστ⟩ w => hστ ▸ pow_pos (hσ w) 2, fun hτ => ?_⟩
    exact ⟨fun w => Real.sqrt (τ w), fun w => Real.sqrt_pos.mpr (hτ w),
      funext fun w => Real.sq_sqrt (hτ w).le⟩
  have hinj : Set.InjOn (fun σ : realSpace K => fun w => σ w ^ 2) P :=
    fun σ₁ h₁ σ₂ h₂ heq => funext fun w =>
      (pow_left_inj₀ (h₁ w).le (h₂ w).le two_ne_zero).mp (congrFun heq w)
  conv_lhs => rw [show P = (fun σ : realSpace K => fun w => σ w ^ 2) '' P from himg.symm]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hPmeas
      (fun σ _ => (gapsw80_t8_hasFDerivAt_sq K σ).hasFDerivWithinAt) hinj g,
    ← lintegral_const_mul' _ _ (by finiteness)]
  refine setLIntegral_congr_fun hPmeas fun σ hσ => ?_
  rw [gapsw80_t8_abs_det_fderiv_sq, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
    ENNReal.ofReal_prod_of_nonneg fun w _ => abs_nonneg _,
    show (∏ w, ENNReal.ofReal |σ w|) = ∏ w, ENNReal.ofReal (σ w) from
      Finset.prod_congr rfl fun w _ => by rw [abs_of_pos (hσ w)],
    mul_assoc]

set_option maxHeartbeats 6400000 in
/-- For measurable `f : realSpace K → ENNReal`, the lower integral over `Set.Ioi 0 ×ˢ Set.univ` of
`ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)` equals
`ENNReal.ofReal ((2 ^ (nrRealPlaces K - 1) * nK K * regulator K)⁻¹)` times the lower integral over
the positive orthant of `(∏ over complex places w, ENNReal.ofReal (τ w)) * f τ`. -/
theorem gapsw80_t8_setLIntegral_placeParam {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ *
        ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ := by

  have hmeB : Measurable (fun c : realSpace K => expMapBasis c) :=
    (continuous_expMapBasis K).measurable
  have hmsq : Measurable (fun σ : realSpace K => fun w => σ w ^ 2) :=
    Measurable.of_eval fun w => (measurable_pi_apply w).pow_const 2

  set H : realSpace K → ENNReal := fun c =>
    ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) with hHdef
  have hH : Measurable H :=
    (ENNReal.measurable_ofReal.comp
        ((Real.measurable_exp.comp (measurable_pi_apply w₀)).pow_const _)).mul (hf.comp (hmsq.comp hmeB))

  have stepL : ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = (2 : ENNReal) * ∫⁻ c, H c := by
    rw [gapsw80_t8_setLIntegral_mkParam_halflog K hH,
      ← lintegral_const_mul' _ _ (by finiteness)]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
    have ht : (0:ℝ) < p.1 := hp.1
    have hcw : gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2 w₀ = Real.log p.1 / 2 := mkParam_w₀ K _ _
    have hplace : (fun w => (expMapBasis (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2) w) ^ 2)
        = gapsw80_t8_placeParam K p := funext fun w =>
      gapsw80_t7_yParam_mkParam_factor K ht p.2 w
    have hn : 1 ≤ nK K := Module.finrank_pos
    simp only [hHdef, hcw, hplace, exp_half_log_pow_two_n K ht]
    rw [show (2:ENNReal) = ENNReal.ofReal (2:ℝ) from by simp, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity),
      show (2:ℝ) * (2 * p.1)⁻¹ * p.1 ^ nK K = p.1 ^ (nK K - 1) by
        rw [show p.1 ^ nK K = p.1 * p.1 ^ (nK K - 1) by
          conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']]
        field_simp]

  have stepR : ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2 : ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
        * ∫⁻ c, H c := by
    have hf' : Measurable (fun τ : realSpace K =>
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ) :=
      (Finset.measurable_prod _ fun w _ =>
        ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)).mul hf
    have hσ : Measurable (fun σ : realSpace K =>
        (∏ w, ENNReal.ofReal (σ w)) *
          ((∏ w : {w // IsComplex w}, ENNReal.ofReal (σ w.1 ^ 2)) * f (fun w => σ w ^ 2))) :=
      (Finset.measurable_prod _ fun w _ =>
          ENNReal.measurable_ofReal.comp (measurable_pi_apply w)).mul (hf'.comp hmsq)
    rw [gapsw80_t8_setLIntegral_sq_pos K, ← gapsw80_t8_expMapBasis_image_univ K,
      setLIntegral_expMapBasis_image MeasurableSet.univ hσ, setLIntegral_univ, ← mul_assoc]
    congr 1
    refine lintegral_congr fun c => ?_

    have heBpos : ∀ w, (0:ℝ) < expMapBasis c w := expMapBasis_pos c
    have hPc0 : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr (heBpos w.1)).ne'
    have hPcT : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ ⊤ :=
      (ENNReal.prod_lt_top fun w _ => ENNReal.ofReal_lt_top).ne

    have hPaPc : (∏ w, ENNReal.ofReal (expMapBasis c w))
          * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
        = ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w).le),
        ← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w.1).le),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (heBpos w).le),
        prod_eq_prod_mul_prod (expMapBasis c), mul_assoc, ← sq,
        ← prod_expMapBasis_pow c, prod_eq_prod_mul_prod (fun w => expMapBasis c w ^ w.mult)]
      congr 2
      · exact Finset.prod_congr rfl fun w _ => by rw [mult_isReal w, pow_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun w _ => by rw [mult_isComplex w]

    simp only [hHdef]
    rw [show (c w₀) * (Module.finrank ℚ K : ℝ) = (nK K : ℝ) * c w₀ from mul_comm _ _,
      Real.exp_nat_mul,
      show (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1 ^ 2))
          = (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) from by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun w _ => by rw [sq, ENNReal.ofReal_mul (heBpos w.1).le],
      show Real.exp (c w₀) ^ (2 * nK K)
          = Real.exp (c w₀) ^ nK K * Real.exp (c w₀) ^ nK K from by rw [two_mul, pow_add],
      ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) _)]

    rw [← mul_assoc _ _ (f _), ← mul_assoc (∏ w, ENNReal.ofReal (expMapBasis c w)),
      ← mul_assoc, ← mul_assoc]
    congr 1

    calc ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
            * ((∏ w, ENNReal.ofReal (expMapBasis c w))
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
        = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * ((∏ w, ENNReal.ofReal (expMapBasis c w))
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
            * ((∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
              * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))) := by ring
      _ = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
            * ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
          rw [hPaPc, ENNReal.inv_mul_cancel hPc0 hPcT, mul_one]

  rw [stepL, stepR, ← mul_assoc]
  congr 1
  have hR : (0:ℝ) < regulator K := regulator_pos K
  have hn : 0 < nK K := Module.finrank_pos
  have hX : (0:ℝ) < (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K :=
    mul_pos (mul_pos (zpow_pos two_pos _) (Nat.cast_pos.mpr hn)) hR
  have h2X : (2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)
      = (2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K := by
    have key : (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * 2 = (2:ℝ) ^ nrRealPlaces K := by
      rw [← zpow_add_one₀ (two_ne_zero (α := ℝ)), sub_add_cancel, zpow_natCast]
    rw [← key]; ring
  have hB : (2:ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
      = ENNReal.ofReal ((2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast,
      show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
      pow_add, mul_assoc ((2:ENNReal) ^ nrRealPlaces K),
      show (2:ENNReal) ^ nrComplexPlaces K * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K
            * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
          = (nK K : ENNReal) * ENNReal.ofReal (regulator K)
            * ((2:ENNReal) * (2:ENNReal)⁻¹) ^ nrComplexPlaces K from by rw [mul_pow]; ring,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, mul_one, ← mul_assoc]
  rw [hB, ← h2X, ← ENNReal.ofReal_mul (inv_nonneg.mpr hX.le),
    show ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)⁻¹
          * ((2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K))
        = (2:ℝ) from by field_simp,
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp]

/-- The map `gapsw80_t8_placeParam K` from `ℝ × logSpace K` to `realSpace K` is continuous. -/
theorem gapsw80_t8_continuous_placeParam :
    Continuous (gapsw80_t8_placeParam K) :=
  continuous_pi fun w => continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)

/-- The pushforward under `gapsw80_t8_placeParam K` of the measure on `Set.Ioi 0 ×ˢ Set.univ` with
density `p.1 ^ (nK K - 1)` equals `(2 ^ (nrRealPlaces K - 1) * nK K * regulator K)⁻¹` times the
measure on the positive orthant with density `∏ over complex places w, τ w`. -/
theorem gapsw80_t8_placeParam_measure_eq :
    Measure.map (gapsw80_t8_placeParam K)
        ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
          (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹
        • (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}).withDensity
            (fun τ => ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) := by
  have hφ : Measurable (gapsw80_t8_placeParam K) := (gapsw80_t8_continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hgL : Measurable fun p => f (gapsw80_t8_placeParam K p) := hf.comp hφ
  rw [lintegral_map hf hφ, lintegral_withDensity_eq_lintegral_mul _ hdL hgL,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hdR hf, smul_eq_mul]
  simp only [Pi.mul_apply]
  exact gapsw80_t8_setLIntegral_placeParam K hf

/-- For `G` a.e. strongly measurable on the positive orthant, the integral over
`Set.Ioi 0 ×ˢ Set.univ` of `p.1 ^ (nK K - 1) * G (gapsw80_t8_placeParam K p)` equals
`(2 ^ (nrRealPlaces K - 1) * nK K * regulator K)⁻¹` times the integral over the positive orthant of
`(∏ over complex places w, τ w) * G τ`. -/
theorem gapsw80_t8_setIntegral_placeParam {G : realSpace K → ℂ}
    (hG : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w})) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p)
      = (((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ) *
        ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ := by
  have hC : (0:ℝ) ≤ ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg
      (mul_nonneg (zpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (regulator_pos K).le)
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} := by
    rw [show {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from
      Set.ext fun τ => by simp]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hφ : Measurable (gapsw80_t8_placeParam K) := (gapsw80_t8_continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)

  have hGmap : AEStronglyMeasurable G (Measure.map (gapsw80_t8_placeParam K)
      ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))) := by
    rw [gapsw80_t8_placeParam_measure_eq]
    exact .mono_ac
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)) hG

  have key := (integral_map hφ.aemeasurable hGmap).symm
  rw [gapsw80_t8_placeParam_measure_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hdR
      (Filter.Eventually.of_forall fun _ => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hdL
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal hC, Complex.real_smul] at key

  have stepL : (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p))
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        (ENNReal.ofReal (p.1 ^ (nK K - 1))).toReal • G (gapsw80_t8_placeParam K p) :=
    setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => by
      rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hp.1) _), Complex.real_smul]
  have stepR : (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)).toReal • G τ)
      = ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ :=
    setIntegral_congr_fun hBmeas fun τ hτ => by
      rw [ENNReal.toReal_prod,
        show (∏ w : {w : InfinitePlace K // IsComplex w}, (ENNReal.ofReal (τ w.1)).toReal)
            = ∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 from
          Finset.prod_congr rfl fun w _ => ENNReal.toReal_ofReal (le_of_lt (hτ w.1)),
        Complex.real_smul]
  rw [stepL, key, stepR, Complex.ofReal_inv]

/-- For `x : mixedSpace K` with all `normAtPlace w x ≠ 0`, the product over `w` of
$(\pi \|x\|_w^2)^{-m_w s/2} \Gamma(m_w s/2)$ equals
$\Gamma_\mathbb{R}(s)^{r_1} (\Gamma_\mathbb{C}(s) 2^{s-1})^{r_2} \prod_w \|x\|_w^{-m_w s}$, where
`‖x‖_w = normAtPlace w x` and `m_w = w.mult`. -/
theorem gapsw80_t8_prod_gammaFactor_eq {s : ℂ} {x : mixedSpace K}
    (hx : ∀ w, normAtPlace w x ≠ 0) :
    ∏ w : InfinitePlace K,
        (((π * normAtPlace w x ^ 2 : ℝ) : ℂ) ^ (-(w.mult * s / 2)) * Complex.Gamma (w.mult * s / 2))
      = Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ) ^ (s - 1)) ^ nrComplexPlaces K
        * ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s)) := by
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    (normAtPlace_nonneg w x).lt_of_ne (Ne.symm (hx w))

  have hreal : ∀ w : {w : InfinitePlace K // IsReal w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = Gammaℝ s * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isReal w, Nat.cast_one, one_mul]
    rw [gapsw80_t8_gammaFactor_isReal (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      gapsw80_t8_ofReal_pow_cpow (hpos w.1).le 2 (-(s/2)),
      show ((2:ℕ):ℂ) * -(s/2) = -s from by push_cast; ring]

  have hcplx : ∀ w : {w : InfinitePlace K // IsComplex w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = (Gammaℂ s * (2:ℂ)^(s-1)) * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isComplex w, Nat.cast_ofNat]
    rw [show ((2:ℂ) * s / 2) = s from by ring,
      gapsw80_t8_gammaFactor_isComplex (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      gapsw80_t8_ofReal_pow_cpow (hpos w.1).le 2 (-s),
      show ((2:ℕ):ℂ) * -s = -((2:ℂ)*s) from by push_cast; ring, mul_assoc]
  rw [prod_eq_prod_mul_prod (K := K), prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((normAtPlace w x:ℝ):ℂ) ^ (-((w.mult:ℂ) * s)))]
  simp only [hreal, hcplx, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    nrRealPlaces, nrComplexPlaces]
  ring

/-- For `x : mixedSpace K` and `s : ℂ`,
`∏ w, (normAtPlace w x) ^ (-(w.mult * s)) = (mixedEmbedding.norm x) ^ (-s)` with complex powers. -/
theorem gapsw80_t8_prod_normAtPlace_cpow {x : mixedSpace K} (s : ℂ) :
    ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s))
      = ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-s) := by
  rw [mixedEmbedding.norm_apply,
    gapsw80_t8_prod_ofReal_cpow Finset.univ
      (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) (-s)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_pow,
    gapsw80_t8_ofReal_pow_cpow (normAtPlace_nonneg w x) w.mult (-s)]
  congr 1; ring

/-- The type of nonzero elements of `K` lying in the fractional ideal `I`; the unit group `(𝓞 K)ˣ`
acts on it by multiplication. -/
abbrev gapsw80_t8_nonzeroIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type :=
  {a : K // a ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ∧ a ≠ 0}

/-- The unit group `(𝓞 K)ˣ` acts on the nonzero elements of `I` by multiplication. -/
scoped instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MulAction (𝓞 K)ˣ (gapsw80_t8_nonzeroIdeal K I) where
  smul u x := ⟨(u : 𝓞 K) • (x : K),
    Submodule.smul_mem _ _ x.2.1,
    smul_ne_zero (by exact_mod_cast u.ne_zero) x.2.2⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul u v x := Subtype.ext (mul_smul _ _ _)

/-- The representative in `K` of an orbit of `(𝓞 K)ˣ` on the nonzero elements of `I`, given by the
element chosen by `Quotient.out`. -/
noncomputable def gapsw80_t8_orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) : K :=
  (x.out : K)

/-- The partial Dedekind zeta function of the ideal class `C`: the sum over nonzero integral ideals
`J` with `ClassGroup.mk0 J = C` of `(Ideal.absNorm J) ^ (-s)`. -/
noncomputable def gapsw80_t8_partialDedekindZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ∑' J : {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = C},
    ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)

/-- For nonzero `x` in `I`, the fractional ideal `(x) * I⁻¹` is contained in `1`. -/
theorem gapsw80_t8_spanSingleton_mul_inv_le_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * (↑I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * ↑I⁻¹
      ≤ (↑I : FractionalIdeal (𝓞 K)⁰ K) * ↑I⁻¹ :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr x.2.1) _
    _ = 1 := I.mul_inv

/-- The nonzero integral ideal `J` of `𝓞 K` with `J = (x) * I⁻¹` as fractional ideals, for `x` a
nonzero element of `I`. -/
noncomputable def gapsw80_t8_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) : (Ideal (𝓞 K))⁰ :=
  ⟨(FractionalIdeal.le_one_iff_exists_coeIdeal.mp
      (gapsw80_t8_spanSingleton_mul_inv_le_one K I x)).choose,
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h ↦
      (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.2.2) (Units.ne_zero I⁻¹))
        ((FractionalIdeal.le_one_iff_exists_coeIdeal.mp
            (gapsw80_t8_spanSingleton_mul_inv_le_one K I x)).choose_spec.symm.trans
          (by rw [show (0 : Ideal (𝓞 K)) = ⊥ from rfl] at h
              rw [h, FractionalIdeal.coeIdeal_bot]))⟩

/-- For nonzero `x` in `I`, the integral ideal `gapsw80_t8_orbitToIdeal K I x`, viewed as a
fractional ideal, equals `FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I⁻¹`. -/
theorem gapsw80_t8_coe_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    ((gapsw80_t8_orbitToIdeal K I x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) * ↑I⁻¹ :=
  (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (gapsw80_t8_spanSingleton_mul_inv_le_one K I x)).choose_spec

/-- For nonzero `x` in `I`, the ideal class of `gapsw80_t8_orbitToIdeal K I x` is
`(ClassGroup.mk K I)⁻¹`. -/
theorem gapsw80_t8_mk0_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    ClassGroup.mk0 (gapsw80_t8_orbitToIdeal K I x) = (ClassGroup.mk K I)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ClassGroup.mk_mk0 K, ← map_mul, ClassGroup.mk_eq_one_iff]
  refine ⟨⟨(x : K), ?_⟩⟩
  rw [show ((FractionalIdeal.mk0 K (gapsw80_t8_orbitToIdeal K I x) * I :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) from by
    rw [Units.val_mul, FractionalIdeal.coe_mk0, gapsw80_t8_coe_orbitToIdeal,
      mul_assoc, I.inv_mul, mul_one],
    FractionalIdeal.coe_spanSingleton]

/-- For nonzero `x` in `I`, the product of `Ideal.absNorm (gapsw80_t8_orbitToIdeal K I x)` and
`FractionalIdeal.absNorm I` is `|Algebra.norm ℚ x|`. -/
theorem gapsw80_t8_absNorm_orbitToIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : gapsw80_t8_nonzeroIdeal K I) :
    (Ideal.absNorm (gapsw80_t8_orbitToIdeal K I x : Ideal (𝓞 K)) : ℚ)
      * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)
      = |Algebra.norm ℚ (x : K)| := by
  have hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun h ↦ (Units.ne_zero I) (FractionalIdeal.absNorm_eq_zero_iff.mp h)
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K), gapsw80_t8_coe_orbitToIdeal, map_mul,
    FractionalIdeal.absNorm_span_singleton, Units.val_inv_eq_inv_val, map_inv₀,
    inv_mul_cancel_right₀ hI]

/-- For a unit `u` of `𝓞 K` and nonzero `x` in `I`,
`gapsw80_t8_orbitToIdeal K I (u • x) = gapsw80_t8_orbitToIdeal K I x`. -/
theorem gapsw80_t8_orbitToIdeal_smul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : (𝓞 K)ˣ) (x : gapsw80_t8_nonzeroIdeal K I) :
    gapsw80_t8_orbitToIdeal K I (u • x) = gapsw80_t8_orbitToIdeal K I x := by
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u • x : gapsw80_t8_nonzeroIdeal K I) : K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
    show FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) • (x : K)) = _
    rw [Algebra.smul_def, map_mul,
      ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top, one_mul]
  exact Subtype.ext <| FractionalIdeal.coeIdeal_injective (K := K) <|
    show ((gapsw80_t8_orbitToIdeal K I (u • x) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((gapsw80_t8_orbitToIdeal K I x : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) from by
      rw [gapsw80_t8_coe_orbitToIdeal, gapsw80_t8_coe_orbitToIdeal, hspan]

/-- A bijection between the `(𝓞 K)ˣ`-orbits of nonzero elements of `I` and the nonzero integral
ideals `J` with `ClassGroup.mk0 J = (ClassGroup.mk K I)⁻¹`. -/
noncomputable def gapsw80_t8_orbitQuotEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)) ≃
      {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = (ClassGroup.mk K I)⁻¹} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨gapsw80_t8_orbitToIdeal K I x, gapsw80_t8_mk0_orbitToIdeal K I x⟩)
      (fun a b h ↦ Subtype.ext <| by
        obtain ⟨u, rfl⟩ := MulAction.orbitRel_apply.mp h
        exact gapsw80_t8_orbitToIdeal_smul K I u b))
    ⟨fun q₁ q₂ h ↦ by
      induction q₁ using Quotient.inductionOn with | _ a => ?_
      induction q₂ using Quotient.inductionOn with | _ b => ?_
      refine Quotient.sound (MulAction.orbitRel_apply.mpr ?_)
      have hab : gapsw80_t8_orbitToIdeal K I a = gapsw80_t8_orbitToIdeal K I b :=
        congrArg Subtype.val h
      have hc : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) := by
        have := congrArg
          (fun J : (Ideal (𝓞 K))⁰ ↦ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I) hab
        simpa only [gapsw80_t8_coe_orbitToIdeal, mul_assoc, I.inv_mul, mul_one] using this
      obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hc
      refine ⟨u⁻¹, Subtype.ext (show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (b : K) = (a : K) from ?_)⟩
      have hu' : ((u : (𝓞 K)ˣ) : 𝓞 K) • (a : K) = (b : K) := hu
      rw [← hu', ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul],
    fun ⟨J, hJ⟩ ↦ by
      have hJI : ClassGroup.mk K (FractionalIdeal.mk0 K J * I) = 1 := by
        rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
      obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).mp
        (ClassGroup.mk_eq_one_iff.mp hJI)
      have hx0 : x ≠ 0 := fun h0 ↦ Units.ne_zero _
        (hx.trans (by rw [h0, map_zero]))
      replace hx : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
        rw [← hx, Units.val_mul, FractionalIdeal.coe_mk0]
      have hxI : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
        FractionalIdeal.spanSingleton_le_iff_mem.mp <|
          calc FractionalIdeal.spanSingleton (𝓞 K)⁰ x
              = ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * ↑I := hx.symm
            _ ≤ 1 * ↑I := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
            _ = ↑I := one_mul _
      refine ⟨Quotient.mk _ ⟨x, hxI, hx0⟩, Subtype.ext (Subtype.ext
        (FractionalIdeal.coeIdeal_injective (K := K)
          (show ((gapsw80_t8_orbitToIdeal K I ⟨x, hxI, hx0⟩ : Ideal (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K) = ↑↑J from ?_)))⟩
      rw [gapsw80_t8_coe_orbitToIdeal, ← hx, mul_assoc, I.mul_inv, mul_one]⟩

/-- The sum over unit-orbits of nonzero elements of `I` of
`|Algebra.norm ℚ x|^(-s)` equals `(FractionalIdeal.absNorm I) ^ (-s)` times the partial Dedekind
zeta function of the class `(ClassGroup.mk K I)⁻¹` at `s`. -/
theorem gapsw80_t8_tsum_orbit_normInv_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} :
    (∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K I x) : ℚ)| : ℝ) : ℂ) ^ (-s))
      = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by
  rw [gapsw80_t8_partialDedekindZeta, ← (gapsw80_t8_orbitQuotEquiv K I).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun q ↦ ?_
  unfold gapsw80_t8_orbitRepr
  have hout : ((gapsw80_t8_orbitQuotEquiv K I q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = gapsw80_t8_orbitToIdeal K I q.out := by
    conv_lhs => rw [← q.out_eq]
    rfl
  have hM : (0:ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have hN : (0:ℝ) ≤ (Ideal.absNorm (gapsw80_t8_orbitToIdeal K I q.out : Ideal (𝓞 K)) : ℝ) :=
    Nat.cast_nonneg _
  rw [hout, ← Complex.ofReal_natCast (Ideal.absNorm _),
    ← Complex.mul_cpow_ofReal_nonneg hM hN]
  congr 2
  exact_mod_cast ((gapsw80_t8_absNorm_orbitToIdeal K I q.out).symm.trans (mul_comm _ _))

/-- For `s : ℂ`, $\operatorname{covol}(I)^{-s} |d_K|^{s/2} = N(I)^{-s} 2^{r_2 s}$, where `covol(I)`
is the covolume of the ideal lattice of `I`, `N(I)` its absolute norm and `r₂ = nrComplexPlaces K`.
-/
theorem gapsw80_t8_covol_discr_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
      * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
    = ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s)
      * ((2:ℝ) : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
  have hN : (0:ℝ) ≤ (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2i : (0:ℝ) ≤ (2:ℝ)⁻¹ := by norm_num
  have h2r : (0:ℝ) ≤ ((2:ℝ)⁻¹) ^ nrComplexPlaces K := pow_nonneg h2i _
  have hD : (0:ℝ) ≤ |(discr K : ℝ)| := abs_nonneg _
  have hDne : ((|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, abs_eq_zero, Int.cast_eq_zero]
    exact discr_ne_zero K
  have harg2 : Complex.arg ((2:ℝ):ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.pi_ne_zero.symm

  rw [mixedEmbedding.covolume_idealLattice, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg hN h2r) (Real.sqrt_nonneg _),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hN h2r,
    Complex.ofReal_pow, gapsw80_t8_ofReal_pow_cpow h2i (nrComplexPlaces K) (-s),
    gapsw80_t8_ofReal_sqrt_cpow hD (-s),
    show (((2:ℝ)⁻¹ : ℝ) : ℂ) = (((2:ℝ):ℂ))⁻¹ from Complex.ofReal_inv 2,
    Complex.inv_cpow _ _ harg2, ← Complex.cpow_neg,
    show -((nrComplexPlaces K : ℂ) * -s) = (nrComplexPlaces K : ℂ) * s from by ring,
    mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hDne,
    show -s / 2 + s / 2 = (0:ℂ) from by ring, Complex.cpow_zero, mul_one]

/-- The bijection between the nonzero elements of `I` and the nonzero vectors of the lattice
`mixedEmbedding.idealLattice K I`, given by the mixed embedding. -/
noncomputable def gapsw80_t8_nonzeroIdealLatticeEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    gapsw80_t8_nonzeroIdeal K I
      ≃ {x : mixedEmbedding.idealLattice K I // (x : mixedSpace K) ≠ 0} where
  toFun a := ⟨⟨mixedEmbedding K (a : K),
      (mem_idealLattice K I).mpr ⟨(a : K), a.2.1, rfl⟩⟩,
    fun h => a.2.2 <| (mixedEmbedding_injective K) (h.trans (_root_.map_zero _).symm)⟩
  invFun x := ⟨((mem_idealLattice K I).mp x.1.2).choose,
    ((mem_idealLattice K I).mp x.1.2).choose_spec.1,
    fun ha => x.2 (by
      have := ((mem_idealLattice K I).mp x.1.2).choose_spec.2
      rw [ha, _root_.map_zero] at this
      exact this.symm)⟩
  left_inv a := Subtype.ext <| mixedEmbedding_injective K
    ((mem_idealLattice K I).mp ((mem_idealLattice K I).mpr ⟨(a : K), a.2.1, rfl⟩)).choose_spec.2
  right_inv x := Subtype.ext <| Subtype.ext ((mem_idealLattice K I).mp x.1.2).choose_spec.2

/-- The bijection between nonzero integer vectors `v : Fin (nK K) → ℤ` and nonzero vectors of
`mixedEmbedding.idealLattice K I`, given by `zEquiv K I`. -/
noncomputable def gapsw80_t8_zEquivNonzero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {v : Fin (nK K) → ℤ // v ≠ 0}
      ≃ {x : mixedEmbedding.idealLattice K I // (x : mixedSpace K) ≠ 0} where
  toFun v := ⟨zEquiv K I v, fun h => v.2 (by
    have : (zEquiv K I v : mixedEmbedding.idealLattice K I) = 0 := Subtype.ext h
    simpa using (zEquiv K I).injective (this.trans (_root_.map_zero _).symm))⟩
  invFun x := ⟨(zEquiv K I).symm x,
    fun h => x.2 (by rw [← (zEquiv K I).apply_symm_apply x.1, h, _root_.map_zero]; rfl)⟩
  left_inv v := Subtype.ext ((zEquiv K I).symm_apply_apply v)
  right_inv x := Subtype.ext ((zEquiv K I).apply_symm_apply x)

/-- For `y` with `0 < y w` at every place `w`, the family
`v ↦ cexp (-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)))` over
`v : Fin (nK K) → ℤ` is summable. -/
theorem gapsw80_t8_summable_thetaTerm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun v : Fin (nK K) → ℤ =>
      cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I

  obtain ⟨w₁, -, hw₁⟩ := Finset.exists_min_image
    (Finset.univ : Finset (InfinitePlace K)) y Finset.univ_nonempty
  set c := y w₁ with hc_def
  have hc : 0 < c := hy w₁
  have hcle : ∀ w, c ≤ y w := fun w => hw₁ w (Finset.mem_univ w)
  refine Summable.of_norm ?_
  refine (gapsw80_t7_summable_dom_gaussian K (mul_pos hc hlam)).of_nonneg_of_le
    (fun v => norm_nonneg _) (fun v => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hcle v) Real.pi_nonneg

/-- For `y` with `0 < y w` at every place `w`, `gapsw80_t4_multiIdealTheta K I y - 1` equals the
sum over nonzero `a` in `I` of `cexp (-(π * ∑ w, y w * (w a) ^ 2))`. -/
theorem gapsw80_t8_multiIdealTheta_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' a : gapsw80_t8_nonzeroIdeal K I,
          cexp ((-(π * ∑ w : InfinitePlace K, y w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by

  set f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) with hf_def
  have hfsum : Summable f := gapsw80_t8_summable_thetaTerm K I hy
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hTheta : gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' v : {v : Fin (nK K) → ℤ // v ≠ 0}, f v := by
    have heq : gapsw80_t4_multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
    refine Eq.symm ((tsum_subtype {v : Fin (nK K) → ℤ | v ≠ 0} f).trans ?_)
    exact tsum_congr fun v => by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, ne_eq, ite_not]
  rw [hTheta]

  rw [← ((gapsw80_t8_zEquivNonzero K I).trans
    (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm).tsum_eq]
  refine tsum_congr fun a => ?_

  have hcoe : ((zEquiv K I) (a : Fin (nK K) → ℤ) : mixedSpace K)
      = mixedEmbedding K
          ((((gapsw80_t8_zEquivNonzero K I).trans
              (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm) a : gapsw80_t8_nonzeroIdeal K I) : K) := by
    have hch := ((mem_idealLattice K I).mp
      ((gapsw80_t8_zEquivNonzero K I) a).1.2).choose_spec.2
    exact hch.symm
  have hsum : (zcastR (a : Fin (nK K) → ℤ) ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR (a : Fin (nK K) → ℤ))
      = ∑ w, y w * (w ((((gapsw80_t8_zEquivNonzero K I).trans
          (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm) a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 :=
    (gapsw80_t4_quadForm_scaledGram K I y a.1).trans
      (Finset.sum_congr rfl fun w _ => by rw [hcoe, normAtPlace_apply])
  simp only [hf_def, hsum]

/-- For `y` with `0 < y w` at every place `w`, the family
`a ↦ Real.exp (-(π * ∑ w, y w * (w a) ^ 2))` over nonzero `a` in `I` is summable. -/
theorem gapsw80_t8_summable_rexpQ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : gapsw80_t8_nonzeroIdeal K I =>
      Real.exp (-(π * ∑ w, y w * (w (a : K)) ^ 2)) := by
  have h : Summable fun a : gapsw80_t8_nonzeroIdeal K I =>
      cexp ((-(π * ∑ w, y w * (w (a : K)) ^ 2) : ℝ) : ℂ) :=
    (Equiv.summable_iff ((gapsw80_t8_zEquivNonzero K I).trans
        (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm)).mp
      (((gapsw80_t8_summable_thetaTerm K I hy).subtype {v | v ≠ 0}).congr fun a => by
        simp only [Function.comp_apply]
        have hcoe : ((zEquiv K I) a.1 : mixedSpace K)
            = mixedEmbedding K
                ((((gapsw80_t8_zEquivNonzero K I).trans
                    (gapsw80_t8_nonzeroIdealLatticeEquiv K I).symm) a :
                  gapsw80_t8_nonzeroIdeal K I) : K) :=
          (((mem_idealLattice K I).mp
            ((gapsw80_t8_zEquivNonzero K I) a).1.2).choose_spec.2).symm
        congr 4
        exact (gapsw80_t4_quadForm_scaledGram K I y a.1).trans
          (Finset.sum_congr rfl fun w _ => by rw [hcoe, normAtPlace_apply]))
  exact h.norm.congr fun a => by rw [Complex.norm_exp, Complex.ofReal_re]

/-- For `t > 0`, `gapsw80_t5_heckeKernel K I t - 1` equals the integral over `gapsw80_t7_unitBox K`
of `gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1`. -/
theorem gapsw80_t8_heckeKernel_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t5_heckeKernel K I t - 1
      = ∫ u in gapsw80_t7_unitBox K,
          (gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1) ∂volume := by
  have hvol : volume (gapsw80_t7_unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hint1 : IntegrableOn
      (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)))
      (gapsw80_t7_unitBox K) volume := by
    have hcont : Continuous
        (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u))) := by
      have h := continuous_genericKernel_integrand K I (Real.log t / 2) 1 (fun _ => one_pos)
      simp only [one_mul] at h
      exact h.congr fun u => by
        congr 1; funext w; exact gapsw80_t7_yParam_mkParam_factor K ht u w
    have hcompact : IsCompact
        (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hcont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set
      (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  rw [integral_sub hint1 hint2, setIntegral_const]
  have hvol' : volume.real (gapsw80_t7_unitBox K) = 1 := by
    rw [measureReal_def, hvol, ENNReal.toReal_one]
  rw [hvol', one_smul]
  congr 1
  unfold gapsw80_t5_heckeKernel
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w; rw [gapsw80_t7_yParam_mkParam_factor K ht]; rfl

/-- For `t > 0`, `u ↦ gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1` is
integrable on `gapsw80_t7_unitBox K`. -/
theorem gapsw80_t8_integrableOn_theta_sub_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1)
      (gapsw80_t7_unitBox K) volume := by
  have hcont : Continuous
      (fun u => gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u))) := by
    have h := continuous_genericKernel_integrand K I (Real.log t / 2) 1 (fun _ => one_pos)
    simp only [one_mul] at h
    exact h.congr fun u => by
      congr 1; funext w; exact gapsw80_t7_yParam_mkParam_factor K ht u w
  have hcompact : IsCompact
      (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact (((hcont.sub continuous_const).locallyIntegrable.integrableOn_isCompact hcompact).mono_set
    (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self))

/-- For `t > 0`, adding the `i`-th basis vector to `u` multiplies
`gapsw80_t8_placeParam K (t, u) w` by `gapsw80_t5_unitSqScale K η w`, where `η` is the fundamental
unit indexed by `i`. -/
theorem gapsw80_t8_placeParam_add_single {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (w : InfinitePlace K) :
    gapsw80_t8_placeParam K (t, u + Pi.single i 1) w
      = gapsw80_t8_placeParam K (t, u) w
        * gapsw80_t5_unitSqScale K (fundSystem K (equivFinRank.symm i)) w := by
  have key : ∀ v, gapsw80_t8_placeParam K (t, v) w
      = gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) v) w := fun v => by
    rw [gapsw80_t7_yParam_mkParam_factor K ht v w]; rfl
  rw [key, key, mkParam_add_single, gapsw80_t5_yParam_add_single K i.2, Pi.mul_apply, mul_comm]

/-- For weights `c`, a parameter `p` and a unit `η`, the weighted quadratic form
`∑ w, c w * gapsw80_t8_placeParam K p w * (w (η • a))^2` equals
`∑ w, c w * gapsw80_t8_placeParam K p w * gapsw80_t5_unitSqScale K η w * (w a)^2`. -/
theorem gapsw80_t8_quadForm_unit_smul_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (η : (𝓞 K)ˣ) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K p w * (w ((η • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K p w * gapsw80_t5_unitSqScale K η w * (w (a : K)) ^ 2 := by
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcoe : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
  rw [hcoe, Algebra.smul_def, map_mul, mul_pow, gapsw80_t5_unitSqScale,
    show ((algebraMap (𝓞 K) K) (η : 𝓞 K) : K) = ((η : 𝓞 K) : K) from rfl]
  ring

/-- For weights `c`, `0 < t`, `u` in the log space and a coordinate index `i`, translating `u` by
the `i`-th basis vector of the log space gives the same weighted quadratic form at `a` as the form
at parameter `(t, u)` evaluated at `a` multiplied by the corresponding fundamental unit
(`fundSystem K (equivFinRank.symm i)`). -/
theorem gapsw80_t8_quadForm_shift_single_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K (t, u + Pi.single i 1) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((fundSystem K (equivFinRank.symm i)) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul_c]
  exact Finset.sum_congr rfl fun w _ => by rw [gapsw80_t8_placeParam_add_single K ht]; ring

/-- For weights `c`, a parameter `p` and a torsion unit `ζ`, the weighted quadratic form
`∑ w, c w * gapsw80_t8_placeParam K p w * (w a)^2` takes the same value at `ζ • a` as at `a`. -/
theorem gapsw80_t8_quadForm_torsion_invariant_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (ζ : torsion K) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K p w
          * (w (((ζ : (𝓞 K)ˣ) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul_c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gapsw80_t5_unitSqScale, (mem_torsion K).mp ζ.2 w, one_pow, mul_one]

/-- For `p : ℝ × logSpace K`, a root of unity `ζ` in `torsion K` and nonzero `a` in `I`,
$\sum_w y_w \, w(\zeta a)^2 = \sum_w y_w \, w(a)^2$, where `y = gapsw80_t8_placeParam K p`. -/
theorem gapsw80_t8_quadForm_torsion_invariant (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℝ × logSpace K) (ζ : torsion K) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        gapsw80_t8_placeParam K p w * (w (((ζ : (𝓞 K)ˣ) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2 := by
  simpa only [Pi.one_apply, one_mul] using gapsw80_t8_quadForm_torsion_invariant_c K I 1 p ζ a

/-- The bijection from `torsion K × (Fin (rank K) → ℤ)` to `(𝓞 K)ˣ` sending `(ζ, m)` to
`ζ * ∏ i, fundSystem K i ^ m i`. -/
noncomputable def gapsw80_t8_dutEquiv : torsion K × (Fin (rank K) → ℤ) ≃ (𝓞 K)ˣ :=
  Equiv.ofBijective (fun p => (p.1 : (𝓞 K)ˣ) * ∏ i, fundSystem K i ^ p.2 i)
    (Function.bijective_iff_existsUnique _ |>.mpr fun x => by
      obtain ⟨ζe, he, huniq⟩ := exist_unique_eq_mul_prod K x
      exact ⟨ζe, he.symm, fun ζe' he' => huniq ζe' he'.symm⟩)

/-- The stabilizer in `(𝓞 K)ˣ` of any nonzero element `a` of `I` is trivial. -/
theorem gapsw80_t8_stabilizer_eq_bot (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : gapsw80_t8_nonzeroIdeal K I) :
    MulAction.stabilizer (𝓞 K)ˣ a = ⊥ := by
  rw [eq_bot_iff]
  intro η hη
  have hstab : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (a : K) :=
    Subtype.ext_iff.mp (MulAction.mem_stabilizer_iff.mp hη)
  have hcoe : algebraMap (𝓞 K) K (η : 𝓞 K) * (a : K) = (a : K) := by
    have hunf : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
    rw [hunf, Algebra.smul_def] at hstab; exact hstab
  have hη1 : algebraMap (𝓞 K) K (η : 𝓞 K) = 1 := (mul_eq_right₀ a.2.2).mp hcoe
  have hη𝓞 : (η : 𝓞 K) = 1 :=
    (IsFractionRing.injective (𝓞 K) K) (hη1.trans (map_one _).symm)
  exact Subgroup.mem_bot.mpr (Units.ext (hη𝓞.trans Units.val_one.symm))

/-- For an orbit `ω`, the bijection from `(𝓞 K)ˣ` to the orbit of `ω.out`, coming from the trivial
stabilizer, sending `η` to `η • ω.out`. -/
noncomputable def gapsw80_t8_orbitGroupEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    (𝓞 K)ˣ ≃ MulAction.orbit (𝓞 K)ˣ ω.out :=
  ((MulAction.orbitEquivQuotientStabilizer (𝓞 K)ˣ ω.out).trans
    ((Subgroup.quotientEquivOfEq (gapsw80_t8_stabilizer_eq_bot K I ω.out)).trans
      (QuotientGroup.quotientBot.toEquiv))).symm

/-- The element of `K` underlying `gapsw80_t8_orbitGroupEquiv K I ω η` is the underlying element of
`η • ω.out`. -/
theorem gapsw80_t8_orbitGroupEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)))
    (η : (𝓞 K)ˣ) :
    ((gapsw80_t8_orbitGroupEquiv K I ω η : gapsw80_t8_nonzeroIdeal K I) : K)
      = ((η • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) := by
  have h := MulAction.orbitEquivQuotientStabilizer_symm_apply (G := (𝓞 K)ˣ) ω.out η
  show ((((MulAction.orbitEquivQuotientStabilizer (𝓞 K)ˣ ω.out).trans
      ((Subgroup.quotientEquivOfEq (gapsw80_t8_stabilizer_eq_bot K I ω.out)).trans
        QuotientGroup.quotientBot.toEquiv)).symm η : gapsw80_t8_nonzeroIdeal K I) : K)
    = ((η • ω.out : gapsw80_t8_nonzeroIdeal K I) : K)
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    show ((QuotientGroup.quotientBot (G := (𝓞 K)ˣ)).toEquiv.symm η : (𝓞 K)ˣ ⧸ (⊥ : Subgroup (𝓞 K)ˣ))
        = QuotientGroup.mk η from rfl,
    show ((Subgroup.quotientEquivOfEq (gapsw80_t8_stabilizer_eq_bot K I ω.out)).symm
          (QuotientGroup.mk η) : (𝓞 K)ˣ ⧸ MulAction.stabilizer (𝓞 K)ˣ ω.out)
        = QuotientGroup.mk η from rfl]
  exact congrArg (fun x : gapsw80_t8_nonzeroIdeal K I => (x : K)) h

/-- The bijection from the sigma type of pairs `(ω, η)` with `ω` an orbit and `η ∈ (𝓞 K)ˣ` onto the
nonzero elements of `I`, sending `(ω, η)` to `η • ω.out`. -/
noncomputable def gapsw80_t8_orbitSigmaEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)), (𝓞 K)ˣ)
      ≃ gapsw80_t8_nonzeroIdeal K I :=
  (Equiv.sigmaCongrRight fun ω => gapsw80_t8_orbitGroupEquiv K I ω).trans
    (MulAction.selfEquivSigmaOrbits (𝓞 K)ˣ (gapsw80_t8_nonzeroIdeal K I)).symm

/-- The element of `K` underlying `gapsw80_t8_orbitSigmaEquiv K I ⟨ω, η⟩` is the underlying element
of `η • ω.out`. -/
theorem gapsw80_t8_orbitSigmaEquiv_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)))
    (η : (𝓞 K)ˣ) :
    ((gapsw80_t8_orbitSigmaEquiv K I ⟨ω, η⟩ : gapsw80_t8_nonzeroIdeal K I) : K)
      = ((η • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) :=
  gapsw80_t8_orbitGroupEquiv_apply K I ω η

/-- The bijection between the `ℤ`-span of the standard basis of `{w // w ≠ w₀} → ℝ` and
`{w // w ≠ w₀} → ℤ`, sending an element to its integer coordinates. -/
noncomputable def gapsw80_t8_spanEquiv :
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      ≃ ({w : InfinitePlace K // w ≠ w₀} → ℤ) where
  toFun g := fun i =>
    ((Basis.mem_span_iff_repr_mem ℤ _ _).mp g.2 i).choose
  invFun m := ⟨fun i => (m i : ℝ), by
    rw [Basis.mem_span_iff_repr_mem]
    exact fun i => ⟨m i, by simp⟩⟩
  left_inv g := by
    apply Subtype.ext; funext i
    have := ((Basis.mem_span_iff_repr_mem ℤ _ _).mp g.2 i).choose_spec
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
    exact this
  right_inv m := by
    funext i
    refine Int.cast_injective (α := ℝ) ?_
    have hmem : (fun j => (m j : ℝ))
        ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) := by
      rw [Basis.mem_span_iff_repr_mem]; exact fun j => ⟨m j, by simp⟩
    have := ((Basis.mem_span_iff_repr_mem ℤ _ _).mp hmem i).choose_spec
    simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
    exact this

/-- For `m : {w : InfinitePlace K // w ≠ w₀} → ℤ`, the `i`-th coordinate of
`(gapsw80_t8_spanEquiv K).symm m` is `m i`. -/
theorem gapsw80_t8_spanEquiv_symm_apply_coe (m : {w : InfinitePlace K // w ≠ w₀} → ℤ)
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    ((gapsw80_t8_spanEquiv K).symm m : logSpace K) i = (m i : ℝ) := rfl

/-- For weights `c`, `0 < t`, `u` in the log space and `g` in the integer span of the standard
basis, translating `u` by `g` gives the same weighted quadratic form at `a` as the form at
parameter `(t, u)` evaluated at `a` multiplied by the product of fundamental units raised to the
integer coordinates of `g`. -/
theorem gapsw80_t8_quadForm_shift_span_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i, fundSystem K (equivFinRank.symm i) ^ (gapsw80_t8_spanEquiv K g i))
                • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  set m := gapsw80_t8_spanEquiv K g with hm_def
  have hg : (g : logSpace K) = ∑ i, (m i : ℝ) • Pi.single i (1:ℝ) := by
    have : g = (gapsw80_t8_spanEquiv K).symm m := ((gapsw80_t8_spanEquiv K).symm_apply_apply g).symm
    rw [this]
    funext j
    simp only [gapsw80_t8_spanEquiv_symm_apply_coe, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hg]
  have hstep : ∀ (v : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ),
      ∀ (b : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, c w * gapsw80_t8_placeParam K (t, v + (k : ℝ) • Pi.single i 1) w * (w (b : K)) ^ 2
        = ∑ w, c w * gapsw80_t8_placeParam K (t, v) w
            * (w (((fundSystem K (equivFinRank.symm i) ^ k) • b : gapsw80_t8_nonzeroIdeal K I)
                : K)) ^ 2 := by
    intro v i k
    induction k using Int.induction_on with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [show (((n:ℤ)+1:ℤ):ℝ) • Pi.single i (1:ℝ)
              = ((n:ℤ):ℝ) • Pi.single i 1 + Pi.single i 1 from by
            push_cast; rw [add_smul, one_smul],
        ← add_assoc, gapsw80_t8_quadForm_shift_single_c K I c ht,
        ih (fundSystem K (equivFinRank.symm i) • b), ← mul_smul, ← _root_.zpow_add_one,
        show ((n:ℤ)+1 : ℤ) = (((n:ℕ)+1:ℕ):ℤ) from by push_cast; ring]
    | pred n ih =>
      intro b
      have key := (gapsw80_t8_quadForm_shift_single_c K I c ht
        (v + ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i 1) i
        ((fundSystem K (equivFinRank.symm i))⁻¹ • b)).symm
      rw [← mul_smul, mul_inv_cancel, one_smul, add_assoc,
        show ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i (1:ℝ) + Pi.single i 1
            = ((-(n:ℤ):ℤ):ℝ) • Pi.single i 1 from by
          rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, sub_add_cancel]] at key
      rw [key, ih ((fundSystem K (equivFinRank.symm i))⁻¹ • b), ← mul_smul,
        show fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)) * (fundSystem K (equivFinRank.symm i))⁻¹
            = fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)-1) from by group]
  suffices ∀ (s : Finset {w : InfinitePlace K // w ≠ w₀}) (a' : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, c w * gapsw80_t8_placeParam K (t, u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) w
          * (w (a' : K)) ^ 2
        = ∑ w, c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i ∈ s, fundSystem K (equivFinRank.symm i) ^ (m i)) • a'
                : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 from this Finset.univ a
  intro s
  induction s using Finset.induction with
  | empty => intro a'; simp
  | insert j s hj ih =>
    intro a'
    rw [Finset.sum_insert hj, add_comm ((m j : ℝ) • Pi.single j 1), ← add_assoc,
      hstep (u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) j (m j) a',
      ih ((fundSystem K (equivFinRank.symm j) ^ (m j)) • a'),
      Finset.prod_insert hj, mul_smul, smul_comm]

/-- For `t > 0`, `u` and `g` in the `ℤ`-span of the standard basis,
$\sum_w y_{u+g}(w) \, w(a)^2 = \sum_w y_u(w) \, w(\eta_g a)^2$, where
`y_u = gapsw80_t8_placeParam K (t, u)` and
`η_g = ∏ i, fundSystem K i ^ (gapsw80_t8_spanEquiv K g i)`. -/
theorem gapsw80_t8_quadForm_shift_span (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        gapsw80_t8_placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i, fundSystem K (equivFinRank.symm i) ^ (gapsw80_t8_spanEquiv K g i))
                • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  simpa only [Pi.one_apply, one_mul] using gapsw80_t8_quadForm_shift_span_c K I 1 ht u g a

/-- The type of nonzero elements of `I` is countable. -/
scoped instance gapsw80_t8_countable_nonzeroIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Countable (gapsw80_t8_nonzeroIdeal K I) :=
  ((gapsw80_t8_nonzeroIdealLatticeEquiv K I).trans
    (gapsw80_t8_zEquivNonzero K I).symm).countable_iff.mpr Subtype.countable

/-- Lebesgue measure on `logSpace K` is invariant under translation by the `ℤ`-span of the
standard basis. -/
local instance : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (logSpace K) volume :=
  ⟨fun _ _ _ => measure_preimage_add _ _ _⟩

/-- The `ℤ`-span of the standard basis of `logSpace K` is countable. -/
local instance : Countable
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}))) :=
  (gapsw80_t8_spanEquiv K).countable_iff.mpr inferInstance

/-- The `ℤ`-span of the standard basis of `logSpace K` acts on `ℝ × logSpace K` by translation
of the second coordinate. -/
noncomputable local instance instSpanProdAddAction : AddAction
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) where
  vadd g p := (p.1, g +ᵥ p.2)
  zero_vadd p := Prod.ext rfl (zero_vadd _ p.2)
  add_vadd g h p := Prod.ext rfl (add_vadd g h p.2)

/-- Translation by each element of the `ℤ`-span of the standard basis is measurable on
`ℝ × logSpace K`. -/
local instance instSpanProdMeasurableConstVAdd : MeasurableConstVAdd
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) :=
  ⟨fun g => measurable_fst.prodMk ((measurable_const_vadd g).comp measurable_snd)⟩

/-- The product of Lebesgue measure on `Set.Ioi 0` and Lebesgue measure on `logSpace K` is
invariant under translation by the `ℤ`-span of the standard basis. -/
local instance instSpanProdVAddInvariant : VAddInvariantMeasure
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (ℝ × logSpace K) (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) :=
  ⟨fun g _ hs =>
    ((MeasurePreserving.id _).prod (measurePreserving_vadd g volume)).measure_preimage
      hs.nullMeasurableSet⟩

/-- For weights `c` and a nonzero element `a` of `I`, the map
`p ↦ cexp (-π ∑ w, c w * gapsw80_t8_placeParam K p w * (w a)^2)` on `ℝ × logSpace K` is continuous.
-/
theorem gapsw80_t8_continuous_cexpQ_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (a : gapsw80_t8_nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finsetSum _ fun w _ => ?_)
  exact (continuous_const.mul
    (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd))).mul continuous_const

/-- For nonzero `a` in `I`, the map
`p ↦ cexp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w a) ^ 2))` on `ℝ × logSpace K` is continuous.
-/
theorem gapsw80_t8_continuous_cexpQ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : gapsw80_t8_nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  simpa only [Pi.one_apply, one_mul] using gapsw80_t8_continuous_cexpQ_c K I 1 a

/-- The sum over nonzero `a` in `I` of the lower integrals over `Set.Ioi 0 ×ˢ gapsw80_t7_unitBox K`
of $e^{-\pi \sum_w y_p(w) w(a)^2} p_1^{\sigma - 1}$, with `y_p = gapsw80_t8_placeParam K p`, equals
`torsionOrder K` times the sum over unit-orbits `ω` of the lower integrals over
`Set.Ioi 0 ×ˢ Set.univ` of the same function with `a` replaced by `gapsw80_t8_orbitRepr K I ω`. -/
theorem gapsw80_t8_lintegral_master_reindex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σre : ℝ) :
    ∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2)) * p.1 ^ (σre - 1))
      = (torsionOrder K : ENNReal) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            ENNReal.ofReal (Real.exp
                (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2))
              * p.1 ^ (σre - 1)) := by
  set GE : gapsw80_t8_nonzeroIdeal K I → ℝ × logSpace K → ENNReal := fun a p =>
    ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
      * p.1 ^ (σre - 1)) with hGE_def
  have hGE_orbitSigma : ∀ ω η p, GE (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, η⟩) p
      = GE (η • ω.out) p := fun ω η p => by unfold GE; congr 4

  rw [← (gapsw80_t8_orbitSigmaEquiv K I).tsum_eq fun a =>
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), GE a p,
    ENNReal.tsum_sigma']
  refine (tsum_congr fun ω => ?_).trans ENNReal.tsum_mul_left

  have hstep6a : ∀ p' : torsion K × (Fin (rank K) → ℤ), ∀ p : ℝ × logSpace K,
      GE (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩) p
        = GE ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p => by
    rw [hGE_orbitSigma,
      show gapsw80_t8_dutEquiv K p' • ω.out
          = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
        rw [← mul_smul]; rfl]
    unfold GE; congr 5
    exact gapsw80_t8_quadForm_torsion_invariant K I p p'.1 _
  rw [← (gapsw80_t8_dutEquiv K).tsum_eq,
    tsum_congr fun p' => lintegral_congr fun p => hstep6a p' p]

  rw [ENNReal.tsum_prod']
  simp only
  rw [ENNReal.tsum_const,
    show (ENat.card (torsion K) : ENNReal) = (torsionOrder K : ENNReal) from by
      rw [ENat.card_eq_coe_natCard]; rfl]
  congr 1

  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (gapsw80_t8_spanEquiv K).symm with hefr_def
  have hefr_prod : ∀ g,
      (∏ j, fundSystem K j ^ efr.symm g j)
        = ∏ i, fundSystem K (equivFinRank.symm i) ^ gapsw80_t8_spanEquiv K g i := fun g => by
    have hefrs : ∀ j, efr.symm g j = gapsw80_t8_spanEquiv K g (equivFinRank j) := fun j => by
      simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
        Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
    exact Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
      fun j => by rw [hefrs j, Equiv.symm_apply_apply]
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [hefr_prod g]]

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σre - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σre - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a, Measurable (GE a) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)
  have hGE_slice_meas : ∀ a,
      Measurable fun t : ℝ => ∫⁻ u in gapsw80_t7_unitBox K, GE a (t, u) ∂volume := fun a =>
    (hGE_meas a).lintegral_prod_right' (ν := volume.restrict (gapsw80_t7_unitBox K))
  have hGE_repr : (fun p => ENNReal.ofReal (Real.exp
          (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2))
        * p.1 ^ (σre - 1))) = GE ω.out := rfl
  simp_rw [hGE_repr, Measure.volume_eq_prod (ℝ) (logSpace K),
    ← Measure.prod_restrict, lintegral_prod _ (hGE_meas _).aemeasurable, setLIntegral_univ]
  rw [← lintegral_tsum fun g => (hGE_slice_meas _).aemeasurable.restrict]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [(gapsw80_t7_unitBox_isAddFundamentalDomain K).lintegral_eq_tsum''
    (fun u => GE ω.out (t, u))]
  exact tsum_congr fun g => setLIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => by
      unfold GE; congr 5
      rw [show (g +ᵥ u : logSpace K) = u + (g : logSpace K) from by
            rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
      exact (gapsw80_t8_quadForm_shift_span K I ht u g ω.out).symm

/-- If `0 < p.1`, the extended norm of the complex number
$e^{-\pi \sum_w c_w y_p(w) w(x)^2} p_1^{\sigma - 1}$ is `ENNReal.ofReal` of the real number
$e^{-\pi \sum_w c_w y_p(w) w(x)^2} p_1^{\operatorname{re} \sigma - 1}$, where
`y_p = gapsw80_t8_placeParam K p`. -/
theorem gapsw80_t8_enorm_integrand_eq_c (c : realSpace K) (σ : ℂ) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  rw [← ofReal_norm, norm_mul, Complex.norm_exp, Complex.ofReal_re,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
    Complex.sub_re, Complex.one_re]

/-- For `0 < p.1`, the extended norm of the complex number
$e^{-\pi \sum_w y_p(w) w(x)^2} p_1^{\sigma - 1}$ is `ENNReal.ofReal` of the real number
$e^{-\pi \sum_w y_p(w) w(x)^2} p_1^{\operatorname{re} \sigma - 1}$, where
`y_p = gapsw80_t8_placeParam K p`. -/
theorem gapsw80_t8_enorm_integrand_eq (σ : ℂ) (x : K) {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  simpa only [Pi.one_apply, one_mul] using gapsw80_t8_enorm_integrand_eq_c K 1 σ x hp

/-- For `σ` with `(gapsw80_t7_heckeWeakFEPair K I).k < σ.re`, the sum over nonzero elements `a` of
the ideal `I` of the lower Lebesgue integrals of
`exp (-π ∑ w, gapsw80_t8_placeParam K p w * (w a)^2) * p.1 ^ (σ.re - 1)` over
`Ioi 0 ×ˢ gapsw80_t7_unitBox K` is not `⊤`. -/
theorem gapsw80_t8_master_finite (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re) :
    (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by

  have hMC : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
        - (gapsw80_t7_heckeWeakFEPair K I).f₀)) (Set.Ioi 0) volume :=
    ((gapsw80_t7_heckeWeakFEPair K I).hasMellin hσ).1
  suffices heq : (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          ‖(t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
            - (gapsw80_t7_heckeWeakFEPair K I).f₀)‖ₑ by
    rw [heq]; exact hMC.2.ne

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σ.re - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σ.re - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a : gapsw80_t8_nonzeroIdeal K I,
      Measurable fun p : ℝ × logSpace K =>
        ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)

  rw [← lintegral_tsum fun a => (hGE_meas a).aemeasurable.restrict,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (Measurable.tsum hGE_meas).aemeasurable]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  have hrpow_nn : (0:ℝ) ≤ t ^ (σ.re - 1) := Real.rpow_nonneg ht'.le _
  have hy : ∀ u : logSpace K, ∀ w, 0 < gapsw80_t8_placeParam K (t, u) w :=
    fun u w => gapsw80_t8_placeParam_pos K ht' (p := (t, u)) w

  have hΘ_real : ∀ u : logSpace K,
      gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1
        = ((∑' a : gapsw80_t8_nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2)) : ℝ)
          : ℂ) := fun u => by
    rw [gapsw80_t8_multiIdealTheta_sub_one K I (hy u), Complex.ofReal_tsum]
    exact tsum_congr fun a => (Complex.ofReal_exp _).symm
  have hΘ_norm : ∀ u : logSpace K,
      ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖
        = ∑' a : gapsw80_t8_nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2)) := fun u => by
    rw [hΘ_real u, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le)]
  have hintΘ := gapsw80_t8_integrableOn_theta_sub_one K I ht'
  calc (∫⁻ u in gapsw80_t7_unitBox K,
          ∑' a : gapsw80_t8_nonzeroIdeal K I,
            ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w
                * (w (a : K)) ^ 2)) * t ^ (σ.re - 1)) ∂volume)

      = ENNReal.ofReal (t ^ (σ.re - 1)) * ∫⁻ u in gapsw80_t7_unitBox K,
            ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖ₑ ∂volume := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun
          (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
        rw [tsum_congr fun a => by rw [mul_comm, ENNReal.ofReal_mul hrpow_nn],
          ENNReal.tsum_mul_left,
          ← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
            (gapsw80_t8_summable_rexpQ K I (hy u)),
          ← ofReal_norm, hΘ_norm u]

    _ = ENNReal.ofReal (t ^ (σ.re - 1) * ∫ u in gapsw80_t7_unitBox K,
            ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖ ∂volume) := by
        rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            fun u _ => (ofReal_norm _).symm,
          ← ofReal_integral_eq_lintegral_ofReal hintΘ.norm (ae_of_all _ fun u => norm_nonneg _),
          ENNReal.ofReal_mul hrpow_nn]

    _ = _ := by
        rw [← ofReal_norm, smul_eq_mul, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.one_re,
          show (gapsw80_t7_heckeWeakFEPair K I).f = gapsw80_t5_heckeKernel K I from rfl,
          show ((gapsw80_t7_heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl,
          gapsw80_t8_heckeKernel_sub_one K I ht',
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_real u),
          integral_complex_ofReal, Complex.norm_real,
          Real.norm_of_nonneg (integral_nonneg fun u => tsum_nonneg fun _ => (Real.exp_pos _).le),
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_norm u)]

/-- For `σ` with `(gapsw80_t7_heckeWeakFEPair K I).k < σ.re` and a unit-orbit `ω` of nonzero
elements of `I`, the function $p \mapsto e^{-\pi \sum_w y_p(w) w(a)^2} p_1^{\sigma - 1}$ is
integrable on `Ioi 0 ×ˢ univ`, where `y_p = gapsw80_t8_placeParam K p` and
`a = gapsw80_t8_orbitRepr K I ω`. -/
theorem gapsw80_t8_integrableOn_orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w
            * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w
          * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (gapsw80_t8_continuous_cexpQ K I ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
      fun p hp => gapsw80_t8_enorm_integrand_eq K σ (gapsw80_t8_orbitRepr K I ω) (p := p) hp.1]
  refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (gapsw80_t8_master_finite K I hσ))
  rw [gapsw80_t8_lintegral_master_reindex K I σ.re]
  exact le_trans (ENNReal.le_tsum (f := fun ω' => ∫⁻ p in Set.Ioi (0:ℝ) ×ˢ Set.univ,
      ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w
        * w (gapsw80_t8_orbitRepr K I ω') ^ 2)) * p.1 ^ (σ.re - 1))) ω)
    (le_mul_of_one_le_left' (by exact_mod_cast torsionOrder_pos K))

set_option maxHeartbeats 6400000 in
/-- Given finiteness of the lower-integral sum over nonzero elements of `I` and integrability of
each orbit-representative integrand on `Ioi 0 ×ˢ univ`, the Mellin-type integral over `t > 0` of
`t^(σ-1)` times the integral over the unit box of the theta sum over nonzero elements of `I` equals
`torsionOrder K` times the sum over unit-orbit classes of the corresponding integral over
`Ioi 0 ×ˢ univ`. -/
theorem gapsw80_t8_rankinSelberg_unfold_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (σ : ℂ)
    (hMaster : (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤)
    (hIntω : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume) :
    (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
        * ∫ u in gapsw80_t7_unitBox K,
            (∑' a : gapsw80_t8_nonzeroIdeal K I,
              cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
            ∂volume)
      = (torsionOrder K : ℂ) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K, c w * gapsw80_t8_placeParam K p w
                * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ (σ - 1) := by

  set F : gapsw80_t8_nonzeroIdeal K I → ℝ × logSpace K → ℂ := fun a p =>
    cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ)
      * ((p.1 : ℝ) : ℂ) ^ (σ - 1) with hF_def
  have hF_sm : ∀ a, AEStronglyMeasurable (F a)
      (volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K))) := fun a =>
    ((gapsw80_t8_continuous_cexpQ_c K I c a).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt).aestronglyMeasurable
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
  have hF_enorm : ∀ a, ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
      ‖F a p‖ₑ = ENNReal.ofReal
        (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a p hp =>
    gapsw80_t8_enorm_integrand_eq_c K c σ (a : K) (p := p) hp.1
  have hMaster' : (∑' a, ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ‖F a p‖ₑ) ≠ ⊤ := by
    refine (tsum_congr fun a => setLIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      (hF_enorm a)).symm ▸ hMaster

  have hFsum_int : IntegrableOn (fun p => ∑' a, F a p)
      ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K)) volume := by
    refine ⟨AEStronglyMeasurable.tsum hF_sm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hMaster')
    rw [← lintegral_tsum fun a => (hF_sm a).enorm]
    exact lintegral_mono fun p => enorm_tsum_le_tsum_enorm
  rw [show (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume)
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ∑' a, F a p from by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hFsum_int]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
      fun u _ => by rw [tsum_mul_right, mul_comm]]

  rw [integral_tsum hF_sm hMaster']

  have hSsum : Summable fun a => ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F a p := by
    refine .of_norm (.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
      (ENNReal.summable_toReal hMaster'))
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top hMaster' (ENNReal.le_tsum
      (f := fun a => ∫⁻ p in Set.Ioi (0:ℝ) ×ˢ gapsw80_t7_unitBox K, ‖F a p‖ₑ) a))
      (enorm_integral_le_lintegral_enorm _)
  have hF_Q : ∀ (a b : gapsw80_t8_nonzeroIdeal K I) (p : ℝ × logSpace K),
      (∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2)
        = ∑ w, c w * gapsw80_t8_placeParam K p w * (w (b : K)) ^ 2 →
      F a p = F b p := fun a b p hQ => by unfold F; rw [hQ]
  have hSsumSig : Summable fun p :
        Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)), (𝓞 K)ˣ =>
      ∫ q in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F (gapsw80_t8_orbitSigmaEquiv K I p) q :=
    (gapsw80_t8_orbitSigmaEquiv K I).summable_iff.mpr hSsum
  rw [((gapsw80_t8_orbitSigmaEquiv K I).tsum_eq _).symm.trans hSsumSig.tsum_sigma,
    ← tsum_mul_left]
  refine tsum_congr fun ω => ?_
  have hstep6a : ∀ (p' : torsion K × (Fin (rank K) → ℤ)) (p : ℝ × logSpace K),
      F (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩) p
        = F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p =>
    hF_Q _ _ p (by
      rw [show ((gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩ :
            gapsw80_t8_nonzeroIdeal K I) : K)
          = ((gapsw80_t8_dutEquiv K p' • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) from
        gapsw80_t8_orbitSigmaEquiv_apply K I ω _,
        show gapsw80_t8_dutEquiv K p' • ω.out
            = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
          rw [← mul_smul]; rfl]
      exact gapsw80_t8_quadForm_torsion_invariant_c K I c p p'.1 _)
  rw [← (gapsw80_t8_dutEquiv K).tsum_eq,
    tsum_congr fun p' => setIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      fun p _ => hstep6a p' p]
  have hSsumPr : Summable fun p' : torsion K × (Fin (rank K) → ℤ) =>
      ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
        F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p :=
    ((hSsumSig.sigma_factor ω).comp_injective (i := gapsw80_t8_dutEquiv K)
      (gapsw80_t8_dutEquiv K).injective).congr
      fun p' => setIntegral_congr_fun
        (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
        fun p _ => hstep6a p' p
  rw [hSsumPr.tsum_prod]
  simp only
  rw [tsum_const, nsmul_eq_mul,
    show ((torsionOrder K : ℕ) : ℂ) = (Nat.card (torsion K) : ℂ) from rfl]
  congr 1
  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (gapsw80_t8_spanEquiv K).symm with hefr_def
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [show (∏ j, fundSystem K j ^ efr.symm g j)
        = (∏ i, fundSystem K (equivFinRank.symm i) ^ gapsw80_t8_spanEquiv K g i) from
      Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
        fun j => by
          simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
            Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
            Equiv.symm_apply_apply, id_eq]]]

  have hInt_ω : IntegrableOn (F ω.out)
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := hIntω ω
  have hInt_box : ∀ b : gapsw80_t8_nonzeroIdeal K I,
      IntegrableOn (F b) ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K)) volume := fun b =>
    ⟨hF_sm b, hasFiniteIntegral_iff_enorm.mpr
      (lt_of_le_of_lt (ENNReal.le_tsum
        (f := fun a => ∫⁻ p in Set.Ioi (0:ℝ) ×ˢ gapsw80_t7_unitBox K, ‖F a p‖ₑ) b)
        (lt_top_iff_ne_top.mpr hMaster'))⟩
  set ν : Measure (ℝ × logSpace K) :=
    ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume with hν_def
  have hν_eq : (volume : Measure (ℝ × logSpace K)).restrict
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) = ν := by
    rw [hν_def, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hν_box : (volume : Measure (ℝ × logSpace K)).restrict
        ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K))
      = ν.restrict (Prod.snd ⁻¹' gapsw80_t7_unitBox K) := by
    rw [hν_def, show (Prod.snd ⁻¹' gapsw80_t7_unitBox K : Set (ℝ × logSpace K))
          = Set.univ ×ˢ gapsw80_t7_unitBox K from Set.univ_prod.symm,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict]
  have hInt_ω' : Integrable (F ω.out) ν := by rw [← hν_eq]; exact hInt_ω
  have hFD_prod : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (Prod.snd ⁻¹' gapsw80_t7_unitBox K) ν :=
    (gapsw80_t7_unitBox_isAddFundamentalDomain K).preimage_of_equiv
      (f := Prod.snd) Measure.quasiMeasurePreserving_snd Function.bijective_id (fun _ _ => rfl)
  rw [show (fun p : ℝ × logSpace K =>
          cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w
                * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1)) = F ω.out from rfl,
    show (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)), F ω.out p)
        = ∫ p, F ω.out p ∂ν from by rw [← hν_eq],
    hFD_prod.integral_eq_tsum'' (F ω.out) hInt_ω']
  refine tsum_congr fun g => ?_
  rw [show (∫ p in Prod.snd ⁻¹' gapsw80_t7_unitBox K, F ω.out (g +ᵥ p) ∂ν)
        = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F ω.out (g +ᵥ p) from by
    show (∫ p, _ ∂(ν.restrict _)) = ∫ p, _ ∂(volume.restrict _); rw [hν_box]]
  refine setIntegral_congr_fun
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
    fun p hp => ?_
  show F _ p = F ω.out (p.1, g +ᵥ p.2)
  unfold F
  congr 5
  rw [show (g +ᵥ p.2 : logSpace K) = p.2 + (g : logSpace K) from by
        rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
  exact (gapsw80_t8_quadForm_shift_span_c K I c hp.1 p.2 g ω.out).symm

/-- For `1 < s.re`, `(gapsw80_t7_heckeWeakFEPair K I).Λ (nK K * s / 2)` equals `torsionOrder K`
times the sum over unit-orbits `x` of nonzero elements of `I` of the integral over `Ioi 0 ×ˢ univ`
of $e^{-\pi \sum_w y_p(w) w(a_x)^2} p_1^{n s / 2 - 1}$, where `y_p = gapsw80_t8_placeParam K p` and
`a_x = gapsw80_t8_orbitRepr K I x`. -/
theorem gapsw80_t8_heckeLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K I x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def

  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hMellin := ((gapsw80_t7_heckeWeakFEPair K I).hasMellin hσ_re).2
  rw [← hMellin]

  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
          - (gapsw80_t7_heckeWeakFEPair K I).f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (gapsw80_t7_heckeWeakFEPair K I).f = gapsw80_t5_heckeKernel K I from rfl,
      show ((gapsw80_t7_heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      gapsw80_t8_heckeKernel_sub_one K I ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    exact gapsw80_t8_multiIdealTheta_sub_one K I (fun w => gapsw80_t8_placeParam_pos K ht' w)
  rw [show mellin (fun t => (gapsw80_t7_heckeWeakFEPair K I).f t
        - (gapsw80_t7_heckeWeakFEPair K I).f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  have hMaster1 : (∑' a : gapsw80_t8_nonzeroIdeal K I,
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
        ENNReal.ofReal
          (Real.exp (-(π * ∑ w, (1:realSpace K) w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
            * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
    simp only [Pi.one_apply, one_mul]; exact gapsw80_t8_master_finite K I hσ_re
  have hIntω1 : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, (1:realSpace K) w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := fun ω => by
    simp only [Pi.one_apply, one_mul]; exact gapsw80_t8_integrableOn_orbitRepr K I hσ_re ω
  have hRS := gapsw80_t8_rankinSelberg_unfold_c K I 1 σ hMaster1 hIntω1
  simp only [Pi.one_apply, one_mul] at hRS
  exact hRS

/-- For `1 < s.re` and a unit-orbit `ω`, the integral over `Ioi 0 ×ˢ univ` of
$e^{-\pi \sum_w y_p(w) w(a)^2} p_1^{n s / 2 - 1}$, where `y_p = gapsw80_t8_placeParam K p` and
`a = gapsw80_t8_orbitRepr K I ω`, equals $(2^{r_1 - 1} n R_K)^{-1}$ times
$\Gamma_\mathbb{R}(s)^{r_1} (\Gamma_\mathbb{C}(s) 2^{s-1})^{r_2} |N(a)|^{-s}$. Here `r₁` and `r₂`
are the numbers of real and complex places, `R_K` is the regulator and `N` is the norm to `ℚ`. -/
theorem gapsw80_t8_perOrbit_integral_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = (((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
        * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
          * ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K I ω) : ℚ)| : ℝ) : ℂ) ^ (-s)) := by
  set a : K := gapsw80_t8_orbitRepr K I ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, gapsw80_t8_prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [gapsw80_t8_ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring

  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finsetSum _ fun w _ =>
          (continuous_apply w).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finsetProd _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    gapsw80_t8_setIntegral_placeParam K hG_sm]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]

    rw [show cexp ((-(π * ∑ w, τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K, cexp ((-(π * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,

      gapsw80_t8_prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            gapsw80_t8_ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]

    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*(w a)^2*τ w):ℝ):ℂ) * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)),

      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    · rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    · rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]

  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact gapsw80_t8_mellin_expNeg_eq_Gamma
          (mul_pos Real.pi_pos (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  rw [show (∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = ∏ w : InfinitePlace K,
            (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by rw [normAtPlace_apply],
    gapsw80_t8_prod_gammaFactor_eq K hx_nz,
    gapsw80_t8_prod_normAtPlace_cpow K s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

/-- The normalising constant `(2 ^ (r₁ - 1) n R_K)⁻¹ (2 ^ (s - 1)) ^ r₂` equals
`(2 ^ (r₁ + r₂ - 1))⁻¹ n⁻¹ R_K⁻¹ 2 ^ (r₂ s)`. -/
theorem gapsw80_t8_regulator_const_eq (s : ℂ) :
    (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) := by
  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have := card_add_two_mul_card_eq_rank K
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) := by
    rw [Complex.ofReal_ofNat,
      ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
      ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
      ← Complex.cpow_neg, ← Complex.cpow_neg,
      ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
      ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
    congr 1
    push_cast [Nat.cast_sub hr₁]
    ring
  rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_zpow, Complex.ofReal_ofNat]
  linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow

/-- For `1 < s.re`, `(gapsw80_t7_heckeWeakFEPair K I).Λ (nK K * s / 2)` equals
$\frac{w_K}{2^{r_1 + r_2 - 1} n R_K} \operatorname{covol}(I)^{-s} |d_K|^{s/2}$ times
$\Gamma_\mathbb{R}(s)^{r_1} \Gamma_\mathbb{C}(s)^{r_2}$ times
`gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s`, where `w_K = torsionOrder K` and `R_K`
is the regulator. -/
theorem gapsw80_t8_heckeLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by
  rw [gapsw80_t8_heckeLambda_unfold_eq K I hs,
    tsum_congr (gapsw80_t8_perOrbit_integral_eq K I hs), tsum_mul_left, tsum_mul_left,
    gapsw80_t8_tsum_orbit_normInv_eq K I, mul_pow (Gammaℂ s), div_eq_mul_inv, mul_inv, mul_inv]
  have hconst := gapsw80_t8_regulator_const_eq K s
  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K I):ℝ):ℂ)^(-s)
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2)
  set CabsN : ℂ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s)
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s)
  have hcd : Ccov * Cdisc = CabsN * C2rs := gapsw80_t8_covol_discr_cpow K I s
  linear_combination (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s) * hcd

omit [NumberField K] in
/-- Each multiplicity weight satisfies `1 ≤ gapsw80_t7_multSq K w`. -/
theorem gapsw80_t8_one_le_multSq (w : InfinitePlace K) : (1:ℝ) ≤ gapsw80_t7_multSq K w :=
  one_le_pow₀ (Nat.one_le_cast.mpr mult_pos)

/-- For `0 < t`, `gapsw80_t7_multHeckeKernel K J t - 1` equals the integral over `u` in the unit
box of `gapsw80_t4_multiIdealTheta K J` at
`w ↦ gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w`, minus `1`. -/
theorem gapsw80_t8_multHeckeKernel_sub_one (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t7_multHeckeKernel K J t - 1
      = ∫ u in gapsw80_t7_unitBox K,
          (gapsw80_t4_multiIdealTheta K J
            (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w) - 1) ∂volume := by
  have hvol : volume (gapsw80_t7_unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hcont : Continuous
      (fun u => gapsw80_t4_multiIdealTheta K J
        (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w)) := by
    have h := continuous_genericKernel_integrand K J (Real.log t / 2)
      (gapsw80_t7_multSq K) (multSq_pos K)
    exact h.congr fun u => by
      congr 1; funext w
      rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht]; rfl
  have hint1 : IntegrableOn
      (fun u => gapsw80_t4_multiIdealTheta K J
        (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w))
      (gapsw80_t7_unitBox K) volume := by
    have hcompact : IsCompact
        (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hcont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set
      (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  rw [integral_sub hint1 hint2, setIntegral_const]
  have hvol' : volume.real (gapsw80_t7_unitBox K) = 1 := by
    rw [measureReal_def, hvol, ENNReal.toReal_one]
  rw [hvol', one_smul]
  congr 1
  unfold gapsw80_t7_multHeckeKernel gapsw80_t7_integrand
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w
  rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht]; rfl

/-- If every weight satisfies `1 ≤ c w` and `0 < p.1`, then
$e^{-\pi \sum_w c_w y_p(w) w(x)^2} \le e^{-\pi \sum_w y_p(w) w(x)^2}$, where
`y_p = gapsw80_t8_placeParam K p`. -/
theorem gapsw80_t8_rexpQ_c_le {c : realSpace K} (hc : ∀ w, 1 ≤ c w) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2))
      ≤ Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2)) := by
  refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le))
  refine Finset.sum_le_sum fun w _ => ?_
  have hpp := (gapsw80_t8_placeParam_pos K hp w).le
  have hwx := sq_nonneg (w x)
  nlinarith [hc w, mul_nonneg hpp hwx]

/-- For `σ` with `(gapsw80_t7_heckeWeakFEPair K J).k < σ.re`, the sum over nonzero `a` in `J` of
the lower integrals over `Ioi 0 ×ˢ gapsw80_t7_unitBox K` of
$e^{-\pi \sum_w m_w^2 y_p(w) w(a)^2} p_1^{\operatorname{re} \sigma - 1}$ is finite, where
`y_p = gapsw80_t8_placeParam K p` and `m_w = mult w`. -/
theorem gapsw80_t8_master_finite_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re) :
    (∑' a : gapsw80_t8_nonzeroIdeal K J,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
                * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (gapsw80_t8_master_finite K J hσ) ?_
  refine ENNReal.tsum_le_tsum fun a => ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))] with p hp
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (gapsw80_t8_rexpQ_c_le K (gapsw80_t8_one_le_multSq K) (a : K) hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

/-- For `σ` with `(gapsw80_t7_heckeWeakFEPair K J).k < σ.re` and a unit-orbit `ω`, the function
$p \mapsto e^{-\pi \sum_w m_w^2 y_p(w) w(a)^2} p_1^{\sigma - 1}$ is integrable on `Ioi 0 ×ˢ univ`,
where `y_p = gapsw80_t8_placeParam K p`, `m_w = mult w` and `a = gapsw80_t8_orbitRepr K J ω`. -/
theorem gapsw80_t8_integrableOn_orbitRepr_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K J))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
            * (w (gapsw80_t8_orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  set a : K := gapsw80_t8_orbitRepr K J ω
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
          * (w a) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (gapsw80_t8_continuous_cexpQ_c K J (gapsw80_t7_multSq K) ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound := (gapsw80_t8_integrableOn_orbitRepr K J hσ ω).2
  rw [hasFiniteIntegral_iff_enorm] at hbound
  refine lt_of_le_of_lt ?_ hbound
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  rw [gapsw80_t8_enorm_integrand_eq_c K (gapsw80_t7_multSq K) σ a hp.1,
    gapsw80_t8_enorm_integrand_eq K σ a hp.1]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (gapsw80_t8_rexpQ_c_le K (gapsw80_t8_one_le_multSq K) a hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

/-- For `1 < s.re`, `(gapsw80_t7_heckeWeakFEPair K I).symm.Λ (nK K * s / 2)` equals
`torsionOrder K` times the sum over unit-orbits of nonzero elements of the trace-dual ideal of `I`
of the integrals over `Ioi 0 ×ˢ univ` of $e^{-\pi \sum_w m_w^2 y_p(w) w(a)^2} p_1^{n s / 2 - 1}$,
where `y_p = gapsw80_t8_placeParam K p`, `m_w = mult w` and `a` is the orbit representative. -/
theorem gapsw80_t8_symmLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ)
            (gapsw80_t8_nonzeroIdeal K (gapsw80_t6_traceDualIdeal K I))),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K (gapsw80_t6_traceDualIdeal K I) x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := gapsw80_t6_traceDualIdeal K I
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def
  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((gapsw80_t7_heckeWeakFEPair K I).symm.k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hσ_reJ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re := hσ_re

  have hMellin := ((gapsw80_t7_heckeWeakFEPair K I).symm.hasMellin hσ_re).2
  rw [← hMellin]

  have hy : ∀ {t : ℝ} (_ : 0 < t) (u : logSpace K), ∀ w,
      0 < gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w := fun ht u w =>
    mul_pos (multSq_pos K w) (gapsw80_t8_placeParam_pos K ht w)
  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).symm.f t
          - (gapsw80_t7_heckeWeakFEPair K I).symm.f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K J,
                cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (gapsw80_t7_heckeWeakFEPair K I).symm.f
          = gapsw80_t7_multHeckeKernel K J from rfl,
      show ((gapsw80_t7_heckeWeakFEPair K I).symm.f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      gapsw80_t8_multHeckeKernel_sub_one K J ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    have := gapsw80_t8_multiIdealTheta_sub_one K J (y := fun w =>
        gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w) (hy ht' u)
    simpa only [mul_assoc] using this
  rw [show mellin (fun t => (gapsw80_t7_heckeWeakFEPair K I).symm.f t
        - (gapsw80_t7_heckeWeakFEPair K I).symm.f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K J,
                cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  exact gapsw80_t8_rankinSelberg_unfold_c K J (gapsw80_t7_multSq K) σ
    (gapsw80_t8_master_finite_mult K J hσ_reJ)
    (gapsw80_t8_integrableOn_orbitRepr_mult K J hσ_reJ)

/-- For `1 < s.re` and a unit-orbit `ω`, the integral over `Ioi 0 ×ˢ univ` of
$e^{-\pi \sum_w m_w^2 y_p(w) w(a)^2} p_1^{n s / 2 - 1}$, where `y_p = gapsw80_t8_placeParam K p`,
`m_w = mult w` and `a = gapsw80_t8_orbitRepr K J ω`, equals $4^{-r_2 s} (2^{r_1 - 1} n R_K)^{-1}$
times $\Gamma_\mathbb{R}(s)^{r_1} (\Gamma_\mathbb{C}(s) 2^{s-1})^{r_2} |N(a)|^{-s}$. -/
theorem gapsw80_t8_perOrbit_integral_eq_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K J))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
            * ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K J ω) : ℚ)| : ℝ) : ℂ) ^ (-s))) := by
  set a : K := gapsw80_t8_orbitRepr K J ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, gapsw80_t8_prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [gapsw80_t8_ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring
  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finsetSum _ fun w _ =>
          (continuous_const.mul (continuous_apply w)).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finsetProd _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    gapsw80_t8_setIntegral_placeParam K hG_sm]
  rw [show ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K:ℂ)*s)
        * ((((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s)))
      = (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
        * (((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s))) from by ring]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * gapsw80_t7_multSq K w * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]
    rw [show cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K,
              cexp ((-(π * gapsw80_t7_multSq K w * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,
      gapsw80_t8_prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            gapsw80_t8_ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)
          * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
          * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)),
      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    · rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    · rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]
  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
              * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact gapsw80_t8_mellin_expNeg_eq_Gamma
          (mul_pos (mul_pos Real.pi_pos (multSq_pos K w)) (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  have hsplit : ∀ w : InfinitePlace K,
      ((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
        = ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
          * ((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) := fun w => by
    rw [show π * gapsw80_t7_multSq K w * (w a)^2
          = gapsw80_t7_multSq K w * (π * (w a)^2) from by ring,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (multSq_pos K w).le
        (mul_nonneg Real.pi_pos.le (sq_nonneg _))]
  rw [show (∏ w : InfinitePlace K,
            (((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = (∏ w : InfinitePlace K, ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))
          * ∏ w : InfinitePlace K,
              (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
                * Complex.Gamma ((w.mult:ℂ)*s/2)) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [hsplit w, normAtPlace_apply]; ring,
    gapsw80_t8_prod_gammaFactor_eq K hx_nz,
    gapsw80_t8_prod_normAtPlace_cpow K s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

  congr 1
  rw [prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))]
  have hreal : (∏ w : {w : InfinitePlace K // IsReal w},
      ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2))) = 1 :=
    Finset.prod_eq_one fun w _ => by
      rw [show gapsw80_t7_multSq K w.1 = 1 from by
        simp [gapsw80_t7_multSq, mult_isReal w], Complex.ofReal_one, Complex.one_cpow]
  have hcplx : (∏ w : {w : InfinitePlace K // IsComplex w},
        ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
      = ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) := by
    rw [show (∏ w : {w : InfinitePlace K // IsComplex w},
            ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
          = ∏ _w : {w : InfinitePlace K // IsComplex w}, ((4:ℝ):ℂ)^(-s) from
        Finset.prod_congr rfl fun w _ => by
          rw [show gapsw80_t7_multSq K w.1 = 4 from by
            simp [gapsw80_t7_multSq, mult_isComplex w]; norm_num,
            mult_isComplex w]
          congr 1; push_cast; ring,
      Finset.prod_const, ← Complex.cpow_nat_mul, Finset.card_univ,
      show Fintype.card {w : InfinitePlace K // IsComplex w} = nrComplexPlaces K from rfl]
    congr 1; ring
  rw [hreal, one_mul, hcplx]

/-- For `1 < s.re`, `(gapsw80_t7_heckeWeakFEPair K I).symm.Λ (nK K * s / 2)` equals
$\frac{w_K}{2^{r_1 + r_2 - 1} n R_K} 4^{-r_2 s} \operatorname{covol}(I^\vee)^{-s}$ times
$|d_K|^{s/2} \Gamma_\mathbb{R}(s)^{r_1} \Gamma_\mathbb{C}(s)^{r_2}$ times the partial Dedekind zeta
function of the class `(ClassGroup.mk K I^∨)⁻¹` at `s`, where `I^∨` is the trace-dual ideal of `I`.
-/
theorem gapsw80_t8_symmLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K
            (gapsw80_t6_traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s := by
  set J := gapsw80_t6_traceDualIdeal K I
  rw [gapsw80_t8_symmLambda_unfold_eq K I hs,
    tsum_congr (gapsw80_t8_perOrbit_integral_eq_mult K J hs), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, gapsw80_t8_tsum_orbit_normInv_eq K J, mul_pow (Gammaℂ s),
    div_eq_mul_inv, mul_inv, mul_inv]
  have hconst := gapsw80_t8_regulator_const_eq K s
  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K J):ℝ):ℂ)^(-s)
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2)
  set CabsN : ℂ := ((FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s)
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s)
  set C4rs : ℂ := ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s)
  have hcd : Ccov * Cdisc = CabsN * C2rs := gapsw80_t8_covol_discr_cpow K J s
  linear_combination C4rs * (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - C4rs * ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s) * hcd

/-- The product of the covolumes of the ideal lattices of `I` and of its trace-dual ideal equals
`(4⁻¹)^(nrComplexPlaces K)`. -/
theorem gapsw80_t8_sat_covol_prod (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I))
      = (4 : ℝ)⁻¹ ^ nrComplexPlaces K := by
  have h4 : ((4:ℝ) ^ nrComplexPlaces K) ≠ 0 := (pow_pos (by norm_num) _).ne'
  have hdet : |(gapsw80_t6_bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I)) := by
    rw [gapsw80_t6_bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, gapsw80_t6_abs_det_Phi]
  have h1 : ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * (4 : ℝ) ^ nrComplexPlaces K
        * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I))
      = 1 := hdet ▸ gapsw80_t6_abs_det_bridgeMatrix K I
  rw [inv_pow]; field_simp
  linear_combination h1

end FLT.Gapsw80T8MellinGammaPartialZeta

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"
p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

