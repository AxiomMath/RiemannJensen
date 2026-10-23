module

public import RiemannJensen.Dedekind.SaddleHessianAdapters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Inversion and action along the Dedekind saddle branch -/

@[expose] public section

namespace RiemannJensen

open Set Filter
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem dedekindScaleA_pos_inv : 0 < dedekindScaleA K := by
  unfold dedekindScaleA
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)

private theorem dedekindDiscriminantAbs_one_le :
    1 ≤ dedekindDiscriminantAbs K := by
  rw [dedekindDiscriminantAbs]
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

private theorem dedekindScaleA_le_two_pi :
    dedekindScaleA K ≤ 2 * Real.pi := by
  unfold dedekindScaleA
  have hpow : Real.rpow (dedekindDiscriminantAbs K)
      (-(1 / (dedekindDegree K : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (dedekindDiscriminantAbs_one_le K) (neg_nonpos.2 (by positivity))
  nlinarith [Real.pi_pos]

private theorem sinRatio_eq_inv_sinc_dedekind (x : ℝ) :
    sinRatio x = (Real.sinc x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [sinRatio_of_ne hx, Real.sinc_of_ne_zero hx]
    field_simp

/-- The sine ratio is continuous on the complete saddle interval. -/
private theorem continuousOn_sinRatio_dedekind :
    ContinuousOn sinRatio (Set.Icc 0 (Real.pi / 2)) := by
  rw [funext sinRatio_eq_inv_sinc_dedekind]
  apply Real.continuous_sinc.continuousOn.fun_inv₀
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hxpos
  · simp
  · rw [Real.sinc_of_ne_zero hxpos.ne']
    exact (div_pos
      (Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2, Real.pi_pos]))
      hxpos).ne'

private theorem continuousOn_alphaCot_dedekind :
    ContinuousOn alphaCot (Set.Icc 0 (Real.pi / 2)) := by
  have hid : alphaCot = fun x => sinRatio x * Real.cos x := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [alphaCot_of_ne hx, sinRatio_of_ne hx]
      ring
  rw [hid]
  exact continuousOn_sinRatio_dedekind.mul Real.continuous_cos.continuousOn

/-- Exact radial coordinate at the right endpoint of the Dedekind branch. -/
theorem dedekindSaddleRadius_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    dedekindSaddleRadius K d (Real.pi / 2) =
      dedekindScaleA K / dedekindScaleT K d := by
  apply dedekindSaddleRadius_eq_of_radial K
      (dedekindSaddleRadialCoeff_nonneg K d hd (by
        constructor <;> linarith [Real.pi_pos]))
  · exact div_pos (dedekindScaleA_pos_inv K) (dedekindScaleT_pos K d hd)
  · have hT := dedekindScaleT_pos K d hd
    have hA : 0 < dedekindScaleA K := dedekindScaleA_pos_inv K
    have hlog :
        Real.log (dedekindScaleA K / dedekindScaleT K d) =
          -(dedekindScaleLambda K d / 2) - 1 := by
      rw [Real.log_div hA.ne' hT.ne', dedekindScaleLambda_div_two,
        Real.log_div hT.ne' hA.ne']
      ring
    rw [saddleRadialAtLambda, Real.cos_pi_div_two,
      alphaCot_of_ne (by positivity : Real.pi / 2 ≠ 0),
      Real.cos_pi_div_two, Real.sin_pi_div_two, hlog]
    field_simp
    ring

/-- Exact formula for the Dedekind saddle level at the right endpoint. -/
theorem dedekindSaddleQ_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    dedekindSaddleQ K d (Real.pi / 2) =
      (dedekindScaleT K d / dedekindScaleA K) ^ 2 +
        (Real.pi / dedekindScaleLambda K d) * (Real.pi / 2) *
          (dedekindScaleT K d / dedekindScaleA K) := by
  rw [dedekindSaddleQ, saddleQAtLambda,
    ← dedekindSaddleRadius, dedekindSaddleRadius_pi_div_two K d hd,
    sinRatio_of_ne (by positivity : Real.pi / 2 ≠ 0), Real.sin_pi_div_two]
  have hT : dedekindScaleT K d ≠ 0 := (dedekindScaleT_pos K d hd).ne'
  have hA : dedekindScaleA K ≠ 0 := (dedekindScaleA_pos_inv K).ne'
  simp only [saddleKappa]
  field_simp

private theorem four_mul_dedekindLambda_half_lt_scale_ratio
    (d : ℕ) (hd : 1 ≤ d) :
    4 * (dedekindScaleLambda K d / 2) <
      dedekindScaleT K d / dedekindScaleA K := by
  let x := dedekindScaleT K d / dedekindScaleA K
  have hx : 0 < x := div_pos (dedekindScaleT_pos K d hd) (dedekindScaleA_pos_inv K)
  have hlog4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 4),
      show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hx4 : 0 < x / 4 := by positivity
  have hbase := Real.log_le_sub_one_of_pos hx4
  have hlogsplit : Real.log x = Real.log (x / 4) + Real.log 4 := by
    rw [← Real.log_mul (by positivity : x / 4 ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    congr 1
    field_simp
  have hcoord : dedekindScaleLambda K d / 2 = Real.log x - 1 := by
    rw [dedekindScaleLambda_div_two]
  rw [hcoord, hlogsplit]
  linarith

/-- The right endpoint of the Dedekind saddle branch lies beyond its scale. -/
theorem dedekindScaleT_lt_saddleQ_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    dedekindScaleT K d < dedekindSaddleQ K d (Real.pi / 2) := by
  rw [dedekindSaddleQ_pi_div_two K d hd]
  let x := dedekindScaleT K d / dedekindScaleA K
  let L := dedekindScaleLambda K d / 2
  have hx : 0 < x := div_pos (dedekindScaleT_pos K d hd) (dedekindScaleA_pos_inv K)
  have hL : 0 < L := half_pos (dedekindScaleLambda_pos K d hd)
  have hcomp : 4 * L < x := by
    simpa [x, L] using four_mul_dedekindLambda_half_lt_scale_ratio K d hd
  have hΛ : dedekindScaleLambda K d = 2 * L := by
    dsimp [L]
    ring
  have hamgm : 2 * Real.pi * x < x ^ 2 + Real.pi ^ 2 * x / (4 * L) := by
    have hfrac : Real.pi ^ 2 < Real.pi ^ 2 * x / (4 * L) := by
      rw [lt_div_iff₀ (by positivity : 0 < 4 * L)]
      nlinarith [sq_pos_of_pos Real.pi_pos]
    nlinarith [sq_nonneg (x - Real.pi), hfrac]
  calc
    dedekindScaleT K d = dedekindScaleA K * x := by
      dsimp [x]
      field_simp [(dedekindScaleA_pos_inv K).ne']
    _ ≤ 2 * Real.pi * x := mul_le_mul_of_nonneg_right (dedekindScaleA_le_two_pi K) hx.le
    _ < x ^ 2 + Real.pi ^ 2 * x / (4 * L) := hamgm
    _ = (dedekindScaleT K d / dedekindScaleA K) ^ 2 +
        (Real.pi / dedekindScaleLambda K d) * (Real.pi / 2) *
          (dedekindScaleT K d / dedekindScaleA K) := by
      rw [hΛ]
      dsimp [x]
      field_simp
      ring

/-- Continuity of the Dedekind radial coefficient. -/
private theorem continuousOn_dedekindSaddleRadialCoeff (d : ℕ) :
    ContinuousOn (dedekindSaddleRadialCoeff K d) (Set.Icc 0 (Real.pi / 2)) := by
  unfold dedekindSaddleRadialCoeff
  fun_prop

/-- Continuity of the Dedekind radial constant. -/
private theorem continuousOn_dedekindSaddleRadialConst (d : ℕ) :
    ContinuousOn (dedekindSaddleRadialConst K d) (Set.Icc 0 (Real.pi / 2)) := by
  unfold dedekindSaddleRadialConst
  exact (continuousOn_alphaCot_dedekind.sub continuousOn_const).sub continuousOn_const

/-- Continuity of the positive Dedekind radial root along the closed branch. -/
theorem continuousOn_dedekindSaddleRadius (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (dedekindSaddleRadius K d) (Set.Icc 0 (Real.pi / 2)) := by
  intro α hα
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  have hr₀ := dedekindSaddleRadius_pos_and_eq K d hd hα
  rw [dedekindSaddleRadial_eq] at hr₀
  set r₀ := dedekindSaddleRadius K d α
  let e := min (ε / 2) (r₀ / 2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hr₀.1)
  have heε : e < ε := (min_le_left _ _).trans_lt (by linarith)
  have her : e ≤ r₀ / 2 := min_le_right _ _
  have hlo : 0 < r₀ - e := by linarith [hr₀.1]
  have hhi : 0 < r₀ + e := by linarith [hr₀.1]
  have hcoeffα := dedekindSaddleRadialCoeff_nonneg K d hd hα
  have hflo := radialEquation_strictAntiOn (B := dedekindSaddleRadialConst K d α)
    hcoeffα hlo hr₀.1 (sub_lt_self r₀ he)
  have hfhi := radialEquation_strictAntiOn (B := dedekindSaddleRadialConst K d α)
    hcoeffα hr₀.1 hhi (lt_add_of_pos_right r₀ he)
  rw [hr₀.2] at hflo hfhi
  have hcont (t : ℝ) : ContinuousWithinAt
      (fun β => radialEquation (dedekindSaddleRadialCoeff K d β)
        (dedekindSaddleRadialConst K d β) t) (Set.Icc 0 (Real.pi / 2)) α := by
    unfold radialEquation
    exact (((continuousOn_dedekindSaddleRadialCoeff K d α hα).div_const t).add
      (continuousOn_dedekindSaddleRadialConst K d α hα)).sub continuousWithinAt_const
  filter_upwards [self_mem_nhdsWithin, hcont _ (Ioi_mem_nhds hflo),
    hcont _ (Iio_mem_nhds hfhi)] with β hβ hβlo hβhi
  simp only [mem_preimage, mem_Ioi, mem_Iio] at hβlo hβhi
  have hrβ := dedekindSaddleRadius_pos_and_eq K d hd hβ
  rw [dedekindSaddleRadial_eq] at hrβ
  have hcoeffβ := dedekindSaddleRadialCoeff_nonneg K d hd hβ
  have hlβ : r₀ - e < dedekindSaddleRadius K d β := by
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with hlt | heq
    · linarith [hrβ.2, radialEquation_strictAntiOn
        (B := dedekindSaddleRadialConst K d β) hcoeffβ hrβ.1 hlo hlt]
    · rw [← heq, hrβ.2] at hβlo
      exact lt_irrefl _ hβlo
  have hβh : dedekindSaddleRadius K d β < r₀ + e := by
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with hlt | heq
    · linarith [hrβ.2, radialEquation_strictAntiOn
        (B := dedekindSaddleRadialConst K d β) hcoeffβ hhi hrβ.1 hlt]
    · rw [heq, hrβ.2] at hβhi
      exact lt_irrefl _ hβhi
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The Dedekind saddle level is continuous on the closed angle interval. -/
theorem continuousOn_dedekindSaddleQ (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (dedekindSaddleQ K d) (Set.Icc 0 (Real.pi / 2)) := by
  rw [show dedekindSaddleQ K d = fun α =>
      (dedekindSaddleRadius K d α)⁻¹ ^ 2 +
        (2 * saddleKappa / dedekindScaleLambda K d) * sinRatio α *
          (dedekindSaddleRadius K d α)⁻¹ by rfl]
  have hr := continuousOn_dedekindSaddleRadius K d hd
  have hinv := hr.fun_inv₀ fun x hx => (dedekindSaddleRadius_pos K d hd hx).ne'
  exact (hinv.pow 2).add
    (((continuousOn_const.mul continuousOn_sinRatio_dedekind).mul hinv))

/-- Every parameter between the endpoint values is recovered by the inverse angle. -/
theorem dedekindSaddleQ_saddleAngle_of_mem (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Icc (dedekindEdgeQ K d)
      (dedekindSaddleQ K d (Real.pi / 2))) :
    dedekindSaddleAngle K d q ∈ Set.Icc 0 (Real.pi / 2) ∧
      dedekindSaddleQ K d (dedekindSaddleAngle K d q) = q := by
  obtain ⟨α, hα, rfl⟩ := intermediate_value_Icc (by positivity)
    (continuousOn_dedekindSaddleQ K d hd) (by simpa [dedekindEdgeQ] using hq)
  rw [dedekindSaddleAngle_saddleQ K d hd hα]
  exact ⟨hα, rfl⟩

/-- Inverse saddle identity on the complete scale window. -/
theorem dedekindSaddle_inverse (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    dedekindSaddleQ K d (dedekindSaddleAngle K d q) = q :=
  (dedekindSaddleQ_saddleAngle_of_mem K d hd
    ⟨hq.1.le, (hq.2.trans_lt (dedekindScaleT_lt_saddleQ_pi_div_two K d hd)).le⟩).2

/-- Range of the inverse Dedekind saddle angle on the scale window. -/
theorem dedekindSaddle_inverse_range (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    0 < dedekindSaddleAngle K d q ∧
      dedekindSaddleAngle K d q < Real.pi / 2 := by
  have htop := dedekindScaleT_lt_saddleQ_pi_div_two K d hd
  rcases dedekindSaddleQ_saddleAngle_of_mem K d hd ⟨hq.1.le, (hq.2.trans_lt htop).le⟩ with
    ⟨hangle, hinv⟩
  refine ⟨hangle.1.lt_of_ne fun hz => hq.1.ne ?_, hangle.2.lt_of_ne fun hz => ?_⟩
  · rw [dedekindEdgeQ, hz, hinv]
  · exact (hq.2.trans_lt htop).ne' (hz ▸ hinv)

private theorem hasDerivAt_analyticLowerSqrt_inv {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt analyticLowerSqrt (analyticLowerSqrt u / (2 * u)) u := by
  have hdiv : HasDerivAt (fun z : ℂ => Complex.log z / 2) (u⁻¹ / 2) u :=
    (Complex.hasDerivAt_log hu).div_const 2
  have hcomp := (Complex.hasDerivAt_exp (Complex.log u / 2)).comp u hdiv
  unfold analyticLowerSqrt
  exact hcomp.congr_deriv (by field_simp [Complex.slitPlane_ne_zero hu])

private noncomputable def analyticSaddlePhaseAtLambda (Λ q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) * u + (Real.pi : ℂ) * analyticLowerSqrt u +
    ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt u * Complex.log u - Complex.log u

private noncomputable def analyticSaddlePhaseDerivAtLambda
    (Λ q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) + (Real.pi : ℂ) * (analyticLowerSqrt u / (2 * u)) +
    ((Real.pi / Λ : ℝ) : ℂ) *
      ((analyticLowerSqrt u / (2 * u)) * Complex.log u + analyticLowerSqrt u / u) -
    1 / u

private theorem hasDerivAt_analyticSaddlePhaseAtLambda
    {Λ q : ℝ} {u : ℂ} (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticSaddlePhaseAtLambda Λ q)
      (analyticSaddlePhaseDerivAtLambda Λ q u) u := by
  have hs := hasDerivAt_analyticLowerSqrt_inv hu
  have hl := Complex.hasDerivAt_log hu
  have hraw := ((((hasDerivAt_id u).const_mul (-(q : ℂ))).add
      (hs.const_mul (Real.pi : ℂ))).add
      ((hs.mul hl).const_mul ((Real.pi / Λ : ℝ) : ℂ))).sub hl
  have heq : (-(q : ℂ) * 1 + (Real.pi : ℂ) *
        (analyticLowerSqrt u / (2 * u)) +
      ((Real.pi / Λ : ℝ) : ℂ) *
        ((analyticLowerSqrt u / (2 * u)) * Complex.log u +
          analyticLowerSqrt u * u⁻¹) - u⁻¹) =
      analyticSaddlePhaseDerivAtLambda Λ q u := by
    dsimp [analyticSaddlePhaseDerivAtLambda]
    field_simp [Complex.slitPlane_ne_zero hu]
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv heq
  filter_upwards [] with z
  dsimp [analyticSaddlePhaseAtLambda]
  ring

private theorem hasDerivAt_saddlePhaseAtLambda_of_im_neg
    (Λ q : ℝ) {u : ℂ} (hu : u.im < 0) :
    HasDerivAt (saddlePhaseAtLambda Λ q)
      (analyticSaddlePhaseDerivAtLambda Λ q u) u := by
  have hslit : u ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr hu.ne)
  have heq : saddlePhaseAtLambda Λ q =ᶠ[𝓝 u]
      analyticSaddlePhaseAtLambda Λ q := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hu]
      with z hz
    rw [saddlePhaseAtLambda, analyticSaddlePhaseAtLambda,
      lowerSqrt_eq_sqrt_of_im_neg hz, lowerLog_eq_log_of_im_neg hz,
      analyticLowerSqrt, ← sqrt_eq_exp (by rintro rfl; simp at hz)]
    simp only [saddleKappa]
    ring_nf
  exact (hasDerivAt_analyticSaddlePhaseAtLambda hslit).congr_of_eventuallyEq heq

private theorem analyticLowerSqrt_ofReal_sq_mul_exp {r α : ℝ} (hr : 0 < r)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    analyticLowerSqrt (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) =
      (r : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ) / 2) := by
  rw [analyticLowerSqrt, ← sqrt_eq_exp (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hr.ne')) (Complex.exp_ne_zero _)),
    ← lowerSqrt_eq_sqrt_of_im_neg (im_ofReal_sq_mul_exp_neg_two_mul_I_neg hr hα)]
  exact lowerSqrt_sq_mul_exp_I_mul hr (by linarith [hα.2, Real.pi_pos]) (by linarith [hα.1])

private theorem log_ofReal_sq_mul_exp {r α : ℝ} (hr : 0 < r)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Complex.log (((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) =
      ((2 * Real.log r : ℝ) : ℂ) + Complex.I * ((-2 * α : ℝ) : ℂ) := by
  rw [← lowerLog_eq_log_of_im_neg (im_ofReal_sq_mul_exp_neg_two_mul_I_neg hr hα)]
  exact lowerLog_sq_mul_exp_I_mul hr (by linarith [hα.2]) (by linarith [hα.1])

private theorem exp_neg_ofReal_mul_I (x : ℝ) :
    Complex.exp (((-x : ℝ) : ℂ) * Complex.I) =
      ((Real.cos x : ℝ) : ℂ) - ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private theorem analyticSaddlePhaseDerivAtLambda_saddleQ_eq_zero
    {Λ α : ℝ} (hΛ : 0 < Λ) (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    analyticSaddlePhaseDerivAtLambda Λ (saddleQAtLambda Λ α)
      (((saddleRadiusAtLambda Λ α ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) = 0 := by
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  let r := saddleRadiusAtLambda Λ α
  let u : ℂ := ((r ^ 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))
  have hr : 0 < r := saddleRadiusAtLambda_pos hΛ.le hαcc
  have hu0 : u ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hr.ne'))
    (Complex.exp_ne_zero _)
  have hs : analyticLowerSqrt u =
      (r : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ) / 2) :=
    analyticLowerSqrt_ofReal_sq_mul_exp hr hα
  have hl : Complex.log u =
      ((2 * Real.log r : ℝ) : ℂ) + Complex.I * ((-2 * α : ℝ) : ℂ) :=
    log_ofReal_sq_mul_exp hr hα
  change analyticSaddlePhaseDerivAtLambda Λ (saddleQAtLambda Λ α) u = 0
  rw [analyticSaddlePhaseDerivAtLambda, hs, hl]
  have hq := saddleQAtLambda_mul_radius_sq hΛ hαcc
  have hre := saddle_real_relation_atLambda hΛ hαcc
  rw [sinRatio_of_ne hα.1.ne'] at hq
  dsimp [r] at hq hre ⊢
  field_simp [hu0, hΛ.ne']
  dsimp [u, r]
  have he2 : Complex.exp (((-2 * α : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (2 * α) : ℝ) : ℂ) - ((Real.sin (2 * α) : ℝ) : ℂ) * Complex.I := by
    rw [show -2 * α = -(2 * α) by ring, exp_neg_ofReal_mul_I]
  rw [show Complex.I * (((-(2 * α)) : ℝ) : ℂ) / 2 = ((-α : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    show Complex.I * ((-2 * α : ℝ) : ℂ) = ((-2 * α : ℝ) : ℂ) * Complex.I by ring,
    exp_neg_ofReal_mul_I, he2]
  apply Complex.ext
  all_goals
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    norm_num
    simp only [Real.cos_two_mul, Real.sin_two_mul]
    field_simp [hr.ne', hΛ.ne', Real.pi_ne_zero,
      (Real.sin_pos_of_pos_of_lt_pi hα.1
        (hα.2.trans (by linarith [Real.pi_pos]))).ne'] at hq hre ⊢
  · linear_combination
      Real.cos α * hre + 2 * Real.sin α * hq +
        (2 * Λ * (1 - saddleRadiusAtLambda Λ α ^ 2 *
          saddleQAtLambda Λ α)) * (Real.sin_sq_add_cos_sq α)
  · linear_combination -Real.sin α * hre + 2 * Real.cos α * hq

/-- Stationarity of the recovered Dedekind saddle. -/
theorem dedekindSaddle_stationary (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    deriv (dedekindSaddlePhase K d q) (dedekindSaddle K d q) = 0 := by
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  let α := dedekindSaddleAngle K d q
  let r := dedekindSaddleRadius K d α
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hrange.1.le, hrange.2.le⟩
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd hαcc
  have hpoint : dedekindSaddle K d q =
      (((r ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) := by
    rw [dedekindSaddle]
    congr 1
    dsimp [α]
    push_cast
    ring_nf
  have huim : (dedekindSaddle K d q).im < 0 := by
    rw [hpoint]
    exact im_ofReal_sq_mul_exp_neg_two_mul_I_neg hr hrange
  change deriv (saddlePhaseAtLambda (dedekindScaleLambda K d) q)
    (dedekindSaddle K d q) = 0
  rw [(hasDerivAt_saddlePhaseAtLambda_of_im_neg
    (dedekindScaleLambda K d) q huim).deriv, hpoint, ← hinv]
  change analyticSaddlePhaseDerivAtLambda (dedekindScaleLambda K d)
    (saddleQAtLambda (dedekindScaleLambda K d) α)
    (((saddleRadiusAtLambda (dedekindScaleLambda K d) α ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))) = 0
  exact analyticSaddlePhaseDerivAtLambda_saddleQ_eq_zero
    (dedekindScaleLambda_pos K d hd) hrange

/-- Exact imaginary part of the universal phase on a lower semicircle. -/
theorem saddlePhaseAtLambda_im_sq_exp_neg_two_mul_I
    (Λ q r α : ℝ) (hr : 0 < r) (hα0 : 0 ≤ α)
    (hαpi : α ≤ Real.pi / 2) :
    (saddlePhaseAtLambda Λ q
      (((r ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)))).im =
      q * r ^ 2 * Real.sin (2 * α) - Real.pi * r * Real.sin α -
        (2 * Real.pi * r / Λ) *
          (α * Real.cos α + Real.log r * Real.sin α) + 2 * α := by
  have hθlower : -Real.pi ≤ -2 * α := by linarith
  have hθupper : -2 * α ≤ 0 := by linarith
  rw [saddlePhaseAtLambda,
    lowerSqrt_sq_mul_exp_I_mul hr hθlower hθupper,
    lowerLog_sq_mul_exp_I_mul hr hθlower hθupper]
  have hexp_arg :
      Complex.I * ((-2 * α : ℝ) : ℂ) / 2 = ((-α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hexp_two :
      Complex.I * ((-2 * α : ℝ) : ℂ) =
        ((-2 * α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hsin_two : Real.sin (-2 * α) = -Real.sin (2 * α) := by
    rw [show -2 * α = -(2 * α) by ring, Real.sin_neg]
  rw [hexp_arg, hexp_two]
  simp only [Complex.add_im, Complex.add_re, Complex.sub_im, Complex.neg_im,
    Complex.neg_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg, saddleKappa]
  rw [hsin_two]
  ring

/-- The universal lower-arc phase has the closed action formula at a saddle. -/
theorem saddlePhaseAtLambda_im_eq_closed_action
    (Λ q r α : ℝ) (hr : 0 < r) (hα0 : 0 ≤ α)
    (hαpi : α ≤ Real.pi / 2) (hΛ : Λ ≠ 0)
    (hre : Real.pi * r * (1 + 2 * Real.log r / Λ) =
      2 * (q * r ^ 2 + 1) * Real.cos α - 2 * Real.pi * r / Λ) :
    (saddlePhaseAtLambda Λ q
      (((r ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)))).im =
      2 * α - Real.sin (2 * α) +
        (2 * Real.pi * r / Λ) *
          (Real.sin α - α * Real.cos α) := by
  rw [saddlePhaseAtLambda_im_sq_exp_neg_two_mul_I Λ q r α hr hα0 hαpi]
  exact saddle_action_algebra Λ q r α hΛ hre

/-- Exact saddle action on the Dedekind scale window. -/
theorem dedekindSaddle_action_formula (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    dedekindSaddleAction K d q =
      2 * dedekindSaddleAngle K d q -
        Real.sin (2 * dedekindSaddleAngle K d q) +
      (2 * Real.pi * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) /
          dedekindScaleLambda K d) *
        (Real.sin (dedekindSaddleAngle K d q) -
          dedekindSaddleAngle K d q *
            Real.cos (dedekindSaddleAngle K d q)) := by
  let α := dedekindSaddleAngle K d q
  let r := dedekindSaddleRadius K d α
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hαcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨hrange.1.le, hrange.2.le⟩
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd hαcc
  have hΛ : dedekindScaleLambda K d ≠ 0 :=
    (dedekindScaleLambda_pos K d hd).ne'
  have hre : Real.pi * r *
        (1 + 2 * Real.log r / dedekindScaleLambda K d) =
      2 * (q * r ^ 2 + 1) * Real.cos α -
        2 * Real.pi * r / dedekindScaleLambda K d := by
    have h := saddle_real_relation_atLambda (dedekindScaleLambda_pos K d hd) hαcc
    change Real.pi * r *
          (1 + 2 * Real.log r / dedekindScaleLambda K d) =
        2 * (dedekindSaddleQ K d α * r ^ 2 + 1) * Real.cos α -
          2 * Real.pi * r / dedekindScaleLambda K d at h
    rwa [show dedekindSaddleQ K d α = q by simpa [α] using dedekindSaddle_inverse K d hd hq] at h
  have hclosed := saddlePhaseAtLambda_im_eq_closed_action
    (dedekindScaleLambda K d) q r α hr hrange.1.le hrange.2.le hΛ hre
  rw [dedekindSaddleAction, dedekindSaddle, dedekindSaddlePhase]
  convert hclosed using 1
  congr 3
  dsimp [α]
  push_cast
  ring_nf

end

end RiemannJensen
