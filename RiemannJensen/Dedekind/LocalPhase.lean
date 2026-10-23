module

public import RiemannJensen.Dedekind.ContourWindowGeometry
public import RiemannJensen.Dedekind.SaddleHessianEventual
public import RiemannJensen.Dedekind.SaddleInverseAction

/-!
# The normalized Dedekind local phase

The local phase is the variation of the Dedekind saddle phase along the arc
`y ↦ u * exp (I * ℓ * y)` through the saddle point `u`, where `ℓ` is the local width, divided by
the quadratic scale `‖H‖ * ℓ ^ 2` with `H` the saddle Hessian.

## Main definitions

* `dedekindLocalPhase`: the normalized phase variation along the local saddle arc.

## Main results

* `dedekindLocalPhase_zero`: the local phase vanishes at `y = 0`.
* `dedekindLocalPhase_first`: the derivative of the local phase at `y = 0` vanishes.
* `eventually_dedekindLocalPhase_re_nonpos`: for all large `d`, the real part of the local phase
  is nonpositive for `y ∈ [-1, 1]`, uniformly in `q`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The variation of the saddle phase from the saddle point `u` to `u * exp (I * ℓ * y)`, where
`ℓ` is the local width, divided by `‖H‖ * ℓ ^ 2` with `H` the saddle Hessian. -/
noncomputable def dedekindLocalPhase (d : ℕ) (q y : ℝ) : ℂ :=
  let ℓ := dedekindLocalWidth K d q
  (dedekindSaddlePhase K d q
      (dedekindSaddle K d q *
        Complex.exp (Complex.I * (ℓ : ℂ) * (y : ℂ))) -
    dedekindSaddlePhase K d q (dedekindSaddle K d q)) /
      (((‖dedekindSaddleHessian K d q‖ * ℓ ^ 2 : ℝ) : ℂ))

/-- The local phase vanishes at `y = 0`. -/
@[simp] theorem dedekindLocalPhase_zero (d : ℕ) (q : ℝ) :
    dedekindLocalPhase K d q 0 = 0 := by
  simp [dedekindLocalPhase]

private theorem hasDerivAt_analyticLowerSqrt_local {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt analyticLowerSqrt (analyticLowerSqrt u / (2 * u)) u :=
  ((Complex.hasDerivAt_log hu).div_const 2).cexp.congr_deriv <| by
    unfold analyticLowerSqrt
    field_simp [Complex.slitPlane_ne_zero hu]

private noncomputable def analyticDedekindPhase (Λ q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) * u + (Real.pi : ℂ) * analyticLowerSqrt u +
    ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt u * Complex.log u - Complex.log u

private noncomputable def analyticDedekindPhaseDeriv (Λ q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) + (Real.pi : ℂ) * (analyticLowerSqrt u / (2 * u)) +
    ((Real.pi / Λ : ℝ) : ℂ) *
      ((analyticLowerSqrt u / (2 * u)) * Complex.log u + analyticLowerSqrt u / u) -
    1 / u

private theorem hasDerivAt_analyticDedekindPhase
    {Λ q : ℝ} {u : ℂ} (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticDedekindPhase Λ q)
      (analyticDedekindPhaseDeriv Λ q u) u := by
  have hs := hasDerivAt_analyticLowerSqrt_local hu
  have hl := Complex.hasDerivAt_log hu
  have hraw := ((((hasDerivAt_id u).const_mul (-(q : ℂ))).add
      (hs.const_mul (Real.pi : ℂ))).add
      ((hs.mul hl).const_mul ((Real.pi / Λ : ℝ) : ℂ))).sub hl
  refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · dsimp [analyticDedekindPhase]
    ring
  · simp only [analyticDedekindPhaseDeriv]
    field_simp [Complex.slitPlane_ne_zero hu]

private theorem hasDerivAt_saddlePhase_of_im_neg
    (Λ q : ℝ) {u : ℂ} (hu : u.im < 0) :
    HasDerivAt (saddlePhaseAtLambda Λ q)
      (analyticDedekindPhaseDeriv Λ q u) u := by
  have heq : saddlePhaseAtLambda Λ q =ᶠ[𝓝 u]
      analyticDedekindPhase Λ q := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hu]
      with z hz
    rw [saddlePhaseAtLambda, analyticDedekindPhase,
      lowerSqrt_eq_sqrt_of_im_neg hz, lowerLog_eq_log_of_im_neg hz, analyticLowerSqrt,
      ← sqrt_eq_exp (by rintro rfl; simp at hz)]
    simp only [saddleKappa]
    ring_nf
  exact (hasDerivAt_analyticDedekindPhase
    (Complex.mem_slitPlane_iff.mpr (Or.inr hu.ne))).congr_of_eventuallyEq heq

private theorem dedekindSaddle_im_neg (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    (dedekindSaddle K d q).im < 0 := by
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hr := dedekindSaddleRadius_pos K d hd (α := dedekindSaddleAngle K d q)
    ⟨hrange.1.le, hrange.2.le⟩
  rw [dedekindSaddle, show (-2 : ℂ) * Complex.I * (dedekindSaddleAngle K d q : ℂ) =
    ((-2 * dedekindSaddleAngle K d q : ℝ) : ℂ) * Complex.I by push_cast; ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [show -2 * dedekindSaddleAngle K d q =
    -(2 * dedekindSaddleAngle K d q) by ring, Real.sin_neg]
  have hs : 0 < Real.sin (2 * dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hrange.1])
      (by linarith [hrange.2])
  nlinarith [sq_pos_of_pos hr]

private noncomputable def dedekindLocalArc (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  dedekindSaddle K d q *
    Complex.exp (Complex.I * (dedekindLocalWidth K d q : ℂ) * z)

private theorem hasDerivAt_dedekindLocalArc (d : ℕ) (q : ℝ) (z : ℂ) :
    HasDerivAt (dedekindLocalArc K d q)
      (dedekindLocalArc K d q z *
        (Complex.I * (dedekindLocalWidth K d q : ℂ))) z := by
  unfold dedekindLocalArc
  have hi := (hasDerivAt_id z).const_mul
    (Complex.I * (dedekindLocalWidth K d q : ℂ))
  have he := (Complex.hasDerivAt_exp
    (Complex.I * (dedekindLocalWidth K d q : ℂ) * z)).comp z hi
  simpa only [Function.comp_apply, mul_one, one_mul,
    mul_assoc] using he.const_mul (dedekindSaddle K d q)

/-- For `q ∈ (dedekindEdgeQ K d, dedekindScaleT K d]`, the derivative of the local phase at
`y = 0` vanishes. -/
theorem dedekindLocalPhase_first
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    deriv (dedekindLocalPhase K d q) 0 = 0 := by
  have hp := hasDerivAt_saddlePhase_of_im_neg (dedekindScaleLambda K d) q
    (dedekindSaddle_im_neg K d hd hq)
  have hp0 : analyticDedekindPhaseDeriv (dedekindScaleLambda K d) q
      (dedekindSaddle K d q) = 0 := by
    have hs := dedekindSaddle_stationary K d hd hq
    unfold dedekindSaddlePhase at hs
    rwa [hp.deriv] at hs
  have hcomp := (((hp.comp_of_eq 0 (hasDerivAt_dedekindLocalArc K d q 0)
    (by simp [dedekindLocalArc])).sub_const
      (dedekindSaddlePhase K d q (dedekindSaddle K d q))).div_const
      (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))).comp_ofReal
  refine ((hcomp.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv
    (by simp [hp0])).deriv
  simp [dedekindLocalPhase, dedekindLocalArc, dedekindSaddlePhase, mul_assoc]

/-- The point `u * exp (I * ℓ * y)` of the local arc is the saddle circle point at angle
`α - ℓ * y / 2`. -/
private theorem dedekindLocalPhase_point_eq_circle
    (d : ℕ) (q y : ℝ) :
    dedekindSaddle K d q * Complex.exp
        (Complex.I * (dedekindLocalWidth K d q : ℂ) * (y : ℂ)) =
      (((dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I *
          (((-2 * (dedekindSaddleAngle K d q -
            dedekindLocalWidth K d q * y / 2) : ℝ) : ℂ)))) := by
  rw [dedekindSaddle, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem sub_mul_div_two_mem_Icc_of_dedekindLocalWidth
    {d : ℕ} {q y : ℝ} (hα : dedekindSaddleAngle K d q ∈ Ioo 0 (Real.pi / 2))
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    dedekindSaddleAngle K d q - dedekindLocalWidth K d q * y / 2 ∈ Icc 0 (Real.pi / 2) := by
  set α := dedekindSaddleAngle K d q
  have hcos : Real.cos α ≤ Real.pi / 2 - α := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le (by linarith [hα.2])
  have hc0 : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩
  have hm1 := min_le_left α (Real.cos α)
  have hm2 := min_le_right α (Real.cos α)
  have hm0 : 0 ≤ min α (Real.cos α) := le_min hα.1.le hc0
  simp only [dedekindLocalWidth, dedekindLocalEpsilon, mem_Icc] at hy ⊢
  constructor <;> nlinarith [hy.1, hy.2]

private theorem dedekindLocalWidth_pos {d : ℕ} {q : ℝ}
    (hα : dedekindSaddleAngle K d q ∈ Ioo 0 (Real.pi / 2)) :
    0 < dedekindLocalWidth K d q :=
  mul_pos (by norm_num [dedekindLocalEpsilon])
    (lt_min hα.1 (Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩))

/-- For all sufficiently large `d`, every `q ∈ (dedekindEdgeQ K d, dedekindScaleT K d]` and every
`y ∈ [-1, 1]`, the real part of the local phase is nonpositive. -/
theorem eventually_dedekindLocalPhase_re_nonpos :
    ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
      dedekindEdgeQ K d < q → q ≤ dedekindScaleT K d →
      ∀ y ∈ Icc (-1 : ℝ) 1, (dedekindLocalPhase K d q y).re ≤ 0 := by
  obtain ⟨D, hΛ⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  filter_upwards [eventually_ge_atTop (max D 1)] with d hd
  intro q hedge hqT y hy
  obtain ⟨hdD, hd1⟩ := max_le_iff.mp hd
  have hrange := dedekindSaddle_inverse_range K d hd1 ⟨hedge, hqT⟩
  have hinv := dedekindSaddle_inverse K d hd1 ⟨hedge, hqT⟩
  have hgap := dedekindSaddlePhase_circle_quadratic_gap K d (hΛ d hdD)
    ⟨hrange.1, hrange.2.le⟩ (sub_mul_div_two_mem_Icc_of_dedekindLocalWidth K hrange hy)
  have hcenter := dedekindLocalPhase_point_eq_circle K d q 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one, zero_div, sub_zero] at hcenter
  rw [hinv, ← hcenter] at hgap
  have hnormb := dedekindSaddleHessian_norm_bounds K d hd1 (hΛ d hdD) hrange
  rw [hinv] at hnormb
  have hsin : 0 < Real.sin (dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi hrange.1 (hrange.2.trans (by linarith [Real.pi_pos]))
  have hden : 0 < ‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 :=
    mul_pos (by nlinarith) (pow_pos (dedekindLocalWidth_pos K hrange) 2)
  rw [dedekindLocalPhase, dedekindLocalPhase_point_eq_circle, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Complex.sub_re,
    Complex.normSq_ofReal, zero_div, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (by nlinarith [sq_nonneg (Real.cos (dedekindSaddleAngle K d q -
          dedekindLocalWidth K d q * y / 2) - Real.cos (dedekindSaddleAngle K d q))])
      hden.le)
    (mul_nonneg hden.le hden.le)

end

end RiemannJensen
