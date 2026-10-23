module

public import RiemannJensen.Dedekind.LocalPhase
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Higher derivatives of the normalized Dedekind local phase

Near the saddle point, the normalized Dedekind local phase agrees with a holomorphic function of
the arc parameter, built from the analytic phase coefficient on the slit plane. This file computes
its first three complex derivatives and deduces the value of the second real derivative of the
local phase at the origin.

## Main definitions

* `higherLocalArc`: The complex arc `z ↦ ρ * exp (I * ℓ * z)` through the saddle point `ρ`, with
  local width `ℓ`.
* `higherAnalyticPhase`: The normalized analytic phase along `higherLocalArc`.
* `higherAnalyticPhaseFirst`, `higherAnalyticPhaseSecond`, `higherAnalyticPhaseThird`: Its first,
  second and third complex derivatives.
* `higherCoeffDeriv3`: The third derivative of the analytic phase coefficient.

## Main results

* `localPhase_eventuallyEq_higher`: Near `0`, the local phase equals `higherAnalyticPhase` on the
  real line.
* `dedekindLocalPhase_taylor`: The second derivative of the local phase at `0` is minus the unit
  Hessian direction.
* `eventually_dedekindLocalPhase_taylor`: For all sufficiently large `d`, the same identity holds
  for every `q` in the saddle range.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The arc `z ↦ ρ * exp (I * ℓ * z)` through the Dedekind saddle point `ρ`, where `ℓ` is the
local width. -/
noncomputable def higherLocalArc (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  dedekindSaddle K d q *
    Complex.exp (Complex.I * (dedekindLocalWidth K d q : ℂ) * z)

/-- The analytic phase coefficient along `higherLocalArc`, minus its value at the saddle point,
divided by `‖H‖ * ℓ ^ 2` for the saddle Hessian `H` and local width `ℓ`. -/
noncomputable def higherAnalyticPhase (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  (analyticPhaseCoeff q (Real.pi : ℂ)
      ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) (higherLocalArc K d q z) -
    analyticPhaseCoeff q (Real.pi : ℂ)
      ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) (dedekindSaddle K d q)) /
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))

/-- The complex derivative of `higherAnalyticPhase`. -/
noncomputable def higherAnalyticPhaseFirst
    (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  let u := higherLocalArc K d q z
  let c := Complex.I * (dedekindLocalWidth K d q : ℂ)
  analyticPhaseCoeffDeriv q (Real.pi : ℂ)
      ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * (u * c) /
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))

/-- The second complex derivative of `higherAnalyticPhase`. -/
noncomputable def higherAnalyticPhaseSecond
    (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  let u := higherLocalArc K d q z
  let c := Complex.I * (dedekindLocalWidth K d q : ℂ)
  (analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
      ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * (u * c) ^ 2 +
    analyticPhaseCoeffDeriv q (Real.pi : ℂ)
      ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * (u * c ^ 2)) /
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))

/-- The derivative of `higherLocalArc` at `z` is `higherLocalArc z * (I * ℓ)`. -/
theorem hasDerivAt_higherLocalArc (d : ℕ) (q : ℝ) (z : ℂ) :
    HasDerivAt (higherLocalArc K d q)
      (higherLocalArc K d q z *
        (Complex.I * (dedekindLocalWidth K d q : ℂ))) z := by
  unfold higherLocalArc
  have hlin : HasDerivAt
      (fun w : ℂ => Complex.I * (dedekindLocalWidth K d q : ℂ) * w)
      (Complex.I * (dedekindLocalWidth K d q : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul
      (Complex.I * (dedekindLocalWidth K d q : ℂ))
  have he := (Complex.hasDerivAt_exp _).comp z hlin
  simpa only [Function.comp_apply, mul_assoc] using
    he.const_mul (dedekindSaddle K d q)

/-- Where the arc lies in the slit plane, `higherAnalyticPhase` has derivative
`higherAnalyticPhaseFirst`. -/
theorem hasDerivAt_higherAnalyticPhase
    (d : ℕ) (q : ℝ) {z : ℂ}
    (hslit : higherLocalArc K d q z ∈ Complex.slitPlane) :
    HasDerivAt (higherAnalyticPhase K d q)
      (higherAnalyticPhaseFirst K d q z) z := by
  have hu := hasDerivAt_higherLocalArc K d q z
  have hp := (hasDerivAt_analyticPhaseCoeff
    (q := q) (a := (Real.pi : ℂ))
    (b := ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)) hslit).comp z hu
  have hnum := hp.sub_const (analyticPhaseCoeff q (Real.pi : ℂ)
    ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) (dedekindSaddle K d q))
  have hraw := hnum.div_const
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp [higherAnalyticPhaseFirst]
  · filter_upwards [] with w
    dsimp [higherAnalyticPhase]

/-- Where the arc lies in the slit plane, `higherAnalyticPhaseFirst` has derivative
`higherAnalyticPhaseSecond`. -/
theorem hasDerivAt_higherAnalyticPhaseFirst
    (d : ℕ) (q : ℝ) {z : ℂ}
    (hslit : higherLocalArc K d q z ∈ Complex.slitPlane) :
    HasDerivAt (higherAnalyticPhaseFirst K d q)
      (higherAnalyticPhaseSecond K d q z) z := by
  let u := higherLocalArc K d q z
  let c : ℂ := Complex.I * (dedekindLocalWidth K d q : ℂ)
  have hu : HasDerivAt (higherLocalArc K d q) (u * c) z := by
    simpa [u, c] using hasDerivAt_higherLocalArc K d q z
  have hp : HasDerivAt
      (fun w => analyticPhaseCoeffDeriv q (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) (higherLocalArc K d q w))
      (analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * (u * c)) z :=
    (hasDerivAt_analyticPhaseCoeffDeriv
      (q := q) (a := (Real.pi : ℂ))
      (b := ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)) hslit).comp z hu
  have hv : HasDerivAt (fun w => higherLocalArc K d q w * c) ((u * c) * c) z :=
    hu.mul_const c
  have hraw := (hp.mul hv).div_const
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp [higherAnalyticPhaseSecond, u, c]
    push_cast
    ring
  · filter_upwards [] with w
    dsimp [higherAnalyticPhaseFirst]

/-- The arc `higherLocalArc` passes through the saddle point at `0`. -/
theorem higherLocalArc_zero (d : ℕ) (q : ℝ) :
    higherLocalArc K d q 0 = dedekindSaddle K d q := by
  simp [higherLocalArc]

/-- For `q` in the saddle range, the Dedekind saddle point lies in the lower half-plane. -/
theorem dedekindSaddle_im_lt_zero (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
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
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hrange.1]) (by linarith [hrange.2])
  nlinarith [sq_pos_of_pos hr]

/-- For `q` in the saddle range, the local phase agrees near `0` with `higherAnalyticPhase`
restricted to the real line. -/
theorem localPhase_eventuallyEq_higher
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    (dedekindLocalPhase K d q : ℝ → ℂ) =ᶠ[𝓝 0]
      (fun y : ℝ => higherAnalyticPhase K d q (y : ℂ)) := by
  have huim := dedekindSaddle_im_lt_zero K d hd hq
  have hev : ∀ᶠ y : ℝ in 𝓝 0, (higherLocalArc K d q (y : ℂ)).im < 0 :=
    (hasDerivAt_higherLocalArc K d q 0).comp_ofReal.continuousAt.eventually
      ((isOpen_lt continuous_im continuous_const).mem_nhds
        (by simpa [higherLocalArc_zero] using huim))
  filter_upwards [hev] with y hy
  rw [dedekindLocalPhase, higherAnalyticPhase]
  change
    (saddlePhaseAtLambda (dedekindScaleLambda K d) q
        (higherLocalArc K d q (y : ℂ)) -
      saddlePhaseAtLambda (dedekindScaleLambda K d) q
        (dedekindSaddle K d q)) / _ = _
  rw [saddlePhaseAtLambda_eq_analytic_of_im_neg _ _ hy,
    saddlePhaseAtLambda_eq_analytic_of_im_neg _ _ huim]

/-- For `q` in the saddle range with nonzero Hessian `H` and positive local width, the second
derivative of the local phase at `0` is `-(H / ‖H‖)`. -/
theorem dedekindLocalPhase_taylor
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hD : 0 < ‖dedekindSaddleHessian K d q‖)
    (hℓ : 0 < dedekindLocalWidth K d q) :
    iteratedDeriv 2 (dedekindLocalPhase K d q) 0 =
      -(dedekindSaddleHessian K d q /
        (‖dedekindSaddleHessian K d q‖ : ℂ)) := by
  have heq := localPhase_eventuallyEq_higher K d hd hq
  rw [Filter.EventuallyEq.iteratedDeriv_eq 2 heq]
  have huim := dedekindSaddle_im_lt_zero K d hd hq
  have hslit0 : dedekindSaddle K d q ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr huim.ne)
  have hslit : higherLocalArc K d q 0 ∈ Complex.slitPlane := by rwa [higherLocalArc_zero]
  have hslit_ev : ∀ᶠ y : ℝ in 𝓝 0, higherLocalArc K d q (y : ℂ) ∈ Complex.slitPlane :=
    (hasDerivAt_higherLocalArc K d q 0).comp_ofReal.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hder : deriv (fun y : ℝ => higherAnalyticPhase K d q (y : ℂ)) =ᶠ[𝓝 0]
      (fun y : ℝ => higherAnalyticPhaseFirst K d q (y : ℂ)) := by
    filter_upwards [hslit_ev] with y hy
    exact (hasDerivAt_higherAnalyticPhase K d q hy).comp_ofReal.deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, hder.deriv_eq,
    (hasDerivAt_higherAnalyticPhaseFirst K d q hslit).comp_ofReal.deriv]
  have hphase1 : analyticPhaseCoeffDeriv q (Real.pi : ℂ)
      ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)
      (dedekindSaddle K d q) = 0 := by
    have hs := dedekindSaddle_stationary K d hd hq
    change deriv (saddlePhaseAtLambda (dedekindScaleLambda K d) q)
      (dedekindSaddle K d q) = 0 at hs
    have hev : saddlePhaseAtLambda (dedekindScaleLambda K d) q =ᶠ[
        𝓝 (dedekindSaddle K d q)]
        analyticPhaseCoeff q (Real.pi : ℂ)
          ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) := by
      filter_upwards [
        (isOpen_lt Complex.continuous_im continuous_const).mem_nhds huim]
          with z hz
      exact saddlePhaseAtLambda_eq_analytic_of_im_neg _ _ hz
    rwa [((hasDerivAt_analyticPhaseCoeff (q := q) (a := (Real.pi : ℂ))
      (b := ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)) hslit0).congr_of_eventuallyEq
        hev).deriv] at hs
  rw [higherAnalyticPhaseSecond, higherLocalArc_zero, hphase1, zero_mul, add_zero]
  rw [← iteratedDeriv_two_saddlePhaseAtLambda_of_im_neg (dedekindScaleLambda K d) q huim]
  field_simp [hD.ne', hℓ.ne']
  unfold dedekindSaddleHessian dedekindSaddlePhase
  rw [Complex.I_sq]
  push_cast
  ring

/-- The third derivative of the analytic phase coefficient with parameters `π` and `π / Λ`. -/
noncomputable def higherCoeffDeriv3 (Λ : ℝ) (u : ℂ) : ℂ :=
  (-2 + 3 * (Real.pi : ℂ) * analyticLowerSqrt u / 8 +
      3 * ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt u * Complex.log u / 8 -
      ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt u / 4) / u ^ 3

/-- On the slit plane, `analyticPhaseCoeffDeriv2` with parameters `π` and `π / Λ` has derivative
`higherCoeffDeriv3 Λ`. -/
theorem hasDerivAt_coeffDeriv2 {Λ : ℝ} {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticPhaseCoeffDeriv2 (Real.pi : ℂ) ((Real.pi / Λ : ℝ) : ℂ))
      (higherCoeffDeriv3 Λ u) u := by
  have hu0 := Complex.slitPlane_ne_zero hu
  have hs := hasDerivAt_analyticLowerSqrt_atLambda hu
  have hl := Complex.hasDerivAt_log hu
  let n : ℂ → ℂ := fun z => 1 - (Real.pi : ℂ) * analyticLowerSqrt z / 4 -
    ((Real.pi / Λ : ℝ) : ℂ) * analyticLowerSqrt z * Complex.log z / 4
  have hn : HasDerivAt n
      (-(Real.pi : ℂ) * (analyticLowerSqrt u / (2 * u)) / 4 -
        ((Real.pi / Λ : ℝ) : ℂ) *
          ((analyticLowerSqrt u / (2 * u)) * Complex.log u +
            analyticLowerSqrt u / u) / 4) u := by
    have hraw := (((hasDerivAt_const u (1 : ℂ)).sub
      ((hs.const_mul (Real.pi : ℂ)).div_const 4)).sub
      (((hs.mul hl).const_mul ((Real.pi / Λ : ℝ) : ℂ)).div_const 4))
    apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
    · field_simp [hu0]
      ring
    · filter_upwards [] with z
      dsimp [n]
      ring
  have hd : HasDerivAt (fun z : ℂ => z ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hraw := hn.div hd (pow_ne_zero 2 hu0)
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp [n, higherCoeffDeriv3, analyticPhaseCoeffDeriv2]
    field_simp [hu0]
    ring
  · filter_upwards [] with z
    dsimp [n, analyticPhaseCoeffDeriv2]

/-- The third complex derivative of `higherAnalyticPhase`. -/
noncomputable def higherAnalyticPhaseThird
    (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  let u := higherLocalArc K d q z
  let c := Complex.I * (dedekindLocalWidth K d q : ℂ)
  (higherCoeffDeriv3 (dedekindScaleLambda K d) u * (u * c) ^ 3 +
      3 * analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * (u * c) ^ 2 * c +
      analyticPhaseCoeffDeriv q (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * (u * c ^ 3)) /
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))

/-- Where the arc lies in the slit plane, `higherAnalyticPhaseSecond` has derivative
`higherAnalyticPhaseThird`. -/
theorem hasDerivAt_higherAnalyticPhaseSecond
    (d : ℕ) (q : ℝ) {z : ℂ}
    (hslit : higherLocalArc K d q z ∈ Complex.slitPlane) :
    HasDerivAt (higherAnalyticPhaseSecond K d q)
      (higherAnalyticPhaseThird K d q z) z := by
  let u := higherLocalArc K d q z
  let c : ℂ := Complex.I * (dedekindLocalWidth K d q : ℂ)
  let v : ℂ := u * c
  have hu : HasDerivAt (higherLocalArc K d q) v z := by
    simpa [u, c, v] using hasDerivAt_higherLocalArc K d q z
  have hp1 : HasDerivAt
      (fun w => analyticPhaseCoeffDeriv q (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) (higherLocalArc K d q w))
      (analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) u * v) z :=
    (hasDerivAt_analyticPhaseCoeffDeriv
      (q := q) (a := (Real.pi : ℂ))
      (b := ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ)) hslit).comp z hu
  have hp2 : HasDerivAt
      (fun w => analyticPhaseCoeffDeriv2 (Real.pi : ℂ)
        ((Real.pi / dedekindScaleLambda K d : ℝ) : ℂ) (higherLocalArc K d q w))
      (higherCoeffDeriv3 (dedekindScaleLambda K d) u * v) z :=
    (hasDerivAt_coeffDeriv2 (Λ := dedekindScaleLambda K d) hslit).comp z hu
  have hv : HasDerivAt (fun w => higherLocalArc K d q w * c) (v * c) z := hu.mul_const c
  have hv2 : HasDerivAt (fun w => (higherLocalArc K d q w * c) ^ 2)
      (2 * v * (v * c)) z := by
    have h := hv.mul hv
    apply (h.congr_of_eventuallyEq ?_).congr_deriv
    · ring
    · filter_upwards [] with w
      simp only [Pi.mul_apply]
      ring
  have huc2 : HasDerivAt (fun w => higherLocalArc K d q w * c ^ 2)
      (v * c ^ 2) z := hu.mul_const (c ^ 2)
  have hraw := ((hp2.mul hv2).add (hp1.mul huc2)).div_const
    (((‖dedekindSaddleHessian K d q‖ * dedekindLocalWidth K d q ^ 2 : ℝ) : ℂ))
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp [higherAnalyticPhaseThird, higherAnalyticPhaseSecond, u, c, v]
    push_cast
    ring
  · filter_upwards [] with w
    dsimp [higherAnalyticPhaseSecond]

/-- For all sufficiently large `d` and every `q` in the saddle range, the second derivative of the
local phase at `0` is `-(H / ‖H‖)`, where `H` is the saddle Hessian. -/
theorem eventually_dedekindLocalPhase_taylor :
    ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
      dedekindEdgeQ K d < q → q ≤ dedekindScaleT K d →
      iteratedDeriv 2 (dedekindLocalPhase K d q) 0 =
        -(dedekindSaddleHessian K d q /
          (‖dedekindSaddleHessian K d q‖ : ℂ)) := by
  obtain ⟨D, hD1, hb⟩ := eventually_dedekindSaddleHessian_norm_bounds K
  filter_upwards [eventually_ge_atTop D] with d hd
  intro q hedge hqT
  have hd1 : 1 ≤ d := hD1.trans hd
  have hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hedge, hqT⟩
  have hrange := dedekindSaddle_inverse_range K d hd1 hq
  have hbounds := hb d hd (dedekindSaddleAngle K d q) hrange
  rw [dedekindSaddle_inverse K d hd1 hq] at hbounds
  have hsin : 0 < Real.sin (dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi hrange.1
      (hrange.2.trans (by linarith [Real.pi_pos]))
  have hnorm : 0 < ‖dedekindSaddleHessian K d q‖ := by nlinarith
  have hcos : 0 < Real.cos (dedekindSaddleAngle K d q) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hrange.2⟩
  have hwidth : 0 < dedekindLocalWidth K d q := by
    unfold dedekindLocalWidth dedekindLocalEpsilon
    exact mul_pos (by norm_num) (lt_min hrange.1 hcos)
  exact dedekindLocalPhase_taylor K d hd1 hq hnorm hwidth

end

end RiemannJensen
