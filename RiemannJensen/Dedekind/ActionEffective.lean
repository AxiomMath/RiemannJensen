module

public import RiemannJensen.Dedekind.SaddleImplicitCalculus
public import RiemannJensen.Dedekind.SaddleHessianEventual

/-!
# Dedekind saddle action and effective Gaussian parameter

For a number field `K` and degree `d`, this file computes the imaginary part of the Dedekind
saddle phase on the lower arc, the derivative of the Dedekind saddle action in `q`, and lower
bounds for the Dedekind effective Gaussian parameter on the counting window.

## Main results

* `dedekind_action_raw`: the imaginary part of the Dedekind saddle phase at `r² e^{-2iα}`.
* `dedekind_action_derivative`: the derivative of `dedekindSaddleAction` on the open branch.
* `dedekind_effective_edge`: near the edge, the effective parameter is bounded below by a
  multiple of `d (q - q_edge)^{3/2}`.
* `dedekind_effective_tail`: a lower bound by an absolute multiple of `d/q` away from the edge.
* `dedekind_effective_window`: the uniform lower bound on the Dedekind counting window.
* `tendsto_dedekindScaleT_atTop`: the Dedekind saddle scale tends to infinity.
* `dedekind_window_nonempty`: the Dedekind counting window is eventually nonempty.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter
open scoped Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The imaginary part of `dedekindSaddlePhase K d q` at the lower-arc point `r² e^{-2iα}`,
for `0 < r` and `0 ≤ α ≤ π / 2`. -/
theorem dedekind_action_raw (d : ℕ) (q r α : ℝ) (hr : 0 < r)
    (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi / 2) :
    (dedekindSaddlePhase K d q
      (((r ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ)))).im =
      q * r ^ 2 * Real.sin (2 * α) - Real.pi * r * Real.sin α -
        (2 * Real.pi * r / dedekindScaleLambda K d) *
          (α * Real.cos α + Real.log r * Real.sin α) + 2 * α := by
  simpa only [dedekindSaddlePhase] using
    saddlePhaseAtLambda_im_sq_exp_neg_two_mul_I
      (dedekindScaleLambda K d) q r α hr hα0 hαpi

/-- Derivative of `sinRatio` away from the zeros of `sin`. -/
theorem hasDerivAt_sinRatio {α : ℝ} (hs : Real.sin α ≠ 0) :
    HasDerivAt sinRatio ((Real.sin α - α * Real.cos α) / Real.sin α ^ 2) α := by
  have hα : α ≠ 0 := by
    rintro rfl
    simp at hs
  have enez : ∀ᶠ x in 𝓝 α, x ≠ 0 := continuousAt_id.eventually_ne hα
  refine (((hasDerivAt_id α).div (Real.hasDerivAt_sin α) hs).congr_of_eventuallyEq
    ?_).congr_deriv ?_
  · filter_upwards [enez] with x hx
    rw [sinRatio_of_ne hx]
    rfl
  · simp [id]

/-- The radial saddle equation, differentiated along the open Dedekind branch. -/
theorem dedekindSaddle_radial_deriv_eq_zero (d : ℕ) (hd : 1 ≤ d) {q α r ap rp : ℝ}
    (hq : q ∈ Ioo (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hαq : dedekindSaddleAngle K d q = α) (hrα : dedekindSaddleRadius K d α = r)
    (hr : 0 < r) (hs : 0 < Real.sin α)
    (hA : HasDerivAt (dedekindSaddleAngle K d) ap q)
    (hR : HasDerivAt (fun y => dedekindSaddleRadius K d (dedekindSaddleAngle K d y)) rp q) :
    (-dedekindScaleLambda K d * Real.sin α / (saddleKappa * r) +
        (Real.sin α * Real.cos α - α) / Real.sin α ^ 2) * ap +
      (-dedekindScaleLambda K d * Real.cos α / (saddleKappa * r ^ 2) - 1 / r) * rp = 0 := by
  subst hαq hrα
  let A := dedekindSaddleAngle K d
  let R := fun y => dedekindSaddleRadius K d (A y)
  let α := A q
  let r := R q
  let Λ := dedekindScaleLambda K d
  have hA : HasDerivAt A ap q := hA
  have hR : HasDerivAt R rp q := hR
  have hr : 0 < r := hr
  have hs : 0 < Real.sin α := hs
  let Fa := -Λ * Real.sin α / (saddleKappa * r) +
    (Real.sin α * Real.cos α - α) / Real.sin α ^ 2
  let Fr := -Λ * Real.cos α / (saddleKappa * r ^ 2) - 1 / r
  have hcosA := (Real.hasDerivAt_cos α).comp q hA
  have hsinA := (Real.hasDerivAt_sin α).comp q hA
  have hterm₁ := (((hasDerivAt_const q Λ).mul hcosA).div
    ((hasDerivAt_const q saddleKappa).mul hR)
    (mul_ne_zero saddleKappa_pos.ne' hr.ne'))
  have hterm₂ := (hA.mul hcosA).div hsinA hs.ne'
  have hlog := (Real.hasDerivAt_log hr.ne').comp q hR
  have hcalc := (((hterm₁.add hterm₂).sub_const (Λ / 2)).sub_const 1).sub hlog
  have hcalc' : HasDerivAt (fun y =>
      Λ * Real.cos (A y) / (saddleKappa * R y) +
        A y * Real.cos (A y) / Real.sin (A y) - Λ / 2 - 1 - Real.log (R y))
      (Fa * ap + Fr * rp) q := by
    refine (hcalc.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with y
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Function.comp_apply]
    · simp only [Pi.mul_apply, Function.comp_apply]
      rw [show A q = α by rfl, show R q = r by rfl]
      dsimp only [Fa, Fr]
      field_simp
      rw [show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by
        nlinarith [Real.cos_sq_add_sin_sq α]]
      ring
  have ezero : ∀ᶠ y in 𝓝 q,
      Λ * Real.cos (A y) / (saddleKappa * R y) +
        A y * Real.cos (A y) / Real.sin (A y) - Λ / 2 - 1 - Real.log (R y) = 0 := by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with y hy
    have hyrange := dedekindSaddle_inverse_range K d hd (Ioo_subset_Ioc_self hy)
    have hchar := dedekindSaddleRadius_characterization K d hd
      ⟨hyrange.1.le, hyrange.2.le⟩
    rw [show alphaCot (A y) = A y * Real.cos (A y) / Real.sin (A y) by
      rw [alphaCot_of_ne hyrange.1.ne']] at hchar
    dsimp [Λ, R, A, saddleKappa]
    rw [saddleKappa] at hchar
    linarith
  exact hcalc'.unique ((hasDerivAt_const q 0).congr_of_eventuallyEq ezero)

/-- The level equation `dedekindSaddleQ K d (dedekindSaddleAngle K d q) = q`, differentiated
along the open Dedekind branch. -/
theorem dedekindSaddle_level_deriv_eq_one (d : ℕ) (hd : 1 ≤ d) {q α r ap rp : ℝ}
    (hq : q ∈ Ioo (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hαq : dedekindSaddleAngle K d q = α) (hrα : dedekindSaddleRadius K d α = r)
    (hr : 0 < r) (hs : 0 < Real.sin α)
    (hA : HasDerivAt (dedekindSaddleAngle K d) ap q)
    (hR : HasDerivAt (fun y => dedekindSaddleRadius K d (dedekindSaddleAngle K d y)) rp q) :
    (2 * saddleKappa / dedekindScaleLambda K d) *
          (Real.sin α - α * Real.cos α) / (Real.sin α ^ 2 * r) * ap +
      (-2 / r ^ 3 -
          (2 * saddleKappa / dedekindScaleLambda K d) * α / (Real.sin α * r ^ 2)) * rp = 1 := by
  subst hαq hrα
  let A := dedekindSaddleAngle K d
  let R := fun y => dedekindSaddleRadius K d (A y)
  let α := A q
  let r := R q
  let Λ := dedekindScaleLambda K d
  have hA : HasDerivAt A ap q := hA
  have hR : HasDerivAt R rp q := hR
  have hr : 0 < r := hr
  have hs : 0 < Real.sin α := hs
  have hα : α ≠ 0 := by
    rintro h
    simp [h] at hs
  have hΛ : 0 < Λ := dedekindScaleLambda_pos K d hd
  let Qa := (2 * saddleKappa / Λ) *
    (Real.sin α - α * Real.cos α) / (Real.sin α ^ 2 * r)
  let Qr := -2 / r ^ 3 -
    (2 * saddleKappa / Λ) * α / (Real.sin α * r ^ 2)
  have hRinv := hR.inv hr.ne'
  have hlevelCalc := (hRinv.pow 2).add
    (((hasDerivAt_const q (2 * saddleKappa / Λ)).mul
      ((hasDerivAt_sinRatio hs.ne').comp q hA)).mul hRinv)
  have hlevelDeriv : HasDerivAt (fun y => dedekindSaddleQ K d (A y))
      (Qa * ap + Qr * rp) q := by
    refine (hlevelCalc.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with y
      simp only [dedekindSaddleQ, saddleQAtLambda, R, A, Λ,
        dedekindSaddleRadius, Pi.add_apply, Pi.mul_apply, Pi.inv_apply,
        Function.comp_apply]
      congr 1
    · simp only [Pi.mul_apply, Pi.inv_apply, Function.comp_apply]
      rw [show A q = α by rfl, show R q = r by rfl, sinRatio_of_ne hα]
      dsimp only [Qa, Qr]
      norm_num
      field_simp [hr.ne', hs.ne', hΛ.ne']
      ring
  have elevel : ∀ᶠ y in 𝓝 q, dedekindSaddleQ K d (A y) = y := by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with y hy
    exact dedekindSaddle_inverse K d hd ⟨hy.1, hy.2.le⟩
  exact hlevelDeriv.unique ((hasDerivAt_id q).congr_of_eventuallyEq elevel)

/-- The derivative of the Dedekind saddle action, in terms of the derivatives `ap` of the saddle
angle and `rp` of the saddle radius. -/
theorem hasDerivAt_dedekindSaddleAction_of_hasDerivAt (d : ℕ) (hd : 1 ≤ d) {q α r ap rp : ℝ}
    (hq : q ∈ Ioo (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hαq : dedekindSaddleAngle K d q = α) (hrα : dedekindSaddleRadius K d α = r)
    (hA : HasDerivAt (dedekindSaddleAngle K d) ap q)
    (hR : HasDerivAt (fun y => dedekindSaddleRadius K d (dedekindSaddleAngle K d y)) rp q) :
    HasDerivAt (dedekindSaddleAction K d)
      ((2 - 2 * Real.cos (2 * α) +
          (2 * Real.pi / dedekindScaleLambda K d) * r * (α * Real.sin α)) * ap +
        (2 * Real.pi / dedekindScaleLambda K d) * (Real.sin α - α * Real.cos α) * rp) q := by
  subst hαq hrα
  let A := dedekindSaddleAngle K d
  let R := fun y => dedekindSaddleRadius K d (A y)
  let α := A q
  let r := R q
  let Λ := dedekindScaleLambda K d
  have hA : HasDerivAt A ap q := hA
  have hR : HasDerivAt R rp q := hR
  let Sa := 2 - 2 * Real.cos (2 * α) +
    (2 * Real.pi / Λ) * r * (α * Real.sin α)
  let Sr := (2 * Real.pi / Λ) *
    (Real.sin α - α * Real.cos α)
  have hsin2A := (Real.hasDerivAt_sin (2 * α)).comp q (hA.const_mul 2)
  have hsinA := (Real.hasDerivAt_sin α).comp q hA
  have hcosA := (Real.hasDerivAt_cos α).comp q hA
  have hcorr := hsinA.sub (hA.mul hcosA)
  have hmain := (hA.const_mul 2).sub hsin2A
  have hcoef := (hasDerivAt_const q (2 * Real.pi / Λ)).mul hR
  have hSraw := hmain.add (hcoef.mul hcorr)
  have hSformula : HasDerivAt (fun y =>
      2 * A y - Real.sin (2 * A y) +
        (2 * Real.pi * R y / Λ) *
          (Real.sin (A y) - A y * Real.cos (A y)))
      (Sa * ap + Sr * rp) q := by
    refine (hSraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with y
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
      ring
    · simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
      dsimp [Sa, Sr, α, r]
      ring
  have eaction : ∀ᶠ y in 𝓝 q,
      dedekindSaddleAction K d y =
        2 * A y - Real.sin (2 * A y) +
          (2 * Real.pi * R y / Λ) *
            (Real.sin (A y) - A y * Real.cos (A y)) := by
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with y hy
    simpa [A, R, Λ] using
      dedekindSaddle_action_formula K d hd (Ioo_subset_Ioc_self hy)
  exact hSformula.congr_of_eventuallyEq eaction

/-- Eliminating `ap` and `rp` between the differentiated radial and level equations: the
saddle-action derivative equals `r² sin 2α`. -/
theorem saddle_action_deriv_eq {Λ r α ap rp : ℝ} (hΛ : 0 < Λ) (hr : 0 < r)
    (hs : 0 < Real.sin α) (hc : 0 < Real.cos α)
    (hrad : (-Λ * Real.sin α / (saddleKappa * r) +
        (Real.sin α * Real.cos α - α) / Real.sin α ^ 2) * ap +
      (-Λ * Real.cos α / (saddleKappa * r ^ 2) - 1 / r) * rp = 0)
    (hlevel : (2 * saddleKappa / Λ) * (Real.sin α - α * Real.cos α) / (Real.sin α ^ 2 * r) * ap +
      (-2 / r ^ 3 - (2 * saddleKappa / Λ) * α / (Real.sin α * r ^ 2)) * rp = 1) :
    (2 - 2 * Real.cos (2 * α) + (2 * Real.pi / Λ) * r * (α * Real.sin α)) * ap +
        (2 * Real.pi / Λ) * (Real.sin α - α * Real.cos α) * rp =
      r ^ 2 * Real.sin (2 * α) := by
  let Fa := -Λ * Real.sin α / (saddleKappa * r) +
    (Real.sin α * Real.cos α - α) / Real.sin α ^ 2
  let Fr := -Λ * Real.cos α / (saddleKappa * r ^ 2) - 1 / r
  let Qa := (2 * saddleKappa / Λ) *
    (Real.sin α - α * Real.cos α) / (Real.sin α ^ 2 * r)
  let Qr := -2 / r ^ 3 -
    (2 * saddleKappa / Λ) * α / (Real.sin α * r ^ 2)
  let Sa := 2 - 2 * Real.cos (2 * α) +
    (2 * Real.pi / Λ) * r * (α * Real.sin α)
  let Sr := (2 * Real.pi / Λ) *
    (Real.sin α - α * Real.cos α)
  let target := r ^ 2 * Real.sin (2 * α)
  have hrad : Fa * ap + Fr * rp = 0 := hrad
  have hlevel : Qa * ap + Qr * rp = 1 := hlevel
  have hFr : Fr < 0 := by
    have hk := saddleKappa_pos
    have hfirst : -Λ * Real.cos α / (saddleKappa * r ^ 2) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hΛ) hc) (by positivity)
    linarith [show 0 < 1 / r by positivity]
  have hcoeff : Fr * Sa - Sr * Fa = target * (Fr * Qa - Qr * Fa) := by
    dsimp [Fa, Fr, Qa, Qr, Sa, Sr, target]
    field_simp [hΛ.ne', hr.ne', hs.ne', Real.pi_ne_zero]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    have hc2 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq α]
    linear_combination
      -(2 * Real.sin α ^ 2 * Real.pi ^ 2 * r ^ 2 * α +
        4 * Real.sin α ^ 2 * Λ * Real.cos α * Real.pi * r * α -
        4 * Real.sin α ^ 3 * Λ * Real.pi * r -
        8 * Real.sin α ^ 3 * Λ ^ 2 * Real.cos α) * hc2
  have hleft : Fr * (Sa * ap + Sr * rp - target) = 0 := by
    calc
      Fr * (Sa * ap + Sr * rp - target)
          = (Fr * Sa - Sr * Fa) * ap - Fr * target := by
              linear_combination Sr * hrad
      _ = target * ((Fr * Qa - Qr * Fa) * ap - Fr) := by
            rw [hcoeff]
            ring
      _ = 0 := by
            rw [show (Fr * Qa - Qr * Fa) * ap - Fr = 0 by
              linear_combination Fr * hlevel - Qr * hrad]
            ring
  exact sub_eq_zero.mp (mul_eq_zero.mp hleft |>.resolve_left hFr.ne)

/-- Exact derivative of the Dedekind saddle action on its open branch. -/
theorem dedekind_action_derivative (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioo (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    HasDerivAt (dedekindSaddleAction K d)
      (dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 *
        Real.sin (2 * dedekindSaddleAngle K d q)) q := by
  have hα := dedekindSaddle_inverse_range K d hd (Ioo_subset_Ioc_self hq)
  have hr := dedekindSaddleRadius_pos K d hd ⟨hα.1.le, hα.2.le⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hA_diff : DifferentiableAt ℝ (dedekindSaddleAngle K d) q :=
    (dedekind_saddle_angle_differentiable K d hd q hq).differentiableAt
      (Ioo_mem_nhds hq.1 hq.2)
  have hA := hA_diff.hasDerivAt
  have hR := ((differentiableAt_dedekindSaddleRadius K d hd hα).comp q hA_diff).hasDerivAt
  exact (hasDerivAt_dedekindSaddleAction_of_hasDerivAt K d hd hq rfl rfl hA hR).congr_deriv <|
    saddle_action_deriv_eq (dedekindScaleLambda_pos K d hd) hr hs hc
      (dedekindSaddle_radial_deriv_eq_zero K d hd hq rfl rfl hr hs hA hR)
      (dedekindSaddle_level_deriv_eq_one K d hd hq rfl rfl hr hs hA hR)

/-- Geometric lower bound for the Dedekind effective Gaussian parameter. -/
theorem dedekind_effective_geometric (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    (3 / 8 : ℝ) * dedekindLocalEpsilon ^ 2 * d *
        Real.sin (dedekindSaddleAngle K d q) *
        min (dedekindSaddleAngle K d q)
          (Real.cos (dedekindSaddleAngle K d q)) ^ 2 ≤
      dedekindEffectiveN K d q := by
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hD : (3 / 8 : ℝ) * Real.sin (dedekindSaddleAngle K d q) ≤
      ‖dedekindSaddleHessian K d q‖ := by
    simpa only [hinv] using (dedekindSaddleHessian_norm_bounds K d hd hΛ hrange).1
  calc
    (3 / 8 : ℝ) * dedekindLocalEpsilon ^ 2 * d *
          Real.sin (dedekindSaddleAngle K d q) *
          min (dedekindSaddleAngle K d q)
            (Real.cos (dedekindSaddleAngle K d q)) ^ 2
        = d * ((3 / 8 : ℝ) * Real.sin (dedekindSaddleAngle K d q)) *
            (dedekindLocalEpsilon ^ 2 *
              min (dedekindSaddleAngle K d q)
                (Real.cos (dedekindSaddleAngle K d q)) ^ 2) := by ring
    _ ≤ d * ‖dedekindSaddleHessian K d q‖ *
            (dedekindLocalEpsilon ^ 2 *
              min (dedekindSaddleAngle K d q)
                (Real.cos (dedekindSaddleAngle K d q)) ^ 2) := by gcongr
    _ = dedekindEffectiveN K d q := by
      rw [dedekindEffectiveN, dedekindLocalWidth]
      ring

/-- Near the edge, the Dedekind effective parameter has the `3/2` lower bound. -/
theorem dedekind_effective_edge (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hsmall : dedekindSaddleAngle K d q ≤ 1 / 2) :
    (dedekindLocalEpsilon ^ 2 / 96) * d * (q - dedekindEdgeQ K d) *
        Real.sqrt (q - dedekindEdgeQ K d) ≤ dedekindEffectiveN K d q := by
  let α := dedekindSaddleAngle K d q
  let t := q - dedekindEdgeQ K d
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hαpi : α ∈ Icc 0 (Real.pi / 2) := ⟨hrange.1.le, hrange.2.le⟩
  have hαsmall : α ∈ Icc 0 (1 / 2 : ℝ) := ⟨hrange.1.le, hsmall⟩
  have ht0 : 0 ≤ t := sub_nonneg.mpr hq.1.le
  have hcos : α ≤ Real.cos α := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := α)
    have hsq := pow_le_pow_left₀ hαsmall.1 hαsmall.2 2
    norm_num at hsq
    nlinarith
  have hmin : min α (Real.cos α) = α := min_eq_left hcos
  have hsin : α / 2 ≤ Real.sin α := by
    have := half_mul_le_sin hαpi
    nlinarith
  have hedge := dedekindSaddleQ_sub_edge_upper K d hΛ hαsmall
  rw [hinv] at hedge
  have ht : t ≤ 6 * α ^ 2 := by simpa [t] using hedge
  have hsqrt : Real.sqrt t ≤ 3 * α := by
    have hsqrt0 := Real.sqrt_nonneg t
    have hsqrt_sq := Real.sq_sqrt ht0
    nlinarith [sq_nonneg (Real.sqrt t - 3 * α)]
  have htsqrt : t * Real.sqrt t ≤ 18 * α ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg t)
    have h₂ := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (sq_nonneg α))
    nlinarith
  have hgeom := dedekind_effective_geometric K d hd hΛ hq
  rw [show dedekindSaddleAngle K d q = α by rfl, hmin] at hgeom
  have hεd : 0 ≤ dedekindLocalEpsilon ^ 2 * d := by positivity
  have hgeom' : (3 / 16 : ℝ) * dedekindLocalEpsilon ^ 2 * d * α ^ 3 ≤
      dedekindEffectiveN K d q := by
    have hm := mul_le_mul_of_nonneg_left hsin hεd
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left htsqrt hεd
  dsimp [α, t] at hgeom' hmul ⊢
  nlinarith

/-- If `π r / 16 ≤ c` and `1 ≤ q r²` with `q, r ≥ 0`, then `1 / 64 ≤ q c²`. -/
theorem one_div_sixtyFour_le_mul_sq {q r c : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hc : Real.pi * r / 16 ≤ c) (hqr : 1 ≤ q * r ^ 2) : 1 / 64 ≤ q * c ^ 2 := by
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi * r / 16) hc 2
  have hqmul := mul_le_mul_of_nonneg_left hsq hq
  have hscaled := mul_le_mul_of_nonneg_left hqr (by norm_num : (0 : ℝ) ≤ 1 / 64)
  have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [mul_nonneg hq (sq_nonneg r)]

/-- Every point of the Dedekind branch interval is positive. -/
theorem dedekindSaddle_pos_of_mem_Ioc (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) : 0 < q := by
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd ⟨hrange.1.le, hrange.2.le⟩
  rw [dedekindSaddle_inverse K d hd hq] at hqr
  nlinarith [sq_nonneg (dedekindSaddleRadius K d (dedekindSaddleAngle K d q))]

/-- Away from the edge, the Dedekind effective parameter is bounded below by
an absolute multiple of `d/q`. -/
theorem dedekind_effective_tail (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hfield : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d))
    (hbig : 1 / 2 ≤ dedekindSaddleAngle K d q) :
    (dedekindLocalEpsilon ^ 2 / 3000) * d / q ≤ dedekindEffectiveN K d q := by
  let α := dedekindSaddleAngle K d q
  let r := dedekindSaddleRadius K d α
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hαpi : α ∈ Icc 0 (Real.pi / 2) := ⟨hrange.1.le, hrange.2.le⟩
  have hcos0 : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hrange.1, Real.pi_pos], hrange.2.le⟩
  have hsin : (1 / 4 : ℝ) ≤ Real.sin α := by
    have hs := half_mul_le_sin hαpi
    dsimp [α] at hbig ⊢
    nlinarith
  have hmin : Real.cos α / 2 ≤ min α (Real.cos α) :=
    le_min (by nlinarith [Real.cos_le_one α]) (by nlinarith)
  have hr : 0 < r := by
    simpa [r] using dedekindSaddleRadius_pos K d hd hαpi
  have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd hαpi
  rw [hinv] at hqr
  have hq0 := dedekindSaddle_pos_of_mem_Ioc K d hd hq
  have hcosr : Real.pi * r / 16 ≤ Real.cos α := by
    have hqT : dedekindSaddleQ K d α ≤ dedekindScaleT K d := hinv.trans_le hq.2
    have hΛlog : 2 * (1 + Real.log 2) ≤ dedekindScaleLambda K d := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2), Real.two_le_pi]
    simpa [r] using (dedekindSaddleCos_radius_comparison K d hΛlog
      (dedekindScaleT_pos K d hd)
      (log_dedekindScaleT_le_three_mul_lambda_div_four K d hd hfield) hαpi hqT).1
  have hqcos := one_div_sixtyFour_le_mul_sq hq0.le hr.le hcosr hqr
  have hgeom := dedekind_effective_geometric K d hd hΛ hq
  have hminsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.cos α / 2) hmin 2
  have hεd : 0 ≤ dedekindLocalEpsilon ^ 2 * d := by positivity
  have hgeom' :
      (3 / 128 : ℝ) * dedekindLocalEpsilon ^ 2 * d * Real.cos α ^ 2 ≤
        dedekindEffectiveN K d q := by
    calc
      (3 / 128 : ℝ) * dedekindLocalEpsilon ^ 2 * d * Real.cos α ^ 2 =
          (3 / 8 : ℝ) * dedekindLocalEpsilon ^ 2 * d * (1 / 4 : ℝ) *
            (Real.cos α / 2) ^ 2 := by ring
      _ ≤ (3 / 8 : ℝ) * dedekindLocalEpsilon ^ 2 * d * Real.sin α *
            (min α (Real.cos α)) ^ 2 := by gcongr
      _ ≤ dedekindEffectiveN K d q := by simpa [α] using hgeom
  apply (div_le_iff₀ hq0).2
  have hgq := mul_le_mul_of_nonneg_right hgeom' hq0.le
  have hqcos' := mul_le_mul_of_nonneg_left hqcos hεd
  nlinarith

/-- The edge and tail bounds combine uniformly on the Dedekind counting window. -/
theorem dedekind_effective_window (M c₀ : ℝ) (hM : 0 < M) (hc₀ : 0 < c₀)
    (hc₀one : c₀ ≤ 1) (d : ℕ) (hd : 2 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (hfield : 4 * (1 + Real.log (dedekindScaleA K)) ≤ dedekindScaleLambda K d)
    {q : ℝ} (hq : q ∈ dedekindCountingWindow K M c₀ d) :
    min
      ((dedekindLocalEpsilon ^ 2 / 96) * d * dedekindEdgeOffset M d *
        Real.sqrt (dedekindEdgeOffset M d))
      ((dedekindLocalEpsilon ^ 2 / 3000) * d /
        dedekindUpperEndpoint K c₀ d) ≤ dedekindEffectiveN K d q := by
  have hd1 : 1 ≤ d := by omega
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast hd)
  have hτ : 0 < dedekindEdgeOffset M d := by
    unfold dedekindEdgeOffset
    positivity
  have hT := dedekindScaleT_pos K d hd1
  have ht : dedekindEdgeOffset M d ≤ q - dedekindEdgeQ K d := by
    unfold dedekindCountingWindow at hq
    linarith [hq.1]
  have hqedge : dedekindEdgeQ K d < q := by linarith
  have hqtop : q ≤ c₀ * dedekindScaleT K d := by
    simpa [dedekindCountingWindow, dedekindUpperEndpoint] using hq.2
  have hqT : q ≤ dedekindScaleT K d :=
    hqtop.trans (by nlinarith)
  have hscale : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hqedge, hqT⟩
  have hq0 := dedekindSaddle_pos_of_mem_Ioc K d hd1 hscale
  have hprod : dedekindEdgeOffset M d * Real.sqrt (dedekindEdgeOffset M d) ≤
      (q - dedekindEdgeQ K d) * Real.sqrt (q - dedekindEdgeQ K d) :=
    mul_le_mul ht (Real.sqrt_le_sqrt ht) (Real.sqrt_nonneg _)
      (sub_nonneg.mpr hqedge.le)
  have hQ : 0 < dedekindUpperEndpoint K c₀ d := by
    unfold dedekindUpperEndpoint
    positivity
  have htailmono : (dedekindLocalEpsilon ^ 2 / 3000) * d /
      dedekindUpperEndpoint K c₀ d ≤
      (dedekindLocalEpsilon ^ 2 / 3000) * d / q :=
    (div_le_div_iff₀ hQ hq0).2 (mul_le_mul_of_nonneg_left hqtop (by positivity))
  by_cases hsmall : dedekindSaddleAngle K d q ≤ 1 / 2
  · have hedgeMono : (dedekindLocalEpsilon ^ 2 / 96) * d *
        dedekindEdgeOffset M d * Real.sqrt (dedekindEdgeOffset M d) ≤
        (dedekindLocalEpsilon ^ 2 / 96) * d *
          (q - dedekindEdgeQ K d) * Real.sqrt (q - dedekindEdgeQ K d) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (by positivity : (0 : ℝ) ≤ dedekindLocalEpsilon ^ 2 / 96 * d)
    exact (min_le_left _ _).trans <| hedgeMono.trans
      (dedekind_effective_edge K d hd1 hΛ hscale hsmall)
  · exact (min_le_right _ _).trans <| htailmono.trans
      (dedekind_effective_tail K d hd1 hΛ hfield hscale (le_of_not_ge hsmall))

/-- The Dedekind saddle scale tends to infinity. -/
theorem tendsto_dedekindScaleT_atTop :
    Tendsto (fun d : ℕ => dedekindScaleT K d) atTop atTop := by
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hΛ : Tendsto (fun d : ℕ => dedekindScaleLambda K d) atTop atTop :=
    tendsto_atTop_mono' _ (eventually_atTop.2 (eventually_log_le_dedekindScaleLambda K)) hlog
  have hcoord : Tendsto (fun d : ℕ => dedekindScaleLambda K d / 2 + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (hΛ.atTop_div_const two_pos)
  have hA : 0 < dedekindScaleA K := by
    unfold dedekindScaleA
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)
  have hmul := (Real.tendsto_exp_atTop.comp hcoord).const_mul_atTop hA
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with d hd
  have hratio : 0 < dedekindScaleT K d / dedekindScaleA K :=
    div_pos (dedekindScaleT_pos K d hd) hA
  simp only [Function.comp_apply]
  rw [dedekindScaleLambda_div_two, sub_add_cancel, Real.exp_log hratio]
  field_simp [hA.ne']

/-- For every fixed positive pair `M,c₀`, the Dedekind counting window is
nonempty for all sufficiently large degrees. -/
theorem dedekind_window_nonempty (M c₀ : ℝ) (hM : 0 < M) (hc₀ : 0 < c₀) :
    ∀ᶠ d : ℕ in atTop, (dedekindCountingWindow K M c₀ d).Nonempty := by
  obtain ⟨Dedge, -, hedge⟩ := eventually_dedekindEdgeQ_le_two K
  filter_upwards [eventually_ge_atTop Dedge,
    tendsto_atTop.1 (tendsto_dedekindScaleT_atTop K) ((2 + M) / c₀),
    eventually_ge_atTop (2 : ℕ)] with d hdedge hT hd
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by positivity
  have hlogpos : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  have hlogle : Real.log (d : ℝ) ≤ d :=
    (Real.log_le_sub_one_of_pos hdpos).trans (by linarith)
  have hratio : Real.log (d : ℝ) / d ≤ 1 := (div_le_one hdpos).2 hlogle
  have hsqrt : Real.sqrt (Real.log (d : ℝ) / d) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hratio
  have hedge2 : dedekindEdgeQ K d ≤ 2 := hedge d hdedge
  have hTc : 2 + M ≤ c₀ * dedekindScaleT K d := by
    simpa [mul_comm] using (div_le_iff₀ hc₀).mp hT
  rw [dedekindCountingWindow, Set.nonempty_Icc]
  unfold dedekindEdgeOffset dedekindUpperEndpoint
  have hm := mul_le_mul_of_nonneg_left hsqrt hM.le
  nlinarith

end

end RiemannJensen
