module

public import RiemannJensen.Analysis.LowerBranchDeriv
public import RiemannJensen.Analysis.SaddleAction
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Exact Hessian formula on the open saddle branch

This file computes the second derivative of `phase` on the open lower half-plane and gives
exact formulae for the real and imaginary parts of `saddleHessian` at the saddle point.

## Implementation notes

The coefficient forced by the definition of `phase` is `π / 4`, not `π / 2`, since
`(sqrt u)'' = -1 / (4 u^(3/2))`; the real and imaginary formulae carry one half of the correction
stated in the paper.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter
open scoped Topology

/-- The explicit value of `u² h''(u)` at `u = r² exp (-2 i α)` forced by
`phase`. -/
noncomputable def explicitSaddleHessian (d : ℕ) (r α : ℝ) : ℂ :=
  1 - (((Real.pi * r / 4 : ℝ) : ℂ) *
    Complex.exp (((-α : ℝ) : ℂ) * Complex.I) *
    (1 + (((2 * Real.log r / scaleLambda d : ℝ) : ℂ) -
      ((2 * α / scaleLambda d : ℝ) : ℂ) * Complex.I)))

/-- Raw real part of the explicit Hessian, before using the saddle equations. -/
theorem explicitSaddleHessian_re (d : ℕ) (r α : ℝ) :
    (explicitSaddleHessian d r α).re =
      1 - Real.pi * r / 4 *
        ((1 + 2 * Real.log r / scaleLambda d) * Real.cos α -
          2 * α / scaleLambda d * Real.sin α) := by
  rw [explicitSaddleHessian, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- Raw imaginary part of the explicit Hessian, before using the saddle equations. -/
theorem explicitSaddleHessian_im (d : ℕ) (r α : ℝ) :
    (explicitSaddleHessian d r α).im =
      Real.pi * r / 4 *
        ((1 + 2 * Real.log r / scaleLambda d) * Real.sin α +
          2 * α / scaleLambda d * Real.cos α) := by
  rw [explicitSaddleHessian, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

/-- If `π r (1 + 2 log r / Λ) = 2 (q r² + 1) cos α - 2 π r / Λ` and
`q r² = 1 + (π / Λ) (α / sin α) r`, then
`1 - (π r / 4) ((1 + 2 log r / Λ) cos α - (2 α / Λ) sin α)` equals
`sin² α + (π r / (2 Λ)) (cos α - α cos (2 α) / sin α)`. -/
theorem hessian_real_algebra (Λ q r α : ℝ) (hΛ : Λ ≠ 0)
    (hsin : Real.sin α ≠ 0)
    (hre : Real.pi * r * (1 + 2 * Real.log r / Λ) =
      2 * (q * r ^ 2 + 1) * Real.cos α - 2 * Real.pi * r / Λ)
    (hq : q * r ^ 2 = 1 + (Real.pi / Λ) * (α / Real.sin α) * r) :
    1 - Real.pi * r / 4 *
        ((1 + 2 * Real.log r / Λ) * Real.cos α -
          2 * α / Λ * Real.sin α) =
      Real.sin α ^ 2 + Real.pi * r / (2 * Λ) *
        (Real.cos α - α * Real.cos (2 * α) / Real.sin α) := by
  calc
    _ = 1 - (Real.pi * r * (1 + 2 * Real.log r / Λ)) *
          Real.cos α / 4 + Real.pi * r * α * Real.sin α / (2 * Λ) := by ring
    _ = 1 - (2 * (q * r ^ 2 + 1) * Real.cos α - 2 * Real.pi * r / Λ) *
          Real.cos α / 4 + Real.pi * r * α * Real.sin α / (2 * Λ) := by rw [hre]
    _ = _ := by
      rw [hq, Real.cos_two_mul]
      field_simp [hΛ, hsin]
      linear_combination 4 * (α * Real.pi * r - 2 * Λ * Real.sin α) * Real.sin_sq_add_cos_sq α

/-- Exact corrected real part on the open saddle branch. -/
theorem explicitSaddleHessian_re_at_saddle (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (explicitSaddleHessian d (saddleRadius d α) α).re =
      Real.sin α ^ 2 +
        Real.pi * saddleRadius d α / (2 * scaleLambda d) *
          (Real.cos α - α * Real.cos (2 * α) / Real.sin α) := by
  rcases hα with ⟨hα0, hαtop⟩
  rw [explicitSaddleHessian_re]
  exact hessian_real_algebra _ _ _ _ (scaleLambda_pos d hd).ne'
    (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])).ne'
    (saddle_real_relation_at_angle d hd ⟨hα0.le, hαtop.le⟩)
    (by rw [saddleQ_mul_radius_sq d hd ⟨hα0.le, hαtop.le⟩, sinRatio_of_ne hα0.ne'])

/-- Exact corrected imaginary part on the open saddle branch. -/
theorem explicitSaddleHessian_im_at_saddle (d : ℕ) (r α : ℝ) :
    (explicitSaddleHessian d r α).im =
      Real.pi * r / 4 *
        ((1 + 2 * Real.log r / scaleLambda d) * Real.sin α +
          2 * α * Real.cos α / scaleLambda d) := by
  rw [explicitSaddleHessian_im]
  ring

/-- In the open lower half-plane the lower square root is the principal
complex square root. -/
theorem lowerSqrt_eq_sqrt_of_im_neg {u : ℂ} (hu : u.im < 0) :
    lowerSqrt u = Complex.sqrt u := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  rw [sqrt_eq_exp hu0]
  unfold lowerSqrt
  rw [lowerArg_eq_arg_of_im_neg hu]
  apply Complex.ext <;> simp [Complex.log, Complex.exp_re, Complex.exp_im, Real.exp_half,
    Real.exp_log (norm_pos_iff.mpr hu0)]

/-- Holomorphic representative of the lower square root on the slit plane. -/
noncomputable def analyticLowerSqrt (u : ℂ) : ℂ :=
  Complex.exp (Complex.log u / 2)

private theorem hasDerivAt_analyticLowerSqrt {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt analyticLowerSqrt (analyticLowerSqrt u / (2 * u)) u :=
  ((Complex.hasDerivAt_log hu).div_const 2).cexp.congr_deriv <| by
    unfold analyticLowerSqrt
    field_simp [Complex.slitPlane_ne_zero hu]

/-- The holomorphic phase which agrees with `phase` in the open lower
half-plane. -/
noncomputable def analyticPhase (d : ℕ) (q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) * u + (Real.pi : ℂ) * analyticLowerSqrt u +
    ((Real.pi / scaleLambda d : ℝ) : ℂ) * analyticLowerSqrt u * Complex.log u -
    Complex.log u

/-- The explicit first derivative of `analyticPhase`. -/
noncomputable def analyticPhaseDeriv (d : ℕ) (q : ℝ) (u : ℂ) : ℂ :=
  -(q : ℂ) + (Real.pi : ℂ) * (analyticLowerSqrt u / (2 * u)) +
    ((Real.pi / scaleLambda d : ℝ) : ℂ) *
      ((analyticLowerSqrt u / (2 * u)) * Complex.log u + analyticLowerSqrt u / u) -
    1 / u

/-- The explicit second derivative of `analyticPhase`. -/
noncomputable def analyticPhaseDeriv2 (d : ℕ) (u : ℂ) : ℂ :=
  (1 - (Real.pi : ℂ) * analyticLowerSqrt u / 4 -
    ((Real.pi / scaleLambda d : ℝ) : ℂ) * analyticLowerSqrt u * Complex.log u / 4) /
    u ^ 2

/-- Explicit third derivative of the analytic phase. -/
noncomputable def analyticPhaseDeriv3 (d : ℕ) (u : ℂ) : ℂ :=
  (-2 + 3 * (Real.pi : ℂ) * analyticLowerSqrt u / 8 +
      3 * ((Real.pi / scaleLambda d : ℝ) : ℂ) *
        analyticLowerSqrt u * Complex.log u / 8 -
      ((Real.pi / scaleLambda d : ℝ) : ℂ) * analyticLowerSqrt u / 4) /
    u ^ 3

/-- On the slit plane, `analyticPhase d q` has derivative `analyticPhaseDeriv d q u` at `u`. -/
theorem hasDerivAt_analyticPhase {d : ℕ} {q : ℝ} {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticPhase d q) (analyticPhaseDeriv d q u) u := by
  have hs := hasDerivAt_analyticLowerSqrt hu
  have hl := Complex.hasDerivAt_log hu
  have hraw := ((((hasDerivAt_id u).const_mul (-(q : ℂ))).add
      (hs.const_mul (Real.pi : ℂ))).add
      ((hs.mul hl).const_mul ((Real.pi / scaleLambda d : ℝ) : ℂ))).sub hl
  refine (hraw.congr_of_eventuallyEq (.of_forall fun z => ?_)).congr_deriv ?_
  · dsimp [analyticPhase]
    ring
  · simp only [analyticPhaseDeriv]
    field_simp [Complex.slitPlane_ne_zero hu]

/-- On the slit plane, `analyticPhaseDeriv d q` has derivative `analyticPhaseDeriv2 d u` at
`u`. -/
theorem hasDerivAt_analyticPhaseDeriv {d : ℕ} {q : ℝ} {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticPhaseDeriv d q) (analyticPhaseDeriv2 d u) u := by
  have hu0 := Complex.slitPlane_ne_zero hu
  have hs := hasDerivAt_analyticLowerSqrt hu
  have hA : HasDerivAt (fun z : ℂ => analyticLowerSqrt z / (2 * z))
      (-analyticLowerSqrt u / (4 * u ^ 2)) u := by
    refine (hs.div ((hasDerivAt_id u).const_mul (2 : ℂ)) (by simpa using hu0)).congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  have hB : HasDerivAt (fun z : ℂ => analyticLowerSqrt z / z)
      (-analyticLowerSqrt u / (2 * u ^ 2)) u := by
    refine (hs.div (hasDerivAt_id u) hu0).congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  have hInv : HasDerivAt (fun z : ℂ => 1 / z) (-1 / u ^ 2) u := by
    simpa [one_div, neg_div] using hasDerivAt_inv hu0
  have hraw := (((hasDerivAt_const u (-(q : ℂ))).add
      (hA.const_mul (Real.pi : ℂ))).add
      (((hA.mul (Complex.hasDerivAt_log hu)).add hB).const_mul
        ((Real.pi / scaleLambda d : ℝ) : ℂ))).sub hInv
  refine hraw.congr_deriv ?_
  simp only [analyticPhaseDeriv2]
  field_simp [hu0]
  ring_nf

/-- On the slit plane, `analyticPhaseDeriv2 d` has derivative `analyticPhaseDeriv3 d u` at `u`. -/
theorem hasDerivAt_analyticPhaseDeriv2 {d : ℕ} {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    HasDerivAt (analyticPhaseDeriv2 d) (analyticPhaseDeriv3 d u) u := by
  have hu0 := Complex.slitPlane_ne_zero hu
  have hs := hasDerivAt_analyticLowerSqrt hu
  have hl := Complex.hasDerivAt_log hu
  let k : ℂ := ((Real.pi / scaleLambda d : ℝ) : ℂ)
  let N : ℂ → ℂ := fun z =>
    1 - (Real.pi : ℂ) * analyticLowerSqrt z / 4 -
      k * analyticLowerSqrt z * Complex.log z / 4
  have hN : HasDerivAt N
      (-(Real.pi : ℂ) * analyticLowerSqrt u / (8 * u) -
        k * analyticLowerSqrt u * Complex.log u / (8 * u) -
        k * analyticLowerSqrt u / (4 * u)) u := by
    have hraw :=
      ((hasDerivAt_const u (1 : ℂ)).sub
        ((hs.const_mul (Real.pi : ℂ)).div_const 4)).sub
        (((hs.mul hl).const_mul k).div_const 4)
    refine (hraw.congr_of_eventuallyEq (.of_forall fun z => ?_)).congr_deriv ?_
    · dsimp [N]
      ring
    · field_simp [hu0]
      ring
  have hden : HasDerivAt (fun z : ℂ => z ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  refine (hN.div hden (pow_ne_zero 2 hu0)).congr_deriv ?_
  simp only [analyticPhaseDeriv3, k]
  field_simp [hu0]
  ring

private theorem iteratedDeriv_two_analyticPhase {d : ℕ} {q : ℝ} {u : ℂ}
    (hu : u ∈ Complex.slitPlane) :
    iteratedDeriv 2 (analyticPhase d q) u = analyticPhaseDeriv2 d u := by
  have hderiv : deriv (analyticPhase d q) =ᶠ[𝓝 u] analyticPhaseDeriv d q := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hu] with z hz
    exact (hasDerivAt_analyticPhase hz).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq]
  exact (hasDerivAt_analyticPhaseDeriv hu).deriv

/-- On the open lower half-plane the branch-defined phase agrees locally with
its holomorphic representative. -/
theorem phase_eq_analyticPhase_of_im_neg (d : ℕ) (q : ℝ) {u : ℂ}
    (hu : u.im < 0) : phase d q u = analyticPhase d q u := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  rw [phase, analyticPhase, lowerLog_eq_log_of_im_neg hu,
    lowerSqrt_eq_sqrt_of_im_neg hu, sqrt_eq_exp hu0]
  rfl

/-- Exact complex second derivative of `phase` throughout the open lower
half-plane. -/
theorem iteratedDeriv_two_phase_of_im_neg (d : ℕ) (q : ℝ) {u : ℂ}
    (hu : u.im < 0) :
    iteratedDeriv 2 (phase d q) u = analyticPhaseDeriv2 d u := by
  have heq : phase d q =ᶠ[𝓝 u] analyticPhase d q := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hu]
      with z hz
    exact phase_eq_analyticPhase_of_im_neg d q hz
  rw [heq.iteratedDeriv_eq 2]
  exact iteratedDeriv_two_analyticPhase (Complex.mem_slitPlane_iff.mpr (Or.inr hu.ne))

private theorem circle_point_im_neg {r α : ℝ} (hr : 0 < r)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    ((((r ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))).im < 0) := by
  rcases hα with ⟨hα0, hαtop⟩
  have hsin : 0 < Real.sin (2 * α) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [mul_comm Complex.I]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [show -2 * α = -(2 * α) by ring, Real.sin_neg]
  nlinarith [mul_pos (sq_pos_of_pos hr) hsin]

/-- Exact formula for `u² h''(u)` at an arbitrary open lower-circle point. -/
theorem phase_hessian_sq_exp_neg_two_mul_I
    (d : ℕ) (q r α : ℝ) (hr : 0 < r)
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    let u : ℂ := ((r ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ))
    u ^ 2 * iteratedDeriv 2 (phase d q) u = explicitSaddleHessian d r α := by
  intro u
  have huim : u.im < 0 := circle_point_im_neg hr hα
  have hu0 : u ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hr.ne')) (Complex.exp_ne_zero _)
  have hs : analyticLowerSqrt u =
      (r : ℂ) * Complex.exp (Complex.I * ((-2 * α : ℝ) : ℂ) / 2) := by
    rw [analyticLowerSqrt, ← sqrt_eq_exp hu0,
      ← lowerSqrt_eq_sqrt_of_im_neg huim]
    exact lowerSqrt_sq_mul_exp_I_mul hr (by linarith [hα.2]) (by linarith [hα.1])
  have hl : Complex.log u =
      ((2 * Real.log r : ℝ) : ℂ) + Complex.I * ((-2 * α : ℝ) : ℂ) := by
    rw [← lowerLog_eq_log_of_im_neg huim]
    exact lowerLog_sq_mul_exp_I_mul hr (by linarith [hα.2]) (by linarith [hα.1])
  rw [iteratedDeriv_two_phase_of_im_neg d q huim, analyticPhaseDeriv2]
  field_simp [hu0]
  rw [hs, hl, explicitSaddleHessian, show Complex.I * ((-2 * α : ℝ) : ℂ) / 2 =
    ((-α : ℝ) : ℂ) * Complex.I by push_cast; ring]
  push_cast
  ring_nf

/-- The defined Hessian at a saddle parameterized by an open angle is the
explicit coefficient. -/
theorem saddleHessian_saddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    saddleHessian d (saddleQ d α) =
      explicitSaddleHessian d (saddleRadius d α) α := by
  have hr := (saddleRadius_pos_and_eq d hd
    ⟨by linarith [hα.1, Real.pi_pos], hα.2.le⟩).1
  rw [saddleHessian, saddle, saddleAngle_saddleQ d hd ⟨hα.1.le, hα.2.le⟩]
  convert phase_hessian_sq_exp_neg_two_mul_I d (saddleQ d α)
    (saddleRadius d α) α hr hα using 1
  congr 4 <;> push_cast <;> ring_nf

/-- Corrected exact real-part formula for the actual `saddleHessian`. -/
theorem saddleHessian_re_saddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (saddleHessian d (saddleQ d α)).re =
      Real.sin α ^ 2 +
        Real.pi * saddleRadius d α / (2 * scaleLambda d) *
          (Real.cos α - α * Real.cos (2 * α) / Real.sin α) :=
  saddleHessian_saddleQ d hd hα ▸ explicitSaddleHessian_re_at_saddle d hd hα

/-- Corrected exact imaginary-part formula for the actual `saddleHessian`. -/
theorem saddleHessian_im_saddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    (saddleHessian d (saddleQ d α)).im =
      Real.pi * saddleRadius d α / 4 *
        ((1 + 2 * Real.log (saddleRadius d α) / scaleLambda d) * Real.sin α +
          2 * α * Real.cos α / scaleLambda d) :=
  saddleHessian_saddleQ d hd hα ▸ explicitSaddleHessian_im_at_saddle d _ α

end RiemannJensen
