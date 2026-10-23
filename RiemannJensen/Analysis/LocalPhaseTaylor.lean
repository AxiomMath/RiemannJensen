module

public import RiemannJensen.Analysis.SaddleStationarity
public import RiemannJensen.Analysis.LocalPhaseSign
public import RiemannJensen.Analysis.GaussianAdapter

/-! # Exact Taylor data for the normalized local phase -/

@[expose] public section

namespace RiemannJensen

open Set
open scoped Topology

/-- Holomorphic local saddle arc, before restriction to the real normalized
coordinate. -/
noncomputable def analyticLocalArc (ε : ℝ) (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  saddle d q * Complex.exp (Complex.I * (localWidth ε d q : ℂ) * z)

/-- Holomorphic representative of the normalized local phase. -/
noncomputable def analyticLocalPhase (ε : ℝ) (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  (analyticPhase d q (analyticLocalArc ε d q z) -
      analyticPhase d q (saddle d q)) /
    ((‖saddleHessian d q‖ * localWidth ε d q ^ 2 : ℝ) : ℂ)

/-- Explicit first derivative of the normalized analytic local phase. -/
noncomputable def analyticLocalPhaseFirst
    (ε : ℝ) (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  let u := analyticLocalArc ε d q z
  let v := u * (Complex.I * (localWidth ε d q : ℂ))
  analyticPhaseDeriv d q u * v /
    ((‖saddleHessian d q‖ * localWidth ε d q ^ 2 : ℝ) : ℂ)

/-- Explicit second derivative of the normalized analytic local phase. -/
noncomputable def analyticLocalPhaseSecond
    (ε : ℝ) (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  let u := analyticLocalArc ε d q z
  let c := Complex.I * (localWidth ε d q : ℂ)
  (analyticPhaseDeriv2 d u * (u * c) ^ 2 +
      analyticPhaseDeriv d q u * (u * c ^ 2)) /
    ((‖saddleHessian d q‖ * localWidth ε d q ^ 2 : ℝ) : ℂ)

/-- Explicit third derivative of the normalized analytic local phase. -/
noncomputable def analyticLocalPhaseThird
    (ε : ℝ) (d : ℕ) (q : ℝ) (z : ℂ) : ℂ :=
  let u := analyticLocalArc ε d q z
  let c := Complex.I * (localWidth ε d q : ℂ)
  (analyticPhaseDeriv3 d u * (u * c) ^ 3 +
      3 * analyticPhaseDeriv2 d u * (u * c) ^ 2 * c +
      analyticPhaseDeriv d q u * (u * c ^ 3)) /
    ((‖saddleHessian d q‖ * localWidth ε d q ^ 2 : ℝ) : ℂ)

/-- The holomorphic local arc passes through the saddle point at `z = 0`. -/
@[simp] theorem analyticLocalArc_zero (ε : ℝ) (d : ℕ) (q : ℝ) :
    analyticLocalArc ε d q 0 = saddle d q := by
  simp [analyticLocalArc]

/-- The normalized analytic local phase vanishes at `z = 0`. -/
@[simp] theorem analyticLocalPhase_zero (ε : ℝ) (d : ℕ) (q : ℝ) :
    analyticLocalPhase ε d q 0 = 0 := by
  simp [analyticLocalPhase]

/-- Derivative of the holomorphic local arc. -/
theorem hasDerivAt_analyticLocalArc (ε : ℝ) (d : ℕ) (q : ℝ) (z : ℂ) :
    HasDerivAt (analyticLocalArc ε d q)
      (analyticLocalArc ε d q z *
        (Complex.I * (localWidth ε d q : ℂ))) z := by
  unfold analyticLocalArc
  simpa [mul_assoc] using (((hasDerivAt_id z).const_mul
    (Complex.I * (localWidth ε d q : ℂ))).cexp).const_mul (saddle d q)

/-- First derivative of the holomorphic normalized local phase. -/
theorem hasDerivAt_analyticLocalPhase
    (ε : ℝ) (d : ℕ) (q : ℝ) {z : ℂ}
    (hslit : analyticLocalArc ε d q z ∈ Complex.slitPlane) :
    HasDerivAt (analyticLocalPhase ε d q)
      (analyticLocalPhaseFirst ε d q z) z :=
  (((hasDerivAt_analyticPhase (d := d) (q := q) hslit).comp z
    (hasDerivAt_analyticLocalArc ε d q z)).sub_const _).div_const _

/-- Second derivative of the holomorphic normalized local phase. -/
theorem hasDerivAt_analyticLocalPhaseFirst
    (ε : ℝ) (d : ℕ) (q : ℝ) {z : ℂ}
    (hslit : analyticLocalArc ε d q z ∈ Complex.slitPlane) :
    HasDerivAt (analyticLocalPhaseFirst ε d q)
      (analyticLocalPhaseSecond ε d q z) z := by
  have hu := hasDerivAt_analyticLocalArc ε d q z
  refine ((((hasDerivAt_analyticPhaseDeriv (d := d) (q := q) hslit).comp z hu).mul
    (hu.mul_const _)).div_const _).congr_deriv ?_
  simp only [analyticLocalPhaseSecond, Function.comp_apply]
  ring

/-- Third derivative of the holomorphic normalized local phase. -/
theorem hasDerivAt_analyticLocalPhaseSecond
    (ε : ℝ) (d : ℕ) (q : ℝ) {z : ℂ}
    (hslit : analyticLocalArc ε d q z ∈ Complex.slitPlane) :
    HasDerivAt (analyticLocalPhaseSecond ε d q)
      (analyticLocalPhaseThird ε d q z) z := by
  have hu := hasDerivAt_analyticLocalArc ε d q z
  refine (((((hasDerivAt_analyticPhaseDeriv2 (d := d) hslit).comp z hu).mul
    ((hu.mul_const (Complex.I * (localWidth ε d q : ℂ))).pow 2)).add
    (((hasDerivAt_analyticPhaseDeriv (d := d) (q := q) hslit).comp z hu).mul
      (hu.mul_const _))).div_const _).congr_deriv ?_
  simp only [analyticLocalPhaseThird, Function.comp_apply, Pi.pow_apply]
  ring

/-- The saddle lies in the open lower half-plane. -/
theorem saddle_im_neg (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) : (saddle d q).im < 0 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  rw [saddle, show (-2 : ℂ) * Complex.I * (saddleAngle d q : ℂ) =
    Complex.I * ((-2 * saddleAngle d q : ℝ) : ℂ) by push_cast; ring]
  exact im_ofReal_sq_mul_exp_I_mul_neg_two_mul_neg
    (saddleRadius_pos_and_eq d hd ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩).1 hα0 hαtop

/-- The analytic phase is stationary at the saddle. -/
theorem analyticPhaseDeriv_saddle_eq_zero (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    analyticPhaseDeriv d q (saddle d q) = 0 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  rw [← hinv]
  exact analyticPhaseDeriv_saddleQ_eq_zero d hd ⟨hα0, hαtop⟩

/-- The first normalized derivative vanishes at the saddle. -/
theorem analyticLocalPhaseFirst_zero
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    analyticLocalPhaseFirst ε d q 0 = 0 := by
  simp [analyticLocalPhaseFirst, analyticPhaseDeriv_saddle_eq_zero d hd hq]

/-- At `z = 0` the second normalized derivative equals `-D / ‖D‖`, where
`D = saddleHessian d q`. -/
theorem analyticLocalPhaseSecond_zero
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε : 0 < ε) :
    analyticLocalPhaseSecond ε d q 0 =
      -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) := by
  have hℓ := localWidth_pos_on_scale_window d hd hq hε
  simp only [analyticLocalPhaseSecond, analyticLocalArc_zero,
    analyticPhaseDeriv_saddle_eq_zero d hd hq, zero_mul, add_zero, saddleHessian,
    ← iteratedDeriv_two_phase_of_im_neg d q (saddle_im_neg d hd hq)]
  push_cast
  field_simp [hℓ.ne']
  rw [Complex.I_sq]
  ring

/-- The analytic local arc stays in the open lower half-plane on the
normalized interval. -/
theorem analyticLocalArc_im_neg
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    (analyticLocalArc ε d q (y : ℂ)).im < 0 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨ha, hb, -⟩
  have hr := (saddleRadius_pos_and_eq d hd
    ⟨by linarith [ha, Real.pi_pos], hb.le⟩).1
  have hw := localWindow_contained_open_lower_semicircle
    d hd hq hε0 hε1
  have hℓ0 : 0 ≤ localWidth ε d q := by
    rw [localWidth]
    exact mul_nonneg hε0 (min_angle_cos_pos_on_scale_window d hd hq).le
  have hlo := mul_le_mul_of_nonneg_left hy.1 hℓ0
  have hhi := mul_le_mul_of_nonneg_left hy.2 hℓ0
  rw [analyticLocalArc, saddle, mul_assoc, ← Complex.exp_add,
    show -2 * Complex.I * (saddleAngle d q : ℂ) +
        Complex.I * (localWidth ε d q : ℂ) * (y : ℂ) =
      (((-2 * saddleAngle d q + localWidth ε d q * y : ℝ) : ℂ)) * Complex.I by
    push_cast
    ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hs := Real.sin_neg_of_neg_of_neg_pi_lt
    (x := -2 * saddleAngle d q + localWidth ε d q * y) (by linarith [hw.2]) (by linarith [hw.1])
  nlinarith [sq_pos_of_pos hr]

/-- The analytic local arc avoids the slit on the normalized interval. -/
theorem analyticLocalArc_mem_slitPlane (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    analyticLocalArc ε d q (y : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (analyticLocalArc_im_neg d hd hq hε0 hε1 hy).ne)

/-- On the real normalized interval, the branch-defined phase is locally
represented by `analyticLocalPhase`. -/
theorem lowerNormalizedPhase_eventuallyEq_analytic
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    lowerNormalizedPhase ε d q =ᶠ[𝓝 y]
      fun t : ℝ => analyticLocalPhase ε d q (t : ℂ) := by
  filter_upwards [(isOpen_lt (g := fun _ : ℝ => (0 : ℝ))
    (f := fun t : ℝ => (analyticLocalArc ε d q (t : ℂ)).im) (by unfold analyticLocalArc; fun_prop)
    (by fun_prop)).mem_nhds (analyticLocalArc_im_neg d hd hq hε0 hε1 hy)] with t ht
  rw [lowerNormalizedPhase_eq_localPhase (lt_of_lt_of_le (by norm_num) hd),
    localPhase, analyticLocalPhase]
  have harc : saddle d q *
      Complex.exp (Complex.I * ((localWidth ε d q * t : ℝ) : ℂ)) =
        analyticLocalArc ε d q (t : ℂ) := by
    rw [analyticLocalArc]
    congr 2
    push_cast
    ring
  rw [harc, phase_eq_analyticPhase_of_im_neg d q ht,
    phase_eq_analyticPhase_of_im_neg d q (saddle_im_neg d hd hq)]

/-- `lowerNormalizedPhase ε d q` has derivative `analyticLocalPhaseFirst ε d q y` at each
`y ∈ [-1, 1]`. -/
theorem hasDerivAt_lowerNormalizedPhase
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    HasDerivAt (lowerNormalizedPhase ε d q)
      (analyticLocalPhaseFirst ε d q (y : ℂ)) y :=
  (hasDerivAt_analyticLocalPhase ε d q
    (analyticLocalArc_mem_slitPlane d hd hq hε0 hε1 hy)).comp_ofReal.congr_of_eventuallyEq
    (lowerNormalizedPhase_eventuallyEq_analytic d hd hq hε0 hε1 hy)

/-- On the normalized interval, `t ↦ analyticLocalPhaseFirst ε d q t` has derivative
`analyticLocalPhaseSecond ε d q y` at `y`. -/
theorem hasDerivAt_analyticLocalPhaseFirst_ofReal
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => analyticLocalPhaseFirst ε d q (t : ℂ))
      (analyticLocalPhaseSecond ε d q (y : ℂ)) y :=
  (hasDerivAt_analyticLocalPhaseFirst ε d q
    (analyticLocalArc_mem_slitPlane d hd hq hε0 hε1 hy)).comp_ofReal

/-- On the normalized interval, `t ↦ analyticLocalPhaseSecond ε d q t` has derivative
`analyticLocalPhaseThird ε d q y` at `y`. -/
theorem hasDerivAt_analyticLocalPhaseSecond_ofReal
    (d : ℕ) (hd : 1 ≤ d) {q ε y : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => analyticLocalPhaseSecond ε d q (t : ℂ))
      (analyticLocalPhaseThird ε d q (y : ℂ)) y :=
  (hasDerivAt_analyticLocalPhaseSecond ε d q
    (analyticLocalArc_mem_slitPlane d hd hq hε0 hε1 hy)).comp_ofReal

/-- A small uniform third-derivative bound keeps the second normalized
derivative close to its value `-D / ‖D‖` at the saddle. -/
theorem norm_analyticLocalPhaseSecond_add_le
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε : 0 < ε) (hε1 : ε < 1)
    (hthird : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      ‖analyticLocalPhaseThird ε d q (y : ℂ)‖ ≤ (1 / 2 : ℝ))
    {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) {t : ℝ} (ht : t ∈ Set.uIcc 0 y) :
    ‖analyticLocalPhaseSecond ε d q (t : ℂ) +
        saddleHessian d q / (‖saddleHessian d q‖ : ℂ)‖ ≤ (1 / 2 : ℝ) * |y| := by
  have hts : Set.uIcc 0 t ⊆ Set.Icc (-1 : ℝ) 1 :=
    (uIcc_subset_uIcc_left ht).trans (Gaussian.uIcc_zero_subset hy)
  have hm := Gaussian.norm_sub_zero_le_of_hasDerivAt
    (h := fun s : ℝ => analyticLocalPhaseSecond ε d q (s : ℂ) +
      saddleHessian d q / (‖saddleHessian d q‖ : ℂ))
    (h' := fun s : ℝ => analyticLocalPhaseThird ε d q (s : ℂ))
    (y := t) (K := (1 / 2 : ℝ))
    (fun s hs =>
      (hasDerivAt_analyticLocalPhaseSecond_ofReal d hd hq hε.le hε1 (hts hs)).add_const _)
    (fun s hs => hthird s (hts hs))
  simp only [Complex.ofReal_zero, analyticLocalPhaseSecond_zero d hd hq hε,
    neg_add_cancel, sub_zero] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (Gaussian.abs_le_of_mem_uIcc_zero ht) (by norm_num))

/-- A small uniform third-derivative bound gives the derivative lower bound
required by the Gaussian adapter. -/
theorem analyticLocalPhaseFirst_norm_lower
    (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hε : 0 < ε) (hε1 : ε < 1) (hD : 0 < ‖saddleHessian d q‖)
    (hthird : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      ‖analyticLocalPhaseThird ε d q (y : ℂ)‖ ≤ (1 / 2 : ℝ))
    {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    (1 / 2 : ℝ) * |y| ≤ ‖analyticLocalPhaseFirst ε d q (y : ℂ)‖ := by
  let A : ℂ := saddleHessian d q / (‖saddleHessian d q‖ : ℂ)
  have hA : ‖A‖ = 1 := by simp [A, hD.ne']
  have hm := Gaussian.norm_sub_zero_le_of_hasDerivAt
    (h := fun s : ℝ => analyticLocalPhaseFirst ε d q (s : ℂ) + A * (s : ℂ))
    (fun t ht => ((hasDerivAt_analyticLocalPhaseFirst_ofReal d hd hq hε.le hε1
      (Gaussian.uIcc_zero_subset hy ht)).add
        ((hasDerivAt_id (t : ℂ)).const_mul A).comp_ofReal).congr_deriv (by simp [A]))
    (fun t ht => norm_analyticLocalPhaseSecond_add_le d hd hq hε hε1 hthird hy ht)
  simp only [analyticLocalPhaseFirst_zero d hd hq, Complex.ofReal_zero,
    mul_zero, add_zero, sub_zero] at hm
  have htri := norm_sub_le (analyticLocalPhaseFirst ε d q (y : ℂ) + A * (y : ℂ))
    (analyticLocalPhaseFirst ε d q (y : ℂ))
  rw [add_sub_cancel_left, norm_mul, hA, one_mul, Complex.norm_real,
    Real.norm_eq_abs] at htri
  nlinarith [mul_le_of_le_one_right (abs_nonneg y) (abs_le.mpr hy)]

end RiemannJensen
