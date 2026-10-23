module

public import RiemannJensen.Analysis.ZetaLog
public import RiemannJensen.Analysis.GammaLog
public import RiemannJensen.Analysis.HessianBounds
public import RiemannJensen.Analysis.AmplitudeDefinitions

/-!
# The explicit bounded phase correction

We define the phase correction attached to the lower saddle point, prove continuity of the
inverse angle and of the Hessian on the saddle branch, establish the Gamma-log and zeta domain
estimates for the saddle point, and show that the phase correction is continuous and bounded by
`8` on the phase window.

## Main definitions

* `saddlePhasePoint`: the scaled Gamma/zeta argument at the lower saddle.
* `phaseCorrection`: the phase correction accompanying the lower saddle contribution.
* `phaseWindow`: the interval of parameters on which the phase correction is analysed.

## Main results

* `continuousOn_phaseCorrection_on_phaseWindow`: the phase correction is continuous on the phase
  window.
* `abs_phaseCorrection_le_eight_on_phaseWindow`: the phase correction has absolute value at most
  `8` on the phase window.
-/

@[expose] public section

namespace RiemannJensen

open Complex

/-- The scaled Gamma/zeta argument at the lower saddle. -/
noncomputable def saddlePhasePoint (d : ℕ) (q : ℝ) : ℂ :=
  contourW d q (-2 * saddleAngle d q)

/-- The explicit `O(1)` phase correction accompanying the principal lower
saddle contribution. -/
noncomputable def phaseCorrection (d : ℕ) (q : ℝ) : ℝ :=
  -(7 / 4) * saddleAngle d q +
    (Complex.log (riemannZeta (1 / 2 + saddlePhasePoint d q))).im +
    (gammaLog (saddlePhasePoint d q)).im -
    Complex.arg (saddleHessian d q) / 2

/-- Exact polar description of the lower-saddle Gamma/zeta argument. -/
theorem saddlePhasePoint_eq_polar (d : ℕ) (q : ℝ) :
    saddlePhasePoint d q =
      (scaleT d * saddleRadius d (saddleAngle d q) : ℝ) *
        Complex.exp (-Complex.I * (saddleAngle d q : ℂ)) := by
  rw [saddlePhasePoint, contourW]
  congr 2
  push_cast
  ring

/-- Real part of the lower-saddle Gamma/zeta argument. -/
theorem saddlePhasePoint_re (d : ℕ) (q : ℝ) :
    (saddlePhasePoint d q).re =
      scaleT d * saddleRadius d (saddleAngle d q) * Real.cos (saddleAngle d q) := by
  rw [saddlePhasePoint_eq_polar]
  simp [Complex.exp_re, Complex.mul_re]

/-- On the scale window the inverse angle lies in `[0, π / 2]`. -/
theorem saddleAngle_mem_Icc_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    saddleAngle d q ∈ Set.Icc 0 (Real.pi / 2) :=
  let ⟨hα0, hαtop, _⟩ := saddle_inverse_on_scale_window d hd hq
  ⟨hα0.le, hαtop.le⟩

/-- On the scale window the saddle radius is positive. -/
theorem saddleRadius_pos_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < saddleRadius d (saddleAngle d q) := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  exact (saddleRadius_pos_and_eq d hd ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩).1

/-- Norm of the lower-saddle Gamma/zeta argument when its radius is nonnegative. -/
theorem norm_saddlePhasePoint (d : ℕ) (q : ℝ) (hT : 0 ≤ scaleT d)
    (hr : 0 ≤ saddleRadius d (saddleAngle d q)) :
    ‖saddlePhasePoint d q‖ = scaleT d * saddleRadius d (saddleAngle d q) := by
  rw [saddlePhasePoint, contourW, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hT hr), Complex.norm_exp]
  simp

/-- Throughout the scale window the lower-saddle point is in the closed right
half-plane, as required by the corrected Gamma logarithm. -/
theorem saddlePhasePoint_re_nonneg_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 ≤ (saddlePhasePoint d q).re := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  rw [saddlePhasePoint_re]
  have hT := scaleT_pos d hd
  have hr := saddleRadius_pos_on_scale_window d hd hq
  have hc : 0 ≤ Real.cos (saddleAngle d q) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩
  positivity

/-- The lower-saddle point has norm strictly larger than `4` throughout the scale window. -/
theorem four_lt_norm_saddlePhasePoint_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    4 < ‖saddlePhasePoint d q‖ := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨-, hαtop, -⟩
  have hα := saddleAngle_mem_Icc_on_scale_window d hd hq
  have htopmem : Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨(half_pos Real.pi_pos).le, le_rfl⟩
  have hrlt := saddleRadius_strictAntiOn d hd hα htopmem hαtop
  rw [saddleRadius_pi_div_two d hd] at hrlt
  have hT := scaleT_pos d hd
  rw [norm_saddlePhasePoint d q hT.le (saddleRadius_pos_on_scale_window d hd hq).le]
  have hmul : 2 * Real.pi < scaleT d * saddleRadius d (saddleAngle d q) := by
    simpa [mul_comm] using (div_lt_iff₀ hT).1 hrlt
  linarith [Real.two_le_pi]

/-- The lower-saddle point belongs to the corrected Gamma-log domain on the
entire scale window. -/
theorem saddlePhasePoint_mem_grDomain_on_scale_window (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    saddlePhasePoint d q ∈ GammaCore.grDomain :=
  ⟨by linarith [saddlePhasePoint_re_nonneg_on_scale_window d hd hq],
    by linarith [four_lt_norm_saddlePhasePoint_on_scale_window d hd hq]⟩

/-- On the scale window with `49 ≤ scaleT d`, if the inverse angle is at most `π / 3` then the
zeta argument at the saddle point has real part at least `4`. -/
theorem saddlePhasePoint_zeta_domain_of_angle_le_pi_div_three
    (d : ℕ) (hd : 1 ≤ d) (hT : 49 ≤ scaleT d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d))
    (hαtop : saddleAngle d q ≤ Real.pi / 3) :
    4 ≤ (1 / 2 + saddlePhasePoint d q).re := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨-, -, hinv⟩
  have hα := saddleAngle_mem_Icc_on_scale_window d hd hq
  have hqr := one_le_saddleQ_mul_radius_sq d hd hα
  rw [hinv] at hqr
  have hTpos : 0 < scaleT d := by linarith
  have hr := saddleRadius_pos_on_scale_window d hd hq
  have hTr2 : 1 ≤ scaleT d * saddleRadius d (saddleAngle d q) ^ 2 := by
    nlinarith [hq.2]
  have hTr : 7 ≤ scaleT d * saddleRadius d (saddleAngle d q) := by
    have hsquare : 49 ≤
        (scaleT d * saddleRadius d (saddleAngle d q)) ^ 2 := by
      nlinarith
    nlinarith [mul_pos hTpos hr]
  have hthird : Real.pi / 3 ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hcos : (1 : ℝ) / 2 ≤ Real.cos (saddleAngle d q) := by
    simpa using cos_strictAntiOn_saddle.antitoneOn hα hthird hαtop
  have hprod : (7 : ℝ) * (1 / 2) ≤
      (scaleT d * saddleRadius d (saddleAngle d q)) *
        Real.cos (saddleAngle d q) :=
    mul_le_mul hTr hcos (by norm_num) (mul_pos hTpos hr).le
  rw [Complex.add_re, saddlePhasePoint_re]
  norm_num
  nlinarith

/-- The generalized inverse angle is continuous on the complete image of the saddle branch. -/
theorem continuousOn_saddleAngle_on_branch (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (saddleAngle d)
      (Set.Icc (edgeQ d) (saddleQ d (Real.pi / 2))) := by
  let A : Set ℝ := Set.Icc 0 (Real.pi / 2)
  let f : A → ℝ := fun α => saddleQ d α.1
  have hf : Continuous f := (continuousOn_saddleQ d hd).domRestrict
  let e : A ≃ₜ Set.range f := (hf.isClosedEmbedding fun α β hab =>
    Subtype.ext ((saddleQ_strictMonoOn d hd).injOn α.2 β.2 hab)).isEmbedding.toHomeomorph
  have hrange : Set.range f =
      Set.Icc (edgeQ d) (saddleQ d (Real.pi / 2)) := by
    rw [edgeQ, ← (continuousOn_saddleQ d hd).image_Icc_of_monotoneOn
      (by positivity : (0 : ℝ) ≤ Real.pi / 2) (saddleQ_strictMonoOn d hd).monotoneOn]
    exact Set.range_domRestrict (saddleQ d) A
  rw [← hrange, continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp e.symm.continuous).congr fun q =>
    (saddleAngle_eq_of_saddleQ_eq d hd (e.symm q).2
      (congrArg Subtype.val (e.apply_symm_apply q))).symm

/-- The inverse angle is continuous on the scale window. -/
theorem continuousOn_saddleAngle_on_scale_window (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (saddleAngle d) (Set.Ioc (edgeQ d) (scaleT d)) :=
  (continuousOn_saddleAngle_on_branch d hd).mono fun _ hq =>
    ⟨hq.1.le, (hq.2.trans_lt (scaleT_lt_saddleQ_pi_div_two d hd)).le⟩

/-- The Hessian is continuous on the scale window. -/
theorem continuousOn_saddleHessian_on_scale_window (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (saddleHessian d) (Set.Ioc (edgeQ d) (scaleT d)) := by
  have hα := continuousOn_saddleAngle_on_scale_window d hd
  have hr : ContinuousOn (fun q => saddleRadius d (saddleAngle d q))
      (Set.Ioc (edgeQ d) (scaleT d)) :=
    (continuousOn_saddleRadius d hd).comp hα
      fun _ hq => saddleAngle_mem_Icc_on_scale_window d hd hq
  have hlog : ContinuousOn
      (fun q => Real.log (saddleRadius d (saddleAngle d q)))
      (Set.Ioc (edgeQ d) (scaleT d)) :=
    hr.log fun _ hq => (saddleRadius_pos_on_scale_window d hd hq).ne'
  refine ContinuousOn.congr (f := fun q => explicitSaddleHessian d
    (saddleRadius d (saddleAngle d q)) (saddleAngle d q)) ?_
    fun q hq => saddleHessian_eq_explicit_on_scale_window d hd hq
  unfold explicitSaddleHessian
  fun_prop

/-- `saddlePhasePoint d` is continuous on `S` whenever `saddleAngle d` is continuous on `S` and
takes values in `[0, π/2]` there. -/
theorem continuousOn_saddlePhasePoint (d : ℕ) (hd : 1 ≤ d) {S : Set ℝ}
    (hα : ContinuousOn (saddleAngle d) S)
    (hαmem : ∀ q ∈ S, saddleAngle d q ∈ Set.Icc 0 (Real.pi / 2)) :
    ContinuousOn (saddlePhasePoint d) S := by
  have hr : ContinuousOn (fun q => saddleRadius d (saddleAngle d q)) S :=
    (continuousOn_saddleRadius d hd).comp hα hαmem
  unfold saddlePhasePoint contourW
  fun_prop

/-- `phaseCorrection d` is continuous on `S` given continuity of `saddleAngle d`,
`saddlePhasePoint d` and `saddleHessian d` on `S`, together with the pointwise zeta, Gamma-log
and Hessian domain conditions. -/
theorem continuousOn_phaseCorrection_of_geometric_inputs (d : ℕ) {S : Set ℝ}
    (hα : ContinuousOn (saddleAngle d) S)
    (hw : ContinuousOn (saddlePhasePoint d) S)
    (hZ : ∀ q ∈ S, 4 ≤ (1 / 2 + saddlePhasePoint d q).re)
    (hG : ∀ q ∈ S, saddlePhasePoint d q ∈ GammaCore.grDomain)
    (hD : ContinuousOn (saddleHessian d) S)
    (hDpos : ∀ q ∈ S, 0 < (saddleHessian d q).re) :
    ContinuousOn (phaseCorrection d) S := by
  have hZlog : ContinuousOn
      (fun q => Complex.log (riemannZeta (1 / 2 + saddlePhasePoint d q))) S :=
    continuousOn_log_riemannZeta.comp (by fun_prop) hZ
  have hGlog : ContinuousOn (fun q => gammaLog (saddlePhasePoint d q)) S :=
    continuousOn_gammaLog.comp hw hG
  have hArg : ContinuousOn (fun q => Complex.arg (saddleHessian d q)) S :=
    Complex.continuousOn_arg.comp hD (fun q hq => Or.inl (hDpos q hq))
  exact (((hα.const_mul (-(7 / 4))).add (continuous_im.comp_continuousOn hZlog)).add
    (continuous_im.comp_continuousOn hGlog)).sub (hArg.div_const 2)

/-- `|phaseCorrection d q| ≤ 8` whenever the inverse angle lies in `[0, π/2]`, the saddle point
lies in the zeta and Gamma-log domains, and the Hessian has positive real part. -/
theorem abs_phaseCorrection_le_eight (d : ℕ) {q : ℝ}
    (hα : saddleAngle d q ∈ Set.Icc 0 (Real.pi / 2))
    (hZ : 4 ≤ (1 / 2 + saddlePhasePoint d q).re)
    (hGre : 0 ≤ (saddlePhasePoint d q).re)
    (hGnorm : 4 ≤ ‖saddlePhasePoint d q‖)
    (hD : 0 < (saddleHessian d q).re) :
    |phaseCorrection d q| ≤ 8 := by
  have hangle : |-(7 / 4) * saddleAngle d q| ≤ 7 * Real.pi / 8 :=
    abs_le.2 ⟨by linarith [hα.2], by linarith [hα.1, Real.pi_pos]⟩
  have hz : |(Complex.log
      (riemannZeta (1 / 2 + saddlePhasePoint d q))).im| ≤ (1 : ℝ) / 2 :=
    (abs_im_le_norm _).trans (norm_log_riemannZeta_le_half hZ)
  have hg : |(gammaLog (saddlePhasePoint d q)).im| ≤ (9 : ℝ) / 4 := by
    refine (abs_im_le_norm _).trans ((norm_gammaLog_le hGre hGnorm).trans ?_)
    apply (div_le_iff₀ (by positivity : 0 < ‖saddlePhasePoint d q‖)).2
    nlinarith
  have harg : |Complex.arg (saddleHessian d q) / 2| ≤ Real.pi / 4 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [abs_arg_le_pi_div_two_iff.mpr hD.le]
  unfold phaseCorrection
  grw [abs_sub, abs_add_le, abs_add_le, hangle, hz, hg, harg]
  linarith [Real.pi_le_four]

/-- On the scale window, when `4 * π ≤ scaleLambda d`, the Hessian has positive real part. -/
theorem saddleHessian_re_pos_on_scale_window_of_four_pi_le (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d) {q : ℝ}
    (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    0 < (saddleHessian d q).re := by
  have hDre := (saddleHessian_re_bounds_on_scale_window d hd hΛ hq).1
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  have hsin : 0 < Real.sin (saddleAngle d q) :=
    Real.sin_pos_of_pos_of_lt_pi hα0 (hαtop.trans (by linarith [Real.pi_pos]))
  nlinarith [sq_pos_of_pos hsin]

/-- The phase window: the interval from `edgeQ d` to the minimum of `scaleT d` and the saddle
parameter at angle `π / 3`. -/
noncomputable def phaseWindow (d : ℕ) : Set ℝ :=
  Set.Ioc (edgeQ d) (min (scaleT d) (saddleQ d (Real.pi / 3)))

/-- A point `q` lies in the phase window exactly when `edgeQ d < q` and `q` is at most both
`scaleT d` and `saddleQ d (π / 3)`. -/
@[simp]
theorem mem_phaseWindow_iff {d : ℕ} {q : ℝ} :
    q ∈ phaseWindow d ↔ edgeQ d < q ∧ q ≤ min (scaleT d) (saddleQ d (Real.pi / 3)) :=
  Iff.rfl

/-- The phase window is contained in the scale window. -/
theorem phaseWindow_subset_scale_window (d : ℕ) :
    phaseWindow d ⊆ Set.Ioc (edgeQ d) (scaleT d) :=
  fun _ hq => ⟨hq.1, hq.2.trans (min_le_left _ _)⟩

/-- Points of the concrete phase window lie in the scale window and have
inverse angle at most `π / 3`. -/
theorem phaseWindow_geometry (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ phaseWindow d) :
    q ∈ Set.Ioc (edgeQ d) (scaleT d) ∧ saddleAngle d q ≤ Real.pi / 3 := by
  have hscale := phaseWindow_subset_scale_window d hq
  rcases saddle_inverse_on_scale_window d hd hscale with ⟨-, -, hinv⟩
  have hthird : Real.pi / 3 ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  refine ⟨hscale, ?_⟩
  by_contra hn
  have hs := saddleQ_strictMonoOn d hd hthird (saddleAngle_mem_Icc_on_scale_window d hd hscale)
    (lt_of_not_ge hn)
  rw [hinv] at hs
  linarith [hq.2.trans (min_le_right _ _)]

/-- The zeta argument `1 / 2 + saddlePhasePoint d q` has real part at least `4` throughout the
phase window, provided `49 ≤ scaleT d`. -/
theorem saddlePhasePoint_zeta_domain_on_phaseWindow
    (d : ℕ) (hd : 1 ≤ d) (hT : 49 ≤ scaleT d) {q : ℝ}
    (hq : q ∈ phaseWindow d) :
    4 ≤ (1 / 2 + saddlePhasePoint d q).re := by
  rcases phaseWindow_geometry d hd hq with ⟨hscale, hangle⟩
  exact saddlePhasePoint_zeta_domain_of_angle_le_pi_div_three d hd hT hscale hangle

/-- The phase correction is continuous on the phase window. -/
theorem continuousOn_phaseCorrection_on_phaseWindow
    (d : ℕ) (hd : 1 ≤ d) (hT : 49 ≤ scaleT d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d) :
    ContinuousOn (phaseCorrection d) (phaseWindow d) := by
  have hsub := phaseWindow_subset_scale_window d
  have hα := (continuousOn_saddleAngle_on_scale_window d hd).mono hsub
  exact continuousOn_phaseCorrection_of_geometric_inputs d hα
    (continuousOn_saddlePhasePoint d hd hα
      fun _ hq => saddleAngle_mem_Icc_on_scale_window d hd (hsub hq))
    (fun _ hq => saddlePhasePoint_zeta_domain_on_phaseWindow d hd hT hq)
    (fun _ hq => saddlePhasePoint_mem_grDomain_on_scale_window d hd (hsub hq))
    ((continuousOn_saddleHessian_on_scale_window d hd).mono hsub)
    fun _ hq => saddleHessian_re_pos_on_scale_window_of_four_pi_le d hd hΛ (hsub hq)

/-- The explicit phase correction has absolute value at most `8` throughout the phase window,
provided `49 ≤ scaleT d` and `4π ≤ scaleLambda d`. -/
theorem abs_phaseCorrection_le_eight_on_phaseWindow
    (d : ℕ) (hd : 1 ≤ d) (hT : 49 ≤ scaleT d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d) {q : ℝ}
    (hq : q ∈ phaseWindow d) :
    |phaseCorrection d q| ≤ 8 := by
  have hscale := phaseWindow_subset_scale_window d hq
  exact abs_phaseCorrection_le_eight d (saddleAngle_mem_Icc_on_scale_window d hd hscale)
    (saddlePhasePoint_zeta_domain_on_phaseWindow d hd hT hq)
    (saddlePhasePoint_re_nonneg_on_scale_window d hd hscale)
    (four_lt_norm_saddlePhasePoint_on_scale_window d hd hscale).le
    (saddleHessian_re_pos_on_scale_window_of_four_pi_le d hd hΛ hscale)

end RiemannJensen
