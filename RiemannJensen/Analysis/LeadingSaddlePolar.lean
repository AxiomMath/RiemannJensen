module

public import RiemannJensen.Analysis.PhaseCorrection
public import RiemannJensen.Analysis.SaddleActionBounds
public import RiemannJensen.Analysis.GaussianNormalization

@[expose] public section

namespace RiemannJensen

open Complex Set

/-- A logarithm of `leadingSaddle d q` with the positive real prefactor `d! / d ^ d` removed,
written as a sum of logarithms of the individual factors. -/
noncomputable def leadingSaddleLog (d : ℕ) (q : ℝ) : ℂ :=
  Complex.log (Real.pi / 2) * (1 / 4) +
    Complex.log (saddlePhasePoint d q) * (7 / 4) +
    Complex.log (riemannZeta (1 / 2 + saddlePhasePoint d q)) +
    gammaLog (saddlePhasePoint d q) +
    (d : ℂ) * phase d q (saddle d q) -
    Complex.log (2 * Real.pi * d * saddleHessian d q) / 2

/-- A positive real multiple of one exponential has polar phase equal to the
imaginary part of its exponent, with no principal-argument ambiguity. -/
theorem eq_norm_mul_exp_I_im_of_eq_pos_mul_exp
    {z L : ℂ} {c : ℝ} (hc : 0 < c)
    (hz : z = (c : ℂ) * Complex.exp L) :
    z = (‖z‖ : ℂ) * Complex.exp (Complex.I * (L.im : ℂ)) := by
  have hsplit : Complex.exp L =
      Complex.exp (L.re : ℂ) * Complex.exp (Complex.I * (L.im : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  have hn : ‖z‖ = c * Real.exp L.re := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
      Complex.norm_exp]
  rw [hn, hz, hsplit]
  push_cast
  ring

/-- `leadingSaddle d q = (d! / d ^ d) * exp (leadingSaddleLog d q)` under the zeta, Gamma and
positive-Hessian domain hypotheses. -/
theorem leadingSaddle_eq_prefactor_mul_exp_leadingSaddleLog
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hZ : 4 ≤ (1 / 2 + saddlePhasePoint d q).re)
    (hG : saddlePhasePoint d q ∈ GammaCore.grDomain)
    (hH : 0 < (saddleHessian d q).re) :
    leadingSaddle d q =
      ((d.factorial : ℝ) / (d : ℝ) ^ d : ℂ) *
        Complex.exp (leadingSaddleLog d q) := by
  have hw0 : saddlePhasePoint d q ≠ 0 := by
    rintro h
    have := hG.2
    rw [h] at this
    norm_num at this
  have hbase : (Real.pi / 2 : ℂ) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') (by norm_num)
  have hH0 : saddleHessian d q ≠ 0 := fun h => by simp [h] at hH
  have hden0 : (2 * Real.pi * d * saddleHessian d q : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
      (by exact_mod_cast (by omega : d ≠ 0))) hH0
  have hamp : amplitude d q (-2 * saddleAngle d q) =
      Complex.cpow (Real.pi / 2) (1 / 4) *
        Complex.cpow (saddlePhasePoint d q) (7 / 4) *
        riemannZeta (1 / 2 + saddlePhasePoint d q) *
        gammaRemainder (saddlePhasePoint d q) := rfl
  have hcpowBase : Complex.cpow (Real.pi / 2) (1 / 4) =
      Complex.exp (Complex.log (Real.pi / 2) * (1 / 4)) :=
    Complex.cpow_def_of_ne_zero hbase _
  have hcpowW : Complex.cpow (saddlePhasePoint d q) (7 / 4) =
      Complex.exp (Complex.log (saddlePhasePoint d q) * (7 / 4)) :=
    Complex.cpow_def_of_ne_zero hw0 _
  rw [leadingSaddle, hamp, hcpowBase, hcpowW, ← exp_log_riemannZeta_of_four_le hZ,
    gammaRemainder_eq_exp_gammaLog hG, sqrt_eq_exp hden0, div_eq_mul_inv, ← Complex.exp_neg]
  unfold leadingSaddleLog
  push_cast
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, mul_assoc,
    ← Complex.exp_add]
  congr 2

/-- The principal argument of the lower saddle point is exactly the negative
saddle angle on the scale window. -/
theorem arg_saddlePhasePoint_eq_neg_saddleAngle
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    Complex.arg (saddlePhasePoint d q) = -saddleAngle d q := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  have hT : 0 < scaleT d :=
    lt_trans (by positivity) (scaleT_gt_base d hd)
  have hr : 0 < saddleRadius d (saddleAngle d q) :=
    (saddleRadius_pos_and_eq d hd
      ⟨by linarith [hα0, Real.pi_pos], hαtop.le⟩).1
  rw [saddlePhasePoint_eq_polar, Complex.arg_real_mul _ (mul_pos hT hr),
    show -Complex.I * (saddleAngle d q : ℂ) = ((-saddleAngle d q : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).2
  constructor <;> linarith [hα0, hαtop, Real.pi_pos]

/-- On the scale window, the imaginary part of `leadingSaddleLog d q` is
`d * saddleAction d q + phaseCorrection d q`. -/
theorem leadingSaddleLog_im
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    (leadingSaddleLog d q).im =
      d * saddleAction d q + phaseCorrection d q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hargden : Complex.arg (2 * Real.pi * d * saddleHessian d q) =
      Complex.arg (saddleHessian d q) := by
    rw [show (2 * Real.pi * d * saddleHessian d q : ℂ) =
      ((2 * Real.pi * (d : ℝ) : ℝ) : ℂ) * saddleHessian d q by
        push_cast
        ring]
    exact Complex.arg_real_mul _ (by positivity)
  have hargbase : Complex.arg (Real.pi / 2 : ℂ) = 0 := by
    rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by
      push_cast
      rfl]
    exact Complex.arg_ofReal_of_nonneg (half_pos Real.pi_pos).le
  unfold leadingSaddleLog phaseCorrection saddleAction
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im]
  simp_rw [Complex.log_im]
  rw [hargden, arg_saddlePhasePoint_eq_neg_saddleAngle d hd hq, hargbase]
  norm_num [Complex.normSq]
  ring

/-- Exact polar form of the leading saddle contribution under the natural
zeta, Gamma and positive-Hessian domain hypotheses. -/
theorem leadingSaddle_eq_norm_mul_exp_phase
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d))
    (hZ : 4 ≤ (1 / 2 + saddlePhasePoint d q).re)
    (hG : saddlePhasePoint d q ∈ GammaCore.grDomain)
    (hH : 0 < (saddleHessian d q).re) :
    leadingSaddle d q =
      (‖leadingSaddle d q‖ : ℂ) *
        Complex.exp (Complex.I *
          ((d : ℝ) * saddleAction d q + phaseCorrection d q)) := by
  have hc : 0 < (d.factorial : ℝ) / (d : ℝ) ^ d := by positivity
  have hpolar := eq_norm_mul_exp_I_im_of_eq_pos_mul_exp hc
    (by exact_mod_cast leadingSaddle_eq_prefactor_mul_exp_leadingSaddleLog d hd hZ hG hH)
  rw [leadingSaddleLog_im d hd hq] at hpolar
  simpa using hpolar

/-- The saddle action vanishes at the coalescence point `edgeQ d`. -/
theorem saddleAction_edgeQ (d : ℕ) (hd : 1 ≤ d) :
    saddleAction d (edgeQ d) = 0 := by
  rw [edgeQ]
  simpa using saddleAction_saddleQ d hd
    (show (0 : ℝ) ∈ Icc 0 (Real.pi / 2) from
      ⟨le_rfl, (half_pos Real.pi_pos).le⟩)

/-- The saddle action at the right endpoint `saddleQ d (π / 2)` of the saddle branch. -/
theorem saddleAction_saddleQ_pi_div_two (d : ℕ) (hd : 1 ≤ d) :
    saddleAction d (saddleQ d (Real.pi / 2)) =
      Real.pi + 4 * Real.pi ^ 2 / (scaleT d * scaleLambda d) := by
  have h := saddleAction_saddleQ d hd
    (show Real.pi / 2 ∈ Icc 0 (Real.pi / 2) from
      ⟨(half_pos Real.pi_pos).le, le_rfl⟩)
  rw [saddleRadius_pi_div_two d hd,
    show 2 * (Real.pi / 2) = Real.pi by ring,
    Real.sin_pi, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  have hT : scaleT d ≠ 0 :=
    (lt_trans (by positivity) (scaleT_gt_base d hd)).ne'
  rw [h]
  field_simp [hT, (scaleLambda_pos d hd).ne']
  ring

/-- Bounded endpoint corrections lose at most `2 C` from an action span. -/
theorem totalPhase_span_lower_of_phaseCorrection_bounds
    (d : ℕ) {a b C : ℝ}
    (ha : |phaseCorrection d a| ≤ C)
    (hb : |phaseCorrection d b| ≤ C) :
    (d : ℝ) * (saddleAction d b - saddleAction d a) - 2 * C ≤
      ((d : ℝ) * saddleAction d b + phaseCorrection d b) -
        ((d : ℝ) * saddleAction d a + phaseCorrection d a) := by
  rw [abs_le] at ha hb
  linarith

/-- Endpoint phase corrections bounded by `8` lose at most `16` from an action span. -/
theorem totalPhase_span_lower_of_eight_bounds
    (d : ℕ) {a b : ℝ}
    (ha : |phaseCorrection d a| ≤ 8)
    (hb : |phaseCorrection d b| ≤ 8) :
    (d : ℝ) * (saddleAction d b - saddleAction d a) - 16 ≤
      ((d : ℝ) * saddleAction d b + phaseCorrection d b) -
        ((d : ℝ) * saddleAction d a + phaseCorrection d a) := by
  linarith [totalPhase_span_lower_of_phaseCorrection_bounds d ha hb]

end RiemannJensen
