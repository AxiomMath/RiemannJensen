module

public import RiemannJensen.Analysis.CountingWholeWindow
public import RiemannJensen.Analysis.CountingEffectiveN
public import RiemannJensen.Analysis.CountingWindowEventually
public import RiemannJensen.Analysis.EventualLowerContribution
public import RiemannJensen.Analysis.XiThetaMoments
public import RiemannJensen.MainTheorem.WindowLoss

/-!
# Final counting-window assembly

This module combines the phase geometry and oscillatory estimate on the counting window with
root counting, giving the two-sided root estimate: for some `C > 0` and all `d ≥ 2`, the Jensen
polynomial of degree `d` has at most `C * √(d log d)` nonreal roots and at least
`d - C * √(d log d)` negative roots.

## Main results

* `riemannJensen_main_from_countingWindow`: The two-sided root estimate.
* `exists_negativeJensenRootCount_lower`: The lower bound on the number of negative roots.
* `exists_nonrealJensenRootCount_upper`: The upper bound on the number of nonreal roots.
-/

@[expose] public section

namespace RiemannJensen

open Filter Set Polynomial

/-- Lower endpoint of the fixed oscillation window. -/
noncomputable def eventualCountingLower (d : ℕ) : ℝ :=
  edgeQ d + oscillationM * Real.sqrt (Real.log d / d)

/-- Upper endpoint of the fixed eventual counting window. -/
noncomputable def eventualCountingUpper (d : ℕ) : ℝ :=
  oscillationC0 * scaleT d

/-- Total oscillatory phase on the counting window. -/
noncomputable def countingTotalPhase (d : ℕ) (q : ℝ) : ℝ :=
  (d : ℝ) * saddleAction d q + phaseCorrection d q

/-- The action, and hence the total phase, is continuous on every admissible
counting window. -/
theorem continuousOn_countingTotalPhase_countingWindow (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d) (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112) :
    ContinuousOn (countingTotalPhase d) (countingWindow M c₀ d) := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hsub : countingWindow M c₀ d ⊆ Set.Ioc (edgeQ d) (scaleT d) :=
    fun q hq => (countingWindow_subset_scale_window d hd hM hcsmall hq).1
  have hα : ContinuousOn (saddleAngle d) (countingWindow M c₀ d) :=
    (continuousOn_saddleAngle_on_branch d hd1).mono fun q hq =>
      ⟨(hsub hq).1.le, ((hsub hq).2.trans_lt (scaleT_lt_saddleQ_pi_div_two d hd1)).le⟩
  have hαmem : ∀ q ∈ countingWindow M c₀ d,
      saddleAngle d q ∈ Set.Icc 0 (Real.pi / 2) := by
    intro q hq
    rcases saddle_inverse_on_scale_window d hd1 (hsub hq) with ⟨ha, hb, -⟩
    exact ⟨ha.le, hb.le⟩
  have hr : ContinuousOn
      (fun q => saddleRadius d (saddleAngle d q))
      (countingWindow M c₀ d) :=
    (continuousOn_saddleRadius d hd1).comp hα hαmem
  have haction : ContinuousOn (saddleAction d) (countingWindow M c₀ d) := by
    have hexpr : ContinuousOn (fun q =>
        2 * saddleAngle d q - Real.sin (2 * saddleAngle d q) +
          (2 * Real.pi * saddleRadius d (saddleAngle d q) / scaleLambda d) *
            (Real.sin (saddleAngle d q) -
              saddleAngle d q * Real.cos (saddleAngle d q)))
        (countingWindow M c₀ d) := by
      fun_prop
    exact hexpr.congr fun q hq => saddleAction_eq_on_scale_window d hd1 (hsub hq)
  unfold countingTotalPhase
  exact haction.const_mul d |>.add
    (continuousOn_phaseCorrection_countingWindow
      d hd hlarge hΛ hM hcsmall)

/-- The leading saddle never vanishes on an admissible counting window. -/
theorem norm_leadingSaddle_pos_of_mem_countingWindow (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d) (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112) (hq : q ∈ countingWindow M c₀ d) :
    0 < ‖leadingSaddle d q‖ := by
  have hscale := (countingWindow_subset_scale_window d hd hM hcsmall hq).1
  rw [norm_pos_iff, leadingSaddle_eq_prefactor_mul_exp_leadingSaddleLog d (by omega)
    (countingWindow_saddlePhasePoint_zeta_domain d hd hlarge hM hcsmall hq)
    (saddlePhasePoint_mem_grDomain_on_scale_window d (by omega) hscale)
    (countingWindow_saddleHessian_re_pos d hd hΛ hM hcsmall hq)]
  exact mul_ne_zero (div_ne_zero (by exact_mod_cast d.factorial_ne_zero)
    (pow_ne_zero d (Nat.cast_ne_zero.2 (by omega)))) (Complex.exp_ne_zero _)

/-- Normalized real error after extracting the leading-saddle amplitude and
phase. -/
noncomputable def countingOscillationError (d : ℕ) (q : ℝ) : ℝ :=
  ((rescaledJensen d).eval (-q) -
      2 * ‖leadingSaddle d q‖ * Real.cos (countingTotalPhase d q)) /
    (2 * ‖leadingSaddle d q‖)

/-- On the counting window, the real part of the leading saddle equals its norm times the cosine
of the total phase. -/
theorem countingWindow_leadingSaddle_re_eq_norm_mul_cos (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d) (hΛ : 4 * Real.pi ≤ scaleLambda d)
    {M c₀ q : ℝ} (hM : 0 < M) (hcsmall : c₀ ≤ Real.pi / 112) (hq : q ∈ countingWindow M c₀ d) :
    (leadingSaddle d q).re =
      ‖leadingSaddle d q‖ * Real.cos (countingTotalPhase d q) := by
  have hpolar := countingWindow_leadingSaddle_eq_norm_mul_exp_phase
    d hd hlarge hΛ hM hcsmall hq
  have hphase :
      (((d : ℝ) : ℂ) * (saddleAction d q : ℂ) +
          (phaseCorrection d q : ℂ)) =
        (countingTotalPhase d q : ℂ) := by
    push_cast [countingTotalPhase]
    rfl
  rw [hphase, mul_comm Complex.I, Complex.exp_mul_I] at hpolar
  simpa [Complex.cos_ofReal_re] using congrArg Complex.re hpolar

/-- The normalized error gives an exact oscillatory formula wherever the
leading saddle is nonzero. -/
theorem countingOscillationError_formula
    (d : ℕ) (q : ℝ) (hL : 0 < ‖leadingSaddle d q‖) :
    (rescaledJensen d).eval (-q) =
      2 * ‖leadingSaddle d q‖ *
        (Real.cos (countingTotalPhase d q) + countingOscillationError d q) := by
  unfold countingOscillationError
  field_simp [hL.ne']
  ring

/-- If the raw error is below the saddle norm and the real part of the leading saddle has polar
form, then the normalized error is below `1 / 2`. -/
theorem abs_countingOscillationError_lt_half
    (d : ℕ) (q : ℝ) (hL : 0 < ‖leadingSaddle d q‖)
    (herr :
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| <
        ‖leadingSaddle d q‖)
    (hre : (leadingSaddle d q).re =
      ‖leadingSaddle d q‖ * Real.cos (countingTotalPhase d q)) :
    |countingOscillationError d q| < 1 / 2 := by
  rw [hre] at herr
  unfold countingOscillationError
  rw [abs_div, abs_of_pos (mul_pos two_pos hL), div_lt_iff₀ (mul_pos two_pos hL)]
  simpa [mul_assoc] using herr

/-- For all large `d`, on the oscillation window the rescaled Jensen polynomial differs from twice
the real part of the leading saddle by less than the saddle norm. -/
theorem eventually_abs_rescaledJensen_sub_lt_norm_leadingSaddle :
    ∀ᶠ d : ℕ in atTop, ∀ q ∈ countingWindow oscillationM oscillationC0 d,
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| < ‖leadingSaddle d q‖ := by
  obtain ⟨C, -, hest⟩ := exists_eventually_oscillation
  have hdecay : Filter.Tendsto
      (fun d : ℕ => C * Real.log d ^ (-((1 : ℝ) / 10)))
      Filter.atTop (nhds 0) := by
    have hp := (tendsto_rpow_neg_atTop
      (show (0 : ℝ) < 1 / 10 by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_apply, mul_zero] using hp.const_mul C
  have hsmall : ∀ᶠ d : ℕ in Filter.atTop,
      C * Real.log d ^ (-((1 : ℝ) / 10)) < 1 :=
    (tendsto_order.1 hdecay).2 1 zero_lt_one
  have hgeom : ∀ᶠ d : ℕ in Filter.atTop,
      2 ≤ d ∧
      4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d ∧
      4 * Real.pi ≤ scaleLambda d := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ),
      Filter.tendsto_atTop.1 tendsto_scaleLambda_atTop
        (24 * Real.pi)] with d hd hΛ
    exact ⟨hd, four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ,
      by linarith [Real.pi_pos]⟩
  filter_upwards [hest, hsmall, hgeom] with d hestd hsm hd
  intro q hq
  have hL := norm_leadingSaddle_pos_of_mem_countingWindow
    d hd.1 hd.2.1 hd.2.2
    (one_pos.trans_le one_le_oscillationM)
    (oscillationC0_le.trans eventualCountingC0_le) hq
  have hupper :
      C * ‖leadingSaddle d q‖ * Real.log d ^ (-(1 : ℝ) / 10) <
        ‖leadingSaddle d q‖ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_lt_mul_of_pos_right hsm hL
  exact lt_of_le_of_lt (hestd q hq) hupper

/-- The total amount subtracted from `dπ` in the explicit endpoint phase
estimate for the oscillation window. -/
noncomputable def countingPhaseDeficit (d : ℕ) : ℝ :=
  (d : ℝ) *
      (12 * Real.sqrt 2 / Real.sqrt (oscillationC0 * scaleT d) +
        (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
          (Real.sqrt (oscillationM *
            Real.sqrt (Real.log d / d))) ^ 3) +
    16

/-- The integer loss used in the final phase-crossing count. -/
noncomputable def countingRootLoss (d : ℕ) : ℕ :=
  Nat.ceil (countingPhaseDeficit d / Real.pi) + 1

/-- The cubic lower-edge phase loss is bounded by a fixed multiple of
`sqrt (d log d)`. -/
theorem edge_phase_loss_le_sqrt {d : ℕ} (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    (d : ℝ) * (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 ≤
      (M * Real.sqrt M) * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  let x := Real.log (d : ℝ) / d
  let τ := M * Real.sqrt x
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsx1 : Real.sqrt x ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hdpos).2 (Real.log_le_self d.cast_nonneg))
  have hτM : τ ≤ M := by
    dsimp [τ]
    nlinarith [mul_le_mul_of_nonneg_left hsx1 hM]
  calc
    (d : ℝ) * (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 =
        (d : ℝ) * τ * Real.sqrt τ := by
      rw [pow_succ, Real.sq_sqrt (mul_nonneg hM (Real.sqrt_nonneg x))]
      ring
    _ ≤ (d : ℝ) * τ * Real.sqrt M := by gcongr
    _ = (M * Real.sqrt M) *
        Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
      rw [← nat_mul_sqrt_log_div_nat hd]
      dsimp [τ, x]
      ring

/-- For some `C > 0` and all `d ≥ 3`, the phase deficit is at most `C * √(d log d)`. -/
theorem exists_countingPhaseDeficit_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      countingPhaseDeficit d ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  obtain ⟨Ctail, hCtail, htail⟩ :=
    exists_upper_window_loss_bound oscillationC0_pos
  let A : ℝ := (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3
  have hA : 0 ≤ A := by positivity
  have hM : 0 ≤ oscillationM := one_le_oscillationM.trans' (by norm_num)
  refine ⟨12 * Real.sqrt 2 * Ctail + A * (oscillationM * Real.sqrt oscillationM) + 16,
    by positivity, fun d hd => ?_⟩
  have hdpos : (0 : ℝ) < d := by positivity
  have hlog : Real.log (d : ℝ) ≤ d :=
    (Real.log_le_sub_one_of_pos hdpos).trans (by linarith)
  have hsqrt := one_le_sqrt_nat_mul_log_nat (by omega : 2 ≤ d)
  have htailmul := mul_le_mul_of_nonneg_left (htail d hd)
    (by positivity : (0 : ℝ) ≤ 12 * Real.sqrt 2)
  have hedgemul := mul_le_mul_of_nonneg_left (edge_phase_loss_le_sqrt (d := d) (by omega) hM) hA
  unfold countingPhaseDeficit
  dsimp [A] at hedgemul ⊢
  ring_nf at htailmul hedgemul ⊢
  nlinarith

/-- The phase deficit is nonnegative. -/
theorem countingPhaseDeficit_nonneg (d : ℕ) : 0 ≤ countingPhaseDeficit d := by
  unfold countingPhaseDeficit
  positivity

/-- The chosen integer loss is eventually bounded by a positive multiple of
`sqrt (d log d)`. -/
theorem exists_countingRootLoss_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      (countingRootLoss d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  obtain ⟨Cdef, hCdef, hdef⟩ := exists_countingPhaseDeficit_le_sqrt
  refine ⟨Cdef / Real.pi + 2, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with d hd
  have hS := one_le_sqrt_nat_mul_log_nat (by omega : 2 ≤ d)
  have hceil := Nat.ceil_lt_add_one
    (div_nonneg (countingPhaseDeficit_nonneg d) Real.pi_pos.le)
  have hdiv : countingPhaseDeficit d / Real.pi ≤
      Cdef / Real.pi * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right Real.pi_pos).2 (hdef d hd)
  have hcoef : 0 ≤ Cdef / Real.pi := by positivity
  unfold countingRootLoss
  push_cast
  nlinarith

/-- The square-root-sized integer loss is eventually smaller than the degree,
so natural subtraction agrees with real subtraction in the phase budget. -/
theorem eventually_countingRootLoss_le_degree :
    ∀ᶠ d : ℕ in atTop, countingRootLoss d ≤ d := by
  obtain ⟨C, hC, hloss⟩ := exists_countingRootLoss_le_sqrt
  have hratio : Tendsto
      (fun d : ℕ => Real.log (d : ℝ) / d) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at this
    exact this.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto
      (fun d : ℕ => Real.sqrt (Real.log (d : ℝ) / d))
      atTop (nhds 0) :=
    (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp hratio
  have hscaled : Tendsto
      (fun d : ℕ => C * Real.sqrt (Real.log (d : ℝ) / d))
      atTop (nhds 0) := by
    simpa using hsqrt.const_mul C
  have hsmall : ∀ᶠ d : ℕ in atTop,
      C * Real.sqrt (Real.log (d : ℝ) / d) < 1 :=
    (tendsto_order.1 hscaled).2 1 zero_lt_one
  filter_upwards [hloss, hsmall,
    Filter.eventually_ge_atTop (1 : ℕ)] with d hloss hsmall hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlt : (countingRootLoss d : ℝ) < d :=
    calc
      (countingRootLoss d : ℝ) ≤
          C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := hloss
      _ = (d : ℝ) *
          (C * Real.sqrt (Real.log (d : ℝ) / d)) := by
        rw [← nat_mul_sqrt_log_div_nat hd]
        ring
      _ < d := by nlinarith
  exact_mod_cast hlt.le

/-- The explicit integer loss fits under the verified real phase span. -/
theorem eventually_countingRootLoss_phase_budget :
    ∀ᶠ d : ℕ in atTop,
      (((d - countingRootLoss d) + 1 : ℕ) : ℝ) * Real.pi ≤
        (d : ℝ) *
          ((Real.pi - 12 * Real.sqrt 2 /
              Real.sqrt (oscillationC0 * scaleT d)) -
            (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
              (Real.sqrt (oscillationM *
                Real.sqrt (Real.log d / d))) ^ 3) - 16 := by
  filter_upwards [eventually_countingRootLoss_le_degree,
    Filter.eventually_ge_atTop (2 : ℕ)] with d hloss hd
  let x := countingPhaseDeficit d / Real.pi
  have hdef : countingPhaseDeficit d ≤ (Nat.ceil x : ℝ) * Real.pi :=
    (div_le_iff₀ Real.pi_pos).1 (Nat.le_ceil x)
  have hceil : Nat.ceil x + 1 = countingRootLoss d := rfl
  have hceil_le : Nat.ceil x + 1 ≤ d := by simpa [hceil] using hloss
  have hcastsub :
      (((d - (Nat.ceil x + 1)) + 1 : ℕ) : ℝ) =
        (d : ℝ) - (Nat.ceil x : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hceil_le]
    push_cast
    ring
  rw [← hceil, hcastsub]
  unfold countingPhaseDeficit at hdef
  nlinarith [Real.pi_pos]

/-- At a single degree `d`, the oscillatory estimate on the oscillation window together with a
total-phase span of `(n + 1) π` across it gives at least `n` negative roots. -/
theorem le_negativeJensenRootCount_of_totalPhase_span {d n : ℕ} (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d) (hΛ : 4 * Real.pi ≤ scaleLambda d)
    (hosc : ∀ q ∈ countingWindow oscillationM oscillationC0 d,
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| < ‖leadingSaddle d q‖)
    (hab : eventualCountingLower d ≤ eventualCountingUpper d)
    (hspan : ((n + 1 : ℕ) : ℝ) * Real.pi ≤
      countingTotalPhase d (eventualCountingUpper d) -
        countingTotalPhase d (eventualCountingLower d)) :
    n ≤ negativeJensenRootCount d := by
  have hM : 0 < oscillationM := one_pos.trans_le one_le_oscillationM
  have hc : oscillationC0 ≤ Real.pi / 112 := oscillationC0_le.trans eventualCountingC0_le
  have hR : ∀ q ∈ countingWindow oscillationM oscillationC0 d, 0 < ‖leadingSaddle d q‖ :=
    fun q hq => norm_leadingSaddle_pos_of_mem_countingWindow d hd hlarge hΛ hM hc hq
  have ha : 0 < eventualCountingLower d :=
    add_pos_of_nonneg_of_pos (edgeQ_nonneg d (hd.trans' (by norm_num)))
      (mul_pos hM (Real.sqrt_pos.2 (div_pos (Real.log_pos (by exact_mod_cast hd))
        (by positivity))))
  exact le_negativeJensenRootCount_of_phaseSpan d (hd.trans' (by norm_num))
    (gammaCoeff_pos d).ne' (fun q => ‖leadingSaddle d q‖) (countingOscillationError d)
    (countingTotalPhase d) _ _ ha hab
    ((rescaledJensen d).continuous.comp continuous_neg).continuousOn
    (continuousOn_countingTotalPhase_countingWindow d hd hlarge hΛ hM hc) hR
    (fun q hq => abs_countingOscillationError_lt_half d q (hR q hq) (hosc q hq)
      (countingWindow_leadingSaddle_re_eq_norm_mul_cos d hd hlarge hΛ hM hc hq))
    (fun q hq => countingOscillationError_formula d q (hR q hq)) hspan

/-- If an integer loss eventually fits the phase budget and is eventually at most
`C₀ * √(d log d)`, then eventually there are at least `d - C₀ * √(d log d)` negative roots. -/
theorem exists_eventual_negativeJensenRootCount_lower_of_counting_loss
    (loss : ℕ → ℕ) {C₀ : ℝ}
    (hbudget : ∀ᶠ d : ℕ in atTop,
      (((d - loss d) + 1 : ℕ) : ℝ) * Real.pi ≤
        (d : ℝ) *
          ((Real.pi - 12 * Real.sqrt 2 /
              Real.sqrt (oscillationC0 * scaleT d)) -
            (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
              (Real.sqrt (oscillationM *
                Real.sqrt (Real.log d / d))) ^ 3) - 16)
    (hloss : ∀ᶠ d : ℕ in atTop,
      (loss d : ℝ) ≤ C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) :
    ∃ D : ℕ, ∀ d ≥ D,
      (d : ℝ) - C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ) := by
  obtain ⟨Dphase, hphase⟩ :=
    exists_eventual_countingWindow_totalPhase_span_lower_of
      oscillationM oscillationC0
      (one_pos.trans_le one_le_oscillationM)
      oscillationC0_pos
      (oscillationC0_le.trans eventualCountingC0_le)
  obtain ⟨Dwin, hwin⟩ :=
    exists_countingWindow_nonempty_threshold_of oscillationM oscillationC0
      (one_pos.trans_le one_le_oscillationM) oscillationC0_pos
  refine Filter.eventually_atTop.1 ?_
  filter_upwards [Filter.eventually_ge_atTop 2,
    Filter.tendsto_atTop.1 tendsto_scaleLambda_atTop (24 * Real.pi),
    eventually_abs_rescaledJensen_sub_lt_norm_leadingSaddle,
    Filter.eventually_atTop.2 ⟨Dphase, hphase⟩,
    Filter.eventually_atTop.2 ⟨Dwin, hwin⟩, hbudget, hloss]
    with d hd hΛ hoscd hphased hwind hbudgetd hlossd
  have hcount : d - loss d ≤ negativeJensenRootCount d :=
    le_negativeJensenRootCount_of_totalPhase_span hd
      (four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ) (by linarith [Real.pi_pos]) hoscd hwind
      (hbudgetd.trans (by
        simpa [eventualCountingLower, eventualCountingUpper, countingTotalPhase] using hphased))
  refine negativeJensenRootCount_cast_lower_of_count hcount ?_
  have hnat : (d : ℝ) ≤ ((d - loss d : ℕ) : ℝ) + loss d := by
    exact_mod_cast (by omega : d ≤ d - loss d + loss d)
  linarith

/-- If an integer loss `loss d` eventually fits the phase budget and is eventually at most
`C₀ * √(d log d)`, then for some `C > 0` and all `d ≥ 2` there are at most `C * √(d log d)`
nonreal roots and at least `d - C * √(d log d)` negative roots, counted by
`nonrealJensenRootCount` and `negativeJensenRootCount`. -/
theorem riemannJensen_main_of_counting_loss
    (loss : ℕ → ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hbudget : ∀ᶠ d : ℕ in atTop,
      (((d - loss d) + 1 : ℕ) : ℝ) * Real.pi ≤
        (d : ℝ) *
          ((Real.pi - 12 * Real.sqrt 2 /
              Real.sqrt (oscillationC0 * scaleT d)) -
            (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
              (Real.sqrt (oscillationM *
                Real.sqrt (Real.log d / d))) ^ 3) - 16)
    (hloss : ∀ᶠ d : ℕ in atTop,
      (loss d : ℝ) ≤ C₀ * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) := by
  obtain ⟨D, hD⟩ :=
    exists_eventual_negativeJensenRootCount_lower_of_counting_loss
      loss hbudget hloss
  exact riemannJensen_main_of_eventual_negative_root_bound
    (fun d _ => gammaCoeff_pos d) hC₀ hD

/-- The complete two-sided root estimate obtained from the oscillation window,
with every analytic and numerical input discharged. -/
theorem riemannJensen_main_from_countingWindow :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ((nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ))) ∧
      ((d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ)) := by
  obtain ⟨C, hC, hloss⟩ := exists_countingRootLoss_le_sqrt
  exact riemannJensen_main_of_counting_loss
    countingRootLoss hC eventually_countingRootLoss_phase_budget hloss

/-- For some `C > 0` and all `d ≥ 2`, there are at least `d - C * √(d log d)` negative roots. -/
theorem exists_negativeJensenRootCount_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (d : ℝ) - C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) ≤
        (negativeJensenRootCount d : ℝ) := by
  obtain ⟨C, hC, hmain⟩ := riemannJensen_main_from_countingWindow
  exact ⟨C, hC, fun d hd => (hmain d hd).2⟩

/-- For some `C > 0` and all `d ≥ 2`, there are at most `C * √(d log d)` nonreal roots. -/
theorem exists_nonrealJensenRootCount_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (nonrealJensenRootCount d : ℝ) ≤
        C * Real.sqrt ((d : ℝ) * Real.log (d : ℝ)) := by
  obtain ⟨C, hC, hmain⟩ := riemannJensen_main_from_countingWindow
  exact ⟨C, hC, fun d hd => (hmain d hd).1⟩

end RiemannJensen
