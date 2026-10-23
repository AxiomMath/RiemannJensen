module

public import RiemannJensen.Dedekind.GammaLogSector
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Cauchy bound for the Dedekind Gamma logarithmic derivative

For a number field `K`, the derivative of `dedekindGammaLog K` is bounded by a constant multiple
of `‖w‖⁻²` on the closed right half-plane `|arg w| ≤ π / 2`, outside a disk depending on `K`.

## Main results

* `norm_deriv_dedekindGammaLog_le`: there are `C, W > 0` such that
  `‖deriv (dedekindGammaLog K) w‖ ≤ C / ‖w‖ ^ 2` whenever `|arg w| ≤ π / 2` and `W ≤ ‖w‖`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Metric
open scoped ComplexOrder

noncomputable section

private theorem slit_of_abs_arg_lt_two_pi_div_three {z : ℂ}
    (hz0 : z ≠ 0) (hz : |Complex.arg z| < 2 * Real.pi / 3) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨fun h => ?_, hz0⟩
  rw [h, abs_of_pos Real.pi_pos] at hz
  linarith [Real.pi_pos]

private theorem shifted_real_not_pole {z : ℂ} (hz : z ∈ Complex.slitPlane) (m : ℕ) :
    z / 2 + 1 / 4 ≠ -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  norm_num at him hre
  rw [Complex.mem_slitPlane_iff] at hz
  rcases hz with hz | hz
  · nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · exact hz (by linarith)

private theorem shifted_complex_not_pole {z : ℂ} (hz : z ∈ Complex.slitPlane) (m : ℕ) :
    z + 1 / 2 ≠ -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  norm_num at him hre
  rw [Complex.mem_slitPlane_iff] at hz
  rcases hz with hz | hz
  · nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · exact hz (by linarith)

private theorem sqrt_two_pi_ne_zero :
    Complex.sqrt ((2 : ℂ) * Real.pi) ≠ 0 := by
  have hnonneg : 0 ≤ (((2 * Real.pi : ℝ) : ℂ)) :=
    RCLike.nonneg_iff_exists_ofReal.mpr ⟨2 * Real.pi, by positivity, rfl⟩
  have heq : Complex.sqrt ((2 : ℂ) * Real.pi) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    rw [show (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
      Complex.sqrt_of_nonneg hnonneg]
    norm_num
  rw [heq]
  exact ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))

private theorem differentiableAt_dedekindGammaRemainderReal {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ dedekindGammaRemainderReal z := by
  unfold dedekindGammaRemainderReal
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hz2 : z / 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff] at hz ⊢
    rcases hz with hz | hz
    · left
      norm_num
      positivity
    · exact Or.inr (by simpa using hz)
  have hnum : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2 + 1 / 4)) z :=
    (Complex.differentiableAt_Gamma _ (shifted_real_not_pole hz)).comp z (by fun_prop)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (w / 2) ^ (w / 2 - 1 / 4)) z :=
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w / 2) z).cpow (by fun_prop) hz2
  have hden : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sqrt (2 * Real.pi) *
        (w / 2) ^ (w / 2 - 1 / 4) * Complex.exp (-w / 2)) z := by
    fun_prop
  have hden0 : Complex.sqrt (2 * Real.pi) *
        (z / 2) ^ (z / 2 - 1 / 4) * Complex.exp (-z / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero sqrt_two_pi_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hz0 two_ne_zero))))
      (Complex.exp_ne_zero _)
  exact hnum.div hden hden0

private theorem differentiableAt_dedekindGammaRemainderComplex {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ dedekindGammaRemainderComplex z := by
  unfold dedekindGammaRemainderComplex
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hnum : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z :=
    (Complex.differentiableAt_Gamma _ (shifted_complex_not_pole hz)).comp z (by fun_prop)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ w) z :=
    differentiableAt_id.cpow differentiableAt_id hz
  have hden : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sqrt (2 * Real.pi) * w ^ w * Complex.exp (-w)) z := by
    fun_prop
  have hden0 : Complex.sqrt (2 * Real.pi) * z ^ z * Complex.exp (-z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero sqrt_two_pi_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)))
      (Complex.exp_ne_zero _)
  exact hnum.div hden hden0

private theorem differentiableAt_dedekindGammaRemainder
    (K : Type) [Field K] [NumberField K] {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (dedekindGammaRemainder K) z := by
  unfold dedekindGammaRemainder
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hcorr : DifferentiableAt ℂ (fun u : ℂ => 1 - 1 / (4 * u ^ 2)) z := by
    fun_prop (disch := simp [hz0])
  exact (hcorr.mul ((differentiableAt_dedekindGammaRemainderReal hz).pow _)).mul
    ((differentiableAt_dedekindGammaRemainderComplex hz).pow _)

private theorem differentiableAt_dedekindGammaLog
    (K : Type) [Field K] [NumberField K] {z : ℂ}
    (hz : z ∈ Complex.slitPlane)
    (hnear : ‖dedekindGammaRemainder K z - 1‖ < 1) :
    DifferentiableAt ℂ (dedekindGammaLog K) z :=
  (differentiableAt_dedekindGammaRemainder K hz).clog
    (by simpa using Complex.mem_slitPlane_of_norm_lt_one hnear)

/-- Points of the closed ball of radius `‖w‖ / 4` around a point `w` of the closed right
half-plane lie in the sector `|arg z| < 2π / 3` and satisfy `3 ‖w‖ / 4 ≤ ‖z‖`. -/
theorem abs_arg_lt_and_norm_ge_of_mem_closedBall {w z : ℂ} (hwre : 0 ≤ w.re) (hnw : 0 < ‖w‖)
    (hz : z ∈ closedBall w (‖w‖ / 4)) :
    |Complex.arg z| < 2 * Real.pi / 3 ∧ 3 * ‖w‖ / 4 ≤ ‖z‖ := by
  have hdist : ‖z - w‖ ≤ ‖w‖ / 4 := mem_closedBall_iff_norm.mp hz
  have hnormlow : 3 * ‖w‖ / 4 ≤ ‖z‖ := by linarith [norm_sub_norm_le w z, norm_sub_rev z w]
  have hzre : -(‖w‖ / 4) ≤ z.re := by
    have hre : |z.re - w.re| ≤ ‖z - w‖ := Complex.abs_re_le_norm (z - w)
    rw [abs_le] at hre
    linarith
  have hzsec : Real.cos (2 * Real.pi / 3) * ‖z‖ < z.re := by
    rw [GammaSector.cos_two_pi_div_three]
    nlinarith
  exact ⟨GammaSector.abs_arg_lt_of_cos_mul_lt (norm_pos_iff.mp (by linarith)) (by positivity)
    (by linarith [Real.pi_pos]) hzsec, hnormlow⟩

/-- On the closed sector `|arg w| ≤ π / 2` and outside a disk depending on `K`, the derivative
of `dedekindGammaLog K` is bounded by `C / ‖w‖ ^ 2` for some constant `C > 0`. -/
theorem norm_deriv_dedekindGammaLog_le
    (K : Type) [Field K] [NumberField K] :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ w : ℂ, |Complex.arg w| ≤ Real.pi / 2 → W ≤ ‖w‖ →
        ‖deriv (dedekindGammaLog K) w‖ ≤ C / ‖w‖ ^ 2 := by
  obtain ⟨C₀, W₀, hC₀, hW₀, hrem⟩ :=
    GammaSector.dedekindGammaRemainder_tends_one K
  let B : ℝ := max W₀ (2 * C₀)
  refine ⟨8 * C₀, max 1 (2 * B), by positivity,
    zero_lt_one.trans_le (le_max_left _ _), fun w hwarg hwW => ?_⟩
  have hnw : 0 < ‖w‖ := zero_lt_one.trans_le ((le_max_left _ _).trans hwW)
  have hsec : ∀ z ∈ closedBall w (‖w‖ / 4),
      |Complex.arg z| < 2 * Real.pi / 3 ∧ 3 * ‖w‖ / 4 ≤ ‖z‖ := fun z hz =>
    abs_arg_lt_and_norm_ge_of_mem_closedBall (Complex.abs_arg_le_pi_div_two_iff.mp hwarg) hnw hz
  have hlarge : ∀ z ∈ closedBall w (‖w‖ / 4), B ≤ ‖z‖ := fun z hz => by
    linarith [(hsec z hz).2, (le_max_right _ _).trans hwW]
  have hnz : ∀ z ∈ closedBall w (‖w‖ / 4), 0 < ‖z‖ := fun z hz =>
    hW₀.trans_le ((le_max_left _ _).trans (hlarge z hz))
  have hremz : ∀ z ∈ closedBall w (‖w‖ / 4), ‖dedekindGammaRemainder K z - 1‖ ≤ C₀ / ‖z‖ :=
    fun z hz => hrem z (hsec z hz).1.le ((le_max_left _ _).trans (hlarge z hz))
  have hhalf : ∀ z ∈ closedBall w (‖w‖ / 4), ‖dedekindGammaRemainder K z - 1‖ ≤ 1 / 2 := by
    intro z hz
    refine (hremz z hz).trans ?_
    rw [div_le_iff₀ (hnz z hz)]
    linarith [(le_max_right _ _).trans (hlarge z hz)]
  have hdiff : DiffContOnCl ℂ (dedekindGammaLog K) (ball w (‖w‖ / 4)) :=
    DifferentiableOn.diffContOnCl_ball (U := closedBall w (‖w‖ / 4)) (fun z hz =>
      (differentiableAt_dedekindGammaLog K
        (slit_of_abs_arg_lt_two_pi_div_three (norm_pos_iff.mp (hnz z hz)) (hsec z hz).1)
        ((hhalf z hz).trans_lt (by norm_num))).differentiableWithinAt) subset_rfl
  have hbound : ∀ z ∈ sphere w (‖w‖ / 4), ‖dedekindGammaLog K z‖ ≤ 2 * C₀ / ‖w‖ := by
    intro z hz
    replace hz := sphere_subset_closedBall hz
    have hlog := norm_log_one_add_half_le_self (hhalf z hz)
    rw [add_sub_cancel] at hlog
    rw [dedekindGammaLog]
    calc
      ‖Complex.log (dedekindGammaRemainder K z)‖ ≤ 3 / 2 * (C₀ / ‖z‖) :=
        hlog.trans (mul_le_mul_of_nonneg_left (hremz z hz) (by norm_num))
      _ ≤ 2 * C₀ / ‖w‖ := by
        rw [show 3 / 2 * (C₀ / ‖z‖) = (3 * C₀ / 2) / ‖z‖ by ring,
          div_le_div_iff₀ (hnz z hz) hnw]
        nlinarith [(hsec z hz).2]
  refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdiff hbound).trans
    (le_of_eq ?_)
  field_simp
  ring

end

end RiemannJensen
