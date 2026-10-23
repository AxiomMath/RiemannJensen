module

public import RiemannJensen.Dedekind.CanonicalFinalAssembly
public import RiemannJensen.Dedekind.ContourWindowGeometry

/-!
# The Dedekind oscillatory formula from the lower-contour asymptotic

A relative estimate for the lower-contour contribution against the leading saddle term on a
counting window implies the oscillatory formula `DedekindOscillation K`.

## Main results

* `dedekind_oscillation_of_lower_contribution`: a relative lower-contribution estimate on a
  sufficiently small counting window implies `DedekindOscillation K`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- If, for all large `d`, the lower-contour contribution differs from the leading saddle term by
at most `C * ‖dedekindLeadingSaddle K d q‖ * (log d) ^ (-1/10)` on a counting window with
`c₀ ≤ π / 128`, then `DedekindOscillation K` holds. -/
theorem dedekind_oscillation_of_lower_contribution
    {M c₀ C : ℝ} (hM : 0 < M) (hc₀ : 0 < c₀)
    (hc₀small : c₀ ≤ Real.pi / 128)
    (hlower : ∀ᶠ d : ℕ in atTop,
      ∀ q ∈ dedekindCountingWindow K M c₀ d,
        ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖ ≤
          C * ‖dedekindLeadingSaddle K d q‖ *
            Real.log (d : ℝ) ^ (-(1 / 10 : ℝ))) :
    DedekindOscillation K := by
  refine ⟨M, c₀, 2 * C, hM, hc₀, ?_⟩
  filter_upwards [hlower, dedekind_contour_local_re K,
    eventually_ge_atTop 2] with d hlow hlocal hd2
  intro q hq
  have hd1 : 1 ≤ d := by omega
  have hA : 0 < dedekindScaleA K := by
    unfold dedekindScaleA
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)
  have hT : 0 < dedekindScaleT K d :=
    (mul_pos hA (Real.exp_pos 1)).trans (dedekindScaleT_gt_base K d hd1)
  have hτ : 0 < dedekindEdgeOffset M d := by
    unfold dedekindEdgeOffset
    exact mul_pos hM (Real.sqrt_pos.2 (div_pos
      (Real.log_pos (by exact_mod_cast hd2)) (by positivity)))
  have hedge : dedekindEdgeQ K d < q := (lt_add_of_pos_right _ hτ).trans_le hq.1
  have hqc : q ≤ c₀ * dedekindScaleT K d := hq.2
  have hqT : q ≤ dedekindScaleT K d :=
    hqc.trans (mul_le_of_le_one_left hT.le (by linarith [Real.pi_lt_four]))
  have hmem : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hedge, hqT⟩
  have hrange := dedekindSaddle_inverse_range K d hd1 hmem
  have hαcc : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) :=
    ⟨hrange.1.le, hrange.2.le⟩
  have hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q) :=
    dedekindSaddleRadius_pos K d hd1 hαcc
  have hwidth : 0 ≤ dedekindLocalWidth K d q := by
    unfold dedekindLocalWidth dedekindLocalEpsilon
    have hcos : 0 ≤ Real.cos (dedekindSaddleAngle K d q) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hαcc.1, Real.pi_pos], hαcc.2⟩
    exact mul_nonneg (by norm_num) (le_min hαcc.1 hcos)
  have hlocalre := hlocal q hedge hqT (-2 * dedekindSaddleAngle K d q)
    ⟨by linarith, by linarith⟩
  have hqpos : 0 < q := by
    have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd1 hαcc
    rw [dedekindSaddle_inverse K d hd1 hmem] at hqr
    nlinarith [sq_nonneg (dedekindSaddleRadius K d (dedekindSaddleAngle K d q))]
  have hratio : 4 ≤ Real.pi / 32 * dedekindScaleT K d / q := by
    rw [le_div_iff₀ hqpos]
    linarith [mul_le_mul_of_nonneg_right hc₀small hT.le]
  have hw_norm : ‖dedekindContourW K d q (-2 * dedekindSaddleAngle K d q)‖ =
      dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) := by
    unfold dedekindContourW
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.norm_real, abs_of_pos hT, abs_of_pos hr]
  have hR : 1 < dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) := by
    rw [← hw_norm]
    linarith [hratio.trans hlocalre,
      Complex.re_le_norm (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q))]
  have hreal : (rescaledDedekindJensenK K d).eval (-q) =
      2 * (dedekindLowerContribution K d q).re := by
    simpa using congrArg Complex.re (dedekind_cauchy_two_re_lowerContribution K d hd1 q hr hR)
  have hre : |(dedekindLowerContribution K d q).re - (dedekindLeadingSaddle K d q).re| ≤
      ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖ := by
    simpa using Complex.abs_re_le_norm
      (dedekindLowerContribution K d q - dedekindLeadingSaddle K d q)
  rw [hreal, ← mul_sub, abs_mul, abs_two]
  linarith [hre.trans (hlow q hq)]

end

end RiemannJensen
