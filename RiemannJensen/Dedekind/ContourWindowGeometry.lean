module

public import RiemannJensen.Dedekind.AmplitudeLocal
public import RiemannJensen.Dedekind.SaddleHessianEventual
public import RiemannJensen.Dedekind.SaddleInverseAction

/-!
# Geometry of the Dedekind local contour window

For all sufficiently large `d` and every `q` with `dedekindEdgeQ K d < q ≤ dedekindScaleT K d`,
the contour `dedekindContourW K d q` has real part at least `(π / 32) * dedekindScaleT K d / q`
on the local arc of half-width `dedekindLocalWidth K d q` around `-2 * dedekindSaddleAngle K d q`.
Consequently, for `q ≤ c₀ * dedekindScaleT K d` with `c₀ ≤ π / 128`, the local arc lies in the
half-plane `4 ≤ Re(1/2 + w)`, and the saddle amplitude does not vanish.

## Main results

* `dedekind_contour_local_re`: the lower bound on the real part of the contour on the local arc.
* `dedekind_contour_zeta_domain`: the local arc lies in the half-plane `4 ≤ Re(1/2 + w)`.
* `dedekind_saddle_amplitude_nonzero`: the saddle amplitude is nonzero on the counting window.
* `eventually_normalizedDedekindLocalAmplitude_zero`: the normalized local amplitude equals `1`
  at `0` on the counting window.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem dedekindContourW_local_re_ge
    (d : ℕ) (q t : ℝ)
    (hR : 0 ≤ dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (ht : |t| ≤ Real.cos (dedekindSaddleAngle K d q)) :
    dedekindScaleT K d *
          dedekindSaddleRadius K d (dedekindSaddleAngle K d q) *
          Real.cos (dedekindSaddleAngle K d q) / 2 ≤
      (dedekindContourW K d q
        (-2 * dedekindSaddleAngle K d q + t)).re := by
  set α := dedekindSaddleAngle K d q with hα
  rw [dedekindContourW_re, ← hα, show (-2 * α + t) / 2 = -(α - t / 2) by ring, Real.cos_neg]
  have hlip := Real.abs_cos_sub_cos_le (α - t / 2) α
  rw [show α - t / 2 - α = -(t / 2) by ring, abs_neg, abs_div, abs_two] at hlip
  have hc : Real.cos α / 2 ≤ Real.cos (α - t / 2) := by
    linarith [neg_abs_le (Real.cos (α - t / 2) - Real.cos α)]
  linarith [mul_le_mul_of_nonneg_left hc hR]

private theorem dedekindSaddleAngle_mem_Icc {d : ℕ} (hd1 : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) :=
  ⟨(dedekindSaddle_inverse_range K d hd1 hq).1.le, (dedekindSaddle_inverse_range K d hd1 hq).2.le⟩

private theorem one_le_mul_dedekindSaddleRadius_sq {d : ℕ} (hd1 : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    1 ≤ q * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 := by
  have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd1 (dedekindSaddleAngle_mem_Icc K hd1 hq)
  rwa [dedekindSaddle_inverse K d hd1 hq] at hqr

private theorem pos_of_mem_dedekindWindow {d : ℕ} (hd1 : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) : 0 < q := by
  nlinarith [one_le_mul_dedekindSaddleRadius_sq K hd1 hq,
    sq_nonneg (dedekindSaddleRadius K d (dedekindSaddleAngle K d q))]

private theorem dedekindLocalWidth_nonneg {d : ℕ} {q : ℝ}
    (hα : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ dedekindLocalWidth K d q := by
  unfold dedekindLocalWidth dedekindLocalEpsilon
  exact mul_nonneg (by norm_num)
    (le_min hα.1 (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩))

private theorem dedekindLocalWidth_le_cos {d : ℕ} {q : ℝ}
    (hα : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2)) :
    dedekindLocalWidth K d q ≤ Real.cos (dedekindSaddleAngle K d q) := by
  have h0 := dedekindLocalWidth_nonneg K hα
  unfold dedekindLocalWidth dedekindLocalEpsilon at h0 ⊢
  nlinarith [min_le_right (dedekindSaddleAngle K d q) (Real.cos (dedekindSaddleAngle K d q))]

private theorem le_scaleT_of_le_mul {d : ℕ} (hd1 : 1 ≤ d) {c₀ q : ℝ}
    (hc₀ : c₀ ≤ Real.pi / 128) (hqc : q ≤ c₀ * dedekindScaleT K d) :
    q ≤ dedekindScaleT K d := by
  nlinarith [dedekindScaleT_pos K d hd1, Real.pi_lt_four]

private theorem four_le_pi_div_mul_div {d : ℕ} (hd1 : 1 ≤ d) {c₀ q : ℝ} (hq : 0 < q)
    (hc₀ : c₀ ≤ Real.pi / 128) (hqc : q ≤ c₀ * dedekindScaleT K d) :
    4 ≤ Real.pi / 32 * dedekindScaleT K d / q := by
  rw [le_div_iff₀ hq]
  nlinarith [dedekindScaleT_pos K d hd1]

/-- For all sufficiently large `d` and `dedekindEdgeQ K d < q ≤ dedekindScaleT K d`, the contour
`dedekindContourW K d q θ` has real part at least `(π / 32) * dedekindScaleT K d / q` for every `θ`
within `dedekindLocalWidth K d q` of `-2 * dedekindSaddleAngle K d q`. -/
theorem dedekind_contour_local_re :
    ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
      dedekindEdgeQ K d < q → q ≤ dedekindScaleT K d →
      ∀ θ ∈ Icc
          (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
          (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q),
        Real.pi / 32 * dedekindScaleT K d / q ≤
          (dedekindContourW K d q θ).re := by
  obtain ⟨D, hD1, hcos⟩ := eventually_dedekindSaddleCos_radius_comparison K
  filter_upwards [eventually_ge_atTop D] with d hd q hedge hqT θ hθ
  have hd1 : 1 ≤ d := hD1.trans hd
  have hqmem : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d) := ⟨hedge, hqT⟩
  have hα := dedekindSaddleAngle_mem_Icc K hd1 hqmem
  have hrpos := dedekindSaddleRadius_pos K d hd1 hα
  have hTpos := dedekindScaleT_pos K d hd1
  have hcoscomp := hcos d hd _ hα (by simpa [dedekindSaddle_inverse K d hd1 hqmem] using hqT)
  have hre := dedekindContourW_local_re_ge K d q (θ + 2 * dedekindSaddleAngle K d q)
    (mul_nonneg hTpos.le hrpos.le)
    ((abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩).trans (dedekindLocalWidth_le_cos K hα))
  rw [show -2 * dedekindSaddleAngle K d q + (θ + 2 * dedekindSaddleAngle K d q) = θ by ring]
    at hre
  have hdiv : 1 / q ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 := by
    rw [div_le_iff₀ (pos_of_mem_dedekindWindow K hd1 hqmem)]
    simpa [mul_comm] using one_le_mul_dedekindSaddleRadius_sq K hd1 hqmem
  refine le_trans ?_ hre
  calc
    Real.pi / 32 * dedekindScaleT K d / q =
        (Real.pi / 32 * dedekindScaleT K d) * (1 / q) := by ring
    _ ≤ (Real.pi / 32 * dedekindScaleT K d) *
        dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 := by gcongr
    _ = (dedekindScaleT K d *
        dedekindSaddleRadius K d (dedekindSaddleAngle K d q) / 2) *
        (Real.pi * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) / 16) := by ring
    _ ≤ (dedekindScaleT K d *
        dedekindSaddleRadius K d (dedekindSaddleAngle K d q) / 2) *
        Real.cos (dedekindSaddleAngle K d q) :=
      mul_le_mul_of_nonneg_left hcoscomp.1 (by positivity)
    _ = _ := by ring

/-- There is `c₁ > 0` (namely `π / 128`) such that for every `0 < c₀ ≤ c₁`, all sufficiently
large `d` and `dedekindEdgeQ K d < q ≤ c₀ * dedekindScaleT K d`, every point `w` of the local arc
satisfies `4 ≤ Re(1/2 + w)`. -/
theorem dedekind_contour_zeta_domain :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ∀ θ ∈ Icc
            (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
            (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q),
          4 ≤ (1 / 2 + dedekindContourW K d q θ).re := by
  refine ⟨Real.pi / 128, by positivity, fun c₀ _ hc₀ => ?_⟩
  filter_upwards [dedekind_contour_local_re K, eventually_ge_atTop 1]
    with d hd hd1 q hedge hqc θ hθ
  have hqT := le_scaleT_of_le_mul K hd1 hc₀ hqc
  rw [add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
  linarith [hd q hedge hqT θ hθ,
    four_le_pi_div_mul_div K hd1 (pos_of_mem_dedekindWindow K hd1 ⟨hedge, hqT⟩) hc₀ hqc]

/-- There is `c₁ > 0` such that for every `0 < c₀ ≤ c₁`, all sufficiently large `d` and
`dedekindEdgeQ K d < q ≤ c₀ * dedekindScaleT K d`, the amplitude
`dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q)` is nonzero. -/
theorem dedekind_saddle_amplitude_nonzero :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q) ≠ 0 := by
  refine ⟨Real.pi / 128, by positivity, fun c₀ _ hc₀ => ?_⟩
  filter_upwards [dedekind_contour_local_re K, eventually_ge_atTop 1]
    with d hlocal hd1 q hedge hqc
  have hqT := le_scaleT_of_le_mul K hd1 hc₀ hqc
  have hw := dedekindLocalWidth_nonneg K (dedekindSaddleAngle_mem_Icc K hd1 ⟨hedge, hqT⟩)
  have hre4 : 4 ≤ (dedekindContourW K d q (-2 * dedekindSaddleAngle K d q)).re :=
    (four_le_pi_div_mul_div K hd1 (pos_of_mem_dedekindWindow K hd1 ⟨hedge, hqT⟩) hc₀ hqc).trans
      (hlocal q hedge hqT _ ⟨by linarith, by linarith⟩)
  have hwnorm : 4 ≤ ‖dedekindContourW K d q (-2 * dedekindSaddleAngle K d q)‖ :=
    hre4.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hs : 1 < (1 / 2 + dedekindContourW K d q (-2 * dedekindSaddleAngle K d q)).re := by
    rw [add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    linarith
  exact dedekindAmplitude_ne_zero K (dedekindLeadingConstant_pos K).ne'
    (norm_ne_zero_iff.mp (by linarith))
    (fun h => Complex.exp_ne_zero _ ((dedekindEulerLog_exp K hs).trans h))
    (dedekindGammaRemainder_ne_zero_of_re_nonneg K (by linarith) hwnorm)

/-- There is `c₁ > 0` such that for every `0 < c₀ ≤ c₁`, all sufficiently large `d` and
`dedekindEdgeQ K d < q ≤ c₀ * dedekindScaleT K d`, the normalized local amplitude
`normalizedDedekindLocalAmplitude K d q 0` equals `1`. -/
theorem eventually_normalizedDedekindLocalAmplitude_zero :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        normalizedDedekindLocalAmplitude K d q 0 = 1 := by
  obtain ⟨c₁, hc₁, hamp⟩ := dedekind_saddle_amplitude_nonzero K
  refine ⟨c₁, hc₁, fun c₀ hc₀ hc₀c₁ => ?_⟩
  filter_upwards [hamp c₀ hc₀ hc₀c₁] with d hd q hedge hqc
  exact normalizedDedekindLocalAmplitude_zero K (hd q hedge hqc)

end

end RiemannJensen
