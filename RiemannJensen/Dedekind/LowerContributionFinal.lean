module

public import RiemannJensen.Dedekind.NormalizedLowerBridge
public import RiemannJensen.Dedekind.LowerIntegrabilityBridge
public import RiemannJensen.Dedekind.EffectiveLog

/-!
# The unconditional Dedekind lower-contour asymptotic

For a number field `K`, the contribution of the lower semicircle to the contour integral is
asymptotic to its leading saddle term, uniformly on a field-dependent counting window.

## Main results

* `exists_eventually_dedekind_lower_contribution`: on the window
  `dedekindCountingWindow K M c₀ d`, for all large `d`, the lower contribution differs from
  `dedekindLeadingSaddle K d q` by a relative error of order
  `dedekindEffectiveN K d q ^ (-1 / 10)` plus an exponentially small remote-contour term.
-/

@[expose] public section

namespace RiemannJensen

open Set Filter MeasureTheory intervalIntegral

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- If `q ≤ c T`, `1 ≤ q r ^ 2`, `c ≤ 1 / 4` and `0 ≤ r ≤ 2`, then `1 < T r`. -/
theorem one_lt_mul_of_le_mul_of_one_le_mul_sq {T r c q : ℝ} (hT : 0 ≤ T) (hr0 : 0 ≤ r)
    (hr2 : r ≤ 2) (hc : c ≤ 1 / 4) (hqc : q ≤ c * T) (hqr : 1 ≤ q * r ^ 2) : 1 < T * r := by
  have hcr : c * r ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_right hc hr0]
  nlinarith [mul_le_mul_of_nonneg_right hqc (sq_nonneg r),
    mul_le_mul_of_nonneg_left hcr (mul_nonneg hT hr0)]

/-- Points of the counting window lie strictly to the right of the edge point. -/
theorem dedekindEdgeQ_lt_of_mem_countingWindow {M c₀ : ℝ} (hM : 0 < M) {d : ℕ} (hd : 2 ≤ d)
    {q : ℝ} (hq : q ∈ dedekindCountingWindow K M c₀ d) : dedekindEdgeQ K d < q := by
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hs : 0 < Real.sqrt (Real.log (d : ℝ) / d) :=
    Real.sqrt_pos.2 (div_pos hlog (by positivity))
  have hq₁ : dedekindEdgeQ K d + M * Real.sqrt (Real.log (d : ℝ) / d) ≤ q := hq.1
  nlinarith [mul_pos hM hs]

/-- On the counting window, `q` lies in the saddle range and the saddle radius `r`
satisfies `0 < r` and `1 < T r`. -/
theorem dedekind_countingWindow_saddle_bounds {M c₀ : ℝ} (hM : 0 < M) {d : ℕ} (hd : 2 ≤ d)
    (hc₀ : c₀ ≤ 1 / 4) {q : ℝ} (hq : q ∈ dedekindCountingWindow K M c₀ d) :
    dedekindEdgeQ K d < q ∧ q ≤ c₀ * dedekindScaleT K d ∧ q ≤ dedekindScaleT K d ∧
      dedekindSaddleAngle K d q ∈ Ioo 0 (Real.pi / 2) ∧
      0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ∧
      1 < dedekindScaleT K d * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) := by
  have hd₁ : 1 ≤ d := by omega
  have hedge := dedekindEdgeQ_lt_of_mem_countingWindow K hM hd hq
  have hqc : q ≤ c₀ * dedekindScaleT K d := by
    simpa [dedekindCountingWindow, dedekindUpperEndpoint] using hq.2
  have hT := dedekindScaleT_pos K d hd₁
  have hqT : q ≤ dedekindScaleT K d :=
    hqc.trans (mul_le_of_le_one_left hT.le (hc₀.trans (by norm_num)))
  have hα := dedekindSaddle_inverse_range K d hd₁ ⟨hedge, hqT⟩
  have hαmem : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  have hr := dedekindSaddleRadius_pos K d hd₁ hαmem
  have hqr : 1 ≤ q * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ^ 2 := by
    have hx := one_le_dedekindSaddleQ_mul_radius_sq K d hd₁ hαmem
    rwa [dedekindSaddle_inverse K d hd₁ ⟨hedge, hqT⟩] at hx
  exact ⟨hedge, hqc, hqT, hα, hr, one_lt_mul_of_le_mul_of_one_le_mul_sq hT.le hr.le
    (dedekindSaddleRadius_le_two K d hd₁ hαmem) hc₀ hqc hqr⟩

/-- On the saddle range, the Hessian has positive real part and norm at most `4`. -/
theorem dedekindSaddleHessian_re_pos_and_norm_le_four (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {q : ℝ}
    (hq : q ∈ Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    0 < (dedekindSaddleHessian K d q).re ∧ ‖dedekindSaddleHessian K d q‖ ≤ 4 := by
  have hα := dedekindSaddle_inverse_range K d hd hq
  have hre := (dedekindSaddleHessian_re_bounds K d hd (by linarith [Real.pi_pos]) hα).1
  have hnorm := (dedekindSaddleHessian_norm_bounds K d hd hΛ hα).2
  rw [dedekindSaddle_inverse K d hd hq] at hre hnorm
  have hsin : 0 < Real.sin (dedekindSaddleAngle K d q) :=
    Real.sin_pos_of_pos_of_lt_pi hα.1 (hα.2.trans (by linarith [Real.pi_pos]))
  exact ⟨(sq_pos_of_pos hsin).trans_le hre,
    hnorm.trans (by linarith [Real.sin_le_one (dedekindSaddleAngle K d q)])⟩

/-- The local width is positive and the local window around `-2α` lies in `[-π, 0]`. -/
theorem dedekindLocalWidth_bounds {d : ℕ} {q : ℝ}
    (hα : dedekindSaddleAngle K d q ∈ Ioo 0 (Real.pi / 2)) :
    0 < dedekindLocalWidth K d q ∧
      -Real.pi ≤ -2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q ∧
      -2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q ≤ 0 := by
  have hcos : 0 < Real.cos (dedekindSaddleAngle K d q) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hα.1], hα.2⟩
  have hcosle : Real.cos (dedekindSaddleAngle K d q) ≤
      Real.pi / 2 - dedekindSaddleAngle K d q := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le (by linarith [hα.2.le])
  have h₁ := min_le_left (dedekindSaddleAngle K d q) (Real.cos (dedekindSaddleAngle K d q))
  have h₂ := min_le_right (dedekindSaddleAngle K d q) (Real.cos (dedekindSaddleAngle K d q))
  unfold dedekindLocalWidth dedekindLocalEpsilon
  refine ⟨mul_pos (by norm_num) (lt_min hα.1 hcos), ?_, ?_⟩ <;> linarith [hα.1]

/-- The saddle scale satisfies `T ^ N ≤ max 1 ((4π / N) ^ N) * d ^ N`, `N` the degree of `K`. -/
theorem dedekindScaleT_pow_le (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) :
    dedekindScaleT K d ^ dedekindDegree K ≤
      max 1 ((4 * Real.pi / dedekindDegree K) ^ dedekindDegree K) *
        (d : ℝ) ^ dedekindDegree K := by
  have hT := dedekindScaleT_pos K d hd
  have hN : (0 : ℝ) < dedekindDegree K := by exact_mod_cast dedekindDegree_pos K
  have hTd : dedekindScaleT K d ≤ 4 * Real.pi / dedekindDegree K * d :=
    calc
      dedekindScaleT K d ≤ dedekindScaleT K d * dedekindScaleLambda K d :=
        le_mul_of_one_le_right hT.le (by linarith [Real.pi_gt_three])
      _ = 4 * Real.pi / dedekindDegree K * d := by
        rw [div_mul_eq_mul_div, eq_div_iff hN.ne', ← dedekindScale_product K d hd]
        ring
  have hp := pow_le_pow_left₀ hT.le hTd (dedekindDegree K)
  rw [mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_right 1 _) (by positivity))

/-- The prefactor of the remote-contour error is `O(d ^ (N + 1))`, `N` the degree of `K`. -/
theorem pi_mul_scaleT_pow_mul_sqrt_le (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {B : ℝ} (hB : 0 ≤ B) {D : ℂ}
    (hD : ‖D‖ ≤ 4) :
    Real.pi * (B * dedekindScaleT K d ^ dedekindDegree K) *
        Real.sqrt (2 * Real.pi * d * ‖D‖) ≤
      Real.pi * B * Real.sqrt (8 * Real.pi) *
        max 1 ((4 * Real.pi / dedekindDegree K) ^ dedekindDegree K) *
          (d : ℝ) ^ (dedekindDegree K + 1) := by
  have hTpow := dedekindScaleT_pow_le K d hd hΛ
  have hsqrt : Real.sqrt (2 * Real.pi * d * ‖D‖) ≤ Real.sqrt (8 * Real.pi) * d := by
    refine (Real.sqrt_le_sqrt (?_ : _ ≤ 8 * Real.pi * (d : ℝ) ^ 2)).trans_eq ?_
    · calc
        2 * Real.pi * d * ‖D‖ ≤ 2 * Real.pi * d * 4 := by gcongr
        _ = 8 * Real.pi * d := by ring
        _ ≤ 8 * Real.pi * (d : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ (by exact_mod_cast hd) two_ne_zero)
            (by positivity)
    · rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc
    _ ≤ Real.pi * (B *
        (max 1 ((4 * Real.pi / dedekindDegree K) ^ dedekindDegree K) *
          (d : ℝ) ^ dedekindDegree K)) * (Real.sqrt (8 * Real.pi) * d) := by gcongr
    _ = _ := by ring

/-- There are constants `M, c₀, C > 0` such that, for all sufficiently large `d` and every
`q ∈ dedekindCountingWindow K M c₀ d`, the lower contribution `dedekindLowerContribution K d q`
differs from `dedekindLeadingSaddle K d q` by at most `‖dedekindLeadingSaddle K d q‖` times
`C * dedekindEffectiveN K d q ^ (-1 / 10)` plus the remote-contour error
`C * d ^ (dedekindDegree K + 1) * exp (-(d * dedekindRemoteGapConst * min ((q - q₀) ^ 2) q⁻¹))`,
where `q₀ = dedekindEdgeQ K d`. -/
theorem exists_eventually_dedekind_lower_contribution :
    ∃ M c₀ C : ℝ, 0 < M ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ dedekindCountingWindow K M c₀ d,
        ‖dedekindLowerContribution K d q - dedekindLeadingSaddle K d q‖ ≤
          ‖dedekindLeadingSaddle K d q‖ *
            (C * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10) +
              C * (d : ℝ) ^ (dedekindDegree K + 1) *
                Real.exp (-(d * (dedekindRemoteGapConst *
                  min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹)))) := by
  obtain ⟨cG, CG, hcG, hCG, hgauss⟩ := dedekind_local_gaussian_adapter K
  obtain ⟨cB, B, hcB, hB, hratio⟩ := dedekind_global_amplitude_ratio K
  obtain ⟨cA, hcA, hnonzero⟩ := dedekind_saddle_amplitude_nonzero K
  let c₀ := min (dedekindOscillationC0 K) (min cG (min cB (min cA (1 / 4))))
  let C : ℝ := max CG (Real.pi * B * Real.sqrt (8 * Real.pi) *
    max 1 ((4 * Real.pi / dedekindDegree K) ^ dedekindDegree K))
  have hM := dedekindOscillationM_pos K
  have hc₀ : 0 < c₀ := lt_min (dedekindOscillationC0_pos K)
    (lt_min hcG (lt_min hcB (lt_min hcA (by norm_num))))
  have hcG' : c₀ ≤ cG := by simp [c₀]
  have hcB' : c₀ ≤ cB := by simp [c₀]
  have hcA' : c₀ ≤ cA := by simp [c₀]
  have hcquarter : c₀ ≤ 1 / 4 := by simp [c₀]
  refine ⟨dedekindOscillationM K, c₀, C, hM, hc₀, hCG.trans_le (le_max_left _ _), ?_⟩
  obtain ⟨DΛ, hDΛ⟩ := eventually_twentyfour_pi_le_dedekindScaleLambda K
  filter_upwards [hgauss (dedekindOscillationM K) c₀ hM hc₀ hcG', hratio c₀ hc₀ hcB',
    hnonzero c₀ hc₀ hcA', eventually_dedekindRemotePhase_gap K,
    eventually_ge_atTop (max DΛ 2)] with d hgd hrd hnd hgap hd q hq
  have hd₂ : 2 ≤ d := (le_max_right _ _).trans hd
  have hd₁ : 1 ≤ d := by omega
  have hΛ := hDΛ d ((le_max_left _ _).trans hd)
  obtain ⟨hedge, hqc, hqT, hα, hr, hR⟩ :=
    dedekind_countingWindow_saddle_bounds K hM hd₂ hcquarter hq
  obtain ⟨hDre, hD4⟩ :=
    dedekindSaddleHessian_re_pos_and_norm_le_four K d hd₁ hΛ ⟨hedge, hqT⟩
  obtain ⟨hℓ, hleft, hright⟩ := dedekindLocalWidth_bounds K hα
  have hmain := dedekind_lower_contribution_of_normalized K (by omega : 0 < d)
    (q := q) (E := CG * dedekindEffectiveN K d q ^ (-(1 : ℝ) / 10))
    (B := B * dedekindScaleT K d ^ dedekindDegree K)
    (g := d * (dedekindRemoteGapConst * min ((q - dedekindEdgeQ K d) ^ 2) q⁻¹))
    hℓ hDre (hnd q hedge hqc)
    (by simpa [normalizedDedekindLocalAmplitude_zero K (hnd q hedge hqc), mul_assoc] using
      hgd q hq)
    hleft hright (intervalIntegrable_dedekind_lower_integrand_canonical K hd₁ q hr hR)
    fun θ hθ hout => by
      simpa only [neg_mul] using
        dedekind_tail_pointwise_of_ratio_gap K (by omega) (hnd q hedge hqc)
          (hrd q hedge hqc θ hθ.1 hθ.2) (hgap q hedge hqT θ hθ hout)
  have htail : Real.pi * (B * dedekindScaleT K d ^ dedekindDegree K) *
      Real.sqrt (2 * Real.pi * d * ‖dedekindSaddleHessian K d q‖) ≤
        C * (d : ℝ) ^ (dedekindDegree K + 1) :=
    (pi_mul_scaleT_pow_mul_sqrt_le K d hd₁ hΛ hB.le hD4).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  refine hmain.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    (mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le)) (norm_nonneg _))
  exact Real.rpow_nonneg (by unfold dedekindEffectiveN; positivity) _

end

end RiemannJensen
