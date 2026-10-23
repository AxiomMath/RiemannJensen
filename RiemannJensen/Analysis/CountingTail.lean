module

public import RiemannJensen.Analysis.RemotePhaseGap

/-!
# The complementary-arc tail on the counting window

A pointwise lower bound `G` for the remote phase gap, combined with the global
amplitude ratio `‖a(θ)‖ ≤ C √T ‖a(θ_q)‖`, gives the tail hypothesis of the
lower-contour estimate with `B = C √T` and `g = d G`.  Feeding in the remote
phase gaps of `RemotePhaseGap` and the packaging `tail_term_le_on_scale_window`
gives the lower-contour estimate and the oscillatory formula with the tail
error `π C √(8π) d e^{-d G}`.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- `T ≤ d` once `Λ ≥ 4π`. -/
theorem scaleT_le_nat_of_scaleLambda {d : ℕ} (hd : 1 ≤ d)
    (hΛ : 4 * Real.pi ≤ scaleLambda d) : scaleT d ≤ d := by
  have hprod := scaleT_mul_scaleLambda d hd
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd)
  have hpi := Real.pi_pos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hΛ hT.le]

/-- **Tail bound from a phase gap and an amplitude ratio.**  If
`‖a(θ)‖ ≤ B ‖a(θ_q)‖` on `[-π, 0]` and `G ≤ Re h(u_q) - Re h(r² e^{iθ})`
off the local window, then `‖a(θ) e^{d h}‖ ≤ B ‖a(θ_q)‖ e^{d Re h(u_q)} e^{-d G}`
off the local window. -/
theorem tail_bound_of_gap {d : ℕ} {q ε B G : ℝ}
    (hamp : ∀ θ ∈ Icc (-Real.pi) 0,
      ‖amplitude d q θ‖ ≤ B * ‖amplitude d q (-2 * saddleAngle d q)‖)
    (hgap : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      G ≤ (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re) :
    ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-(d * G)) := by
  intro θ hθ hθout
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hre : ((d : ℂ) * phase d q (lowerContourPoint d q θ)).re =
      d * (phase d q (lowerContourPoint d q θ)).re := by
    simp
  rw [norm_mul, Complex.norm_exp, hre]
  have hexp : Real.exp (d * (phase d q (lowerContourPoint d q θ)).re) ≤
      Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-(d * G)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left (hgap θ hθ hθout) hd0
    nlinarith
  calc ‖amplitude d q θ‖ * Real.exp (d * (phase d q (lowerContourPoint d q θ)).re)
      ≤ (B * ‖amplitude d q (-2 * saddleAngle d q)‖) *
          (Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-(d * G))) :=
        mul_le_mul (hamp θ hθ) hexp (Real.exp_pos _).le
          ((norm_nonneg _).trans (hamp θ hθ))
    _ = _ := by ring

/-- **Tail bound on the counting window from a phase gap.** There is an absolute `C > 0` such
that on the counting window any pointwise lower bound `G` for the remote phase gap gives the
tail hypothesis of `countingWindow_lowerContribution_estimate` with `B = C √T` and `g = d G`. -/
theorem exists_countingWindow_tail_of_gap :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      ∀ {M c₀ q ε G : ℝ}, 0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
        40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
        (∀ θ ∈ Icc (-Real.pi) 0,
          θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
            (-2 * saddleAngle d q + localWidth ε d q) →
          G ≤ (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re) →
        ∀ θ ∈ Icc (-Real.pi) 0,
          θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
            (-2 * saddleAngle d q + localWidth ε d q) →
          ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
            C * Real.sqrt (scaleT d) * ‖amplitude d q (-2 * saddleAngle d q)‖ *
              Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-(d * G)) := by
  obtain ⟨C, hC, hratio⟩ := exists_countingWindow_global_amplitude_ratio
  refine ⟨C, hC, ?_⟩
  intro d hd hΛ M c₀ q ε G hM hc₀ hcsmall hscale hq hgap
  have hlarge := four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ
  have hne := countingWindow_saddle_amplitude_ne_zero d hd hlarge hM hc₀ hcsmall
    hscale hq
  have hpos : 0 < ‖amplitude d q (saddleTheta d q)‖ := norm_pos_iff.2 hne
  apply tail_bound_of_gap _ hgap
  intro θ hθ
  have h := hratio d hd hlarge hM hc₀ hcsmall hscale hq θ hθ.1
    (hθ.2.trans Real.pi_pos.le)
  rw [div_le_iff₀ hpos] at h
  exact h

/-- **Lower-contour estimate on the counting window from a phase gap.**  With
the tail discharged by a pointwise remote-gap bound `G`, the complementary-arc
error is `π C √(8π) d e^{-d G}` for an absolute `C > 0`. -/
theorem exists_countingWindow_lowerContribution_estimate_of_gap :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q ε c Cp G : ℝ} {p' p'' p''' : ℝ → ℂ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      0 < ε → ε ≤ 1 → 1 ≤ effectiveN ε d q → 0 < c → 0 ≤ Cp →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y) →
      p' 0 = 0 →
      p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) →
      (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0) →
      (∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp) →
      (∀ θ ∈ Icc (-Real.pi) 0,
        θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
          (-2 * saddleAngle d q + localWidth ε d q) →
        G ≤ (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re) →
      ‖lowerContribution d q - leadingSaddle d q‖ ≤
        ‖leadingSaddle d q‖ *
          (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
              effectiveN ε d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d * Real.exp (-(d * G))) := by
  obtain ⟨C, hC, htail⟩ := exists_countingWindow_tail_of_gap
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q ε c Cp G p' p'' p''' hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc
    hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd hgap
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  have hest := countingWindow_lowerContribution_estimate hd hΛ hM hc₀ hcsmall hscale
    hq hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd
    (htail d hd hΛ hM hc₀ hcsmall hscale hq hgap)
  have hterm := tail_term_le_on_scale_window (B := C * Real.sqrt (scaleT d))
    (K₁ := C) (g := d * G) hd1 hΛ hsc hC.le le_rfl
    (scaleT_le_nat_of_scaleLambda hd1 (by linarith [Real.pi_pos]))
  refine hest.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  linarith

/-- **Oscillatory approximation on the counting window from a phase gap**:
`(rescaledJensen d).eval (-q)` differs from `2 Re (leadingSaddle d q)` by at most
`2 ‖leadingSaddle d q‖` times the window error plus the tail error `π C √(8π) d e^{-d G}`. -/
theorem exists_countingWindow_rescaledJensen_eval_of_gap :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q ε c Cp G : ℝ} {p' p'' p''' : ℝ → ℂ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      0 < ε → ε ≤ 1 → 1 ≤ effectiveN ε d q → 0 < c → 0 ≤ Cp →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y) →
      p' 0 = 0 →
      p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) →
      (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0) →
      (∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp) →
      (∀ θ ∈ Icc (-Real.pi) 0,
        θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
          (-2 * saddleAngle d q + localWidth ε d q) →
        G ≤ (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re) →
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
        2 * ‖leadingSaddle d q‖ *
          (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
              effectiveN ε d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d * Real.exp (-(d * G))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_lowerContribution_estimate_of_gap
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q ε c Cp G p' p'' p''' hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc
    hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd hgap
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨-, hr, hRT, -⟩ :=
    countingWindow_large_radius d hd hM hc₀ hcsmall hscale hq
  have h := abs_sub_two_re_le_of_eq_add_star
    (rescaledJensen_eval_eq_lowerContribution_add_star d hd1 q (gammaCoeff_pos d).ne' hr hRT)
    (hest hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0
      hre hlower hp''_bd hp'''_bd hgap)
  simpa [mul_assoc] using h

/-- **Large-angle lower-contour estimate on the counting window**
(unconditional tail): for `1/2 ≤ α_q`, the tail error is
`π C √(8π) d exp(-d · 3 ε² / (2048 π² q))`. -/
theorem exists_countingWindow_lowerContribution_estimate_large_angle :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q ε c Cp : ℝ} {p' p'' p''' : ℝ → ℂ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      0 < ε → ε ≤ 1 → 1 / 2 ≤ saddleAngle d q →
      1 ≤ effectiveN ε d q → 0 < c → 0 ≤ Cp →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y) →
      p' 0 = 0 →
      p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) →
      (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0) →
      (∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp) →
      ‖lowerContribution d q - leadingSaddle d q‖ ≤
        ‖leadingSaddle d q‖ *
          (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
              effectiveN ε d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * (3 * ε ^ 2 / (2048 * Real.pi ^ 2 * q))))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_lowerContribution_estimate_of_gap
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q ε c Cp p' p'' p''' hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hα hn hc
    hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  exact hest hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0
    hre hlower hp''_bd hp'''_bd
    (fun θ hθ hθout => remote_phase_gap_large_angle d hd1 hΛ hsc hε0 hε1 hα hθ hθout)

/-- **Large-angle oscillatory approximation on the counting window**: for `1/2 ≤ α_q`, the
tail error is `π C √(8π) d exp(-d · 3 ε² / (2048 π² q))`. -/
theorem exists_countingWindow_rescaledJensen_eval_large_angle :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q ε c Cp : ℝ} {p' p'' p''' : ℝ → ℂ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      0 < ε → ε ≤ 1 → 1 / 2 ≤ saddleAngle d q →
      1 ≤ effectiveN ε d q → 0 < c → 0 ≤ Cp →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y) →
      p' 0 = 0 →
      p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) →
      (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0) →
      (∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp) →
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
        2 * ‖leadingSaddle d q‖ *
          (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
              effectiveN ε d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * (3 * ε ^ 2 / (2048 * Real.pi ^ 2 * q))))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_rescaledJensen_eval_of_gap
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q ε c Cp p' p'' p''' hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hα hn hc
    hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  exact hest hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0
    hre hlower hp''_bd hp'''_bd
    (fun θ hθ hθout => remote_phase_gap_large_angle d hd1 hΛ hsc hε0 hε1 hα hθ hθout)

/-- **Lower-contour estimate on the counting window, conditional on the edge
comparison**: if `α_q < 1/2` implies `q - q_edge ≤ K α_q²` (`K > 0`), the tail
error is `π C √(8π) d exp(-d ε² c_K min((q - q_edge)², q⁻¹))`. -/
theorem exists_countingWindow_lowerContribution_estimate_of_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q ε c Cp K : ℝ} {p' p'' p''' : ℝ → ℂ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      0 < ε → ε ≤ 1 → 0 < K →
      (saddleAngle d q < 1 / 2 → q - edgeQ d ≤ K * saddleAngle d q ^ 2) →
      1 ≤ effectiveN ε d q → 0 < c → 0 ≤ Cp →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y) →
      p' 0 = 0 →
      p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) →
      (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0) →
      (∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp) →
      ‖lowerContribution d q - leadingSaddle d q‖ ≤
        ‖leadingSaddle d q‖ *
          (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
              effectiveN ε d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * (ε ^ 2 * remoteGapConst K *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_lowerContribution_estimate_of_gap
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q ε c Cp K p' p'' p''' hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hK hedge
    hn hc hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  exact hest hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0
    hre hlower hp''_bd hp'''_bd
    (fun θ hθ hθout => remote_phase_gap_of_edge d hd1 hΛ hsc hε0 hε1 hK hedge hθ hθout)

/-- **Oscillatory approximation on the counting window, conditional on the edge
comparison**: the tail error is `π C √(8π) d exp(-d ε² c_K min((q - q_edge)², q⁻¹))`. -/
theorem exists_countingWindow_rescaledJensen_eval_of_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {M c₀ q ε c Cp K : ℝ} {p' p'' p''' : ℝ → ℂ},
      2 ≤ d → 24 * Real.pi ≤ scaleLambda d →
      0 < M → 0 < c₀ → c₀ ≤ Real.pi / 112 →
      40000 * c₀ ≤ scaleT d → q ∈ countingWindow M c₀ d →
      0 < ε → ε ≤ 1 → 0 < K →
      (saddleAngle d q < 1 / 2 → q - edgeQ d ≤ K * saddleAngle d q ^ 2) →
      1 ≤ effectiveN ε d q → 0 < c → 0 ≤ Cp →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y) →
      (∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y) →
      p' 0 = 0 →
      p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)) →
      (∀ y ∈ Icc (-1:ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0) →
      (∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ Cp) →
      (∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ Cp) →
      |(rescaledJensen d).eval (-q) - 2 * (leadingSaddle d q).re| ≤
        2 * ‖leadingSaddle d q‖ *
          (windowRelConst c (max (4 + 8 * 2 * zetaLogDerivMajorant) Cp) *
              effectiveN ε d q ^ (-(1:ℝ)/10) +
            Real.pi * C * Real.sqrt (2 * Real.pi * 4) * d *
              Real.exp (-(d * (ε ^ 2 * remoteGapConst K *
                min ((q - edgeQ d) ^ 2) q⁻¹)))) := by
  obtain ⟨C, hC, hest⟩ := exists_countingWindow_rescaledJensen_eval_of_gap
  refine ⟨C, hC, ?_⟩
  intro d M c₀ q ε c Cp K p' p'' p''' hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hK hedge
    hn hc hCp hp hp' hp'' hp'0 hp''0 hre hlower hp''_bd hp'''_bd
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  obtain ⟨hsc, -⟩ := countingWindow_subset_scale_window d hd hM hcsmall hq
  exact hest hd hΛ hM hc₀ hcsmall hscale hq hε0 hε1 hn hc hCp hp hp' hp'' hp'0 hp''0
    hre hlower hp''_bd hp'''_bd
    (fun θ hθ hθout => remote_phase_gap_of_edge d hd1 hΛ hsc hε0 hε1 hK hedge hθ hθout)

end RiemannJensen
