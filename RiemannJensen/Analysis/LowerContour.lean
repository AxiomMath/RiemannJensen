module

public import RiemannJensen.Analysis.LowerContourLocal
public import RiemannJensen.Analysis.AmplitudeDefinitions
public import RiemannJensen.Analysis.AmplitudeLocal

/-!
# The lower-contour contribution

The contribution of the lower semicircle `u = r² e^{iθ}`, `-π ≤ θ ≤ 0`, to the
Cauchy integral is
`L_d(q) = d! / (2π d^d) ∫_{-π}^{0} a_q(θ) e^{d h_q(r² e^{iθ})} dθ`.
Under the saddle-geometry and amplitude hypotheses (stated explicitly), it
satisfies `L_d(q) = Z_d(q) (1 + O(n_q^{-1/10}) + O(√(2π d |D_q|) e^{-g}))`,
with `Z_d(q) = leadingSaddle d q`, `n_q = effectiveN ε d q`, and the local
window centred at `θ_q = -2 α` of half-width `ℓ_q = localWidth ε d q`.
-/

@[expose] public section

namespace RiemannJensen

open Set MeasureTheory

/-- The point `r² e^{iθ}` of the saddle circle. -/
noncomputable def lowerContourPoint (d : ℕ) (q θ : ℝ) : ℂ :=
  (((saddleRadius d (saddleAngle d q)) ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))

/-- The phase along the saddle circle, `θ ↦ h_q(r² e^{iθ})`. -/
noncomputable def lowerPhaseAngle (d : ℕ) (q : ℝ) (θ : ℝ) : ℂ :=
  phase d q (lowerContourPoint d q θ)

/-- The contribution `L_d(q)` of the lower semicircle. -/
noncomputable def lowerContribution (d : ℕ) (q : ℝ) : ℂ :=
  ((d.factorial : ℂ) / (d : ℂ) ^ d) *
    ((1 / (2 * (Real.pi : ℂ))) *
      ∫ θ in (-Real.pi)..0, amplitude d q θ *
        Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ)))

/-- The normalized local phase
`p_q(y) = d (h_q(r² e^{i(θ_q + ℓ_q y)}) - h_q(u_q)) / n_q`. -/
noncomputable def lowerNormalizedPhase (ε : ℝ) (d : ℕ) (q : ℝ) : ℝ → ℂ :=
  windowPhase (lowerPhaseAngle d q) (-2 * saddleAngle d q) (localWidth ε d q) d
    (effectiveN ε d q)

/-- The saddle is the point of the saddle circle at angle `θ_q = -2 α`. -/
theorem saddle_eq_lowerContourPoint (d : ℕ) (q : ℝ) :
    saddle d q = lowerContourPoint d q (-2 * saddleAngle d q) := by
  unfold saddle lowerContourPoint
  congr 2
  push_cast
  ring

/-- At the saddle angle `θ_q = -2 α`, the phase along the saddle circle is `h_q(u_q)`. -/
theorem lowerPhaseAngle_center (d : ℕ) (q : ℝ) :
    lowerPhaseAngle d q (-2 * saddleAngle d q) = phase d q (saddle d q) := by
  rw [lowerPhaseAngle, saddle_eq_lowerContourPoint]

/-- The normalized local phase vanishes at the centre: `p_q(0) = 0`. -/
@[simp]
theorem lowerNormalizedPhase_zero (ε : ℝ) (d : ℕ) (q : ℝ) :
    lowerNormalizedPhase ε d q 0 = 0 :=
  windowPhase_zero _ _ _ _ _

/-- **Lower-contour estimate.** With the saddle geometry and amplitude bounds as explicit
hypotheses, `L_d(q) = Z_d(q) {1 + O(n_q^{-1/10}) + O(√(2π d |D_q|) e^{-g})}`
with the explicit constants `windowRelConst c C` and `π B`. -/
theorem lowerContribution_estimate {d : ℕ} {q ε c C B g : ℝ} {f' p' p'' p''' : ℝ → ℂ}
    (hd : 0 < d) (hℓ : 0 < localWidth ε d q) (hD : 0 < (saddleHessian d q).re)
    (ha : amplitude d q (-2 * saddleAngle d q) ≠ 0)
    (hn : 1 ≤ effectiveN ε d q) (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (localAmplitude ε d q) (f' y) y)
    (hf'_cont : ContinuousOn f' (Icc (-1 : ℝ) 1))
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hf_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖localAmplitude ε d q y‖ ≤ C)
    (hf'_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖f' y‖ ≤ C)
    (hp''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p'' y‖ ≤ C)
    (hp'''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p''' y‖ ≤ C)
    (h1 : -Real.pi ≤ -2 * saddleAngle d q - localWidth ε d q)
    (h2 : -2 * saddleAngle d q + localWidth ε d q ≤ 0)
    (hint : IntervalIntegrable
      (fun θ => amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ)))
      volume (-Real.pi) 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-g)) :
    ‖lowerContribution d q - leadingSaddle d q‖ ≤
      ‖leadingSaddle d q‖ *
        (windowRelConst c C * effectiveN ε d q ^ (-(1 : ℝ) / 10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) * Real.exp (-g)) := by
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd
  have hcast : (((d : ℝ)) : ℂ) = (d : ℂ) := Complex.ofReal_natCast d
  have key := lower_semicircle_estimate (a := amplitude d q) (H := lowerPhaseAngle d q)
    (θ₀ := -2 * saddleAngle d q) (dd := (d : ℝ)) (B := B) (g := g) hℓ hdd hD ha hn hc hC hf
    hf'_cont hp hp' hp'' hp'0 hp''0 hre hlower hf_bd hf'_bd hp''_bd hp'''_bd h1 h2
    (by simpa only [lowerPhaseAngle, hcast] using hint)
    (by
      intro θ hθ hθ'
      rw [lowerPhaseAngle_center, hcast]
      exact htail θ hθ hθ')
  rw [lowerPhaseAngle_center, hcast] at key
  simp only [lowerPhaseAngle] at key
  have hL : leadingSaddle d q = ((d.factorial : ℂ) / (d : ℂ) ^ d) *
      (amplitude d q (-2 * saddleAngle d q) *
        Complex.exp ((d : ℂ) * phase d q (saddle d q)) /
          Complex.sqrt (2 * Real.pi * d * saddleHessian d q)) := by
    rw [leadingSaddle, mul_div_assoc]
  rw [lowerContribution, hL, ← mul_sub, norm_mul, norm_mul _ (_ / _)]
  calc _ ≤ _ := mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = _ := by rw [effectiveN]; ring

/-- **Lower-contour estimate, amplitude side discharged.** As
`lowerContribution_estimate`, but with the `C¹` hypotheses on the normalized
amplitude replaced by the geometric hypotheses of `localAmplitude_C1_bounds`
(saddle radius `R = T r ≥ 200`, `ℓ ≤ 1`, `Re(1/2 + w) ≥ 4` and `ℓ R ≤ K Re w` on
the window); the phase is controlled by its own constant `Cp`. The error constant
is `windowRelConst c (max (4 + 8 K M) Cp)` with `M = zetaLogDerivMajorant`. -/
theorem lowerContribution_estimate_of_geometry {d : ℕ} {q ε c Cp K B g : ℝ} {p' p'' p''' : ℝ → ℂ}
    (hd : 0 < d) (hℓ : 0 < localWidth ε d q) (hℓ1 : localWidth ε d q ≤ 1)
    (hD : 0 < (saddleHessian d q).re)
    (hn : 1 ≤ effectiveN ε d q) (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hreW : ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hK : ∀ y ∈ Icc (-1 : ℝ) 1,
      localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
        K * (contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt (lowerNormalizedPhase ε d q) (p' y) y)
    (hp' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp'0 : p' 0 = 0)
    (hp''0 : p'' 0 = -(saddleHessian d q / (‖saddleHessian d q‖ : ℂ)))
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1, (lowerNormalizedPhase ε d q y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1 : ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hp''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p'' y‖ ≤ Cp)
    (hp'''_bd : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p''' y‖ ≤ Cp)
    (h1 : -Real.pi ≤ -2 * saddleAngle d q - localWidth ε d q)
    (h2 : -2 * saddleAngle d q + localWidth ε d q ≤ 0)
    (hint : IntervalIntegrable
      (fun θ => amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ)))
      volume (-Real.pi) 0)
    (htail : ∀ θ ∈ Icc (-Real.pi) 0,
      θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
        (-2 * saddleAngle d q + localWidth ε d q) →
      ‖amplitude d q θ * Complex.exp ((d : ℂ) * phase d q (lowerContourPoint d q θ))‖ ≤
        B * ‖amplitude d q (-2 * saddleAngle d q)‖ *
          Real.exp (d * (phase d q (saddle d q)).re) * Real.exp (-g)) :
    ‖lowerContribution d q - leadingSaddle d q‖ ≤
      ‖leadingSaddle d q‖ *
        (windowRelConst c (max (4 + 8 * K * zetaLogDerivMajorant) Cp) *
            effectiveN ε d q ^ (-(1 : ℝ) / 10) +
          Real.pi * B * Real.sqrt (2 * Real.pi * d * ‖saddleHessian d q‖) * Real.exp (-g)) := by
  obtain ⟨hf, hfc, hfb, hf'b, hf0⟩ :=
    localAmplitude_C1_bounds ε d q K hR hℓ.le hℓ1 hreW hK
  have ha : amplitude d q (-2 * saddleAngle d q) ≠ 0 := by
    intro h
    have : localAmplitude ε d q 0 = 0 := by
      change amplitude d q (-2 * saddleAngle d q + localWidth ε d q * 0) /
        amplitude d q (-2 * saddleAngle d q) = 0
      rw [h, div_zero]
    rw [this] at hf0
    exact zero_ne_one hf0
  have hCa : 4 + 8 * K * zetaLogDerivMajorant ≤ max (4 + 8 * K * zetaLogDerivMajorant) Cp :=
    le_max_left _ _
  have hCp' : Cp ≤ max (4 + 8 * K * zetaLogDerivMajorant) Cp := le_max_right _ _
  exact lowerContribution_estimate (f' := localAmplitudeDeriv ε d q) hd hℓ hD ha hn hc
    (hCp.trans hCp') hf hfc hp hp' hp'' hp'0 hp''0 hre hlower
    (fun y hy => (hfb y hy).trans hCa) (fun y hy => (hf'b y hy).trans hCa)
    (fun y hy => (hp''_bd y hy).trans hCp') (fun y hy => (hp'''_bd y hy).trans hCp')
    h1 h2 hint htail

end RiemannJensen
