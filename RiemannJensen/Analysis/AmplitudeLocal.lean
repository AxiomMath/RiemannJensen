module

public import RiemannJensen.Analysis.ZetaLogDerivDecay
public import RiemannJensen.Analysis.AmplitudeDefinitions
public import RiemannJensen.Analysis.ComplexStirling
public import RiemannJensen.Analysis.GammaRemainderBounds

/-!
# The normalized local amplitude

For the saddle angle `θ_q = -2 α_q` and the local width `ℓ_q`, the normalized local amplitude
is `f_q(y) = a_q(θ_q + ℓ_q y) / a_q(θ_q)` on `[-1, 1]`. We prove `f_q(0) = 1` and a uniform
`C¹` bound via the logarithmic derivative: with `w(y) = w_q(θ_q + ℓ_q y)` one has
`w'(y) = (i ℓ_q / 2) w(y)` and `a'/a = (i ℓ_q / 2) (7/4 + w ζ'/ζ(1/2 + w) + w (log g)'(w))`.

## Main definitions

* `localAmplitude`: The normalized local amplitude `f_q`.
* `localAmplitudeDeriv`: The explicit derivative of `f_q`.

## Main results

* `localAmplitude_C1_bounds`: `f_q(0) = 1`, and `f_q` is `C¹` on `[-1, 1]` with `f_q` and its
  derivative bounded by `4 + 8 K M`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set

/-- The angular parameter of the lower saddle on the circle `w = R e^{iθ/2}`. -/
noncomputable def saddleTheta (d : ℕ) (q : ℝ) : ℝ :=
  -2 * saddleAngle d q

/-- The `w`-coordinate along the local saddle interval. -/
noncomputable def localW (ε : ℝ) (d : ℕ) (q y : ℝ) : ℂ :=
  contourW d q (saddleTheta d q + localWidth ε d q * y)

/-- The normalized local amplitude `f_q(y) = a_q(θ_q + ℓ_q y) / a_q(θ_q)`. -/
noncomputable def localAmplitude (ε : ℝ) (d : ℕ) (q y : ℝ) : ℂ :=
  amplitude d q (saddleTheta d q + localWidth ε d q * y) /
    amplitude d q (saddleTheta d q)

/-- The logarithmic derivative of the local amplitude in the variable `y`. -/
noncomputable def localAmplitudeLogDeriv (ε : ℝ) (d : ℕ) (q y : ℝ) : ℂ :=
  Complex.I * (localWidth ε d q : ℂ) / 2 *
    (7 / 4 +
      localW ε d q y *
        (deriv riemannZeta (1 / 2 + localW ε d q y) /
          riemannZeta (1 / 2 + localW ε d q y)) +
      localW ε d q y * logDeriv gammaRemainder (localW ε d q y))

/-- The explicit derivative of the normalized local amplitude. -/
noncomputable def localAmplitudeDeriv (ε : ℝ) (d : ℕ) (q y : ℝ) : ℂ :=
  localAmplitude ε d q y * localAmplitudeLogDeriv ε d q y

/-- At `y = 0` the local `w`-coordinate is the contour point at the saddle angle. -/
theorem localW_zero (ε : ℝ) (d : ℕ) (q : ℝ) :
    localW ε d q 0 = contourW d q (saddleTheta d q) := by
  simp [localW]

/-- The local `w`-coordinate satisfies `w'(y) = (i ℓ / 2) w(y)`. -/
theorem hasDerivAt_localW (ε : ℝ) (d : ℕ) (q y : ℝ) :
    HasDerivAt (localW ε d q)
      (Complex.I * (localWidth ε d q : ℂ) / 2 * localW ε d q y) y := by
  have h1 : HasDerivAt
      (fun y : ℝ => ((saddleTheta d q + localWidth ε d q * y : ℝ) : ℂ))
      ((localWidth ε d q * 1 : ℝ) : ℂ) y :=
    (((hasDerivAt_id y).const_mul (localWidth ε d q)).const_add
      (saddleTheta d q)).ofReal_comp
  have h2 := (((h1.const_mul Complex.I).div_const 2).cexp).const_mul
    (((scaleT d * saddleRadius d (saddleAngle d q) : ℝ)) : ℂ)
  unfold localW contourW
  refine h2.congr_deriv ?_
  push_cast
  ring

/-- If `re(1/2 + w) ≥ 4` and `‖w‖ ≥ 4`, then `w` lies in the slit plane and in
`GammaCore.grDomain`, `w ≠ 0`, `1/2 + w ≠ 1`, `ζ(1/2 + w) ≠ 0`, `gammaRemainder w ≠ 0` and
`0 ≤ re w`. -/
theorem local_point_facts {w : ℂ} (hw : 4 ≤ (1 / 2 + w).re) (hn : 4 ≤ ‖w‖) :
    w ∈ slitPlane ∧ w ≠ 0 ∧ w ∈ GammaCore.grDomain ∧ 1 / 2 + w ≠ 1 ∧
      riemannZeta (1 / 2 + w) ≠ 0 ∧ gammaRemainder w ≠ 0 ∧ 0 ≤ w.re := by
  have hre : 7 / 2 ≤ w.re := by linarith [show (1 / 2 + w).re = 1 / 2 + w.re by simp]
  have hmem : w ∈ GammaCore.grDomain := GammaCore.subset_grDomain (by linarith) hn
  refine ⟨Or.inl (by linarith), ?_, hmem, ?_, riemannZeta_ne_zero_of_four_le_re hw,
    gammaRemainder_ne_zero hmem, by linarith⟩
  · rintro rfl
    norm_num at hre
  · intro h
    rw [h] at hw
    norm_num at hw

/-- The constant prefactor `(π/2)^(1/4)` of the amplitude. -/
noncomputable def amplitudeConst : ℂ :=
  Complex.cpow (Real.pi / 2) (1 / 4)

/-- The amplitude is `amplitudeConst * w ^ (7/4) * ζ(1/2 + w) * gammaRemainder w` at the contour
point `w = contourW d q θ`. -/
theorem amplitude_eq_const_mul (d : ℕ) (q θ : ℝ) :
    amplitude d q θ =
      amplitudeConst * contourW d q θ ^ (7 / 4 : ℂ) *
        riemannZeta (1 / 2 + contourW d q θ) * gammaRemainder (contourW d q θ) :=
  rfl

/-- The constant prefactor of the amplitude is nonzero. -/
theorem amplitudeConst_ne_zero : amplitudeConst ≠ 0 := by
  unfold amplitudeConst
  rw [Complex.cpow_eq_pow]
  refine (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr ?_
  exact_mod_cast (show (0 : ℝ) < Real.pi / 2 by positivity).ne'

/-- Along the local interval, the derivative in `y` of the amplitude is the amplitude times
`localAmplitudeLogDeriv`. -/
theorem hasDerivAt_amplitude_local (ε : ℝ) (d : ℕ) (q y : ℝ)
    (hw : 4 ≤ (1 / 2 + localW ε d q y).re) (hn : 4 ≤ ‖localW ε d q y‖) :
    HasDerivAt (fun y => amplitude d q (saddleTheta d q + localWidth ε d q * y))
      (amplitude d q (saddleTheta d q + localWidth ε d q * y) *
        localAmplitudeLogDeriv ε d q y) y := by
  obtain ⟨hslit, hW0, hmem, hne, hz0, hg0, -⟩ := local_point_facts hw hn
  set W := localW ε d q with hWdef
  have hW := hasDerivAt_localW ε d q y
  have hP := ((hasDerivAt_id (W y)).cpow_const (c := (7 / 4 : ℂ)) hslit).comp y hW
  have hZ := (differentiableAt_riemannZeta hne).hasDerivAt.comp y (hW.const_add (1 / 2))
  have hgd : DifferentiableAt ℂ gammaRemainder (W y) :=
    differentiableOn_gammaRemainder.differentiableAt
      (GammaCore.isOpen_grDomain.mem_nhds hmem)
  have hG := hgd.hasDerivAt.comp y hW
  have htot := ((hP.const_mul amplitudeConst).mul hZ).mul hG
  have hfun : (fun y => amplitude d q (saddleTheta d q + localWidth ε d q * y)) =
      fun y => amplitudeConst * W y ^ (7 / 4 : ℂ) * riemannZeta (1 / 2 + W y) *
        gammaRemainder (W y) := rfl
  rw [hfun]
  refine htot.congr_deriv ?_
  have hpow : W y ^ ((7 / 4 : ℂ) - 1) = W y ^ (7 / 4 : ℂ) / W y := by
    rw [Complex.cpow_sub _ _ hW0, Complex.cpow_one]
  have hA : amplitude d q (saddleTheta d q + localWidth ε d q * y) =
      amplitudeConst * W y ^ (7 / 4 : ℂ) * riemannZeta (1 / 2 + W y) *
        gammaRemainder (W y) := rfl
  rw [hA]
  simp only [id, localAmplitudeLogDeriv, logDeriv_apply, hpow, ← hWdef,
    Function.comp_apply, Pi.mul_apply]
  generalize riemannZeta (1 / 2 + W y) = z at hz0 ⊢
  generalize deriv riemannZeta (1 / 2 + W y) = z'
  generalize gammaRemainder (W y) = G at hg0 ⊢
  generalize deriv gammaRemainder (W y) = G'
  field_simp

/-- The normalized local amplitude has derivative `localAmplitudeDeriv` at `y`. -/
theorem hasDerivAt_localAmplitude (ε : ℝ) (d : ℕ) (q y : ℝ)
    (hw : 4 ≤ (1 / 2 + localW ε d q y).re) (hn : 4 ≤ ‖localW ε d q y‖) :
    HasDerivAt (localAmplitude ε d q) (localAmplitudeDeriv ε d q y) y := by
  have h := (hasDerivAt_amplitude_local ε d q y hw hn).div_const
    (amplitude d q (saddleTheta d q))
  refine h.congr_deriv ?_
  unfold localAmplitudeDeriv localAmplitude
  ring

/-- The local `w`-coordinate has modulus equal to the saddle radius `T r`. -/
theorem norm_localW (ε : ℝ) (d : ℕ) (q y : ℝ)
    (hR : 0 ≤ scaleT d * saddleRadius d (saddleAngle d q)) :
    ‖localW ε d q y‖ = scaleT d * saddleRadius d (saddleAngle d q) :=
  norm_contourW d q _ hR

/-- The modulus of the amplitude on a saddle circle of positive radius. -/
theorem norm_amplitude (d : ℕ) (q θ : ℝ)
    (hR : 0 < scaleT d * saddleRadius d (saddleAngle d q)) :
    ‖amplitude d q θ‖ =
      ‖amplitudeConst‖ * (scaleT d * saddleRadius d (saddleAngle d q)) ^ (7 / 4 : ℝ) *
        ‖riemannZeta (1 / 2 + contourW d q θ)‖ * ‖gammaRemainder (contourW d q θ)‖ := by
  have hp : ‖contourW d q θ ^ (7 / 4 : ℂ)‖ = ‖contourW d q θ‖ ^ (7 / 4 : ℝ) := by
    simpa using Complex.norm_cpow_real (contourW d q θ) (7 / 4)
  rw [amplitude_eq_const_mul, norm_mul, norm_mul, norm_mul, hp, norm_contourW d q θ hR.le]

/-- Two-sided bound for the Gamma remainder on `‖w‖ ≥ 200`. -/
theorem gammaRemainder_norm_bounds {w : ℂ} (hw : 0 ≤ w.re) (hn : 200 ≤ ‖w‖) :
    67 / 100 ≤ ‖gammaRemainder w‖ ∧ ‖gammaRemainder w‖ ≤ 133 / 100 := by
  have h := norm_gammaRemainder_sub_one_le hw (by linarith)
  have h66 : 66 / ‖w‖ ≤ 33 / 100 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h1 := norm_sub_norm_le (gammaRemainder w) 1
  have h2 := norm_sub_norm_le 1 (gammaRemainder w)
  rw [norm_one] at h1 h2
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- The amplitude is nonzero at a contour point with `re(1/2 + w) ≥ 4` and `‖w‖ ≥ 4`. -/
theorem amplitude_ne_zero_of_re_of_norm {d : ℕ} {q θ : ℝ}
    (hw : 4 ≤ (1 / 2 + contourW d q θ).re) (hn : 4 ≤ ‖contourW d q θ‖) :
    amplitude d q θ ≠ 0 := by
  obtain ⟨-, hW0, -, -, hz0, hg0, -⟩ := local_point_facts hw hn
  rw [amplitude_eq_const_mul]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero amplitudeConst_ne_zero ?_) hz0) hg0
  exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hW0

/-- The normalized local amplitude equals `1` at `y = 0`. -/
theorem localAmplitude_zero {ε : ℝ} {d : ℕ} {q : ℝ}
    (h : amplitude d q (saddleTheta d q) ≠ 0) : localAmplitude ε d q 0 = 1 := by
  unfold localAmplitude
  rw [mul_zero, add_zero, div_self h]

/-- On a saddle circle of radius at least `200`, the normalized local amplitude is at most `4`. -/
theorem norm_localAmplitude_le_four {ε : ℝ} {d : ℕ} {q y : ℝ}
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hy : 4 ≤ (1 / 2 + localW ε d q y).re)
    (h0 : 4 ≤ (1 / 2 + contourW d q (saddleTheta d q)).re) :
    ‖localAmplitude ε d q y‖ ≤ 4 := by
  set R := scaleT d * saddleRadius d (saddleAngle d q) with hRdef
  have hRpos : 0 < R := by linarith
  have hny : ‖localW ε d q y‖ = R := norm_localW ε d q y hRpos.le
  have hn0 : ‖contourW d q (saddleTheta d q)‖ = R := norm_contourW d q _ hRpos.le
  obtain ⟨-, -, -, -, -, -, hrey⟩ := local_point_facts hy (by rw [hny]; linarith)
  obtain ⟨-, -, -, -, -, -, hre0⟩ := local_point_facts h0 (by rw [hn0]; linarith)
  have hzy := norm_riemannZeta_le_four_thirds hy
  have hz0 := three_fourths_le_norm_riemannZeta h0
  have hgy := gammaRemainder_norm_bounds hrey (by rw [hny]; exact hR)
  have hg0 := gammaRemainder_norm_bounds hre0 (by rw [hn0]; exact hR)
  set X := ‖amplitudeConst‖ * R ^ (7 / 4 : ℝ) with hX
  have hXpos : 0 < X := mul_pos (norm_pos_iff.mpr amplitudeConst_ne_zero) (by positivity)
  have hAy : ‖amplitude d q (saddleTheta d q + localWidth ε d q * y)‖ ≤
      X * (4 / 3) * (133 / 100) := by
    rw [norm_amplitude d q _ hRpos]
    change X * ‖riemannZeta (1 / 2 + localW ε d q y)‖ *
      ‖gammaRemainder (localW ε d q y)‖ ≤ _
    have := mul_le_mul hzy hgy.2 (norm_nonneg _) (by norm_num)
    nlinarith
  have hA0 : X * (3 / 4) * (67 / 100) ≤ ‖amplitude d q (saddleTheta d q)‖ := by
    rw [norm_amplitude d q _ hRpos]
    have := mul_le_mul hz0 hg0.1 (by norm_num) (norm_nonneg _)
    nlinarith
  unfold localAmplitude
  rw [norm_div, div_le_iff₀ (by nlinarith)]
  nlinarith

/-- On a saddle circle of radius `R ≥ 200`, if `0 ≤ ℓ ≤ 1` and `ℓ R ≤ K re w`, then the
logarithmic derivative of the local amplitude is at most `1 + 2 K M`. -/
theorem norm_localAmplitudeLogDeriv_le {ε : ℝ} {d : ℕ} {q K y : ℝ}
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hℓ0 : 0 ≤ localWidth ε d q) (hℓ1 : localWidth ε d q ≤ 1) (hK0 : 0 ≤ K)
    (hy : 4 ≤ (1 / 2 + localW ε d q y).re)
    (hK : localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
      K * (localW ε d q y).re) :
    ‖localAmplitudeLogDeriv ε d q y‖ ≤ 1 + 2 * K * zetaLogDerivMajorant := by
  set R := scaleT d * saddleRadius d (saddleAngle d q) with hRdef
  set ℓ := localWidth ε d q with hℓdef
  have hRpos : 0 < R := by linarith
  have hnW : ‖localW ε d q y‖ = R := norm_localW ε d q y hRpos.le
  obtain ⟨-, -, -, -, -, -, hrey⟩ := local_point_facts hy (by rw [hnW]; linarith)
  have hZ := mul_norm_zetaLogDeriv_le (x := ℓ * R) hK0 hy (by
    have : (1 / 2 + localW ε d q y).re = 1 / 2 + (localW ε d q y).re := by simp
    rw [this]
    nlinarith)
  have hG := norm_logDeriv_gammaRemainder_le hrey (by rw [hnW]; linarith)
  rw [hnW] at hG
  set Z := ‖deriv riemannZeta (1 / 2 + localW ε d q y) /
    riemannZeta (1 / 2 + localW ε d q y)‖ with hZdef
  set G := ‖logDeriv gammaRemainder (localW ε d q y)‖ with hGdef
  have hZn : 0 ≤ Z := norm_nonneg _
  have hGn : 0 ≤ G := norm_nonneg _
  have hRG : R * G ≤ 14 / 200 := by
    calc R * G ≤ R * (14 / R ^ 2) := mul_le_mul_of_nonneg_left hG hRpos.le
      _ = 14 / R := by field_simp
      _ ≤ 14 / 200 := by
        rw [div_le_div_iff₀ hRpos (by norm_num)]
        linarith
  have hnorm : ‖localAmplitudeLogDeriv ε d q y‖ ≤ ℓ / 2 * (7 / 4 + R * Z + R * G) := by
    unfold localAmplitudeLogDeriv
    rw [norm_mul]
    have h1 : ‖Complex.I * (ℓ : ℂ) / 2‖ = ℓ / 2 := by
      rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hℓ0]
      norm_num
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc _ ≤ ‖(7 / 4 : ℂ)‖ + ‖localW ε d q y *
            (deriv riemannZeta (1 / 2 + localW ε d q y) /
              riemannZeta (1 / 2 + localW ε d q y))‖ +
          ‖localW ε d q y * logDeriv gammaRemainder (localW ε d q y)‖ :=
          norm_add₃_le
      _ = 7 / 4 + R * Z + R * G := by
          have h74 : ‖(7 / 4 : ℂ)‖ = 7 / 4 := by norm_num
          rw [norm_mul, norm_mul, hnW, h74]
  have hlRG : ℓ * (R * G) ≤ 14 / 200 := by
    calc ℓ * (R * G) ≤ 1 * (R * G) :=
          mul_le_mul_of_nonneg_right hℓ1 (mul_nonneg hRpos.le hGn)
      _ ≤ 14 / 200 := by linarith
  have hfinal : ℓ / 2 * (7 / 4 + R * Z + R * G) =
      7 / 8 * ℓ + (ℓ * R) * Z / 2 + ℓ * (R * G) / 2 := by ring
  rw [hfinal] at hnorm
  nlinarith

/-- The local `w`-coordinate is continuous. -/
theorem continuous_localW (ε : ℝ) (d : ℕ) (q : ℝ) : Continuous (localW ε d q) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_localW ε d q x).continuousAt

/-- The derivative of the normalized local amplitude is continuous at `y` when
`re(1/2 + w) ≥ 4` and `‖w‖ ≥ 4`. -/
theorem continuousAt_localAmplitudeDeriv {ε : ℝ} {d : ℕ} {q y : ℝ}
    (hw : 4 ≤ (1 / 2 + localW ε d q y).re) (hn : 4 ≤ ‖localW ε d q y‖) :
    ContinuousAt (localAmplitudeDeriv ε d q) y := by
  obtain ⟨-, -, hmem, hne, hz0, hg0, -⟩ := local_point_facts hw hn
  have hWc := continuous_localW ε d q
  have hfc := (hasDerivAt_localAmplitude ε d q y hw hn).continuousAt
  have hzetaD : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hzA := hzetaD.analyticAt (isOpen_ne.mem_nhds hne)
  have hgA := differentiableOn_gammaRemainder.analyticAt
    (GammaCore.isOpen_grDomain.mem_nhds hmem)
  have hin : ContinuousAt (fun x : ℝ => 1 / 2 + localW ε d q x) y :=
    (continuous_const.add hWc).continuousAt
  have hz' : ContinuousAt (fun x : ℝ => deriv riemannZeta (1 / 2 + localW ε d q x)) y :=
    ContinuousAt.comp (f := fun x : ℝ => 1 / 2 + localW ε d q x)
      hzA.deriv.continuousAt hin
  have hz : ContinuousAt (fun x : ℝ => riemannZeta (1 / 2 + localW ε d q x)) y :=
    ContinuousAt.comp (f := fun x : ℝ => 1 / 2 + localW ε d q x)
      hzA.continuousAt hin
  have hlg' : ContinuousAt (fun x : ℝ => logDeriv gammaRemainder (localW ε d q x)) y :=
    ContinuousAt.comp (f := localW ε d q)
      (hgA.deriv.continuousAt.div hgA.continuousAt hg0) hWc.continuousAt
  unfold localAmplitudeDeriv localAmplitudeLogDeriv
  exact hfc.mul (continuousAt_const.mul
    ((continuousAt_const.add (hWc.continuousAt.mul (hz'.div hz hz0))).add
      (hWc.continuousAt.mul hlg')))

/-- **The normalized local amplitude is uniformly `C¹`.**

Suppose the saddle radius `R = T r` is at least `200`, the local width satisfies `0 ≤ ℓ ≤ 1`,
and on the local interval `re(1/2 + w) ≥ 4` and `ℓ R ≤ K re w`. Then `f = localAmplitude ε d q`
satisfies `f 0 = 1`, has the explicit derivative `localAmplitudeDeriv ε d q` on `[-1, 1]`, that
derivative is continuous there, and both are bounded by `4 + 8 K M`, where
`M = zetaLogDerivMajorant` is an absolute constant. -/
theorem localAmplitude_C1_bounds (ε : ℝ) (d : ℕ) (q K : ℝ)
    (hR : 200 ≤ scaleT d * saddleRadius d (saddleAngle d q))
    (hℓ0 : 0 ≤ localWidth ε d q) (hℓ1 : localWidth ε d q ≤ 1)
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + contourW d q (saddleTheta d q + localWidth ε d q * y)).re)
    (hK : ∀ y ∈ Icc (-1 : ℝ) 1,
      localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
        K * (contourW d q (saddleTheta d q + localWidth ε d q * y)).re) :
    (∀ y ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (localAmplitude ε d q) (localAmplitudeDeriv ε d q y) y) ∧
      ContinuousOn (localAmplitudeDeriv ε d q) (Icc (-1 : ℝ) 1) ∧
      (∀ y ∈ Icc (-1 : ℝ) 1,
        ‖localAmplitude ε d q y‖ ≤ 4 + 8 * K * zetaLogDerivMajorant) ∧
      (∀ y ∈ Icc (-1 : ℝ) 1,
        ‖localAmplitudeDeriv ε d q y‖ ≤ 4 + 8 * K * zetaLogDerivMajorant) ∧
      localAmplitude ε d q 0 = 1 := by
  have hRpos : 0 < scaleT d * saddleRadius d (saddleAngle d q) := by linarith
  have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hreW : ∀ y ∈ Icc (-1 : ℝ) 1, 4 ≤ (1 / 2 + localW ε d q y).re := hre
  have hnW : ∀ y, 4 ≤ ‖localW ε d q y‖ := fun y => by
    rw [norm_localW ε d q y hRpos.le]
    linarith
  have hre0 := hreW 0 h0mem
  rw [localW_zero] at hre0
  have hKnn : 0 ≤ K := by
    have h : localWidth ε d q * (scaleT d * saddleRadius d (saddleAngle d q)) ≤
        K * (localW ε d q 0).re := hK 0 h0mem
    have hpos : 0 < (localW ε d q 0).re := by
      have := hreW 0 h0mem
      simp only [add_re] at this
      norm_num at this
      linarith
    by_contra! hneg
    linarith [mul_neg_of_neg_of_pos hneg hpos, mul_nonneg hℓ0 hRpos.le]
  have hM := zetaLogDerivMajorant_nonneg
  have hbound := fun y (hy : y ∈ Icc (-1 : ℝ) 1) =>
    norm_localAmplitude_le_four (ε := ε) hR (hreW y hy) hre0
  refine ⟨fun y hy => hasDerivAt_localAmplitude ε d q y (hreW y hy) (hnW y),
    fun y hy => (continuousAt_localAmplitudeDeriv (hreW y hy) (hnW y)).continuousWithinAt,
    fun y hy => by
      linarith [hbound y hy, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hKnn) hM],
    fun y hy => ?_, localAmplitude_zero (amplitude_ne_zero_of_re_of_norm hre0
      (by rw [norm_contourW d q _ hRpos.le]; linarith))⟩
  unfold localAmplitudeDeriv
  rw [norm_mul]
  calc ‖localAmplitude ε d q y‖ * ‖localAmplitudeLogDeriv ε d q y‖
      ≤ 4 * (1 + 2 * K * zetaLogDerivMajorant) :=
        mul_le_mul (hbound y hy) (norm_localAmplitudeLogDeriv_le hR hℓ0 hℓ1 hKnn (hreW y hy)
          (hK y hy)) (norm_nonneg _) (by norm_num)
    _ = 4 + 8 * K * zetaLogDerivMajorant := by ring

end RiemannJensen
