module

public import RiemannJensen.Dedekind.AmplitudeBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The derivative of the normalized local Dedekind amplitude

We compute the derivative of the normalized local Dedekind amplitude on small counting windows,
and show that it is uniformly bounded and continuous on the normalized local interval `[-1,1]`.

## Main definitions

* `dedekindLocalW`: The `w` coordinate of the normalized local Dedekind amplitude.
* `dedekindLocalAmplitudeDeriv`: The explicit derivative of the normalized local amplitude.

## Main results

* `hasDerivAt_normalizedDedekindLocalAmplitude`: The normalized amplitude has derivative
  `dedekindLocalAmplitudeDeriv` at every sufficiently large right-half-plane local point.
* `dedekind_local_amplitude_deriv`: On small counting windows the derivative exists and is
  uniformly bounded on `[-1,1]`.
* `eventually_continuousOn_dedekindLocalAmplitudeDeriv`: On small counting windows the derivative
  is continuous on `[-1,1]`.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set Filter
open scoped ComplexOrder

noncomputable section

private theorem amp_shifted_real_not_pole {z : ℂ} (hz : z ∈ Complex.slitPlane) (m : ℕ) :
    z / 2 + 1 / 4 ≠ -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  norm_num at him hre
  rw [Complex.mem_slitPlane_iff] at hz
  rcases hz with hz | hz
  · linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  · exact hz (by linarith)

private theorem amp_shifted_complex_not_pole {z : ℂ} (hz : z ∈ Complex.slitPlane) (m : ℕ) :
    z + 1 / 2 ≠ -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  norm_num at him hre
  rw [Complex.mem_slitPlane_iff] at hz
  rcases hz with hz | hz
  · linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  · exact hz (by linarith)

private theorem amp_sqrt_two_pi_ne_zero :
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

private theorem amp_differentiableAt_dedekindGammaRemainderReal {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ dedekindGammaRemainderReal z := by
  unfold dedekindGammaRemainderReal
  have hz2 : z / 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff] at hz ⊢
    rcases hz with hz | hz
    · left
      norm_num
      positivity
    · right
      norm_num
      exact hz
  have hnum : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2 + 1 / 4)) z :=
    (Complex.differentiableAt_Gamma _ (amp_shifted_real_not_pole hz)).comp z (by fun_prop)
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => (w / 2) ^ (w / 2 - 1 / 4)) z :=
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w / 2) z).cpow
      (by fun_prop) hz2
  have hden : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sqrt (2 * Real.pi) *
        (w / 2) ^ (w / 2 - 1 / 4) * Complex.exp (-w / 2)) z := by
    fun_prop
  have hden0 : Complex.sqrt (2 * Real.pi) *
        (z / 2) ^ (z / 2 - 1 / 4) * Complex.exp (-z / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero amp_sqrt_two_pi_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (div_ne_zero (Complex.slitPlane_ne_zero hz) two_ne_zero))))
      (Complex.exp_ne_zero _)
  exact hnum.div hden hden0

private theorem amp_differentiableAt_dedekindGammaRemainderComplex {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ dedekindGammaRemainderComplex z := by
  unfold dedekindGammaRemainderComplex
  have hnum : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z :=
    (Complex.differentiableAt_Gamma _ (amp_shifted_complex_not_pole hz)).comp z (by fun_prop)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ w) z :=
    differentiableAt_id.cpow differentiableAt_id hz
  have hden : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sqrt (2 * Real.pi) * w ^ w * Complex.exp (-w)) z := by
    fun_prop
  have hden0 : Complex.sqrt (2 * Real.pi) * z ^ z * Complex.exp (-z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero amp_sqrt_two_pi_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hz))))
      (Complex.exp_ne_zero _)
  exact hnum.div hden hden0

private theorem amp_differentiableAt_dedekindGammaRemainder
    (K : Type) [Field K] [NumberField K] {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (dedekindGammaRemainder K) z := by
  unfold dedekindGammaRemainder
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hcorr : DifferentiableAt ℂ (fun u : ℂ => 1 - 1 / (4 * u ^ 2)) z := by
    fun_prop (disch := simp [hz0])
  exact (hcorr.mul ((amp_differentiableAt_dedekindGammaRemainderReal hz).pow _)).mul
    ((amp_differentiableAt_dedekindGammaRemainderComplex hz).pow _)

/-- The `w` coordinate of the normalized local Dedekind amplitude. -/
noncomputable def dedekindLocalW
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q y : ℝ) : ℂ :=
  dedekindContourW K d q
    (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y)

/-- The explicit derivative of the normalized local Dedekind amplitude. -/
noncomputable def dedekindLocalAmplitudeDeriv
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q y : ℝ) : ℂ :=
  normalizedDedekindLocalAmplitude K d q y *
    dedekindLocalAmplitudeLogDeriv K d q y

private theorem hasDerivAt_dedekindLocalW
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q y : ℝ) :
    HasDerivAt (dedekindLocalW K d q)
      (Complex.I * (dedekindLocalWidth K d q : ℂ) / 2 *
        dedekindLocalW K d q y) y := by
  have h1 : HasDerivAt
      (fun y : ℝ => ((-2 * dedekindSaddleAngle K d q +
        dedekindLocalWidth K d q * y : ℝ) : ℂ))
      ((dedekindLocalWidth K d q * 1 : ℝ) : ℂ) y :=
    (((hasDerivAt_id y).const_mul (dedekindLocalWidth K d q)).const_add
      (-2 * dedekindSaddleAngle K d q)).ofReal_comp
  have h2 := (((h1.const_mul Complex.I).div_const 2).cexp).const_mul
    (((dedekindScaleT K d *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) : ℝ)) : ℂ)
  unfold dedekindLocalW dedekindContourW
  refine h2.congr_deriv ?_
  push_cast
  ring

private theorem amp_logDeriv_product_identity {L P a W z z' G G' D : ℂ} (hW : W ≠ 0)
    (hz : z ≠ 0) (hG : G ≠ 0) (hD : G' / G = D) :
    (L * (P * (W ^ P / W) * 1 * (a * W)) * z + L * W ^ P * (z' * (a * W))) * G +
        L * W ^ P * z * (G' * (a * W)) =
      L * W ^ P * z * G * (a * (P + W * (z' / z) + W * D)) := by
  subst hD
  field_simp

private theorem differentiableAt_analyticDedekindZeta
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (analyticDedekindZeta K) s :=
  (analyticDedekindZeta_holomorphic K _ (Set.mem_compl_singleton_iff.mpr hs)).differentiableAt
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hs))

private theorem hasDerivAt_dedekindAmplitude_local
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q y : ℝ)
    (hwre : 4 ≤ (1 / 2 + dedekindLocalW K d q y).re)
    (hwnorm : 4 ≤ ‖dedekindLocalW K d q y‖)
    (hgammaSlit : dedekindGammaRemainder K (dedekindLocalW K d q y) ∈
      Complex.slitPlane) :
    HasDerivAt
      (fun y => dedekindAmplitude K d q
        (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y))
      (dedekindAmplitude K d q
          (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q * y) *
        dedekindLocalAmplitudeLogDeriv K d q y) y := by
  let w := dedekindLocalW K d q
  have h72 : 7 / 2 ≤ (w y).re := by
    norm_num [add_re] at hwre
    linarith
  have hw0 : w y ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖w y‖ ≠ 0)
  have hwslit : w y ∈ Complex.slitPlane := Or.inl (by linarith)
  have hsre : 1 < (1 / 2 + w y).re := by linarith
  have hsne : 1 / 2 + w y ≠ 1 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hgDiff : DifferentiableAt ℂ (dedekindGammaRemainder K) (w y) :=
    amp_differentiableAt_dedekindGammaRemainder K hwslit
  have hw := hasDerivAt_dedekindLocalW K d q y
  have hpow := ((hasDerivAt_id (w y)).cpow_const
      (c := (dedekindPowerExponent K : ℂ)) hwslit).comp y hw
  have hzeta :=
    (differentiableAt_analyticDedekindZeta K hsne).hasDerivAt.comp y (hw.const_add (1 / 2))
  have hgamma := hgDiff.hasDerivAt.comp y hw
  have htot := (((hpow.const_mul (dedekindLeadingConstant K : ℂ)).mul hzeta).mul hgamma)
  have hgammaLogDeriv :
      deriv (dedekindGammaRemainder K) (w y) /
          dedekindGammaRemainder K (w y) =
        deriv (dedekindGammaLog K) (w y) := by
    have h := Complex.deriv_log_comp_eq_logDeriv hgDiff hgammaSlit
    change deriv (dedekindGammaRemainder K) (w y) /
        dedekindGammaRemainder K (w y) =
      deriv (fun x => Complex.log (dedekindGammaRemainder K x)) (w y)
    simpa [Function.comp_def, logDeriv] using h.symm
  have hpow' : (w y) ^ ((dedekindPowerExponent K : ℂ) - 1) =
      (w y) ^ (dedekindPowerExponent K : ℂ) / (w y) := by
    rw [Complex.cpow_sub _ _ hw0, Complex.cpow_one]
  unfold dedekindAmplitude
  change HasDerivAt
    (fun y : ℝ =>
      (dedekindLeadingConstant K : ℂ) *
        w y ^ (dedekindPowerExponent K : ℂ) *
        analyticDedekindZeta K (1 / 2 + w y) *
        dedekindGammaRemainder K (w y)) _ y
  refine htot.congr_deriv ?_
  simp only [id, Function.comp_apply, Pi.mul_apply, hpow']
  unfold dedekindLocalAmplitudeLogDeriv
  dsimp only
  exact amp_logDeriv_product_identity hw0 (analyticDedekindZeta_ne_zero_of_one_lt_re K hsre)
    (dedekindGammaRemainder_ne_zero_of_re_nonneg K (by linarith) hwnorm) hgammaLogDeriv

/-- The normalized amplitude has the explicit derivative at every sufficiently
large right-half-plane local point. -/
theorem hasDerivAt_normalizedDedekindLocalAmplitude
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q y : ℝ)
    (hwre : 4 ≤ (1 / 2 + dedekindLocalW K d q y).re)
    (hwnorm : 4 ≤ ‖dedekindLocalW K d q y‖)
    (hgammaSlit : dedekindGammaRemainder K (dedekindLocalW K d q y) ∈
      Complex.slitPlane) :
    HasDerivAt (normalizedDedekindLocalAmplitude K d q)
      (dedekindLocalAmplitudeDeriv K d q y) y := by
  have h := (hasDerivAt_dedekindAmplitude_local K d q y hwre hwnorm hgammaSlit).div_const
    (dedekindAmplitude K d q (-2 * dedekindSaddleAngle K d q))
  refine h.congr_deriv ?_
  unfold dedekindLocalAmplitudeDeriv normalizedDedekindLocalAmplitude
  ring


private theorem continuousAt_deriv_dedekindGammaLog
    (K : Type) [Field K] [NumberField K] {w : ℂ}
    (hw : w ∈ Complex.slitPlane)
    (hg : dedekindGammaRemainder K w ∈ Complex.slitPlane) :
    ContinuousAt (deriv (dedekindGammaLog K)) w := by
  let U : Set ℂ := Complex.slitPlane ∩
    (dedekindGammaRemainder K) ⁻¹' Complex.slitPlane
  have hU : U ∈ nhds w :=
    inter_mem (Complex.isOpen_slitPlane.mem_nhds hw)
      ((amp_differentiableAt_dedekindGammaRemainder K hw).continuousAt.eventually
        (Complex.isOpen_slitPlane.mem_nhds hg))
  have hdiff : DifferentiableOn ℂ (dedekindGammaLog K) U := by
    intro z hz
    unfold dedekindGammaLog
    exact ((amp_differentiableAt_dedekindGammaRemainder K hz.1).hasDerivAt.clog
      hz.2).differentiableAt.differentiableWithinAt
  exact (hdiff.analyticAt hU).deriv.continuousAt

private theorem continuousAt_deriv_analyticDedekindZeta
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : s ≠ 1) :
    ContinuousAt (deriv (analyticDedekindZeta K)) s := by
  have hU : ({1}ᶜ : Set ℂ) ∈ nhds s :=
    isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hs)
  exact ((analyticDedekindZeta_holomorphic K).analyticAt hU).deriv.continuousAt

/-- Continuity of the explicit normalized-amplitude derivative under the same
pointwise right-half-plane and Gamma-branch hypotheses used for its formula. -/
theorem continuousOn_dedekindLocalAmplitudeDeriv
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q : ℝ)
    (hre : ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + dedekindLocalW K d q y).re)
    (hnorm : ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ ‖dedekindLocalW K d q y‖)
    (hgamma : ∀ y ∈ Icc (-1 : ℝ) 1,
      dedekindGammaRemainder K (dedekindLocalW K d q y) ∈
        Complex.slitPlane) :
    ContinuousOn (dedekindLocalAmplitudeDeriv K d q) (Icc (-1 : ℝ) 1) := by
  intro y hy
  let w := dedekindLocalW K d q
  have hwre := hre y hy
  have hwnorm := hnorm y hy
  have hgslit := hgamma y hy
  have hwslit : w y ∈ Complex.slitPlane := Or.inl (by
    norm_num [add_re] at hwre
    linarith)
  have hsne : 1 / 2 + w y ≠ 1 := by
    intro h
    have hsre : 1 < (1 / 2 + w y).re := by linarith
    rw [h] at hsre
    norm_num at hsre
  have hwcont : ContinuousAt w y :=
    (hasDerivAt_dedekindLocalW K d q y).continuousAt
  have hscont : ContinuousAt (fun x => 1 / 2 + w x) y :=
    hwcont.const_add _
  have hzcont : ContinuousAt (fun x => analyticDedekindZeta K (1 / 2 + w x)) y := by
    simpa [Function.comp_def] using
      (differentiableAt_analyticDedekindZeta K hsne).continuousAt.comp_of_eq hscont rfl
  have hdzcont : ContinuousAt
      (fun x => deriv (analyticDedekindZeta K) (1 / 2 + w x)) y := by
    simpa [Function.comp_def] using
      (continuousAt_deriv_analyticDedekindZeta K hsne).comp_of_eq hscont rfl
  have hGcont : ContinuousAt (fun x => deriv (dedekindGammaLog K) (w x)) y := by
    simpa [Function.comp_def] using
      (continuousAt_deriv_dedekindGammaLog K hwslit hgslit).comp_of_eq hwcont rfl
  have hquot : ContinuousAt (fun x =>
      deriv (analyticDedekindZeta K) (1 / 2 + w x) /
        analyticDedekindZeta K (1 / 2 + w x)) y :=
    hdzcont.div hzcont (analyticDedekindZeta_ne_zero_of_one_lt_re K (by linarith))
  have hLcont : ContinuousAt (dedekindLocalAmplitudeLogDeriv K d q) y := by
    unfold dedekindLocalAmplitudeLogDeriv
    change ContinuousAt (fun x =>
      Complex.I * (dedekindLocalWidth K d q : ℂ) / 2 *
        ((dedekindPowerExponent K : ℂ) +
          w x * (deriv (analyticDedekindZeta K) (1 / 2 + w x) /
            analyticDedekindZeta K (1 / 2 + w x)) +
          w x * deriv (dedekindGammaLog K) (w x))) y
    fun_prop
  unfold dedekindLocalAmplitudeDeriv
  exact ((hasDerivAt_normalizedDedekindLocalAmplitude K d q y hwre hwnorm
    hgslit).continuousAt.mul hLcont).continuousWithinAt


private theorem dedekindLocalWidth_nonneg_of_mem_Icc
    (K : Type) [Field K] [NumberField K] {d : ℕ} {q : ℝ}
    (hα : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ dedekindLocalWidth K d q := by
  unfold dedekindLocalWidth dedekindLocalEpsilon
  exact mul_nonneg (by norm_num)
    (le_min hα.1 (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩))

private theorem dedekindLocalWidth_le_one
    (K : Type) [Field K] [NumberField K] {d : ℕ} {q : ℝ}
    (hα : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2)) :
    dedekindLocalWidth K d q ≤ 1 := by
  unfold dedekindLocalWidth dedekindLocalEpsilon
  have hm := min_le_left (dedekindSaddleAngle K d q) (Real.cos (dedekindSaddleAngle K d q))
  nlinarith [hα.2, Real.pi_lt_four]

private theorem le_dedekindScaleT_of_le_mul
    (K : Type) [Field K] [NumberField K] {d : ℕ} {q c₀ : ℝ} (hd1 : 1 ≤ d)
    (hcpi : c₀ ≤ Real.pi / 128) (hqc : q ≤ c₀ * dedekindScaleT K d) :
    q ≤ dedekindScaleT K d :=
  hqc.trans (mul_le_of_le_one_left (dedekindScaleT_pos K d hd1).le
    (by linarith [Real.pi_lt_four]))

private theorem dedekindLocalWidth_mul_norm_le_re
    (K : Type) [Field K] [NumberField K]
    (d : ℕ) (q y : ℝ)
    (hT : 0 ≤ dedekindScaleT K d)
    (hr : 0 ≤ dedekindSaddleRadius K d (dedekindSaddleAngle K d q))
    (hα : dedekindSaddleAngle K d q ∈ Set.Icc 0 (Real.pi / 2))
    (hy : |y| ≤ 1) :
    dedekindLocalWidth K d q * ‖dedekindLocalW K d q y‖ ≤
      (1 / 2 + dedekindLocalW K d q y).re := by
  let α := dedekindSaddleAngle K d q
  let ℓ := dedekindLocalWidth K d q
  let R := dedekindScaleT K d * dedekindSaddleRadius K d α
  have hcos : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hℓ0 : 0 ≤ ℓ := dedekindLocalWidth_nonneg_of_mem_Icc K hα
  have hℓcos : ℓ ≤ Real.cos α / 4 := by
    dsimp [ℓ, dedekindLocalWidth, dedekindLocalEpsilon]
    have := min_le_right α (Real.cos α)
    nlinarith
  have ht : |ℓ * y| ≤ Real.cos α := by
    rw [abs_mul, abs_of_nonneg hℓ0]
    calc
      ℓ * |y| ≤ ℓ * 1 := mul_le_mul_of_nonneg_left hy hℓ0
      _ ≤ Real.cos α := by linarith
  have hlip := Real.abs_cos_sub_cos_le (α - ℓ * y / 2) α
  rw [show α - ℓ * y / 2 - α = -(ℓ * y / 2) by ring, abs_neg, abs_div, abs_two] at hlip
  have hcoslower : Real.cos α / 2 ≤ Real.cos (α - ℓ * y / 2) := by
    have hlo := neg_abs_le (Real.cos (α - ℓ * y / 2) - Real.cos α)
    linarith
  have hR0 : 0 ≤ R := mul_nonneg hT hr
  have hnorm : ‖dedekindLocalW K d q y‖ = R := by
    unfold dedekindLocalW
    exact norm_dedekindContourW K hT hr
  have hre : (dedekindLocalW K d q y).re =
      R * Real.cos (α - ℓ * y / 2) := by
    simp only [dedekindLocalW, dedekindContourW_re]
    rw [show (-2 * α + ℓ * y) / 2 = -(α - ℓ * y / 2) by ring, Real.cos_neg]
  rw [hnorm]
  norm_num [add_re]
  rw [hre]
  have hleft : ℓ * R ≤ (Real.cos α / 2) * R :=
    mul_le_mul_of_nonneg_right (by linarith) hR0
  have hright : (Real.cos α / 2) * R ≤ R * Real.cos (α - ℓ * y / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hcoslower hR0]
  linarith

private theorem dedekindSaddleAngle_mem_Icc_and_pos_of_window
    (K : Type) [Field K] [NumberField K] {d : ℕ} {q : ℝ} (hd1 : 1 ≤ d)
    (hedge : dedekindEdgeQ K d < q) (hqT : q ≤ dedekindScaleT K d) :
    dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) ∧ 0 < q := by
  have hα := dedekindSaddle_inverse_range K d hd1 ⟨hedge, hqT⟩
  have hαcc : dedekindSaddleAngle K d q ∈ Icc 0 (Real.pi / 2) := ⟨hα.1.le, hα.2.le⟩
  refine ⟨hαcc, ?_⟩
  have hqr := one_le_dedekindSaddleQ_mul_radius_sq K d hd1 hαcc
  rw [dedekindSaddle_inverse K d hd1 ⟨hedge, hqT⟩] at hqr
  nlinarith [sq_nonneg (dedekindSaddleRadius K d (dedekindSaddleAngle K d q))]

private theorem le_re_dedekindLocalW_of_window
    (K : Type) [Field K] [NumberField K] {d : ℕ} {q c₀ R₀ y : ℝ} (hd1 : 1 ≤ d)
    (hedge : dedekindEdgeQ K d < q) (hqT : q ≤ dedekindScaleT K d)
    (hqc : q ≤ c₀ * dedekindScaleT K d) (hR₀ : 0 < R₀) (hcR : c₀ ≤ Real.pi / (32 * R₀))
    (hlocal : ∀ θ ∈ Icc (-2 * dedekindSaddleAngle K d q - dedekindLocalWidth K d q)
        (-2 * dedekindSaddleAngle K d q + dedekindLocalWidth K d q),
        Real.pi / 32 * dedekindScaleT K d / q ≤ (dedekindContourW K d q θ).re)
    (hy : |y| ≤ 1) :
    R₀ ≤ (dedekindLocalW K d q y).re := by
  obtain ⟨hαcc, hqpos⟩ := dedekindSaddleAngle_mem_Icc_and_pos_of_window K hd1 hedge hqT
  have hwidth0 := dedekindLocalWidth_nonneg_of_mem_Icc K hαcc
  have hT := dedekindScaleT_pos K d hd1
  have hrebase : Real.pi / 32 * dedekindScaleT K d / q ≤ (dedekindLocalW K d q y).re := by
    refine hlocal _ ?_
    rw [abs_le] at hy
    constructor <;> nlinarith
  have hc : 32 * R₀ * c₀ ≤ Real.pi := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hR₀)] at hcR
    nlinarith [hcR]
  have hmul : R₀ * q ≤ (dedekindLocalW K d q y).re * q :=
    calc R₀ * q ≤ R₀ * (c₀ * dedekindScaleT K d) := by gcongr
      _ ≤ Real.pi / 32 * dedekindScaleT K d := by nlinarith
      _ ≤ _ := (div_le_iff₀ hqpos).mp hrebase
  nlinarith

private theorem dedekindGammaRemainder_mem_slitPlane_of_le_re
    (K : Type) [Field K] [NumberField K] {WG : ℝ}
    (hnear : ∀ w : ℂ, |arg w| ≤ 2 * Real.pi / 3 → WG ≤ ‖w‖ →
      ‖dedekindGammaRemainder K w - 1‖ ≤ 1 / 2 ∧ dedekindGammaRemainder K w ≠ 0)
    {w : ℂ} (hw0 : 0 ≤ w.re) (hWG : WG ≤ w.re) :
    dedekindGammaRemainder K w ∈ Complex.slitPlane := by
  have harg : |arg w| ≤ 2 * Real.pi / 3 :=
    (Complex.abs_arg_le_pi_div_two_iff.mpr hw0).trans (by linarith [Real.pi_pos])
  have hgnear :=
    (hnear w harg (hWG.trans (Complex.re_le_norm _))).1
  rw [show dedekindGammaRemainder K w = 1 + (dedekindGammaRemainder K w - 1) by ring]
  apply Complex.mem_slitPlane_of_norm_lt_one
  linarith

/-- On every sufficiently small fixed counting window, the normalized local Dedekind amplitude
has derivative `dedekindLocalAmplitudeDeriv`, and that derivative is uniformly bounded on
`[-1,1]`. -/
theorem dedekind_local_amplitude_deriv
    (K : Type) [Field K] [NumberField K] :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ∀ y : ℝ, |y| ≤ 1 →
          HasDerivAt (normalizedDedekindLocalAmplitude K d q)
            (dedekindLocalAmplitudeDeriv K d q y) y ∧
          ‖dedekindLocalAmplitudeDeriv K d q y‖ ≤ C := by
  obtain ⟨cA, CA, hcA, hCA, hamp⟩ := dedekind_local_amplitude_bound K
  obtain ⟨CL, WL, hCL, hWL, hlog⟩ :=
    dedekind_local_amplitude_C1_conditional K
  obtain ⟨WG, hWG, hnear⟩ :=
    GammaSector.dedekindGammaRemainder_near_one K
  let R₀ : ℝ := max 4 (max (max 1 WL) WG)
  let c₁ : ℝ := min cA (min (Real.pi / 128) (Real.pi / (32 * R₀)))
  let C : ℝ := CA * CL
  have hR₀ : 0 < R₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨c₁, C, lt_min hcA (lt_min (by positivity)
    (div_pos Real.pi_pos (mul_pos (by norm_num) hR₀))), mul_pos hCA hCL, fun c₀ hc₀ hc₀c₁ => ?_⟩
  have hcA' : c₀ ≤ cA := hc₀c₁.trans (min_le_left _ _)
  have hcpi : c₀ ≤ Real.pi / 128 :=
    hc₀c₁.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hcR : c₀ ≤ Real.pi / (32 * R₀) :=
    hc₀c₁.trans (min_le_right _ _) |>.trans (min_le_right _ _)
  filter_upwards [hamp c₀ hc₀ hcA', dedekind_contour_local_re K,
    eventually_ge_atTop 1] with d hampd hlocal hd1
  intro q hedge hqc y hy
  have hT := dedekindScaleT_pos K d hd1
  have hqT := le_dedekindScaleT_of_le_mul K hd1 hcpi hqc
  obtain ⟨hαcc, -⟩ := dedekindSaddleAngle_mem_Icc_and_pos_of_window K hd1 hedge hqT
  have hr := dedekindSaddleRadius_pos K d hd1 hαcc
  have hwidth0 := dedekindLocalWidth_nonneg_of_mem_Icc K hαcc
  let w := dedekindLocalW K d q y
  have hR₀re : R₀ ≤ w.re :=
    le_re_dedekindLocalW_of_window K hd1 hedge hqT hqc hR₀ hcR (hlocal q hedge hqT) hy
  have hre4 : 4 ≤ (1 / 2 + w).re := by
    norm_num [add_re]
    linarith [(le_max_left 4 (max (max 1 WL) WG)).trans hR₀re]
  have hwnorm : R₀ ≤ ‖w‖ :=
    hR₀re.trans (Complex.re_le_norm _)
  have hlargeL : max 1 WL ≤ ‖w‖ :=
    ((le_max_left (max 1 WL) WG).trans
      (le_max_right 4 (max (max 1 WL) WG))).trans hwnorm
  have hgslit : dedekindGammaRemainder K w ∈ Complex.slitPlane :=
    dedekindGammaRemainder_mem_slitPlane_of_le_re K hnear (hR₀.le.trans hR₀re)
      (((le_max_right (max 1 WL) WG).trans (le_max_right 4 _)).trans hR₀re)
  have hspeed : dedekindLocalWidth K d q * ‖w‖ ≤ (1 / 2 + w).re :=
    dedekindLocalWidth_mul_norm_le_re K d q y hT.le hr.le hαcc hy
  have hlogbd := hlog d q y hwidth0 (dedekindLocalWidth_le_one K hαcc) hre4 hlargeL hspeed
  have hderiv := hasDerivAt_normalizedDedekindLocalAmplitude K d q y
    hre4 ((le_max_left 4 (max (max 1 WL) WG)).trans hwnorm) hgslit
  refine ⟨hderiv, ?_⟩
  unfold dedekindLocalAmplitudeDeriv
  rw [norm_mul]
  exact mul_le_mul (hampd q hedge hqc y hy) hlogbd (norm_nonneg _) hCA.le

/-- On the same sufficiently small counting windows, the explicit derivative
of the normalized Dedekind amplitude is continuous on the normalized local
interval. -/
theorem eventually_continuousOn_dedekindLocalAmplitudeDeriv
    (K : Type) [Field K] [NumberField K] :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q : ℝ,
        dedekindEdgeQ K d < q → q ≤ c₀ * dedekindScaleT K d →
        ContinuousOn (dedekindLocalAmplitudeDeriv K d q) (Icc (-1 : ℝ) 1) := by
  obtain ⟨-, WL, -, -, -⟩ := dedekind_local_amplitude_C1_conditional K
  obtain ⟨WG, -, hnear⟩ := GammaSector.dedekindGammaRemainder_near_one K
  let R₀ : ℝ := max 4 (max (max 1 WL) WG)
  let c₁ : ℝ := min (Real.pi / 128) (Real.pi / (32 * R₀))
  have hR₀ : 0 < R₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨c₁, lt_min (by positivity)
    (div_pos Real.pi_pos (mul_pos (by norm_num) hR₀)),
    fun c₀ hc₀ hc₀c₁ => ?_⟩
  have hcpi : c₀ ≤ Real.pi / 128 :=
    hc₀c₁.trans (min_le_left _ _)
  have hcR : c₀ ≤ Real.pi / (32 * R₀) :=
    hc₀c₁.trans (min_le_right _ _)
  filter_upwards [dedekind_contour_local_re K,
    eventually_ge_atTop 1] with d hlocal hd1
  intro q hedge hqc
  have hqT := le_dedekindScaleT_of_le_mul K hd1 hcpi hqc
  have hR₀re : ∀ y ∈ Icc (-1 : ℝ) 1, R₀ ≤ (dedekindLocalW K d q y).re := fun y hy =>
    le_re_dedekindLocalW_of_window K hd1 hedge hqT hqc hR₀ hcR (hlocal q hedge hqT)
      (abs_le.mpr hy)
  have h4 : (4 : ℝ) ≤ R₀ := le_max_left _ _
  apply continuousOn_dedekindLocalAmplitudeDeriv K d q
  · intro y hy
    norm_num [add_re]
    linarith [hR₀re y hy]
  · exact fun y hy => (h4.trans (hR₀re y hy)).trans (Complex.re_le_norm _)
  · exact fun y hy => dedekindGammaRemainder_mem_slitPlane_of_le_re K hnear
      (by linarith [hR₀re y hy])
      (((le_max_right (max 1 WL) WG).trans (le_max_right 4 _)).trans (hR₀re y hy))

end

end RiemannJensen
