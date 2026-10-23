module

public import RiemannJensen.Analysis.GaussianFull
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

namespace RiemannJensen

namespace Gaussian

open Complex Set MeasureTheory intervalIntegral

/-- For `0 < η ≤ 1`, the integral of `x⁻²` over `[η, 1]` equals `η⁻¹ - 1`. -/
theorem integral_inv_sq {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫ x in η..1, (x ^ 2)⁻¹) = η⁻¹ - 1 := by
  have hz : (0 : ℝ) ∉ Set.uIcc η 1 := by
    simp [Set.uIcc_of_le hη1, not_le_of_gt hη]
  have h := _root_.integral_zpow (a := η) (b := 1) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  norm_num [zpow_neg] at h
  rw [h]
  ring

/-- Integrating a `K/(n y²)` majorant over `[η,1]` costs at most `K/(nη)`. -/
theorem norm_tail_integral_le {r : ℝ → ℂ} {η n K : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < n) (hK : 0 ≤ K)
    (hr : ∀ y ∈ Set.Ioc η 1, ‖r y‖ ≤ (K / n) * (y ^ 2)⁻¹) :
    ‖∫ y in η..1, r y‖ ≤ K / (n * η) := by
  have hg : IntervalIntegrable (fun y : ℝ => (K / n) * (y ^ 2)⁻¹) volume η 1 :=
    (ContinuousOn.intervalIntegrable ((continuousOn_pow 2).inv₀ fun y hy =>
      pow_ne_zero _ (hη.trans_le ((Set.uIcc_of_le hη1).subset hy).1).ne')).const_mul _
  have h := intervalIntegral.norm_integral_le_of_norm_le hη1
    (Filter.Eventually.of_forall hr) hg
  rw [intervalIntegral.integral_const_mul, integral_inv_sq hη hη1] at h
  calc
    _ ≤ K / n * (η⁻¹ - 1) := h
    _ ≤ K / n * η⁻¹ := mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by positivity)
    _ = K / (n * η) := by field_simp

/-- For `0 < η ≤ 1`, the integral of `x⁻²` over `[-1, -η]` equals `η⁻¹ - 1`. -/
theorem integral_inv_sq_neg {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫ x in (-1 : ℝ)..(-η), (x ^ 2)⁻¹) = η⁻¹ - 1 := by
  rw [← integral_inv_sq hη hη1, ← intervalIntegral.integral_comp_neg]
  simp only [neg_sq]

/-- The corresponding `K/(n y²)` estimate on `[-1,-η]`. -/
theorem norm_tail_integral_neg_le {r : ℝ → ℂ} {η n K : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < n) (hK : 0 ≤ K)
    (hr : ∀ y ∈ Set.Ioc (-1 : ℝ) (-η), ‖r y‖ ≤ (K / n) * (y ^ 2)⁻¹) :
    ‖∫ y in (-1 : ℝ)..(-η), r y‖ ≤ K / (n * η) := by
  have hab : (-1 : ℝ) ≤ -η := neg_le_neg hη1
  have hg : IntervalIntegrable (fun y : ℝ => (K / n) * (y ^ 2)⁻¹)
      volume (-1) (-η) :=
    (ContinuousOn.intervalIntegrable ((continuousOn_pow 2).inv₀ fun y hy =>
      pow_ne_zero _ (((Set.uIcc_of_le hab).subset hy).2.trans_lt
        (neg_lt_zero.mpr hη)).ne)).const_mul _
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall hr) hg
  rw [intervalIntegral.integral_const_mul, integral_inv_sq_neg hη hη1] at h
  calc
    _ ≤ K / n * (η⁻¹ - 1) := h
    _ ≤ K / n * η⁻¹ := mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by positivity)
    _ = K / (n * η) := by field_simp

/-- The exact derivative arising in nonstationary-phase integration by parts. -/
noncomputable def tailQuotientDeriv (f f' p' p'' : ℝ → ℂ) (n : ℝ) (y : ℝ) : ℂ :=
  (f' y * ((n : ℂ) * p' y) - f y * ((n : ℂ) * p'' y)) /
    (((n : ℂ) * p' y) ^ 2)

/-- The quotient derivative split into the two terms used in its norm estimate. -/
lemma tailQuotientDeriv_eq {f f' p' p'' : ℝ → ℂ} {n y : ℝ} (hn : n ≠ 0) (hp : p' y ≠ 0) :
    tailQuotientDeriv f f' p' p'' n y =
      f' y / ((n : ℂ) * p' y) -
      f y * p'' y / ((n : ℂ) * (p' y) ^ 2) := by
  dsimp [tailQuotientDeriv]
  field_simp [Complex.ofReal_ne_zero.mpr hn, hp]

/-- A complex number whose norm dominates `c * |y|`, with `c > 0` and `y ≠ 0`, is nonzero. -/
theorem ne_zero_of_mul_abs_le_norm {z : ℂ} {c y : ℝ} (hc : 0 < c) (hy : 0 < |y|)
    (h : c * |y| ≤ ‖z‖) : z ≠ 0 :=
  norm_pos_iff.mp ((mul_pos hc hy).trans_le h)

/-- A nonnegative real multiple of a number with nonpositive real part has nonpositive
real part. -/
theorem re_ofReal_mul_nonpos {n : ℝ} {z : ℂ} (hn : 0 ≤ n) (h : z.re ≤ 0) :
    ((n : ℂ) * z).re ≤ 0 := by
  rw [Complex.re_ofReal_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hn h

/-- Pointwise `1/(n y²)` control of the differentiated integration-by-parts
quotient for `0 < |y| ≤ 1`. -/
theorem norm_tailQuotientDeriv_le
    {f f' p' p'' : ℝ → ℂ} {n c C y : ℝ}
    (hn : 0 < n) (hc : 0 < c)
    (hy : 0 < |y|) (hy1 : |y| ≤ 1) (hC : 0 ≤ C)
    (hf : ‖f y‖ ≤ C) (hfp : ‖f' y‖ ≤ C)
    (hpp : ‖p'' y‖ ≤ C)
    (hlower : c * |y| ≤ ‖p' y‖) :
    ‖tailQuotientDeriv f f' p' p'' n y‖ ≤
      ((C / c + C ^ 2 / c ^ 2) / n) * (y ^ 2)⁻¹ := by
  rw [tailQuotientDeriv_eq hn.ne' (ne_zero_of_mul_abs_le_norm hc hy hlower)]
  apply (norm_sub_le _ _).trans
  simp only [norm_div, norm_mul, norm_real, Real.norm_of_nonneg hn.le, norm_pow]
  have hden1 : n * c * |y| ≤ n * ‖p' y‖ := by
    nlinarith
  have hs : (c * |y|) ^ 2 ≤ ‖p' y‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hc.le (abs_nonneg y)) (norm_nonneg _)).2 hlower
  have hden2 : n * c ^ 2 * |y| ^ 2 ≤ n * ‖p' y‖ ^ 2 := by
    nlinarith
  have hy_sq : |y| ^ 2 ≤ |y| := by
    nlinarith [abs_nonneg y]
  have h1 : ‖f' y‖ / (n * ‖p' y‖) ≤ C / (n * c * |y| ^ 2) :=
    (div_le_div₀ hC hfp (by positivity) hden1).trans
      (div_le_div_of_nonneg_left hC (by positivity) (by gcongr))
  have h2 : ‖f y‖ * ‖p'' y‖ / (n * ‖p' y‖ ^ 2) ≤ C ^ 2 / (n * c ^ 2 * |y| ^ 2) :=
    div_le_div₀ (sq_nonneg C) ((mul_le_mul hf hpp (norm_nonneg _) hC).trans_eq (sq C).symm)
      (by positivity) hden2
  calc
    _ ≤ C / (n * c * |y| ^ 2) + C ^ 2 / (n * c ^ 2 * |y| ^ 2) :=
      add_le_add h1 h2
    _ = ((C / c + C ^ 2 / c ^ 2) / n) * (y ^ 2)⁻¹ := by
      rw [sq_abs]
      field_simp

/-- A boundary term in phase integration by parts is bounded by
`C / (n c |y|)`. -/
theorem norm_phase_boundary_le
    {f p p' : ℝ → ℂ} {n c C y : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hy : 0 < |y|) (hC : 0 ≤ C)
    (hf : ‖f y‖ ≤ C) (hp : (p y).re ≤ 0)
    (hlower : c * |y| ≤ ‖p' y‖) :
    ‖f y / ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y)‖ ≤
      C / (n * c * |y|) := by
  calc
    _ ≤ ‖f y / ((n : ℂ) * p' y)‖ :=
      norm_mul_exp_le_norm_of_re_nonpos (re_ofReal_mul_nonpos hn.le hp)
    _ = ‖f y‖ / (n * ‖p' y‖) := by
      simp only [norm_div, norm_mul, norm_real, Real.norm_of_nonneg hn.le]
    _ ≤ C / (n * c * |y|) :=
      div_le_div₀ hC hf (by positivity) (by nlinarith)

/-- The boundary-term estimate, weakened to a lower bound `η ≤ |y|`. -/
theorem norm_phase_boundary_le_of_le
    {f p p' : ℝ → ℂ} {n c C η y : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hη : 0 < η) (hηy : η ≤ |y|) (hC : 0 ≤ C)
    (hf : ‖f y‖ ≤ C) (hp : (p y).re ≤ 0)
    (hlower : c * |y| ≤ ‖p' y‖) :
    ‖f y / ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y)‖ ≤ C / (n * c * η) :=
  (norm_phase_boundary_le hn hc (hη.trans_le hηy) hC hf hp hlower).trans
    (div_le_div_of_nonneg_left hC (by positivity) (by gcongr))

/-- The pointwise integrand bound for the remainder in phase integration by parts. -/
theorem norm_tailQuotientDeriv_mul_exp_le
    {f f' p p' p'' : ℝ → ℂ} {n c C y : ℝ}
    (hn : 0 < n) (hc : 0 < c)
    (hy : 0 < |y|) (hy1 : |y| ≤ 1) (hC : 0 ≤ C) (hp : (p y).re ≤ 0)
    (hf : ‖f y‖ ≤ C) (hfp : ‖f' y‖ ≤ C)
    (hpp : ‖p'' y‖ ≤ C)
    (hlower : c * |y| ≤ ‖p' y‖) :
    ‖tailQuotientDeriv f f' p' p'' n y * Complex.exp ((n : ℂ) * p y)‖ ≤
      ((C / c + C ^ 2 / c ^ 2) / n) * (y ^ 2)⁻¹ :=
  (norm_mul_exp_le_norm_of_re_nonpos (re_ofReal_mul_nonpos hn.le hp)).trans
    (norm_tailQuotientDeriv_le hn hc hy hy1 hC hf hfp hpp hlower)

/-- Exact interval integration by parts for a complex phase whose derivative does not vanish. -/
theorem interval_phase_integration_by_parts
    {f f' p p' p'' : ℝ → ℂ} {a b n : ℝ}
    (hn : 0 < n)
    (hf : ∀ y ∈ Set.uIcc a b, HasDerivAt f (f' y) y)
    (hp : ∀ y ∈ Set.uIcc a b, HasDerivAt p (p' y) y)
    (hpp : ∀ y ∈ Set.uIcc a b, HasDerivAt p' (p'' y) y)
    (hp_ne : ∀ y ∈ Set.uIcc a b, p' y ≠ 0)
    (hu' : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n) volume a b)
    (hv' : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y)) volume a b) :
    (∫ y in a..b, f y * Complex.exp ((n : ℂ) * p y)) =
      f b / ((n : ℂ) * p' b) * Complex.exp ((n : ℂ) * p b) -
      f a / ((n : ℂ) * p' a) * Complex.exp ((n : ℂ) * p a) -
      ∫ y in a..b,
        tailQuotientDeriv f f' p' p'' n y * Complex.exp ((n : ℂ) * p y) := by
  let u : ℝ → ℂ := fun y => f y / ((n : ℂ) * p' y)
  let v : ℝ → ℂ := fun y => Complex.exp ((n : ℂ) * p y)
  have hu : ∀ y ∈ Set.uIcc a b,
      HasDerivAt u (tailQuotientDeriv f f' p' p'' n y) y := by
    intro y hy
    dsimp only [u, tailQuotientDeriv]
    exact (hf y hy).div (HasDerivAt.const_mul (n : ℂ) (hpp y hy))
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne') (hp_ne y hy))
  have hv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt v (((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y)) y := by
    intro y hy
    dsimp only [v]
    rw [mul_comm]
    exact (HasDerivAt.const_mul (n : ℂ) (hp y hy)).cexp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have heq :
      (∫ y in a..b, u y * (((n : ℂ) * p' y) * v y)) =
        ∫ y in a..b, f y * v y := by
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only [u]
    rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne')
      (hp_ne y hy))]
    ring
  rw [heq] at hibp
  simpa only [u, v] using hibp

/-- Nonstationary phase on the positive tail.  The three copies of `C / c`
in the constant are the two endpoint terms and the first differentiated
quotient term. -/
theorem norm_phase_tail_pos_le
    {f f' p p' p'' : ℝ → ℂ} {η n c C : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < n) (hc : 0 < c) (hC : 0 ≤ C)
    (hf_deriv : ∀ y ∈ Set.uIcc η 1, HasDerivAt f (f' y) y)
    (hp_deriv : ∀ y ∈ Set.uIcc η 1, HasDerivAt p (p' y) y)
    (hpp_deriv : ∀ y ∈ Set.uIcc η 1, HasDerivAt p' (p'' y) y)
    (hp_re : ∀ y ∈ Set.uIcc η 1, (p y).re ≤ 0)
    (hf : ∀ y ∈ Set.uIcc η 1, ‖f y‖ ≤ C)
    (hfp : ∀ y ∈ Set.uIcc η 1, ‖f' y‖ ≤ C)
    (hpp : ∀ y ∈ Set.uIcc η 1, ‖p'' y‖ ≤ C)
    (hlower : ∀ y ∈ Set.uIcc η 1, c * |y| ≤ ‖p' y‖)
    (hu' : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n) volume η 1)
    (hv' : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y)) volume η 1) :
    ‖∫ y in η..1, f y * Complex.exp ((n : ℂ) * p y)‖ ≤
      (3 * C / c + C ^ 2 / c ^ 2) / (n * η) := by
  have hp_ne : ∀ y ∈ Set.uIcc η 1, p' y ≠ 0 := fun y hy =>
    ne_zero_of_mul_abs_le_norm hc
      (abs_pos.mpr (hη.trans_le ((Set.uIcc_of_le hη1).subset hy).1).ne') (hlower y hy)
  have hrem :
      ‖∫ y in η..1,
          tailQuotientDeriv f f' p' p'' n y * Complex.exp ((n : ℂ) * p y)‖ ≤
        (C / c + C ^ 2 / c ^ 2) / (n * η) := by
    refine norm_tail_integral_le hη hη1 hn (by positivity) fun y hy => ?_
    have hyu : y ∈ Set.uIcc η 1 := Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self hy)
    have hy0 : 0 < y := hη.trans hy.1
    exact norm_tailQuotientDeriv_mul_exp_le hn hc (abs_pos.mpr hy0.ne')
      ((abs_of_pos hy0).le.trans hy.2) hC (hp_re y hyu) (hf y hyu) (hfp y hyu)
      (hpp y hyu) (hlower y hyu)
  have hηmem : η ∈ Set.uIcc η 1 := Set.left_mem_uIcc
  have h1mem : (1 : ℝ) ∈ Set.uIcc η 1 := Set.right_mem_uIcc
  rw [interval_phase_integration_by_parts hn hf_deriv hp_deriv hpp_deriv hp_ne hu' hv']
  refine (norm_sub_le_of_le (norm_sub_le_of_le
    (norm_phase_boundary_le_of_le hn hc hη (by simpa using hη1) hC
      (hf 1 h1mem) (hp_re 1 h1mem) (hlower 1 h1mem))
    (norm_phase_boundary_le_of_le hn hc hη (le_abs_self η) hC
      (hf η hηmem) (hp_re η hηmem) (hlower η hηmem))) hrem).trans_eq ?_
  field_simp
  ring

/-- The reflected nonstationary-phase estimate on the negative tail. -/
theorem norm_phase_tail_neg_le
    {f f' p p' p'' : ℝ → ℂ} {η n c C : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < n) (hc : 0 < c) (hC : 0 ≤ C)
    (hf_deriv : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), HasDerivAt f (f' y) y)
    (hp_deriv : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), HasDerivAt p (p' y) y)
    (hpp_deriv : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), HasDerivAt p' (p'' y) y)
    (hp_re : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), (p y).re ≤ 0)
    (hf : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), ‖f y‖ ≤ C)
    (hfp : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), ‖f' y‖ ≤ C)
    (hpp : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), ‖p'' y‖ ≤ C)
    (hlower : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), c * |y| ≤ ‖p' y‖)
    (hu' : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n)
      volume (-1) (-η))
    (hv' : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y))
      volume (-1) (-η)) :
    ‖∫ y in (-1 : ℝ)..(-η), f y * Complex.exp ((n : ℂ) * p y)‖ ≤
      (3 * C / c + C ^ 2 / c ^ 2) / (n * η) := by
  have hab : (-1 : ℝ) ≤ -η := neg_le_neg hη1
  have hp_ne : ∀ y ∈ Set.uIcc (-1 : ℝ) (-η), p' y ≠ 0 := fun y hy =>
    ne_zero_of_mul_abs_le_norm hc
      (abs_pos.mpr (((Set.uIcc_of_le hab).subset hy).2.trans_lt (neg_lt_zero.mpr hη)).ne)
      (hlower y hy)
  have hrem :
      ‖∫ y in (-1 : ℝ)..(-η),
          tailQuotientDeriv f f' p' p'' n y * Complex.exp ((n : ℂ) * p y)‖ ≤
        (C / c + C ^ 2 / c ^ 2) / (n * η) := by
    refine norm_tail_integral_neg_le hη hη1 hn (by positivity) fun y hy => ?_
    have hyu : y ∈ Set.uIcc (-1 : ℝ) (-η) := Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self hy)
    have hyneg : y < 0 := hy.2.trans_lt (neg_lt_zero.mpr hη)
    exact norm_tailQuotientDeriv_mul_exp_le hn hc (abs_pos.mpr hyneg.ne)
      ((abs_of_neg hyneg).le.trans (by linarith [hy.1])) hC (hp_re y hyu) (hf y hyu)
      (hfp y hyu) (hpp y hyu) (hlower y hyu)
  have hηmem : -η ∈ Set.uIcc (-1 : ℝ) (-η) := Set.right_mem_uIcc
  have h1mem : (-1 : ℝ) ∈ Set.uIcc (-1 : ℝ) (-η) := Set.left_mem_uIcc
  rw [interval_phase_integration_by_parts hn hf_deriv hp_deriv hpp_deriv hp_ne hu' hv']
  refine (norm_sub_le_of_le (norm_sub_le_of_le
    (norm_phase_boundary_le_of_le hn hc hη ((le_abs_self η).trans_eq (abs_neg η).symm) hC
      (hf (-η) hηmem) (hp_re (-η) hηmem) (hlower (-η) hηmem))
    (norm_phase_boundary_le_of_le hn hc hη (by simpa using hη1) hC
      (hf (-1) h1mem) (hp_re (-1) h1mem) (hlower (-1) h1mem))) hrem).trans_eq ?_
  field_simp
  ring

/-- One-sided bounds on the integrals of `g` over `[-1, -η]` and `[η, 1]` bound the integral of
`g` over `[-1, 1]` minus its integral over `[-η, η]` by their sum. -/
theorem norm_phase_tail_le_of_one_sided
    {g : ℝ → ℂ} {η n c C : ℝ}
    (hi_neg : IntervalIntegrable g volume (-1 : ℝ) (-η))
    (hi_mid : IntervalIntegrable g volume (-η) η)
    (hi_pos : IntervalIntegrable g volume η 1)
    (hneg : ‖∫ y in (-1 : ℝ)..(-η), g y‖ ≤ (3 * C / c + C ^ 2 / c ^ 2) / (n * η))
    (hpos : ‖∫ y in η..1, g y‖ ≤ (3 * C / c + C ^ 2 / c ^ 2) / (n * η)) :
    ‖(∫ y in (-1 : ℝ)..1, g y) - ∫ y in (-η)..η, g y‖ ≤
      (6 * C / c + 2 * C ^ 2 / c ^ 2) / (n * η) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi_neg.trans hi_mid) hi_pos,
    ← intervalIntegral.integral_add_adjacent_intervals hi_neg hi_mid, add_sub_right_comm,
    add_sub_cancel_right]
  exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

/-- The explicit nonstationary-phase hypotheses imply the phase-tail
hypothesis used by `uniform_complex_gaussian_estimate_of_tail_estimates`. -/
theorem phase_tail_at_gaussianCutoff
    {f f' p p' p'' : ℝ → ℂ} {n c C : ℝ}
    (hn : 1 ≤ n) (hc : 0 < c) (hC : 0 ≤ C)
    (hf_deriv_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      HasDerivAt f (f' y) y)
    (hp_deriv_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      HasDerivAt p (p' y) y)
    (hpp_deriv_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      HasDerivAt p' (p'' y) y)
    (hp_re_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), (p y).re ≤ 0)
    (hf_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), ‖f y‖ ≤ C)
    (hfp_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), ‖f' y‖ ≤ C)
    (hpp_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)), ‖p'' y‖ ≤ C)
    (hlower_neg : ∀ y ∈ Set.uIcc (-1 : ℝ) (-(gaussianCutoff n)),
      c * |y| ≤ ‖p' y‖)
    (hu_neg : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n)
      volume (-1) (-(gaussianCutoff n)))
    (hv_neg : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y))
      volume (-1) (-(gaussianCutoff n)))
    (hf_deriv_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1,
      HasDerivAt f (f' y) y)
    (hp_deriv_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1,
      HasDerivAt p (p' y) y)
    (hpp_deriv_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1,
      HasDerivAt p' (p'' y) y)
    (hp_re_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, (p y).re ≤ 0)
    (hf_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, ‖f y‖ ≤ C)
    (hfp_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, ‖f' y‖ ≤ C)
    (hpp_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, ‖p'' y‖ ≤ C)
    (hlower_pos : ∀ y ∈ Set.uIcc (gaussianCutoff n) 1, c * |y| ≤ ‖p' y‖)
    (hu_pos : IntervalIntegrable (tailQuotientDeriv f f' p' p'' n)
      volume (gaussianCutoff n) 1)
    (hv_pos : IntervalIntegrable
      (fun y => ((n : ℂ) * p' y) * Complex.exp ((n : ℂ) * p y))
      volume (gaussianCutoff n) 1)
    (hi_neg : IntervalIntegrable
      (fun y => f y * Complex.exp ((n : ℂ) * p y))
      volume (-1) (-(gaussianCutoff n)))
    (hi_mid : IntervalIntegrable
      (fun y => f y * Complex.exp ((n : ℂ) * p y))
      volume (-(gaussianCutoff n)) (gaussianCutoff n))
    (hi_pos : IntervalIntegrable
      (fun y => f y * Complex.exp ((n : ℂ) * p y))
      volume (gaussianCutoff n) 1) :
    ‖(∫ y in (-1 : ℝ)..1, f y * Complex.exp ((n : ℂ) * p y)) -
        ∫ y in (-(gaussianCutoff n))..(gaussianCutoff n),
          f y * Complex.exp ((n : ℂ) * p y)‖ ≤
      (6 * C / c + 2 * C ^ 2 / c ^ 2) * n ^ (-(3 : ℝ) / 5) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hη : 0 < gaussianCutoff n := gaussianCutoff_pos hn0
  have hη1 : gaussianCutoff n ≤ 1 := gaussianCutoff_le_one hn
  have hneg := norm_phase_tail_neg_le hη hη1 hn0 hc hC
    hf_deriv_neg hp_deriv_neg hpp_deriv_neg hp_re_neg hf_neg hfp_neg hpp_neg
    hlower_neg hu_neg hv_neg
  have hpos := norm_phase_tail_pos_le hη hη1 hn0 hc hC
    hf_deriv_pos hp_deriv_pos hpp_deriv_pos hp_re_pos hf_pos hfp_pos hpp_pos
    hlower_pos hu_pos hv_pos
  have h := norm_phase_tail_le_of_one_sided hi_neg hi_mid hi_pos hneg hpos
  rwa [div_eq_mul_inv, inv_scale_mul_cutoff hn0] at h

end Gaussian

end RiemannJensen
