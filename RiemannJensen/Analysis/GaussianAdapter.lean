module

public import RiemannJensen.Analysis.GaussianAssembly

/-!
# A smooth-hypothesis form of the uniform complex Gaussian estimate

The uniform estimate `uniform_complex_gaussian_estimate` is stated with its
pointwise and integrability hypotheses on the individual subintervals.  This
module derives all of them from `C³` control of the phase and `C¹` control of
the amplitude on `[-1, 1]`.
-/

@[expose] public section

namespace RiemannJensen

namespace Gaussian

open Complex Set MeasureTheory intervalIntegral

/-- The mean value inequality on the segment from `0` to `y`. -/
lemma norm_sub_zero_le_of_hasDerivAt {h h' : ℝ → ℂ} {y K : ℝ}
    (hd : ∀ t ∈ uIcc 0 y, HasDerivAt h (h' t) t)
    (hb : ∀ t ∈ uIcc 0 y, ‖h' t‖ ≤ K) :
    ‖h y - h 0‖ ≤ K * |y| := by
  simpa [Real.norm_eq_abs] using
    (convex_uIcc (0 : ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc

/-- If `y ∈ [-1, 1]`, then the segment between `0` and `y` lies in `[-1, 1]`. -/
lemma uIcc_zero_subset {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    uIcc 0 y ⊆ Icc (-1 : ℝ) 1 :=
  uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hy

/-- A point of the segment between `0` and `y` has absolute value at most `|y|`. -/
lemma abs_le_of_mem_uIcc_zero {y t : ℝ} (ht : t ∈ uIcc 0 y) : |t| ≤ |y| := by
  simpa using abs_sub_left_of_mem_uIcc ht

/-- The cubic Taylor bound for a phase with vanishing value and slope at the
origin, second derivative `-A` there, and third derivative bounded by `C`. -/
theorem norm_phase_sub_quadratic_le_of_C3
    {p p' p'' p''' : ℝ → ℂ} {A : ℂ} {C : ℝ}
    (hp : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p (p' y) y)
    (hp' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp0 : p 0 = 0) (hp'0 : p' 0 = 0) (hp''0 : p'' 0 = -A)
    (hp'''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ C)
    {y : ℝ} (hy : y ∈ Icc (-1:ℝ) 1) :
    ‖p y - (-A * ((y : ℂ) ^ 2) / 2)‖ ≤ C * |y| ^ 3 := by
  have hsub := uIcc_zero_subset hy
  have hC : 0 ≤ C := (norm_nonneg _).trans (hp'''_bd 0 ⟨by norm_num, by norm_num⟩)
  have h2 : ∀ t ∈ uIcc 0 y, ‖p'' t + A‖ ≤ C * |y| := by
    intro t ht
    have hts : uIcc 0 t ⊆ Icc (-1:ℝ) 1 := (uIcc_subset_uIcc_left ht).trans hsub
    have := norm_sub_zero_le_of_hasDerivAt (h := fun s => p'' s + A) (h' := p''')
      (y := t) (K := C) (fun s hs => (hp'' s (hts hs)).add_const A)
      (fun s hs => hp'''_bd s (hts hs))
    simp only [hp''0, neg_add_cancel, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (abs_le_of_mem_uIcc_zero ht) hC)
  have h1 : ∀ t ∈ uIcc 0 y, ‖p' t + A * (t : ℂ)‖ ≤ C * |y| * |y| := by
    intro t ht
    have hts : uIcc 0 t ⊆ uIcc 0 y := uIcc_subset_uIcc_left ht
    have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (p' + fun s : ℝ => A * (s : ℂ)) (p'' s + A) s :=
      fun s hs => ((hp' s (hsub (hts hs))).add
        ((hasDerivAt_id (s : ℂ)).const_mul A).comp_ofReal).congr_deriv (by simp)
    have := norm_sub_zero_le_of_hasDerivAt hd (fun s hs => h2 s (hts hs))
    simp only [Pi.add_apply, hp'0, Complex.ofReal_zero, mul_zero, add_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (abs_le_of_mem_uIcc_zero ht) (by positivity))
  have hd : ∀ s ∈ uIcc 0 y, HasDerivAt (p - fun s : ℝ => -A * ((s : ℂ) ^ 2) / 2)
      (p' s + A * (s : ℂ)) s := by
    intro s hs
    have hq : HasDerivAt (fun z : ℂ => -A * z ^ 2 / 2) (-A * (s : ℂ)) (s : ℂ) :=
      (((hasDerivAt_pow 2 (s : ℂ)).const_mul (-A)).div_const 2).congr_deriv (by push_cast; ring)
    exact ((hp s (hsub hs)).sub hq.comp_ofReal).congr_deriv (by ring)
  have := norm_sub_zero_le_of_hasDerivAt hd h1
  simp only [Pi.sub_apply, hp0, Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, sub_zero] at this
  exact this.trans_eq (by ring)

/-- The quotient derivative `tailQuotientDeriv` is continuous wherever its
ingredients are continuous and the phase derivative does not vanish. -/
theorem continuousOn_tailQuotientDeriv {f f' p' p'' : ℝ → ℂ} {n : ℝ} {s : Set ℝ}
    (hn : n ≠ 0) (hf : ContinuousOn f s) (hf' : ContinuousOn f' s)
    (hp' : ContinuousOn p' s) (hp'' : ContinuousOn p'' s) (hne : ∀ y ∈ s, p' y ≠ 0) :
    ContinuousOn (tailQuotientDeriv f f' p' p'' n) s := by
  unfold tailQuotientDeriv
  exact ((hf'.mul (continuousOn_const.mul hp')).sub (hf.mul (continuousOn_const.mul hp''))).div
    ((continuousOn_const.mul hp').pow 2) fun y hy =>
      pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr hn) (hne y hy))

/-- The uniform complex Gaussian estimate for a `C¹` amplitude and a `C³`
phase on `[-1, 1]`. -/
theorem gaussian_estimate_of_C3_C1
    {f f' p p' p'' p''' : ℝ → ℂ} {A : ℂ} {n c C : ℝ}
    (hn : 1 ≤ n) (hc : 0 < c) (hC : 0 ≤ C) (hA_norm : ‖A‖ = 1) (hA_re : 0 < A.re)
    (hf : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt f (f' y) y)
    (hf'_cont : ContinuousOn f' (Icc (-1:ℝ) 1))
    (hp : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p (p' y) y)
    (hp' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p' (p'' y) y)
    (hp'' : ∀ y ∈ Icc (-1:ℝ) 1, HasDerivAt p'' (p''' y) y)
    (hp0 : p 0 = 0) (hp'0 : p' 0 = 0) (hp''0 : p'' 0 = -A)
    (hre : ∀ y ∈ Icc (-1:ℝ) 1, (p y).re ≤ 0)
    (hlower : ∀ y ∈ Icc (-1:ℝ) 1, c * |y| ≤ ‖p' y‖)
    (hf_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖f y‖ ≤ C)
    (hf'_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖f' y‖ ≤ C)
    (hp''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p'' y‖ ≤ C)
    (hp'''_bd : ∀ y ∈ Icc (-1:ℝ) 1, ‖p''' y‖ ≤ C) :
    ‖(∫ y in (-1:ℝ)..1, f y * Complex.exp ((n:ℂ) * p y)) -
        f 0 * (((Real.pi:ℂ) / (((n/2:ℝ):ℂ) * A)) ^ (1/2:ℂ))‖ ≤
      (2 * C ^ 2 + 6 * C + 6 * C / c + 2 * C ^ 2 / c ^ 2) * n ^ (-(3:ℝ)/5) := by
  set η := gaussianCutoff n
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hη : 0 < η := gaussianCutoff_pos hn0
  have hη1 : η ≤ 1 := gaussianCutoff_le_one hn
  have hmid : uIcc (-η) η ⊆ Icc (-1:ℝ) 1 :=
    uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, hη1⟩
  have hmid' : uIoc (-η) η ⊆ Icc (-1:ℝ) 1 := uIoc_subset_uIcc.trans hmid
  have hneg : uIcc (-1:ℝ) (-η) ⊆ Icc (-1:ℝ) 1 :=
    uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ ⟨by linarith, by linarith⟩
  have hpos : uIcc η 1 ⊆ Icc (-1:ℝ) 1 :=
    uIcc_subset_Icc ⟨by linarith, hη1⟩ ⟨by norm_num, le_rfl⟩
  have hfc : ContinuousOn f (Icc (-1:ℝ) 1) := HasDerivAt.continuousOn hf
  have hpc : ContinuousOn p (Icc (-1:ℝ) 1) := HasDerivAt.continuousOn hp
  have hp'c : ContinuousOn p' (Icc (-1:ℝ) 1) := HasDerivAt.continuousOn hp'
  have hIc : ContinuousOn (fun y => f y * Complex.exp ((n:ℂ) * p y)) (Icc (-1:ℝ) 1) :=
    hfc.mul ((continuousOn_const.mul hpc).cexp)
  have hVc : ContinuousOn (fun y => ((n:ℂ) * p' y) * Complex.exp ((n:ℂ) * p y))
      (Icc (-1:ℝ) 1) :=
    (continuousOn_const.mul hp'c).mul ((continuousOn_const.mul hpc).cexp)
  have hp'ne : ∀ y ∈ Icc (-1:ℝ) 1, η ≤ |y| → p' y ≠ 0 := by
    intro y hy hyη h
    have := hlower y hy
    rw [h, norm_zero] at this
    nlinarith [mul_pos hc hη]
  have hUc : ∀ s ⊆ Icc (-1:ℝ) 1, (∀ y ∈ s, η ≤ |y|) →
      ContinuousOn (tailQuotientDeriv f f' p' p'' n) s := fun s hs hsη =>
    continuousOn_tailQuotientDeriv hn0.ne' (hfc.mono hs) (hf'_cont.mono hs) (hp'c.mono hs)
      ((HasDerivAt.continuousOn hp'').mono hs) fun y hy => hp'ne y (hs hy) (hsη y hy)
  have hnegη : ∀ y ∈ uIcc (-1:ℝ) (-η), η ≤ |y| := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    exact le_abs.mpr (Or.inr (by linarith [hy.2]))
  have hposη : ∀ y ∈ uIcc η 1, η ≤ |y| := by
    intro y hy
    rw [uIcc_of_le hη1] at hy
    exact hy.1.trans (le_abs_self y)
  apply uniform_complex_gaussian_estimate (f' := f') (p' := p') (p'' := p'')
    hn hc hC hA_norm hA_re
  · exact fun y hy => hre y (hmid' hy)
  · intro y _
    rw [show (-A * ((y:ℂ) ^ 2) / 2) = ((-(y ^ 2 / 2) : ℝ) : ℂ) * A by push_cast; ring,
      Complex.re_ofReal_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg y]) hA_re.le
  · exact fun y hy => norm_phase_sub_quadratic_le_of_C3 hp hp' hp'' hp0 hp'0 hp''0
      hp'''_bd (hmid' hy)
  · exact fun y hy => hf_bd y (hmid' hy)
  · intro y hy
    have hy' := hmid' hy
    exact norm_sub_zero_le_of_hasDerivAt (fun t ht => hf t (uIcc_zero_subset hy' ht))
      (fun t ht => hf'_bd t (uIcc_zero_subset hy' ht))
  · exact (hIc.mono hmid).intervalIntegrable
  · exact (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  · exact hf_bd 0 ⟨by norm_num, by norm_num⟩
  any_goals exact fun y hy => by solve_by_elim [hneg hy]
  · exact (hUc _ hneg hnegη).intervalIntegrable
  · exact (hVc.mono hneg).intervalIntegrable
  · exact (hUc _ hpos hposη).intervalIntegrable
  · exact (hVc.mono hpos).intervalIntegrable
  · exact (hIc.mono hneg).intervalIntegrable
  · exact (hIc.mono hpos).intervalIntegrable

/-- The modulus of the Gaussian main term. -/
theorem norm_gaussian_main_term {A : ℂ} {n : ℝ} (hn : 0 < n) (hA_norm : ‖A‖ = 1)
    (_hA_re : 0 < A.re) :
    ‖((Real.pi:ℂ) / (((n/2:ℝ):ℂ) * A)) ^ (1/2:ℂ)‖ = Real.sqrt (2 * Real.pi / n) := by
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real, Real.sqrt_eq_rpow,
    norm_div, norm_mul, hA_norm, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (by positivity)]
  congr 1
  field_simp

end Gaussian

end RiemannJensen
