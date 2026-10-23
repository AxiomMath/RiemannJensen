module

public import RiemannJensen.Analysis.SaddleCosineComparison
public import RiemannJensen.Analysis.AmplitudeGlobal
public import RiemannJensen.Analysis.LocalWindowGeometry

/-!
# The zeta half-plane on the counting window

On the local arc around the saddle point, the contour `contourW d q` stays in the half-plane
`4 ≤ re (1 / 2 + w)`, for every `q` in the counting window.

## Main results

* `pi_mul_scaleT_div_le_scaleT_mul_saddleRadius_mul_cos`: the lower bound `π T / (16 q)` for the
  saddle real-part scale.
* `contourW_local_zeta_domain_of_q_le`: for `q ≤ c₀ T` with `c₀ ≤ π / 112`, the local arc lies in
  the half-plane `4 ≤ re (1 / 2 + w)`.
* `countingWindow_local_zeta_domain`: the same conclusion on the normalized local interval, for
  every `q` in the counting window.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The saddle real-part scale `T r(α) cos α` is at least `π T / (16 q)`. -/
theorem pi_mul_scaleT_div_le_scaleT_mul_saddleRadius_mul_cos
    (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    Real.pi * scaleT d / (16 * q) ≤
      scaleT d * saddleRadius d (saddleAngle d q) *
        Real.cos (saddleAngle d q) := by
  have hT := scaleT_pos d hd
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hr := saddleRadius_pos_of_mem_Icc d hd ⟨hα0.le, hαtop.le⟩
  have hp := one_le_saddleQ_mul_radius_sq d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hp
  have hq0 : 0 < q := by
    by_contra hn
    nlinarith [sq_nonneg (saddleRadius d (saddleAngle d q))]
  have hc := pi_mul_radius_div_sixteen_le_cos d hd hlarge hq
  rw [div_le_iff₀ (by positivity)]
  calc
    Real.pi * scaleT d ≤
        (scaleT d * saddleRadius d (saddleAngle d q) *
          (Real.pi * saddleRadius d (saddleAngle d q) / 16)) * (16 * q) := by
      nlinarith [mul_pos Real.pi_pos hT]
    _ ≤ (scaleT d * saddleRadius d (saddleAngle d q) *
          Real.cos (saddleAngle d q)) * (16 * q) := by
      gcongr

/-- If `q ≤ c₀ T` with `c₀ ≤ π/112`, then every point of the local arc `|t| ≤ cos α` satisfies
`4 ≤ re (1 / 2 + contourW d q (θ + t))`. -/
theorem contourW_local_zeta_domain_of_q_le
    (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q t c₀ : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d))
    (hcsmall : c₀ ≤ Real.pi / 112) (hqtop : q ≤ c₀ * scaleT d)
    (ht : |t| ≤ Real.cos (saddleAngle d q)) :
    4 ≤ (1 / 2 + contourW d q (saddleTheta d q + t)).re := by
  have hT := scaleT_pos d hd
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hr := saddleRadius_pos_of_mem_Icc d hd ⟨hα0.le, hαtop.le⟩
  have hp := one_le_saddleQ_mul_radius_sq d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hp
  have hq0 : 0 < q := by
    by_contra hn
    nlinarith [sq_nonneg (saddleRadius d (saddleAngle d q))]
  refine contourW_local_zeta_domain d q t (mul_nonneg hT.le hr.le) ht
    (le_trans ?_ (pi_mul_scaleT_div_le_scaleT_mul_saddleRadius_mul_cos d hd hlarge hq))
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- If `q ≤ c₀ T` with `c₀ ≤ π/112` and `0 ≤ ε ≤ 1`, then for every `y ∈ [-1, 1]` the point
`contourW d q (θ + localWidth ε d q * y)` satisfies `4 ≤ re (1 / 2 + w)`. -/
theorem contourW_normalized_local_zeta_domain
    (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q ε c₀ : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d))
    (hcsmall : c₀ ≤ Real.pi / 112) (hqtop : q ≤ c₀ * scaleT d) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + contourW d q
        (saddleTheta d q + localWidth ε d q * y)).re := by
  intro y hy
  apply contourW_local_zeta_domain_of_q_le d hd hlarge hq hcsmall hqtop
  have hmin0 := (min_angle_cos_pos_on_scale_window d hd hq).le
  have hm := min_le_right (saddleAngle d q) (Real.cos (saddleAngle d q))
  have hw0 : 0 ≤ localWidth ε d q := mul_nonneg hε0 hmin0
  rw [abs_mul, abs_of_nonneg hw0]
  nlinarith [mul_le_mul_of_nonneg_left (abs_le.2 hy) hw0,
    show localWidth ε d q ≤ Real.cos (saddleAngle d q) by
      rw [localWidth]
      nlinarith]

/-- For `0 ≤ ε ≤ 1`, `c₀ ≤ π / 112`, every `q` in `countingWindow M c₀ d` and every
`y ∈ [-1, 1]`, the point `contourW d q (θ + localWidth ε d q * y)`
satisfies `4 ≤ re (1 / 2 + w)`. -/
theorem countingWindow_local_zeta_domain
    (d : ℕ) (hd : 2 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {M c₀ ε q : ℝ} (hM : 0 < M)
    (hcsmall : c₀ ≤ Real.pi / 112) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq : q ∈ countingWindow M c₀ d) :
    ∀ y ∈ Icc (-1 : ℝ) 1,
      4 ≤ (1 / 2 + contourW d q
        (saddleTheta d q + localWidth ε d q * y)).re := by
  have hd1 : 1 ≤ d := by omega
  have hsqrt : 0 < Real.sqrt (Real.log d / d) :=
    Real.sqrt_pos.2 (div_pos (Real.log_pos (by exact_mod_cast hd)) (by positivity))
  have hT := scaleT_pos d hd1
  have hscale : q ∈ Ioc (edgeQ d) (scaleT d) :=
    ⟨by nlinarith [hq.1, mul_pos hM hsqrt], by nlinarith [hq.2, Real.pi_le_four]⟩
  exact contourW_normalized_local_zeta_domain d hd1 hlarge hscale hcsmall hq.2 hε0 hε1

end RiemannJensen
