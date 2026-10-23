module

public import RiemannJensen.Analysis.CirclePhaseBridge
public import RiemannJensen.Analysis.LocalWindowGeometry
public import RiemannJensen.Analysis.SaddleCosineComparison
public import RiemannJensen.Analysis.CountingAmplitude

/-!
# The remote phase gap

Outside the local window `(θ_q - ℓ_q, θ_q + ℓ_q)` of the closed lower saddle
semicircle, the real part of the phase drops below its saddle value by a
quantitative amount.  The global circle gap `Re h(u_q) - Re h(r² e^{-2iβ}) ≥
(3/2)(cos β - cos α)²` reduces this to a lower bound for `|cos β - cos α|`
when `|β - α| ≥ ℓ_q / 2`.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- The difference `cos (α - ℓ / 2) - cos α` as a product of sines. -/
theorem cos_sub_half_sub_cos (α ℓ : ℝ) :
    Real.cos (α - ℓ / 2) - Real.cos α = 2 * Real.sin (α - ℓ / 4) * Real.sin (ℓ / 4) := by
  rw [Real.cos_sub_cos, show (α - ℓ / 2 + α) / 2 = α - ℓ / 4 by ring,
    show (α - ℓ / 2 - α) / 2 = -(ℓ / 4) by ring, Real.sin_neg]
  ring

/-- The difference `cos α - cos (α + ℓ / 2)` as a product of sines. -/
theorem cos_sub_cos_add_half (α ℓ : ℝ) :
    Real.cos α - Real.cos (α + ℓ / 2) = 2 * Real.sin (α + ℓ / 4) * Real.sin (ℓ / 4) := by
  rw [Real.cos_sub_cos, show (α + (α + ℓ / 2)) / 2 = α + ℓ / 4 by ring,
    show (α - (α + ℓ / 2)) / 2 = -(ℓ / 4) by ring, Real.sin_neg]
  ring

/-- For `0 ≤ α ≤ 2π`, `sin α / 2 ≤ sin (α / 2)`. -/
theorem sin_div_two_le_sin_half {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 2 * Real.pi) :
    Real.sin α / 2 ≤ Real.sin (α / 2) := by
  have h2 : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    rw [← Real.sin_two_mul]
    ring_nf
  have hs0 : 0 ≤ Real.sin (α / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  nlinarith [Real.cos_le_one (α / 2)]

/-- A cosine separation estimate: if `β ∈ [0, π/2]` lies at distance at least
`ℓ / 2` from `α`, where `0 < ℓ ≤ α` and `ℓ ≤ π/2 - α`, then
`ℓ sin α / (2π) ≤ |cos β - cos α|`. -/
theorem cos_separation_of_far {α β ℓ : ℝ}
    (hα0 : 0 < α) (hℓ0 : 0 < ℓ) (hℓα : ℓ ≤ α)
    (hℓtop : ℓ ≤ Real.pi / 2 - α) (hβ : β ∈ Icc 0 (Real.pi / 2))
    (hfar : β ≤ α - ℓ / 2 ∨ α + ℓ / 2 ≤ β) :
    ℓ * Real.sin α / (2 * Real.pi) ≤ |Real.cos β - Real.cos α| := by
  have hpi := Real.pi_pos
  have hsinα0 : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0.le (by linarith)
  have hjordan : ℓ / (2 * Real.pi) ≤ Real.sin (ℓ / 4) := by
    have h := Real.mul_le_sin (x := ℓ / 4) (by positivity) (by linarith)
    have : 2 / Real.pi * (ℓ / 4) = ℓ / (2 * Real.pi) := by
      field_simp
      ring
    linarith
  have hjordan0 : 0 ≤ ℓ / (2 * Real.pi) := by positivity
  have hl0 : 0 ≤ ℓ * Real.sin α / (2 * Real.pi) := by positivity
  have hsplit : ℓ * Real.sin α / (2 * Real.pi) =
      2 * (Real.sin α / 2) * (ℓ / (2 * Real.pi)) := by ring
  rcases hfar with hle | hge
  · have hcos : Real.cos (α - ℓ / 2) ≤ Real.cos β :=
      Real.cos_le_cos_of_nonneg_of_le_pi hβ.1 (by linarith) hle
    have hdiff := cos_sub_half_sub_cos α ℓ
    have hhalf : Real.sin α / 2 ≤ Real.sin (α / 2) :=
      sin_div_two_le_sin_half hα0.le (by linarith)
    have hmono : Real.sin (α / 2) ≤ Real.sin (α - ℓ / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
        (by linarith)
    have hprod : ℓ * Real.sin α / (2 * Real.pi) ≤
        2 * Real.sin (α - ℓ / 4) * Real.sin (ℓ / 4) := by
      rw [hsplit]
      have hA : 0 ≤ Real.sin α / 2 := by linarith
      have := mul_le_mul (hhalf.trans hmono) hjordan hjordan0
        (hA.trans (hhalf.trans hmono))
      linarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hcos : Real.cos β ≤ Real.cos (α + ℓ / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hβ.2]) hge
    have hdiff := cos_sub_cos_add_half α ℓ
    have hmono : Real.sin α ≤ Real.sin (α + ℓ / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
        (by linarith)
    have hprod : ℓ * Real.sin α / (2 * Real.pi) ≤
        2 * Real.sin (α + ℓ / 4) * Real.sin (ℓ / 4) := by
      rw [hsplit]
      have := mul_le_mul (show Real.sin α / 2 ≤ Real.sin (α + ℓ / 4) by linarith) hjordan
        hjordan0 (by linarith)
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- On the scale window, with `ε ≤ 1`, the local width is at most the saddle angle. -/
theorem localWidth_le_saddleAngle (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hε1 : ε ≤ 1) :
    localWidth ε d q ≤ saddleAngle d q := by
  obtain ⟨hα0, hαtop, -⟩ := saddle_inverse_on_scale_window d hd hq
  have hcos0 : 0 < Real.cos (saddleAngle d q) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hαtop⟩
  rw [localWidth]
  have hm := min_le_left (saddleAngle d q) (Real.cos (saddleAngle d q))
  have hm0 : 0 ≤ min (saddleAngle d q) (Real.cos (saddleAngle d q)) :=
    le_min hα0.le hcos0.le
  nlinarith

/-- On the scale window, with `ε ≤ 1`, the local width is at most `π / 2 - α_q`. -/
theorem localWidth_le_pi_div_two_sub_saddleAngle (d : ℕ) (hd : 1 ≤ d) {q ε : ℝ}
    (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hε1 : ε ≤ 1) :
    localWidth ε d q ≤ Real.pi / 2 - saddleAngle d q := by
  obtain ⟨hα0, hαtop, -⟩ := saddle_inverse_on_scale_window d hd hq
  have hcos0 : 0 < Real.cos (saddleAngle d q) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hαtop⟩
  have hcosdist : Real.cos (saddleAngle d q) ≤ Real.pi / 2 - saddleAngle d q := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le (by linarith)
  rw [localWidth]
  have hm := min_le_right (saddleAngle d q) (Real.cos (saddleAngle d q))
  have hm0 : 0 ≤ min (saddleAngle d q) (Real.cos (saddleAngle d q)) :=
    le_min hα0.le hcos0.le
  nlinarith

/-- **Generic local-endpoint gap**. On the scale window, with `0 < ε ≤ 1`, every point
`θ ∈ [-π, 0]` outside the local window `(θ_q - ℓ_q, θ_q + ℓ_q)` satisfies
`Re h(u_q) - Re h(r² e^{iθ}) ≥ (3 / (8π²)) ε² min(α, cos α)² sin² α`. -/
theorem remote_phase_gap_generic
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hθout : θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
      (-2 * saddleAngle d q + localWidth ε d q)) :
    3 / (8 * Real.pi ^ 2) * ε ^ 2 *
        min (saddleAngle d q) (Real.cos (saddleAngle d q)) ^ 2 *
        Real.sin (saddleAngle d q) ^ 2 ≤
      (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re := by
  have hℓα := localWidth_le_saddleAngle d hd hq hε1
  have hℓtop := localWidth_le_pi_div_two_sub_saddleAngle d hd hq hε1
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  set α := saddleAngle d q with hαdef
  set ℓ := localWidth ε d q with hℓdef
  have hpi := Real.pi_pos
  have hℓ0 : 0 < ℓ := localWidth_pos_on_scale_window d hd hq hε0
  have hsin0 : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0.le (by linarith)
  set β := -θ / 2 with hβdef
  have hβ : β ∈ Icc 0 (Real.pi / 2) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hfar : β ≤ α - ℓ / 2 ∨ α + ℓ / 2 ≤ β := by
    by_contra hn
    push Not at hn
    exact hθout ⟨by linarith [hn.2], by linarith [hn.1]⟩
  have hsep := cos_separation_of_far hα0 hℓ0 hℓα hℓtop hβ hfar
  have hgap := phase_circle_quadratic_gap d hd hΛ ⟨hα0, hαtop.le⟩ hβ
  rw [hinv, show -2 * β = θ by linarith] at hgap
  rw [saddle_eq_lowerContourPoint, lowerContourPoint, lowerContourPoint]
  refine le_trans ?_ hgap
  have hsepsq : (ℓ * Real.sin α / (2 * Real.pi)) ^ 2 ≤
      (Real.cos β - Real.cos α) ^ 2 := by
    rw [← sq_abs (Real.cos β - Real.cos α)]
    exact pow_le_pow_left₀ (by positivity) hsep 2
  have hlhs : 3 / (8 * Real.pi ^ 2) * ε ^ 2 * min α (Real.cos α) ^ 2 *
      Real.sin α ^ 2 = 3 / 2 * (ℓ * Real.sin α / (2 * Real.pi)) ^ 2 := by
    rw [hℓdef, localWidth]
    field_simp
    ring
  rw [hlhs]
  linarith

/-- On the scale window the level is at least `1/4`. -/
theorem quarter_le_of_scale_window
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) :
    1 / 4 ≤ q := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hp := one_le_saddleQ_mul_radius_sq d hd
    (show saddleAngle d q ∈ Icc 0 (Real.pi / 2) from ⟨hα0.le, hαtop.le⟩)
  rw [hinv] at hp
  obtain ⟨hr, hr2⟩ := saddleRadius_pos_le_two_on_scale_window d hd hq
  have hq0 : 0 < q := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (sq_nonneg (saddleRadius d (saddleAngle d q)))
    linarith
  have hr4 : saddleRadius d (saddleAngle d q) ^ 2 ≤ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hr4 hq0.le]

/-- On the scale window with `1/2 ≤ α_q`, `π² / (256 q) ≤ min(α_q, cos α_q)²`. -/
theorem pi_sq_div_le_min_saddleAngle_cos_sq
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hαlarge : 1 / 2 ≤ saddleAngle d q) :
    Real.pi ^ 2 / (256 * q) ≤ min (saddleAngle d q) (Real.cos (saddleAngle d q)) ^ 2 := by
  set α := saddleAngle d q with hαdef
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hq4 := quarter_le_of_scale_window d hd hq
  have hq0 : 0 < q := by linarith
  have hlarge := four_mul_one_add_log_two_pi_le_of_scaleLambda hΛ
  have hcosr := pi_mul_radius_div_sixteen_le_cos d hd hlarge hq
  have hrq := inv_sqrt_le_saddleRadius_on_scale_window d hd hq
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsq2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hsqhalf : 1 / 2 ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by linarith)
  have hcosq : Real.pi / (16 * Real.sqrt q) ≤ Real.cos α := by
    rw [show Real.pi / (16 * Real.sqrt q) = Real.pi * (1 / Real.sqrt q) / 16 by field_simp]
    have := mul_le_mul_of_nonneg_left hrq hpi.le
    linarith
  have hαq : Real.pi / (16 * Real.sqrt q) ≤ α := by
    have : Real.pi / (16 * Real.sqrt q) ≤ Real.pi / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have h := pow_le_pow_left₀ (by positivity) (le_min hαq hcosq) 2
  have : (Real.pi / (16 * Real.sqrt q)) ^ 2 = Real.pi ^ 2 / (256 * q) := by
    rw [div_pow, mul_pow, hsq2]
    norm_num
  linarith

/-- **Large-angle remote gap**. On the scale window with `0 < ε ≤ 1` and `1/2 ≤ α_q`, every
`θ ∈ [-π, 0]` outside the local window satisfies
`Re h(u_q) - Re h(r² e^{iθ}) ≥ 3 ε² / (2048 π² q)`. -/
theorem remote_phase_gap_large_angle
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hαlarge : 1 / 2 ≤ saddleAngle d q)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hθout : θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
      (-2 * saddleAngle d q + localWidth ε d q)) :
    3 * ε ^ 2 / (2048 * Real.pi ^ 2 * q) ≤
      (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re := by
  have hgen := remote_phase_gap_generic d hd hΛ hq hε0 hε1 hθ hθout
  have hminsq := pi_sq_div_le_min_saddleAngle_cos_sq d hd hΛ hq hαlarge
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  set α := saddleAngle d q with hαdef
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hq0 : 0 < q := by linarith [quarter_le_of_scale_window d hd hq]
  have hsin : 1 / Real.pi ≤ Real.sin α := by
    have h := Real.mul_le_sin (x := 1 / 2) (by norm_num) (by linarith)
    have hm : Real.sin (1 / 2) ≤ Real.sin α :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hαtop.le hαlarge
    have : 2 / Real.pi * (1 / 2) = 1 / Real.pi := by field_simp
    linarith
  have hsinsq : 1 / Real.pi ^ 2 ≤ Real.sin α ^ 2 := by
    simpa [div_pow] using pow_le_pow_left₀ (by positivity) hsin 2
  have hc0 : 0 ≤ 3 / (8 * Real.pi ^ 2) * ε ^ 2 := by positivity
  have h1 := mul_le_mul hminsq hsinsq (by positivity) (sq_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left h1 hc0
  rw [show 3 * ε ^ 2 / (2048 * Real.pi ^ 2 * q) =
      3 / (8 * Real.pi ^ 2) * ε ^ 2 * (Real.pi ^ 2 / (256 * q) * (1 / Real.pi ^ 2)) by
    field_simp
    ring]
  linarith

/-- **Small-angle remote gap from an edge comparison.**  If `α_q < 1/2` and
`q - q_edge ≤ K α_q²` with `K > 0`, then outside the local window
`Re h(u_q) - Re h(r² e^{iθ}) ≥ 3 ε² (q - q_edge)² / (2 π⁴ K²)`. -/
theorem remote_phase_gap_small_angle
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε K : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 0 < K) (hαsmall : saddleAngle d q < 1 / 2)
    (hedge : q - edgeQ d ≤ K * saddleAngle d q ^ 2)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hθout : θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
      (-2 * saddleAngle d q + localWidth ε d q)) :
    3 * ε ^ 2 * (q - edgeQ d) ^ 2 / (2 * Real.pi ^ 4 * K ^ 2) ≤
      (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re := by
  have hgen := remote_phase_gap_generic d hd hΛ hq hε0 hε1 hθ hθout
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  set α := saddleAngle d q with hαdef
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hcos : α ≤ Real.cos α := by
    have h := Real.one_sub_sq_div_two_le_cos (x := α)
    nlinarith
  have hsin : 2 / Real.pi * α ≤ Real.sin α :=
    Real.mul_le_sin hα0.le hαtop.le
  have hsinsq : (2 / Real.pi * α) ^ 2 ≤ Real.sin α ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  have hqe0 : 0 < q - edgeQ d := by linarith [hq.1]
  have hedgesq : (q - edgeQ d) ^ 2 ≤ K ^ 2 * α ^ 4 := by
    have := pow_le_pow_left₀ hqe0.le hedge 2
    nlinarith
  have hα4 : (q - edgeQ d) ^ 2 / K ^ 2 ≤ α ^ 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [min_eq_left hcos] at hgen
  have hkey : 3 * ε ^ 2 * (q - edgeQ d) ^ 2 / (2 * Real.pi ^ 4 * K ^ 2) ≤
      3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2 * Real.sin α ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsinsq
      (by positivity : (0 : ℝ) ≤ 3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2)
    have h2 : 3 * ε ^ 2 * (q - edgeQ d) ^ 2 / (2 * Real.pi ^ 4 * K ^ 2) ≤
        3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2 * (2 / Real.pi * α) ^ 2 := by
      rw [show 3 / (8 * Real.pi ^ 2) * ε ^ 2 * α ^ 2 * (2 / Real.pi * α) ^ 2 =
          3 * ε ^ 2 / (2 * Real.pi ^ 4) * α ^ 4 by field_simp; ring,
        show 3 * ε ^ 2 * (q - edgeQ d) ^ 2 / (2 * Real.pi ^ 4 * K ^ 2) =
          3 * ε ^ 2 / (2 * Real.pi ^ 4) * ((q - edgeQ d) ^ 2 / K ^ 2) by field_simp]
      exact mul_le_mul_of_nonneg_left hα4 (by positivity)
    linarith
  linarith

/-- The remote-gap constant `3 / (2048 π⁴ max(K², 1))`. -/
noncomputable def remoteGapConst (K : ℝ) : ℝ :=
  3 / (2048 * Real.pi ^ 4 * max (K ^ 2) 1)

/-- The remote-gap constant `remoteGapConst K` is positive. -/
theorem remoteGapConst_pos (K : ℝ) : 0 < remoteGapConst K := by
  rw [remoteGapConst]
  have : 0 < max (K ^ 2) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have := Real.pi_pos
  positivity

/-- **Whole remote gap, conditional on the small-angle edge comparison**. Assume that whenever
`α_q < 1/2` one has `q - q_edge ≤ K α_q²` with `K > 0`. Then on the scale window, for
`0 < ε ≤ 1`, every `θ ∈ [-π, 0]` outside the local window satisfies
`Re h(u_q) - Re h(r² e^{iθ}) ≥ ε² c_K min((q - q_edge)², q⁻¹)`. -/
theorem remote_phase_gap_of_edge
    (d : ℕ) (hd : 1 ≤ d) (hΛ : 24 * Real.pi ≤ scaleLambda d)
    {q ε K : ℝ} (hq : q ∈ Ioc (edgeQ d) (scaleT d)) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 0 < K)
    (hedge : saddleAngle d q < 1 / 2 → q - edgeQ d ≤ K * saddleAngle d q ^ 2)
    {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) 0)
    (hθout : θ ∉ Ioo (-2 * saddleAngle d q - localWidth ε d q)
      (-2 * saddleAngle d q + localWidth ε d q)) :
    ε ^ 2 * remoteGapConst K * min ((q - edgeQ d) ^ 2) q⁻¹ ≤
      (phase d q (saddle d q)).re - (phase d q (lowerContourPoint d q θ)).re := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hM1 : 1 ≤ max (K ^ 2) 1 := le_max_right _ _
  have hMK : K ^ 2 ≤ max (K ^ 2) 1 := le_max_left _ _
  have hq0 : 0 < q := by linarith [quarter_le_of_scale_window d hd hq]
  have hε2 : 0 < ε ^ 2 := by positivity
  have hm0 : 0 ≤ min ((q - edgeQ d) ^ 2) q⁻¹ :=
    le_min (sq_nonneg _) (inv_nonneg.2 hq0.le)
  rcases lt_or_ge (saddleAngle d q) (1 / 2) with hsmall | hlarge
  · have h := remote_phase_gap_small_angle d hd hΛ hq hε0 hε1 hK hsmall
      (hedge hsmall) hθ hθout
    refine le_trans ?_ h
    have hm := min_le_left ((q - edgeQ d) ^ 2) q⁻¹
    have hc : remoteGapConst K ≤ 3 / (2 * Real.pi ^ 4 * K ^ 2) := by
      rw [remoteGapConst]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [pow_pos hpi 4]
    calc ε ^ 2 * remoteGapConst K * min ((q - edgeQ d) ^ 2) q⁻¹
        ≤ ε ^ 2 * (3 / (2 * Real.pi ^ 4 * K ^ 2)) * (q - edgeQ d) ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hc hε2.le) hm hm0
          positivity
      _ = _ := by field_simp
  · have h := remote_phase_gap_large_angle d hd hΛ hq hε0 hε1 hlarge hθ hθout
    refine le_trans ?_ h
    have hm := min_le_right ((q - edgeQ d) ^ 2) q⁻¹
    have hc : remoteGapConst K ≤ 3 / (2048 * Real.pi ^ 2) := by
      rw [remoteGapConst]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : Real.pi ^ 2 ≤ Real.pi ^ 4 * max (K ^ 2) 1 :=
        (pow_le_pow_right₀ (by linarith) (by norm_num)).trans
          (le_mul_of_one_le_right (by positivity) hM1)
      nlinarith
    calc ε ^ 2 * remoteGapConst K * min ((q - edgeQ d) ^ 2) q⁻¹
        ≤ ε ^ 2 * (3 / (2048 * Real.pi ^ 2)) * q⁻¹ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hc hε2.le) hm hm0
          positivity
      _ = _ := by field_simp

end RiemannJensen
