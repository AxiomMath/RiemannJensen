module

public import RiemannJensen.Analysis.SaddleComparisons
public import RiemannJensen.Analysis.CircleGap

/-!
# Comparing the saddle cosine and radius

For `q ∈ (edgeQ d, scaleT d]`, the cosine of the saddle angle `saddleAngle d q` is comparable to
the saddle radius at that angle, once `scaleLambda d` is large enough.

## Main results

* `saddleRadius_log_lower_on_scale_window`: the logarithm of the saddle radius is at least
  `-(3 * scaleLambda d / 8)`.
* `pi_mul_radius_div_sixteen_le_cos`: `π r / 16 ≤ cos α`, for `r` the saddle radius at `α`.
* `cos_le_pi_mul_radius_div_two`: `cos α ≤ π r / 2`.
-/

@[expose] public section

namespace RiemannJensen

/-- For `q ∈ (edgeQ d, scaleT d]` and `scaleLambda d ≥ 4 (1 + log (2π))`, the logarithm of the
saddle radius at `saddleAngle d q` is at least `-(3 scaleLambda d / 8)`. -/
theorem saddleRadius_log_lower_on_scale_window (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    -(3 * scaleLambda d / 8) ≤ Real.log (saddleRadius d (saddleAngle d q)) := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, hinv⟩
  have hr : 0 < saddleRadius d (saddleAngle d q) :=
    (saddleRadius_pos_and_eq d hd ⟨by linarith [Real.pi_pos], hαtop.le⟩).1
  have hT : 0 < scaleT d := lt_trans (by positivity) (scaleT_gt_base d hd)
  have hp := one_le_saddleQ_mul_radius_sq d hd ⟨hα0.le, hαtop.le⟩
  rw [hinv] at hp
  have hTr2 : 1 ≤ scaleT d * saddleRadius d (saddleAngle d q) ^ 2 := by
    nlinarith [hq.2, sq_nonneg (saddleRadius d (saddleAngle d q))]
  have hlogprod := Real.log_le_log one_pos hTr2
  rw [Real.log_one, Real.log_mul hT.ne' (pow_ne_zero 2 hr.ne'), Real.log_pow] at hlogprod
  have hcoord := scaleLambda_div_two d
  rw [Real.log_div hT.ne' (by positivity)] at hcoord
  push_cast at hlogprod
  nlinarith

/-- For `q ∈ (edgeQ d, scaleT d]` and `scaleLambda d ≥ 4 (1 + log (2π))`, the cosine of the
saddle angle is at least `π / 16` times the saddle radius. -/
theorem pi_mul_radius_div_sixteen_le_cos (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 4 * (1 + Real.log (2 * Real.pi)) ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    Real.pi * saddleRadius d (saddleAngle d q) / 16 ≤ Real.cos (saddleAngle d q) := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  have hαfull : saddleAngle d q ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hαtop.le⟩
  have hden : 0 < (Real.pi / 2) * saddleRadius d (saddleAngle d q) :=
    mul_pos (by positivity) (saddleRadius_pos_and_eq d hd hαfull).1
  have hlog := saddleRadius_log_lower_on_scale_window d hd hlarge hq
  have hcot := alphaCot_le_one_of_mem ⟨hα0.le, hαtop.le⟩
  have hchar := saddleRadius_characterization d hd hαfull
  have hterm : scaleLambda d / 8 ≤
      scaleLambda d * Real.cos (saddleAngle d q) /
        ((Real.pi / 2) * saddleRadius d (saddleAngle d q)) := by
    linarith
  nlinarith [mul_pos (scaleLambda_pos d hd) Real.pi_pos, (le_div_iff₀ hden).1 hterm]

/-- For `q ∈ (edgeQ d, scaleT d]` and `scaleLambda d ≥ 2 (1 + log 2)`, the cosine of the saddle
angle is at most `π / 2` times the saddle radius. -/
theorem cos_le_pi_mul_radius_div_two (d : ℕ) (hd : 1 ≤ d)
    (hlarge : 2 * (1 + Real.log 2) ≤ scaleLambda d)
    {q : ℝ} (hq : q ∈ Set.Ioc (edgeQ d) (scaleT d)) :
    Real.cos (saddleAngle d q) ≤ Real.pi * saddleRadius d (saddleAngle d q) / 2 := by
  rcases saddle_inverse_on_scale_window d hd hq with ⟨hα0, hαtop, -⟩
  have hαfull : saddleAngle d q ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hαtop.le⟩
  have hr := (saddleRadius_pos_and_eq d hd hαfull).1
  have hlog : Real.log (saddleRadius d (saddleAngle d q)) ≤ Real.log 2 :=
    Real.log_le_log hr (saddleRadius_le_two d hd ⟨hα0.le, hαtop.le⟩)
  have hcot0 : 0 ≤ alphaCot (saddleAngle d q) := by
    rw [alphaCot_of_ne hα0.ne']
    have hs : 0 < Real.sin (saddleAngle d q) :=
      Real.sin_pos_of_pos_of_lt_pi hα0 (hαtop.trans (by linarith [Real.pi_pos]))
    have hc : 0 ≤ Real.cos (saddleAngle d q) := Real.cos_nonneg_of_mem_Icc hαfull
    positivity
  have hchar := saddleRadius_characterization d hd hαfull
  have hterm :
      scaleLambda d * Real.cos (saddleAngle d q) /
          ((Real.pi / 2) * saddleRadius d (saddleAngle d q)) ≤
        scaleLambda d := by
    linarith
  have hden : 0 < (Real.pi / 2) * saddleRadius d (saddleAngle d q) := mul_pos (by positivity) hr
  nlinarith [mul_pos (scaleLambda_pos d hd) Real.pi_pos, (div_le_iff₀ hden).1 hterm]

end RiemannJensen
