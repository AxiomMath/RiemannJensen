module

public import RiemannJensen.Dedekind.SaddleInverseAction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Bounds on the Dedekind saddle action -/

@[expose] public section

namespace RiemannJensen

noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem dedekind_sin_sub_self_mul_cos_le_cube {α : ℝ} (hα : 0 ≤ α) :
    Real.sin α - α * Real.cos α ≤ α ^ 3 / 2 := by
  have hs := Real.sin_le hα
  have hc := Real.one_sub_sq_div_two_le_cos (x := α)
  nlinarith [mul_nonneg hα (sub_nonneg.mpr hc)]

private theorem dedekind_two_mul_sub_sin_two_mul_le_cube {α : ℝ} (hα : 0 ≤ α) :
    2 * α - Real.sin (2 * α) ≤ (4 / 3 : ℝ) * α ^ 3 := by
  rcases hα.eq_or_lt with rfl | ha
  · norm_num
  · nlinarith [Real.sin_gt_sub_cube (x := 2 * α) (by positivity)]

/-- If `0 ≤ α` and `0 ≤ c ≤ 1 / 6`, then
`2α - sin 2α + c (sin α - α cos α) ≤ (3 / 2) α ^ 3`. -/
theorem two_mul_sub_sin_add_mul_le_three_halves_cube {α c : ℝ} (hα : 0 ≤ α)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 6) :
    2 * α - Real.sin (2 * α) + c * (Real.sin α - α * Real.cos α) ≤
      (3 / 2 : ℝ) * α ^ 3 := by
  have h₁ := mul_le_mul_of_nonneg_left (dedekind_sin_sub_self_mul_cos_le_cube hα) hc0
  have h₂ := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ α ^ 3 / 2)
  linarith [pow_nonneg hα 3, dedekind_two_mul_sub_sin_two_mul_le_cube hα]

/-- If `24π ≤ dedekindScaleLambda K d`, then `π - 12√2 / √q` is at most the Dedekind saddle
action at every `q` in the scale window. -/
theorem dedekind_pi_sub_twelve_sqrt_two_div_sqrt_le_action
    (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindScaleT K d)) :
    Real.pi - 12 * Real.sqrt 2 / Real.sqrt q ≤
      dedekindSaddleAction K d q := by
  have hΛ2 : 2 * Real.pi ≤ dedekindScaleLambda K d := by linarith [Real.pi_pos]
  have hlarge2 : 2 * (1 + Real.log 2) ≤ dedekindScaleLambda K d := by
    linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2), Real.two_le_pi]
  have hrange := dedekindSaddle_inverse_range K d hd hq
  have hinv := dedekindSaddle_inverse K d hd hq
  have hα : dedekindSaddleAngle K d q ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨hrange.1.le, hrange.2.le⟩
  have hr : 0 < dedekindSaddleRadius K d (dedekindSaddleAngle K d q) :=
    dedekindSaddleRadius_pos K d hd hα
  have hrup : dedekindSaddleRadius K d (dedekindSaddleAngle K d q) ≤
      Real.sqrt 2 / Real.sqrt q := by
    have hc := (dedekindSaddleRadius_level_comparison K d hΛ2 hα).2
    rw [hinv] at hc
    exact hc
  have hcosup : Real.cos (dedekindSaddleAngle K d q) ≤
      Real.pi * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) / 2 := by
    simpa [dedekindSaddleRadius] using
      cos_le_pi_mul_saddleRadiusAtLambda_div_two hlarge2 hα
  have hcos0 : 0 ≤ Real.cos (dedekindSaddleAngle K d q) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hrange.1, Real.pi_pos], hrange.2.le⟩
  have hloss : Real.pi - 6 * Real.cos (dedekindSaddleAngle K d q) ≤
      2 * dedekindSaddleAngle K d q - Real.sin (2 * dedekindSaddleAngle K d q) := by
    have hj := Real.mul_le_sin (x := Real.pi / 2 - dedekindSaddleAngle K d q)
      (by linarith [hrange.2]) (by linarith [hrange.1])
    rw [Real.sin_pi_div_two_sub, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at hj
    rw [Real.sin_two_mul]
    nlinarith [Real.pi_div_two_le_two, Real.sin_le_one (dedekindSaddleAngle K d q)]
  have hcorr : 0 ≤ Real.sin (dedekindSaddleAngle K d q) -
      dedekindSaddleAngle K d q * Real.cos (dedekindSaddleAngle K d q) :=
    sub_nonneg.mpr (self_mul_cos_lt_sin hrange.1 hrange.2.le).le
  have hcoef : 0 ≤ 2 * Real.pi *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) /
      dedekindScaleLambda K d := div_nonneg (by positivity) (dedekindScaleLambda_pos K d hd).le
  have hmain : 2 * dedekindSaddleAngle K d q -
      Real.sin (2 * dedekindSaddleAngle K d q) ≤
      dedekindSaddleAction K d q := by
    rw [dedekindSaddle_action_formula K d hd hq]
    exact le_add_of_nonneg_right (mul_nonneg hcoef hcorr)
  rw [mul_div_assoc]
  linarith [mul_le_mul_of_nonneg_right Real.pi_div_two_le_two hr.le]

private theorem dedekindSaddleAngle_pos_of_edgeQ_lt (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindSaddleQ K d (Real.pi / 2))) :
    0 < dedekindSaddleAngle K d q := by
  obtain ⟨hα, hinv⟩ := dedekindSaddleQ_saddleAngle_of_mem K d hd ⟨hq.1.le, hq.2⟩
  refine hα.1.lt_of_ne fun hz => hq.1.ne ?_
  rw [dedekindEdgeQ, ← hinv, ← hz]

private theorem dedekindSaddle_action_formula_to_endpoint
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d)
      (dedekindSaddleQ K d (Real.pi / 2))) :
    dedekindSaddleAction K d q =
      2 * dedekindSaddleAngle K d q -
        Real.sin (2 * dedekindSaddleAngle K d q) +
      (2 * Real.pi * dedekindSaddleRadius K d (dedekindSaddleAngle K d q) /
          dedekindScaleLambda K d) *
        (Real.sin (dedekindSaddleAngle K d q) -
          dedekindSaddleAngle K d q * Real.cos (dedekindSaddleAngle K d q)) := by
  rcases dedekindSaddleQ_saddleAngle_of_mem K d hd ⟨hq.1.le, hq.2⟩ with
    ⟨hα, hinv⟩
  have hαpos := dedekindSaddleAngle_pos_of_edgeQ_lt K d hd hq
  let α := dedekindSaddleAngle K d q
  let r := dedekindSaddleRadius K d α
  have hr : 0 < r := dedekindSaddleRadius_pos K d hd hα
  have hΛ : dedekindScaleLambda K d ≠ 0 :=
    (dedekindScaleLambda_pos K d hd).ne'
  have hre := saddle_real_relation_atLambda (dedekindScaleLambda_pos K d hd) hα
  change Real.pi * r * (1 + 2 * Real.log r / dedekindScaleLambda K d) =
      2 * (dedekindSaddleQ K d α * r ^ 2 + 1) * Real.cos α -
        2 * Real.pi * r / dedekindScaleLambda K d at hre
  rw [show dedekindSaddleQ K d α = q by simpa [α] using hinv] at hre
  have hclosed := saddlePhaseAtLambda_im_eq_closed_action
    (dedekindScaleLambda K d) q r α hr hαpos.le hα.2 hΛ hre
  rw [dedekindSaddleAction, dedekindSaddle, dedekindSaddlePhase]
  convert hclosed using 1
  congr 3
  dsimp [α]
  push_cast
  ring_nf

/-- The Dedekind saddle action is nonnegative on
`(dedekindEdgeQ K d, dedekindSaddleQ K d (π / 2)]`. -/
theorem dedekindSaddleAction_nonneg (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindSaddleQ K d (Real.pi / 2))) :
    0 ≤ dedekindSaddleAction K d q := by
  obtain ⟨hα, -⟩ := dedekindSaddleQ_saddleAngle_of_mem K d hd ⟨hq.1.le, hq.2⟩
  have hαpos := dedekindSaddleAngle_pos_of_edgeQ_lt K d hd hq
  have hr := dedekindSaddleRadius_pos K d hd hα
  have hΛ := dedekindScaleLambda_pos K d hd
  have hbase : 0 ≤ 2 * dedekindSaddleAngle K d q -
      Real.sin (2 * dedekindSaddleAngle K d q) :=
    sub_nonneg.mpr (Real.sin_le (by linarith))
  have hcorr : 0 ≤ Real.sin (dedekindSaddleAngle K d q) -
      dedekindSaddleAngle K d q * Real.cos (dedekindSaddleAngle K d q) :=
    sub_nonneg.mpr (self_mul_cos_lt_sin hαpos hα.2).le
  rw [dedekindSaddle_action_formula_to_endpoint K d hd hq]
  positivity

/-- If `24π ≤ dedekindScaleLambda K d` and
`q ∈ (dedekindEdgeQ K d, dedekindSaddleQ K d (π / 2)]`, the Dedekind saddle action at `q` is
at most `3 / 2` times the cube of the saddle angle. -/
theorem dedekindSaddleAction_le_three_halves_cube (d : ℕ) (hd : 1 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d) {q : ℝ}
    (hq : q ∈ Set.Ioc (dedekindEdgeQ K d) (dedekindSaddleQ K d (Real.pi / 2))) :
    dedekindSaddleAction K d q ≤ (3 / 2 : ℝ) * dedekindSaddleAngle K d q ^ 3 := by
  obtain ⟨hα, -⟩ := dedekindSaddleQ_saddleAngle_of_mem K d hd ⟨hq.1.le, hq.2⟩
  have hr := dedekindSaddleRadius_pos K d hd hα
  have hr2 := dedekindSaddleRadius_le_two K d hd hα
  have hΛpos := dedekindScaleLambda_pos K d hd
  have hcoef : 2 * Real.pi *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) /
      dedekindScaleLambda K d ≤ 1 / 6 := by
    apply (div_le_iff₀ hΛpos).2
    nlinarith [Real.pi_pos]
  have hcoef0 : 0 ≤ 2 * Real.pi *
      dedekindSaddleRadius K d (dedekindSaddleAngle K d q) /
      dedekindScaleLambda K d := by positivity
  rw [dedekindSaddle_action_formula_to_endpoint K d hd hq]
  exact two_mul_sub_sin_add_mul_le_three_halves_cube hα.1 hcoef0 hcoef

private theorem dedekindSaddleAction_eq_zero_above_endpoint
    (d : ℕ) (hd : 1 ≤ d) {q : ℝ}
    (hq : dedekindSaddleQ K d (Real.pi / 2) < q) :
    dedekindSaddleAction K d q = 0 := by
  have hset : {α : ℝ | 0 ≤ α ∧ α ≤ Real.pi / 2 ∧
      q ≤ dedekindSaddleQ K d α} = ∅ := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hα0, hαtop, hqα⟩
    have hmono := (dedekindSaddleQ_strictMonoOn K d hd).monotoneOn
      (show α ∈ Set.Icc 0 (Real.pi / 2) from ⟨hα0, hαtop⟩)
      (show Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) from ⟨by positivity, le_rfl⟩)
      hαtop
    linarith
  have hang : dedekindSaddleAngle K d q = 0 := by
    simp [dedekindSaddleAngle, hset]
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hr := dedekindSaddleRadius_pos K d hd h0
  have hraw := saddlePhaseAtLambda_im_sq_exp_neg_two_mul_I
    (dedekindScaleLambda K d) q (dedekindSaddleRadius K d 0) 0 hr
      (le_refl 0) (by positivity)
  rw [dedekindSaddleAction, dedekindSaddle, hang, dedekindSaddlePhase]
  simpa using hraw

/-- At the point `dedekindEdgeQ K d + dedekindEdgeOffset M d` the Dedekind saddle action is at
most `(3 / 2) * (√50)^3 * (√(M * √(log d / d)))^3` in absolute value. -/
theorem dedekindSaddle_action_edge
    (M c₀ : ℝ) (d : ℕ) (hM : 0 < M) (_hc₀ : 0 < c₀) (hd : 2 ≤ d)
    (hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d)
    (_hnonempty : dedekindEdgeQ K d + dedekindEdgeOffset M d ≤
      dedekindUpperEndpoint K c₀ d) :
    |dedekindSaddleAction K d
        (dedekindEdgeQ K d + dedekindEdgeOffset M d)| ≤
      (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
        (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 := by
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hdreal : (1 : ℝ) < d := by exact_mod_cast hd
  have ht : 0 < M * Real.sqrt (Real.log d / d) := mul_pos hM
    (Real.sqrt_pos.2 (div_pos (Real.log_pos hdreal) (zero_lt_one.trans hdreal)))
  have hoff : dedekindEdgeOffset M d =
      M * Real.sqrt (Real.log d / d) := rfl
  let q := dedekindEdgeQ K d + dedekindEdgeOffset M d
  have hqedge : dedekindEdgeQ K d < q := by
    dsimp [q]
    rw [hoff]
    linarith
  by_cases hqtop : q ≤ dedekindSaddleQ K d (Real.pi / 2)
  · have hqmem : q ∈ Set.Ioc (dedekindEdgeQ K d)
        (dedekindSaddleQ K d (Real.pi / 2)) := ⟨hqedge, hqtop⟩
    have hrec := dedekindSaddleQ_saddleAngle_of_mem K d hd1
      ⟨hqedge.le, hqtop⟩
    have hquad := dedekindSaddleQ_sub_edge_lower K d hΛ hrec.1
    rw [hrec.2] at hquad
    have hsq : dedekindSaddleAngle K d q ^ 2 ≤
        50 * (M * Real.sqrt (Real.log d / d)) := by
      have h : q - dedekindEdgeQ K d = M * Real.sqrt (Real.log d / d) := by simp [q, hoff]
      linarith
    have hangle : dedekindSaddleAngle K d q ≤
        Real.sqrt 50 * Real.sqrt (M * Real.sqrt (Real.log d / d)) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 50)]
      exact Real.le_sqrt_of_sq_le hsq
    rw [abs_of_nonneg (dedekindSaddleAction_nonneg K d hd1 hqmem)]
    calc
      dedekindSaddleAction K d q ≤
          (3 / 2 : ℝ) * dedekindSaddleAngle K d q ^ 3 :=
            dedekindSaddleAction_le_three_halves_cube K d hd1 hΛ hqmem
      _ ≤ (3 / 2 : ℝ) *
          (Real.sqrt 50 * Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 := by
        gcongr; exact hrec.1.1
      _ = (3 / 2 : ℝ) * (Real.sqrt 50) ^ 3 *
          (Real.sqrt (M * Real.sqrt (Real.log d / d))) ^ 3 := by ring
  · have hzero := dedekindSaddleAction_eq_zero_above_endpoint K d hd1
      (lt_of_not_ge hqtop)
    rw [hzero, abs_zero]
    positivity

private theorem dedekindScaleA_pos_deriv : 0 < dedekindScaleA K := by
  unfold dedekindScaleA
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)

private theorem dedekindScaleA_le_two_pi_deriv : dedekindScaleA K ≤ 2 * Real.pi := by
  have hdisc : 1 ≤ dedekindDiscriminantAbs K := by
    rw [dedekindDiscriminantAbs]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  unfold dedekindScaleA
  have hpow : Real.rpow (dedekindDiscriminantAbs K)
      (-(1 / (dedekindDegree K : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hdisc (neg_nonpos.2 (by positivity))
  nlinarith [Real.pi_pos]

private theorem dedekindScaleT_eq_A_mul_exp (d : ℕ) (hd : 1 ≤ d) :
    dedekindScaleT K d = dedekindScaleA K *
      Real.exp (dedekindScaleLambda K d / 2 + 1) := by
  have hA := dedekindScaleA_pos_deriv K
  have hT : 0 < dedekindScaleT K d :=
    lt_trans (mul_pos hA (Real.exp_pos 1)) (dedekindScaleT_gt_base K d hd)
  have hlog : Real.log (dedekindScaleT K d / dedekindScaleA K) =
      dedekindScaleLambda K d / 2 + 1 := by
    rw [dedekindScaleLambda_div_two]
    ring
  rw [← hlog, Real.exp_log (div_pos hT hA)]
  field_simp

/-- There are absolute constants `C, q₁ > 0` such that `π - C / √q` is at most the Dedekind
saddle action at `q` for every `d ≥ 1` and every `q₁ ≤ q ≤ dedekindScaleT K d`. -/
theorem dedekindSaddle_action_tail :
    ∃ C q₁ : ℝ, 0 < C ∧ 0 < q₁ ∧
      ∀ d : ℕ, 1 ≤ d → ∀ q : ℝ,
        q₁ ≤ q → q ≤ dedekindScaleT K d →
          Real.pi - C / Real.sqrt q ≤ dedekindSaddleAction K d q := by
  refine ⟨12 * Real.sqrt 2,
    2 * Real.pi * Real.exp (12 * Real.pi + 1) + 1, by positivity, by positivity, ?_⟩
  intro d hd q hq₁ hqT
  have hΛ : 24 * Real.pi ≤ dedekindScaleLambda K d := by
    by_contra hn
    have hΛlt : dedekindScaleLambda K d < 24 * Real.pi := lt_of_not_ge hn
    have hA := dedekindScaleA_pos_deriv K
    have hAle := dedekindScaleA_le_two_pi_deriv K
    have hexp : Real.exp (dedekindScaleLambda K d / 2 + 1) <
        Real.exp (12 * Real.pi + 1) := Real.exp_lt_exp.mpr (by linarith)
    have hbound : dedekindScaleT K d <
        2 * Real.pi * Real.exp (12 * Real.pi + 1) := by
      rw [dedekindScaleT_eq_A_mul_exp K d hd]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hAle (Real.exp_pos _).le)
        (mul_lt_mul_of_pos_left hexp (by positivity))
    linarith
  have hedge : dedekindEdgeQ K d ≤ 2 :=
    dedekindEdgeQ_le_two K d (by linarith [Real.pi_pos])
  have htwoq₁ : 2 < 2 * Real.pi * Real.exp (12 * Real.pi + 1) + 1 := by
    have he : 1 ≤ Real.exp (12 * Real.pi + 1) :=
      Real.one_le_exp (by linarith [Real.pi_pos])
    nlinarith [Real.pi_gt_three]
  have hqedge : dedekindEdgeQ K d < q :=
    lt_of_le_of_lt hedge (htwoq₁.trans_le hq₁)
  exact dedekind_pi_sub_twelve_sqrt_two_div_sqrt_le_action K d hd hΛ
    ⟨hqedge, hqT⟩

end

end RiemannJensen