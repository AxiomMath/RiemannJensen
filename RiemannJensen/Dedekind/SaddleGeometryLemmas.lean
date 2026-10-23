module

public import RiemannJensen.Dedekind.ScaleLemmas
public import RiemannJensen.Analysis.ScaleExponent
public import RiemannJensen.Analysis.SaddleRadial
public import RiemannJensen.Analysis.SaddleTrig
public import RiemannJensen.Analysis.SaddleGeometry

/-!
# Initial Dedekind saddle geometry
-/

@[expose] public section

namespace RiemannJensen

open Set

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- On the lower branch,
`(n T / 2) √u (log (T / A) - 1 + log u / 2) = (π d) √u (1 + log u / λ)`
for the Dedekind scales `T`, `A`, `λ` and degree `n`. -/
theorem dedekind_scale_exponent_lower_branch (d : ℕ) (hd : 1 ≤ d) (u : ℂ) :
    ((((dedekindDegree K : ℝ) * dedekindScaleT K d / 2 : ℝ) : ℂ) * lowerSqrt u) *
      ((((Real.log (dedekindScaleT K d / dedekindScaleA K) - 1 : ℝ) : ℂ) +
        lowerLog u / 2)) =
    (((Real.pi * d : ℝ) : ℂ) * lowerSqrt u) *
      (1 + lowerLog u / (dedekindScaleLambda K d : ℂ)) := by
  have hprod : ((dedekindDegree K : ℝ) : ℂ) *
      (dedekindScaleT K d : ℂ) * (dedekindScaleLambda K d : ℂ) =
      4 * (Real.pi : ℂ) * (d : ℂ) := by
    exact_mod_cast dedekindScale_product K d hd
  rw [← dedekindScaleLambda_div_two K d]
  push_cast at hprod ⊢
  field_simp [(dedekindScaleLambda_pos K d hd).ne']
  ring_nf at hprod ⊢
  linear_combination
    (lowerSqrt u * (dedekindScaleLambda K d + lowerLog u)) * hprod

/-- The reciprocal coefficient `λ cos α / κ` of the Dedekind radial equation. -/
def dedekindSaddleRadialCoeff (d : ℕ) (α : ℝ) : ℝ :=
  dedekindScaleLambda K d * Real.cos α / saddleKappa

/-- The constant coefficient `cot α - λ / 2 - 1` of the Dedekind radial equation. -/
def dedekindSaddleRadialConst (d : ℕ) (α : ℝ) : ℝ :=
  alphaCot α - dedekindScaleLambda K d / 2 - 1

/-- The abstract Dedekind radial residual is the generic normal-form equation. -/
theorem dedekindSaddleRadial_eq (d : ℕ) (α r : ℝ) :
    saddleRadialAtLambda (dedekindScaleLambda K d) α r =
      radialEquation (dedekindSaddleRadialCoeff K d α)
        (dedekindSaddleRadialConst K d α) r := by
  rw [saddleRadialAtLambda, radialEquation, dedekindSaddleRadialCoeff,
    dedekindSaddleRadialConst, saddleKappa, div_div]
  ring

/-- On the closed saddle-angle interval the reciprocal coefficient is nonnegative. -/
theorem dedekindSaddleRadialCoeff_nonneg (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) : 0 ≤ dedekindSaddleRadialCoeff K d α := by
  rw [dedekindSaddleRadialCoeff]
  exact div_nonneg
    (mul_nonneg (dedekindScaleLambda_pos K d hd).le
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩))
    (by rw [saddleKappa]; positivity)

/-- The Dedekind radial saddle equation has a unique positive root. -/
theorem existsUnique_dedekindSaddleRadial (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) :
    ∃! r : ℝ, 0 < r ∧
      saddleRadialAtLambda (dedekindScaleLambda K d) α r = 0 := by
  simpa [dedekindSaddleRadial_eq] using
    (existsUnique_radialEquation
      (dedekindSaddleRadialCoeff_nonneg K d hd hα) :
      ∃! r : ℝ, 0 < r ∧
        radialEquation (dedekindSaddleRadialCoeff K d α)
          (dedekindSaddleRadialConst K d α) r = 0)

/-- Any positive root of the Dedekind radial equation equals `dedekindSaddleRadius K d α`. -/
theorem dedekindSaddleRadius_eq_of_radial {d : ℕ} {α r : ℝ}
    (hcoeff : 0 ≤ dedekindSaddleRadialCoeff K d α) (hr : 0 < r)
    (heq : saddleRadialAtLambda (dedekindScaleLambda K d) α r = 0) :
    dedekindSaddleRadius K d α = r := by
  rw [dedekindSaddleRadius, saddleRadiusAtLambda]
  rw [dedekindSaddleRadial_eq] at heq
  have hanti := radialEquation_strictAntiOn (B := dedekindSaddleRadialConst K d α) hcoeff
  have hset :
      {x : ℝ | 0 < x ∧
        saddleRadialAtLambda (dedekindScaleLambda K d) α x ≤ 0} =
        Ici r := by
    ext x
    simp only [mem_ofPred_eq, mem_Ici, dedekindSaddleRadial_eq]
    exact ⟨fun ⟨hx, hxeq⟩ => (hanti.le_iff_ge hx hr).1 (hxeq.trans_eq heq.symm),
      fun hrx => ⟨hr.trans_le hrx, (hanti.antitoneOn hr (hr.trans_le hrx) hrx).trans_eq heq⟩⟩
  rw [hset, csInf_Ici]

/-- The Dedekind saddle radius is positive and is a root of the radial equation
`saddleRadialAtLambda (dedekindScaleLambda K d) α`. -/
theorem dedekindSaddleRadius_pos_and_eq (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) :
    0 < dedekindSaddleRadius K d α ∧
      saddleRadialAtLambda (dedekindScaleLambda K d) α
        (dedekindSaddleRadius K d α) = 0 := by
  rcases existsUnique_dedekindSaddleRadial K d hd hα with ⟨r, hr, _⟩
  have hs := dedekindSaddleRadius_eq_of_radial K
    (dedekindSaddleRadialCoeff_nonneg K d hd hα) hr.1 hr.2
  simpa [hs] using hr

/-- The Dedekind saddle radius is positive for `α ∈ [0, π / 2]`. -/
theorem dedekindSaddleRadius_pos (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) : 0 < dedekindSaddleRadius K d α :=
  (dedekindSaddleRadius_pos_and_eq K d hd hα).1

/-- At the Dedekind saddle radius `r`, `λ cos α / (κ r) + cot α = λ / 2 + 1 + log r`. -/
theorem dedekindSaddleRadius_characterization (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) :
    dedekindScaleLambda K d * Real.cos α /
          (saddleKappa * dedekindSaddleRadius K d α) + alphaCot α =
      dedekindScaleLambda K d / 2 + 1 +
        Real.log (dedekindSaddleRadius K d α) := by
  have h := (dedekindSaddleRadius_pos_and_eq K d hd hα).2
  rw [saddleRadialAtLambda] at h
  linarith

/-- The reciprocal radial coefficient strictly decreases with the saddle angle. -/
theorem dedekindSaddleRadialCoeff_strictAntiOn (d : ℕ) (hd : 1 ≤ d) :
    StrictAntiOn (dedekindSaddleRadialCoeff K d) (Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  simp only [dedekindSaddleRadialCoeff]
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left (cos_strictAntiOn_saddle hα hβ hαβ)
      (dedekindScaleLambda_pos K d hd))
    (by rw [saddleKappa]; positivity)

/-- The constant radial coefficient strictly decreases with the saddle angle. -/
theorem dedekindSaddleRadialConst_strictAntiOn (d : ℕ) :
    StrictAntiOn (dedekindSaddleRadialConst K d) (Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  simp only [dedekindSaddleRadialConst]
  linarith [alphaCot_strictAntiOn hα hβ hαβ]

/-- The Dedekind saddle radius strictly decreases with the saddle angle. -/
theorem dedekindSaddleRadius_strictAntiOn (d : ℕ) (hd : 1 ≤ d) :
    StrictAntiOn (dedekindSaddleRadius K d) (Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  have hcoeff := dedekindSaddleRadialCoeff_strictAntiOn K d hd hα hβ hαβ
  have hconst := dedekindSaddleRadialConst_strictAntiOn K d hα hβ hαβ
  obtain ⟨hαpos, hαeq⟩ := dedekindSaddleRadius_pos_and_eq K d hd hα
  obtain ⟨hβpos, hβeq⟩ := dedekindSaddleRadius_pos_and_eq K d hd hβ
  rw [dedekindSaddleRadial_eq] at hαeq hβeq
  refine (radialEquation_root_mono (dedekindSaddleRadialCoeff_nonneg K d hd hα)
    hcoeff.le hconst.le hβpos hαpos hβeq hαeq).lt_of_ne fun heqr => ?_
  have hdiv := (div_lt_div_iff_of_pos_right hαpos).2 hcoeff
  rw [heqr] at hβeq
  unfold radialEquation at hαeq hβeq
  linarith

/-- The reciprocal Dedekind saddle radius strictly increases with angle. -/
theorem dedekindSaddleRadius_inv_strictMonoOn (d : ℕ) (hd : 1 ≤ d) :
    StrictMonoOn (fun α => (dedekindSaddleRadius K d α)⁻¹)
      (Icc 0 (Real.pi / 2)) := fun _ hα _ hβ hαβ =>
  (inv_lt_inv₀ (dedekindSaddleRadius_pos K d hd hα) (dedekindSaddleRadius_pos K d hd hβ)).2
    (dedekindSaddleRadius_strictAntiOn K d hd hα hβ hαβ)

/-- The Dedekind saddle parameter strictly increases with angle. -/
theorem dedekindSaddleQ_strictMonoOn (d : ℕ) (hd : 1 ≤ d) :
    StrictMonoOn (dedekindSaddleQ K d) (Icc 0 (Real.pi / 2)) := by
  intro α hα β hβ hαβ
  have hinv := dedekindSaddleRadius_inv_strictMonoOn K d hd hα hβ hαβ
  have hinvα : 0 < (dedekindSaddleRadius K d α)⁻¹ :=
    inv_pos.2 (dedekindSaddleRadius_pos K d hd hα)
  have hprod : sinRatio α * (dedekindSaddleRadius K d α)⁻¹ ≤
      sinRatio β * (dedekindSaddleRadius K d β)⁻¹ :=
    mul_le_mul (sinRatio_strictMonoOn hα hβ hαβ).le hinv.le hinvα.le
      (sinRatio_pos_of_mem hβ).le
  have hc : 0 < 2 * saddleKappa / dedekindScaleLambda K d := by
    rw [saddleKappa]
    exact div_pos (by positivity) (dedekindScaleLambda_pos K d hd)
  simp only [dedekindSaddleRadius] at hinv hinvα hprod
  simp only [dedekindSaddleQ, saddleQAtLambda]
  nlinarith [mul_le_mul_of_nonneg_left hprod hc.le]

/-- On the image of the Dedekind saddle branch, the generalized inverse recovers the angle. -/
theorem dedekindSaddleAngle_saddleQ (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hα : α ∈ Icc 0 (Real.pi / 2)) : dedekindSaddleAngle K d (dedekindSaddleQ K d α) = α := by
  rw [dedekindSaddleAngle]
  have hset :
      {β : ℝ | 0 ≤ β ∧ β ≤ Real.pi / 2 ∧
        dedekindSaddleQ K d α ≤ dedekindSaddleQ K d β} =
        Icc α (Real.pi / 2) := by
    ext β
    simp only [mem_ofPred_eq, mem_Icc]
    have hmono := dedekindSaddleQ_strictMonoOn K d hd
    exact ⟨fun ⟨hβ0, hβtop, hq⟩ =>
        ⟨(hmono.le_iff_le hα ⟨hβ0, hβtop⟩).1 hq, hβtop⟩,
      fun ⟨hαβ, hβtop⟩ => ⟨hα.1.trans hαβ, hβtop,
        hmono.monotoneOn hα ⟨hα.1.trans hαβ, hβtop⟩ hαβ⟩⟩
  rw [hset, csInf_Icc hα.2]

end

end RiemannJensen
