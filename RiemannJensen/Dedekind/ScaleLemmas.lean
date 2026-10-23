module

public import RiemannJensen.Dedekind.FieldSaddleDefinitions
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Exact properties of the Dedekind saddle scale
-/

@[expose] public section

namespace RiemannJensen

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- The constant `n_K A_K / (2π)` in the Dedekind scale equation. -/
def dedekindScaleFactor : ℝ :=
  (dedekindDegree K : ℝ) * dedekindScaleA K / (2 * Real.pi)

/-- The function `x ↦ dedekindScaleFactor K · e ^ (x + 1) · x`, whose level sets define the
Dedekind logarithmic scale. -/
def dedekindScaleAux (x : ℝ) : ℝ :=
  dedekindScaleFactor K * Real.exp (x + 1) * x

private theorem dedekindDegree_cast_pos : 0 < (dedekindDegree K : ℝ) := by
  exact_mod_cast dedekindDegree_pos K

private theorem dedekindScaleA_pos : 0 < dedekindScaleA K := by
  unfold dedekindScaleA
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.rpow_pos_of_pos (dedekindDiscriminantAbs_pos K) _)

private theorem dedekindScaleFactor_pos : 0 < dedekindScaleFactor K := by
  unfold dedekindScaleFactor
  exact div_pos (mul_pos (dedekindDegree_cast_pos K) (dedekindScaleA_pos K))
    (mul_pos (by norm_num) Real.pi_pos)

private theorem dedekindScaleAux_zero : dedekindScaleAux K 0 = 0 := by
  simp [dedekindScaleAux]

private theorem dedekindScaleAux_continuous : Continuous (dedekindScaleAux K) := by
  unfold dedekindScaleAux
  fun_prop

private theorem dedekindScaleAux_strictMonoOn :
    StrictMonoOn (dedekindScaleAux K) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hc := dedekindScaleFactor_pos K
  have : Real.exp (x + 1) ≤ Real.exp (y + 1) := Real.exp_monotone (by linarith)
  unfold dedekindScaleAux
  calc
    dedekindScaleFactor K * Real.exp (x + 1) * x
        < dedekindScaleFactor K * Real.exp (x + 1) * y := by gcongr
    _ ≤ dedekindScaleFactor K * Real.exp (y + 1) * y := by gcongr

private theorem dedekindScaleAux_exists (d : ℕ) (hd : 1 ≤ d) :
    ∃ x : ℝ, 0 < x ∧ dedekindScaleAux K x = d := by
  have hc := dedekindScaleFactor_pos K
  have hupper : (d : ℝ) ≤ dedekindScaleAux K (d / dedekindScaleFactor K) := by
    have hexp := Real.one_le_exp (x := d / dedekindScaleFactor K + 1) (by positivity)
    have heq : dedekindScaleFactor K * ((d : ℝ) / dedekindScaleFactor K) = d := by
      field_simp
    rw [dedekindScaleAux]
    nlinarith
  obtain ⟨x, hx, hxd⟩ := intermediate_value_Icc (by positivity)
    (dedekindScaleAux_continuous K).continuousOn ⟨by simp [dedekindScaleAux_zero], hupper⟩
  refine ⟨x, hx.1.lt_of_ne ?_, hxd⟩
  rintro rfl
  rw [dedekindScaleAux_zero] at hxd
  exact (Nat.cast_ne_zero.mpr (by omega : d ≠ 0)) hxd.symm

private theorem dedekindScaleLevel_at_exp (x : ℝ) :
    (dedekindDegree K : ℝ) *
          (dedekindScaleA K * Real.exp (x + 1)) / (2 * Real.pi) *
        (Real.log ((dedekindScaleA K * Real.exp (x + 1)) /
          dedekindScaleA K) - 1) =
      dedekindScaleAux K x := by
  have ha : dedekindScaleA K ≠ 0 := ne_of_gt (dedekindScaleA_pos K)
  rw [show (dedekindScaleA K * Real.exp (x + 1)) / dedekindScaleA K =
      Real.exp (x + 1) by field_simp, Real.log_exp]
  unfold dedekindScaleAux dedekindScaleFactor
  ring

private theorem dedekind_log_coordinate_pos {t : ℝ}
    (ht : dedekindScaleA K * Real.exp 1 < t) :
    0 < Real.log (t / dedekindScaleA K) - 1 := by
  have ha : 0 < dedekindScaleA K := dedekindScaleA_pos K
  have hratio : Real.exp 1 < t / dedekindScaleA K :=
    (lt_div_iff₀ ha).2 (by simpa [mul_comm] using ht)
  have hlog : (1 : ℝ) < Real.log (t / dedekindScaleA K) :=
    (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos 1) hratio)).2 hratio
  linarith

private theorem dedekind_exp_log_coordinate {t : ℝ}
    (ht : dedekindScaleA K * Real.exp 1 < t) :
    dedekindScaleA K *
        Real.exp ((Real.log (t / dedekindScaleA K) - 1) + 1) = t := by
  have ha : 0 < dedekindScaleA K := dedekindScaleA_pos K
  have htpos : 0 < t := lt_trans (mul_pos ha (Real.exp_pos _)) ht
  rw [sub_add_cancel, Real.exp_log (div_pos htpos ha)]
  field_simp

private theorem dedekindScaleLevel_eq_aux_log {t : ℝ}
    (ht : dedekindScaleA K * Real.exp 1 < t) :
    (dedekindDegree K : ℝ) * t / (2 * Real.pi) *
        (Real.log (t / dedekindScaleA K) - 1) =
      dedekindScaleAux K (Real.log (t / dedekindScaleA K) - 1) := by
  conv_lhs => rw [← dedekind_exp_log_coordinate K ht]
  rw [dedekindScaleLevel_at_exp]

private theorem exists_isLeast_dedekindScaleSet (d : ℕ) (hd : 1 ≤ d) :
    ∃ t : ℝ, IsLeast
      {u : ℝ | dedekindScaleA K * Real.exp 1 < u ∧
        (d : ℝ) ≤ (dedekindDegree K : ℝ) * u / (2 * Real.pi) *
          (Real.log (u / dedekindScaleA K) - 1)} t ∧
      (dedekindDegree K : ℝ) * t / (2 * Real.pi) *
          (Real.log (t / dedekindScaleA K) - 1) = d := by
  obtain ⟨x, hx0, hxd⟩ := dedekindScaleAux_exists K d hd
  have htlevel := (dedekindScaleLevel_at_exp K x).trans hxd
  refine ⟨_, ⟨⟨mul_lt_mul_of_pos_left (Real.exp_strictMono (by linarith))
    (dedekindScaleA_pos K), htlevel.ge⟩, fun u hu => ?_⟩, htlevel⟩
  have hxy : x ≤ Real.log (u / dedekindScaleA K) - 1 :=
    ((dedekindScaleAux_strictMonoOn K).le_iff_le hx0.le
      (dedekind_log_coordinate_pos K hu.1).le).mp
      (hxd ▸ dedekindScaleLevel_eq_aux_log K hu.1 ▸ hu.2)
  rw [← dedekind_exp_log_coordinate K hu.1]
  exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith)) (dedekindScaleA_pos K).le

/-- The Dedekind saddle scale `T_d` exceeds `A_K · e` and satisfies its defining level equation
`n_K T_d / (2π) · (log (T_d / A_K) - 1) = d`. -/
theorem dedekindScaleT_mem_and_level (d : ℕ) (hd : 1 ≤ d) :
    dedekindScaleA K * Real.exp 1 < dedekindScaleT K d ∧
      (dedekindDegree K : ℝ) * dedekindScaleT K d / (2 * Real.pi) *
          (Real.log (dedekindScaleT K d / dedekindScaleA K) - 1) = d := by
  obtain ⟨t, ht, htlevel⟩ := exists_isLeast_dedekindScaleSet K d hd
  rw [dedekindScaleT, ht.csInf_eq]
  exact ⟨ht.1.1, htlevel⟩

/-- Exact defining equation for the Dedekind saddle scale. -/
theorem dedekindScaleT_level (d : ℕ) (hd : 1 ≤ d) :
    (dedekindDegree K : ℝ) * dedekindScaleT K d / (2 * Real.pi) *
        (Real.log (dedekindScaleT K d / dedekindScaleA K) - 1) = d :=
  (dedekindScaleT_mem_and_level K d hd).2

/-- The Dedekind saddle scale exceeds `A_K · e`. -/
theorem dedekindScaleT_gt_base (d : ℕ) (hd : 1 ≤ d) :
    dedekindScaleA K * Real.exp 1 < dedekindScaleT K d :=
  (dedekindScaleT_mem_and_level K d hd).1

/-- The Dedekind saddle scale is positive. -/
theorem dedekindScaleT_pos (d : ℕ) (hd : 1 ≤ d) : 0 < dedekindScaleT K d :=
  (mul_pos (dedekindScaleA_pos K) (Real.exp_pos 1)).trans (dedekindScaleT_gt_base K d hd)

/-- Positivity of the Dedekind logarithmic scale. -/
theorem dedekindScaleLambda_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < dedekindScaleLambda K d := by
  rw [dedekindScaleLambda]
  exact mul_pos (by norm_num)
    (dedekind_log_coordinate_pos K (dedekindScaleT_gt_base K d hd))

/-- The exact identity `n_K T_d Λ_d = 4 π d`. -/
theorem dedekindScale_product (d : ℕ) (hd : 1 ≤ d) :
    (dedekindDegree K : ℝ) * dedekindScaleT K d * dedekindScaleLambda K d =
      4 * Real.pi * d := by
  have hlevel := dedekindScaleT_level K d hd
  rw [dedekindScaleLambda]
  field_simp at hlevel ⊢
  nlinarith [Real.pi_pos]

/-- The logarithmic coordinate is half the Dedekind logarithmic scale. -/
theorem dedekindScaleLambda_div_two (d : ℕ) :
    dedekindScaleLambda K d / 2 =
      Real.log (dedekindScaleT K d / dedekindScaleA K) - 1 := by
  rw [dedekindScaleLambda]
  ring

/-- `Λ_d / 2` solves `dedekindScaleAux K x = d`. -/
theorem dedekindScaleAux_scaleLambda (d : ℕ) (hd : 1 ≤ d) :
    dedekindScaleAux K (dedekindScaleLambda K d / 2) = d := by
  rw [dedekindScaleLambda_div_two,
    ← dedekindScaleLevel_eq_aux_log K (dedekindScaleT_gt_base K d hd)]
  exact dedekindScaleT_level K d hd

private theorem eventually_le_half_dedekindScaleLambda {X : ℝ} (hX : 0 ≤ X) :
    ∃ D : ℕ, ∀ d ≥ D, 1 ≤ d ∧ X ≤ dedekindScaleLambda K d / 2 := by
  obtain ⟨D, hD⟩ := exists_nat_ge (dedekindScaleAux K X)
  refine ⟨max D 1, fun d hd => ?_⟩
  have hd1 : 1 ≤ d := (le_max_right D 1).trans hd
  refine ⟨hd1, ((dedekindScaleAux_strictMonoOn K).le_iff_le (Set.mem_Ici.2 hX)
    (Set.mem_Ici.2 (half_pos (dedekindScaleLambda_pos K d hd1)).le)).mp ?_⟩
  rw [dedekindScaleAux_scaleLambda K d hd1]
  exact hD.trans (by exact_mod_cast (le_max_left D 1).trans hd)

/-- Eventually the Dedekind logarithmic scale is at least `log d`. -/
theorem eventually_log_le_dedekindScaleLambda :
    ∃ D : ℕ, ∀ d ≥ D, Real.log d ≤ dedekindScaleLambda K d := by
  obtain ⟨D, hD⟩ := eventually_le_half_dedekindScaleLambda K
    (X := max 1 (dedekindScaleFactor K * Real.exp 1)) (zero_le_one.trans (le_max_left _ _))
  refine ⟨D, fun d hd => ?_⟩
  obtain ⟨hd1, hXx⟩ := hD d hd
  set x := dedekindScaleLambda K d / 2 with hx
  have hxd : dedekindScaleAux K x = d := dedekindScaleAux_scaleLambda K d hd1
  have hxpos : 0 < x := zero_lt_one.trans_le ((le_max_left _ _).trans hXx)
  have hcex : dedekindScaleFactor K * Real.exp 1 ≤ x := (le_max_right 1 _).trans hXx
  have hxhalf : x ≤ Real.exp (x / 2) := by
    convert Real.two_mul_le_exp (x := x / 2) using 1
    ring
  have hsquare : x ^ 2 ≤ Real.exp x := by
    calc
      x ^ 2 ≤ Real.exp (x / 2) ^ 2 := by gcongr
      _ = Real.exp x := by rw [sq, ← Real.exp_add, add_halves]
  have hdexp : (d : ℝ) ≤ Real.exp (2 * x) := by
    rw [← hxd, dedekindScaleAux, Real.exp_add]
    calc
      dedekindScaleFactor K * (Real.exp x * Real.exp 1) * x =
          (dedekindScaleFactor K * Real.exp 1 * x) * Real.exp x := by ring
      _ ≤ x ^ 2 * Real.exp x := by
        gcongr
        nlinarith
      _ ≤ Real.exp x * Real.exp x := by gcongr
      _ = Real.exp (2 * x) := by rw [← Real.exp_add, two_mul]
  have hlog : Real.log d ≤ 2 * x :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hd1)).2 hdexp
  linarith

/-- Eventually the Dedekind logarithmic scale is at most `3 log d`. -/
theorem eventually_dedekindScaleLambda_le_three_log :
    ∃ D : ℕ, ∀ d ≥ D, dedekindScaleLambda K d ≤ 3 * Real.log d := by
  have hcpos : 0 < dedekindScaleFactor K * Real.exp 1 :=
    mul_pos (dedekindScaleFactor_pos K) (Real.exp_pos _)
  obtain ⟨D, hD⟩ := eventually_le_half_dedekindScaleLambda K
    (X := max 1 (1 / (dedekindScaleFactor K * Real.exp 1)))
    (zero_le_one.trans (le_max_left _ _))
  refine ⟨D, fun d hd => ?_⟩
  obtain ⟨hd1, hXx⟩ := hD d hd
  set x := dedekindScaleLambda K d / 2 with hx
  have hxd : dedekindScaleAux K x = d := dedekindScaleAux_scaleLambda K d hd1
  have hxpos : 0 < x := zero_lt_one.trans_le ((le_max_left _ _).trans hXx)
  have hone : 1 ≤ dedekindScaleFactor K * Real.exp 1 * x := by
    rw [mul_comm]
    exact (div_le_iff₀ hcpos).mp ((le_max_right 1 _).trans hXx)
  have hexpd : Real.exp x ≤ (d : ℝ) := by
    rw [← hxd, dedekindScaleAux, Real.exp_add]
    calc
      Real.exp x = 1 * Real.exp x := (one_mul _).symm
      _ ≤ (dedekindScaleFactor K * Real.exp 1 * x) * Real.exp x := by gcongr
      _ = dedekindScaleFactor K * (Real.exp x * Real.exp 1) * x := by ring
  have hxlog : x ≤ Real.log d :=
    (Real.le_log_iff_exp_le (by exact_mod_cast hd1)).2 hexpd
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  linarith

end

end RiemannJensen
