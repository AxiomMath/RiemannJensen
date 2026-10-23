module

public import Mathlib

/-!
# Complex Stirling formula on the closed right half-plane

For `s` with `0 ≤ re s` and `1 ≤ ‖s‖` we prove `Γ(s) = exp (stirMain s + stirR s)`, where
`stirMain s = (s - 1/2) log s - s + log(2π)/2` and the remainder `stirR s` is the sum of the
one-step defects `stirD (s + j)`, `j ≥ 0`. Bounds `‖stirD z‖ = O(‖z‖⁻²)` give
`‖stirR s‖ = O(‖s‖⁻¹)`, and hence an explicit bound on `‖Γ(s) / (√(2π) s^(s-1/2) e^(-s)) - 1‖`.

## Main definitions

* `StirlingScratch.stirMain`: the Stirling main term `(z - 1/2) log z - z + log(2π)/2`.
* `StirlingScratch.stirD`: the defect `stirMain (z + 1) - stirMain z - log z`.
* `StirlingScratch.stirR`: the remainder `∑_{j ≥ 0} stirD (s + j)`.
* `StirlingScratch.logGammaSeq`: the logarithmic partial products of Euler's limit for `Γ`.

## Main results

* `StirlingScratch.Gamma_eq_exp_stirMain_add`: `Γ(s) = exp (stirMain s + stirR s)`.
* `StirlingScratch.Gamma_stirling_exp_form`: `Γ(s) = √(2π) s^(s-1/2) e^(-s) exp R` with
  `‖R‖ ≤ 7/(2‖s‖)` when `‖s‖ ≥ 2`.
* `StirlingScratch.Gamma_stirling_quotient`: the relative error is at most `28/‖s‖` when
  `‖s‖ ≥ 2`.
* `StirlingScratch.Gamma_stirling_quotient_one`: the relative error is at most
  `136 e^136/‖s‖` when `‖s‖ ≥ 1`.
* `StirlingScratch.exists_Gamma_stirling_quotient`: the relative error is `O(‖s‖⁻¹)`
  uniformly on `0 ≤ re s`, `1 ≤ ‖s‖`.
-/

@[expose] public section

open Complex Filter Topology Finset

namespace StirlingScratch

/-- Stirling main term `(z - 1/2) log z - z + log(2π)/2`, principal `log`. -/
noncomputable def stirMain (z : ℂ) : ℂ :=
  (z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)

/-- One-step defect: `stirMain (z+1) - stirMain z - log z`. -/
noncomputable def stirD (z : ℂ) : ℂ := stirMain (z + 1) - stirMain z - Complex.log z

/-- For `0 ≤ re z`: `1 ≤ re (1 + z⁻¹)`. -/
lemma one_le_re_one_add_inv {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ (1 + z⁻¹).re := by
  rw [add_re, one_re, inv_re]
  have : 0 ≤ z.re / normSq z := div_nonneg hz (normSq_nonneg z)
  linarith

/-- `log (z+1) = log z + log (1 + z⁻¹)` on the closed right half-plane minus `0`. -/
lemma log_add_one_eq {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Complex.log (z + 1) = Complex.log z + Complex.log (1 + z⁻¹) := by
  have hre : 0 < (1 + z⁻¹).re := by linarith [one_le_re_one_add_inv hz]
  have hw0 : (1 + z⁻¹) ≠ 0 := fun h => by simp [h] at hre
  have h1 : |arg z| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hz
  have h2 : |arg (1 + z⁻¹)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  rw [← show z * (1 + z⁻¹) = z + 1 by field_simp]
  refine log_mul hz0 hw0 ?_
  rw [abs_le] at h1
  rw [abs_lt] at h2
  constructor <;> linarith [Real.pi_pos]

/-- For `0 ≤ re z`, `z ≠ 0`: `stirD z = (z + 1/2) log (1 + z⁻¹) - 1`. -/
lemma stirD_eq {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    stirD z = (z + 1 / 2) * Complex.log (1 + z⁻¹) - 1 := by
  unfold stirD stirMain
  rw [log_add_one_eq hz hz0]
  ring

/-- For `0 < ‖w‖ ≤ 1/2`: `‖(w⁻¹ + 1/2) log(1+w) - 1‖ ≤ (7/6) ‖w‖^2`. -/
lemma norm_defect_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) (hw0 : w ≠ 0) :
    ‖(w⁻¹ + 1 / 2) * Complex.log (1 + w) - 1‖ ≤ 7 / 6 * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  have hT : logTaylor 3 w = w - w ^ 2 / 2 := by
    simp [logTaylor_succ, logTaylor_zero]
    ring
  have hA := norm_log_sub_logTaylor_le 2 hw1
  rw [hT] at hA
  have hB := norm_log_one_add_sub_self_le hw1
  have hid : (w⁻¹ + 1 / 2) * Complex.log (1 + w) - 1 =
      w⁻¹ * (Complex.log (1 + w) - (w - w ^ 2 / 2)) + 1 / 2 * (Complex.log (1 + w) - w) := by
    field_simp
    ring
  rw [hid]
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  calc ‖w⁻¹ * (Complex.log (1 + w) - (w - w ^ 2 / 2)) + 1 / 2 * (Complex.log (1 + w) - w)‖
      ≤ ‖w⁻¹‖ * ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖
          + ‖(1 / 2 : ℂ)‖ * ‖Complex.log (1 + w) - w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖w‖⁻¹ * (‖w‖ ^ (2 + 1) * 2 / (2 + 1)) + 1 / 2 * (‖w‖ ^ 2 * 2 / 2) := by
        rw [norm_inv, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        gcongr
        · calc ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖
              ≤ ‖w‖ ^ (2 + 1) * (1 - ‖w‖)⁻¹ / (2 + 1) := by exact_mod_cast hA
            _ ≤ ‖w‖ ^ (2 + 1) * 2 / (2 + 1) := by gcongr
        · calc ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := hB
            _ ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = 7 / 6 * ‖w‖ ^ 2 := by
      field_simp
      ring

/-- `‖stirD z‖ ≤ (7/6)/‖z‖^2` for `0 ≤ re z`, `‖z‖ ≥ 2`. -/
lemma norm_stirD_le {z : ℂ} (hz : 0 ≤ z.re) (hz2 : 2 ≤ ‖z‖) :
    ‖stirD z‖ ≤ 7 / 6 / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [stirD_eq hz hz0]
  have hw : ‖z⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  simpa only [inv_inv, norm_inv, inv_pow, ← div_eq_mul_inv] using
    norm_defect_le hw (inv_ne_zero hz0)

/-- Coarse bound on `log u` when `1 ≤ Re u` and `‖u‖ ≤ 2`. -/
lemma norm_log_le_three {u : ℂ} (h1 : 1 ≤ u.re) (h2 : ‖u‖ ≤ 2) : ‖Complex.log u‖ ≤ 3 := by
  have hu1 : 1 ≤ ‖u‖ := h1.trans ((le_abs_self _).trans (Complex.abs_re_le_norm u))
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [log_re, log_im]
  have hl0 : 0 ≤ Real.log ‖u‖ := Real.log_nonneg hu1
  have hl1 : Real.log ‖u‖ ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < ‖u‖)]
  have ha : |arg u| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr (by linarith)
  rw [abs_of_nonneg hl0]
  linarith [Real.pi_lt_four]

/-- `‖stirD z‖ ≤ 34/‖z‖^2` for `0 ≤ re z`, `‖z‖ ≥ 1`. -/
lemma norm_stirD_le' {z : ℂ} (hz : 0 ≤ z.re) (hz1 : 1 ≤ ‖z‖) :
    ‖stirD z‖ ≤ 34 / ‖z‖ ^ 2 := by
  rcases le_or_gt 2 ‖z‖ with h2 | h2
  · exact (norm_stirD_le hz h2).trans (by gcongr; norm_num)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [stirD_eq hz hz0]
  have hn : ‖1 + z⁻¹‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_inv]
    linarith [inv_le_one_of_one_le₀ hz1]
  have hL := norm_log_le_three (one_le_re_one_add_inv hz) hn
  have hb : ‖(z + 1 / 2) * Complex.log (1 + z⁻¹) - 1‖ ≤ 17 / 2 := by
    calc _ ≤ ‖z + 1 / 2‖ * ‖Complex.log (1 + z⁻¹)‖ + ‖(1 : ℂ)‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ (‖z‖ + 1 / 2) * 3 + 1 := by
          rw [norm_one]
          gcongr
          refine (norm_add_le _ _).trans ?_
          norm_num
      _ ≤ 17 / 2 := by nlinarith
  refine hb.trans ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ### Summation bound -/

/-- `∑_{j ≤ n} 1/(r + j)^2 ≤ 1/r^2 + 1/r - 1/(r + n)` for `r > 0`. -/
lemma sum_inv_sq_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ j ∈ range (n + 1), 1 / (r + j) ^ 2 ≤ 1 / r ^ 2 + 1 / r - 1 / (r + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : 0 < r + n := by positivity
    have key : 1 / (r + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (r + n) - 1 / (r + ((n + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- `∑_{j < n} 1/(r + j)^2 ≤ 1/r^2 + 1/r` for `r > 0`. -/
lemma sum_inv_sq_le' {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ j ∈ range n, 1 / (r + j) ^ 2 ≤ 1 / r ^ 2 + 1 / r := by
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  · linarith [sum_inv_sq_le hr n, (by positivity : 0 ≤ 1 / (r + n))]

/-- For `0 ≤ re s` and `j : ℕ`: `‖s‖^2 + j^2 ≤ ‖s + j‖^2`. -/
lemma sq_norm_add_nat {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) :
    ‖s‖ ^ 2 + (j : ℝ) ^ 2 ≤ ‖s + j‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero]
  have : 0 ≤ s.re * j := mul_nonneg hs (Nat.cast_nonneg j)
  nlinarith

/-- For `0 ≤ re s` and `j : ℕ`: `‖s‖ ≤ ‖s + j‖`. -/
lemma norm_le_norm_add_nat {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) : ‖s‖ ≤ ‖s + j‖ := by
  have := sq_norm_add_nat hs j
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by nlinarith [sq_nonneg (j : ℝ)])

/-- For `0 ≤ re s`, `0 < ‖s‖` and `0 ≤ c`: `c/‖s + j‖^2 ≤ 2c/(‖s‖ + j)^2`. -/
lemma div_sq_norm_add_nat_le {s : ℂ} (hs : 0 ≤ s.re) (hs0 : 0 < ‖s‖) (j : ℕ) {c : ℝ}
    (hc : 0 ≤ c) : c / ‖s + j‖ ^ 2 ≤ 2 * c * (1 / (‖s‖ + j) ^ 2) := by
  have hpos : 0 < ‖s‖ + j := by positivity
  have h2 : (‖s‖ + j) ^ 2 ≤ 2 * ‖s + j‖ ^ 2 := by
    nlinarith [sq_nonneg (‖s‖ - j), sq_norm_add_nat hs j]
  calc c / ‖s + j‖ ^ 2 ≤ c / ((‖s‖ + j) ^ 2 / 2) :=
      div_le_div_of_nonneg_left hc (by positivity) (by linarith)
    _ = 2 * c * (1 / (‖s‖ + j) ^ 2) := by field_simp

/-- For `0 ≤ re s` and `j : ℕ`: `0 ≤ re (s + j)`. -/
lemma re_add_nat_nonneg {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) : 0 ≤ (s + j).re := by
  simp only [add_re, natCast_re]
  positivity

/-- `‖stirD (s + j)‖ ≤ (7/3)/(‖s‖ + j)^2` for `0 ≤ re s`, `‖s‖ ≥ 2`. -/
lemma norm_stirD_add_le {s : ℂ} (hs : 0 ≤ s.re) (hs2 : 2 ≤ ‖s‖) (j : ℕ) :
    ‖stirD (s + j)‖ ≤ 7 / 3 * (1 / (‖s‖ + j) ^ 2) := by
  convert (norm_stirD_le (re_add_nat_nonneg hs j) (hs2.trans (norm_le_norm_add_nat hs j))).trans
    (div_sq_norm_add_nat_le hs (by linarith) j (c := 7 / 6) (by norm_num)) using 2
  norm_num

/-- `‖stirD (s + j)‖ ≤ 68/(‖s‖ + j)^2` for `0 ≤ re s`, `‖s‖ ≥ 1`. -/
lemma norm_stirD_add_le' {s : ℂ} (hs : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) (j : ℕ) :
    ‖stirD (s + j)‖ ≤ 68 * (1 / (‖s‖ + j) ^ 2) := by
  convert (norm_stirD_le' (re_add_nat_nonneg hs j) (hs1.trans (norm_le_norm_add_nat hs j))).trans
    (div_sq_norm_add_nat_le hs (by linarith) j (c := 34) (by norm_num)) using 2
  norm_num

/-- The Stirling remainder `R(s) = ∑_{j ≥ 0} stirD (s + j)`. -/
noncomputable def stirR (s : ℂ) : ℂ := ∑' j : ℕ, stirD (s + j)

/-- For `r > 0`, the series `∑_j c/(r + j)^2` is summable. -/
lemma summable_bound {r : ℝ} (hr : 0 < r) (c : ℝ) :
    Summable (fun j : ℕ => c * (1 / (r + j) ^ 2)) :=
  (summable_of_sum_range_le (c := 1 / r ^ 2 + 1 / r) (fun j => by positivity)
    (fun n => sum_inv_sq_le' hr n)).mul_left _

/-- For `r > 0` and `c ≥ 0`: `∑_j c/(r + j)^2 ≤ c (1/r^2 + 1/r)`. -/
lemma tsum_bound_le {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : 0 ≤ c) :
    ∑' j : ℕ, c * (1 / (r + j) ^ 2) ≤ c * (1 / r ^ 2 + 1 / r) := by
  rw [tsum_mul_left]
  gcongr
  exact Real.tsum_le_of_sum_range_le (fun j => by positivity) (fun n => sum_inv_sq_le' hr n)

/-- For `0 ≤ re s`, `‖s‖ ≥ 1`, the series `∑_j stirD (s + j)` is summable. -/
lemma summable_stirD {s : ℂ} (hs : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    Summable (fun j : ℕ => stirD (s + j)) :=
  Summable.of_norm_bounded (summable_bound (by linarith) 68) (norm_stirD_add_le' hs hs1)

/-- A termwise bound `‖stirD (s + j)‖ ≤ c/(‖s‖ + j)^2` gives `‖stirR s‖ ≤ c (1/‖s‖^2 + 1/‖s‖)`. -/
lemma norm_stirR_le_of {s : ℂ} (hr : 0 < ‖s‖) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j : ℕ, ‖stirD (s + j)‖ ≤ c * (1 / (‖s‖ + j) ^ 2)) :
    ‖stirR s‖ ≤ c * (1 / ‖s‖ ^ 2 + 1 / ‖s‖) :=
  (tsum_of_norm_bounded (summable_bound hr _).hasSum h).trans (tsum_bound_le hr hc)

/-- `‖stirR s‖ ≤ 7/(2‖s‖)` for `0 ≤ re s`, `‖s‖ ≥ 2`. -/
theorem norm_stirR_le {s : ℂ} (hs : 0 ≤ s.re) (hs2 : 2 ≤ ‖s‖) :
    ‖stirR s‖ ≤ 7 / 2 / ‖s‖ := by
  have hr : 0 < ‖s‖ := by linarith
  refine (norm_stirR_le_of hr (by norm_num) (norm_stirD_add_le hs hs2)).trans ?_
  rw [div_add_div _ _ (by positivity) hr.ne', mul_div_assoc', div_le_div_iff₀ (by positivity) hr]
  nlinarith

/-- `‖stirR s‖ ≤ 136/‖s‖` for `0 ≤ re s`, `‖s‖ ≥ 1`. -/
theorem norm_stirR_le' {s : ℂ} (hs : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    ‖stirR s‖ ≤ 136 / ‖s‖ := by
  have hr : 0 < ‖s‖ := by linarith
  refine (norm_stirR_le_of hr (by norm_num) (norm_stirD_add_le' hs hs1)).trans ?_
  rw [div_add_div _ _ (by positivity) hr.ne', mul_div_assoc', div_le_div_iff₀ (by positivity) hr]
  nlinarith

/-! ### The limit of the boundary bracket -/

/-- `n log (1 + a/n) → a` as `n → ∞`. -/
lemma tendsto_mul_log_one_add_div (a : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (1 + a / n)) atTop (𝓝 a) := by
  refine Complex.tendsto_nat_mul_log_one_add_of_tendsto (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp

/-- `log (1 + a/n) → 0` as `n → ∞`. -/
lemma tendsto_log_one_add_div (a : ℂ) :
    Tendsto (fun n : ℕ => Complex.log (1 + a / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + a / (n : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat a)
  rw [← Complex.log_one]
  exact (continuousAt_clog (by simp [slitPlane])).tendsto.comp h1

/-- The boundary bracket `s log n + log n! - stirMain (s + n + 1) → 0`. -/
lemma tendsto_bracket (s : ℂ) :
    Tendsto (fun n : ℕ => s * (Real.log n : ℂ) + (Real.log (n.factorial) : ℂ)
      - stirMain (s + n + 1)) atTop (𝓝 0) := by
  set ℓ : ℕ → ℂ := fun n => Complex.log (1 + (s + 1) / n) with hℓ
  have hF : Tendsto (fun n : ℕ =>
      ((Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 : ℝ) : ℂ) + (s + 1)
        - (s + 1 / 2) * ℓ n - n * ℓ n) atTop (𝓝 0) := by
    have hS : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2)
        atTop (𝓝 0) := by
      have hc : ContinuousAt Real.log (√Real.pi) :=
        Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne'
      have := (hc.tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi).sub_const
        (Real.log Real.pi / 2)
      rwa [Function.comp_def, Real.log_sqrt Real.pi_pos.le, sub_self] at this
    have hS' := (continuous_ofReal.tendsto 0).comp hS
    rw [ofReal_zero] at hS'
    have := ((hS'.add_const (s + 1)).sub
      ((tendsto_log_one_add_div (s + 1)).const_mul (s + 1 / 2))).sub
        (tendsto_mul_log_one_add_div (s + 1))
    simpa using this
  refine hF.congr' ?_
  filter_upwards [eventually_ge_atTop (⌈‖s‖⌉₊ + 1)] with n hn
  have hnR : ‖s‖ + 1 ≤ (n : ℝ) := by
    have := Nat.le_ceil ‖s‖
    have h' : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h'
    linarith
  have hn0 : (0 : ℝ) < n := by linarith [norm_nonneg s]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hfac : Real.log (n.factorial) = Real.log (Stirling.stirlingSeq n)
      + (Real.log 2 + Real.log n) / 2 + n * (Real.log n - 1) := by
    rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hn0.ne',
      Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have h2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  have hw0 : (1 + (s + 1) / n) ≠ 0 := by
    intro h
    have : s + n + 1 = 0 := by
      have e : s + n + 1 = (n : ℂ) * (1 + (s + 1) / n) := by field_simp; ring
      rw [e, h, mul_zero]
    have hre := congrArg Complex.re this
    simp only [add_re, natCast_re, one_re, zero_re] at hre
    have := Complex.abs_re_le_norm s
    rw [abs_le] at this
    linarith
  have hlog : Complex.log (s + n + 1) = (Real.log n : ℂ) + ℓ n := by
    have e : s + n + 1 = ((n : ℝ) : ℂ) * (1 + (s + 1) / n) := by
      push_cast; field_simp; ring
    rw [e, log_ofReal_mul hn0 hw0]
  simp only [stirMain]
  rw [show s + n + 1 - 1 / 2 = s + n + 1 / 2 by ring, hlog, hfac, h2pi]
  push_cast
  ring

/-! ### Assembly: Euler's limit and telescoping -/

/-- Partial sums `L_n(s) = s log n + log n! - ∑_{j ≤ n} log (s + j)` (principal logs, termwise). -/
noncomputable def logGammaSeq (s : ℂ) (n : ℕ) : ℂ :=
  s * (Real.log n : ℂ) + (Real.log n.factorial : ℂ) - ∑ j ∈ range (n + 1), Complex.log (s + j)

/-- If `s + j ≠ 0` for all `j : ℕ` and `n ≠ 0`, then `exp (logGammaSeq s n) = GammaSeq s n`. -/
lemma exp_logGammaSeq {s : ℂ} (hne : ∀ j : ℕ, s + j ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    exp (logGammaSeq s n) = GammaSeq s n := by
  unfold logGammaSeq GammaSeq
  rw [exp_sub, exp_add, exp_sum]
  congr 1
  · congr 1
    · rw [natCast_log, cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), mul_comm s (log (n : ℂ))]
    · rw [natCast_log, exp_log (by exact_mod_cast n.factorial_ne_zero)]
  · exact Finset.prod_congr rfl fun m _ => exp_log (hne m)

/-- Telescoping: `logGammaSeq s n` equals
`s log n + log n! - stirMain (s + n + 1) + stirMain s + ∑_{j ≤ n} stirD (s + j)`. -/
lemma logGammaSeq_eq (s : ℂ) (n : ℕ) :
    logGammaSeq s n = (s * (Real.log n : ℂ) + (Real.log n.factorial : ℂ) - stirMain (s + n + 1))
      + stirMain s + ∑ j ∈ range (n + 1), stirD (s + j) := by
  have h1 : ∀ j : ℕ, Complex.log (s + j) =
      (stirMain (s + ((j + 1 : ℕ) : ℂ)) - stirMain (s + (j : ℕ))) - stirD (s + j) := by
    intro j
    rw [show s + ((j + 1 : ℕ) : ℂ) = s + j + 1 by push_cast; ring]
    unfold stirD
    ring
  rw [logGammaSeq, Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun j : ℕ => stirMain (s + (j : ℕ)))]
  push_cast
  rw [add_zero]
  ring_nf

/-- **Binet-type identity.** For `Re s ≥ 0`, `‖s‖ ≥ 1`: `Γ(s) = exp (stirMain s + stirR s)`. -/
theorem Gamma_eq_exp_stirMain_add {s : ℂ} (hs : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    Gamma s = exp (stirMain s + stirR s) := by
  have hne : ∀ j : ℕ, s + j ≠ 0 := fun j h => by
    have := norm_le_norm_add_nat hs j
    rw [h, norm_zero] at this
    linarith
  have hsum := (summable_stirD hs hs1).hasSum
  have hT : Tendsto (logGammaSeq s) atTop (𝓝 (stirMain s + stirR s)) := by
    have hpart : Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1), stirD (s + j)) atTop
        (𝓝 (stirR s)) := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have := ((tendsto_bracket s).add_const (stirMain s)).add hpart
    rw [zero_add] at this
    exact this.congr' (Eventually.of_forall fun n => (logGammaSeq_eq s n).symm)
  have h1 : Tendsto (GammaSeq s) atTop (𝓝 (exp (stirMain s + stirR s))) := by
    refine ((continuous_exp.tendsto _).comp hT).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact exp_logGammaSeq hne hn
  exact tendsto_nhds_unique (GammaSeq_tendsto_Gamma s) h1

/-- For `s ≠ 0`: `exp (stirMain s) = √(2π) s^(s-1/2) e^(-s)`. -/
lemma exp_stirMain {s : ℂ} (hs0 : s ≠ 0) :
    exp (stirMain s) = (Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) * exp (-s) := by
  have hsq : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = exp ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
    rw [← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 2
    ring
  rw [hsq, cpow_def_of_ne_zero hs0, stirMain, ← exp_add, ← exp_add]
  congr 1
  ring

/-- `e^2 < 8`. -/
lemma real_exp_two_lt : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos 1]

/-- **Complex Stirling, exponential form.** For `Re s ≥ 0`, `‖s‖ ≥ 2`,
`Γ(s) = √(2π) s^(s-1/2) e^(-s) exp R` with `‖R‖ ≤ 7/(2‖s‖)`. -/
theorem Gamma_stirling_exp_form {s : ℂ} (hs : 0 ≤ s.re) (hs2 : 2 ≤ ‖s‖) :
    ∃ R : ℂ, Gamma s = (Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) * exp (-s) * exp R ∧
      ‖R‖ ≤ 7 / 2 / ‖s‖ := by
  have hs0 : s ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨stirR s, ?_, norm_stirR_le hs hs2⟩
  rw [Gamma_eq_exp_stirMain_add hs (by linarith), exp_add, exp_stirMain hs0]

/-- `‖exp z - 1‖ ≤ ‖z‖ exp ‖z‖`. -/
lemma norm_exp_sub_one_le_mul_exp (z : ℂ) : ‖exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  simpa using norm_exp_sub_sum_le_norm_mul_exp z 1

/-- **Complex Stirling, quotient form.** For `Re s ≥ 0`, `‖s‖ ≥ 2`,
`‖Γ(s) / (√(2π) s^(s-1/2) e^(-s)) - 1‖ ≤ 28/‖s‖`. -/
theorem Gamma_stirling_quotient {s : ℂ} (hs : 0 ≤ s.re) (hs2 : 2 ≤ ‖s‖) :
    ‖Gamma s / ((Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) * exp (-s)) - 1‖
      ≤ 28 / ‖s‖ := by
  have hr : 0 < ‖s‖ := by linarith
  rw [← exp_stirMain (norm_pos_iff.mp hr), Gamma_eq_exp_stirMain_add hs (by linarith), exp_add,
    mul_div_cancel_left₀ _ (exp_ne_zero _)]
  have hR := norm_stirR_le hs hs2
  have hR2 : ‖stirR s‖ ≤ 2 := hR.trans ((div_le_iff₀ hr).mpr (by linarith))
  calc ‖exp (stirR s) - 1‖ ≤ ‖stirR s‖ * Real.exp ‖stirR s‖ := norm_exp_sub_one_le_mul_exp _
    _ ≤ 7 / 2 / ‖s‖ * 8 := by
        gcongr
        exact (Real.exp_le_exp.mpr hR2).trans real_exp_two_lt.le
    _ = 28 / ‖s‖ := by ring

/-- **Complex Stirling on `Re s ≥ 0`, `‖s‖ ≥ 1`.**
`‖Γ(s) / (√(2π) s^(s-1/2) e^(-s)) - 1‖ ≤ 136 e^136/‖s‖`. -/
theorem Gamma_stirling_quotient_one {s : ℂ} (hs : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    ‖Gamma s / ((Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) * exp (-s)) - 1‖
      ≤ 136 * Real.exp 136 / ‖s‖ := by
  have hr : 0 < ‖s‖ := by linarith
  rw [← exp_stirMain (norm_pos_iff.mp hr), Gamma_eq_exp_stirMain_add hs hs1, exp_add,
    mul_div_cancel_left₀ _ (exp_ne_zero _)]
  have hR := norm_stirR_le' hs hs1
  have hR2 : ‖stirR s‖ ≤ 136 := hR.trans ((div_le_iff₀ hr).mpr (by linarith))
  calc ‖exp (stirR s) - 1‖ ≤ ‖stirR s‖ * Real.exp ‖stirR s‖ := norm_exp_sub_one_le_mul_exp _
    _ ≤ 136 / ‖s‖ * Real.exp 136 := by gcongr
    _ = 136 * Real.exp 136 / ‖s‖ := by ring

/-- There is `C > 0` with `‖Γ(s) / (√(2π) s^(s-1/2) e^(-s)) - 1‖ ≤ C/‖s‖` for all `s` with
`Re s ≥ 0` and `‖s‖ ≥ 1`. -/
theorem exists_Gamma_stirling_quotient :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
      ‖Gamma s / ((Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) * exp (-s)) - 1‖ ≤ C / ‖s‖ :=
  ⟨136 * Real.exp 136, by positivity, fun _ hs hs1 => Gamma_stirling_quotient_one hs hs1⟩

end StirlingScratch
