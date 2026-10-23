module

public import RiemannJensen.Dedekind.FieldSaddleDefinitions
public import Mathlib

/-!
# Sectorial Stirling estimate for the Dedekind Gamma remainder

For `|arg w| ≤ 2π/3` and `‖w‖` large,
`g_K(w) = (1 - 1/(4w²)) g_ℝ(w)^{r₁} g_ℂ(w)^{r₂} = 1 + O_K(‖w‖⁻¹)`, with explicit constants.

The proof is a native complex Stirling formula in the sector `Re z ≥ -‖z‖/2`
(equivalently `|arg z| ≤ 2π/3`), obtained from Euler's limit
`Γ(s) = lim n^s n! / (s(s+1)⋯(s+n))` by telescoping the one-step defects
`stirD (s + j)`, each of size `O(‖s + j‖⁻²)`.

## Main definitions

* `stirMain`: the Stirling main term `(z - 1/2) log z - z + log(2π)/2`.
* `stirR`: the Stirling remainder `∑_{j ≥ 0} stirD (s + j)`.
* `shiftedQuotient`: the shifted Stirling quotient `Γ(z + a) / (√(2π) z^(z + a - 1/2) e^(-z))`.
* `remainderConst`: the explicit constant `1 + 156 r₁ 2^{r₁} + 78 r₂ 2^{r₂}`.

## Main results

* `Gamma_eq_exp_stirMain_add`: `Γ(s) = exp (stirMain s + stirR s)` on the sector, `‖s‖ ≥ 8`.
* `norm_shiftedQuotient_sub_one_le`: `‖shiftedQuotient a z - 1‖ ≤ 39/‖z‖` for `0 ≤ a ≤ 1/2`.
* `norm_dedekindGammaRemainder_sub_one_le`: the explicit sectorial bound on `g_K(w) - 1`.
* `dedekindGammaRemainder_tends_one`: `g_K(w) = 1 + O_K(‖w‖⁻¹)` uniformly on the sector.
* `dedekindGammaRemainder_near_one`: far out in the sector, `g_K(w)` is within `1/2` of one.
-/

@[expose] public section

open Complex Filter Topology Finset
open scoped ComplexOrder

namespace RiemannJensen

namespace GammaSector

/-! ### Sector geometry -/

/-- `cos (2π/3) = -1/2`. -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

/-- A point of the closed sector `|arg w| ≤ 2π/3` satisfies `-‖w‖/2 ≤ Re w`. -/
theorem re_ge_of_abs_arg_le {w : ℂ} (hw : |arg w| ≤ 2 * Real.pi / 3) :
    -(‖w‖ / 2) ≤ w.re := by
  have hpi := Real.pi_pos
  have h1 : Real.cos (2 * Real.pi / 3) ≤ Real.cos |arg w| :=
    Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, abs_arg_le_pi w⟩
      ⟨by positivity, by linarith⟩ hw
  rw [Real.cos_abs, cos_two_pi_div_three] at h1
  nlinarith [norm_nonneg w, norm_mul_cos_arg w]

/-- If `cos θ · ‖x‖ < Re x` with `θ ∈ [0, π]`, then `|arg x| < θ`. -/
theorem abs_arg_lt_of_cos_mul_lt {x : ℂ} (hx : x ≠ 0) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (h : Real.cos θ * ‖x‖ < x.re) : |arg x| < θ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc : Real.cos θ < Real.cos |arg x| := by
    rwa [Real.cos_abs, cos_arg hx, lt_div_iff₀ hn]
  by_contra! hcon
  have := Real.strictAntiOn_cos.antitoneOn ⟨h0, hπ⟩ ⟨abs_nonneg _, abs_arg_le_pi x⟩ hcon
  linarith

/-- `1 + u ≠ 0` when `‖u‖ < 1`. -/
theorem one_add_ne_zero_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) : 1 + u ≠ 0 := fun h => by
  have := congrArg Complex.re h
  simp only [add_re, one_re, zero_re] at this
  linarith [(abs_le.mp (Complex.abs_re_le_norm u)).1]

/-- `‖arg (1 + u)‖ < π/3` when `‖u‖ ≤ 1/4`. -/
theorem abs_arg_one_add_lt {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) : |arg (1 + u)| < Real.pi / 3 := by
  have hre : 1 - ‖u‖ ≤ (1 + u).re := by
    simp only [add_re, one_re]
    linarith [(abs_le.mp (Complex.abs_re_le_norm u)).1]
  have hn : ‖1 + u‖ ≤ 1 + ‖u‖ := (norm_add_le _ _).trans (by rw [norm_one])
  refine abs_arg_lt_of_cos_mul_lt (one_add_ne_zero_of_norm_lt_one (by linarith)) (by positivity)
    (by linarith [Real.pi_pos]) ?_
  rw [Real.cos_pi_div_three]
  nlinarith [norm_nonneg u]

/-- A nonzero point with `-‖z‖/2 ≤ Re z` lies in the closed sector `|arg z| ≤ 2π/3`. -/
theorem abs_arg_le_of_re_ge {z : ℂ} (hz : -(‖z‖ / 2) ≤ z.re) (hz0 : z ≠ 0) :
    |arg z| ≤ 2 * Real.pi / 3 := by
  have hpi := Real.pi_pos
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  by_contra! hcon
  have hcos : Real.cos |arg z| < Real.cos (2 * Real.pi / 3) :=
    Real.strictAntiOn_cos ⟨by positivity, by linarith⟩ ⟨abs_nonneg _, abs_arg_le_pi z⟩ hcon
  rw [Real.cos_abs, cos_two_pi_div_three, cos_arg hz0, div_lt_iff₀ hn] at hcos
  linarith

/-- On the sector, `log (z (1 + u)) = log z + log (1 + u)` for `‖u‖ ≤ 1/4`. -/
theorem log_mul_one_add {z u : ℂ} (hz : -(‖z‖ / 2) ≤ z.re) (hz0 : z ≠ 0) (hu : ‖u‖ ≤ 1 / 4) :
    Complex.log (z * (1 + u)) = Complex.log z + Complex.log (1 + u) := by
  obtain ⟨h1l, h1r⟩ := abs_le.mp (abs_arg_le_of_re_ge hz hz0)
  obtain ⟨h2l, h2r⟩ := abs_lt.mp (abs_arg_one_add_lt hu)
  exact log_mul hz0 (one_add_ne_zero_of_norm_lt_one (by linarith)) ⟨by linarith, by linarith⟩

/-- The sector `Re z ≥ -‖z‖/2` is stable under adding a nonnegative real. -/
theorem sector_add_real {z : ℂ} (hz : -(‖z‖ / 2) ≤ z.re) {a : ℝ} (ha : 0 ≤ a) :
    -(‖z + a‖ / 2) ≤ (z + a).re := by
  rw [show (z + a).re = z.re + a by simp]
  rcases le_or_gt 0 (z.re + a) with h | h
  · linarith [norm_nonneg (z + a)]
  · have hsq : ‖z + a‖ ^ 2 = (z.re + a) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      simp
      ring
    have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      ring
    have hx : z.re < 0 := by linarith
    have h4 : 4 * z.re ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h5 : (z.re + a) ^ 2 ≤ z.re ^ 2 := by nlinarith
    have h6 : 4 * (z.re + a) ^ 2 ≤ ‖z + a‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (z + a)]

/-- On the sector, `(‖z‖ + a)/2 ≤ ‖z + a‖` for real `a ≥ 0`. -/
theorem norm_add_real_ge {z : ℂ} (hz : -(‖z‖ / 2) ≤ z.re) {a : ℝ} (ha : 0 ≤ a) :
    (‖z‖ + a) / 2 ≤ ‖z + a‖ := by
  have hsq : ‖z + a‖ ^ 2 = ‖z‖ ^ 2 + 2 * a * z.re + a ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp
    ring
  have h : ((‖z‖ + a) / 2) ^ 2 ≤ ‖z + a‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (‖z‖ - a), norm_nonneg z]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h

/-! ### The one-step Stirling defect on the sector -/

/-- Stirling main term `(z - 1/2) log z - z + log(2π)/2`, principal `log`. -/
noncomputable def stirMain (z : ℂ) : ℂ :=
  (z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)

/-- One-step defect: `stirMain (z+1) - stirMain z - log z`. -/
noncomputable def stirD (z : ℂ) : ℂ := stirMain (z + 1) - stirMain z - Complex.log z

/-- On the sector with `‖z‖ ≥ 4`, `stirD z = (z + 1/2) log (1 + z⁻¹) - 1`. -/
theorem stirD_eq {z : ℂ} (hz : -(‖z‖ / 2) ≤ z.re) (hz4 : 4 ≤ ‖z‖) :
    stirD z = (z + 1 / 2) * Complex.log (1 + z⁻¹) - 1 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hu : ‖z⁻¹‖ ≤ 1 / 4 := by
    rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hmul : z * (1 + z⁻¹) = z + 1 := by field_simp
  have hL := log_mul_one_add hz hz0 hu
  rw [hmul] at hL
  unfold stirD stirMain
  rw [hL]
  ring

/-- For `‖t‖ ≤ 1/2`, `‖log (1 + t) - t‖ ≤ ‖t‖²`. -/
theorem norm_log_one_add_sub_self_le_sq {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    ‖Complex.log (1 + t) - t‖ ≤ ‖t‖ ^ 2 := by
  have hinv : (1 - ‖t‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  calc _ ≤ ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ / 2 := norm_log_one_add_sub_self_le (by linarith)
    _ ≤ ‖t‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖t‖ ^ 2 := by ring

/-- For `0 < ‖w‖ ≤ 1/2`, `‖(w⁻¹ + 1/2) log(1+w) - 1‖ ≤ (7/6) ‖w‖²`. -/
theorem norm_defect_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) (hw0 : w ≠ 0) :
    ‖(w⁻¹ + 1 / 2) * Complex.log (1 + w) - 1‖ ≤ 7 / 6 * ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ < 1 := hw.trans_lt (by norm_num)
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  have hT : logTaylor 3 w = w - w ^ 2 / 2 := by
    simp [logTaylor_succ, logTaylor_zero]
    ring
  have hA := norm_log_sub_logTaylor_le 2 hw1
  rw [hT] at hA
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
        · exact (norm_log_one_add_sub_self_le_sq hw).trans_eq (by ring)
    _ = 7 / 6 * ‖w‖ ^ 2 := by
        field_simp
        ring

/-- `‖stirD z‖ ≤ (7/6)/‖z‖²` on the sector, `‖z‖ ≥ 4`. -/
theorem norm_stirD_le {z : ℂ} (hz : -(‖z‖ / 2) ≤ z.re) (hz4 : 4 ≤ ‖z‖) :
    ‖stirD z‖ ≤ 7 / 6 / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [stirD_eq hz hz4]
  have hw : ‖z⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h := norm_defect_le hw (inv_ne_zero hz0)
  rw [inv_inv, norm_inv] at h
  calc _ ≤ 7 / 6 * ‖z‖⁻¹ ^ 2 := h
    _ = 7 / 6 / ‖z‖ ^ 2 := by ring

/-- `‖stirD (s + j)‖ ≤ (14/3) / (‖s‖ + j)²` on the sector, `‖s‖ ≥ 8`. -/
theorem norm_stirD_add_le {s : ℂ} (hs : -(‖s‖ / 2) ≤ s.re) (hs8 : 8 ≤ ‖s‖) (j : ℕ) :
    ‖stirD (s + j)‖ ≤ 14 / 3 * (1 / (‖s‖ + j) ^ 2) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsec := sector_add_real hs hj
  have hn := norm_add_real_ge hs hj
  push_cast at hsec hn
  have hpos : 0 < ‖s‖ + j := by positivity
  have h4 : 4 ≤ ‖s + j‖ := by linarith
  have h2 : (‖s‖ + j) ^ 2 / 4 ≤ ‖s + j‖ ^ 2 := by nlinarith
  calc ‖stirD (s + j)‖ ≤ 7 / 6 / ‖s + j‖ ^ 2 := norm_stirD_le hsec h4
    _ ≤ 7 / 6 / ((‖s‖ + j) ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
    _ = 14 / 3 * (1 / (‖s‖ + j) ^ 2) := by
      field_simp
      ring

/-! ### Summation -/

/-- For `r > 0`, `∑_{j ≤ n} 1/(r + j)² ≤ 1/r² + 1/r - 1/(r + n)`. -/
theorem sum_inv_sq_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
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

/-- For `r > 0`, `∑_{j < n} 1/(r + j)² ≤ 1/r² + 1/r`. -/
theorem sum_inv_sq_le' {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ j ∈ range n, 1 / (r + j) ^ 2 ≤ 1 / r ^ 2 + 1 / r := by
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  · linarith [sum_inv_sq_le hr n, (by positivity : (0 : ℝ) ≤ 1 / (r + n))]

/-- For `r > 0`, the series `∑_j c / (r + j)²` is summable. -/
theorem summable_bound {r : ℝ} (hr : 0 < r) (c : ℝ) :
    Summable (fun j : ℕ => c * (1 / (r + j) ^ 2)) :=
  (summable_of_sum_range_le (c := 1 / r ^ 2 + 1 / r) (fun j => by positivity)
    (fun n => sum_inv_sq_le' hr n)).mul_left _

/-- For `r > 0` and `c ≥ 0`, `∑_j c / (r + j)² ≤ c (1/r² + 1/r)`. -/
theorem tsum_bound_le {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : 0 ≤ c) :
    ∑' j : ℕ, c * (1 / (r + j) ^ 2) ≤ c * (1 / r ^ 2 + 1 / r) := by
  rw [tsum_mul_left]
  gcongr
  exact Real.tsum_le_of_sum_range_le (fun j => by positivity) (fun n => sum_inv_sq_le' hr n)

/-- The Stirling remainder `R(s) = ∑_{j ≥ 0} stirD (s + j)`. -/
noncomputable def stirR (s : ℂ) : ℂ := ∑' j : ℕ, stirD (s + j)

/-- On the sector with `‖s‖ ≥ 8`, the defects `stirD (s + j)` are summable over `j`. -/
theorem summable_stirD {s : ℂ} (hs : -(‖s‖ / 2) ≤ s.re) (hs8 : 8 ≤ ‖s‖) :
    Summable (fun j : ℕ => stirD (s + j)) :=
  Summable.of_norm_bounded (summable_bound (by linarith) (14 / 3)) (norm_stirD_add_le hs hs8)

/-- `‖R(s)‖ ≤ 6/‖s‖` on the sector, `‖s‖ ≥ 8`. -/
theorem norm_stirR_le {s : ℂ} (hs : -(‖s‖ / 2) ≤ s.re) (hs8 : 8 ≤ ‖s‖) :
    ‖stirR s‖ ≤ 6 / ‖s‖ := by
  have hr : 0 < ‖s‖ := by linarith
  have h1 : ‖stirR s‖ ≤ ∑' j : ℕ, 14 / 3 * (1 / (‖s‖ + j) ^ 2) :=
    tsum_of_norm_bounded (summable_bound hr _).hasSum (norm_stirD_add_le hs hs8)
  have h3 : 14 / 3 * (1 / ‖s‖ ^ 2 + 1 / ‖s‖) ≤ 6 / ‖s‖ := by
    rw [div_add_div _ _ (by positivity) hr.ne', mul_div_assoc', div_le_div_iff₀ (by positivity) hr]
    nlinarith
  linarith [tsum_bound_le hr (c := 14 / 3) (by norm_num)]

/-! ### Euler's limit and the boundary bracket -/

/-- `n log (1 + a/n) → a` as `n → ∞`. -/
theorem tendsto_mul_log_one_add_div (a : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (1 + a / n)) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (‖a‖ ^ 2))
  filter_upwards [eventually_ge_atTop ⌈2 * ‖a‖ + 1⌉₊] with n hn
  have hnR : 2 * ‖a‖ + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hn0 : 0 < (n : ℝ) := by linarith [norm_nonneg a]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hw : ‖a / n‖ = ‖a‖ / n := by rw [norm_div, Complex.norm_natCast]
  have hw1 : ‖a / n‖ ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ hn0]
    linarith
  have hid : (n : ℂ) * Complex.log (1 + a / n) - a = n * (Complex.log (1 + a / n) - a / n) := by
    field_simp
  rw [hid, norm_mul, Complex.norm_natCast]
  calc (n : ℝ) * ‖Complex.log (1 + a / n) - a / n‖
      ≤ n * ‖a / n‖ ^ 2 := by
        gcongr
        exact norm_log_one_add_sub_self_le_sq hw1
    _ = ‖a‖ ^ 2 / n := by
        rw [hw]
        field_simp

/-- `log (1 + a/n) → 0` as `n → ∞`. -/
theorem tendsto_log_one_add_div (a : ℂ) :
    Tendsto (fun n : ℕ => Complex.log (1 + a / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + a / (n : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat a)
  have := (continuousAt_clog (by simp [slitPlane])).tendsto.comp h1
  rwa [Complex.log_one] at this

/-- Stirling's formula in logarithmic form: `log (stirlingSeq n) - log π / 2 → 0`. -/
theorem tendsto_log_stirlingSeq_sub_half_log_pi :
    Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2)
      atTop (𝓝 0) := by
  have hc : ContinuousAt Real.log (√Real.pi) :=
    Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have :=
    (hc.tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi).sub_const (Real.log Real.pi / 2)
  rwa [Function.comp_def, Real.log_sqrt Real.pi_pos.le, sub_self] at this

/-- For `‖s‖ + 1 ≤ n`, the boundary bracket `s log n + log n! - stirMain (s + n + 1)` splits
into the Stirling defect `log (stirlingSeq n) - log π / 2` and terms in `log (1 + (s + 1)/n)`. -/
theorem bracket_eq {s : ℂ} {n : ℕ} (hnR : ‖s‖ + 1 ≤ (n : ℝ)) :
    s * (Real.log n : ℂ) + (Real.log (n.factorial) : ℂ) - stirMain (s + n + 1) =
      ((Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 : ℝ) : ℂ) + (s + 1)
        - (s + 1 / 2) * Complex.log (1 + (s + 1) / n) - n * Complex.log (1 + (s + 1) / n) := by
  have hn0 : (0 : ℝ) < n := by linarith [norm_nonneg s]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hfac : Real.log (n.factorial) = Real.log (Stirling.stirlingSeq n)
      + (Real.log 2 + Real.log n) / 2 + n * (Real.log n - 1) := by
    rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hn0.ne',
      Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have h2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  have e : s + n + 1 = ((n : ℝ) : ℂ) * (1 + (s + 1) / n) := by
    push_cast
    field_simp
    ring
  have hw0 : (1 + (s + 1) / n) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re (show s + n + 1 = 0 by rw [e, h, mul_zero])
    simp only [add_re, natCast_re, one_re, zero_re] at hre
    linarith [(abs_le.mp (Complex.abs_re_le_norm s)).1]
  have hlog : Complex.log (s + n + 1) = (Real.log n : ℂ) + Complex.log (1 + (s + 1) / n) := by
    rw [e, log_ofReal_mul hn0 hw0]
  simp only [stirMain]
  rw [show s + n + 1 - 1 / 2 = s + n + 1 / 2 by ring, hlog, hfac, h2pi]
  push_cast
  ring

/-- The boundary bracket `s log n + log n! - stirMain (s + n + 1) → 0`, for every `s`. -/
theorem tendsto_bracket (s : ℂ) :
    Tendsto (fun n : ℕ => s * (Real.log n : ℂ) + (Real.log (n.factorial) : ℂ)
      - stirMain (s + n + 1)) atTop (𝓝 0) := by
  have hS' := (continuous_ofReal.tendsto 0).comp tendsto_log_stirlingSeq_sub_half_log_pi
  rw [ofReal_zero] at hS'
  have hF := ((hS'.add_const (s + 1)).sub
    ((tendsto_log_one_add_div (s + 1)).const_mul (s + 1 / 2))).sub
      (tendsto_mul_log_one_add_div (s + 1))
  simp only [Function.comp_def, mul_zero, sub_zero, zero_add, sub_self] at hF
  refine hF.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖s‖ + 1⌉₊] with n hn
  exact (bracket_eq ((Nat.le_ceil _).trans (by exact_mod_cast hn))).symm

/-- Partial sums `L_n(s) = s log n + log n! - ∑_{j ≤ n} log (s + j)`. -/
noncomputable def logGammaSeq (s : ℂ) (n : ℕ) : ℂ :=
  s * (Real.log n : ℂ) + (Real.log n.factorial : ℂ) - ∑ j ∈ range (n + 1), Complex.log (s + j)

/-- If no `s + j` vanishes, then `exp (logGammaSeq s n) = GammaSeq s n` for `n ≠ 0`. -/
theorem exp_logGammaSeq {s : ℂ} (hne : ∀ j : ℕ, s + j ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    exp (logGammaSeq s n) = GammaSeq s n := by
  unfold logGammaSeq GammaSeq
  rw [exp_sub, exp_add, exp_sum]
  congr 1
  · congr 1
    · rw [natCast_log, cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), mul_comm s (log (n : ℂ))]
    · rw [natCast_log, exp_log (by exact_mod_cast n.factorial_ne_zero)]
  · exact Finset.prod_congr rfl fun m _ => exp_log (hne m)

/-- `logGammaSeq s n` equals the boundary bracket plus `stirMain s` plus the partial sum
`∑_{j ≤ n} stirD (s + j)`. -/
theorem logGammaSeq_eq (s : ℂ) (n : ℕ) :
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

/-- **Sectorial Binet-type identity.** On `Re s ≥ -‖s‖/2`, `‖s‖ ≥ 8`:
`Γ(s) = exp (stirMain s + stirR s)`. -/
theorem Gamma_eq_exp_stirMain_add {s : ℂ} (hs : -(‖s‖ / 2) ≤ s.re) (hs8 : 8 ≤ ‖s‖) :
    Gamma s = exp (stirMain s + stirR s) := by
  have hne : ∀ j : ℕ, s + j ≠ 0 := fun j h => by
    have := norm_add_real_ge hs (Nat.cast_nonneg j)
    push_cast at this
    rw [h, norm_zero] at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hsum := (summable_stirD hs hs8).hasSum
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

/-- `√(2π) = exp (log(2π)/2)`, as complex numbers. -/
theorem sqrt_two_pi_eq :
    ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = exp ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  rw [← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
  congr 2
  ring

/-! ### The shifted Stirling quotient on the sector -/

/-- The shifted Stirling quotient `Γ(z + a) / (√(2π) z^(z + a - 1/2) e^(-z))`. -/
noncomputable def shiftedQuotient (a : ℝ) (z : ℂ) : ℂ :=
  Gamma (z + a) / ((Real.sqrt (2 * Real.pi) : ℂ) * z ^ (z + a - 1 / 2) * exp (-z))

/-- The explicit logarithm `R(z + a) + (z + a - 1/2) log (1 + a/z) - a` of
`shiftedQuotient a z`. -/
noncomputable def shiftedLog (a : ℝ) (z : ℂ) : ℂ :=
  stirR (z + a) + (z + a - 1 / 2) * Complex.log (1 + a / z) - a

/-- For `0 ≤ a ≤ 1/2`, on the sector with `‖z‖ ≥ 16`,
`shiftedQuotient a z = exp (shiftedLog a z)`. -/
theorem shiftedQuotient_eq_exp {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) {z : ℂ}
    (hz : -(‖z‖ / 2) ≤ z.re) (hz16 : 16 ≤ ‖z‖) :
    shiftedQuotient a z = exp (shiftedLog a z) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hsec := sector_add_real hz ha0
  have hn := norm_add_real_ge hz ha0
  have hs8 : 8 ≤ ‖z + a‖ := by linarith
  have hu : ‖(a : ℂ) / z‖ ≤ 1 / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0,
      div_le_iff₀ (by linarith)]
    linarith
  have hmul : z * (1 + (a : ℂ) / z) = z + a := by field_simp
  have hL := log_mul_one_add hz hz0 hu
  rw [hmul] at hL
  rw [shiftedQuotient, Gamma_eq_exp_stirMain_add hsec hs8, sqrt_two_pi_eq,
    cpow_def_of_ne_zero hz0, ← exp_add, ← exp_add, ← exp_sub]
  congr 1
  unfold shiftedLog stirMain
  rw [hL]
  ring

/-- For `0 ≤ a ≤ 1/2` and `‖z‖ ≥ 16`, `‖(z + a - 1/2) log (1 + a/z) - a‖ ≤ 1/‖z‖`. -/
theorem norm_mul_log_one_add_div_sub_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) {z : ℂ}
    (hz16 : 16 ≤ ‖z‖) :
    ‖(z + a - 1 / 2) * Complex.log (1 + a / z) - a‖ ≤ 1 / ‖z‖ := by
  have hnz : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hnz
  set t : ℂ := (a : ℂ) / z with ht
  have htn : ‖t‖ = a / ‖z‖ := by
    rw [ht, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  have ht2 : ‖t‖ ≤ 1 / (2 * ‖z‖) := by
    rw [htn, div_le_div_iff₀ hnz (by positivity)]
    nlinarith
  have hthalf : ‖t‖ ≤ 1 / 2 := by
    refine ht2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hB := norm_log_one_add_sub_self_le_sq hthalf
  have hC := norm_log_one_add_half_le_self hthalf
  have hzt : z * t = a := by
    rw [ht]
    field_simp
  have hid : (z + a - 1 / 2) * Complex.log (1 + t) - a =
      z * (Complex.log (1 + t) - t) + ((a : ℂ) - 1 / 2) * Complex.log (1 + t) := by
    rw [mul_sub z, hzt]
    ring
  have ha2 : ‖((a : ℂ) - 1 / 2)‖ ≤ 1 / 2 := by
    rw [show ((a : ℂ) - 1 / 2) = ((a - 1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rw [hid]
  calc ‖z * (Complex.log (1 + t) - t) + ((a : ℂ) - 1 / 2) * Complex.log (1 + t)‖
      ≤ ‖z‖ * ‖t‖ ^ 2 + 1 / 2 * (3 / 2 * ‖t‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        gcongr
    _ ≤ ‖z‖ * (1 / (2 * ‖z‖)) ^ 2 + 1 / 2 * (3 / 2 * (1 / (2 * ‖z‖))) := by gcongr
    _ = 5 / 8 / ‖z‖ := by
      field_simp
      ring
    _ ≤ 1 / ‖z‖ := by
      gcongr
      norm_num

/-- `‖shiftedLog a z‖ ≤ 13/‖z‖` on the sector, `‖z‖ ≥ 16`, `0 ≤ a ≤ 1/2`. -/
theorem norm_shiftedLog_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) {z : ℂ}
    (hz : -(‖z‖ / 2) ≤ z.re) (hz16 : 16 ≤ ‖z‖) :
    ‖shiftedLog a z‖ ≤ 13 / ‖z‖ := by
  have hnz : 0 < ‖z‖ := by linarith
  have hn := norm_add_real_ge hz ha0
  have hR : ‖stirR (z + a)‖ ≤ 12 / ‖z‖ := by
    refine (norm_stirR_le (sector_add_real hz ha0) (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by linarith) hnz]
    nlinarith
  unfold shiftedLog
  rw [add_sub_assoc]
  exact (norm_add_le _ _).trans
    ((add_le_add hR (norm_mul_log_one_add_div_sub_le ha0 ha hz16)).trans_eq (by ring))

/-- **Sectorial shifted Stirling.** For `0 ≤ a ≤ 1/2`, `Re z ≥ -‖z‖/2` and `‖z‖ ≥ 16`,
`‖Γ(z + a) / (√(2π) z^(z + a - 1/2) e^(-z)) - 1‖ ≤ 39/‖z‖`. -/
theorem norm_shiftedQuotient_sub_one_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) {z : ℂ}
    (hz : -(‖z‖ / 2) ≤ z.re) (hz16 : 16 ≤ ‖z‖) :
    ‖shiftedQuotient a z - 1‖ ≤ 39 / ‖z‖ := by
  have hnz : 0 < ‖z‖ := by linarith
  rw [shiftedQuotient_eq_exp ha0 ha hz hz16]
  have hL := norm_shiftedLog_le ha0 ha hz hz16
  have hE := norm_exp_sub_sum_le_norm_mul_exp (shiftedLog a z) 1
  simp only [range_one, sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at hE
  have hL1 : ‖shiftedLog a z‖ ≤ 1 := hL.trans ((div_le_iff₀ hnz).mpr (by linarith))
  have hexp : Real.exp ‖shiftedLog a z‖ ≤ 3 :=
    (Real.exp_le_exp.mpr hL1).trans (by linarith [Real.exp_one_lt_d9])
  calc ‖exp (shiftedLog a z) - 1‖ ≤ ‖shiftedLog a z‖ * Real.exp ‖shiftedLog a z‖ := hE
    _ ≤ 13 / ‖z‖ * 3 := by gcongr
    _ = 39 / ‖z‖ := by ring

/-! ### The real and complex Gamma remainders -/

/-- `Complex.sqrt (2π) = √(2π)`, as complex numbers. -/
theorem complex_sqrt_two_mul_pi :
    Complex.sqrt ((2 : ℂ) * Real.pi) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
  have hnonneg : 0 ≤ (((2 * Real.pi : ℝ) : ℂ)) :=
    RCLike.nonneg_iff_exists_ofReal.mpr ⟨2 * Real.pi, by positivity, rfl⟩
  rw [show (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
    Complex.sqrt_of_nonneg hnonneg]
  norm_num

/-- `g_ℝ(w)` is the shifted Stirling quotient with shift `1/4` at `w/2`. -/
theorem dedekindGammaRemainderReal_eq (w : ℂ) :
    dedekindGammaRemainderReal w = shiftedQuotient (1 / 4) (w / 2) := by
  unfold dedekindGammaRemainderReal shiftedQuotient
  rw [complex_sqrt_two_mul_pi,
    show Complex.cpow (w / 2) (w / 2 - 1 / 4) = (w / 2) ^ (w / 2 - 1 / 4) from rfl]
  have e1 : w / 2 + ((1 / 4 : ℝ) : ℂ) = w / 2 + 1 / 4 := by push_cast; ring
  rw [e1, show w / 2 + 1 / 4 - 1 / 2 = w / 2 - 1 / 4 by ring, neg_div]

/-- `g_ℂ(w)` is the shifted Stirling quotient with shift `1/2` at `w`. -/
theorem dedekindGammaRemainderComplex_eq (w : ℂ) :
    dedekindGammaRemainderComplex w = shiftedQuotient (1 / 2) w := by
  unfold dedekindGammaRemainderComplex shiftedQuotient
  rw [complex_sqrt_two_mul_pi, show Complex.cpow w w = w ^ w from rfl]
  have e1 : w + ((1 / 2 : ℝ) : ℂ) = w + 1 / 2 := by push_cast; ring
  rw [e1, show w + 1 / 2 - 1 / 2 = w by ring]

/-- `‖g_ℝ(w) - 1‖ ≤ 78/‖w‖` for `|arg w| ≤ 2π/3`, `‖w‖ ≥ 32`. -/
theorem norm_dedekindGammaRemainderReal_sub_one_le {w : ℂ} (hw : |arg w| ≤ 2 * Real.pi / 3)
    (hw32 : 32 ≤ ‖w‖) : ‖dedekindGammaRemainderReal w - 1‖ ≤ 78 / ‖w‖ := by
  have hsec := re_ge_of_abs_arg_le hw
  have hn : ‖w / 2‖ = ‖w‖ / 2 := by rw [norm_div]; norm_num
  have hsec2 : -(‖w / 2‖ / 2) ≤ (w / 2).re := by
    rw [hn]
    simp only [div_re]
    norm_num
    linarith
  have h16 : 16 ≤ ‖w / 2‖ := by
    rw [hn]
    linarith
  rw [dedekindGammaRemainderReal_eq]
  refine (norm_shiftedQuotient_sub_one_le (by norm_num) (by norm_num) hsec2 h16).trans ?_
  rw [hn]
  have : 0 < ‖w‖ := by linarith
  field_simp
  norm_num

/-- `‖g_ℂ(w) - 1‖ ≤ 39/‖w‖` for `|arg w| ≤ 2π/3`, `‖w‖ ≥ 16`. -/
theorem norm_dedekindGammaRemainderComplex_sub_one_le {w : ℂ} (hw : |arg w| ≤ 2 * Real.pi / 3)
    (hw16 : 16 ≤ ‖w‖) : ‖dedekindGammaRemainderComplex w - 1‖ ≤ 39 / ‖w‖ := by
  rw [dedekindGammaRemainderComplex_eq]
  exact norm_shiftedQuotient_sub_one_le (by norm_num) (by norm_num) (re_ge_of_abs_arg_le hw) hw16

/-! ### Products and powers near one -/

/-- If `‖x - 1‖ ≤ ε ≤ 1` and `‖y - 1‖ ≤ δ`, then `‖x y - 1‖ ≤ ε + 2δ`. -/
theorem norm_mul_sub_one_le {x y : ℂ} {ε δ : ℝ} (hx : ‖x - 1‖ ≤ ε) (hy : ‖y - 1‖ ≤ δ)
    (hε : ε ≤ 1) : ‖x * y - 1‖ ≤ ε + 2 * δ := by
  have hid : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hy
  rw [hid]
  calc ‖(x - 1) * (y - 1) + (x - 1) + (y - 1)‖
      ≤ ‖x - 1‖ * ‖y - 1‖ + ‖x - 1‖ + ‖y - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [← norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ ε * δ + ε + δ := by
        gcongr
        exact (norm_nonneg _).trans hx
    _ ≤ ε + 2 * δ := by nlinarith

/-- If `‖x - 1‖ ≤ ε ≤ 1`, then `‖xⁿ - 1‖ ≤ n 2ⁿ ε`. -/
theorem norm_pow_sub_one_le {x : ℂ} {ε : ℝ} (hx : ‖x - 1‖ ≤ ε) (hε : ε ≤ 1) (n : ℕ) :
    ‖x ^ n - 1‖ ≤ n * 2 ^ n * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hx
  have hxn : ‖x‖ ≤ 2 := by linarith [norm_sub_norm_le x 1, (norm_one : ‖(1 : ℂ)‖ = 1)]
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : x ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
    rw [hid]
    calc ‖x * (x ^ n - 1) + (x - 1)‖ ≤ ‖x‖ * ‖x ^ n - 1‖ + ‖x - 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ 2 * (n * 2 ^ n * ε) + ε := by gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * ε := by
          push_cast
          have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
          have e : ((n : ℝ) + 1) * 2 ^ (n + 1) * ε = 2 * (n * 2 ^ n * ε) + 2 * 2 ^ n * ε := by ring
          rw [e]
          nlinarith

/-! ### The Dedekind Gamma remainder -/

/-- The explicit constant `C(r₁, r₂) = 1 + 156 r₁ 2^{r₁} + 78 r₂ 2^{r₂}`. -/
noncomputable def remainderConst (r₁ r₂ : ℕ) : ℝ :=
  1 + 2 * ((r₁ : ℝ) * 2 ^ r₁ * 78) + 2 * ((r₂ : ℝ) * 2 ^ r₂ * 39)

/-- `1 ≤ remainderConst r₁ r₂`. -/
theorem one_le_remainderConst (r₁ r₂ : ℕ) : 1 ≤ remainderConst r₁ r₂ := by
  unfold remainderConst
  have h1 : (0 : ℝ) ≤ 2 * ((r₁ : ℝ) * 2 ^ r₁ * 78) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * ((r₂ : ℝ) * 2 ^ r₂ * 39) := by positivity
  linarith

/-- For `|arg w| ≤ 2π/3` and `‖w‖ ≥ max 78 C`, where `C = remainderConst r₁ r₂`,
`‖dedekindGammaRemainder K w - 1‖ ≤ C/‖w‖`. -/
theorem norm_dedekindGammaRemainder_sub_one_le
    (K : Type) [Field K] [NumberField K] {w : ℂ}
    (hw : |arg w| ≤ 2 * Real.pi / 3)
    (hW : max 78 (remainderConst (dedekindRealPlaces K)
      (dedekindComplexPlaces K)) ≤ ‖w‖) :
    ‖dedekindGammaRemainder K w - 1‖ ≤
      remainderConst (dedekindRealPlaces K) (dedekindComplexPlaces K) / ‖w‖ := by
  let r₁ := dedekindRealPlaces K
  let r₂ := dedekindComplexPlaces K
  have h78 : 78 ≤ ‖w‖ := (le_max_left _ _).trans hW
  have hC : remainderConst r₁ r₂ ≤ ‖w‖ := (le_max_right _ _).trans hW
  have hnw : 0 < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := norm_pos_iff.mp hnw
  have hP : ‖(1 - 1 / (4 * w ^ 2)) - 1‖ ≤ 1 / ‖w‖ := by
    rw [sub_sub_cancel_left, norm_neg, norm_div, norm_one, norm_mul, norm_pow,
      show ‖(4 : ℂ)‖ = 4 by norm_num, div_le_div_iff₀ (by positivity) hnw]
    nlinarith
  have hP1 : 1 / ‖w‖ ≤ 1 := (div_le_one hnw).mpr (by linarith)
  have hR := norm_dedekindGammaRemainderReal_sub_one_le hw (by linarith)
  have hR1 : 78 / ‖w‖ ≤ 1 := (div_le_one hnw).mpr (by linarith)
  have hRp := norm_pow_sub_one_le hR hR1 r₁
  have hCx := norm_dedekindGammaRemainderComplex_sub_one_le hw (by linarith)
  have hC1 : 39 / ‖w‖ ≤ 1 := (div_le_one hnw).mpr (by linarith)
  have hCp := norm_pow_sub_one_le hCx hC1 r₂
  have h1 := norm_mul_sub_one_le hP hRp hP1
  have hA1 : 1 / ‖w‖ + 2 * (r₁ * 2 ^ r₁ * (78 / ‖w‖)) ≤ 1 :=
    calc 1 / ‖w‖ + 2 * (r₁ * 2 ^ r₁ * (78 / ‖w‖))
        = (1 + 2 * ((r₁ : ℝ) * 2 ^ r₁ * 78)) / ‖w‖ := by field_simp
      _ ≤ remainderConst r₁ r₂ / ‖w‖ := by
        refine div_le_div_of_nonneg_right ?_ hnw.le
        unfold remainderConst
        linarith [show (0 : ℝ) ≤ 2 * ((r₂ : ℝ) * 2 ^ r₂ * 39) by positivity]
      _ ≤ 1 := (div_le_one hnw).mpr hC
  have h2 := norm_mul_sub_one_le h1 hCp hA1
  unfold dedekindGammaRemainder
  change ‖((1 - 1 / (4 * w ^ 2)) * dedekindGammaRemainderReal w ^ r₁) *
      dedekindGammaRemainderComplex w ^ r₂ - 1‖ ≤ remainderConst r₁ r₂ / ‖w‖
  refine h2.trans_eq ?_
  unfold remainderConst
  field_simp

/-- Uniformly on the closed sector `|arg w| ≤ 2π/3`, `dedekindGammaRemainder K w` is
`1 + O_K(‖w‖⁻¹)`. -/
theorem dedekindGammaRemainder_tends_one
    (K : Type) [Field K] [NumberField K] :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ w : ℂ, |arg w| ≤ 2 * Real.pi / 3 → W ≤ ‖w‖ →
        ‖dedekindGammaRemainder K w - 1‖ ≤ C / ‖w‖ :=
  ⟨_, _, one_pos.trans_le (one_le_remainderConst _ _),
    (by norm_num : (0 : ℝ) < 78).trans_le (le_max_left 78 _),
    fun _ hw hW => norm_dedekindGammaRemainder_sub_one_le K hw hW⟩

/-- Sufficiently far out in the closed sector `|arg w| ≤ 2π/3`, `dedekindGammaRemainder K w`
is within `1/2` of one, and in particular nonzero. -/
theorem dedekindGammaRemainder_near_one
    (K : Type) [Field K] [NumberField K] :
    ∃ W : ℝ, 0 < W ∧
      ∀ w : ℂ, |arg w| ≤ 2 * Real.pi / 3 → W ≤ ‖w‖ →
        ‖dedekindGammaRemainder K w - 1‖ ≤ 1 / 2 ∧
          dedekindGammaRemainder K w ≠ 0 := by
  obtain ⟨C, W, hC, hW, h⟩ := dedekindGammaRemainder_tends_one K
  refine ⟨max W (2 * C), hW.trans_le (le_max_left _ _), fun w hw hwW => ?_⟩
  have hWw := (le_max_left _ _).trans hwW
  have hnw : 0 < ‖w‖ := hW.trans_le hWw
  have hb := h w hw hWw
  have hhalf : ‖dedekindGammaRemainder K w - 1‖ ≤ 1 / 2 := by
    refine hb.trans ?_
    rw [div_le_iff₀ hnw]
    have := (le_max_right _ _).trans hwW
    linarith
  refine ⟨hhalf, fun h0 => ?_⟩
  rw [h0, zero_sub, norm_neg, norm_one] at hhalf
  norm_num at hhalf

end GammaSector

end RiemannJensen
