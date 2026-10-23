module

public import RiemannJensen.Analysis.ZetaEulerFoundation

/-!
# A square-root bound for the Riemann zeta function

For `1 / 2 ≤ s.re`, the Euler–Maclaurin expression `riemannZeta0` truncated at `N` bounds
`‖riemannZeta s‖` by explicit terms in `N`. Taking `N = ⌈‖s‖⌉₊` gives `‖riemannZeta s‖ ≤ C * √‖s‖`
for `2 ≤ ‖s‖`.

## Main results

* `sum_one_div_sqrt_le`: `∑_{n ≤ N} 1 / √n ≤ 2 √N`.
* `norm_zeta_finite_sum_le`: the partial sum `∑_{n ≤ N} n ^ (-s)` has norm at most `2 √N` when
  `1 / 2 ≤ s.re`.
* `norm_riemannZeta_le_euler_terms`: an explicit bound on `‖riemannZeta s‖` in terms of `N`.
* `exists_global_riemannZeta_sqrt_bound`: `‖riemannZeta s‖ ≤ C * √‖s‖` on
  `{s | 1 / 2 ≤ s.re ∧ 2 ≤ ‖s‖}`.
-/

@[expose] public section

namespace RiemannJensen

open Set Filter MeasureTheory

private lemma one_div_sqrt_succ_le_two_mul_sub (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℝ) ≤ 2 * (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) := by
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity),
    Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n), Real.sqrt_nonneg (n : ℝ),
    Real.sqrt_le_sqrt (show (n : ℝ) ≤ n + 1 by linarith),
    sq_nonneg (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ))]

/-- For every `N`, `∑_{n = 0}^{N} 1 / √n ≤ 2 √N`, where the term `n = 0` is `0`. -/
lemma sum_one_div_sqrt_le (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [one_div_sqrt_succ_le_two_mul_sub N]

private lemma norm_one_div_nat_cpow_le_inv_sqrt (s : ℂ) (hs : 1 / 2 ≤ s.re) (n : ℕ) :
    ‖1 / (n : ℂ) ^ s‖ ≤ 1 / Real.sqrt (n : ℝ) := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs
    simp [Complex.zero_cpow hs0]
  rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn, Real.sqrt_eq_rpow]
  exact one_div_le_one_div_of_le (by positivity)
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hs)

/-- If `1 / 2 ≤ s.re`, then `‖∑_{n = 0}^{N} 1 / n ^ s‖ ≤ 2 √N`. -/
lemma norm_zeta_finite_sum_le (s : ℂ) (hs : 1 / 2 ≤ s.re) (N : ℕ) :
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ 2 * Real.sqrt N := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), ‖1 / (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), 1 / Real.sqrt (n : ℝ) :=
      Finset.sum_le_sum fun n _ ↦ norm_one_div_nat_cpow_le_inv_sqrt s hs n
    _ ≤ _ := sum_one_div_sqrt_le N

/-- If `1 / 2 ≤ s.re`, `s ≠ 1` and `1 ≤ N`, then
`‖ζ(s)‖ ≤ 2 √N + N ^ (1 - σ) / ‖1 - s‖ + N ^ (-σ) / 2 + ‖s‖ * (N ^ (-σ) / σ)`, where `σ = s.re`. -/
lemma norm_riemannZeta_le_euler_terms (s : ℂ) (hs : 1 / 2 ≤ s.re)
    (N : ℕ) (hN : 1 ≤ N) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤
      2 * Real.sqrt N + N ^ (1 - s.re) / ‖1 - s‖ + N ^ (-s.re) / 2 +
        ‖s‖ * (N ^ (-s.re) / s.re) := by
  have hspos : 0 < s.re := by linarith
  have hNpos : 0 < N := by omega
  rw [← riemannZeta0_eq_riemannZeta hNpos hspos hs1]
  unfold riemannZeta0
  apply le_trans norm_add₄_le
  have hsum := norm_zeta_finite_sum_le s hs N
  have hpow1 :
      ‖(-((N : ℂ) ^ (1 - s))) / (1 - s)‖ = N ^ (1 - s.re) / ‖1 - s‖ := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hNpos]
    simp
  have hpow0 : ‖(-((N : ℂ) ^ (-s))) / 2‖ = N ^ (-s.re) / 2 := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hNpos]
    norm_num
  have hI :
      ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
        ≤ N ^ (-s.re) / s.re := by
    simpa [Complex.re_add_im] using ZetaBnd_aux1b N hN (σ := s.re) (t := s.im) hspos
  rw [hpow1, hpow0, norm_mul]
  gcongr

private lemma ceil_sqrt_bounds {R : ℝ} (hR : 2 ≤ R) :
    Real.sqrt ⌈R⌉₊ ≤ 2 * Real.sqrt R ∧ R / Real.sqrt ⌈R⌉₊ ≤ Real.sqrt R := by
  have hR0 : 0 ≤ R := by linarith
  have hNR : (⌈R⌉₊ : ℝ) ≤ 2 * R := by linarith [Nat.ceil_lt_add_one hR0]
  have hNpos : (0 : ℝ) < ⌈R⌉₊ := by linarith [Nat.le_ceil R]
  have hsle : Real.sqrt R ≤ Real.sqrt (⌈R⌉₊ : ℝ) := Real.sqrt_le_sqrt (Nat.le_ceil R)
  refine ⟨by nlinarith [sq_nonneg (Real.sqrt (⌈R⌉₊ : ℝ) - 2 * Real.sqrt R),
    Real.sq_sqrt hR0, Real.sq_sqrt hNpos.le, Real.sqrt_nonneg R], ?_⟩
  rw [div_le_iff₀ (Real.sqrt_pos.2 hNpos)]
  nlinarith [Real.sq_sqrt hR0, Real.sqrt_nonneg R]

private lemma natCast_rpow_neg_le_inv_sqrt {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (N : ℝ) ^ (-σ) ≤ (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- There is a constant `C > 0` such that `‖ζ(s)‖ ≤ C * √‖s‖` whenever `1 / 2 ≤ s.re` and
`2 ≤ ‖s‖`. -/
theorem exists_global_riemannZeta_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      1 / 2 ≤ s.re →
      2 ≤ ‖s‖ →
      ‖riemannZeta s‖ ≤ C * Real.sqrt ‖s‖ := by
  refine ⟨10, by norm_num, fun s hs hsnorm ↦ ?_⟩
  set N := ⌈‖s‖⌉₊
  have hbase : (1 : ℝ) ≤ N := by linarith [Nat.le_ceil ‖s‖]
  have hN : 1 ≤ N := by exact_mod_cast hbase
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hsnorm
  have hsqrt := ceil_sqrt_bounds hsnorm
  have hsN : 0 < Real.sqrt N := by positivity
  have hpowneg := natCast_rpow_neg_le_inv_sqrt hN hs
  have hpow1 : (N : ℝ) ^ (1 - s.re) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hden : (1 : ℝ) ≤ ‖1 - s‖ := by
    linarith [norm_sub_norm_le s 1, norm_sub_rev s 1, norm_one (α := ℂ)]
  have hterm1 : (N : ℝ) ^ (1 - s.re) / ‖1 - s‖ ≤ Real.sqrt N :=
    (div_le_self (by positivity) hden).trans hpow1
  have htermI : (N : ℝ) ^ (-s.re) / s.re ≤ 2 * (Real.sqrt N)⁻¹ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [inv_nonneg.2 hsN.le]
  have := norm_riemannZeta_le_euler_terms s hs N hN hs1
  have h₃ := mul_le_mul_of_nonneg_left htermI (norm_nonneg s)
  rw [div_eq_mul_inv] at hsqrt
  nlinarith [hsqrt.1, hsqrt.2, Real.sqrt_nonneg ‖s‖,
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith : -s.re ≤ 0)]

end RiemannJensen
