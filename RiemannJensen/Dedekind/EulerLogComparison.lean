module

public import RiemannJensen.Dedekind.EulerLogBounds
public import RiemannJensen.Dedekind.PrimesOverCard
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Comparison of the Dedekind Euler logarithm with the Riemann zeta function

For a number field `K` of degree `n` and `Re s > 1`, the logarithm of the Euler product of the
Dedekind zeta function is bounded in norm by `n * log ζ(Re s)`. Consequently the Dedekind zeta
function is bounded above by `ζ(4) ^ n` and below by `(ζ(4) ^ n)⁻¹` on the half-plane `Re s ≥ 4`.

## Main results

* `norm_log_one_sub_le_neg_log_one_sub_norm`: `‖log (1 - z)‖ ≤ -log (1 - ‖z‖)` for `‖z‖ < 1`.
* `tsum_neg_log_one_sub_prime_rpow_eq_log_riemannZeta`: the sum over primes of
  `-log (1 - p ^ (-σ))` equals `log ζ(σ)` for `σ > 1`.
* `card_filter_rationalPrimeBelow_le_degree`: at most `[K : ℚ]` prime ideals lie above a
  rational prime.
* `norm_dedekindEulerLog_le_log_riemannZeta`: the Dedekind Euler logarithm has norm at most
  `[K : ℚ] * log ζ(Re s)`.
* `norm_analyticDedekindZeta_le_riemannZeta_four_pow`: `‖ζ_K(s)‖ ≤ ζ(4) ^ [K : ℚ]` for
  `Re s ≥ 4`.
* `inv_riemannZeta_four_pow_le_norm_analyticDedekindZeta`: `(ζ(4) ^ [K : ℚ])⁻¹ ≤ ‖ζ_K(s)‖` for
  `Re s ≥ 4`.
-/

@[expose] public section

namespace RiemannJensen

set_option autoImplicit false

noncomputable section

open NumberField Complex

/-- For `‖z‖ < 1`, `‖log (1 - z)‖ ≤ -log (1 - ‖z‖)`. -/
theorem norm_log_one_sub_le_neg_log_one_sub_norm {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have hr : HasSum (fun n : ℕ ↦ ‖z‖ ^ n / n) (-Real.log (1 - ‖z‖)) := by
    have h := Complex.hasSum_taylorSeries_neg_log (z := (‖z‖ : ℂ)) (by simpa using hz)
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log (by linarith),
      ← Complex.ofReal_neg] at h
    exact (Complex.hasSum_ofReal).1 (by simpa using h)
  have hn (n : ℕ) : ‖z ^ n / (n : ℂ)‖ = ‖z‖ ^ n / n := by simp
  rw [← norm_neg, ← (Complex.hasSum_taylorSeries_neg_log hz).tsum_eq, ← hr.tsum_eq]
  exact (norm_tsum_le_tsum_norm (by simpa only [hn] using hr.summable)).trans_eq (by simp only [hn])

/-- Pointwise domination of a prime-ideal Euler logarithm by the logarithm
attached to its rational prime below. -/
theorem norm_dedekindPrimeLogFactor_le_rationalPrime
    (K : Type) [Field K] [NumberField K] (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {s : ℂ} (hs : 1 < s.re) :
    ‖dedekindPrimeLogFactor K p s‖ ≤
      -Real.log (1 - ((rationalPrimeBelow K p : ℕ) : ℝ) ^ (-s.re)) := by
  let q : ℕ := rationalPrimeBelow K p
  let N : ℕ := Ideal.absNorm p.asIdeal
  have hqprime : q.Prime := (rationalPrimeBelow K p).2
  have hqN : q ≤ N := by
    dsimp [q, N]
    rw [absNorm_eq_rationalPrimeBelow_pow K p]
    refine Nat.le_self_pow (fun h0 => ?_) q
    have hN1 : Ideal.absNorm p.asIdeal = 1 := by
      rw [absNorm_eq_rationalPrimeBelow_pow K p, h0, pow_zero]
    exact p.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp hN1)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hqprime.pos.trans_le hqN
  have hnorm : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hN0)]
    simp
  have hle : (N : ℝ) ^ (-s.re) ≤ (q : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hq0 (by exact_mod_cast hqN) (by linarith)
  have hqlt : (q : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hqprime.one_lt) (by linarith)
  have hz : ‖(N : ℂ) ^ (-s)‖ < 1 := hnorm ▸ hle.trans_lt hqlt
  rw [dedekindPrimeLogFactor, norm_neg]
  refine (norm_log_one_sub_le_neg_log_one_sub_norm hz).trans ?_
  rw [hnorm, neg_le_neg_iff]
  exact Real.log_le_log (by linarith) (by linarith)

/-- The rational-prime negative-log Euler series is the logarithm of the
Riemann zeta function on the real half-line `σ > 1`. -/
theorem tsum_neg_log_one_sub_prime_rpow_eq_log_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ)) =
      Real.log (riemannZeta (σ : ℂ)).re := by
  have hterm (p : Nat.Primes) :
      -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(σ : ℂ))) =
        ((-Real.log (1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    have hlt : (p : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
    rw [show ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) by norm_cast, ← ofReal_neg,
      ← ofReal_cpow (Nat.cast_nonneg _), ← ofReal_one, ← ofReal_sub, ← ofReal_log (by linarith)]
    push_cast
    ring
  have h := riemannZeta_eulerProduct_exp_log (s := (σ : ℂ)) (by simpa using hσ)
  simp_rw [hterm] at h
  rw [← ofReal_tsum, ← ofReal_exp] at h
  rw [← h, ofReal_re, Real.log_exp]

/-- The real prime logarithm series is summable on `σ > 1`. -/
theorem summable_neg_log_one_sub_prime_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-σ))) := by
  have hprime : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).comp_injective Subtype.val_injective
  simpa only [sub_eq_add_neg] using
    (Real.summable_log_one_add_of_summable hprime.neg).neg

/-- For `4 ≤ σ`, `log ζ(σ) ≤ log ζ(4)`. -/
theorem log_riemannZeta_le_log_riemannZeta_four {σ : ℝ} (hσ : 4 ≤ σ) :
    Real.log (riemannZeta (σ : ℂ)).re ≤ Real.log (riemannZeta (4 : ℂ)).re := by
  rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
    ← tsum_neg_log_one_sub_prime_rpow_eq_log_riemannZeta (by linarith : 1 < σ),
    ← tsum_neg_log_one_sub_prime_rpow_eq_log_riemannZeta (by norm_num : (1 : ℝ) < 4)]
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_neg_log_one_sub_prime_rpow (by linarith))
    (summable_neg_log_one_sub_prime_rpow (by norm_num))
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  rw [neg_le_neg_iff]
  exact Real.log_le_log (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)))
    (sub_le_sub_left (Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)) 1)

/-- Any finset of prime ideals of `𝓞 K` contains at most `[K : ℚ]` ideals lying over the same
rational prime as `p₀`. -/
theorem card_filter_rationalPrimeBelow_le_degree
    (K : Type) [Field K] [NumberField K] (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (p₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (T.filter fun p => rationalPrimeBelow K p = rationalPrimeBelow K p₀).card ≤
      dedekindDegree K := by
  let q : Ideal ℤ := Ideal.under ℤ p₀.asIdeal
  have hq0 : q ≠ ⊥ := by
    have : NeZero p₀.asIdeal := ⟨p₀.ne_bot⟩
    exact fun h => (Nat.absNorm_under_prime p₀.asIdeal).ne_zero (Ideal.absNorm_eq_zero_iff.mpr h)
  have hqmax : q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq0
  calc
    (T.filter fun p => rationalPrimeBelow K p = rationalPrimeBelow K p₀).card
        ≤ (IsDedekindDomain.primesOverFinset q (𝓞 K)).card := by
          refine Finset.card_le_card_of_injOn
            IsDedekindDomain.HeightOneSpectrum.asIdeal ?_ ?_
          · intro p hp
            rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
            refine ⟨p.isPrime, ⟨?_⟩⟩
            refine hqmax.eq_of_le (Ideal.comap_ne_top _ p.isPrime.ne_top) ?_
            rw [← Int.ideal_span_absNorm_eq_self q, Ideal.span_singleton_le_iff_mem,
              Ideal.mem_comap, map_natCast]
            have hm : ((Ideal.absNorm (Ideal.under ℤ p.asIdeal) : ℕ) : 𝓞 K) ∈ p.asIdeal := by
              simpa only [map_natCast] using
                (Ideal.mem_under ℤ p.asIdeal).mp
                  (Ideal.absNorm_mem (Ideal.under ℤ p.asIdeal))
            have habs :
                Ideal.absNorm (Ideal.under ℤ p.asIdeal) =
                  Ideal.absNorm (Ideal.under ℤ p₀.asIdeal) :=
              congrArg (fun r : Nat.Primes => (r : ℕ)) (Finset.mem_filter.mp hp).2
            rwa [← habs]
          · exact fun _ _ _ _ hp => IsDedekindDomain.HeightOneSpectrum.ext hp
    _ ≤ dedekindDegree K := by
      simpa [dedekindDegree] using card_primesOverFinset_le_finrank K hq0

/-- The terms of the rational-prime negative-log Euler series are nonnegative. -/
theorem neg_log_one_sub_prime_rpow_nonneg {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    0 ≤ -Real.log (1 - (p : ℝ) ^ (-σ)) :=
  neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.2.one_lt) (by linarith))).le
    (sub_le_self 1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

/-- Finite partial sums of the prime-ideal Euler logarithms are bounded by the degree times
the rational-prime negative-log Euler series. -/
theorem sum_norm_dedekindPrimeLogFactor_le
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∑ p ∈ T, ‖dedekindPrimeLogFactor K p s‖ ≤
      (dedekindDegree K : ℝ) * ∑' q : Nat.Primes, -Real.log (1 - (q : ℝ) ^ (-s.re)) := by
  let h : Nat.Primes → ℝ := fun p => -Real.log (1 - (p : ℝ) ^ (-s.re))
  have hh0 : ∀ p, 0 ≤ h p := neg_log_one_sub_prime_rpow_nonneg (by linarith)
  calc
    ∑ p ∈ T, ‖dedekindPrimeLogFactor K p s‖
        ≤ ∑ p ∈ T, h (rationalPrimeBelow K p) :=
      Finset.sum_le_sum fun p _ => norm_dedekindPrimeLogFactor_le_rationalPrime K p hs
    _ = ∑ q ∈ T.image (rationalPrimeBelow K),
        ∑ p ∈ T.filter (fun p => rationalPrimeBelow K p = q),
          h (rationalPrimeBelow K p) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem (rationalPrimeBelow K) hp) _).symm
    _ ≤ ∑ q ∈ T.image (rationalPrimeBelow K), (dedekindDegree K : ℝ) * h q := by
      refine Finset.sum_le_sum fun q hq => ?_
      obtain ⟨p₀, -, rfl⟩ := Finset.mem_image.mp hq
      refine (Finset.sum_eq_card_nsmul fun p hp =>
        congrArg h (Finset.mem_filter.mp hp).2).trans_le ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_rationalPrimeBelow_le_degree K T p₀) (hh0 _)
    _ ≤ (dedekindDegree K : ℝ) * ∑' q : Nat.Primes, h q := by
      rw [← Finset.mul_sum]
      gcongr
      exact (summable_neg_log_one_sub_prime_rpow hs).sum_le_tsum _ (fun q _ => hh0 q)

/-- For `1 < Re s`, the Dedekind Euler logarithm has norm at most `[K : ℚ] * log ζ(Re s)`. -/
theorem norm_dedekindEulerLog_le_log_riemannZeta
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    ‖dedekindEulerLog K s‖ ≤
      (dedekindDegree K : ℝ) * Real.log (riemannZeta (s.re : ℂ)).re := by
  rw [dedekindEulerLog_eq_locallyUniformSum K hs,
    ← tsum_neg_log_one_sub_prime_rpow_eq_log_riemannZeta hs]
  exact (norm_tsum_le_tsum_norm (summable_of_sum_le (fun _ => norm_nonneg _)
    (sum_norm_dedekindPrimeLogFactor_le K hs))).trans
    (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (sum_norm_dedekindPrimeLogFactor_le K hs))

/-- The Dedekind Euler logarithm is bounded by the degree times `log ζ(4)` on `Re s ≥ 4`. -/
theorem norm_dedekindEulerLog_le_degree_mul_log_riemannZeta_four
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    ‖dedekindEulerLog K s‖ ≤ (dedekindDegree K : ℝ) * Real.log (riemannZeta (4 : ℂ)).re :=
  (norm_dedekindEulerLog_le_log_riemannZeta K (by linarith)).trans
    (mul_le_mul_of_nonneg_left (log_riemannZeta_le_log_riemannZeta_four hs) (Nat.cast_nonneg _))

/-- For `4 ≤ Re s`, `‖ζ_K(s)‖ ≤ ζ(4) ^ [K : ℚ]`. -/
theorem norm_analyticDedekindZeta_le_riemannZeta_four_pow
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    ‖analyticDedekindZeta K s‖ ≤ (riemannZeta (4 : ℂ)).re ^ dedekindDegree K := by
  have hz4 : 0 < (riemannZeta (4 : ℂ)).re := riemannZeta_re_pos_of_one_lt (by norm_num)
  rw [← dedekindEulerLog_exp K (by linarith), Complex.norm_exp, ← Real.exp_log hz4,
    ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans
    (norm_dedekindEulerLog_le_degree_mul_log_riemannZeta_four K hs))

/-- For `4 ≤ Re s`, `(ζ(4) ^ [K : ℚ])⁻¹ ≤ ‖ζ_K(s)‖`. -/
theorem inv_riemannZeta_four_pow_le_norm_analyticDedekindZeta
    (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 4 ≤ s.re) :
    ((riemannZeta (4 : ℂ)).re ^ dedekindDegree K)⁻¹ ≤ ‖analyticDedekindZeta K s‖ := by
  have hz4 : 0 < (riemannZeta (4 : ℂ)).re := riemannZeta_re_pos_of_one_lt (by norm_num)
  rw [← dedekindEulerLog_exp K (by linarith), Complex.norm_exp, ← Real.exp_log hz4,
    ← Real.exp_nat_mul, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr
    ((neg_le_neg (norm_dedekindEulerLog_le_degree_mul_log_riemannZeta_four K hs)).trans
      ((neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _)))

end

end RiemannJensen
