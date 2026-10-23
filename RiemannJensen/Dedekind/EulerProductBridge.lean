module

public import RiemannJensen.Dedekind.EulerLog
public import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# Euler product for the Dedekind zeta function

For a number field `K` and `Re s > 1`, the Dedekind zeta function `dedekindZeta K s` is the sum
of `N(I)^(-s)` over the nonzero ideals `I` of `𝓞 K`, and equals the product over prime ideals `P`
of `(1 - N(P)^(-s))⁻¹`. Consequently it does not vanish there, and the exponential of the
Euler logarithm `dedekindEulerLog K s` is `analyticDedekindZeta K s`.

## Main definitions

* `EulerProductBridge.P6B.ZetaNeZero.idealCount`: the number of ideals of `𝓞 K` of norm `n`.
* `EulerProductBridge.P6B.ZetaNeZero.primeSet`: the nonzero ideals all of whose prime divisors
  lie in a given finite set of primes.
* `dedekindPrimesEquiv`: height-one primes of `𝓞 K` are the prime ideals of `𝓞 K`.

## Main results

* `EulerProductBridge.P6B.ZetaNeZero.tsum_absNorm_cpow_eq_dedekindZeta`: for `Re z > 1`,
  `dedekindZeta K z` is the sum of `N(I)^(-z)` over all ideals `I`.
* `EulerProductBridge.P6B.ZetaNeZero.tsum_primeSet_eq_prod`: the sum of `N(I)^(-s)` over the
  ideals supported on a finite set `T` of primes is the product of the Euler factors over `T`.
* `EulerProductBridge.P6B.ZetaNeZero.dedekindZeta_ne_zero`: `dedekindZeta K s ≠ 0` for
  `Re s > 1`.
* `analyticDedekindZeta_ne_zero_of_one_lt_re`: `analyticDedekindZeta K s ≠ 0` for `Re s > 1`.
* `dedekindEulerLog_exp`: `exp (dedekindEulerLog K s) = analyticDedekindZeta K s` for
  `Re s > 1`.
-/

@[expose] public section

namespace RiemannJensen

set_option autoImplicit false

noncomputable section

open NumberField Filter Complex
open scoped Topology Classical

namespace EulerProductBridge

namespace P6B

namespace ZetaNeZero

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The number of ideals of `𝓞 K` of absolute norm `n`. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- The Dedekind zeta function is the L-series of the ideal-counting function `idealCount K`. -/
theorem dedekindZeta_eq_LSeries (z : ℂ) :
    dedekindZeta K z = LSeries (fun n => (idealCount K n : ℂ)) z := rfl

/-- There are finitely many ideals of `𝓞 K` of a given absolute norm. -/
scoped instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- There is exactly one ideal of absolute norm `0`, the zero ideal. -/
@[simp]
theorem idealCount_zero : idealCount K 0 = 1 := by
  rw [idealCount]
  have : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_eq_zero_iff.mpr rfl⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp I.2) }
  exact Nat.card_unique

/-- The number of nonzero ideals of norm at most `n`, divided by `n`, tends to the residue
`dedekindZeta_residue K`. -/
theorem tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue]
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = idealCount K 0 from (idealCount_zero K).symm,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le)]
  simp only [idealCount]
  rw [← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- The number of nonzero ideals of norm at most `n` is `O(n)`. -/
theorem isBigO_sum_idealCount :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
  have h1 : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ (tendsto_sum_idealCount_div K)
    filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (Nat.cast_ne_zero.mpr hn)
  exact h1.congr_right fun n => (Real.rpow_one _).symm

/-- The L-series of `idealCount K` converges absolutely for `Re z > 1`. -/
theorem LSeriesSummable_idealCount {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) z := by
  simpa only [Complex.ofReal_natCast] using
    LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
      (isBigO_sum_idealCount K) (fun n => Nat.cast_nonneg _) zero_le_one hz

/-- For real `σ > 1`, the series `∑ N(I)^(-σ)` over the ideals of `𝓞 K` converges. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  rw [← e.summable_iff]
  have hnn : ∀ p, 0 ≤ ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) p := fun p =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) ⟨n, c⟩ = (n : ℝ) ^ (-σ) :=
    fun n c => by simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun _ => Summable.of_finite, ?_⟩
  simp_rw [hfib, tsum_const, nsmul_eq_mul]
  have hL : Summable fun n => ‖LSeries.term (fun n => (idealCount K n : ℂ)) σ n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_idealCount K (z := σ) (by simpa using hσ))
  refine hL.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · rw [h0, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (by linarith : σ ≠ 0)), mul_zero]
  · rw [Complex.norm_natCast, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]
    rfl

/-- For `Re z > 1`, the series `∑ N(I)^(-z)` over the ideals of `𝓞 K` converges absolutely. -/
theorem summable_norm_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)‖ := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hz)
  refine (summable_absNorm_rpow K hz).congr fun I => ?_
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow hz0, norm_zero,
      Real.zero_rpow (neg_ne_zero.mpr (by linarith : z.re ≠ 0))]
  · rw [Complex.norm_natCast_cpow_of_pos h, Complex.neg_re]

/-- For `Re z > 1`, the series `∑ N(I)^(-z)` over the ideals of `𝓞 K` is summable. -/
theorem summable_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) :=
  (summable_norm_absNorm_cpow K hz).of_norm

/-- For `Re z > 1`, `dedekindZeta K z` is the sum of `N(I)^(-z)` over the ideals `I` of `𝓞 K`. -/
theorem tsum_absNorm_cpow_eq_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
    ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) = dedekindZeta K z := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hz)
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  have hs : Summable ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) :=
    e.summable_iff.mpr (summable_absNorm_cpow K hz)
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) ⟨n, c⟩ = (n : ℂ) ^ (-z) :=
    fun n c => by simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  rw [← e.tsum_eq, show (fun c => (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) (e c))
      = (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e from rfl, hs.tsum_sigma,
    dedekindZeta_eq_LSeries, LSeries]
  refine tsum_congr fun n => ?_
  simp_rw [hfib]
  rw [tsum_const, ← idealCount, nsmul_eq_mul, LSeries.term_def]
  split_ifs with h0
  · rw [h0, Nat.cast_zero, Complex.zero_cpow hz0, mul_zero]
  · rw [Complex.cpow_neg, div_eq_mul_inv]

/-- The prime ideals of `𝓞 K`. -/
abbrev Primes : Type u := {Q : Ideal (𝓞 K) // Prime Q}

/-- The nonzero ideals of `𝓞 K` all of whose prime divisors lie in the finite set `T`. -/
def primeSet (T : Finset (Primes K)) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ 0 ∧ ∀ Q : Primes K, Q.1 ∣ I → Q ∈ T}

omit [NumberField K] in
/-- An ideal lies in `primeSet K T` iff it is nonzero and all its prime divisors lie in `T`. -/
@[simp]
theorem mem_primeSet_iff {T : Finset (Primes K)} {I : Ideal (𝓞 K)} :
    I ∈ primeSet K T ↔ I ≠ 0 ∧ ∀ Q : Primes K, Q.1 ∣ I → Q ∈ T := Iff.rfl

/-- The only nonzero ideal with no prime divisors is the unit ideal. -/
theorem primeSet_empty : primeSet K ∅ = {⊤} := by
  ext I
  simp only [primeSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hI0, hprime⟩
    by_contra hne
    have hnu : ¬IsUnit I := fun h => hne (Ideal.isUnit_iff.mp h)
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_factors hI0 hnu
    exact absurd (hprime ⟨P, UniqueFactorizationMonoid.prime_of_factor P hP⟩
      (UniqueFactorizationMonoid.dvd_of_mem_factors hP)) (Finset.notMem_empty _)
  · rintro rfl
    exact ⟨Ideal.one_eq_top (R := 𝓞 K) ▸ one_ne_zero, fun Q hdvd =>
      absurd (Ideal.isUnit_iff.mpr (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))) Q.2.not_isUnit⟩

/-- A prime ideal has absolute norm at least `2`. -/
theorem two_le_absNorm (Q : Primes K) : 2 ≤ Ideal.absNorm Q.1 := by
  have h0 : Ideal.absNorm Q.1 ≠ 0 := fun h =>
    Q.2.ne_zero (by rwa [Ideal.zero_eq_bot, ← Ideal.absNorm_eq_zero_iff])
  have h1 : Ideal.absNorm Q.1 ≠ 1 := fun h =>
    Q.2.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

/-- For a prime ideal `Q` and `Re s > 0`, `‖N(Q)^(-s)‖ < 1`. -/
theorem norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    ‖((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have h2 := two_le_absNorm K Q
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h1 : (1 : ℝ) < (Ideal.absNorm Q.1 : ℕ) := by exact_mod_cast h2
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

/-- For a prime ideal `Q` and `Re s > 0`, the Euler factor `1 - N(Q)^(-s)` is nonzero. -/
theorem one_sub_absNorm_cpow_ne_zero {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    (1 : ℂ) - ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s) ≠ 0 := fun h =>
  (norm_absNorm_cpow_neg_lt_one K hs Q).ne' (by rw [← sub_eq_zero.mp h, norm_one])

/-- For natural numbers `m`, `k` and complex `v`, `(m ^ k) ^ v = (m ^ v) ^ k`. -/
theorem cpow_pow_natCast (m k : ℕ) (v : ℂ) :
    ((m ^ k : ℕ) : ℂ) ^ v = ((m : ℂ) ^ v) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- Multiplying an ideal of `primeSet K T` by a power of `P` gives an ideal of
`primeSet K (insert P T)`. -/
theorem pow_mul_mem_primeSet_insert (P : Primes K) {T : Finset (Primes K)} (k : ℕ)
    {c : Ideal (𝓞 K)} (hc : c ∈ primeSet K T) : P.1 ^ k * c ∈ primeSet K (insert P T) := by
  refine ⟨mul_ne_zero (pow_ne_zero k P.2.ne_zero) hc.1, fun Q hdvd => ?_⟩
  rcases (Prime.dvd_mul Q.2).mp hdvd with hQP | hQc
  · obtain rfl : Q = P := Subtype.ext
      (associated_iff_eq.mp (Prime.associated_of_dvd Q.2 P.2 (Q.2.dvd_of_dvd_pow hQP)))
    exact Finset.mem_insert_self _ T
  · exact Finset.mem_insert_of_mem (hc.2 Q hQc)

/-- For `P ∉ T` and `c ∈ primeSet K T`, `P ^ k * c = P ^ k' * c'` with `k ≤ k'` forces
`k = k'` and `c = c'`. -/
theorem eq_of_pow_mul_eq_pow_mul_primeSet (P : Primes K) {T : Finset (Primes K)} (hPT : P ∉ T)
    {k k' : ℕ} {c c' : Ideal (𝓞 K)} (hc : c ∈ primeSet K T) (hkk : k ≤ k')
    (h : P.1 ^ k * c = P.1 ^ k' * c') : k = k' ∧ c = c' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
  rw [pow_add, mul_assoc] at h
  have hcc : c = P.1 ^ d * c' := mul_left_cancel₀ (pow_ne_zero k P.2.ne_zero) h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨rfl, by simpa using hcc⟩
  · exact (hPT (hc.2 P (hcc ▸ dvd_mul_of_dvd_left (dvd_pow_self P.1 hd.ne') c'))).elim

/-- For `P ∉ T`, the map `(k, c) ↦ P ^ k * c` is a bijection from `ℕ × primeSet K T` onto
`primeSet K (insert P T)`. -/
theorem bijective_pow_mul_primeSet (P : Primes K) {T : Finset (Primes K)} (hPT : P ∉ T) :
    Function.Bijective fun kc : ℕ × primeSet K T =>
      (⟨P.1 ^ kc.1 * kc.2.1, pow_mul_mem_primeSet_insert K P kc.1 kc.2.2⟩ :
        primeSet K (insert P T)) := by
  constructor
  · rintro ⟨k, c⟩ ⟨k', c'⟩ hab
    have hval : P.1 ^ k * c.1 = P.1 ^ k' * c'.1 := congrArg Subtype.val hab
    rcases le_total k k' with hkk | hkk
    · obtain ⟨h1, h2⟩ := eq_of_pow_mul_eq_pow_mul_primeSet K P hPT c.2 hkk hval
      exact Prod.ext h1 (Subtype.ext h2)
    · obtain ⟨h1, h2⟩ := eq_of_pow_mul_eq_pow_mul_primeSet K P hPT c'.2 hkk hval.symm
      exact Prod.ext h1.symm (Subtype.ext h2.symm)
  · rintro ⟨J, hJ0, hJmem⟩
    obtain ⟨c, hc, hPc⟩ :=
      (FiniteMultiplicity.of_not_isUnit P.2.not_isUnit hJ0).exists_eq_pow_mul_and_not_dvd
    have hc0 : c ≠ 0 := fun h => hJ0 (by rw [hc, h, mul_zero])
    have hcmem : c ∈ primeSet K T := by
      refine ⟨hc0, fun Q hQc => ?_⟩
      rcases Finset.mem_insert.mp (hJmem Q (hc ▸ dvd_mul_of_dvd_right hQc _)) with rfl | hQT
      · exact absurd hQc hPc
      · exact hQT
    exact ⟨⟨multiplicity P.1 J, ⟨c, hcmem⟩⟩, Subtype.ext hc.symm⟩

/-- For `Re s > 1` and a prime `P ∉ T`, adjoining `P` to `T` multiplies the sum of `N(I)^(-s)`
over `primeSet K T` by the Euler factor `(1 - N(P)^(-s))⁻¹`. -/
theorem tsum_primeSet_insert {s : ℂ} (hs : 1 < s.re) (P : Primes K)
    {T : Finset (Primes K)} (hPT : P ∉ T) :
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  let e := Equiv.ofBijective _ (bijective_pow_mul_primeSet K P hPT)
  calc
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
        = ∑' kc : ℕ × primeSet K T,
            ((Ideal.absNorm (e kc).1 : ℕ) : ℂ) ^ (-s) :=
      (e.tsum_eq _).symm
    _ = ∑' kc : ℕ × primeSet K T,
          ((((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ kc.1
            * ((Ideal.absNorm kc.2.1 : ℕ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun kc => ?_
      rw [show (e kc).1 = P.1 ^ kc.1 * kc.2.1 from rfl, map_mul, map_pow, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, cpow_pow_natCast]
    _ = (∑' k : ℕ, (((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k)
          * ∑' J : primeSet K T, ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) :=
      (tsum_mul_tsum_of_summable_norm
        (summable_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)).norm
        ((summable_norm_absNorm_cpow K hs).subtype _)).symm
    _ = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
      rw [tsum_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)]

/-- For `Re s > 1` and a finite set `T` of primes, the sum of `N(I)^(-s)` over `primeSet K T` is
the product of the Euler factors `(1 - N(P)^(-s))⁻¹` over `P ∈ T`. -/
theorem tsum_primeSet_eq_prod {s : ℂ} (hs : 1 < s.re) (T : Finset (Primes K)) :
    ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
    rw [primeSet_empty,
      tsum_singleton ⊤ (fun J : Ideal (𝓞 K) => ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)),
      Finset.prod_empty, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow]
  | insert P T hPT ih =>
    rw [tsum_primeSet_insert K hs P hPT, Finset.prod_insert hPT, ih]

/-- A nonzero ideal whose prime factors all lie in `T` belongs to `primeSet K T`. -/
theorem mem_primeSet_of_factors {I : Ideal (𝓞 K)} (hI : I ≠ 0) {T : Finset (Primes K)}
    (hT : ∀ Q : Primes K, Q.1 ∈ UniqueFactorizationMonoid.factors I → Q ∈ T) :
    I ∈ primeSet K T := by
  refine ⟨hI, fun Q hdvd => ?_⟩
  obtain ⟨R, hR, hQR⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI Q.2.irreducible hdvd
  exact hT Q (associated_iff_eq.mp hQR ▸ hR)

omit [NumberField K] in
/-- If every nonzero ideal of `F` lies in `S`, then for a nonnegative `g` with `g 0 = 0`, the
indicator of `g` on `Sᶜ` is bounded by its indicator on `Fᶜ`. -/
theorem indicator_compl_le_of_subset_ne_zero {S F : Set (Ideal (𝓞 K))} {g : Ideal (𝓞 K) → ℝ}
    (hg : ∀ I, 0 ≤ g I) (hg0 : g 0 = 0) (hin : ∀ I ∈ F, I ≠ 0 → I ∈ S) (I : Ideal (𝓞 K)) :
    Sᶜ.indicator g I ≤ Fᶜ.indicator g I := by
  by_cases hI0 : I = 0
  · calc Sᶜ.indicator g I ≤ g I := Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => hg I)
      _ = 0 := by rw [hI0, hg0]
      _ ≤ Fᶜ.indicator g I := Set.indicator_nonneg (fun _ _ => hg _) _
  · by_cases hmem : I ∈ S
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
      exact Set.indicator_nonneg (fun _ _ => hg _) _
    · rw [Set.indicator_of_mem (Set.mem_compl hmem),
        Set.indicator_of_mem (Set.mem_compl fun h => hmem (hin I h hI0))]

/-- For an absolutely summable `f` on ideals with `f 0 = 0`, the sums of `f` over `primeSet K T`
tend to the sum of `f` over all ideals as the finite set `T` of primes grows. -/
theorem tendsto_tsum_primeSet_of_summable {f : Ideal (𝓞 K) → ℂ}
    (hf : Summable fun I => ‖f I‖) (hf0 : f 0 = 0) :
    Tendsto (fun T : Finset (Primes K) => ∑' I : primeSet K T, f I) atTop (𝓝 (∑' I, f I)) := by
  have htail : Tendsto (fun F : Finset (Ideal (𝓞 K)) =>
      ∑' I, ((↑F : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I) atTop (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero (fun I => ‖f I‖)).congr fun F =>
      tsum_subtype ((↑F : Set (Ideal (𝓞 K)))ᶜ) (fun I => ‖f I‖)
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨F₀, hF₀⟩ := Metric.tendsto_atTop.mp htail ε hε
  refine ⟨F₀.biUnion (fun I =>
      ((UniqueFactorizationMonoid.factors I).toFinset).subtype Prime), fun T hT => ?_⟩
  have hin : ∀ I ∈ F₀, I ≠ 0 → I ∈ primeSet K T := fun I hI hI0 =>
    mem_primeSet_of_factors K hI0 fun Q hQ => hT <|
      Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_subtype.mpr (Multiset.mem_toFinset.mpr hQ)⟩
  have hbound := hF₀ F₀ le_rfl
  rw [Real.dist_0_eq_abs, abs_of_nonneg (tsum_nonneg fun I =>
    Set.indicator_nonneg (fun _ _ => norm_nonneg _) I)] at hbound
  have hsplit := hf.of_norm.tsum_subtype_add_tsum_subtype_compl (primeSet K T)
  rw [dist_eq_norm, show (∑' I : primeSet K T, f I) - ∑' I, f I = -∑' I : ↥(primeSet K T)ᶜ, f I by
    rw [← hsplit, sub_add_cancel_left], norm_neg]
  calc ‖∑' I : ↥(primeSet K T)ᶜ, f I‖
      ≤ ∑' I : ↥(primeSet K T)ᶜ, ‖f I‖ := norm_tsum_le_tsum_norm (hf.subtype _)
    _ = ∑' I, ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I :=
      tsum_subtype ((primeSet K T)ᶜ) (fun I => ‖f I‖)
    _ ≤ ∑' I, ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
      Summable.tsum_le_tsum
        (indicator_compl_le_of_subset_ne_zero K (g := fun I => ‖f I‖) (fun _ => norm_nonneg _)
          (by rw [hf0, norm_zero]) fun I hI => hin I (Finset.mem_coe.mp hI))
        (hf.indicator _) (hf.indicator _)
    _ < ε := hbound

/-- For `Re s > 1`, `dedekindZeta K s` is the exponential of the sum of `-log (1 - N(P)^(-s))`
over the prime ideals `P`. -/
theorem dedekindZeta_eq_exp_tsum_neg_log {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      cexp (∑' P : Primes K, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))) := by
  have hsz : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs)
  have hsum : Summable (fun P : Primes K => ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) :=
    (summable_absNorm_cpow K hs).comp_injective Subtype.val_injective
  have hlim1 : Tendsto (fun T : Finset (Primes K) =>
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (cexp (∑' P : Primes K, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))))) := by
    refine ((Complex.continuous_exp.tendsto _).comp hsum.clog_one_sub.neg.hasSum).congr fun T => ?_
    simp only [Function.comp_apply]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun P _ => by
      rw [exp_neg, exp_log (one_sub_absNorm_cpow_ne_zero K (zero_lt_one.trans hs) P)]
  have h := tendsto_tsum_primeSet_of_summable K
    (f := fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s))
    (summable_norm_absNorm_cpow K hs)
    (by simp [Complex.zero_cpow hsz])
  rw [tsum_absNorm_cpow_eq_dedekindZeta K hs] at h
  exact tendsto_nhds_unique (h.congr fun T => tsum_primeSet_eq_prod K hs T) hlim1

/-- The Dedekind zeta function does not vanish for `Re s > 1`. -/
theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  rw [dedekindZeta_eq_exp_tsum_neg_log K hs]
  exact Complex.exp_ne_zero _

end P6B.ZetaNeZero

end EulerProductBridge

/-- The height-one primes of `𝓞 K` are equivalent to its prime ideals. -/
def dedekindPrimesEquiv (K : Type) [Field K] [NumberField K] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) ≃ EulerProductBridge.P6B.ZetaNeZero.Primes K where
  toFun v := ⟨v.asIdeal, v.prime⟩
  invFun Q := ⟨Q.1, Ideal.isPrime_of_prime Q.2, fun h =>
    Q.2.ne_zero (by rwa [Ideal.zero_eq_bot])⟩
  left_inv v := rfl
  right_inv Q := rfl

/-- The ideal underlying `dedekindPrimesEquiv K v` is `v.asIdeal`. -/
@[simp]
theorem dedekindPrimesEquiv_apply_coe (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : (dedekindPrimesEquiv K v).1 = v.asIdeal :=
  rfl

/-- The ideal of the height-one prime `(dedekindPrimesEquiv K).symm Q` is `Q`. -/
@[simp]
theorem dedekindPrimesEquiv_symm_apply_asIdeal (K : Type) [Field K] [NumberField K]
    (Q : EulerProductBridge.P6B.ZetaNeZero.Primes K) :
    ((dedekindPrimesEquiv K).symm Q).asIdeal = Q.1 :=
  rfl

/-- The continued Dedekind zeta function `analyticDedekindZeta K` does not vanish for
`Re s > 1`. -/
theorem analyticDedekindZeta_ne_zero_of_one_lt_re (K : Type) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) : analyticDedekindZeta K s ≠ 0 := by
  rw [analyticDedekindZeta_eq_dirichletSeries K s hs]
  exact EulerProductBridge.P6B.ZetaNeZero.dedekindZeta_ne_zero K hs

/-- For `Re s > 1` and each height-one prime `p`, the series of the terms
`dedekindEulerLogTerm K s p m` sums to `-log (1 - N(p)^(-s))`. -/
theorem dedekindEulerLog_inner_hasSum (K : Type) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    HasSum (fun m : ℕ => dedekindEulerLogTerm K s p m)
      (-Complex.log (1 - ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  have hp : ‖((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 :=
    EulerProductBridge.P6B.ZetaNeZero.norm_absNorm_cpow_neg_lt_one K
      (zero_lt_one.trans hs) (dedekindPrimesEquiv K p)
  convert Complex.hasSum_taylorSeries_neg_log' hp using 1
  funext m
  rw [dedekindEulerLogTerm, show -((m + 1 : ℕ) : ℂ) * s =
    ((m + 1 : ℕ) : ℂ) * (-s) by ring, Complex.cpow_nat_mul]
  norm_num

/-- For `Re s > 1`, the series of `-log (1 - N(p)^(-s))` over the height-one primes `p` is
summable. -/
theorem dedekindPrimeLog_summable (K : Type) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      -Complex.log (1 - ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s))) :=
  (dedekindPrimesEquiv K).symm.summable_iff.mp
    ((EulerProductBridge.P6B.ZetaNeZero.summable_absNorm_cpow K hs).comp_injective
      Subtype.val_injective).clog_one_sub.neg

/-- For `Re s > 1`, `dedekindEulerLog K s` is the sum of `-log (1 - N(p)^(-s))` over the
height-one primes `p`. -/
theorem dedekindEulerLog_eq_primeLogSum (K : Type) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    dedekindEulerLog K s = ∑' p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)) := by
  rw [dedekindEulerLog_of_one_lt_re K s hs]
  exact tsum_congr fun p => (dedekindEulerLog_inner_hasSum K hs p).tsum_eq

/-- For `Re s > 1`, the exponential of the Euler logarithm `dedekindEulerLog K s` is the
continued Dedekind zeta function `analyticDedekindZeta K s`. -/
theorem dedekindEulerLog_exp (K : Type) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) : Complex.exp (dedekindEulerLog K s) = analyticDedekindZeta K s := by
  rw [dedekindEulerLog_eq_primeLogSum K hs, analyticDedekindZeta_eq_dirichletSeries K s hs,
    EulerProductBridge.P6B.ZetaNeZero.dedekindZeta_eq_exp_tsum_neg_log K hs]
  exact congrArg cexp ((dedekindPrimesEquiv K).tsum_eq fun P =>
    -Complex.log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)))

end

end RiemannJensen
