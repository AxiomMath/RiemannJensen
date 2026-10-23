module

public import RiemannJensen.MainTheorem.Counting
public import RiemannJensen.MainTheorem.WindowLoss
public import RiemannJensen.Dedekind.ScaleLemmas

/-!
# Root-count adapters for Dedekind Jensen polynomials

For a number field `K`, the rescaled reciprocal `rescaledDedekindJensenK K d` vanishes at `-q`,
with `q > 0`, exactly when the Jensen polynomial `dedekindJensenK K d` vanishes at the negative
point `-(dedekindScaleT K d) ^ 2 / (d * q)`. Distinct such zeros therefore bound the number of
distinct negative roots of `dedekindJensenK K d` from below.

## Main results

* `rescaledDedekindJensenK_neg_zero_iff`: `-q` is a zero of the rescaled reciprocal if and only
  if `-(dedekindScaleT K d) ^ 2 / (d * q)` is a zero of the Jensen polynomial.
* `le_dedekindNegativeRootCountK_of_rescaled_roots`: `n` distinct positive `q` with `-q` a zero
  of the rescaled reciprocal give `n ≤ dedekindNegativeRootCountK K d`.
-/

@[expose] public section

namespace RiemannJensen

noncomputable section

variable (K : Type) [Field K] [NumberField K]

/-- Evaluation of `rescaledDedekindJensenK K d` at `x` in terms of `dedekindReciprocalK K d` at
`(d / T ^ 2) * x`, where `T = dedekindScaleT K d`. -/
theorem eval_rescaledDedekindJensenK (d : ℕ) (x : ℝ) :
    (rescaledDedekindJensenK K d).eval x =
      ((dedekindScaleT K d) ^ 2 / (d : ℝ)) ^ d *
        (dedekindReciprocalK K d).eval
          (((d : ℝ) / (dedekindScaleT K d) ^ 2) * x) := by
  simp [rescaledDedekindJensenK]

/-- For `q ≠ 0`, the rescaled reciprocal at `-q` is `(-q) ^ d` times the Jensen polynomial at
`-(dedekindScaleT K d) ^ 2 / (d * q)`. -/
theorem rescaledDedekindJensenK_eval_neg (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : q ≠ 0) :
    (rescaledDedekindJensenK K d).eval (-q) =
      (-q) ^ d * (dedekindJensenK K d).eval (-(dedekindScaleT K d) ^ 2 / ((d : ℝ) * q)) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd)
  have hT : dedekindScaleT K d ≠ 0 := (dedekindScaleT_pos K d hd).ne'
  have hT2 : dedekindScaleT K d ^ 2 ≠ 0 := pow_ne_zero 2 hT
  have hy : ((d : ℝ) / dedekindScaleT K d ^ 2) * (-q) ≠ 0 :=
    mul_ne_zero (div_ne_zero hd0 hT2) (neg_ne_zero.mpr hq)
  rw [eval_rescaledDedekindJensenK,
    show dedekindReciprocalK K d = dedekindReciprocal (entireDedekindXi K) d by rfl,
    eval_dedekindReciprocal_eq (entireDedekindXi K) d hy,
    dedekindJensenK_eq K d,
    ← mul_assoc, ← mul_pow]
  congr 2 <;> field_simp

/-- For `q > 0`, `-q` is a zero of the rescaled reciprocal iff
`-(dedekindScaleT K d) ^ 2 / (d * q)` is a zero of `dedekindJensenK K d`. -/
theorem rescaledDedekindJensenK_neg_zero_iff (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : 0 < q) :
    (rescaledDedekindJensenK K d).eval (-q) = 0 ↔
      (dedekindJensenK K d).eval (-(dedekindScaleT K d) ^ 2 / ((d : ℝ) * q)) = 0 := by
  rw [rescaledDedekindJensenK_eval_neg K d hd hq.ne']
  have hpow : (-q) ^ d ≠ 0 := pow_ne_zero d (neg_ne_zero.mpr hq.ne')
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hpow,
    fun h => by rw [h, mul_zero]⟩

/-- If `0 < q` and `(rescaledDedekindJensenK K d).eval (-q) = 0`, then
`-(dedekindScaleT K d) ^ 2 / (d * q)` is a negative root of `dedekindJensenK K d`. -/
theorem rescaledDedekindJensenK_root_transport (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : 0 < q)
    (hroot : (rescaledDedekindJensenK K d).eval (-q) = 0) :
    -(dedekindScaleT K d) ^ 2 / ((d : ℝ) * q) < 0 ∧
      (dedekindJensenK K d).eval (-(dedekindScaleT K d) ^ 2 / ((d : ℝ) * q)) = 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact ⟨div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos (dedekindScaleT_pos K d hd)))
      (mul_pos hdR hq),
    (rescaledDedekindJensenK_neg_zero_iff K d hd hq).mp hroot⟩

/-- An injective positive family of rescaled zeros gives that many distinct
negative roots of the canonical Dedekind Jensen polynomial. -/
theorem le_dedekindNegativeRootCountK_of_rescaled_roots (d : ℕ) {n : ℕ} (hd : 1 ≤ d)
    (hJ : dedekindJensenK K d ≠ 0) (q : Fin n → ℝ) (hq_inj : Function.Injective q)
    (hq_pos : ∀ i, 0 < q i)
    (hq_root : ∀ i, (rescaledDedekindJensenK K d).eval (-(q i)) = 0) :
    n ≤ dedekindNegativeRootCountK K d := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd)
  have hden_inj : Function.Injective (fun i => (d : ℝ) * q i) :=
    fun i j hij => hq_inj (mul_left_cancel₀ hd0 hij)
  exact le_negativeDistinctRootCount_of_injective hJ
    (fun i => -(dedekindScaleT K d) ^ 2 / ((d : ℝ) * q i))
    (reciprocalRootArgument_injective (pow_ne_zero 2 (dedekindScaleT_pos K d hd).ne') hden_inj)
    (fun i => (rescaledDedekindJensenK_root_transport K d hd (hq_pos i) (hq_root i)).1)
    (fun i => (rescaledDedekindJensenK_root_transport K d hd (hq_pos i) (hq_root i)).2)

end

end RiemannJensen
