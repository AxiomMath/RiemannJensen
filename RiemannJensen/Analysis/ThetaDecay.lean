module

public import RiemannJensen.Theta
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# A uniform one-sided decay estimate for the xi theta kernel

For `t ≥ 0`, the theta kernel `thetaPhi t` is bounded by
`thetaDecayConstant * exp (9 * t / 2 - π * exp (2 * t))`, where `thetaDecayConstant` is an
explicit positive multiple of the Hurwitz-kernel sum `HurwitzKernelBounds.F_nat 4 1 1`.

## Main definitions

* `thetaDecayConstant`: The constant `4 π² e^π F_nat 4 1 1`.

## Main results

* `thetaPhi_le_exp_decay`: For `t ≥ 0`, `thetaPhi t` is at most
  `thetaDecayConstant * exp (9 * t / 2 - π * exp (2 * t))`.
* `exists_thetaPhi_decay`: There is `C > 0` such that `0 ≤ thetaPhi t` and
  `thetaPhi t ≤ C * exp (9 * t / 2 - π * exp (2 * t))` for all `t ≥ 0`.
-/

@[expose] public section

namespace RiemannJensen

/-- The constant `4 π² e^π F_nat 4 1 1`, a positive multiple of a Hurwitz-kernel sum. -/
noncomputable def thetaDecayConstant : ℝ :=
  4 * Real.pi ^ 2 * Real.exp Real.pi * HurwitzKernelBounds.F_nat 4 1 1

/-- The sequence `m ↦ 4 π² e^π f_nat 4 1 1 m` is summable. -/
lemma summable_thetaDecayMajorant :
    Summable fun m : ℕ => 4 * Real.pi ^ 2 * Real.exp Real.pi * HurwitzKernelBounds.f_nat 4 1 1 m :=
  (HurwitzKernelBounds.summable_f_nat 4 1 (by norm_num)).mul_left _

/-- `thetaDecayConstant` is the sum of the majorant terms `4 π² e^π f_nat 4 1 1 m`. -/
lemma thetaDecayConstant_eq_tsum :
    thetaDecayConstant =
      ∑' m : ℕ, 4 * Real.pi ^ 2 * Real.exp Real.pi * HurwitzKernelBounds.f_nat 4 1 1 m := by
  rw [thetaDecayConstant, HurwitzKernelBounds.F_nat,
    (HurwitzKernelBounds.summable_f_nat 4 1 (by norm_num)).tsum_mul_left]

/-- The constant `thetaDecayConstant` is positive. -/
lemma thetaDecayConstant_pos : 0 < thetaDecayConstant := by
  unfold thetaDecayConstant HurwitzKernelBounds.F_nat
  have hsum_pos : 0 < ∑' m : ℕ, HurwitzKernelBounds.f_nat 4 1 1 m :=
    (HurwitzKernelBounds.summable_f_nat 4 1 (by norm_num)).tsum_pos
      (fun m => by unfold HurwitzKernelBounds.f_nat; positivity) 0
      (by unfold HurwitzKernelBounds.f_nat; positivity)
  positivity

/-- For `t ≥ 0`, the `m`-th theta term is at most
`exp (9 * t / 2 - π * exp (2 * t)) * (4 π² e^π f_nat 4 1 1 m)`. -/
lemma thetaTerm_le_decayMajorant (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    thetaTerm m t ≤
      Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) *
        (4 * Real.pi ^ 2 * Real.exp Real.pi * HurwitzKernelBounds.f_nat 4 1 1 m) := by
  let n : ℝ := (m + 1 : ℕ)
  have hn : 1 ≤ n := by simp [n]
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hE : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  calc
    thetaTerm m t ≤
        (4 * Real.pi ^ 2 * n ^ 4 * Real.exp (9 * t / 2)) *
          Real.exp (-Real.pi * n ^ 2 * Real.exp (2 * t)) := by
      simp only [thetaTerm]
      have hsecond : 0 ≤ 6 * Real.pi * n ^ 2 * Real.exp (5 * t / 2) := by positivity
      have hexp : 0 ≤ Real.exp (-Real.pi * n ^ 2 * Real.exp (2 * t)) := by positivity
      nlinarith
    _ = Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) *
          (4 * Real.pi ^ 2 * n ^ 4 *
            Real.exp (-Real.pi * (n ^ 2 - 1) * Real.exp (2 * t))) := by
      rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
      ring_nf
    _ ≤ Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) *
          (4 * Real.pi ^ 2 * n ^ 4 *
            Real.exp (-Real.pi * (n ^ 2 - 1))) := by
      gcongr _ * (_ * Real.exp ?_)
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn2)) (sub_nonneg.mpr hE)]
    _ = Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) *
          (4 * Real.pi ^ 2 * Real.exp Real.pi *
            HurwitzKernelBounds.f_nat 4 1 1 m) := by
      simp only [HurwitzKernelBounds.f_nat, n]
      rw [show -Real.pi * ((((m + 1 : ℕ) : ℝ)) ^ 2 - 1) =
          Real.pi + -Real.pi * ((m : ℝ) + 1) ^ 2 * 1 by push_cast; ring, Real.exp_add]
      push_cast
      ring

/-- For `t ≥ 0`, `thetaPhi t ≤ thetaDecayConstant * exp (9 * t / 2 - π * exp (2 * t))`. -/
theorem thetaPhi_le_exp_decay {t : ℝ} (ht : 0 ≤ t) :
    thetaPhi t ≤ thetaDecayConstant * Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) := by
  calc
    thetaPhi t ≤ ∑' m : ℕ, Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) *
        (4 * Real.pi ^ 2 * Real.exp Real.pi * HurwitzKernelBounds.f_nat 4 1 1 m) :=
      (summable_thetaTerm t).tsum_le_tsum (thetaTerm_le_decayMajorant · ht)
        (summable_thetaDecayMajorant.mul_left _)
    _ = thetaDecayConstant * Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) := by
      rw [summable_thetaDecayMajorant.tsum_mul_left, mul_comm, thetaDecayConstant_eq_tsum]

/-- There is a constant `C > 0` such that for every `t ≥ 0`, `thetaPhi t` is nonnegative and
`thetaPhi t ≤ C * exp (9 * t / 2 - π * exp (2 * t))`. -/
theorem exists_thetaPhi_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      0 ≤ thetaPhi t ∧
        thetaPhi t ≤ C * Real.exp (9 * t / 2 - Real.pi * Real.exp (2 * t)) :=
  ⟨thetaDecayConstant, thetaDecayConstant_pos,
    fun _ ht => ⟨(thetaPhi_pos ht).le, thetaPhi_le_exp_decay ht⟩⟩

end RiemannJensen
