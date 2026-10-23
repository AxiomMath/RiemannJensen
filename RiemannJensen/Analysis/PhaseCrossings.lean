module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Phase crossings and zeros of oscillatory functions

If a continuous function has the form `P x = 2 * R x * (cos (θ x) + E x)` on `[a, b]` with
`R x > 0` and `|E x| < 1 / 2`, and the continuous phase `θ` gains at least `n` half-turns, then
`P` has at least `n` distinct zeros in `(a, b)`. No monotonicity of `θ` is assumed.

## Main definitions

* `RiemannJensen.OrderedZeros`: `P` has `n` strictly increasing zeros in `(a, b)`.

## Main results

* `RiemannJensen.phaseCrossings_orderedZeros`: a phase gain from `c` to `c + nπ`, with
  `cos c = ±1`, yields `n` strictly increasing zeros.
* `RiemannJensen.phaseCrossings_distinctZeros`: the same hypotheses yield an injective family of
  `n` zeros.
* `RiemannJensen.phaseCrossings_of_phaseSpan`: a phase gain of at least `(n + 1)π` between the
  endpoints yields `n` distinct zeros.
-/

@[expose] public section

namespace RiemannJensen

open Set

/-- A list of distinct, increasingly ordered zeros of `P` in the open interval
`(a,b)`. -/
def OrderedZeros (P : ℝ → ℝ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ z : List ℝ, z.length = n ∧ z.Pairwise (· < ·) ∧
    ∀ x ∈ z, x ∈ Ioo a b ∧ P x = 0

private lemma exists_phase_level
    {θ : ℝ → ℝ} {a b level : ℝ}
    (hab : a ≤ b) (hθ : ContinuousOn θ (Icc a b))
    (ha : θ a ≤ level) (hb : level ≤ θ b) :
    ∃ x ∈ Icc a b, θ x = level :=
  intermediate_value_Icc hab hθ ⟨ha, hb⟩

private lemma oscillatory_value_sign
    {P R E θ : ℝ → ℝ} {x c s : ℝ}
    (hR : 0 < R x) (hE : |E x| < 1 / 2)
    (hP : P x = 2 * R x * (Real.cos (θ x) + E x))
    (hθ : θ x = c) (hcos : Real.cos c = s)
    (hs : s = 1 ∨ s = -1) :
    (s = 1 ∧ 0 < P x) ∨ (s = -1 ∧ P x < 0) := by
  obtain ⟨hE₁, hE₂⟩ := abs_lt.mp hE
  rw [hP, hθ, hcos]
  rcases hs with rfl | rfl
  · exact .inl ⟨rfl, by nlinarith⟩
  · exact .inr ⟨rfl, by nlinarith⟩

/-- A function continuous on `[x₀, x₁]` whose values at the endpoints have opposite signs
vanishes somewhere in `(x₀, x₁)`. -/
lemma exists_zero_of_sign_flip {P : ℝ → ℝ} {x₀ x₁ : ℝ} (h : x₀ ≤ x₁)
    (hP : ContinuousOn P (Icc x₀ x₁))
    (hs : (0 < P x₀ ∧ P x₁ < 0) ∨ (P x₀ < 0 ∧ 0 < P x₁)) :
    ∃ z ∈ Ioo x₀ x₁, P z = 0 := by
  rcases hs with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact intermediate_value_Ioo' h hP ⟨h₁, h₀⟩
  · exact intermediate_value_Ioo h hP ⟨h₀, h₁⟩

private lemma next_trig_sign {c s : ℝ}
    (hcos : Real.cos c = s) (hsin : Real.sin c = 0) :
    Real.cos (c + Real.pi) = -s ∧ Real.sin (c + Real.pi) = 0 :=
  ⟨by simp [hcos], by simp [hsin]⟩

/-- **Phase-crossing lemma.**  Suppose a continuous oscillatory expression has
relative error strictly smaller than one half.  If its continuous phase crosses
`n` successive half-turns, then the expression has `n` distinct, increasingly
ordered zeros. No monotonicity of `θ` is assumed. -/
theorem phaseCrossings_orderedZeros
    (P R E θ : ℝ → ℝ) (a b c s : ℝ) (n : ℕ)
    (hab : a ≤ b)
    (hPcont : ContinuousOn P (Icc a b))
    (hθcont : ContinuousOn θ (Icc a b))
    (hR : ∀ x ∈ Icc a b, 0 < R x)
    (hE : ∀ x ∈ Icc a b, |E x| < 1 / 2)
    (hformula : ∀ x ∈ Icc a b,
      P x = 2 * R x * (Real.cos (θ x) + E x))
    (hcos : Real.cos c = s) (hsin : Real.sin c = 0)
    (hs : s = 1 ∨ s = -1)
    (ha : θ a ≤ c)
    (hb : c + (n : ℝ) * Real.pi ≤ θ b) :
    OrderedZeros P a b n := by
  induction n generalizing a c s with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ n ih =>
      have hpi := Real.pi_pos
      have hn := n.cast_nonneg (α := ℝ)
      push_cast at hb
      obtain ⟨x₀, hx₀, hθx₀⟩ := exists_phase_level hab hθcont ha (by nlinarith)
      obtain ⟨x₁, hx₁, hθx₁⟩ : ∃ x ∈ Icc x₀ b, θ x = c + Real.pi := exists_phase_level hx₀.2
        (hθcont.mono (Icc_subset_Icc hx₀.1 le_rfl)) (by linarith) (by nlinarith)
      have hx₀x₁ : x₀ < x₁ := hx₁.1.lt_of_ne (by rintro rfl; linarith)
      have hx₁ab : x₁ ∈ Icc a b := ⟨hx₀.1.trans hx₁.1, hx₁.2⟩
      have hs₁ : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
      obtain ⟨hcos₁, hsin₁⟩ := next_trig_sign hcos hsin
      obtain ⟨z, hz, hPz⟩ := exists_zero_of_sign_flip hx₀x₁.le
          (hPcont.mono (Icc_subset_Icc hx₀.1 hx₁.2)) <| by
        rcases oscillatory_value_sign (hR x₀ hx₀) (hE x₀ hx₀) (hformula x₀ hx₀) hθx₀ hcos hs,
          oscillatory_value_sign (hR x₁ hx₁ab) (hE x₁ hx₁ab) (hformula x₁ hx₁ab) hθx₁ hcos₁
            hs₁ with ⟨⟨h, h₀⟩ | ⟨h, h₀⟩, ⟨h', h₁⟩ | ⟨h', h₁⟩⟩ <;>
          first | (exfalso; linarith) | exact .inl ⟨h₀, h₁⟩ | exact .inr ⟨h₀, h₁⟩
      obtain ⟨zs, hlen, hsorted, hzs⟩ := ih x₁ (c + Real.pi) (-s) hx₁.2
        (hPcont.mono (Icc_subset_Icc hx₁ab.1 le_rfl))
        (hθcont.mono (Icc_subset_Icc hx₁ab.1 le_rfl))
        (fun x hx => hR x ⟨hx₁ab.1.trans hx.1, hx.2⟩)
        (fun x hx => hE x ⟨hx₁ab.1.trans hx.1, hx.2⟩)
        (fun x hx => hformula x ⟨hx₁ab.1.trans hx.1, hx.2⟩)
        hcos₁ hsin₁ hs₁ hθx₁.le (by linarith)
      refine ⟨z :: zs, by simp [hlen], List.pairwise_cons.2
        ⟨fun y hy => hz.2.trans (hzs y hy).1.1, hsorted⟩, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨⟨hx₀.1.trans_lt hz.1, hz.2.trans_le hx₁.2⟩, hPz⟩,
        fun y hy => ⟨⟨hx₁ab.1.trans_lt (hzs y hy).1.1, (hzs y hy).1.2⟩, (hzs y hy).2⟩⟩

/-- The ordered zeros supplied by `phaseCrossings_orderedZeros` are pairwise
distinct. -/
theorem phaseCrossings_distinctZeros
    (P R E θ : ℝ → ℝ) (a b c s : ℝ) (n : ℕ)
    (hab : a ≤ b)
    (hPcont : ContinuousOn P (Icc a b))
    (hθcont : ContinuousOn θ (Icc a b))
    (hR : ∀ x ∈ Icc a b, 0 < R x)
    (hE : ∀ x ∈ Icc a b, |E x| < 1 / 2)
    (hformula : ∀ x ∈ Icc a b,
      P x = 2 * R x * (Real.cos (θ x) + E x))
    (hcos : Real.cos c = s) (hsin : Real.sin c = 0)
    (hs : s = 1 ∨ s = -1)
    (ha : θ a ≤ c)
    (hb : c + (n : ℝ) * Real.pi ≤ θ b) :
    ∃ z : Fin n → ℝ, Function.Injective z ∧
      ∀ i, z i ∈ Ioo a b ∧ P (z i) = 0 := by
  obtain ⟨zs, rfl, hpair, hroot⟩ := phaseCrossings_orderedZeros
    P R E θ a b c s n hab hPcont hθcont hR hE hformula hcos hsin hs ha hb
  exact ⟨zs.get, fun _ _ h => hpair.nodup.get_inj_iff.mp h, fun i => hroot _ (zs.get_mem i)⟩

/-- Endpoint-only form of the phase-crossing lemma.  A phase gain of at least
`(n+1)π` forces `n` distinct zeros.  No monotonicity of `θ` is assumed. -/
theorem phaseCrossings_of_phaseSpan
    (P R E θ : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hab : a ≤ b)
    (hPcont : ContinuousOn P (Icc a b))
    (hθcont : ContinuousOn θ (Icc a b))
    (hR : ∀ x ∈ Icc a b, 0 < R x)
    (hE : ∀ x ∈ Icc a b, |E x| < 1 / 2)
    (hformula : ∀ x ∈ Icc a b,
      P x = 2 * R x * (Real.cos (θ x) + E x))
    (hspan : ((n + 1 : ℕ) : ℝ) * Real.pi ≤ θ b - θ a) :
    ∃ z : Fin n → ℝ, Function.Injective z ∧
      ∀ i, z i ∈ Ioo a b ∧ P (z i) = 0 := by
  set k : ℤ := ⌈θ a / Real.pi⌉
  have ha : θ a ≤ k * Real.pi := (div_le_iff₀ Real.pi_pos).mp (Int.le_ceil _)
  have hc_lt : k * Real.pi < θ a + Real.pi := by
    rw [← lt_div_iff₀ Real.pi_pos, add_div, div_self Real.pi_pos.ne']
    exact Int.ceil_lt_add_one _
  push_cast at hspan
  exact phaseCrossings_distinctZeros P R E θ a b _ _ n hab hPcont hθcont hR hE hformula rfl
    (Real.sin_int_mul_pi k) ((abs_eq zero_le_one).mp (Real.abs_cos_int_mul_pi k)) ha
    (by linarith)

end RiemannJensen
