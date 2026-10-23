module

public import RiemannJensen.Dedekind.CompletedZetaAdapter

/-!
# The meromorphic continuation of the Dedekind zeta function

This file extracts from the completed zeta package an entire continuation of
`(s - 1) ζ_K(s)`, and hence a project-native continuation of `ζ_K` away from
its unique possible pole at `1`. It follows that `ζ_K` has an analytic continuation to
`ℂ \ {1}`, unique by the identity theorem, and that the completed xi-function `dedekindXi K`
built from it agrees with `entireDedekindXi K` near `1 / 2`, so the two have the same Jensen
polynomials.

## Main results

* `exists_isDedekindZetaContinuation`: `ζ_K` has an analytic continuation to `ℂ \ {1}`.
* `isDedekindZetaContinuation_unique`: Two such continuations agree on `ℂ \ {1}`.
* `dedekindJensenK_eq`: `dedekindJensenK K d = dedekindJensen (entireDedekindXi K) d`.
* `dedekindNegativeRootCountK_eq`: The same for the negative root counts.
-/

@[expose] public section

namespace RiemannJensen

open Complex Set NumberField

noncomputable section

private theorem discr_abs_cast_ne_zero (K : Type) [Field K] [NumberField K] :
    (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 :=
  Int.cast_ne_zero.mpr (abs_ne_zero.mpr (NumberField.discr_ne_zero K))

private theorem one_le_nrRealPlaces_add_nrComplexPlaces (K : Type) [Field K] [NumberField K] :
    1 ≤ InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

/-- `π ^ (s / 2) / (2 Γ(s / 2 + 1))`, so that `s * piGammaFactor s = Γℝ(s)⁻¹`. -/
def piGammaFactor (s : ℂ) : ℂ :=
  ((Real.pi : ℝ) : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2 + 1))⁻¹ / 2

private theorem differentiable_piGammaFactor : Differentiable ℂ piGammaFactor := by
  unfold piGammaFactor
  refine Differentiable.div_const (Differentiable.mul ?_ ?_) 2
  · exact (differentiable_id.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact Complex.differentiable_one_div_Gamma.comp
      ((differentiable_id.div_const 2).add_const 1)

private theorem mul_piGammaFactor (s : ℂ) : s * piGammaFactor s = (Complex.Gammaℝ s)⁻¹ := by
  rw [piGammaFactor, Complex.Gammaℝ_def, mul_inv, ← Complex.cpow_neg, neg_div, neg_neg,
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s / 2)]
  ring

/-- The factor turning the entire `rawDedekindXi K` into `(s - 1) ζ_K(s)` for `1 < Re s`. -/
def regularizingFactor (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹ *
    (piGammaFactor s * (Complex.Gammaℝ s)⁻¹ ^
      (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) *
      (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K)

private theorem differentiable_regularizingFactor (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (regularizingFactor K) := by
  have hD := discr_abs_cast_ne_zero K
  exact (Differentiable.inv ((differentiable_id.div_const 2).const_cpow (Or.inl hD))
    (fun s => Complex.cpow_ne_zero_iff.mpr (Or.inl hD))).mul
      ((differentiable_piGammaFactor.mul (Complex.differentiable_Gammaℝ_inv.pow _)).mul
        ((Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)).pow _))

/-- An entire function agreeing with `(s - 1) ζ_K(s)` for `1 < Re s`. -/
def regularizedDedekindZeta (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  rawDedekindXi K s * regularizingFactor K s

/-- The regularized continuation is entire. -/
theorem regularizedDedekindZeta_entire (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (regularizedDedekindZeta K) :=
  (rawDedekindXi_entire K).mul (differentiable_regularizingFactor K)

/-- On the half-plane of absolute convergence, the regularized continuation
is `(s - 1)` times the Dirichlet series. -/
theorem regularizedDedekindZeta_eq_raw (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) : regularizedDedekindZeta K s = (s - 1) * rawDedekindZeta K s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  have hDs : (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (discr_abs_cast_ne_zero K))
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓ1 : Complex.Gammaℝ (s + 1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
  have hG : s * (piGammaFactor s * (Complex.Gammaℝ s)⁻¹ ^
      (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) *
        (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K) =
      (Complex.Gammaℝ s)⁻¹ ^
          (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K) *
        (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K := by
    calc
      _ = (s * piGammaFactor s) * (Complex.Gammaℝ s)⁻¹ ^
          (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) *
          (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K := by ring
      _ = _ := by
        rw [mul_piGammaFactor, ← pow_succ',
          Nat.sub_add_cancel (one_le_nrRealPlaces_add_nrComplexPlaces K)]
  rw [rawDedekindZeta]
  calc
    _ = (s - 1) * packageCompletedZeta K s *
        ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹ *
        (s * (piGammaFactor s * (Complex.Gammaℝ s)⁻¹ ^
          (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) *
          (Complex.Gammaℝ (s + 1))⁻¹ ^ InfinitePlace.nrComplexPlaces K)) := by
      rw [regularizedDedekindZeta, regularizingFactor, rawDedekindXi_eq K s hs0 hs1]
      ring
    _ = (s - 1) * NumberField.dedekindZeta K s *
        (((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2) *
          ((((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹) *
        (Complex.Gammaℝ s * (Complex.Gammaℝ s)⁻¹) ^
          (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K) *
        (Complex.Gammaℝ (s + 1) * (Complex.Gammaℝ (s + 1))⁻¹) ^
          InfinitePlace.nrComplexPlaces K) := by
      rw [hG, packageCompletedZeta_eq_product K s hs, ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
      ring
    _ = _ := by
      rw [mul_inv_cancel₀ hDs, mul_inv_cancel₀ hΓ, mul_inv_cancel₀ hΓ1, one_pow, one_pow,
        mul_one, mul_one, mul_one]

/-- The reciprocal `(|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂})⁻¹` of the discriminant and
archimedean factor of `ζ_K`, written as a product of reciprocals so that it is entire. -/
def dedekindInverseArchimedeanFactor (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹ *
    (Complex.Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
    (Complex.Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K

/-- The reciprocal archimedean factor is entire. -/
theorem dedekindInverseArchimedeanFactor_entire (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (dedekindInverseArchimedeanFactor K) := by
  have hD := discr_abs_cast_ne_zero K
  exact ((Differentiable.inv
    ((differentiable_id.div_const 2).const_cpow (Or.inl hD))
    (fun s => Complex.cpow_ne_zero_iff.mpr (Or.inl hD))).mul
      (Complex.differentiable_Gammaℝ_inv.pow _)).mul
      (Complex.differentiable_Gammaℂ_inv.pow _)

private theorem arch_mul_inverse_eq_one (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 0 < s.re) :
    (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
      Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K) *
      dedekindInverseArchimedeanFactor K s = 1 := by
  have hD : (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (discr_abs_cast_ne_zero K))
  have hR : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hC : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_)
      (Complex.Gamma_ne_zero_of_re_pos hs)
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  rw [dedekindInverseArchimedeanFactor]
  calc
    _ = ((((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹)) *
        (Complex.Gammaℝ s * (Complex.Gammaℝ s)⁻¹) ^ InfinitePlace.nrRealPlaces K *
        (Complex.Gammaℂ s * (Complex.Gammaℂ s)⁻¹) ^ InfinitePlace.nrComplexPlaces K := by
      ring
    _ = 1 := by
      rw [mul_inv_cancel₀ hD, mul_inv_cancel₀ hR, mul_inv_cancel₀ hC, one_pow, one_pow,
        mul_one, mul_one]

/-- For every `s`, `s` times the regularized continuation equals `rawDedekindXi K s` times
`(|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂})⁻¹`. -/
theorem regularizedDedekindZeta_scaled_eq (K : Type) [Field K] [NumberField K] (s : ℂ) :
    s * regularizedDedekindZeta K s =
      rawDedekindXi K s * dedekindInverseArchimedeanFactor K s := by
  let f : ℂ → ℂ := fun z => z * regularizedDedekindZeta K z
  let g : ℂ → ℂ := fun z => rawDedekindXi K z * dedekindInverseArchimedeanFactor K z
  have hf : Differentiable ℂ f :=
    differentiable_id.mul (regularizedDedekindZeta_entire K)
  have hg : Differentiable ℂ g :=
    (rawDedekindXi_entire K).mul (dedekindInverseArchimedeanFactor_entire K)
  have heq : Set.EqOn f g Set.univ := by
    refine holomorphic_eqOn_of_open_agreement Set.univ {z : ℂ | 1 < z.re}
      f g isOpen_univ isPreconnected_univ
      (isOpen_lt continuous_const Complex.continuous_re) ⟨2, by norm_num⟩
      (fun _ _ => Set.mem_univ _) hf.differentiableOn hg.differentiableOn ?_
    intro z hz
    have hz0 : z ≠ 0 := Complex.ne_zero_of_one_lt_re hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      norm_num at hz
    dsimp [f, g]
    rw [regularizedDedekindZeta_eq_raw K z hz,
      rawDedekindXi_eq K z hz0 hz1, packageCompletedZeta_eq_product K z hz, rawDedekindZeta]
    calc
      z * ((z - 1) * NumberField.dedekindZeta K z) =
          z * (z - 1) * NumberField.dedekindZeta K z := by ring
      _ = z * (z - 1) *
          ((((|NumberField.discr K| : ℤ) : ℂ) ^ (z / 2) *
            Complex.Gammaℝ z ^ InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ z ^ InfinitePlace.nrComplexPlaces K) *
            dedekindInverseArchimedeanFactor K z) *
          NumberField.dedekindZeta K z := by
        rw [arch_mul_inverse_eq_one K z (zero_lt_one.trans hz)]
        ring
      _ = _ := by ring
  exact heq (Set.mem_univ s)

/-- The project-native meromorphic continuation of the Dedekind zeta
function.  Its totalized value at the pole `1` is immaterial. -/
def analyticDedekindZeta (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  regularizedDedekindZeta K s / (s - 1)

/-- The continued Dedekind zeta function is holomorphic away from `1`. -/
theorem analyticDedekindZeta_holomorphic (K : Type) [Field K] [NumberField K] :
    DifferentiableOn ℂ (analyticDedekindZeta K) ({1}ᶜ : Set ℂ) := fun s hs =>
  (regularizedDedekindZeta_entire K s).div (differentiableAt_id.sub_const 1)
    (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)) |>.differentiableWithinAt

/-- The continuation agrees with the Dirichlet series `rawDedekindZeta K s` for `1 < Re s`. -/
theorem analyticDedekindZeta_eq_raw (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) : analyticDedekindZeta K s = rawDedekindZeta K s := by
  rw [analyticDedekindZeta, regularizedDedekindZeta_eq_raw K s hs]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr (by
    rintro rfl
    norm_num at hs))

/-- The continued Dedekind zeta function commutes with conjugation away from
its pole. -/
theorem analyticDedekindZeta_conj (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : s ≠ 1) :
    analyticDedekindZeta K (star s) = star (analyticDedekindZeta K s) :=
  conjugation_symmetry_off_one (analyticDedekindZeta K)
    (analyticDedekindZeta_holomorphic K) (fun z hz => by
      rw [analyticDedekindZeta_eq_raw K (star z) (by simpa using hz),
        analyticDedekindZeta_eq_raw K z hz]
      exact rawDedekindZeta_conj_of_one_lt_re K z hz) s hs

/-- The completed xi product identity throughout the open right half-plane,
away from the zeta pole at `1`. -/
theorem entireDedekindXi_eq_product_of_pos_re (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    entireDedekindXi K s =
      (s * (s - 1) / 2) *
        (dedekindDiscriminantAbs K : ℂ) ^ (s / 2) *
        dedekindGammaR s ^ dedekindRealPlaces K *
        dedekindGammaC s ^ dedekindComplexPlaces K *
        analyticDedekindZeta K s := by
  have hreg : regularizedDedekindZeta K s =
      (s - 1) * analyticDedekindZeta K s := by
    rw [analyticDedekindZeta]
    field_simp
  have hraw : rawDedekindXi K s = s * regularizedDedekindZeta K s *
      (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
        Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K) := by
    calc
      _ = rawDedekindXi K s *
          (dedekindInverseArchimedeanFactor K s *
            (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
              Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
              Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K)) := by
        rw [mul_comm (dedekindInverseArchimedeanFactor K s),
          arch_mul_inverse_eq_one K s hs, mul_one]
      _ = (rawDedekindXi K s * dedekindInverseArchimedeanFactor K s) *
          (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
            Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K) := by ring
      _ = (s * regularizedDedekindZeta K s) *
          (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
            Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces K) := by
        rw [← regularizedDedekindZeta_scaled_eq]
      _ = _ := by ring
  rw [entireDedekindXi_def, hraw, hreg, dedekindDiscriminantAbs, dedekindGammaR, dedekindGammaC,
    dedekindRealPlaces, dedekindComplexPlaces]
  have hdisc :
      (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)) =
        (((|NumberField.discr K| : ℤ) : ℂ)) := by
    norm_cast
  rw [hdisc]
  ring

/-- `analyticDedekindZeta K` is an analytic continuation of the Dedekind zeta function. -/
theorem isDedekindZetaContinuation_analyticDedekindZeta (K : Type) [Field K] [NumberField K] :
    IsDedekindZetaContinuation K (analyticDedekindZeta K) :=
  ⟨analyticDedekindZeta_holomorphic K, analyticDedekindZeta_eq_raw K⟩

/-- The Dedekind zeta function of every number field has an analytic continuation to
`ℂ \ {1}`. -/
theorem exists_isDedekindZetaContinuation (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, IsDedekindZetaContinuation K f :=
  ⟨_, isDedekindZetaContinuation_analyticDedekindZeta K⟩

/-- Two analytic continuations of the Dedekind zeta function agree on `ℂ \ {1}`. -/
theorem isDedekindZetaContinuation_unique (K : Type) [Field K] [NumberField K]
    {f g : ℂ → ℂ} (hf : IsDedekindZetaContinuation K f) (hg : IsDedekindZetaContinuation K g) :
    ∀ s : ℂ, s ≠ 1 → f s = g s := fun s hs =>
  holomorphic_eqOn_of_open_agreement {1}ᶜ {z : ℂ | 1 < z.re} f g isOpen_compl_singleton
    (puncturedPlane_isPreconnected 1) (isOpen_lt continuous_const Complex.continuous_re)
    ⟨2, by norm_num⟩ (fun z hz => by
      rintro rfl
      norm_num at hz)
    hf.differentiableOn hg.differentiableOn
    (fun z hz => (hf.eq_dedekindZeta z hz).trans (hg.eq_dedekindZeta z hz).symm) hs

/-- `continuedDedekindZeta K` agrees with `analyticDedekindZeta K` off `1`. -/
theorem continuedDedekindZeta_eq (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : s ≠ 1) :
    continuedDedekindZeta K s = analyticDedekindZeta K s :=
  isDedekindZetaContinuation_unique K
    (Classical.epsilon_spec (exists_isDedekindZetaContinuation K))
    (isDedekindZetaContinuation_analyticDedekindZeta K) s hs

/-- On the right half-plane, away from `1`, `dedekindXi K` is the entire xi-function. -/
theorem dedekindXi_eq_entireDedekindXi (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    dedekindXi K s = entireDedekindXi K s := by
  rw [entireDedekindXi_eq_product_of_pos_re K s hs hs1, dedekindXi, completedDedekindZeta,
    continuedDedekindZeta_eq K s hs1, dedekindDiscriminantAbs, dedekindGammaR, dedekindGammaC,
    dedekindRealPlaces, dedekindComplexPlaces,
    show (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ)) = (((|NumberField.discr K| : ℤ) : ℂ)) by
      norm_cast]
  ring

/-- `dedekindXi K` agrees with the entire xi-function near `1 / 2`. -/
theorem dedekindXi_eventuallyEq_entireDedekindXi (K : Type) [Field K] [NumberField K] :
    dedekindXi K =ᶠ[nhds (1 / 2)] entireDedekindXi K := by
  have hU : IsOpen ({z : ℂ | 0 < z.re} ∩ {1}ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  filter_upwards [hU.mem_nhds ⟨by norm_num, by norm_num⟩] with s hs
  exact dedekindXi_eq_entireDedekindXi K s hs.1 hs.2

/-- The Jensen polynomials of `dedekindXi K` are those of the entire xi-function. -/
theorem dedekindJensen_dedekindXi (K : Type) [Field K] [NumberField K] :
    dedekindJensen (dedekindXi K) = dedekindJensen (entireDedekindXi K) := by
  have hc : centeredDedekindFunction (dedekindXi K) =ᶠ[nhds 0]
      centeredDedekindFunction (entireDedekindXi K) :=
    (dedekindXi_eventuallyEq_entireDedekindXi K).comp_tendsto
      ((continuous_const_add (1 / 2 : ℂ)).tendsto' 0 (1 / 2) (add_zero _))
  have hγ : dedekindGammaCoeff (dedekindXi K) = dedekindGammaCoeff (entireDedekindXi K) := by
    funext j
    rw [dedekindGammaCoeff, dedekindGammaCoeff, hc.iteratedDeriv_eq]
  funext d
  rw [dedekindJensen, dedekindJensen, hγ]

/-- The degree-`d` Dedekind Jensen polynomial of `K` is that of the entire xi-function. -/
theorem dedekindJensenK_eq (K : Type) [Field K] [NumberField K] (d : ℕ) :
    dedekindJensenK K d = dedekindJensen (entireDedekindXi K) d := by
  rw [dedekindJensenK, dedekindJensen_dedekindXi]

/-- The negative root count of `K` is that of the entire xi-function. -/
theorem dedekindNegativeRootCountK_eq (K : Type) [Field K] [NumberField K] (d : ℕ) :
    dedekindNegativeRootCountK K d = dedekindNegativeRootCount (entireDedekindXi K) d := by
  rw [dedekindNegativeRootCountK, dedekindNegativeRootCount, dedekindNegativeRootCount,
    dedekindJensen_dedekindXi]

end

end RiemannJensen
