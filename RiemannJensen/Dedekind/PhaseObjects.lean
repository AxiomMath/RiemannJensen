module

public import RiemannJensen.Dedekind.GeometryDefs
public import RiemannJensen.Dedekind.Foundation
public import RiemannJensen.Analysis.LeadingSaddlePolar
public import RiemannJensen.Analysis.ZetaLog

/-!
# Dedekind phase objects

The explicit phase correction `ω_d` of the Dedekind leading saddle term, together with
the objects it is built from, and the four endgame statements about it: continuity,
a uniform bound, the exact polar form of the leading term, and the endpoint phase-span
bound.

Every object is defined at the field's own logarithmic scale `Λ_d`; the saddle geometry
reuses the field-independent definitions of `RiemannJensen.Dedekind.GeometryDefs`.
-/

@[expose] public section

namespace RiemannJensen.Dedekind

open Complex Set Filter Topology NumberField

variable (K : Type*) [Field K] [NumberField K]

/-! ### Scale and saddle geometry -/

/-- The Dedekind power exponent `μ_K = 2 - r₁ / 4`. -/
noncomputable def muK : ℝ := 2 - (dedekindRealPlaces K : ℝ) / 4

/-- The Dedekind leading constant `c_K = 2^(3r₁/4 + r₂ - 1) π^(r₁/4) Δ_K^(1/4)`. -/
noncomputable def cK : ℝ :=
  (2 : ℝ) ^ (3 * (dedekindRealPlaces K : ℝ) / 4 + dedekindComplexPlaces K - 1) *
    Real.pi ^ ((dedekindRealPlaces K : ℝ) / 4) * dedekindDiscriminantAbs K ^ ((1 : ℝ) / 4)

/-- The Dedekind gamma scale `a_K = 2π Δ_K^(-1/N)`. -/
noncomputable def dedekindScaleA : ℝ :=
  2 * Real.pi * dedekindDiscriminantAbs K ^ (-(1 / (dedekindDegree K : ℝ)))

/-- The saddle scale `T_d`: the infimum of the `t > a_K e` with
`d ≤ N t / (2π) (log (t / a_K) - 1)`. -/
noncomputable def scaleT (d : ℕ) : ℝ :=
  sInf {t : ℝ | dedekindScaleA K * Real.exp 1 < t ∧
    (d : ℝ) ≤ (dedekindDegree K : ℝ) * t / (2 * Real.pi) *
      (Real.log (t / dedekindScaleA K) - 1)}

/-- The logarithmic scale `Λ_d = 2 (log (T_d / a_K) - 1)`. -/
noncomputable def scaleLambda (d : ℕ) : ℝ :=
  2 * (Real.log (scaleT K d / dedekindScaleA K) - 1)

/-- The saddle radius `r_d(α)` at the field's logarithmic scale. -/
noncomputable def saddleRadius (d : ℕ) (α : ℝ) : ℝ :=
  saddleRadiusAtLambda (scaleLambda K d) α

/-- The saddle parameter `q_d(α)` at the field's logarithmic scale. -/
noncomputable def saddleQ (d : ℕ) (α : ℝ) : ℝ :=
  saddleQAtLambda (scaleLambda K d) α

/-- The saddle edge `q_{e,d} = q_d(0)`. -/
noncomputable def edgeQ (d : ℕ) : ℝ := saddleQ K d 0

/-- The inverse saddle angle `α_d(q)`: the infimum of the `α ∈ [0, π/2]` with
`q ≤ q_d(α)`. -/
noncomputable def saddleAngle (d : ℕ) (q : ℝ) : ℝ :=
  sInf {α : ℝ | 0 ≤ α ∧ α ≤ Real.pi / 2 ∧ q ≤ saddleQ K d α}

/-- The lower saddle `u_{d,q} = r_d(α_d(q))² e^{-2iα_d(q)}`. -/
noncomputable def saddle (d : ℕ) (q : ℝ) : ℂ :=
  ((saddleRadius K d (saddleAngle K d q)) ^ 2 : ℝ) *
    Complex.exp (-2 * Complex.I * (saddleAngle K d q : ℂ))

/-- The saddle phase `h_{d,q}` at the field's logarithmic scale. -/
noncomputable def phase (d : ℕ) (q : ℝ) (u : ℂ) : ℂ :=
  saddlePhaseAtLambda (scaleLambda K d) q u

/-- The angular Hessian `D_{d,q} = u_{d,q}² h_{d,q}''(u_{d,q})`. -/
noncomputable def saddleHessian (d : ℕ) (q : ℝ) : ℂ :=
  saddle K d q ^ 2 * iteratedDeriv 2 (phase K d q) (saddle K d q)

/-- The saddle action `S_d(q) = Im h_{d,q}(u_{d,q})`. -/
noncomputable def saddleAction (d : ℕ) (q : ℝ) : ℝ :=
  (phase K d q (saddle K d q)).im

/-- The fixed local-width constant `ε₀ = 1/1000`. -/
noncomputable def localEpsilon : ℝ := 1 / 1000

/-- The local width `ℓ_{d,q} = ε₀ min(α_d(q), cos α_d(q))`. -/
noncomputable def localWidth (d : ℕ) (q : ℝ) : ℝ :=
  localEpsilon * min (saddleAngle K d q) (Real.cos (saddleAngle K d q))

/-- The scaled contour argument `w_{d,q}(θ) = T_d r_d(α_d(q)) e^{iθ/2}`. -/
noncomputable def contourW (d : ℕ) (q θ : ℝ) : ℂ :=
  (scaleT K d * saddleRadius K d (saddleAngle K d q) : ℝ) *
    Complex.exp (Complex.I * (θ : ℂ) / 2)

/-- The edge offset `τ_{M,d} = M √(log d / d)`. -/
noncomputable def edgeOffset (M : ℝ) (d : ℕ) : ℝ :=
  M * Real.sqrt (Real.log d / d)

/-- The upper counting endpoint `Q_{c₀,d} = c₀ T_d`. -/
noncomputable def upperEndpoint (c₀ : ℝ) (d : ℕ) : ℝ := c₀ * scaleT K d

/-- The counting window `I_{M,c₀,d} = [q_{e,d} + τ_{M,d}, Q_{c₀,d}]`. -/
noncomputable def countingWindow (M c₀ : ℝ) (d : ℕ) : Set ℝ :=
  Set.Icc (edgeQ K d + edgeOffset M d) (upperEndpoint K c₀ d)

/-! ### Gamma remainder and its logarithm -/

/-- The real shifted-Gamma remainder
`g_ℝ(w) = Γ(w/2 + 1/4) / (√(2π) (w/2)^(w/2 - 1/4) e^(-w/2))`. -/
noncomputable def gammaRemainderReal (w : ℂ) : ℂ :=
  Complex.Gamma (w / 2 + 1 / 4) /
    ((Real.sqrt (2 * Real.pi) : ℂ) * (w / 2) ^ (w / 2 - 1 / 4) * Complex.exp (-w / 2))

/-- The complex shifted-Gamma remainder `g_ℂ(w) = Γ(w + 1/2) / (√(2π) w^w e^(-w))`. -/
noncomputable def gammaRemainderComplex (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1 / 2) /
    ((Real.sqrt (2 * Real.pi) : ℂ) * w ^ w * Complex.exp (-w))

/-- The Dedekind Stirling remainder `g_K(w) = (1 - 1/(4w²)) g_ℝ(w)^{r₁} g_ℂ(w)^{r₂}`. -/
noncomputable def dedekindGammaRemainder (w : ℂ) : ℂ :=
  (1 - 1 / (4 * w ^ 2)) * gammaRemainderReal w ^ dedekindRealPlaces K *
    gammaRemainderComplex w ^ dedekindComplexPlaces K

/-- The holomorphic logarithm of `g_ℂ` on the right half-plane, from Binet's form of
Stirling's formula. -/
noncomputable def gammaComplexLog (w : ℂ) : ℂ :=
  StirlingScratch.stirR (w + 1 / 2) + w * (Complex.log (w + 1 / 2) - Complex.log w) - 1 / 2

/-- The Dedekind Gamma logarithm `L_{g,K}`: the sum of the logarithms of the three factors
of `g_K`, each the one that is real on the positive real axis. -/
noncomputable def dedekindGammaLog (w : ℂ) : ℂ :=
  Complex.log (1 - 1 / (4 * w ^ 2)) +
    (dedekindRealPlaces K : ℂ) * GammaCore.gammaCoreLog w +
    (dedekindComplexPlaces K : ℂ) * gammaComplexLog w

/-! ### Dedekind zeta and its Euler logarithm -/

/-- The totalized Dedekind zeta function: the holomorphic continuation of
`NumberField.dedekindZeta K` off `1`, and `0` at `1`. -/
noncomputable def analyticDedekindZeta (s : ℂ) : ℂ := by
  classical
  exact if s = 1 then 0 else
    if h : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
        ∀ z : ℂ, 1 < z.re → f z = rawDedekindZeta K z then h.choose s
    else rawDedekindZeta K s

/-- The Dedekind Euler logarithm
`𝓛_K(s) = ∑_𝔭 ∑_{m ≥ 1} (N𝔭)^{-ms} / m` for `re s > 1`, and `0` otherwise. -/
noncomputable def dedekindEulerLog (s : ℂ) : ℂ := by
  classical
  exact if 1 < s.re then
    ∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∑' m : ℕ,
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)) / ((m : ℂ) + 1)
  else 0

/-! ### Amplitude, leading term and phase correction -/

/-- The contour amplitude `a_{d,q}(θ) = c_K w^{μ_K} ζ_K(1/2 + w) g_K(w)`. -/
noncomputable def dedekindAmplitude (d : ℕ) (q θ : ℝ) : ℂ :=
  (cK K : ℂ) * contourW K d q θ ^ (muK K : ℂ) *
    analyticDedekindZeta K (1 / 2 + contourW K d q θ) *
    dedekindGammaRemainder K (contourW K d q θ)

/-- The leading saddle contribution
`Z_d(q) = d!/d^d · a_{d,q}(-2α_d(q)) e^{d h_{d,q}(u_{d,q})} / √(2π d D_{d,q})`. -/
noncomputable def leadingSaddle (d : ℕ) (q : ℝ) : ℂ :=
  ((d.factorial : ℂ) / (d : ℂ) ^ d) *
    (dedekindAmplitude K d q (-2 * saddleAngle K d q) *
      Complex.exp ((d : ℂ) * phase K d q (saddle K d q))) /
    Complex.sqrt (2 * Real.pi * d * saddleHessian K d q)

/-- The Gamma/zeta argument at the lower saddle, `w_{d,q}(-2α_d(q))`. -/
noncomputable def saddlePoint (d : ℕ) (q : ℝ) : ℂ :=
  contourW K d q (-2 * saddleAngle K d q)

/-- The explicit phase correction
`ω_d(q) = -μ_K α_d(q) + Im 𝓛_K(1/2 + w) + Im L_{g,K}(w) - Arg D_{d,q} / 2`,
with `w = w_{d,q}(-2α_d(q))`. -/
noncomputable def phaseCorrection (d : ℕ) (q : ℝ) : ℝ :=
  -muK K * saddleAngle K d q +
    (dedekindEulerLog K (1 / 2 + saddlePoint K d q)).im +
    (dedekindGammaLog K (saddlePoint K d q)).im -
    Complex.arg (saddleHessian K d q) / 2

/-- The explicit Hessian `1 - (π r e^{-iα}/4)(1 + (2 log r - 2iα)/Λ)` at logarithmic
scale `Λ`. -/
noncomputable def explicitSaddleHessianAtLambda (Λ r α : ℝ) : ℂ :=
  1 - (((Real.pi * r / 4 : ℝ) : ℂ) *
    Complex.exp (((-α : ℝ) : ℂ) * Complex.I) *
    (1 + (((2 * Real.log r / Λ : ℝ) : ℂ) - ((2 * α / Λ : ℝ) : ℂ) * Complex.I)))

/-! ### Elementary facts about the definitions -/

/-- The inverse saddle angle always lies in `[0, π/2]`. -/
theorem saddleAngle_mem_Icc (d : ℕ) (q : ℝ) :
    saddleAngle K d q ∈ Icc 0 (Real.pi / 2) := by
  unfold saddleAngle
  set S := {α : ℝ | 0 ≤ α ∧ α ≤ Real.pi / 2 ∧ q ≤ saddleQ K d α}
  rcases S.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · rw [h, Real.sInf_empty]
    exact ⟨le_rfl, by positivity⟩
  · exact ⟨le_csInf ⟨a, ha⟩ (fun b hb => hb.1), (csInf_le ⟨0, fun b hb => hb.1⟩ ha).trans ha.2.1⟩

/-- The Dedekind gamma scale `a_K` is positive. -/
theorem dedekindScaleA_pos : 0 < dedekindScaleA K := by
  unfold dedekindScaleA
  have := dedekindDiscriminantAbs_pos K
  positivity

/-- The saddle scale `T_d` is nonnegative. -/
theorem scaleT_nonneg (d : ℕ) : 0 ≤ scaleT K d :=
  Real.sInf_nonneg fun t ht => by nlinarith [(dedekindScaleA_pos K).le, ht.1, Real.exp_pos 1]

/-- The saddle radius `r_d(α)` is nonnegative. -/
theorem saddleRadius_nonneg (d : ℕ) (α : ℝ) : 0 ≤ saddleRadius K d α :=
  Real.sInf_nonneg (fun _ hr => hr.1.le)

/-- The local width is nonnegative. -/
theorem localWidth_nonneg (d : ℕ) (q : ℝ) : 0 ≤ localWidth K d q := by
  obtain ⟨h0, h1⟩ := saddleAngle_mem_Icc K d q
  have hc : 0 ≤ Real.cos (saddleAngle K d q) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  unfold localWidth localEpsilon
  exact mul_nonneg (by norm_num) (le_min h0 hc)

/-- The scale `T_d` is `a_K e^{Λ_d/2 + 1}` as soon as `Λ_d > 0`. -/
theorem scaleT_eq_of_scaleLambda_pos {d : ℕ} (hΛ : 0 < scaleLambda K d) :
    scaleT K d = dedekindScaleA K * Real.exp (scaleLambda K d / 2 + 1) := by
  have ha := dedekindScaleA_pos K
  have hlog : Real.log (scaleT K d / dedekindScaleA K) = scaleLambda K d / 2 + 1 := by
    unfold scaleLambda
    ring
  have hpos : 0 < scaleT K d / dedekindScaleA K := by
    by_contra hle
    replace hle := not_lt.mp hle
    have h0 : scaleT K d / dedekindScaleA K = 0 :=
      le_antisymm hle (div_nonneg (scaleT_nonneg K d) ha.le)
    rw [h0, Real.log_zero] at hlog
    linarith
  rw [← hlog, Real.exp_log hpos]
  field_simp

/-- Polar form of the lower-saddle Gamma/zeta argument. -/
theorem saddlePoint_eq_polar (d : ℕ) (q : ℝ) :
    saddlePoint K d q =
      ((scaleT K d * saddleRadius K d (saddleAngle K d q) : ℝ) : ℂ) *
        Complex.exp (((-saddleAngle K d q : ℝ) : ℂ) * Complex.I) := by
  rw [saddlePoint, contourW]
  congr 2
  push_cast
  ring

/-- The real part of the saddle argument is `T_d r_d(α_d(q)) cos α_d(q)`. -/
theorem saddlePoint_re (d : ℕ) (q : ℝ) :
    (saddlePoint K d q).re =
      scaleT K d * saddleRadius K d (saddleAngle K d q) * Real.cos (saddleAngle K d q) := by
  rw [saddlePoint_eq_polar, Complex.exp_ofReal_mul_I]
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The modulus of the saddle argument is `T_d r_d(α_d(q))`. -/
theorem norm_saddlePoint (d : ℕ) (q : ℝ) :
    ‖saddlePoint K d q‖ = scaleT K d * saddleRadius K d (saddleAngle K d q) := by
  rw [saddlePoint_eq_polar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (scaleT_nonneg K d) (saddleRadius_nonneg K d _)),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- In the local zeta range the saddle argument has real part at least `7/2`. -/
theorem seven_halves_le_re_saddlePoint {d : ℕ} {q : ℝ}
    (hZ : 4 ≤ (1 / 2 + saddlePoint K d q).re) :
    7 / 2 ≤ (saddlePoint K d q).re := by
  norm_num at hZ
  linarith

/-- In the local zeta range the saddle argument has modulus at least `7/2`. -/
theorem seven_halves_le_norm_saddlePoint {d : ℕ} {q : ℝ}
    (hZ : 4 ≤ (1 / 2 + saddlePoint K d q).re) :
    7 / 2 ≤ ‖saddlePoint K d q‖ :=
  (seven_halves_le_re_saddlePoint K hZ).trans (Complex.re_le_norm _)

/-- In the local zeta range the modulus `T_d r_d(α_d(q))` of the saddle argument is positive. -/
theorem scaleT_mul_saddleRadius_pos {d : ℕ} {q : ℝ}
    (hZ : 4 ≤ (1 / 2 + saddlePoint K d q).re) :
    0 < scaleT K d * saddleRadius K d (saddleAngle K d q) := by
  rw [← norm_saddlePoint]
  linarith [seven_halves_le_norm_saddlePoint K hZ]

/-- The principal argument of the saddle argument is `-α_d(q)` once its modulus is
positive. -/
theorem arg_saddlePoint {d : ℕ} {q : ℝ}
    (hR : 0 < scaleT K d * saddleRadius K d (saddleAngle K d q)) :
    Complex.arg (saddlePoint K d q) = -saddleAngle K d q := by
  obtain ⟨h0, h1⟩ := saddleAngle_mem_Icc K d q
  rw [saddlePoint_eq_polar, Complex.arg_real_mul _ hR, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).2
  constructor <;> linarith [Real.pi_pos]

/-! ### The Gamma logarithm -/

/-- `g_ℂ = exp ∘ gammaComplexLog` on the closed right half-plane away from the unit
disc. -/
theorem gammaRemainderComplex_eq_exp {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 ≤ ‖w‖) :
    gammaRemainderComplex w = Complex.exp (gammaComplexLog w) := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hs : 0 ≤ (w + 1 / 2).re := by
    simp
    linarith
  have hs1 : 1 ≤ ‖w + 1 / 2‖ := by
    have := GammaCore.norm_le_norm_add_real hw (a := 1 / 2) (by norm_num)
    push_cast at this
    linarith
  rw [gammaRemainderComplex, StirlingScratch.Gamma_eq_exp_stirMain_add hs hs1,
    GammaCore.sqrt_two_pi_eq, Complex.cpow_def_of_ne_zero hw0, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  unfold gammaComplexLog StirlingScratch.stirMain
  ring

/-- The Gamma remainder exponential identity `g_K(w) = exp (L_{g,K}(w))` on
`re w ≥ 0`, `‖w‖ > 3`. -/
theorem dedekindGammaRemainder_eq_exp {w : ℂ} (hw : 0 ≤ w.re) (hw3 : 3 < ‖w‖) :
    dedekindGammaRemainder K w = Complex.exp (dedekindGammaLog K w) := by
  have hgr : w ∈ GammaCore.grDomain := ⟨by linarith, hw3⟩
  have hp : (1 - 1 / (4 * w ^ 2) : ℂ) ≠ 0 :=
    gammaPolarCorrection_ne_zero (w := w) (by linarith)
  rw [dedekindGammaLog, Complex.exp_add, Complex.exp_add, Complex.exp_log hp,
    Complex.exp_nat_mul, Complex.exp_nat_mul, ← GammaCore.gammaCoreRemainder_eq_exp hgr,
    ← gammaRemainderComplex_eq_exp hw (by linarith)]
  rfl

private theorem re_gammaPolarCorrection_pos {w : ℂ} (hw : 1 < ‖w‖) :
    0 < (1 - 1 / (4 * w ^ 2) : ℂ).re := by
  have hsq : 1 < ‖w‖ ^ 2 := by nlinarith
  have hsmall : ‖gammaPolarCorrection w - 1‖ < 1 := by
    rw [norm_gammaPolarCorrection_sub_one, div_lt_one (by positivity)]
    nlinarith
  have hre := Complex.abs_re_le_norm (gammaPolarCorrection w - 1)
  rw [Complex.sub_re, Complex.one_re] at hre
  rw [← gammaPolarCorrection_apply]
  linarith [neg_le_of_abs_le hre]

/-- The Gamma logarithm is continuous on `{0 < re w, 3 < ‖w‖}`. -/
theorem continuousOn_dedekindGammaLog :
    ContinuousOn (dedekindGammaLog K) {w : ℂ | 0 < w.re ∧ 3 < ‖w‖} := by
  intro w hw
  obtain ⟨hre, hn⟩ := hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  apply ContinuousAt.continuousWithinAt
  have hpolar : ContinuousAt (fun z : ℂ => Complex.log (1 - 1 / (4 * z ^ 2))) w := by
    have hc : ContinuousAt (fun z : ℂ => (1 - 1 / (4 * z ^ 2) : ℂ)) w := by
      have h4 : (4 * w ^ 2 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hw0)
      exact continuousAt_const.sub (continuousAt_const.div
        (continuousAt_const.mul (continuousAt_id.pow 2)) h4)
    exact hc.clog (Or.inl (re_gammaPolarCorrection_pos (by linarith)))
  have hcore : ContinuousAt GammaCore.gammaCoreLog w :=
    (GammaCore.hasDerivAt_gammaCoreLog ⟨by linarith, hn⟩).continuousAt
  have hs : w + 1 / 2 ∈ GammaCore.stirDomain := by
    refine ⟨by simp; linarith, ?_⟩
    have := GammaCore.norm_le_norm_add_real hre.le (a := 1 / 2) (by norm_num)
    push_cast at this
    linarith
  have hstir : ContinuousAt (fun z : ℂ => StirlingScratch.stirR (z + 1 / 2)) w := by
    have hd : DifferentiableAt ℂ StirlingScratch.stirR (w + 1 / 2) :=
      (GammaCore.differentiableOn_stirR _ hs).differentiableAt
        (GammaCore.isOpen_stirDomain.mem_nhds hs)
    exact ContinuousAt.comp (g := StirlingScratch.stirR) (f := fun z : ℂ => z + 1 / 2)
      hd.continuousAt (by fun_prop)
  have hlog1 : ContinuousAt (fun z : ℂ => Complex.log (z + 1 / 2)) w :=
    (continuousAt_id.add continuousAt_const).clog (Or.inl (by simp; linarith))
  have hlog2 : ContinuousAt (fun z : ℂ => Complex.log z) w :=
    continuousAt_id.clog (Or.inl hre)
  have hcomplex : ContinuousAt gammaComplexLog w := by
    unfold gammaComplexLog
    exact (hstir.add (continuousAt_id.mul (hlog1.sub hlog2))).sub continuousAt_const
  unfold dedekindGammaLog
  exact (hpolar.add (continuousAt_const.mul hcore)).add (continuousAt_const.mul hcomplex)

/-- The polar correction logarithm is bounded by `1 / ‖w‖` for `‖w‖ ≥ 2`. -/
theorem norm_log_gammaPolarCorrection_le {w : ℂ} (hw2 : 2 ≤ ‖w‖) :
    ‖Complex.log (1 - 1 / (4 * w ^ 2))‖ ≤ 1 / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  have hn : ‖gammaPolarCorrection w - 1‖ = 1 / (4 * ‖w‖ ^ 2) :=
    norm_gammaPolarCorrection_sub_one w
  have hhalf : ‖gammaPolarCorrection w - 1‖ ≤ 1 / 2 := by
    rw [hn, div_le_iff₀ (by positivity)]
    nlinarith
  rw [← gammaPolarCorrection_apply]
  calc _ ≤ 3 / 2 * ‖gammaPolarCorrection w - 1‖ := by
        simpa using norm_log_one_add_half_le_self hhalf
    _ = 3 / (8 * ‖w‖ ^ 2) := by
      rw [hn]
      ring
    _ ≤ 1 / ‖w‖ := by
      rw [div_le_div_iff₀ (by positivity) hnw]
      nlinarith

/-- The real-place Gamma logarithm is bounded by `273 / ‖w‖` for `re w ≥ 0`, `‖w‖ ≥ 2`. -/
theorem norm_gammaCoreLog_le_div {w : ℂ} (hw : 0 ≤ w.re) (hw2 : 2 ≤ ‖w‖) :
    ‖GammaCore.gammaCoreLog w‖ ≤ 273 / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  have hsplit : GammaCore.gammaCoreLog w = StirlingScratch.stirR (w / 2 + 1 / 4) +
      ((w / 2 - 1 / 4) * (Complex.log (w / 2 + 1 / 4) - Complex.log (w / 2)) - 1 / 4) := by
    unfold GammaCore.gammaCoreLog
    ring
  have hs := GammaCore.norm_half_le_norm_s hw
  have hsre : 0 ≤ (w / 2 + 1 / 4).re := by
    simp
    linarith
  have hstir := StirlingScratch.norm_stirR_le' hsre (by linarith)
  have helem := GammaCore.norm_elem_part_le hw (by linarith)
  have hsp : 0 < ‖w / 2 + 1 / 4‖ := by linarith
  have h1 : 136 / ‖w / 2 + 1 / 4‖ ≤ 272 / ‖w‖ := by
    rw [div_le_div_iff₀ hsp hnw]
    nlinarith
  rw [hsplit]
  calc _ ≤ ‖StirlingScratch.stirR (w / 2 + 1 / 4)‖ +
        ‖(w / 2 - 1 / 4) * (Complex.log (w / 2 + 1 / 4) - Complex.log (w / 2)) - 1 / 4‖ :=
        norm_add_le _ _
    _ ≤ 272 / ‖w‖ + 5 / 16 / ‖w‖ := add_le_add (hstir.trans h1) helem
    _ ≤ 273 / ‖w‖ := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hnw.le

/-- The elementary part of the complex-place Gamma logarithm is bounded by `1 / ‖w‖`. -/
theorem norm_mul_log_add_half_sub_log_sub_half_le {w : ℂ} (hw : 0 ≤ w.re) (hw2 : 2 ≤ ‖w‖) :
    ‖w * (Complex.log (w + 1 / 2) - Complex.log w) - 1 / 2‖ ≤ 1 / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp hnw.ne'
  have hL := GammaCore.log_add_real_eq hw hw0 (a := 1 / 2) (by norm_num)
  push_cast at hL
  set t : ℂ := 1 / 2 / w with ht
  have ht0 : t ≠ 0 := by simp [ht, hw0]
  have htn : ‖t‖ = 1 / (2 * ‖w‖) := by
    rw [ht, norm_div, norm_div]
    norm_num
    ring
  have ht2 : ‖t‖ ≤ 1 / 2 := by
    rw [htn, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hid : w * (Complex.log (w + 1 / 2) - Complex.log w) - 1 / 2 =
      (1 / 2 : ℂ) * (((t⁻¹ - 1) * Complex.log (1 + t) - 1) + Complex.log (1 + t)) := by
    rw [hL, ht]
    field_simp
    ring
  rw [hid, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖((t⁻¹ - 1) * Complex.log (1 + t) - 1) + Complex.log (1 + t)‖
      ≤ 1 / 2 * (5 / 2 * ‖t‖ + 3 / 2 * ‖t‖) := by
        gcongr
        exact (norm_add_le _ _).trans
          (add_le_add (GammaCore.norm_aux_log ht2 ht0) (norm_log_one_add_half_le_self ht2))
    _ = 1 / ‖w‖ := by
      rw [htn]
      field_simp
      ring

/-- The complex-place Gamma logarithm is bounded by `5 / ‖w‖` for `re w ≥ 0`, `‖w‖ ≥ 2`. -/
theorem norm_gammaComplexLog_le_div {w : ℂ} (hw : 0 ≤ w.re) (hw2 : 2 ≤ ‖w‖) :
    ‖gammaComplexLog w‖ ≤ 5 / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  have hsn : ‖w‖ ≤ ‖w + 1 / 2‖ := by
    simpa using GammaCore.norm_le_norm_add_real hw (a := 1 / 2) (by norm_num)
  have hsre : 0 ≤ (w + 1 / 2).re := by
    simp
    linarith
  have hstir : ‖StirlingScratch.stirR (w + 1 / 2)‖ ≤ 7 / 2 / ‖w‖ :=
    (StirlingScratch.norm_stirR_le hsre (by linarith)).trans
      (div_le_div_of_nonneg_left (by norm_num) hnw hsn)
  have hsplit : gammaComplexLog w = StirlingScratch.stirR (w + 1 / 2) +
      (w * (Complex.log (w + 1 / 2) - Complex.log w) - 1 / 2) := by
    unfold gammaComplexLog
    ring
  rw [hsplit]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 7 / 2 / ‖w‖ + 1 / ‖w‖ :=
      add_le_add hstir (norm_mul_log_add_half_sub_log_sub_half_le hw hw2)
    _ ≤ 5 / ‖w‖ := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hnw.le

/-- The Gamma logarithm bound: `‖L_{g,K}(w)‖ ≤ C_K / ‖w‖` for `re w ≥ 0`, `‖w‖ ≥ 2`. -/
theorem norm_dedekindGammaLog_le {w : ℂ} (hw : 0 ≤ w.re) (hw2 : 2 ≤ ‖w‖) :
    ‖dedekindGammaLog K w‖ ≤
      (1 + 273 * dedekindRealPlaces K + 5 * dedekindComplexPlaces K) / ‖w‖ := by
  have hnw : 0 < ‖w‖ := by linarith
  have hP := norm_log_gammaPolarCorrection_le hw2
  have hR := norm_gammaCoreLog_le_div hw hw2
  have hC := norm_gammaComplexLog_le_div hw hw2
  unfold dedekindGammaLog
  calc _ ≤ ‖Complex.log (1 - 1 / (4 * w ^ 2))‖ +
        ‖(dedekindRealPlaces K : ℂ) * GammaCore.gammaCoreLog w‖ +
        ‖(dedekindComplexPlaces K : ℂ) * gammaComplexLog w‖ := norm_add₃_le
    _ = ‖Complex.log (1 - 1 / (4 * w ^ 2))‖ +
        (dedekindRealPlaces K : ℝ) * ‖GammaCore.gammaCoreLog w‖ +
        (dedekindComplexPlaces K : ℝ) * ‖gammaComplexLog w‖ := by
          rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    _ ≤ 1 / ‖w‖ + (dedekindRealPlaces K : ℝ) * (273 / ‖w‖) +
        (dedekindComplexPlaces K : ℝ) * (5 / ‖w‖) := by gcongr
    _ = _ := by field_simp

/-! ### Dedekind zeta -/

/-- On `re s > 1` the totalized Dedekind zeta function is Mathlib's Dirichlet series. -/
theorem analyticDedekindZeta_eq_raw {s : ℂ} (hs : 1 < s.re) :
    analyticDedekindZeta K s = rawDedekindZeta K s := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  unfold analyticDedekindZeta
  simp only [hs1, ite_false]
  split_ifs with h
  · exact h.choose_spec.2 s hs
  · rfl

/-! ### Analytic hypotheses

The following propositions are analytic statements about the objects defined above. The
theorems below take them as explicit hypotheses. -/

/-- For `re s > 1`, `exp (𝓛_K(s)) = ζ_K(s)`. -/
def EulerLogExp : Prop :=
  ∀ s : ℂ, 1 < s.re → Complex.exp (dedekindEulerLog K s) = analyticDedekindZeta K s

/-- For `re s = σ > 1`, `|𝓛_K(s)| ≤ N log ζ(σ)`. -/
def EulerLogBound : Prop :=
  ∀ s : ℂ, 1 < s.re →
    ‖dedekindEulerLog K s‖ ≤ (dedekindDegree K : ℝ) * Real.log (riemannZeta (s.re : ℂ)).re

/-- The Dedekind Euler logarithm `𝓛_K` is continuous on `re s > 1`. -/
def EulerLogContinuous : Prop :=
  ContinuousOn (dedekindEulerLog K) {s : ℂ | 1 < s.re}

/-- For sufficiently small fixed `c₀ > 0`, `q ≤ c₀ T_d` implies `re (1/2 + w_{d,q}(θ)) ≥ 4`
throughout the local arc `[-2α_d(q) - ℓ_{d,q}, -2α_d(q) + ℓ_{d,q}]` (for large `d` and `q`
past the edge). -/
def ContourZetaDomain : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
    ∀ᶠ d : ℕ in atTop, ∀ q : ℝ, edgeQ K d < q → q ≤ c₀ * scaleT K d →
      ∀ θ ∈ Icc (-2 * saddleAngle K d q - localWidth K d q)
          (-2 * saddleAngle K d q + localWidth K d q),
        4 ≤ (1 / 2 + contourW K d q θ).re

/-- The inverse saddle angle `q ↦ α_d(q)` is differentiable on `(q_{e,d}, T_d)`. -/
def SaddleAngleDifferentiable : Prop :=
  ∀ d : ℕ, 1 ≤ d → DifferentiableOn ℝ (saddleAngle K d) (Ioo (edgeQ K d) (scaleT K d))

/-- The lower saddle `q ↦ u_{d,q}` is differentiable on `(q_{e,d}, T_d)`. -/
def SaddleBranchDifferentiable : Prop :=
  ∀ d : ℕ, 1 ≤ d → DifferentiableOn ℝ (saddle K d) (Ioo (edgeQ K d) (scaleT K d))

/-- For `q_{e,d} < q ≤ T_d`, `0 < α_d(q) < π/2`. -/
def SaddleInverseRange : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ q : ℝ, edgeQ K d < q → q ≤ scaleT K d →
    0 < saddleAngle K d q ∧ saddleAngle K d q < Real.pi / 2

/-- On the saddle branch, `D = 1 - (π r e^{-iα}/4)(1 + (2 log r - 2iα)/Λ_d)`. -/
def HessianFormula : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ q : ℝ, edgeQ K d < q → q ≤ scaleT K d →
    saddleHessian K d q = explicitSaddleHessianAtLambda (scaleLambda K d)
      (saddleRadius K d (saddleAngle K d q)) (saddleAngle K d q)

/-- For all large `d` on the saddle branch, `sin²α ≤ re D ≤ 2 sin²α`. -/
def HessianRealBounds : Prop :=
  ∀ᶠ d : ℕ in atTop, ∀ q : ℝ, edgeQ K d < q → q ≤ scaleT K d →
    Real.sin (saddleAngle K d q) ^ 2 ≤ (saddleHessian K d q).re ∧
      (saddleHessian K d q).re ≤ 2 * Real.sin (saddleAngle K d q) ^ 2

/-- If `M, c₀ > 0`, `d ≥ 2`, `Λ_d ≥ 24π` and the counting window is nonempty, then
`|S_d(q_{e,d} + τ_{M,d})| ≤ (3/2)(√50)³ (√(M √(log d / d)))³`. -/
def ActionEdge : Prop :=
  ∀ M c₀ : ℝ, 0 < M → 0 < c₀ → ∀ d : ℕ, 2 ≤ d → 24 * Real.pi ≤ scaleLambda K d →
    (countingWindow K M c₀ d).Nonempty →
      |saddleAction K d (edgeQ K d + edgeOffset M d)| ≤
        3 / 2 * Real.sqrt 50 ^ 3 * Real.sqrt (M * Real.sqrt (Real.log d / d)) ^ 3

/-- There are absolute `C, q₁ > 0` with `S_d(q) ≥ π - C q^{-1/2}`
whenever `q₁ ≤ q ≤ T_d`. -/
def ActionTail : Prop :=
  ∃ C q₁ : ℝ, 0 < C ∧ 0 < q₁ ∧ ∀ d : ℕ, 1 ≤ d → ∀ q : ℝ, q₁ ≤ q → q ≤ scaleT K d →
    Real.pi - C * q ^ (-(1 / 2 : ℝ)) ≤ saddleAction K d q

/-- For all sufficiently large `d`, `log d ≤ Λ_d`. -/
def ScaleLambdaLower : Prop :=
  ∀ᶠ d : ℕ in atTop, Real.log d ≤ scaleLambda K d

/-- For fixed `M, c₀ > 0` the counting window is nonempty for all sufficiently large `d`. -/
def WindowNonempty : Prop :=
  ∀ M c₀ : ℝ, 0 < M → 0 < c₀ → ∀ᶠ d : ℕ in atTop, (countingWindow K M c₀ d).Nonempty

/-! ### Exact polar form of the leading term -/

/-- The Dedekind leading constant `c_K` is positive. -/
theorem cK_pos : 0 < cK K := by
  unfold cK
  have := dedekindDiscriminantAbs_pos K
  positivity

/-- Multiplying by the positive real `2πd` does not change the principal argument. -/
theorem arg_two_pi_mul_natCast_mul {d : ℕ} (hd : (0 : ℝ) < d) (z : ℂ) :
    Complex.arg (2 * Real.pi * d * z) = Complex.arg z := by
  rw [show (2 * Real.pi * d * z : ℂ) = ((2 * Real.pi * (d : ℝ) : ℝ) : ℂ) * z by push_cast; ring]
  exact Complex.arg_real_mul _ (by positivity)

/-- **Exact polar form of the leading term**. Assuming `EulerLogExp K`, in the local zeta
range `re (1/2 + w) ≥ 4`, `Z_d(q) = |Z_d(q)| exp(i (d S_d(q) + ω_d(q)))`. -/
theorem leadingSaddle_eq_norm_mul_exp_phase
    (lem_zeta_log_exp : EulerLogExp K) (d : ℕ) (q : ℝ) (hZ : 4 ≤ (1 / 2 + saddlePoint K d q).re) :
    leadingSaddle K d q =
      (‖leadingSaddle K d q‖ : ℂ) *
        Complex.exp (Complex.I *
          (((d : ℝ) * saddleAction K d q + phaseCorrection K d q : ℝ) : ℂ)) := by
  have hn := seven_halves_le_norm_saddlePoint K hZ
  have hre := seven_halves_le_re_saddlePoint K hZ
  have hw0 : saddlePoint K d q ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  set w := saddlePoint K d q with hwdef
  have hR := scaleT_mul_saddleRadius_pos K hZ
  by_cases hX : (2 * Real.pi * d * saddleHessian K d q : ℂ) = 0
  · have h0 : leadingSaddle K d q = 0 := by
      rw [leadingSaddle, hX]
      simp
    simp [h0]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h => hX (by simp [h]))
  have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
  set L : ℂ := Complex.log w * (muK K : ℂ) + dedekindEulerLog K (1 / 2 + w) +
      dedekindGammaLog K w + (d : ℂ) * phase K d q (saddle K d q) -
      Complex.log (2 * Real.pi * d * saddleHessian K d q) / 2 with hL
  have hc : 0 < (d.factorial : ℝ) / (d : ℝ) ^ d * cK K := mul_pos (by positivity) (cK_pos K)
  have hfac : leadingSaddle K d q =
      (((d.factorial : ℝ) / (d : ℝ) ^ d * cK K : ℝ) : ℂ) * Complex.exp L := by
    have hamp : dedekindAmplitude K d q (-2 * saddleAngle K d q) =
        (cK K : ℂ) * w ^ (muK K : ℂ) * analyticDedekindZeta K (1 / 2 + w) *
          dedekindGammaRemainder K w := rfl
    rw [leadingSaddle, hamp, ← lem_zeta_log_exp _ (by simp; linarith),
      dedekindGammaRemainder_eq_exp K (by linarith) (by linarith),
      Complex.cpow_def_of_ne_zero hw0, sqrt_eq_exp hX, hL, Complex.exp_sub, Complex.exp_add,
      Complex.exp_add, Complex.exp_add]
    push_cast
    field_simp
  have hpolar := RiemannJensen.eq_norm_mul_exp_I_im_of_eq_pos_mul_exp hc hfac
  have hLim : L.im = (d : ℝ) * saddleAction K d q + phaseCorrection K d q := by
    rw [hL]
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.log_im,
      Complex.div_ofNat_im,
      arg_two_pi_mul_natCast_mul hdpos (saddleHessian K d q)]
    rw [arg_saddlePoint K hR]
    unfold phaseCorrection saddleAction
    rw [← hwdef]
    ring
  rwa [hLim] at hpolar

/-! ### The window lies in the local zeta range -/

/-- The edge offset `τ_{M,d}` is positive for `M > 0` and `d ≥ 2`. -/
theorem edgeOffset_pos {M : ℝ} (hM : 0 < M) {d : ℕ} (hd : 2 ≤ d) : 0 < edgeOffset M d := by
  have hd1 : (1 : ℝ) < d := Nat.one_lt_cast.mpr hd
  unfold edgeOffset
  exact mul_pos hM (Real.sqrt_pos.mpr (div_pos (Real.log_pos hd1) (by linarith)))

/-- The edge offset `τ_{M,d}` is nonnegative for `M ≥ 0`. -/
theorem edgeOffset_nonneg {M : ℝ} (hM : 0 ≤ M) (d : ℕ) : 0 ≤ edgeOffset M d :=
  mul_nonneg hM (Real.sqrt_nonneg _)

/-- For sufficiently small `c₀`, the whole counting window is eventually in the local zeta
range. -/
theorem eventually_zetaRange_on_window (lem_contour_zeta_domain : ContourZetaDomain K) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ M c₀ : ℝ, 0 < M → 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ countingWindow K M c₀ d,
        4 ≤ (1 / 2 + saddlePoint K d q).re := by
  obtain ⟨c₁, hc₁, h⟩ := lem_contour_zeta_domain
  refine ⟨c₁, hc₁, fun M c₀ hM hc₀ hc => ?_⟩
  filter_upwards [h c₀ hc₀ hc, eventually_ge_atTop 2] with d hd hd2 q hq
  have hτ := edgeOffset_pos hM hd2
  have hℓ := localWidth_nonneg K d q
  exact hd q (by linarith [hq.1]) hq.2 _ ⟨by linarith, by linarith⟩

/-- **Exact polar form on the window**: for small `c₀ > 0` and every `M > 0`, eventually every
`q` in the counting window satisfies `Z_d(q) = ‖Z_d(q)‖ exp(i (d S_d(q) + ω_d(q)))`. -/
theorem eventually_leadingSaddle_polar_on_window (lem_zeta_log_exp : EulerLogExp K)
    (lem_contour_zeta_domain : ContourZetaDomain K) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ M c₀ : ℝ, 0 < M → 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ∀ q ∈ countingWindow K M c₀ d,
        leadingSaddle K d q = (‖leadingSaddle K d q‖ : ℂ) *
          Complex.exp (Complex.I *
            (((d : ℝ) * saddleAction K d q + phaseCorrection K d q : ℝ) : ℂ)) := by
  obtain ⟨c₁, hc₁, h⟩ := eventually_zetaRange_on_window K lem_contour_zeta_domain
  refine ⟨c₁, hc₁, fun M c₀ hM hc₀ hc => ?_⟩
  filter_upwards [h M c₀ hM hc₀ hc] with d hd q hq
  exact leadingSaddle_eq_norm_mul_exp_phase K lem_zeta_log_exp d q (hd q hq)

/-! ### Uniform phase-correction bound -/

/-- In the region `4 ≤ re s`, the Euler logarithm has imaginary part at most `[K : ℚ] / 3`. -/
theorem abs_im_dedekindEulerLog_le (lem_zeta_log : EulerLogBound K) {s : ℂ} (hs : 4 ≤ s.re) :
    |(dedekindEulerLog K s).im| ≤ (dedekindDegree K : ℝ) / 3 := by
  refine (Complex.abs_im_le_norm _).trans ((lem_zeta_log _ (by linarith)).trans ?_)
  have hz := norm_riemannZeta_sub_one_le_one_third (s := ((s.re : ℝ) : ℂ)) (by simpa using hs)
  have hzre := Complex.abs_re_le_norm (riemannZeta ((s.re : ℝ) : ℂ) - 1)
  rw [Complex.sub_re, Complex.one_re] at hzre
  have hpos : 0 < (riemannZeta ((s.re : ℝ) : ℂ)).re := by
    linarith [neg_le_of_abs_le (hzre.trans hz)]
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hup := (le_abs_self _).trans (hzre.trans hz)
  have hN : (0 : ℝ) ≤ dedekindDegree K := Nat.cast_nonneg _
  nlinarith

/-- The phase correction is bounded at every point of the local zeta range. -/
theorem abs_phaseCorrection_le_of_zetaRange (lem_zeta_log : EulerLogBound K)
    {d : ℕ} {q : ℝ} (hZ : 4 ≤ (1 / 2 + saddlePoint K d q).re) :
    |phaseCorrection K d q| ≤
      |muK K| * (Real.pi / 2) + (dedekindDegree K : ℝ) / 3 +
        (1 + 273 * dedekindRealPlaces K + 5 * dedekindComplexPlaces K) / 2 +
        Real.pi / 2 := by
  have hn := seven_halves_le_norm_saddlePoint K hZ
  have hre := seven_halves_le_re_saddlePoint K hZ
  obtain ⟨hα0, hα1⟩ := saddleAngle_mem_Icc K d q
  set w := saddlePoint K d q with hw
  have h1 : |-muK K * saddleAngle K d q| ≤ |muK K| * (Real.pi / 2) := by
    rw [abs_mul, abs_neg, abs_of_nonneg hα0]
    exact mul_le_mul_of_nonneg_left hα1 (abs_nonneg _)
  have h2 := abs_im_dedekindEulerLog_le K lem_zeta_log hZ
  have h3 : |(dedekindGammaLog K w).im| ≤
      (1 + 273 * dedekindRealPlaces K + 5 * dedekindComplexPlaces K) / 2 := by
    refine (Complex.abs_im_le_norm _).trans ?_
    refine (norm_dedekindGammaLog_le K (by linarith) (by linarith)).trans ?_
    have hC : (0 : ℝ) ≤ 1 + 273 * dedekindRealPlaces K + 5 * dedekindComplexPlaces K := by
      positivity
    exact div_le_div_of_nonneg_left hC (by norm_num) (by linarith)
  have h4 : |Complex.arg (saddleHessian K d q) / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_two]
    exact div_le_div_of_nonneg_right (Complex.abs_arg_le_pi _) (by norm_num)
  unfold phaseCorrection
  rw [← hw]
  calc _ ≤ |-muK K * saddleAngle K d q| + |(dedekindEulerLog K (1 / 2 + w)).im| +
        |(dedekindGammaLog K w).im| + |Complex.arg (saddleHessian K d q) / 2| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by gcongr

/-- **Uniform phase-correction bound**. For every fixed `M > 0` and sufficiently small fixed
`c₀ > 0` there is `C > 0` with `|ω_d(q)| ≤ C` for all large `d` and `q ∈ I_{M,c₀,d}`. -/
theorem exists_abs_phaseCorrection_le (lem_contour_zeta_domain : ContourZetaDomain K)
    (lem_zeta_log : EulerLogBound K) :
    ∀ M : ℝ, 0 < M → ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop, ∀ q ∈ countingWindow K M c₀ d,
        |phaseCorrection K d q| ≤ C := by
  intro M hM
  obtain ⟨c₁, hc₁, h⟩ := eventually_zetaRange_on_window K lem_contour_zeta_domain
  refine ⟨c₁, hc₁, fun c₀ hc₀ hc => ?_⟩
  refine ⟨|muK K| * (Real.pi / 2) + (dedekindDegree K : ℝ) / 3 +
      (1 + 273 * dedekindRealPlaces K + 5 * dedekindComplexPlaces K) / 2 + Real.pi / 2,
    by positivity, ?_⟩
  filter_upwards [h M c₀ hM hc₀ hc] with d hd q hq
  exact abs_phaseCorrection_le_of_zetaRange K lem_zeta_log (hd q hq)

/-! ### Continuity of the phase correction -/

/-- `‖u_{d,q}‖ = r_d(α_d(q))²`, so the saddle radius is recovered from the saddle. -/
theorem saddleRadius_eq_sqrt_norm_saddle (d : ℕ) (q : ℝ) :
    saddleRadius K d (saddleAngle K d q) = Real.sqrt ‖saddle K d q‖ := by
  have hr := saddleRadius_nonneg K d (saddleAngle K d q)
  have he : ‖Complex.exp (-2 * Complex.I * (saddleAngle K d q : ℂ))‖ = 1 := by
    rw [show (-2 * Complex.I * (saddleAngle K d q : ℂ)) =
      ((-2 * saddleAngle K d q : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [saddle, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), he,
    mul_one, Real.sqrt_sq hr]

/-- The explicit Hessian is continuous along continuous `r` and `α` with `r` nonvanishing. -/
theorem continuousOn_explicitSaddleHessianAtLambda (Λ : ℝ) {s : Set ℝ} {r α : ℝ → ℝ}
    (hr : ContinuousOn r s) (hα : ContinuousOn α s) (hr0 : ∀ x ∈ s, r x ≠ 0) :
    ContinuousOn (fun x => explicitSaddleHessianAtLambda Λ (r x) (α x)) s := by
  have hlog : ContinuousOn (fun x => Real.log (r x)) s := hr.log hr0
  unfold explicitSaddleHessianAtLambda
  fun_prop

/-- The saddle argument is continuous wherever its radius and angle are. -/
theorem continuousOn_saddlePoint {d : ℕ} {s : Set ℝ}
    (hr : ContinuousOn (fun q => saddleRadius K d (saddleAngle K d q)) s)
    (hα : ContinuousOn (saddleAngle K d) s) : ContinuousOn (saddlePoint K d) s := by
  have hpol : ContinuousOn (fun q =>
      ((scaleT K d * saddleRadius K d (saddleAngle K d q) : ℝ) : ℂ) *
        Complex.exp (((-saddleAngle K d q : ℝ) : ℂ) * Complex.I)) s := by
    fun_prop
  exact hpol.congr fun q _ => saddlePoint_eq_polar K d q

/-- **Continuity of the phase correction**, for sufficiently small fixed `c₀`: for fixed
`M > 0` and all large `d`, `ω_d` is continuous on `I_{M,c₀,d}`. -/
theorem continuousOn_phaseCorrection
    (lem_contour_zeta_domain : ContourZetaDomain K)
    (lem_zeta_log_continuous : EulerLogContinuous K)
    (lem_saddle_angle_differentiable : SaddleAngleDifferentiable K)
    (lem_saddle_branch_differentiable : SaddleBranchDifferentiable K)
    (lem_saddle_inverse_range : SaddleInverseRange K)
    (lem_hessian_formula : HessianFormula K)
    (lem_hessian_real_bounds : HessianRealBounds K) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ M c₀ : ℝ, 0 < M → 0 < c₀ → c₀ ≤ c₁ →
      ∀ᶠ d : ℕ in atTop, ContinuousOn (phaseCorrection K d) (countingWindow K M c₀ d) := by
  obtain ⟨c₁, hc₁, h⟩ := eventually_zetaRange_on_window K lem_contour_zeta_domain
  refine ⟨min c₁ (1 / 2), lt_min hc₁ (by norm_num), fun M c₀ hM hc₀ hc => ?_⟩
  have hcc : c₀ ≤ c₁ := hc.trans (min_le_left _ _)
  have hclt : c₀ < 1 := lt_of_le_of_lt (hc.trans (min_le_right _ _)) (by norm_num)
  filter_upwards [h M c₀ hM hc₀ hcc, lem_hessian_real_bounds, eventually_ge_atTop 2]
    with d hZ hHB hd2
  set I := countingWindow K M c₀ d with hIdef
  rcases I.eq_empty_or_nonempty with hI | ⟨q0, hq0⟩
  · simp [hI]
  have hd1 : 1 ≤ d := by omega
  have hP := scaleT_mul_saddleRadius_pos K (hZ q0 hq0)
  have hT : 0 < scaleT K d := (scaleT_nonneg K d).lt_of_ne fun h0 => by simp [← h0] at hP
  have hsub : I ⊆ Ioo (edgeQ K d) (scaleT K d) := fun q hq =>
    ⟨by linarith [hq.1, edgeOffset_pos hM hd2],
      lt_of_le_of_lt hq.2 (show c₀ * scaleT K d < scaleT K d by nlinarith)⟩
  have hα : ContinuousOn (saddleAngle K d) I :=
    (lem_saddle_angle_differentiable d hd1).continuousOn.mono hsub
  have hu : ContinuousOn (saddle K d) I :=
    (lem_saddle_branch_differentiable d hd1).continuousOn.mono hsub
  have hr : ContinuousOn (fun q => saddleRadius K d (saddleAngle K d q)) I :=
    hu.norm.sqrt.congr (fun q _ => saddleRadius_eq_sqrt_norm_saddle K d q)
  have hr0 : ∀ q ∈ I, saddleRadius K d (saddleAngle K d q) ≠ 0 := fun q hq =>
    right_ne_zero_of_mul (scaleT_mul_saddleRadius_pos K (hZ q hq)).ne'
  have hw := continuousOn_saddlePoint K hr hα
  have hL : ContinuousOn (fun q => dedekindEulerLog K (1 / 2 + saddlePoint K d q)) I :=
    lem_zeta_log_continuous.comp (continuousOn_const.add hw) fun q hq =>
      show 1 < (1 / 2 + saddlePoint K d q).re by linarith [hZ q hq]
  have hG : ContinuousOn (fun q => dedekindGammaLog K (saddlePoint K d q)) I :=
    (continuousOn_dedekindGammaLog K).comp hw (fun q hq => by
      have h0 := hZ q hq
      exact ⟨by linarith [seven_halves_le_re_saddlePoint K h0],
        by linarith [seven_halves_le_norm_saddlePoint K h0]⟩)
  have hD : ContinuousOn (saddleHessian K d) I :=
    (continuousOn_explicitSaddleHessianAtLambda (scaleLambda K d) hr hα hr0).congr
      (fun q hq => lem_hessian_formula d hd1 q (hsub hq).1 (hsub hq).2.le)
  have hargD : ContinuousOn (fun q => Complex.arg (saddleHessian K d q)) I :=
    Complex.continuousOn_arg.comp hD fun q hq => by
      have hrange := lem_saddle_inverse_range d hd1 q (hsub hq).1 (hsub hq).2.le
      have hs : 0 < Real.sin (saddleAngle K d q) :=
        Real.sin_pos_of_pos_of_lt_pi hrange.1 (by linarith [hrange.2, Real.pi_pos])
      exact Or.inl (lt_of_lt_of_le (by positivity) (hHB q (hsub hq).1 (hsub hq).2.le).1)
  unfold phaseCorrection
  exact (((continuousOn_const.mul hα).add (Complex.continuous_im.comp_continuousOn hL)).add
    (Complex.continuous_im.comp_continuousOn hG)).sub (hargD.div_const 2)

/-! ### Endpoint phase span -/

/-- For `x ≥ 0`, `(√x)³ = x^(3/2)`. -/
theorem sqrt_pow_three_eq_rpow {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ^ 3 = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- If `log d ≤ Λ_d` eventually, then for fixed `c₀ > 0` and `q₁`, eventually `Λ_d ≥ 24π` and
`q₁ ≤ c₀ T_d`. -/
theorem eventually_le_upperEndpoint (lem_scale_lambda_lower : ScaleLambdaLower K) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (q₁ : ℝ) :
    ∀ᶠ d : ℕ in atTop, 24 * Real.pi ≤ scaleLambda K d ∧ q₁ ≤ upperEndpoint K c₀ d := by
  have ha := dedekindScaleA_pos K
  have hca : 0 < c₀ * dedekindScaleA K := mul_pos hc₀ ha
  have hlogd : ∀ᶠ d : ℕ in atTop,
      max (24 * Real.pi) (2 * q₁ / (c₀ * dedekindScaleA K)) ≤ Real.log d :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [lem_scale_lambda_lower, hlogd] with d hΛ hlog
  have hΛ24 : 24 * Real.pi ≤ scaleLambda K d := ((le_max_left _ _).trans hlog).trans hΛ
  have hΛpos : 0 < scaleLambda K d := by linarith [Real.pi_pos]
  have hTlow : dedekindScaleA K * (scaleLambda K d / 2) ≤ scaleT K d := by
    rw [scaleT_eq_of_scaleLambda_pos K hΛpos]
    apply mul_le_mul_of_nonneg_left _ ha.le
    have := Real.add_one_le_exp (scaleLambda K d / 2 + 1)
    linarith
  have h2q : 2 * q₁ ≤ Real.log d * (c₀ * dedekindScaleA K) :=
    (div_le_iff₀ hca).mp ((le_max_right _ _).trans hlog)
  have h3 : c₀ * (dedekindScaleA K * (scaleLambda K d / 2)) ≤ c₀ * scaleT K d :=
    mul_le_mul_of_nonneg_left hTlow hc₀.le
  have h4 : Real.log d * (c₀ * dedekindScaleA K) ≤ scaleLambda K d * (c₀ * dedekindScaleA K) :=
    mul_le_mul_of_nonneg_right hΛ hca.le
  refine ⟨hΛ24, ?_⟩
  unfold upperEndpoint
  nlinarith

/-- **Endpoint phase-span bound**. For every fixed `M > 0` and sufficiently small fixed
`c₀ > 0`, for all large `d` the endpoint increase of `d S_d + ω_d` on `I_{M,c₀,d}` is at
least `π d - C d (Q_{c₀,d}^{-1/2} + τ_{M,d}^{3/2}) - C`. -/
theorem phaseSpan_lower
    (lem_contour_zeta_domain : ContourZetaDomain K)
    (lem_zeta_log : EulerLogBound K)
    (lem_action_edge : ActionEdge K)
    (lem_action_tail : ActionTail K)
    (lem_scale_lambda_lower : ScaleLambdaLower K)
    (lem_window_nonempty : WindowNonempty K) :
    ∀ M : ℝ, 0 < M → ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ c₁ →
      ∃ C : ℝ, ∀ᶠ d : ℕ in atTop,
        Real.pi * d - C * d * (upperEndpoint K c₀ d ^ (-(1 / 2 : ℝ)) +
            edgeOffset M d ^ (3 / 2 : ℝ)) - C ≤
          ((d : ℝ) * saddleAction K d (upperEndpoint K c₀ d) +
              phaseCorrection K d (upperEndpoint K c₀ d)) -
            ((d : ℝ) * saddleAction K d (edgeQ K d + edgeOffset M d) +
              phaseCorrection K d (edgeQ K d + edgeOffset M d)) := by
  intro M hM
  obtain ⟨c₁, hc₁, hB⟩ :=
    exists_abs_phaseCorrection_le K lem_contour_zeta_domain lem_zeta_log M hM
  refine ⟨min c₁ 1, lt_min hc₁ one_pos, fun c₀ hc₀ hc => ?_⟩
  obtain ⟨Cω, hCω, hBd⟩ := hB c₀ hc₀ (hc.trans (min_le_left _ _))
  have hc1 : c₀ ≤ 1 := hc.trans (min_le_right _ _)
  obtain ⟨Ct, q₁, hCt, hq₁, htail⟩ := lem_action_tail
  have hE : (0 : ℝ) ≤ 3 / 2 * Real.sqrt 50 ^ 3 := by positivity
  refine ⟨Ct + 3 / 2 * Real.sqrt 50 ^ 3 + 2 * Cω, ?_⟩
  filter_upwards [hBd, eventually_le_upperEndpoint K lem_scale_lambda_lower hc₀ q₁,
    lem_window_nonempty M c₀ hM hc₀, eventually_ge_atTop 2] with d hbd hU hne hd2
  obtain ⟨hΛ24, hQq⟩ := hU
  have hdpos : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hQT : upperEndpoint K c₀ d ≤ scaleT K d := mul_le_of_le_one_left (scaleT_nonneg K d) hc1
  obtain ⟨q0, hq0⟩ := hne
  have hlow_le : edgeQ K d + edgeOffset M d ≤ upperEndpoint K c₀ d := hq0.1.trans hq0.2
  have hωa := abs_le.mp (hbd _ ⟨le_rfl, hlow_le⟩)
  have hωQ := abs_le.mp (hbd _ ⟨hlow_le, le_rfl⟩)
  have hSQ := htail d (by omega) _ hQq hQT
  have hτ0 := edgeOffset_nonneg hM.le d
  have hSa : saddleAction K d (edgeQ K d + edgeOffset M d) ≤
      3 / 2 * Real.sqrt 50 ^ 3 * edgeOffset M d ^ (3 / 2 : ℝ) := by
    rw [← sqrt_pow_three_eq_rpow hτ0]
    exact (le_abs_self _).trans (lem_action_edge M c₀ hM hc₀ d hd2 hΛ24 ⟨q0, hq0⟩)
  have hB0 : 0 ≤ upperEndpoint K c₀ d ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hA0 : 0 ≤ edgeOffset M d ^ (3 / 2 : ℝ) := Real.rpow_nonneg hτ0 _
  have k1 := mul_le_mul_of_nonneg_left hSQ hdpos
  have k2 := mul_le_mul_of_nonneg_left hSa hdpos
  have k3 : 0 ≤ (3 / 2 * Real.sqrt 50 ^ 3 + 2 * Cω) * d *
      upperEndpoint K c₀ d ^ (-(1 / 2 : ℝ)) := by positivity
  have k4 : 0 ≤ (Ct + 2 * Cω) * d * edgeOffset M d ^ (3 / 2 : ℝ) := by positivity
  nlinarith

end RiemannJensen.Dedekind
