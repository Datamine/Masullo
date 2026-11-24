import ArchimedeanGammaTests
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Pi

open Filter MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev E := mixedEmbedding.mixedSpace F

private abbrev HR := PiLp 2 (fun _ : R F ↦ ℝ)
private abbrev HC := PiLp 2 (fun _ : C F ↦ ℂ)
private abbrev H := WithLp 2 (HR F × HC F)

private def mixedGaussianCoordinates : E F ≃L[ℝ] H F :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : R F ↦ ℝ)).symm).prodCongr
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : C F ↦ ℂ)).symm.trans
        (ContinuousLinearEquiv.smulLeft
          (Units.mk0 (Real.sqrt 2) (Real.sqrt_ne_zero'.mpr (by norm_num)))))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (HR F) (HC F)).symm

private theorem mixedGaussianCoordinates_norm_sq (x : E F) :
    ‖mixedGaussianCoordinates F x‖^2 =
      (∑ i : R F, ‖x.1 i‖^2) + 2 * ∑ i : C F, ‖x.2 i‖^2 := by
  let r : HR F := WithLp.toLp 2 x.1
  let c : HC F := WithLp.toLp 2 x.2
  change ‖WithLp.toLp 2 (r, Real.sqrt 2 • c)‖^2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖r‖^2 + ‖Real.sqrt 2 • c‖^2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)),
    PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]

private def mixedGammaRealMonomial (a : R F → ℂ × ℕ) (x : E F) : ℂ :=
  ∏ v : R F, (x.1 v : ℂ) ^ ((a v).2 % 2)

private def mixedGammaComplexMonomial (j : C F → ℂ × ℤ) (x : E F) : ℂ :=
  ∏ v : C F, x.2 v ^ (-(j v).2).toNat * star (x.2 v) ^ (j v).2.toNat * (Real.pi : ℂ)⁻¹

private theorem temperateGrowth_prod {I U : Type*} [Fintype I]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (g : I → U → ℂ) (hg : ∀ i, (g i).HasTemperateGrowth) :
    (fun x ↦ ∏ i, g i x).HasTemperateGrowth := by
  suffices ∀ T : Finset I, (fun x ↦ ∏ i ∈ T, g i x).HasTemperateGrowth from this _
  intro T
  induction T using Finset.induction_on with
  | empty => simp [Function.HasTemperateGrowth.const]
  | insert v T hv ih =>
    simp_rw [Finset.prod_insert hv]
    exact (hg v).mul ih

private theorem mixedGammaMonomial_temperate (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ) :
    (fun x ↦ mixedGammaRealMonomial F a x * mixedGammaComplexMonomial F j x).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.mul
  · apply temperateGrowth_prod
    intro i
    have h : (fun x : E F ↦ (x.1 i : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (R F → ℝ) (C F → ℂ)))).hasTemperateGrowth
    exact h.pow _
  · apply temperateGrowth_prod
    intro i
    have h : (fun x : E F ↦ x.2 i).HasTemperateGrowth :=
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ (R F → ℝ) (C F → ℂ))).hasTemperateGrowth
    have h' : (fun x : E F ↦ star (x.2 i)).HasTemperateGrowth := by
      exact Complex.conjCLE.hasTemperateGrowth.comp h
    exact ((h.pow _).mul (h'.pow _)).mul (Function.HasTemperateGrowth.const _)

/-- The product of the local parity and angular Gaussian tests defines a
Schwartz function on the mixed space. -/
theorem exists_mixedGammaProductTest (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ)
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (hf : ∀ v x, f v x = (x : ℂ)^((a v).2 % 2) * (Real.exp (-Real.pi * ‖x‖^2) : ℂ))
    (hg : ∀ v z, g v z = (z ^ (-(j v).2).toNat * star z ^ (j v).2.toNat) *
      ((Real.pi : ℂ)⁻¹ * (Real.exp (-(2*Real.pi)*‖z‖^2) : ℂ))) :
    ∃ φ : 𝓢(E F, ℂ), ∀ x, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v) := by
  obtain ⟨G, hG⟩ := exists_gaussian_schwartz (E := H F) Real.pi Real.pi_pos
  let A := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedGaussianCoordinates F) G
  let p (x : E F) := mixedGammaRealMonomial F a x * mixedGammaComplexMonomial F j x
  refine ⟨SchwartzMap.smulLeftCLM ℂ p A, fun x ↦ ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (mixedGammaMonomial_temperate F a j)]
  change p x * G (mixedGaussianCoordinates F x) = _
  rw [hG, mixedGaussianCoordinates_norm_sq]
  simp_rw [hf, hg, ← mul_assoc, Finset.prod_mul_distrib]
  have hr : (∏ v : R F, (Real.exp (-Real.pi * ‖x.1 v‖^2) : ℂ)) =
      (Real.exp (-Real.pi * ∑ v : R F, ‖x.1 v‖^2) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.mul_sum]
  have hc : (∏ v : C F, (Real.exp (-(2*Real.pi)*‖x.2 v‖^2) : ℂ)) =
      (Real.exp (-(2*Real.pi) * ∑ v : C F, ‖x.2 v‖^2) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.mul_sum]
  rw [hr, hc]
  have he : -Real.pi * ((∑ v : R F, ‖x.1 v‖^2) + 2 * ∑ v : C F, ‖x.2 v‖^2) =
      -Real.pi * (∑ v : R F, ‖x.1 v‖^2) + -(2*Real.pi) * (∑ v : C F, ‖x.2 v‖^2) := by ring
  rw [he, Real.exp_add, Complex.ofReal_mul]
  simp only [p, mixedGammaRealMonomial, mixedGammaComplexMonomial, Finset.prod_mul_distrib]
  ring

attribute [local instance] realArchUnitsMeasurable complexArchUnitsMeasurable
  realArchUnitsBorel complexArchUnitsBorel realArchUnitsSigmaCompact complexArchUnitsSigmaCompact
  complexZeta_circleMeasurable

/-- Archimedean zeta integration of a separated test is the product
of the real and complex zeta integrals in their convergence half-planes. -/
theorem archimedeanNumberFieldZeta_separated
    (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ)
    (φ : 𝓢(E F, ℂ)) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : E F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (z : ℂ) (har : ∀ i, 0 < (z + (a i).1).re) (hcr : ∀ i, 0 < (z + (j i).1).re) :
    archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ =
      (∏ i, realArchimedeanZetaContinued (a i).2 (f i) (z + (a i).1)) *
      ∏ i, complexArchimedeanZetaContinued complexTamagawaAngularMeasure
        (j i).2 (g i) (z + (j i).1) := by
  let W (i : R F) (u : ℝˣ) := realArchUnitWeight (a i).2 (z + (a i).1) u * f i u.val
  let V (i : C F) (u : ℂˣ) := complexArchUnitWeight (j i).2 (z + (j i).1) u * g i u.val
  have he (p : (R F → ℝˣ) × (C F → ℂˣ)) :
      ((∏ i, realArchUnitWeight (a i).2 (z + (a i).1) (p.1 i)) *
        (∏ i, complexArchUnitWeight (j i).2 (z + (j i).1) (p.2 i))) *
        φ (fun i ↦ (p.1 i : ℝ), fun i ↦ (p.2 i : ℂ)) =
      (∏ i, W i (p.1 i)) * ∏ i, V i (p.2 i) := by
    rw [hφ]
    simp only [W, V, Finset.prod_mul_distrib]
    ring
  change archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ =
    _
  rw [archimedeanNumberFieldZeta_eq_productIntegral F a j z har hcr, archimedeanCoordinateMeasure]
  simp_rw [he]
  let μR := Measure.pi (fun _ : R F ↦ realArchMultiplicativeHaar)
  let μC := Measure.pi (fun _ : C F ↦ complexArchMultiplicativeHaar)
  have hF := integral_prod_mul (μ := μR) (ν := μC)
    (fun p ↦ ∏ i, W i (p i)) (fun p ↦ ∏ i, V i (p i))
  change (∫ p : (R F → ℝˣ) × (C F → ℂˣ),
    (∏ i, W i (p.1 i)) * (∏ i, V i (p.2 i)) ∂μR.prod μC) = _
  rw [hF]
  unfold μR μC
  rw [integral_fintype_prod_eq_prod W, integral_fintype_prod_eq_prod V]
  congr 1
  · exact Finset.prod_congr rfl fun i _ =>
      (realArchimedeanZetaContinued_eq_unitIntegral (a i).2 (f i) (har i)).2.symm
  · exact Finset.prod_congr rfl fun i _ =>
      (complexArchimedeanZetaContinued_eq_unitIntegral (j i).2 (g i) (hcr i)).2.symm

/-- A single mixed Schwartz test realizes the product of all archimedean
Euler factors as meromorphic germs. -/
theorem exists_archimedeanGammaProductTest_separated_explicit_exact
    (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ)
    (ha : ∀ i, (a i).1.re = 0) (hj : ∀ i, (j i).1.re = 0) :
    ∃ (φ : 𝓢(E F, ℂ)) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)),
      (∀ x : E F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v)) ∧
      (∀ i x, f i x = (x : ℂ) ^ ((a i).2 % 2) *
        (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ)) ∧
      (∀ i x, g i x = (x ^ (-(j i).2).toNat * star x ^ (j i).2.toNat) *
        ((Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ))) ∧
      (∀ c : ℂ,
        (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) =ᶠ[𝓝[≠] c]
          fun z ↦ (archimedeanNumberFieldZetaDenominator F a j z)⁻¹) ∧
      EqOn (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ)
        (fun z ↦ (archimedeanNumberFieldZetaDenominator F a j z)⁻¹) {z | 0 < z.re} := by
  choose f hf hfg using fun i : R F ↦ exists_realGammaTest_explicit (a i).2
  choose g hg hgg using fun i : C F ↦ exists_complexGammaTest_explicit (j i).2
  obtain ⟨φ, hφ⟩ := exists_mixedGammaProductTest F a j f g hf hg
  refine ⟨φ, f, g, hφ, hf, hg, ?_⟩
  suffices hEq : EqOn
      (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ)
      (fun z ↦ (archimedeanNumberFieldZetaDenominator F a j z)⁻¹) {z | 0 < z.re} from
    ⟨fun c ↦ boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re) ⟨1, by simp⟩
    (archimedeanNumberFieldZeta_meromorphic F complexTamagawaAngularMeasure a j φ)
    (fun z ↦ (archimedeanNumberFieldZetaDenominator_analytic F a j z).meromorphicAt.inv) hEq c, hEq⟩
  intro z hz
  have har (i : R F) : 0 < (z + (a i).1).re := by simpa [Complex.add_re, ha] using hz
  have hcr (i : C F) : 0 < (z + (j i).1).re := by simpa [Complex.add_re, hj] using hz
  have hn (s : ℂ) (hs : 0 < s.re) (n : ℕ) : s + n ≠ 0 := fun h ↦ by
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn' (s : ℂ) (hs : 0 < s.re) (n : ℕ) : 2 * s + n ≠ 0 := by
    apply hn _ _ n
    simpa [Complex.mul_re] using (show 0 < 2 * s.re by positivity)
  have hr (i : R F) : realArchimedeanZetaContinued (a i).2 (f i) (z + (a i).1) =
      (realArchZetaDenominator (a i).2 (z + (a i).1))⁻¹ := by
    let s := z + (a i).1
    have hD : realArchZetaDenominator (a i).2 s ≠ 0 :=
      inv_ne_zero ((realArchZetaRegular_iff_gamma _ _).mp (fun n h ↦ (hn s (har i) n h).elim))
    have h₁ := (realArchimedeanZetaContinued_analyticAt (a i).2 (f i) (hn s (har i))).continuousAt
    have h₂ := (realArchZetaDenominator_analytic (a i).2 s).continuousAt.inv₀ hD
    apply ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).mp ?_).eq_of_nhds
    simpa only [Pi.inv_def, realArchZetaDenominator, inv_inv] using hfg i s
  have hc (i : C F) : complexArchimedeanZetaContinued complexTamagawaAngularMeasure
      (j i).2 (g i) (z + (j i).1) = (complexArchZetaDenominator (j i).2 (z + (j i).1))⁻¹ := by
    let s := z + (j i).1
    have hD : complexArchZetaDenominator (j i).2 s ≠ 0 :=
      inv_ne_zero ((complexArchZetaRegular_iff_gamma _ _).mp (fun n h ↦ (hn' s (hcr i) n h).elim))
    have h₁ := (complexArchimedeanZetaContinued_analyticAt complexTamagawaAngularMeasure
      (j i).2 (g i) (hn' s (hcr i))).continuousAt
    have h₂ := (complexArchZetaDenominator_analytic (j i).2 s).continuousAt.inv₀ hD
    apply ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).mp ?_).eq_of_nhds
    simpa only [Pi.inv_def, complexArchZetaDenominator, inv_inv] using hgg i s
  change archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ =
    (archimedeanNumberFieldZetaDenominator F a j z)⁻¹
  rw [archimedeanNumberFieldZeta_separated F a j φ f g hφ z har hcr]
  simp only [hr, hc, archimedeanNumberFieldZetaDenominator, mul_inv, Finset.prod_inv_distrib]

/-- The explicit factors give the separated reference and its meromorphic germs. -/
theorem exists_archimedeanGammaProductTest_separated_explicit
    (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ)
    (ha : ∀ i, (a i).1.re = 0) (hj : ∀ i, (j i).1.re = 0) :
    ∃ (φ : 𝓢(E F, ℂ)) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)),
      (∀ x : E F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v)) ∧
      (∀ i x, f i x = (x : ℂ) ^ ((a i).2 % 2) *
        (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ)) ∧
      (∀ i x, g i x = (x ^ (-(j i).2).toNat * star x ^ (j i).2.toNat) *
        ((Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2) : ℂ))) ∧
      ∀ c : ℂ,
        (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) =ᶠ[𝓝[≠] c]
          fun z ↦ (archimedeanNumberFieldZetaDenominator F a j z)⁻¹ := by
  obtain ⟨φ, f, g, hφ, hf, hg, h, _⟩ :=
    exists_archimedeanGammaProductTest_separated_explicit_exact F a j ha hj
  exact ⟨φ, f, g, hφ, hf, hg, h⟩

/-- A separated mixed Schwartz reference test for the archimedean Euler product. -/
theorem exists_archimedeanGammaProductTest_separated
    (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ)
    (ha : ∀ i, (a i).1.re = 0) (hj : ∀ i, (j i).1.re = 0) :
    ∃ (φ : 𝓢(E F, ℂ)) (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)),
      (∀ x : E F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v)) ∧
      ∀ c : ℂ,
      (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) =ᶠ[𝓝[≠] c]
        fun z ↦ (archimedeanNumberFieldZetaDenominator F a j z)⁻¹ := by
  obtain ⟨φ, f, g, hφ, _, _, h⟩ :=
    exists_archimedeanGammaProductTest_separated_explicit F a j ha hj
  exact ⟨φ, f, g, hφ, h⟩

/-- A mixed Schwartz reference test for the archimedean Euler product. -/
theorem exists_archimedeanGammaProductTest
    (a : R F → ℂ × ℕ) (j : C F → ℂ × ℤ)
    (ha : ∀ i, (a i).1.re = 0) (hj : ∀ i, (j i).1.re = 0) :
    ∃ φ : 𝓢(E F, ℂ), ∀ c : ℂ,
      (fun z ↦ archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) =ᶠ[𝓝[≠] c]
        fun z ↦ (archimedeanNumberFieldZetaDenominator F a j z)⁻¹ := by
  obtain ⟨φ, _, _, _, h⟩ := exists_archimedeanGammaProductTest_separated F a j ha hj
  exact ⟨φ, h⟩

end

end Masullo
