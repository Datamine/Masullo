import FiniteLocalZeta
import LocallyConstantProduct
import Mathlib.MeasureTheory.Integral.Pi

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Completion (v : S) := v.val.adicCompletion F
private abbrev FiniteTests := locallyConstantTests (∀ v : S, Completion F S v)
private abbrev FiniteUnits := ∀ v : S, (Completion F S v)ˣ
private abbrev Phases := ∀ v : S, (Completion F S v)ˣ →ₜ* Circle

/-- The product denominator needs factors only from unramified places. -/
def sLocalFiniteZetaDenominator (χ : Phases F S) (z : ℂ) : ℂ :=
  ∏ v : S, if finiteZetaUnramified F v.val (χ v) then
    finiteZetaDenominator F v.val (χ v) z else 1

theorem sLocalFiniteZetaDenominator_analytic (χ : Phases F S) :
    AnalyticOnNhd ℂ (sLocalFiniteZetaDenominator F S χ) univ := by
  apply Finset.analyticOnNhd_fun_prod
  intro v _
  by_cases h : finiteZetaUnramified F v.val (χ v)
  · simp only [ite_eq_left h]
    exact fun z _ => finiteZetaDenominator_analytic F v.val (χ v) z
  · simp only [ite_eq_right h]
    exact analyticOnNhd_const

theorem sLocalFiniteZetaDenominator_ne_zero_of_pos (χ : Phases F S) (z : ℂ) (hz : 0 < z.re) :
    sLocalFiniteZetaDenominator F S χ z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  by_cases h : finiteZetaUnramified F v.val (χ v)
  · rw [ite_eq_left h]
    exact finiteZetaDenominator_ne_zero_of_pos F v.val (χ v) z hz
  · rw [ite_eq_right h]
    exact one_ne_zero

/-- The integrand on the entire finite product, for a test that can couple
different places. -/
def sLocalFiniteZetaIntegrand (χ : Phases F S) (f : FiniteTests F S) (z : ℂ)
    (u : FiniteUnits F S) : ℂ :=
  f.val (fun v => (u v).val) * ∏ v : S, ((χ v (u v) : ℂ) * finiteZetaWeight F v.val z (u v))

private theorem finiteProductIntegrand_add (χ : Phases F S) (a b : FiniteTests F S) (z : ℂ) :
    sLocalFiniteZetaIntegrand F S χ (a + b) z = fun u =>
      sLocalFiniteZetaIntegrand F S χ a z u + sLocalFiniteZetaIntegrand F S χ b z u := by
  funext u
  exact add_mul _ _ _

private theorem finiteProductIntegrand_smul (χ : Phases F S) (c : ℂ) (f : FiniteTests F S) (z : ℂ) :
    sLocalFiniteZetaIntegrand F S χ (c • f) z = fun u => c * sLocalFiniteZetaIntegrand F S χ f z u := by
  funext u
  exact mul_assoc _ _ _

variable [∀ v : S, MeasurableSpace (Completion F S v)ˣ]
  [∀ v : S, BorelSpace (Completion F S v)ˣ]
variable (μ : ∀ v : S, Measure (Completion F S v)ˣ) [∀ v : S, (μ v).IsHaarMeasure]
  [∀ v : S, SigmaFinite (μ v)]

/-- Local numerator used in the continued finite product. -/
def finiteProductClearedLocal (χ : Phases F S) (v : S)
    (f : locallyConstantTests (Completion F S v)) (z : ℂ) : ℂ :=
  if finiteZetaUnramified F v.val (χ v) then
    finiteZetaClearedDistribution F v.val (μ v) (χ v) z f
  else finiteZetaContinuation F v.val (μ v) (χ v) f z

omit [∀ v : S, SigmaFinite (μ v)] in
private theorem finiteProductClearedLocal_analytic (χ : Phases F S) (v : S)
    (f : locallyConstantTests (Completion F S v)) :
    AnalyticOnNhd ℂ (finiteProductClearedLocal F S μ χ v f) univ := by
  by_cases h : finiteZetaUnramified F v.val (χ v)
  · have he : finiteProductClearedLocal F S μ χ v f = fun z =>
        finiteZetaClearedDistribution F v.val (μ v) (χ v) z f :=
      funext fun z => ite_eq_left h
    rw [he]
    exact finiteZetaClearedDistribution_analytic F v.val (μ v) (χ v) f
  · have he : finiteProductClearedLocal F S μ χ v f =
        finiteZetaContinuation F v.val (μ v) (χ v) f :=
      funext fun z => ite_eq_right h
    rw [he]
    exact finiteZetaContinuation_analytic_of_ramified F v.val (μ v) (χ v) h f

omit [∀ v : S, SigmaFinite (μ v)] in
theorem finiteProductClearedLocal_eq (χ : Phases F S) (v : S)
    (f : locallyConstantTests (Completion F S v)) (z : ℂ) (hz : 0 < z.re) :
    finiteProductClearedLocal F S μ χ v f z =
      finiteZetaIntegral F v.val (μ v) (χ v) f z *
        (if finiteZetaUnramified F v.val (χ v) then finiteZetaDenominator F v.val (χ v) z else 1) := by
  by_cases h : finiteZetaUnramified F v.val (χ v)
  · simpa only [finiteProductClearedLocal, ite_eq_left h] using
      finiteZetaClearedDistribution_eq_mul_integral F v.val (μ v) (χ v) f z hz
  · simpa only [finiteProductClearedLocal, ite_eq_right h, mul_one] using
      (finiteZetaContinuation_eq_integral F v.val (μ v) (χ v) f z hz).2.symm

private theorem finiteProductCleared_exists (χ : Phases F S) (f : FiniteTests F S) :
    ∃ N : ℂ → ℂ, AnalyticOnNhd ℂ N univ ∧ ∀ z : ℂ, 0 < z.re →
      Integrable (sLocalFiniteZetaIntegrand F S χ f z) (Measure.pi μ) ∧
      N z = (∫ u, sLocalFiniteZetaIntegrand F S χ f z u ∂Measure.pi μ) *
        sLocalFiniteZetaDenominator F S χ z := by
  have hf : f ∈ Submodule.span ℂ (Set.range (locallyConstantTestPiProduct
      (X := Completion F S))) := by
    rw [locallyConstantTest_span_piProduct]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨g, rfl⟩ := hg
    let N (z : ℂ) := ∏ v : S, finiteProductClearedLocal F S μ χ v (g v) z
    refine ⟨N, Finset.analyticOnNhd_fun_prod _ (fun v _ =>
      finiteProductClearedLocal_analytic F S μ χ v (g v)), fun z hz => ?_⟩
    let h (v : S) (u : (Completion F S v)ˣ) :=
      (g v).val u.val * (χ v u : ℂ) * finiteZetaWeight F v.val z u
    have he : sLocalFiniteZetaIntegrand F S χ (locallyConstantTestPiProduct g) z =
        fun u => ∏ v : S, h v (u v) := by
      funext u
      simp only [sLocalFiniteZetaIntegrand, locallyConstantTestPiProduct_apply,
        ← Finset.prod_mul_distrib, h, mul_assoc]
    rw [he]
    refine ⟨Integrable.fintype_prod_dep (fun v =>
      (finiteZetaContinuation_eq_integral F v.val (μ v) (χ v) (g v) z hz).1), ?_⟩
    rw [integral_fintype_prod_eq_prod]
    dsimp [N, sLocalFiniteZetaDenominator]
    simp_rw [finiteProductClearedLocal_eq F S μ χ _ _ z hz, Finset.prod_mul_distrib]
    rfl
  | zero =>
    refine ⟨0, analyticOnNhd_const, fun z _ => ?_⟩
    have he : sLocalFiniteZetaIntegrand F S χ 0 z = 0 := by
      funext u
      change 0 * _ = 0
      exact zero_mul _
    simp [he]
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, hAe⟩ := ha
    obtain ⟨B, hB, hBe⟩ := hb
    refine ⟨fun z => A z + B z, hA.add hB, fun z hz => ?_⟩
    obtain ⟨ha, hAe⟩ := hAe z hz
    obtain ⟨hb, hBe⟩ := hBe z hz
    rw [finiteProductIntegrand_add]
    refine ⟨ha.add hb, ?_⟩
    change A z + B z = _
    rw [integral_add ha hb, add_mul, hAe, hBe]
  | smul c a _ ha =>
    obtain ⟨A, hA, hAe⟩ := ha
    refine ⟨fun z => c * A z, analyticOnNhd_const.mul hA, fun z hz => ?_⟩
    obtain ⟨ha, hAe⟩ := hAe z hz
    rw [finiteProductIntegrand_smul]
    refine ⟨ha.const_mul c, ?_⟩
    change c * A z = _
    rw [integral_const_mul, mul_assoc, hAe]

private theorem finiteProductAnalytic_eq {A B : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A univ) (hB : AnalyticOnNhd ℂ B univ)
    (h : ∀ z : ℂ, 0 < z.re → A z = B z) :
    A = B := by
  apply hA.eq_of_eventuallyEq hB (z₀ := 1)
  have hpos : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hpos.mono h

/-- The entire numerator for every finite-product Schwartz–Bruhat test.
The construction is independent of how the test is written as a finite sum
of products, by uniqueness on the half-plane of absolute convergence. -/
def sLocalFiniteZetaCleared (χ : Phases F S) (z : ℂ) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    FiniteTests F S →L[ℂ] ℂ := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  let N (f : FiniteTests F S) := (finiteProductCleared_exists F S μ χ f).choose
  have han (f : FiniteTests F S) : AnalyticOnNhd ℂ (N f) univ :=
    (finiteProductCleared_exists F S μ χ f).choose_spec.1
  have he (f : FiniteTests F S) (w : ℂ) (hw : 0 < w.re) :
      Integrable (sLocalFiniteZetaIntegrand F S χ f w) (Measure.pi μ) ∧
      N f w = (∫ u, sLocalFiniteZetaIntegrand F S χ f w u ∂Measure.pi μ) *
        sLocalFiniteZetaDenominator F S χ w :=
    (finiteProductCleared_exists F S μ χ f).choose_spec.2 w hw
  let L : FiniteTests F S →ₗ[ℂ] ℂ :=
    { toFun := fun f => N f z
      map_add' := fun f g => by
        have heq : N (f + g) = fun w => N f w + N g w := by
          apply finiteProductAnalytic_eq (han (f + g)) ((han f).add (han g))
          intro w hw
          change N (f + g) w = N f w + N g w
          rw [(he (f + g) w hw).2, (he f w hw).2, (he g w hw).2,
            finiteProductIntegrand_add, integral_add (he f w hw).1 (he g w hw).1, add_mul]
        exact congrFun heq z
      map_smul' := fun c f => by
        have heq : N (c • f) = fun w => c * N f w := by
          apply finiteProductAnalytic_eq (han (c • f)) (analyticOnNhd_const.mul (han f))
          intro w hw
          change N (c • f) w = c * N f w
          rw [(he (c • f) w hw).2, (he f w hw).2, finiteProductIntegrand_smul,
            integral_const_mul, mul_assoc]
        exact congrFun heq z }
  exact ⟨L, finest_linear_continuous L⟩

theorem sLocalFiniteZetaCleared_analytic (χ : Phases F S) (f : FiniteTests F S) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    AnalyticOnNhd ℂ (fun z => sLocalFiniteZetaCleared F S μ χ z f) univ :=
  (finiteProductCleared_exists F S μ χ f).choose_spec.1

private theorem sLocalFiniteZetaCleared_eq (χ : Phases F S) (f : FiniteTests F S)
    (z : ℂ) (hz : 0 < z.re) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    Integrable (sLocalFiniteZetaIntegrand F S χ f z) (Measure.pi μ) ∧
    sLocalFiniteZetaCleared F S μ χ z f =
      (∫ u, sLocalFiniteZetaIntegrand F S χ f z u ∂Measure.pi μ) *
        sLocalFiniteZetaDenominator F S χ z :=
  (finiteProductCleared_exists F S μ χ f).choose_spec.2 z hz

/-- The numerator on an elementary product is the product of the local
numerators, including at removable points. -/
theorem sLocalFiniteZetaCleared_piProduct (χ : Phases F S)
    (g : ∀ v : S, locallyConstantTests (Completion F S v)) (z : ℂ) :
    sLocalFiniteZetaCleared F S μ χ z (locallyConstantTestPiProduct g) =
      ∏ v : S, finiteProductClearedLocal F S μ χ v (g v) z := by
  let N (w : ℂ) := ∏ v : S, finiteProductClearedLocal F S μ χ v (g v) w
  have he : (fun z ↦ sLocalFiniteZetaCleared F S μ χ z (locallyConstantTestPiProduct g)) = N := by
      apply finiteProductAnalytic_eq (sLocalFiniteZetaCleared_analytic F S μ χ _)
        (Finset.analyticOnNhd_fun_prod _ (fun v _ ↦ finiteProductClearedLocal_analytic F S μ χ v (g v)))
      intro z hz
      rw [(sLocalFiniteZetaCleared_eq F S μ χ _ z hz).2]
      let h (v : S) (u : (Completion F S v)ˣ) :=
        (g v).val u.val * (χ v u : ℂ) * finiteZetaWeight F v.val z u
      have hg' : sLocalFiniteZetaIntegrand F S χ (locallyConstantTestPiProduct g) z =
          fun u ↦ ∏ v : S, h v (u v) := by
        funext u
        simp only [sLocalFiniteZetaIntegrand, locallyConstantTestPiProduct_apply,
          ← Finset.prod_mul_distrib, h, mul_assoc]
      rw [hg', integral_fintype_prod_eq_prod]
      dsimp [N, sLocalFiniteZetaDenominator]
      simp_rw [finiteProductClearedLocal_eq F S μ χ _ _ z hz, Finset.prod_mul_distrib]
      rfl
  exact congrFun he z

/-- The entire numerator of a coupled finite test is a finite linear
combination of real exponentials in the common Mellin variable. -/
theorem sLocalFiniteZetaCleared_mem_exponentialAlgebra (χ : Phases F S) (f : FiniteTests F S) :
    (fun z => sLocalFiniteZetaCleared F S μ χ z f) ∈ mellinExponentialAlgebra := by
  have hf : f ∈ Submodule.span ℂ (Set.range (locallyConstantTestPiProduct
      (X := Completion F S))) := by
    rw [locallyConstantTest_span_piProduct]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨g, rfl⟩ := hg
    have he : (fun z => sLocalFiniteZetaCleared F S μ χ z (locallyConstantTestPiProduct g)) =
        ∏ v : S, finiteProductClearedLocal F S μ χ v (g v) := by
      funext z
      simpa only [Finset.prod_apply] using sLocalFiniteZetaCleared_piProduct F S μ χ g z
    rw [he]
    exact mellinExponentialAlgebra.prod_mem fun v _ =>
      finiteZeta_localCleared_mem_exponentialAlgebra F v.val (μ v) (χ v) (g v)
  | zero =>
    have he : (fun z => sLocalFiniteZetaCleared F S μ χ z 0) = 0 :=
      funext fun z => map_zero (sLocalFiniteZetaCleared F S μ χ z)
    rw [he]
    exact mellinExponentialAlgebra.zero_mem
  | add f g _ _ hf hg =>
    have he : (fun z => sLocalFiniteZetaCleared F S μ χ z (f + g)) =
        (fun z => sLocalFiniteZetaCleared F S μ χ z f) +
          (fun z => sLocalFiniteZetaCleared F S μ χ z g) :=
      funext fun z => map_add (sLocalFiniteZetaCleared F S μ χ z) f g
    rw [he]
    exact mellinExponentialAlgebra.add_mem hf hg
  | smul c f _ hf =>
    have he : (fun z => sLocalFiniteZetaCleared F S μ χ z (c • f)) =
        c • (fun z => sLocalFiniteZetaCleared F S μ χ z f) :=
      funext fun z => map_smul (sLocalFiniteZetaCleared F S μ χ z) c f
    rw [he]
    exact mellinExponentialAlgebra.smul_mem hf c

/-- The finite-product numerator is bounded on closed strips for any
locally constant compactly supported test. -/
theorem sLocalFiniteZetaCleared_norm_le_on_strip (χ : Phases F S) (f : FiniteTests F S)
    (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖sLocalFiniteZetaCleared F S μ χ z f‖ ≤ C := by
  have hf : f ∈ Submodule.span ℂ (Set.range (locallyConstantTestPiProduct
      (X := Completion F S))) := by
    rw [locallyConstantTest_span_piProduct]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨g, rfl⟩ := hg
    have hlocal (v : S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
        ‖finiteProductClearedLocal F S μ χ v (g v) z‖ ≤ C :=
      finiteZeta_localCleared_norm_le_on_strip F v.val (μ v) (χ v) (g v) a b
    choose C hC hbound using hlocal
    refine ⟨∏ v, C v, Finset.prod_nonneg fun v _ ↦ hC v, fun z hz ↦ ?_⟩
    rw [sLocalFiniteZetaCleared_piProduct, norm_prod]
    exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hbound v z hz)
  | zero => exact ⟨0, le_rfl, fun z _ ↦ by rw [map_zero, norm_zero]⟩
  | add f g _ _ hf hg =>
    obtain ⟨C, hC, hf⟩ := hf
    obtain ⟨D, hD, hg⟩ := hg
    exact ⟨C + D, add_nonneg hC hD, fun z hz ↦ by
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hf z hz) (hg z hz))⟩
  | smul c f _ hf =>
    obtain ⟨C, hC, hf⟩ := hf
    exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun z hz ↦ by
      rw [map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hf z hz) (norm_nonneg _)⟩

/-- The continuation of the finite-product integral as a continuous functional
of the test, with the same totalization at the denominator zeros as scalar division. -/
def sLocalFiniteZetaContinued (χ : Phases F S) (z : ℂ) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    FiniteTests F S →L[ℂ] ℂ :=
  (sLocalFiniteZetaDenominator F S χ z)⁻¹ • sLocalFiniteZetaCleared F S μ χ z

theorem sLocalFiniteZetaContinued_eq_integral (χ : Phases F S) (f : FiniteTests F S)
    (z : ℂ) (hz : 0 < z.re) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    Integrable (sLocalFiniteZetaIntegrand F S χ f z) (Measure.pi μ) ∧
      sLocalFiniteZetaContinued F S μ χ z f =
        ∫ u, sLocalFiniteZetaIntegrand F S χ f z u ∂Measure.pi μ := by
  obtain ⟨hI, he⟩ := sLocalFiniteZetaCleared_eq F S μ χ f z hz
  refine ⟨hI, ?_⟩
  simp only [sLocalFiniteZetaContinued, smul_apply, smul_eq_mul, he]
  rw [mul_left_comm, inv_mul_cancel₀ (sLocalFiniteZetaDenominator_ne_zero_of_pos F S χ z hz), mul_one]

theorem sLocalFiniteZetaContinued_meromorphic (χ : Phases F S) (f : FiniteTests F S) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    Meromorphic (fun z => sLocalFiniteZetaContinued F S μ χ z f) := by
  intro z
  change MeromorphicAt (fun z => (sLocalFiniteZetaDenominator F S χ z)⁻¹ *
    sLocalFiniteZetaCleared F S μ χ z f) z
  exact ((sLocalFiniteZetaDenominator_analytic F S χ z trivial).meromorphicAt.inv).mul
    ((sLocalFiniteZetaCleared_analytic F S μ χ f z trivial).meromorphicAt)

theorem sLocalFiniteZetaContinued_analyticAt (χ : Phases F S) (f : FiniteTests F S)
    (z : ℂ) (hz : sLocalFiniteZetaDenominator F S χ z ≠ 0) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    AnalyticAt ℂ (fun z => sLocalFiniteZetaContinued F S μ χ z f) z := by
  change AnalyticAt ℂ (fun z => (sLocalFiniteZetaDenominator F S χ z)⁻¹ *
    sLocalFiniteZetaCleared F S μ χ z f) z
  exact ((sLocalFiniteZetaDenominator_analytic F S χ z trivial).inv hz).mul
    (sLocalFiniteZetaCleared_analytic F S μ χ f z trivial)

end

end Masullo
