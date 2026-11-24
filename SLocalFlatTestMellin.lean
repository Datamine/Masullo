import SLocalCompactMellin
import SLocalFlatTestSpace

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev L (v : S) := v.val.adicCompletion F
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FiniteTests := locallyConstantTests (∀ v : S, L F S v)
private abbrev K := SLocalThetaNormOne F S
private abbrev X := sLocalBruhatImage F S

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

omit [∀ v : S, SigmaFinite (μ v)] in
/-- In the finite variables, every local exponent is allowed when the
additive test vanishes at the origin. -/
theorem finiteZetaIntegral_analyticAt_of_zero
    (v : S) (χ : (L F S v)ˣ →ₜ* Circle)
    (g : locallyConstantTests (L F S v)) (hg : g.val 0 = 0) (c : ℂ) :
    AnalyticAt ℂ (finiteZetaIntegral F v.val (μ v) χ g) c := by
  let a (u : (L F S v)ˣ) := Real.log ‖u.val‖
  let b (u : (L F S v)ˣ) := g.val u.val * (χ u : ℂ)
  have ha : Continuous a := (Units.continuous_val.norm.log fun u ↦ norm_ne_zero_iff.mpr u.ne_zero)
  have hb : Continuous b := (g.property.1.continuous.comp Units.continuous_val).mul
    (continuous_subtype_val.comp χ.continuous)
  have hK : HasCompactSupport b := (finiteTest_restrictUnits_hasCompactSupport F S v g hg).mul_right
  have h := analyticAt_integral_exp_mul_of_hasCompactSupport (μ v) ha hb hK c
  convert h using 1
  funext z
  apply integral_congr_ae
  exact .of_forall fun u ↦ mul_comm _ _

private theorem sLocalFiniteZeta_exists_analyticGerm_of_piProduct_zero
    (χ : ∀ v : S, (L F S v)ˣ →ₜ* Circle)
    (g : ∀ v : S, locallyConstantTests (L F S v)) (h0 : ∀ v, (g v).val 0 = 0) (c : ℂ) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧
      (fun z ↦ sLocalFiniteZetaContinued F S μ χ z (locallyConstantTestPiProduct g)) =ᶠ[𝓝[≠] c] G := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  let G (z : ℂ) := ∏ v : S, finiteZetaIntegral F v.val (μ v) (χ v) (g v) z
  have hG (c : ℂ) : AnalyticAt ℂ G c :=
    Finset.analyticAt_fun_prod _ fun v _ ↦ finiteZetaIntegral_analyticAt_of_zero F S μ v (χ v) (g v) (h0 v) c
  refine ⟨G, hG c, boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re) ⟨1, by simp⟩
    (sLocalFiniteZetaContinued_meromorphic F S μ χ _) (fun z ↦ (hG z).meromorphicAt) ?_ c⟩
  intro z hz
  change sLocalFiniteZetaContinued F S μ χ z (locallyConstantTestPiProduct g) = G z
  rw [(sLocalFiniteZetaContinued_eq_integral F S μ χ _ z hz).2]
  let h (v : S) (u : (L F S v)ˣ) :=
    (g v).val u.val * (χ v u : ℂ) * finiteZetaWeight F v.val z u
  have he : sLocalFiniteZetaIntegrand F S χ (locallyConstantTestPiProduct g) z =
      fun u ↦ ∏ v, h v (u v) := by
    funext u
    simp only [sLocalFiniteZetaIntegrand, locallyConstantTestPiProduct_apply,
      ← Finset.prod_mul_distrib, h, mul_assoc]
  rw [he, integral_fintype_prod_eq_prod h]
  rfl

private abbrev Z (ω : PontryaginDual (K F S)) (f : X F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- Lemma 5.3.4.2(2). On every unitary component the actual
S-local Mellin transform of a flat test has holomorphic germs everywhere. -/
theorem sLocalProductZeta_exists_analyticGerm_of_polarFree (ω : PontryaginDual (K F S))
    (f : X F S) (hf : f ∈ sLocalPolarFreeTestSubspace F S) (c : ℂ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ Z F S μ ω f =ᶠ[𝓝[≠] c] G := by
  unfold sLocalPolarFreeTestSubspace at hf
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨φ, g, hφ, h0, rfl⟩ := h
    let a := sLocalRealArchParameters F S ω
    let j := sLocalComplexArchParameters F S ω
    let χ := sLocalFiniteZetaPhases F S ω
    obtain ⟨A, hA, heA⟩ := archimedeanNumberFieldZeta_exists_analyticGerm_of_flat F
      complexTamagawaAngularMeasure a j φ
      ((mem_schwartzFlatSubspace _ _).mp hφ) c
    obtain ⟨B, hB, heB⟩ :=
      sLocalFiniteZeta_exists_analyticGerm_of_piProduct_zero F S μ χ g h0 c
    refine ⟨fun z ↦ B z * A z, hB.mul hA, ?_⟩
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    filter_upwards [heA, heB] with z hz hw
    change archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z
      (sLocalFiniteZetaSchwartzTest F S μ χ z (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g))) = _
    rw [sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure, map_smul, smul_eq_mul]
    exact congrArg₂ (· * ·) hw hz
  | zero =>
    refine ⟨0, analyticAt_const, .of_forall fun z ↦ ?_⟩
    exact (sLocalContinuedMellinEval F S μ ω z).map_zero
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, hAx⟩ := hx
    obtain ⟨B, hB, hBy⟩ := hy
    refine ⟨fun z ↦ A z + B z, hA.add hB, ?_⟩
    filter_upwards [hAx,hBy] with z hx hy
    change sLocalContinuedMellinEval F S μ ω z (x+y) = _
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    obtain ⟨A, hA, hAx⟩ := hx
    refine ⟨fun z ↦ a * A z, analyticAt_const.mul hA, ?_⟩
    filter_upwards [hAx] with z hx
    change sLocalContinuedMellinEval F S μ ω z (a • x) = _
    rw [map_smul, smul_eq_mul]
    exact congrArg (a * ·) hx

/-- The normalized meromorphic representative of a flat test is entire on
each unitary component, including at the removable points. -/
theorem sLocalProductZeta_entire_of_polarFree (ω : PontryaginDual (K F S))
    (f : X F S) (hf : f ∈ sLocalPolarFreeTestSubspace F S) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) univ := by
  intro c hc
  have hm : MeromorphicOn (Z F S μ ω f) univ :=
    (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f).meromorphicOn
  obtain ⟨A, hA, he⟩ := sLocalProductZeta_exists_analyticGerm_of_polarFree F S μ ω f hf c
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ hc).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm hc, meromorphicOrderAt_congr he]
  exact hA.meromorphicOrderAt_nonneg

/-- Proposition 5.3.4.4(2) implies (1). A test with the same meromorphic
Mellin component as a flat test has an entire continuation. -/
theorem sLocalProductZeta_entire_of_flat_representative (ω : PontryaginDual (K F S))
    (f : X F S) (hf : ∃ g ∈ sLocalPolarFreeTestSubspace F S,
      ∀ c : ℂ, Z F S μ ω f =ᶠ[𝓝[≠] c] Z F S μ ω g) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) univ := by
  obtain ⟨g, hg, he⟩ := hf
  intro c hc
  have hm : MeromorphicOn (Z F S μ ω f) univ :=
    (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f).meromorphicOn
  obtain ⟨A, hA, hAg⟩ := sLocalProductZeta_exists_analyticGerm_of_polarFree F S μ ω g hg c
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ hc).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm hc, meromorphicOrderAt_congr ((he c).trans hAg)]
  exact hA.meromorphicOrderAt_nonneg

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

include hν in
/-- Every homogeneous class represented by a manuscript flat test
lies in the entire-Mellin subspace of the full finite principal-value image. -/
theorem sLocalArchPolarKernel_mk_of_polarFree (ω : PontryaginDual (K F S))
    (f : X F S) (hf : f ∈ sLocalPolarFreeTestSubspace F S) :
    (⟨(sLocalHomogeneousThetaKernel F S ν ω).mkQ f,
      ⟨f, by
        have hle : sLocalPolarFreeTestSubspace F S ≤ sLocalFiniteNonzeroTestSubspace F S Finset.univ := by
          rw [sLocalPolarFreeTestSubspace_eq_inf]
          exact inf_le_right
        exact hle hf, rfl⟩⟩ : sLocalArchPolarImage F S ν ω) ∈ sLocalArchPolarKernel F S μ ν hν ω := by
  exact (mem_sLocalArchPolarKernel_iff_entire F S μ ν hν ω _ f rfl).mpr
    (sLocalProductZeta_entire_of_polarFree F S μ ω f hf)

end

end Masullo
