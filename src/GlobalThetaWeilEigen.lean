import GlobalThetaDualGeneration
import GlobalWeilEigenUniqueness

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev E := GlobalBruhat F
private abbrev Θ := GlobalThetaQuotient F
private abbrev M := (globalThetaOperator F).ker
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : (globalIdeleTamagawa F).IsHaarMeasure := globalIdeleTamagawa_isHaar F

private theorem strongDual_eval_differentiable {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [ContinuousSMul ℂ X] {A : ℂ → StrongDual ℂ X} (hA : Differentiable ℂ A) (x : X) :
    Differentiable ℂ (fun z => A z x) := by
  intro z
  exact (vectorHolomorphic_hasDerivAt_comp hA.differentiableOn isOpen_univ
    (strongBidualEvaluation x) ⟨z, mem_univ z⟩).differentiableAt

/-- Lifting an entire family of test distributions that vanishes on the
theta kernel gives an entire family in the strong quotient dual. -/
theorem globalThetaWeil_lift_holomorphic
    (A : ℂ → StrongDual ℂ (E F)) (hA : Differentiable ℂ A)
    (hvan : ∀ z f, f ∈ M F → A z f = 0) :
    Differentiable ℂ (fun z => (M F).liftQL (A z) (hvan z)) := by
  let D := StrongDual ℂ (Θ F)
  letI : T2Space (Θ F) := globalThetaQuotient_t2Space F
  letI : UniformSpace (Θ F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Θ F) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Θ F) := globalThetaQuotient_complete F
  letI : BarrelledSpace ℂ (Θ F) := globalThetaQuotient_barrelled F
  letI : CompleteSpace D := globalThetaQuotient_strongDual_complete F
  letI : PolynormableSpace ℂ D := strongDual_withBoundedSeminorms.toPolynormableSpace
  letI : PolynormableSpace ℂ (Θ F) := (globalThetaQuotient_nuclear F).2.1
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (globalThetaQuotient_nuclear F)
  apply differentiableOn_univ.mp
  apply differentiableOn_of_weaklyHolomorphicOn isOpen_univ
  intro φ
  obtain ⟨q, rfl⟩ := e.surjective φ
  obtain ⟨f, rfl⟩ := (M F).mkQ_surjective q
  exact (strongDual_eval_differentiable hA f).differentiableOn.congr fun z _ =>
    (he ((M F).mkQ f) ((M F).liftQL (A z) (hvan z))).trans (by rfl)

private theorem normalizedGlobalWeil_vanishes_on_theta
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F))
    (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (L : ℂ → ℂ) (A : ℂ → StrongDual ℂ (E F))
    (hA : Differentiable ℂ A)
    (hE : EqOn L
      (fun z => ((2 : ℂ) ^ Fintype.card {v : InfinitePlace F // v.IsComplex})⁻¹ *
        (globalWeilTamagawaScale F * globalCompletedHeckeEuler F ω S hS hu z))
      {z | 1 < z.re})
    (hfac : ∀ z, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L w • A w)
    (z : ℂ) (f : E F) (hf : f ∈ M F) : A z f = 0 := by
  have hzero (w : ℂ) : globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 w = 0 := by
    have hθ : ∀ q, adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q = 0 := by
      have h := LinearMap.mem_ker.mp hf
      exact congrFun h
    exact (adelicTheta_zero_iff_continuedZeta F ν f).mp hθ ω w
  have hnonzero (w : ℂ) (hw : 1 < w.re) : L w ≠ 0 := by
    rw [hE hw]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num)))
      (mul_ne_zero (globalWeilTamagawaScale_ne_zero F)
        (globalCompletedHeckeEuler_ne_zero F ω S hS hu hw))
  have hnear : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 1 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hz : (fun w => A w f) =ᶠ[𝓝[≠] (2 : ℂ)] 0 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, hfac 2] with w hw he
    have he' := DFunLike.congr_fun he f
    change globalContinuedMellinEval F ν ω w f = L w * A w f at he'
    rw [globalContinuedMellinEval_apply, hzero w] at he'
    exact (mul_eq_zero.mp he'.symm).resolve_left (hnonzero w hw)
  have ha := (strongDual_eval_differentiable hA f).differentiableOn.analyticOnNhd isOpen_univ
  exact (ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (2 : ℂ)) hz.frequently) (mem_univ z)

private theorem globalThetaTranspose_injective :
    Injective (globalThetaTranspose F) := (globalThetaTranspose_isEmbedding F).injective

/-- The transpose identifies the covariance law on theta classes with
the same covariance law on adelic test functions. -/
theorem globalThetaTranspose_eigen_iff (c : IdeleQuasiCharacter F)
    (T : StrongDual ℂ (Θ F)) :
    globalThetaTranspose F T ∈ adelicWeilEigenspace F c ↔
      ∀ q x, T (globalThetaTranslate F q x) = (c q : ℂ) * T x := by
  constructor
  · intro h q x
    obtain ⟨a, rfl⟩ := ideleClassMap_surjective F q
    obtain ⟨f, rfl⟩ := (M F).mkQ_surjective x
    change T (globalThetaTranslate F (ideleClassMap F a) (Submodule.Quotient.mk f)) =
      (c (ideleClassMap F a) : ℂ) * T (Submodule.Quotient.mk f)
    rw [globalThetaTranslate_class, globalThetaTranslateIdeles_mk]
    exact h a f
  · intro h a f
    change T (Submodule.Quotient.mk (GlobalBruhat.leftTranslate F a f)) =
      (c (ideleClassMap F a) : ℂ) * T (Submodule.Quotient.mk f)
    rw [← globalThetaTranslateIdeles_mk, ← globalThetaTranslate_class]
    exact h (ideleClassMap F a) (Submodule.Quotient.mk f)

/-- The space of continuous covariant functionals on the global theta quotient. -/
def globalThetaWeilEigenspace (c : IdeleQuasiCharacter F) :
    Submodule ℂ (StrongDual ℂ (Θ F)) :=
  (adelicWeilEigenspace F c).comap (globalThetaTranspose F).toLinearMap

theorem mem_globalThetaWeilEigenspace (c : IdeleQuasiCharacter F) (T : StrongDual ℂ (Θ F)) :
    T ∈ globalThetaWeilEigenspace F c ↔
      ∀ q x, T (globalThetaTranslate F q x) = (c q : ℂ) * T x :=
  globalThetaTranspose_eigen_iff F c T

private theorem adelicWeil_span_of_normalized (c : IdeleQuasiCharacter F)
    (A : StrongDual ℂ (E F)) (hA : A ∈ adelicWeilEigenspace F c)
    (g : E F) (hg : A g = 1) (T : StrongDual ℂ (E F)) (hT : T ∈ adelicWeilEigenspace F c) :
    T = T g • A := by
  let a : adelicWeilEigenspace F c := ⟨A, hA⟩
  have ha : a ≠ 0 := by
    intro h
    have hz : A g = 0 := congrArg (fun b : adelicWeilEigenspace F c => b.val g) h
    rw [hg] at hz
    exact one_ne_zero hz
  obtain ⟨b, hb⟩ := (finrank_eq_one_iff_of_nonzero' a ha).mp
    (adelicWeilEigenspace_finrank F c) ⟨T, hT⟩
  have h : b • A = T := congrArg Subtype.val hb
  have hb' : b = T g := by
    have h' := DFunLike.congr_fun h g
    change b * A g = T g at h'
    rwa [hg, mul_one] at h'
  rw [hb'] at h
  exact h.symm

set_option maxHeartbeats 1500000 in
/-- The normalized adelic family from the corrected Gaussian factorization
descends to a holomorphic family of generators on the global theta quotient. -/
theorem exists_globalThetaWeil_normalized_family
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count
      (globalClassMeasure F ν))
    (ω : PontryaginDual (K F))
    (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :
    let c (z : ℂ) := ideleNormTwist F (compactIdeleClassCharacter F ω) z
    let g := (correctedGlobalWeilGaussian F S ω hS hu).val
    ∃ (L : ℂ → ℂ) (A : ℂ → StrongDual ℂ (E F)) (B : ℂ → StrongDual ℂ (Θ F)),
      MeromorphicOn L univ ∧ Differentiable ℂ A ∧ Differentiable ℂ B ∧
      (∀ z, A z ∈ adelicWeilEigenspace F (c z) ∧ B z ∈ globalThetaWeilEigenspace F (c z)) ∧
      (∀ z, globalThetaTranspose F (B z) = A z) ∧
      (∀ z, A z g = 1 ∧ B z (Submodule.Quotient.mk g) = 1) ∧
      (∀ z, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L w • A w) ∧
      (∀ z, globalZetaContinued F ν g (compactIdeleClassCharacter F ω) 0 =ᶠ[𝓝[≠] z] L) ∧
      (∀ z T, T ∈ adelicWeilEigenspace F (c z) → T = T g • A z) ∧
      (∀ z T, T ∈ globalThetaWeilEigenspace F (c z) → T = T (Submodule.Quotient.mk g) • B z) := by
  intro c g
  obtain ⟨L, A, hE, hL, hA, hg, hcov, hfac, hLref, _⟩ :=
    exists_globalWeil_correctedGaussian_family F S ω hS hu ν hν
  have hvan : ∀ z f, f ∈ M F → A z f = 0 :=
    normalizedGlobalWeil_vanishes_on_theta F ν ω S hS hu L A hA hE hfac
  let B (z : ℂ) : StrongDual ℂ (Θ F) := (M F).liftQL (A z) (hvan z)
  have hB (z : ℂ) : globalThetaTranspose F (B z) = A z := by ext f; rfl
  have hEig (z : ℂ) : A z ∈ adelicWeilEigenspace F (c z) := hcov z
  have hspan (z : ℂ) (T : StrongDual ℂ (E F)) (hT : T ∈ adelicWeilEigenspace F (c z)) :
      T = T g • A z := adelicWeil_span_of_normalized F (c z) (A z) (hEig z) g (hg z) T hT
  refine ⟨L, A, B, hL, hA, globalThetaWeil_lift_holomorphic F A hA hvan, ?_, hB,
    fun z => ⟨hg z, hg z⟩, hfac, hLref, hspan, ?_⟩
  · intro z
    refine ⟨hEig z, ?_⟩
    change globalThetaTranspose F (B z) ∈ adelicWeilEigenspace F (c z)
    rw [hB]
    exact hEig z
  · intro z T hT
    apply globalThetaTranspose_injective F
    change globalThetaTranspose F T ∈ adelicWeilEigenspace F (c z) at hT
    rw [map_smul, hB]
    exact hspan z _ hT

/-- Every covariant continuous adelic functional descends uniquely to the
global theta quotient, for an arbitrary idele class quasi-character. -/
theorem globalThetaWeil_existsUnique_lift (c : IdeleQuasiCharacter F)
    (T : StrongDual ℂ (E F)) (hT : T ∈ adelicWeilEigenspace F c) :
    ∃! U : StrongDual ℂ (Θ F), globalThetaTranspose F U = T ∧ U ∈ globalThetaWeilEigenspace F c := by
  obtain ⟨ω, z, rfl, _⟩ := ideleClassCharacter_existsUnique_compact_twist F c
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨ν, hν, hW, _⟩ := globalIdeleTamagawa_exists_weil F
  letI := hν
  obtain ⟨_, A, B, _, _, _, hEig, hB, hg, _, _, hspan, _⟩ :=
    exists_globalThetaWeil_normalized_family F ν hW ω S hs hu
  let d := T (correctedGlobalWeilGaussian F S ω hs hu).val
  have he := hspan z T hT
  have hLift : globalThetaTranspose F (d • B z) = T := by
    rw [map_smul, hB]
    exact he.symm
  refine ⟨d • B z, ⟨hLift, Submodule.smul_mem _ _ (hEig z).2⟩, ?_⟩
  intro U hU
  exact globalThetaTranspose_injective F (hU.1.trans hLift.symm)

/-- The global transpose induces an isomorphism on each eigenspace. -/
def globalThetaWeilEigenspace_equiv (c : IdeleQuasiCharacter F) :
    globalThetaWeilEigenspace F c ≃ₗ[ℂ] adelicWeilEigenspace F c := by
  let L : globalThetaWeilEigenspace F c →ₗ[ℂ] adelicWeilEigenspace F c :=
    ((globalThetaTranspose F).toLinearMap.comp (globalThetaWeilEigenspace F c).subtype).codRestrict
      (adelicWeilEigenspace F c) fun U => U.property
  apply LinearEquiv.ofBijective L
  constructor
  · intro U V h
    exact Subtype.ext (globalThetaTranspose_injective F (congrArg Subtype.val h))
  · intro T
    obtain ⟨U, hU, _⟩ := globalThetaWeil_existsUnique_lift F c T.val T.property
    exact ⟨⟨U, hU.2⟩, Subtype.ext hU.1⟩

theorem globalThetaWeilEigenspace_finrank (c : IdeleQuasiCharacter F) :
    Module.finrank ℂ (globalThetaWeilEigenspace F c) = 1 :=
  (globalThetaWeilEigenspace_equiv F c).finrank_eq.trans (adelicWeilEigenspace_finrank F c)

end
end Masullo
