import SLocalStandardThetaSlice
import SLocalUnramifiedThetaRange
import SLocalMeromorphicKernels

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

private abbrev Q (ν : Measure (K F S)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F S)) :=
  SLocalHomogeneousThetaQuotient F S ν ω

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

/-- Tensoring with the standard finite test and taking the actual
homogeneous theta class is continuous. -/
def sLocalStandardThetaMap (ω : PontryaginDual (K F S)) : Arch F →L[ℂ] Q F S ν ω := by
  let g := sLocalStandardFiniteTest F S ω
  let B := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  have hg : Continuous (fun f : Arch F => sLocalBruhatPure F S f g) :=
    ((continuous_inductiveTensor_lift_iff (sLocalBruhatPure F S)).mp
      (sLocalBruhatPure_lift_continuous F S)).1 g
  let P : Arch F →L[ℂ] sLocalBruhatImage F S :=
    ⟨(sLocalBruhatPure F S).flip g, hg⟩
  exact (sLocalHomogeneousThetaKernel F S ν ω).mkQL.comp P

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)) Measure.count
  (sLocalClassHaar F S ν))

include hν in
/-- Fixed standard finite tests exhaust the actual local homogeneous quotient. -/
theorem sLocalStandardThetaMap_surjective (ω : PontryaginDual (K F S)) :
    Surjective (sLocalStandardThetaMap F S ν ω) := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  intro b
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective M b
  obtain ⟨f, hf⟩ := exists_sLocalStandardThetaSlice F S μ ω a
  refine ⟨f, ?_⟩
  let x := sLocalBruhatPure F S f (sLocalStandardFiniteTest F S ω)
  change M.mkQ x = M.mkQ a
  apply sub_eq_zero.mp
  rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [mem_sLocalHomogeneousThetaKernel_iff,
    sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω (x - a) 1 zero_lt_one]
  intro y
  let z : ℂ := 1 + (y : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  change sLocalThetaZetaIntegral F S ν ω (x - a) z = 0
  rw [← sLocalContinuedZeta_eq_theta F S μ ν hν ω (x - a) hz]
  change sLocalContinuedMellinEval F S μ ω z (x - a) = 0
  have he : sLocalContinuedMellinEval F S μ ω z x = sLocalContinuedMellinEval F S μ ω z a := hf z hz
  rw [map_sub, he, sub_self]

include hν in
/-- A vertical line in the absolute convergence half-plane determines the
fixed-test theta kernel by the archimedean Mellin evaluations alone. -/
theorem mem_sLocalStandardThetaMap_ker_iff (ω : PontryaginDual (K F S)) (f : Arch F) :
    f ∈ (sLocalStandardThetaMap F S ν ω).ker ↔
      ∀ y : ℝ, archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
        (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω)
        (1 + (y : ℂ) * Complex.I) f = 0 := by
  let g := sLocalStandardFiniteTest F S ω
  let b := sLocalBruhatPure F S f g
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let C : ℂ := ∏ v : S, ((μ v).real (finitePlaceIntegralUnits F v.val) : ℂ)
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ =>
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ v)).ne'
  change M.mkQ b = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_sLocalHomogeneousThetaKernel_iff,
    sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω b 1 zero_lt_one]
  simp only [Complex.ofReal_one]
  apply forall_congr'
  intro y
  let z : ℂ := 1 + (y : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  rw [← sLocalContinuedZeta_eq_theta F S μ ν hν ω b hz]
  change sLocalContinuedMellinEval F S μ ω z (sLocalBruhatPure F S f g) = 0 ↔ _
  rw [sLocalStandardThetaSlice_mellin, sLocalStandardFiniteTest_cleared F S μ ω z hz,
    mul_eq_zero, or_iff_right]
  exact mul_ne_zero (inv_ne_zero (sLocalFiniteZetaDenominator_ne_zero_of_pos F S _ z hz)) hC

include hν in
/-- The standard theta map is open for the actual quotient topology. -/
theorem sLocalStandardThetaMap_isOpenMap (ω : PontryaginDual (K F S)) :
    IsOpenMap (sLocalStandardThetaMap F S ν ω) := by
  let X := Arch F
  let Y := Q F S ν ω
  letI : @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact completeSpace_schwartzMap
  obtain ⟨_, _, hmet, hc⟩ := sLocalHomogeneousTheta_isFrechet F S ν ω
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : TopologicalSpace.MetrizableSpace Y := hmet
  letI : CompleteSpace Y := hc
  letI : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  exact isOpenMap_of_surjective_complete_baire (sLocalStandardThetaMap F S ν ω)
    (sLocalStandardThetaMap_surjective F S ν μ hν ω)

include hν in
/-- The Schwartz space modulo the kernel of the fixed-test theta map is
topologically isomorphic to the actual local homogeneous quotient. -/
def sLocalStandardThetaQuotientEquiv (ω : PontryaginDual (K F S)) :
    (Arch F ⧸ (sLocalStandardThetaMap F S ν ω).ker) ≃L[ℂ] Q F S ν ω := by
  let A := sLocalStandardThetaMap F S ν ω
  let e := A.toLinearMap.quotKerEquivOfSurjective (sLocalStandardThetaMap_surjective F S ν μ hν ω)
  have he (x : Arch F) : e (A.ker.mkQ x) = A x :=
    A.toLinearMap.quotKerEquivOfSurjective_apply_mk _ x
  have hcomp : (e : (Arch F ⧸ A.ker) → Q F S ν ω) ∘ A.ker.mkQL = A := funext he
  have hcont := A.ker.isOpenQuotientMap_mkQL.continuous_comp_iff.mp
    (hcomp ▸ A.continuous)
  have hopen : IsOpenMap e := IsOpenMap.of_comp A.ker.mkQL.continuous
    A.ker.isOpenQuotientMap_mkQL.surjective (hcomp.symm ▸ sLocalStandardThetaMap_isOpenMap F S ν μ hν ω)
  exact ⟨e, hcont, e.toEquiv.continuous_symm_iff.mpr hopen⟩

local instance standardThetaGlobalMeasurable : MeasurableSpace (Idele F) := borel _
local instance standardThetaGlobalBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (χ : PontryaginDual (normOneIdeleClass F))
  (hs : Surjective (sIdeleClassInclusion F S))
  (hu : globalNormOneCharacter F χ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

/-- The standard-test map to the actual global homogeneous theta isotype. -/
def globalStandardThetaMap : Arch F →L[ℂ] (GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F η χ) :=
  (sLocalHomogeneousThetaToGlobalEquiv F χ η S hs hu ν).toContinuousLinearMap.comp
    (sLocalStandardThetaMap F S ν (sLocalNormOneCharacterOfGlobal F χ S hs hu))

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The global map takes the class of the same fixed-test insertion, with
integer-ring padding at the places outside the block. -/
theorem globalStandardThetaMap_apply (f : Arch F) :
    globalStandardThetaMap F S ν η χ hs hu f = (globalIdelicZetaComponentKernel F η χ).mkQ
      (sLocalBruhatPure F S f (sLocalStandardFiniteTest F S
        (sLocalNormOneCharacterOfGlobal F χ S hs hu))).val := by
  let ω := sLocalNormOneCharacterOfGlobal F χ S hs hu
  let b := sLocalBruhatPure F S f (sLocalStandardFiniteTest F S ω)
  have he := DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η χ S hs hu ν)
    (Submodule.Quotient.mk b)
  change sLocalHomogeneousThetaToGlobal F η χ S hs hu ν
      (sLocalThetaToComponent F S ν ω (Submodule.Quotient.mk b)) =
    globalThetaToComponent F η χ (sLocalThetaToGlobal F S (Submodule.Quotient.mk b)) at he
  rw [sLocalThetaToGlobal_mk] at he
  exact he

include hν in
/-- The standard-test map is an open surjection to the global isotype
when the localized block meets every idele class and carries the character. -/
theorem globalStandardThetaMap_open_surjective :
    IsOpenMap (globalStandardThetaMap F S ν η χ hs hu) ∧
      Surjective (globalStandardThetaMap F S ν η χ hs hu) := by
  let e := sLocalHomogeneousThetaToGlobalEquiv F χ η S hs hu ν
  let ω := sLocalNormOneCharacterOfGlobal F χ S hs hu
  exact ⟨e.isOpenMap.comp (sLocalStandardThetaMap_isOpenMap F S ν μ hν ω),
    e.surjective.comp (sLocalStandardThetaMap_surjective F S ν μ hν ω)⟩

include hν in
/-- The quotient of the archimedean Schwartz space by the kernel of the
fixed-test theta map is topologically the global homogeneous theta isotype. -/
def globalStandardThetaQuotientEquiv :
    (Arch F ⧸ (sLocalStandardThetaMap F S ν (sLocalNormOneCharacterOfGlobal F χ S hs hu)).ker) ≃L[ℂ]
      (GlobalBruhat F ⧸ globalIdelicZetaComponentKernel F η χ) :=
  (sLocalStandardThetaQuotientEquiv F S ν μ hν (sLocalNormOneCharacterOfGlobal F χ S hs hu)).trans
    (sLocalHomogeneousThetaToGlobalEquiv F χ η S hs hu ν)

include μ in
/-- The source class-group hypothesis supplies the covering condition,
and the local Haar normalization can always be chosen compatibly. -/
theorem exists_globalStandardThetaMap_open_surjective [Subsingleton (SPicardGroup F S)] :
    ∃ ν : Measure (K F S), ∃ hhaar : ν.IsHaarMeasure,
      letI := hhaar
      let A := globalStandardThetaMap F S ν η χ
        (sIdeleClassInclusion_surjective_of_subsingleton_sPicard F S) hu
      IsOpenMap A ∧ Surjective A := by
  let ρ := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨ν, hhaar, hν⟩ := sLocalClassHaar_exists_weil F S ρ
  letI := hhaar
  exact ⟨ν, hhaar, globalStandardThetaMap_open_surjective F S ν μ hν η χ _ hu⟩

end
end Masullo
