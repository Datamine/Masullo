import SLocalPaleyWienerDensity
import GlobalThetaSobolevIsotypes

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F
private abbrev K := normOneIdeleClass F
private abbrev Θ := GlobalThetaQuotient F
private abbrev ZeroTests := (GlobalBruhat.polarEvaluation F).ker

local instance globalPaleyWienerIdeleMeasurableSpace : MeasurableSpace (Idele F) := borel _
local instance globalPaleyWienerIdeleBorelSpace : BorelSpace (Idele F) := ⟨rfl⟩
local instance globalPaleyWienerNormOneMeasurableSpace : MeasurableSpace (K F) := borel _
local instance globalPaleyWienerNormOneBorelSpace : BorelSpace (K F) := ⟨rfl⟩
attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev M := globalIdelicZetaComponentKernel F η ω

/-- The zero-moment test quotient map into the polar-free global theta space. -/
def globalPolarThetaOfTest : ZeroTests F →L[ℂ] GlobalPolarTheta F :=
  ((globalThetaOperator F).ker.mkQL.comp (ZeroTests F).subtypeL).codRestrict _
    (fun f ↦ f.property)

theorem globalPolarThetaOfTest_surjective : Surjective (globalPolarThetaOfTest F) :=
  ((globalThetaOperator F).ker.isOpenQuotientMap_mkQL.restrictPreimage
    (GlobalPolarTheta F)).surjective

set_option maxHeartbeats 1600000 in
include hν in
/-- Polar-free representatives of a global homogeneous theta class can be
taken in any surjective base stage outside which the character is unramified. -/
theorem globalPolarTheta_exists_baseRepresentative (S : Finset (Place F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (f : ZeroTests F) :
    ∃ g : E F S, GlobalBruhat.polarEvaluation F g.val = 0 ∧
      (M F η ω).mkQ f.val = (M F η ω).mkQ g.val := by
  classical
  obtain ⟨T, x, hx⟩ := globalBruhat_exhausted F f.val
  let U := S ∪ T
  let y := sLocalBruhatTransition F (T := U) Finset.subset_union_right x
  have hy : y.val = f.val := hx
  let hsU := sIdeleClassInclusion_surjective_mono F (show S ⊆ U from Finset.subset_union_left) hs
  let huU := sUnramified_mono F (show S ⊆ U from Finset.subset_union_left) hu
  let J := SLocalThetaNormOne F U
  letI : CompactSpace J := sLocalThetaNormOne_compact F U
  let νU : Measure J := Measure.haar
  let ψ := sLocalNormOneCharacterOfGlobal F ω U hsU huU
  let A := sLocalHomogeneousThetaKernel F U νU ψ
  let j := sLocalHomogeneousThetaToGlobal F η ω U hsU huU νU
  have hj (v : E F U) : j (A.mkQ v) = (M F η ω).mkQ v.val :=
    DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω U hsU huU νU)
      ((sLocalThetaOperator F U).ker.mkQ v)
  obtain ⟨g, hg, hzero⟩ := exists_sLocalBaseRepresentative_preserves_zero_moments F ν ω η hν
    (show S ⊆ U from Finset.subset_union_left) hs hu νU y
  have hEq : (M F η ω).mkQ y.val = (M F η ω).mkQ g.val :=
    (hj y).symm.trans ((congrArg j hg).trans (hj _))
  exact ⟨g, hzero (by rw [hy]; exact f.property), hy ▸ hEq⟩

section Hilbert

local instance globalPaleyWienerIdeleClassMeasurableSpace : MeasurableSpace (IdeleClass F) := borel _
local instance globalPaleyWienerIdeleClassBorelSpace : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]
variable (a l r s : ℝ) (hs : 0 ≤ s)

private abbrev H := globalThetaSobolevCompletion F μ a l r s hs
private abbrev I := globalThetaSobolevDenseMap F μ a l r s hs
private abbrev ρ := globalThetaSobolevNormOneAction F μ a l r s hs
private abbrev U := compactActionIsotype (K := K F) (E := H F μ a l r s hs)
  (ρ F μ a l r s hs) ω

local instance : CompleteSpace (H F μ a l r s hs) :=
  globalThetaSobolevCompletion_complete F μ a l r s hs

local instance : IsClosed (U F ω μ a l r s hs : Set (H F μ a l r s hs)) :=
  fixedSubmodule_isClosed _

/-- The isotype projection of a dense polar-free test in the Hilbert completion. -/
def globalPaleyWienerTestMap : ZeroTests F →L[ℂ] U F ω μ a l r s hs :=
  (U F ω μ a l r s hs).orthogonalProjectionOnto.comp
    ((I F μ a l r s hs).comp (globalPolarThetaOfTest F))

theorem globalPaleyWienerTestMap_dense :
    DenseRange (globalPaleyWienerTestMap F ω μ a l r s hs) := by
  have hd : DenseRange ((I F μ a l r s hs) ∘ globalPolarThetaOfTest F) := by
    intro y
    rw [range_comp, (globalPolarThetaOfTest_surjective F).range_eq, image_univ]
    exact globalThetaSobolevCompletion_dense F μ a l r s hs y
  let P := (U F ω μ a l r s hs).orthogonalProjectionOnto
  have hP : Surjective P := fun y ↦ ⟨y.val,
    (U F ω μ a l r s hs).orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  exact hP.denseRange.comp hd P.continuous

set_option maxHeartbeats 2400000 in
/-- The Hilbert projection of a polar-free theta test depends only on the
corresponding global homogeneous theta class. -/
theorem globalPaleyWienerTestMap_eq_of_component
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (f g : ZeroTests F) (hfg : (M F η ω).mkQ f.val = (M F η ω).mkQ g.val) :
    globalPaleyWienerTestMap F ω μ a l r s hs f = globalPaleyWienerTestMap F ω μ a l r s hs g := by
  obtain ⟨j, _, _, _, hJ⟩ := globalThetaComponent_pettisSection F η ω τ
  let J := j.comp (globalThetaToComponent F η ω)
  let π := globalThetaPolarEvaluation F
  let A := I F μ a l r s hs
  let B := U F ω μ a l r s hs
  let P := B.starProjection
  have hmean : (τ.real univ : ℂ) = 1 := by simp [Measure.real]
  have hJ' (q : Θ F) : HasPositivePettisIntegral τ
      (fun k ↦ ((((ω k)⁻¹ : Circle) : ℂ)) • globalThetaNormOneAction F k q) (J q) := by
    have h := hJ q
    rw [hmean, one_smul] at h
    exact h
  have hpol (u : GlobalPolarTheta F) : π (J u.val) = 0 := by
    have hv (k : K F) : π (globalThetaNormOneAction F k u.val) = 0 := by
      change π (globalThetaTranslate F k.val u.val) = 0
      change globalThetaPolarEvaluation F (globalThetaTranslate F k.val u.val) = _
      rw [globalThetaPolarEvaluation_translate, show ideleClassNorm F k.val = 1 from k.property,
        one_smul, show globalThetaPolarEvaluation F u.val = 0 from u.property]
    have hcoord (L : (ℂ × ℂ) →L[ℂ] ℂ) : L (π (J u.val)) = 0 := by
      change (L.comp π) (J u.val) = 0
      rw [(hJ' u.val (L.comp π)).2]
      have hz (k : K F) : (L.comp π)
          ((((ω k)⁻¹ : Circle) : ℂ) • globalThetaNormOneAction F k u.val) = 0 := by
        simp only [ContinuousLinearMap.comp_apply, map_smul, hv, map_zero, smul_zero]
      simp only [hz, integral_zero]
    exact Prod.ext (hcoord (ContinuousLinearMap.fst ℂ ℂ ℂ))
      (hcoord (ContinuousLinearMap.snd ℂ ℂ ℂ))
  let J₀ := (J.comp (GlobalPolarTheta F).subtypeL).codRestrict
    (GlobalPolarTheta F) hpol
  have hcompare (u : GlobalPolarTheta F) : A (J₀ u) = P (A u) := by
    let D := ρ F μ a l r s hs
    have hP := ((globalThetaSobolev_normOne_decomposition F μ a l r s hs τ).1 ω).1 (A u)
    apply ext_inner_left ℂ
    intro x
    let ℓ : StrongDual ℂ (H F μ a l r s hs) := innerSL ℂ x
    let Q := (GlobalPolarTheta F)
    letI : PolynormableSpace ℂ (Θ F) :=
      polynormableSpace_complex_quotient (globalThetaOperator F).ker
    obtain ⟨ℓ', hℓ'⟩ := StrongDual.exists_extension Q (ℓ.comp A)
    have hleft : ℓ (A (J₀ u)) = ∫ k, ℓ' ((((ω k)⁻¹ : Circle) : ℂ) •
        globalThetaNormOneAction F k u.val) ∂τ := by
      exact (hℓ' (J₀ u)).symm.trans ((hJ' u.val ℓ').2)
    change ℓ (A (J₀ u)) = ℓ (P (A u))
    rw [hleft, (hP ℓ).2]
    apply integral_congr_ae
    exact .of_forall fun k ↦ by
      change ℓ' ((((ω k)⁻¹ : Circle) : ℂ) •
        globalThetaNormOneAction F k u.val) = ℓ ((((ω k)⁻¹ : Circle) : ℂ) • D k (A u))
      simp only [map_smul]
      apply congrArg ((((ω k)⁻¹ : Circle) : ℂ) • ·)
      exact (hℓ' (globalPolarThetaTranslate F k.val u)).trans
        (congrArg ℓ (globalThetaSobolevNormOneAction_dense F μ a l r s hs k u).symm)
  apply Subtype.ext
  change P (A (globalPolarThetaOfTest F f)) = P (A (globalPolarThetaOfTest F g))
  rw [← hcompare, ← hcompare]
  congr 1
  apply Subtype.ext
  exact congrArg j hfg


variable (S : Finset (Place F))

private def polarStageInclusion :
    (ZeroTests F).comap (sLocalBruhatInclusion F S).toLinearMap →L[ℂ] ZeroTests F :=
  ((sLocalBruhatInclusion F S).comp
    ((ZeroTests F).comap (sLocalBruhatInclusion F S).toLinearMap).subtypeL).codRestrict _ fun f ↦
      f.property

/-- A global Paley–Wiener level is the closure in the Hilbert isotype of
the images of the zero-moment tests with Fourier support in the given region.
The integer-ring transition to an enlarged stage represents the same global
Schwartz–Bruhat test, so the generators can be taken at the base stage. -/
def globalPaleyWienerHilbertLevel (B : Set (SAdeles F S)) :
    Submodule ℂ (U F ω μ a l r s hs) :=
  (((sLocalPaleyWienerTests F S B).comap
    ((ZeroTests F).comap (sLocalBruhatInclusion F S).toLinearMap).subtype).map
      ((globalPaleyWienerTestMap F ω μ a l r s hs).comp (polarStageInclusion F S)).toLinearMap).topologicalClosure

theorem globalPaleyWienerHilbertLevel_mono :
    Monotone (globalPaleyWienerHilbertLevel F ω μ a l r s hs S) := by
  intro B C h
  apply Submodule.topologicalClosure_mono
  apply Submodule.map_mono
  apply Submodule.comap_mono
  exact sLocalPaleyWienerTests_mono F S h

set_option maxHeartbeats 2400000 in
include hν in
/-- Both global families exhaust the actual polar-free Hilbert isotype
when the base contains the ramified places and represents every ideal class. -/
theorem globalPaleyWienerHilbertLevel_dense
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (hsur : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (region : ℝ → Set (SAdeles F S))
    (hr : region = sLocalPaleyWienerBox F S ∨ region = sLocalPaleyWienerRegion F S) :
    (⨆ R : ℝ, globalPaleyWienerHilbertLevel F ω μ a l r s hs S (region R)).topologicalClosure = ⊤ := by
  let J := (⨆ R : ℝ, globalPaleyWienerHilbertLevel F ω μ a l r s hs S (region R)).topologicalClosure
  have hJ : IsClosed (J : Set (U F ω μ a l r s hs)) := Submodule.isClosed_topologicalClosure _
  have htest : range (globalPaleyWienerTestMap F ω μ a l r s hs) ⊆ J := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg, hfg⟩ := globalPolarTheta_exists_baseRepresentative F η ν hν ω S hsur hu f
    let Z := (ZeroTests F).comap (sLocalBruhatInclusion F S).toLinearMap
    let g₀ : Z := ⟨g, hg⟩
    rw [globalPaleyWienerTestMap_eq_of_component F η ω μ a l r s hs τ f
      (polarStageInclusion F S g₀) hfg]
    obtain ⟨v, hv, hlim⟩ := exists_sLocalCompactFourier_sequence_preserves_moments F S g
    let v₀ (n : ℕ) : Z := ⟨v n, (hv n).2.trans hg⟩
    have hvlim : Tendsto v₀ atTop (𝓝 g₀) := tendsto_subtype_rng.mpr hlim
    let P := (globalPaleyWienerTestMap F ω μ a l r s hs).comp (polarStageInclusion F S)
    apply hJ.mem_of_tendsto ((P.continuous.tendsto g₀).comp hvlim)
    apply Eventually.of_forall
    intro n
    obtain ⟨X, hX, hx⟩ := (mem_sLocalCompactFourierTests_iff F S (v n)).mp (hv n).1
    have hregion : ∃ R, v n ∈ sLocalPaleyWienerTests F S (region R) := by
      rcases hr with rfl | rfl
      · exact ⟨X, hx⟩
      · exact ⟨_, sLocalPaleyWienerTests_mono F S (sLocalPaleyWienerBox_subset_region F S hX.le) hx⟩
    obtain ⟨R, hR⟩ := hregion
    exact Submodule.le_topologicalClosure _ (le_iSup
      (fun R ↦ globalPaleyWienerHilbertLevel F ω μ a l r s hs S (region R)) R
      (Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨v₀ n, hR, rfl⟩)))
  apply top_unique
  intro y _
  exact hJ.closure_subset_iff.mpr htest (globalPaleyWienerTestMap_dense F ω μ a l r s hs y)


private def globalGeometricIsotypeEmbedding :
    U F ω μ a l r s hs →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  (H F μ a l r s hs).subtypeₗᵢ.comp (U F ω μ a l r s hs).subtypeₗᵢ

/-- The geometric subspace in the specified norm-one isotype, viewed in the
ambient global Sobolev Hilbert space. -/
def globalGeometricIsotype : Submodule ℂ (Lp ℂ 2 μ) :=
  (globalGeometricIsotypeEmbedding F ω μ a l r s hs).toLinearMap.range

/-- The global Paley–Wiener level viewed in the ambient Sobolev space. -/
def globalAmbientPaleyWienerLevel (B : Set (SAdeles F S)) : Submodule ℂ (Lp ℂ 2 μ) :=
  (globalPaleyWienerHilbertLevel F ω μ a l r s hs S B).map
    (globalGeometricIsotypeEmbedding F ω μ a l r s hs).toLinearMap

private theorem globalGeometricIsotype_isClosed :
    IsClosed (globalGeometricIsotype F ω μ a l r s hs : Set (Lp ℂ 2 μ)) := by
  letI : CompleteSpace (U F ω μ a l r s hs) := (fixedSubmodule_isClosed _).completeSpace_coe
  exact (globalGeometricIsotypeEmbedding F ω μ a l r s hs).isometry.isClosedEmbedding.isClosed_range

private theorem globalAmbientPaleyWienerLevel_isClosed (B : Set (SAdeles F S)) :
    IsClosed (globalAmbientPaleyWienerLevel F ω μ a l r s hs S B : Set (Lp ℂ 2 μ)) := by
  letI : CompleteSpace (U F ω μ a l r s hs) := (fixedSubmodule_isClosed _).completeSpace_coe
  exact (globalGeometricIsotypeEmbedding F ω μ a l r s hs).isometry.isClosedEmbedding.isClosedMap
    _ (Submodule.isClosed_topologicalClosure _)

/-- The orthogonal projection onto the polar-free geometric isotype. -/
def globalGeometricIsotypeProjection : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  letI := globalGeometricIsotype_isClosed F ω μ a l r s hs
  (globalGeometricIsotype F ω μ a l r s hs).starProjection

/-- The orthogonal projection onto an ambient global Paley–Wiener level. -/
def globalPaleyWienerLevelProjection (B : Set (SAdeles F S)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  letI := globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S B
  (globalAmbientPaleyWienerLevel F ω μ a l r s hs S B).starProjection

theorem globalPaleyWienerLevelProjection_mem_theta (B : Set (SAdeles F S)) (x : Lp ℂ 2 μ) :
    globalPaleyWienerLevelProjection F ω μ a l r s hs S B x ∈ H F μ a l r s hs := by
  letI := globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S B
  obtain ⟨u, _, hu⟩ := Submodule.mem_map.mp
    ((globalAmbientPaleyWienerLevel F ω μ a l r s hs S B).starProjection_apply_mem x)
  exact hu ▸ u.val.property

theorem globalGeometricIsotypeProjection_adjoint :
    (globalGeometricIsotypeProjection F ω μ a l r s hs).adjoint =
      globalGeometricIsotypeProjection F ω μ a l r s hs := by
  letI := globalGeometricIsotype_isClosed F ω μ a l r s hs
  exact (isSelfAdjoint_starProjection (globalGeometricIsotype F ω μ a l r s hs)).star_eq

theorem globalPaleyWienerLevelProjection_adjoint (B : Set (SAdeles F S)) :
    (globalPaleyWienerLevelProjection F ω μ a l r s hs S B).adjoint =
      globalPaleyWienerLevelProjection F ω μ a l r s hs S B := by
  letI := globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S B
  exact (isSelfAdjoint_starProjection
    (globalAmbientPaleyWienerLevel F ω μ a l r s hs S B)).star_eq

theorem globalPaleyWienerLevelProjection_norm (B : Set (SAdeles F S)) :
    ‖globalPaleyWienerLevelProjection F ω μ a l r s hs S B‖ ≤ 1 := by
  letI := globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S B
  exact (globalAmbientPaleyWienerLevel F ω μ a l r s hs S B).starProjection_norm_le

set_option maxHeartbeats 2000000 in
include hν in
/-- The absolute and invariant global Paley–Wiener projections converge
strongly to the polar-free geometric projection on the given isotype. -/
theorem globalPaleyWienerLevelProjection_tendsto
    (τ : Measure (K F)) [τ.IsHaarMeasure] [IsProbabilityMeasure τ]
    (hsur : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (region : ℝ → Set (SAdeles F S))
    (hr : region = sLocalPaleyWienerBox F S ∨ region = sLocalPaleyWienerRegion F S)
    (x : Lp ℂ 2 μ) :
    Tendsto (fun R ↦ globalPaleyWienerLevelProjection F ω μ a l r s hs S (region R) x)
      atTop (𝓝 (globalGeometricIsotypeProjection F ω μ a l r s hs x)) := by
  let j := globalGeometricIsotypeEmbedding F ω μ a l r s hs
  let A (R : ℝ) := globalPaleyWienerHilbertLevel F ω μ a l r s hs S (region R)
  let B (R : ℝ) := globalAmbientPaleyWienerLevel F ω μ a l r s hs S (region R)
  let V := globalGeometricIsotype F ω μ a l r s hs
  letI (R : ℝ) : IsClosed (B R : Set (Lp ℂ 2 μ)) :=
    globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S (region R)
  letI : IsClosed (V : Set (Lp ℂ 2 μ)) := globalGeometricIsotype_isClosed F ω μ a l r s hs
  letI : IsClosed ((⨆ R, B R).topologicalClosure : Set (Lp ℂ 2 μ)) :=
    Submodule.isClosed_topologicalClosure _
  have hA := globalPaleyWienerHilbertLevel_dense F η ν hν ω μ a l r s hs S τ hsur hu region hr
  have hV : (⨆ R, B R).topologicalClosure = V := by
    apply le_antisymm
    · apply (⨆ R, B R).topologicalClosure_minimal ?_
        (show IsClosed (V : Set (Lp ℂ 2 μ)) from inferInstance)
      apply iSup_le
      intro R y hy
      obtain ⟨u, _, h⟩ := Submodule.mem_map.mp hy
      exact ⟨u, h⟩
    · have hc := (⨆ R, A R).topologicalClosure_map j.toContinuousLinearMap
      rw [show (⨆ R, A R).topologicalClosure = ⊤ from hA, Submodule.map_top,
        Submodule.map_iSup] at hc
      exact hc
  have hrm : Monotone region := by
    rcases hr with rfl | rfl
    · exact sLocalPaleyWienerBox_mono F S
    · exact sLocalPaleyWienerRegion_mono F S
  have hB : Monotone B :=
    fun _ _ h ↦ Submodule.map_mono (globalPaleyWienerHilbertLevel_mono F ω μ a l r s hs S (hrm h))
  have h := Submodule.starProjection_tendsto_closure_iSup B hB x
  have hcongr (P Q : Submodule ℂ (Lp ℂ 2 μ)) [P.HasOrthogonalProjection]
      [Q.HasOrthogonalProjection] (he : P = Q) : P.starProjection x = Q.starProjection x := by
    subst Q
    rfl
  have he := hcongr _ _ hV
  rwa [he] at h

/-- The specified norm-one isotype in the ambient Sobolev Hilbert space. -/
def globalAmbientSobolevIsotype : Submodule ℂ (Lp ℂ 2 μ) :=
  thetaCharacterSubspace (fun k : K F ↦
    hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) l r s hs k.val)
    (fun k ↦ (ω k : ℂ))

theorem globalAmbientSobolevIsotype_isClosed :
    IsClosed (globalAmbientSobolevIsotype F ω μ l r s hs : Set (Lp ℂ 2 μ)) :=
  isClosed_thetaCharacterSubspace _ _

private theorem globalGeometricIsotypeEmbedding_mem_ambient (u : U F ω μ a l r s hs) :
    globalGeometricIsotypeEmbedding F ω μ a l r s hs u ∈
      globalAmbientSobolevIsotype F ω μ l r s hs := by
  apply (mem_thetaCharacterSubspace _ _ _).mpr
  intro k
  have hu := u.property k
  change hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs k.val (u.val : Lp ℂ 2 μ) =
      (ω k : ℂ) • (u.val : Lp ℂ 2 μ)
  have he := congrArg (fun z : H F μ a l r s hs ↦ (z : Lp ℂ 2 μ)) hu
  change ((((ω k)⁻¹ : Circle) : ℂ) • hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs k.val (u.val : Lp ℂ 2 μ)) =
      (u.val : Lp ℂ 2 μ) at he
  have h := congrArg ((ω k : ℂ) • ·) he
  rwa [smul_smul, Circle.coe_inv, mul_inv_cancel₀ (ω k).coe_ne_zero, one_smul] at h

/-- The orthogonal projection onto the ambient isotype. -/
def globalAmbientSobolevIsotypeProjection : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  letI := globalAmbientSobolevIsotype_isClosed F ω μ l r s hs
  (globalAmbientSobolevIsotype F ω μ l r s hs).starProjection

theorem globalGeometricIsotypeProjection_comp_ambient :
    (globalGeometricIsotypeProjection F ω μ a l r s hs).comp
      (globalAmbientSobolevIsotypeProjection F ω μ l r s hs) =
        globalGeometricIsotypeProjection F ω μ a l r s hs := by
  letI := globalAmbientSobolevIsotype_isClosed F ω μ l r s hs
  letI := globalGeometricIsotype_isClosed F ω μ a l r s hs
  apply Submodule.starProjection_comp_starProjection_of_le
  rintro _ ⟨u, rfl⟩
  exact globalGeometricIsotypeEmbedding_mem_ambient F ω μ a l r s hs u

theorem globalPaleyWienerLevelProjection_comp_ambient (B : Set (SAdeles F S)) :
    (globalPaleyWienerLevelProjection F ω μ a l r s hs S B).comp
      (globalAmbientSobolevIsotypeProjection F ω μ l r s hs) =
        globalPaleyWienerLevelProjection F ω μ a l r s hs S B := by
  letI := globalAmbientSobolevIsotype_isClosed F ω μ l r s hs
  letI := globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S B
  apply Submodule.starProjection_comp_starProjection_of_le
  rintro _ ⟨u, _, rfl⟩
  exact globalGeometricIsotypeEmbedding_mem_ambient F ω μ a l r s hs u

theorem globalGeometricIsotypeProjection_mapsTo_ambient :
    MapsTo (globalGeometricIsotypeProjection F ω μ a l r s hs)
      (globalAmbientSobolevIsotype F ω μ l r s hs) (globalAmbientSobolevIsotype F ω μ l r s hs) := by
  letI := globalGeometricIsotype_isClosed F ω μ a l r s hs
  intro x _
  obtain ⟨u, hu⟩ := (globalGeometricIsotype F ω μ a l r s hs).starProjection_apply_mem x
  exact hu ▸ globalGeometricIsotypeEmbedding_mem_ambient F ω μ a l r s hs u

theorem globalPaleyWienerLevelProjection_mapsTo_ambient (B : Set (SAdeles F S)) :
    MapsTo (globalPaleyWienerLevelProjection F ω μ a l r s hs S B)
      (globalAmbientSobolevIsotype F ω μ l r s hs) (globalAmbientSobolevIsotype F ω μ l r s hs) := by
  letI := globalAmbientPaleyWienerLevel_isClosed F ω μ a l r s hs S B
  intro x _
  obtain ⟨u, _, hu⟩ := Submodule.mem_map.mp
    ((globalAmbientPaleyWienerLevel F ω μ a l r s hs S B).starProjection_apply_mem x)
  exact hu ▸ globalGeometricIsotypeEmbedding_mem_ambient F ω μ a l r s hs u

end Hilbert

end
end Masullo
