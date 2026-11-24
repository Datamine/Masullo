import SLocalArchRangeComparison
import HomogeneousThetaPlaceLimit
import SLocalPaddingCharacters

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace (SIdeleQuotient F S) := borel _
local instance (S : Finset (HeightOneSpectrum (𝓞 F))) : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩

private theorem globalWeilPrincipalValues_mem_thetaKernel_iff
    (T : Finset (HeightOneSpectrum (𝓞 F))) (f : GlobalBruhat F) :
    globalWeilPrincipalValues F T f ∈ (globalThetaOperator F).ker ↔
      f ∈ (globalThetaOperator F).ker := by
  classical
  obtain ⟨A, g, hg⟩ := globalBruhat_exhausted F f
  let S := A ∪ T
  let x := sLocalBruhatTransition F (show A ⊆ S from Finset.subset_union_left) g
  let U : Finset S := Finset.univ.filter fun v ↦ v.val ∈ T
  have hU : U.map ⟨Subtype.val, Subtype.val_injective⟩ = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro hv
      exact Finset.mem_map.mpr ⟨⟨v, Finset.mem_union_right A hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  have hx : x.val = f := hg
  rw [← hx, ← hU, globalWeilPrincipalValues_stage,
    ← (sLocalThetaKernel_iff_global F S _), ← (sLocalThetaKernel_iff_global F S x)]
  obtain ⟨P, ⟨hP, hmk⟩, _⟩ := existsUnique_sLocalWeilPrincipalValuesQuotient F S U
  let N := (sLocalThetaOperator F S).ker
  rw [← Submodule.Quotient.mk_eq_zero N, ← Submodule.Quotient.mk_eq_zero N]
  change N.mkQ (sLocalWeilPrincipalValues F S U x) = 0 ↔ N.mkQ x = 0
  rw [← hmk x]
  nth_rewrite 1 [← map_zero P]
  exact hP.eq_iff

/-- Global finite principal values descend to a continuous operator on
the ordinary adelic theta quotient. -/
def globalWeilPrincipalValuesQuotient (T : Finset (HeightOneSpectrum (𝓞 F))) :
    GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F := by
  let N := (globalThetaOperator F).ker
  refine N.liftQL (N.mkQL.comp (globalWeilPrincipalValues F T)) ?_
  intro f hf
  exact (Submodule.Quotient.mk_eq_zero N).mpr
    ((globalWeilPrincipalValues_mem_thetaKernel_iff F T f).mpr hf)

theorem globalWeilPrincipalValuesQuotient_injective (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Function.Injective (globalWeilPrincipalValuesQuotient F T) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  let N := (globalThetaOperator F).ker
  obtain ⟨f, rfl⟩ := N.mkQ_surjective q
  change Submodule.Quotient.mk (p := N) (globalWeilPrincipalValues F T f) = 0 at hq
  change Submodule.Quotient.mk (p := N) f = 0
  rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
  exact (globalWeilPrincipalValues_mem_thetaKernel_iff F T f).mp hq

/-- On the ordinary theta quotients, the descended operators commute with
every finite-stage insertion containing the selected places. -/
theorem globalWeilPrincipalValuesQuotient_stage
    (S : Finset (HeightOneSpectrum (𝓞 F))) (T : Finset S)
    (P : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S)
    (hP : ∀ f : sLocalBruhatImage F S,
      P ((sLocalThetaOperator F S).ker.mkQ f) =
        (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S T f)) :
    (globalWeilPrincipalValuesQuotient F (T.map ⟨Subtype.val, Subtype.val_injective⟩)).comp
        (sLocalThetaToGlobal F S) =
      (sLocalThetaToGlobal F S).comp P := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := (sLocalThetaOperator F S).ker.mkQ_surjective q
  change (globalThetaOperator F).ker.mkQ
      (globalWeilPrincipalValues F (T.map ⟨Subtype.val, Subtype.val_injective⟩) f.val) =
    sLocalThetaToGlobal F S (P ((sLocalThetaOperator F S).ker.mkQ f))
  rw [globalWeilPrincipalValues_stage, hP]
  rfl

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ω : PontryaginDual (normOneIdeleClass F))
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : Function.Surjective (sIdeleClassInclusion F S))
variable (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (ν : Measure (SLocalThetaNormOne F S)) [ν.IsHaarMeasure]

private theorem sLocalHomogeneousThetaToGlobal_mk_representative (f : sLocalBruhatImage F S) :
    sLocalHomogeneousThetaToGlobal F η ω S hS hω ν
      ((sLocalHomogeneousThetaKernel F S ν (sLocalNormOneCharacterOfGlobal F ω S hS hω)).mkQ f) =
        (globalIdelicZetaComponentKernel F η ω).mkQ f.val :=
  DFunLike.congr_fun (sLocalHomogeneousThetaToGlobal_comp F η ω S hS hω ν)
    ((sLocalThetaOperator F S).ker.mkQ f)

/-- The local-to-global range implication in Proposition 7.2.2.1.
The selected principal-value product commutes with padding on the
specified homogeneous component. -/
theorem sLocalHomogeneousThetaToGlobal_mem_principalValue_range (T : Finset S)
    (q : SLocalHomogeneousThetaQuotient F S ν (sLocalNormOneCharacterOfGlobal F ω S hS hω))
    (hq : q ∈ (sLocalFiniteNonzeroTestSubspace F S T).map
      (sLocalHomogeneousThetaKernel F S ν (sLocalNormOneCharacterOfGlobal F ω S hS hω)).mkQ) :
    sLocalHomogeneousThetaToGlobal F η ω S hS hω ν q ∈
      range (fun g : GlobalBruhat F ↦
        (globalIdelicZetaComponentKernel F η ω).mkQ
          (globalWeilPrincipalValues F (T.map ⟨Subtype.val, Subtype.val_injective⟩) g)) := by
  obtain ⟨f, hf, rfl⟩ := hq
  rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace] at hf
  obtain ⟨g, rfl⟩ := hf
  refine ⟨g.val, ?_⟩
  change (globalIdelicZetaComponentKernel F η ω).mkQ
    (globalWeilPrincipalValues F (T.map ⟨Subtype.val, Subtype.val_injective⟩) g.val) = _
  rw [globalWeilPrincipalValues_stage]
  exact (sLocalHomogeneousThetaToGlobal_mk_representative F η ω S hS hω ν
    (sLocalWeilPrincipalValues F S T g)).symm

section Reflection

local instance (U : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace (SAdeles F U)ˣ := borel _
local instance (U : Finset (HeightOneSpectrum (𝓞 F))) : BorelSpace (SAdeles F U)ˣ := ⟨rfl⟩

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev productHaar (U : Finset (HeightOneSpectrum (𝓞 F))) :=
  sLocalZetaProductMeasure F U (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)

variable (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F μ S)
  Measure.count (sLocalClassHaar F S ν))

set_option maxHeartbeats 1300000 in
include hν in
/-- Membership in the global principal-value range reflects back to the
smaller stage on the original character component. -/
theorem sLocalHomogeneousThetaToGlobal_mem_principalValue_range_iff (W : Finset S)
    (q : SLocalHomogeneousThetaQuotient F S ν (sLocalNormOneCharacterOfGlobal F ω S hS hω)) :
    sLocalHomogeneousThetaToGlobal F η ω S hS hω ν q ∈
      range (fun g : GlobalBruhat F ↦
        (globalIdelicZetaComponentKernel F η ω).mkQ
          (globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) g)) ↔
    q ∈ (sLocalFiniteNonzeroTestSubspace F S W).map
      (sLocalHomogeneousThetaKernel F S ν (sLocalNormOneCharacterOfGlobal F ω S hS hω)).mkQ := by
  classical
  constructor
  · rintro ⟨g, hg⟩
    let σ := sLocalNormOneCharacterOfGlobal F ω S hS hω
    let M := sLocalHomogeneousThetaKernel F S ν σ
    obtain ⟨f, rfl⟩ := M.mkQ_surjective q
    obtain ⟨A, a, ha⟩ := globalBruhat_exhausted F g
    obtain ⟨B, hB⟩ := sIdeleClass_eventually_surjective F
    let T := (S ∪ A) ∪ B
    have hST : S ⊆ T := Finset.subset_union_left.trans Finset.subset_union_left
    have hAT : A ⊆ T := Finset.subset_union_right.trans Finset.subset_union_left
    have hT := hB T Finset.subset_union_right
    have hωT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))) := by
      apply (mem_sUnramified_iff F T _).mpr
      intro v hv u
      exact (mem_sUnramified_iff F S _).mp hω v (fun h ↦ hv (hST h)) u
    letI : (productHaar F μ T).IsHaarMeasure :=
      sLocalZetaProductMeasure_isHaar F T (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
    obtain ⟨νT, hνT, hweil⟩ := sLocalClassHaar_exists_weil F T (productHaar F μ T)
    letI := hνT
    let τ := sLocalNormOneCharacterOfGlobal F ω T hT hωT
    let MT := sLocalHomogeneousThetaKernel F T νT τ
    let e : S ↪ T := ⟨fun v ↦ ⟨v.val, hST v.property⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun w : T ↦ w.val) h)⟩
    let b := sLocalBruhatTransition F hAT a
    let y := sLocalWeilPrincipalValues F T (W.map e) b
    have hb : b.val = g := ha
    have hsets : (W.map e).map (⟨Subtype.val, Subtype.val_injective⟩ : T ↪ _) =
        W.map (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ _) := by
      rw [Finset.map_map]
      rfl
    have hy : y.val = globalWeilPrincipalValues F (W.map ⟨Subtype.val, Subtype.val_injective⟩) g := by
      have he := globalWeilPrincipalValues_stage F T (W.map e) b
      rw [hsets, hb] at he
      exact he.symm
    have hEq : MT.mkQ y = MT.mkQ (sLocalBruhatTransition F hST f) := by
      apply (sLocalHomogeneousThetaToGlobal_isClosedEmbedding F η ω T hT hωT νT).injective
      rw [sLocalHomogeneousThetaToGlobal_mk_representative, sLocalHomogeneousThetaToGlobal_mk_representative, hy]
      have hf := sLocalHomogeneousThetaToGlobal_mk_representative F η ω S hS hω ν f
      exact hg.trans hf
    have hm : MT.mkQ (sLocalBruhatTransition F hST f) ∈
        (sLocalFiniteNonzeroTestSubspace F T (W.map e)).map MT.mkQ := by
      refine ⟨y, ?_, hEq⟩
      rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
      exact ⟨b, rfl⟩
    have hlarge := (sLocal_mk_mem_selected_finiteImage_iff_poleBound F T (fun v ↦ μ v.val)
      νT hweil τ (W.map e) (sLocalBruhatTransition F hST f)).mp hm
    apply (sLocal_mk_mem_selected_finiteImage_iff_poleBound F S (fun v ↦ μ v.val) ν hν σ W f).mpr
    intro c
    exact (sLocalSelectedPoleBound_global_pad_iff F S ω hS hω μ hST hT hωT W f c).mpr (hlarge c)
  · exact sLocalHomogeneousThetaToGlobal_mem_principalValue_range F η ω S hS hω ν W q

end Reflection

/-- The zero test satisfies all finite lower bounds on the order of
its continued global zeta component. An exact finite order excludes it. -/
theorem globalZetaContinued_zero_test_order
    (νG : Measure (normOneIdeleClass F)) (χ : IdeleQuasiCharacter F) (κ c : ℂ) :
    meromorphicOrderAt (globalZetaContinued F νG 0 χ κ) c = ⊤ := by
  have hθ (q : IdeleClass F) : adelicTheta F (fun _ ↦ 0) q = 0 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [adelicTheta, thetaOnIdeles, thetaSummand, Quotient.lift_mk, tsum_zero]
  have hu (ψ : IdeleQuasiCharacter F) (z : ℂ) : thetaZetaUpper F νG 0 ψ z = 0 := by
    unfold thetaZetaUpper
    simp only [map_zero]
    change (∫ q in {q : IdeleClass F | 1 ≤ ideleClassNorm F q},
        adelicTheta F (fun _ ↦ 0) q * (ideleNormTwist F ψ z q : ℂ) ∂globalClassMeasure F νG) = 0
    simp only [hθ, zero_mul, integral_zero]
  have h : globalZetaContinued F νG 0 χ κ = fun _ ↦ 0 := by
    funext z
    simp only [globalZetaContinued, map_zero, hu]
    change (0 : ℂ) + 0 + _ * 0 / _ - _ * 0 / _ = 0
    simp
  rw [h, meromorphicOrderAt_const, ite_eq_left rfl]

end

end Masullo
