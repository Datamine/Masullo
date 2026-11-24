import AdelicWeilCoordinateCovariance
import SLocalBruhatFiniteTensor
import PrintedComplexWeilReference

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev L (v : Place F) := v.adicCompletion F
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev K := normOneIdeleClass F
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev FT (S : Finset (Place F)) (w : S) := locallyConstantTests (L F w.val)
private abbrev Test (S : Finset (Place F)) := locallyConstantTests (∀ w : S, L F w.val)

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
local instance : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (L F v) := borel _
local instance (v : Place F) : BorelSpace (L F v) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (L F v)ˣ := borel _
local instance (v : Place F) : BorelSpace (L F v)ˣ := ⟨rfl⟩
local instance (v : Place F) : LocallyCompactSpace (L F v) := finitePlace_locallyCompact F v
local instance (v : Place F) : SecondCountableTopology (L F v) := finitePlace_secondCountable F v
local instance (v : Place F) : LocallyCompactSpace (L F v)ˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
local instance (v : Place F) : SecondCountableTopology (L F v)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
private abbrev μ (v : Place F) := finitePlaceMultiplicativeTamagawa F v
local instance (v : Place F) : (μ F v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar F v
local instance (v : Place F) : SigmaFinite (μ F v) := inferInstance
local instance : (globalIdeleTamagawa F).IsHaarMeasure := globalIdeleTamagawa_isHaar F

private theorem evaluation_factorizes_of_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} (P : (∀ i, X i) → ℂ) (r : ∀ i, X i) (N : ∀ i, X i → ℂ)
    (h : ∀ k i, P k = P (update k i (r i)) * N i (k i)) (k : ∀ i, X i) :
    P k = P r * ∏ i, N i (k i) := by
  have hs (s : Finset ι) (f : ∀ i, X i) :
      P f = P (fun i => if i ∈ s then r i else f i) * ∏ i ∈ s, N i (f i) := by
    induction s using Finset.induction_on generalizing f with
    | empty => simp
    | @insert v s hv ih =>
      let f' := update f v (r v)
      have hf (i : ι) (his : i ∈ s) : f' i = f i := by
        have hne : i ≠ v := by
          rintro rfl
          exact hv his
        exact update_of_ne hne _ _
      have hreplace : (fun i => if i ∈ s then r i else f' i) =
          fun i => if i ∈ insert v s then r i else f i := by
        ext i
        by_cases hiv : i = v
        · subst i
          simp [hv, f']
        · by_cases his : i ∈ s
          · simp [his]
          · simp [hiv, his, f']
      rw [h f v]
      change P f' * N v (f v) = _
      rw [ih f', hreplace, Finset.prod_insert hv]
      rw [Finset.prod_congr rfl (fun i hi => congrArg (N i) (hf i hi)), mul_assoc, mul_comm (∏ i ∈ s, N i (f i))]
  simpa using hs Finset.univ k

variable (S : Finset (Place F)) (ω : PontryaginDual (K F))
    (hS : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev τ := sLocalNormOneCharacterOfGlobal F ω S hS hu
private abbrev χ (v : S) := sLocalFiniteZetaPhases F S (τ F S ω hS hu) v
private abbrev a := sLocalRealArchParameters F S (τ F S ω hS hu)
private abbrev j := sLocalComplexArchParameters F S (τ F S ω hS hu)

private def finiteWeilReference (v : S) : FT F S v := finiteWeilNormalizedTest F v.val (χ F S ω hS hu v)

private def stageWeilReference : E F S :=
  sLocalBruhatPure F S
    (mixedWeilTest F (mixedWeilRealReference F (a F S ω hS hu))
      (mixedWeilComplexReference F (j F S ω hS hu)))
    (locallyConstantTestPiProduct (finiteWeilReference F S ω hS hu))

private theorem stageWeilFactor_eval (v : S) (k : ∀ w : S, FT F S w) (y : FT F S v)
    (x : ∀ w : S, L F w.val) :
    (locallyConstantTestPiProduct (update k v y)).val x =
      y.val (x v) * ∏ w ∈ Finset.univ.erase v, (k w).val (x w) := by
  rw [locallyConstantTestPiProduct_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v), update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [update_of_ne (Finset.mem_erase.mp hw).1]

private def stageWeilFiniteSlice (v : S) (φ : Arch F) (k : ∀ w : S, FT F S w) :
    FT F S v →ₗ[ℂ] GlobalBruhat F :=
  (E F S).subtype.comp ((sLocalBruhatPure F S φ).comp
    { toFun := fun y => locallyConstantTestPiProduct (update k v y)
      map_add' := by
        intro y b
        apply Subtype.ext
        funext x
        change (locallyConstantTestPiProduct (update k v (y + b))).val x =
          (locallyConstantTestPiProduct (update k v y)).val x +
          (locallyConstantTestPiProduct (update k v b)).val x
        simp_rw [stageWeilFactor_eval F S]
        exact add_mul _ _ _
      map_smul' := by
        intro c y
        rw [RingHom.id_apply]
        apply Subtype.ext
        funext x
        change (locallyConstantTestPiProduct (update k v (c • y))).val x =
          c * (locallyConstantTestPiProduct (update k v y)).val x
        simp_rw [stageWeilFactor_eval F S]
        exact mul_assoc _ _ _ })

private theorem stageWeil_finiteRestriction_eval
    (σ : PontryaginDual (SLocalThetaNormOne F S)) (z : ℂ)
    (T : StrongDual ℂ (GlobalBruhat F)) (φ : Arch F)
    (hT : ∀ v u (f : ∀ w : S, FT F S w),
      T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
        (update f v (locallyConstantTestTranslate _ u (f v))))).val =
      ((sLocalFiniteZetaPhases F S σ v u : ℂ) * finiteZetaWeight F v.val z u) *
        T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct f)).val)
    (k : ∀ w : S, FT F S w) :
    T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val =
      T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct (fun v => finiteWeilNormalizedTest F v.val (sLocalFiniteZetaPhases F S σ v)))).val *
        ∏ v : S, finiteWeilNormalizedDistribution F v.val (μ F v.val) (sLocalFiniteZetaPhases F S σ v) z (k v) := by
  refine evaluation_factorizes_of_update
    (fun g => T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)).val)
    (fun v => finiteWeilNormalizedTest F v.val (sLocalFiniteZetaPhases F S σ v))
    (fun v => finiteWeilNormalizedDistribution F v.val (μ F v.val) (sLocalFiniteZetaPhases F S σ v) z) ?_ k
  intro f v
  letI : TopologicalSpace (FT F S v) := finestLocallyConvexTopology _
  let U : StrongDual ℂ (FT F S v) := T.comp
    ⟨stageWeilFiniteSlice F S v φ f, finest_linear_continuous _⟩
  have hU (u : (L F v.val)ˣ) (b : FT F S v) :
      U (locallyConstantTestTranslate _ u b) =
        ((sLocalFiniteZetaPhases F S σ v u : ℂ) * finiteZetaWeight F v.val z u) * U b := by
    have h := hT v u (update f v b)
    change T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
      (update f v (locallyConstantTestTranslate _ u b)))).val = _
    rwa [update_self, update_idem] at h
  have h := DFunLike.congr_fun
    (finiteWeilEigen_distribution_eq F v.val (μ F v.val) (sLocalFiniteZetaPhases F S σ v) z U hU) (f v)
  change U (f v) = U (finiteWeilNormalizedTest F v.val (sLocalFiniteZetaPhases F S σ v)) *
    finiteWeilNormalizedDistribution F v.val (μ F v.val) (sLocalFiniteZetaPhases F S σ v) z (f v) at h
  change T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct (update f v (f v)))).val = _ at h
  rwa [update_eq_self] at h

private theorem globalWeil_finiteRestriction_eval (z : ℂ)
    (T : StrongDual ℂ (GlobalBruhat F)) (hT : IsGlobalWeilEigen F ω z T)
    (φ : Arch F) (k : ∀ w : S, FT F S w) :
    T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val =
      T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct (finiteWeilReference F S ω hS hu))).val *
        ∏ v : S, finiteWeilNormalizedDistribution F v.val (μ F v.val) (χ F S ω hS hu v) z (k v) := by
  exact stageWeil_finiteRestriction_eval F S (τ F S ω hS hu) z T φ
    (fun v u f => globalWeil_finiteRestriction_covariance F S ω hS hu z T hT v u φ f) k

/-- Every global eigenfunctional has the exact normalized local tensor
pairings on an admissible stage, scaled by its value at the stage reference. -/
theorem globalWeil_stageSeparated_eval (z : ℂ)
    (T : StrongDual ℂ (GlobalBruhat F)) (hT : IsGlobalWeilEigen F ω z T)
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) (k : ∀ v : S, FT F S v) :
    T (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)).val =
      T (stageWeilReference F S ω hS hu).val *
        (sLocalNormalizedArchWeilTensor F S (τ F S ω hS hu) f g z *
          ∏ v : S, finiteWeilNormalizedDistribution F v.val (μ F v.val) (χ F S ω hS hu v) z (k v)) := by
  rw [globalWeil_archRestriction_eval F S ω hS hu z T hT,
    globalWeil_finiteRestriction_eval F S ω hS hu z T hT]
  unfold stageWeilReference
  ring

private theorem globalWeil_eqOnStage_of_separated (T U : StrongDual ℂ (GlobalBruhat F))
    (he : ∀ f g k, T (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)).val =
      U (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)).val)
    (x : E F S) : T x.val = U x.val := by
  have hp (φ : Arch F) (ψ : Test F S) :
      T (sLocalBruhatPure F S φ ψ).val = U (sLocalBruhatPure F S φ ψ).val := by
    let L := (E F S).subtype.comp (sLocalBruhatPure F S φ)
    have h : T.toLinearMap.comp L = U.toLinearMap.comp L := by
      apply LinearMap.ext_on locallyConstantTest_span_piProduct
      rintro _ ⟨k, rfl⟩
      let ψ := locallyConstantTestPiProduct k
      let A : Arch F →L[ℂ] GlobalBruhat F :=
        ⟨GlobalBruhat.pure F (insertFinite F S ψ), GlobalBruhat.pure_continuous F _⟩
      have he' : T.comp A = U.comp A :=
        mixedWeilFunctional_eq_of_separated F _ _ (fun f g => he f g k)
      exact DFunLike.congr_fun he' φ
    exact DFunLike.congr_fun h ψ
  letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    change T (sLocalBruhatPure F S φ ψ).val = U (sLocalBruhatPure F S φ ψ).val
    exact hp φ ψ
  | add x y hx hy =>
    rw [map_add, Submodule.coe_add, map_add, map_add, hx, hy]

private theorem stageWeilReference_normalized (z : ℂ) :
    normalizedStageWeilMellin F (μ F) ω S hS hu (stageWeilReference F S ω hS hu) z = 1 := by
  unfold stageWeilReference
  rw [normalizedStageWeilMellin_separated_eval F S (μ F) ω hS hu _ _ _
    (mixedWeilTest_apply F _ _)]
  simp only [finiteWeilReference, finiteWeilNormalizedDistribution_reference, Finset.prod_const_one, mul_one]
  change (∏ v : R F, realWeilNormalizedFamily (a F S ω hS hu v).2 (z + (a F S ω hS hu v).1)
      (mixedWeilRealReference F (a F S ω hS hu) v)) *
    (∏ v : C F, complexWeilNormalizedFamily (j F S ω hS hu v).2 (z + (j F S ω hS hu v).1)
      (mixedWeilComplexReference F (j F S ω hS hu) v)) = 1
  have hR (v : R F) := (realGammaNormalized_distribution (a F S ω hS hu v).2).choose_spec.choose_spec.2.2.1
    (z + (a F S ω hS hu v).1)
  have hC (v : C F) := (complexGammaNormalized_distribution (j F S ω hS hu v).2).choose_spec.choose_spec.2.2.1
    (z + (j F S ω hS hu v).1)
  simp only [mixedWeilRealReference, mixedWeilComplexReference, realWeilNormalizedFamily,
    complexWeilNormalizedFamily, hR, hC, Finset.prod_const_one, mul_one]

private theorem globalWeil_eqOnStage (z : ℂ) (T N : StrongDual ℂ (GlobalBruhat F))
    (hT : IsGlobalWeilEigen F ω z T)
    (hN : ∀ f : E F S, N f.val = normalizedStageWeilMellin F (μ F) ω S hS hu f z)
    (f : E F S) :
    T f.val = T (stageWeilReference F S ω hS hu).val * N f.val := by
  let U := T (stageWeilReference F S ω hS hu).val • N
  change T f.val = U f.val
  apply globalWeil_eqOnStage_of_separated F S T U _ f
  intro b c k
  change _ = T (stageWeilReference F S ω hS hu).val * N _
  rw [hN, normalizedStageWeilMellin_separated_eval F S (μ F) ω hS hu _ _ _
    (mixedWeilTest_apply F b c), globalWeil_stageSeparated_eval F S ω hS hu z T hT]

private theorem globalWeil_eq_normalized (z : ℂ)
    (T N : StrongDual ℂ (GlobalBruhat F)) (hT : IsGlobalWeilEigen F ω z T)
    (hN : ∀ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
      (huU : globalNormOneCharacter F ω ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))
      (f : E F U), N f.val = normalizedStageWeilMellin F (μ F) ω U hU huU f z) :
    T = T (stageWeilReference F S ω hS hu).val • N := by
  let ref := stageWeilReference F S ω hS hu
  ext f
  obtain ⟨V, g, hg⟩ := globalBruhat_exhausted F f
  let U := S ∪ V
  have hSU : S ⊆ U := Finset.subset_union_left
  have hVU : V ⊆ U := Finset.subset_union_right
  have hU : Surjective (sIdeleClassInclusion F U) := by
    intro x
    obtain ⟨y, rfl⟩ := hS x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk (sIdeleTransition F hSU b), rfl⟩
  have huU : globalNormOneCharacter F ω ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))) :=
    (mem_sUnramified_iff F U _).mpr fun v hv u =>
      (mem_sUnramified_iff F S _).mp hu v (fun h => hv (hSU h)) u
  have h := globalWeil_eqOnStage F U ω hU huU z T N hT (hN U hU huU)
  have href : N ref.val = 1 := (hN S hS hu ref).trans (stageWeilReference_normalized F S ω hS hu z)
  have hscale := h (sLocalBruhatTransition F hSU ref)
  change T ref.val = T (stageWeilReference F U ω hU huU).val * N ref.val at hscale
  rw [href, mul_one] at hscale
  have hval := h (sLocalBruhatTransition F hVU g)
  change T g.val = T (stageWeilReference F U ω hU huU).val * N g.val at hval
  rw [← hscale] at hval
  change T f = T ref.val * N f
  exact hg ▸ hval

/-- The eigenspace of an actual quasi-character in the full adelic Schwartz–Bruhat dual. -/
def adelicWeilEigenspace (c : IdeleQuasiCharacter F) :
    Submodule ℂ (StrongDual ℂ (GlobalBruhat F)) where
  carrier := {T | ∀ a f, T (GlobalBruhat.leftTranslate F a f) =
    (c (ideleClassMap F a) : ℂ) * T f}
  zero_mem' := by intro a f; simp
  add_mem' {T U} hT hU := by
    intro a f
    change T (GlobalBruhat.leftTranslate F a f) + U (GlobalBruhat.leftTranslate F a f) =
      (c (ideleClassMap F a) : ℂ) * (T f + U f)
    rw [hT a f, hU a f, mul_add]
  smul_mem' b T hT := by
    intro a f
    change b * T (GlobalBruhat.leftTranslate F a f) =
      (c (ideleClassMap F a) : ℂ) * (b * T f)
    rw [hT a f, mul_left_comm]

abbrev globalWeilEigenspace (ω : PontryaginDual (K F)) (z : ℂ) :=
  adelicWeilEigenspace F (ideleNormTwist F (compactIdeleClassCharacter F ω) z)

include hS hu in
private theorem globalWeilEigenspace_referenceEquiv (z : ℂ)
    (N : StrongDual ℂ (GlobalBruhat F)) (hcov : IsGlobalWeilEigen F ω z N)
    (hN : ∀ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
      (huU : globalNormOneCharacter F ω ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))
      (f : E F U), N f.val = normalizedStageWeilMellin F (μ F) ω U hU huU f z) :
    Nonempty (globalWeilEigenspace F ω z ≃ₗ[ℂ] ℂ) := by
  let ref := (stageWeilReference F S ω hS hu).val
  let v : globalWeilEigenspace F ω z := ⟨N, hcov⟩
  have href : N ref = 1 := (hN S hS hu _).trans (stageWeilReference_normalized F S ω hS hu z)
  refine ⟨{ toFun := fun T => T.val ref
            invFun := fun c => c • v
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro T
    apply Subtype.ext
    exact (globalWeil_eq_normalized F S ω hS hu z T.val N T.property hN).symm
  · intro c
    change c * N ref = c
    rw [href, mul_one]

/-- The adelic eigenspace at every point of every norm-one component has dimension one. -/
theorem globalWeilEigenspace_finrank (ω : PontryaginDual (K F)) (z : ℂ) :
    Module.finrank ℂ (globalWeilEigenspace F ω z) = 1 := by
  obtain ⟨B, hB⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hBsur, hBunr⟩ := hB B Subset.rfl
  obtain ⟨ν, hν, hνW, _⟩ := globalIdeleTamagawa_exists_weil F
  letI := hν
  obtain ⟨_, _, Δ, _, _, _, _, _, _, hcov, hstage⟩ :=
    exists_globalWeilTamagawa_eigenfamily F ω B hBsur hBunr ν hνW
  obtain ⟨e⟩ := globalWeilEigenspace_referenceEquiv F B ω hBsur hBunr z (Δ z)
    (fun a f => hcov a f z) (fun U hU huU f => hstage U hU huU f z)
  exact e.finrank_eq.trans (Module.finrank_self ℂ)

/-- The global dimension assertion of Theorem 3.4.3.3 for every
continuous quasi-character of the idele class group. -/
theorem adelicWeilEigenspace_finrank (c : IdeleQuasiCharacter F) :
    Module.finrank ℂ (adelicWeilEigenspace F c) = 1 := by
  obtain ⟨ω, z, rfl, _⟩ := ideleClassCharacter_existsUnique_compact_twist F c
  exact globalWeilEigenspace_finrank F ω z

private def complexReferenceScale : ℂ := (2 : ℂ) ^ Fintype.card (C F)

/-- The global reference tensor with the scalar of Definition 3.4.3.2 and
the corrected angular conjugation in its complex factors. -/
def correctedGlobalWeilGaussian : E F S :=
  sLocalBruhatPure F S
    (mixedWeilTest F (mixedWeilRealReference F (a F S ω hS hu))
      (fun v => correctedComplexWeilReference (j F S ω hS hu v).2))
    (locallyConstantTestPiProduct (finiteWeilReference F S ω hS hu))

private theorem correctedGlobalWeilGaussian_stage_eval (z : ℂ) :
    normalizedStageWeilMellin F (μ F) ω S hS hu (correctedGlobalWeilGaussian F S ω hS hu) z =
      (complexReferenceScale F)⁻¹ := by
  unfold correctedGlobalWeilGaussian
  rw [normalizedStageWeilMellin_separated_eval F S (μ F) ω hS hu _ _ _
    (mixedWeilTest_apply F _ _)]
  simp only [finiteWeilReference, finiteWeilNormalizedDistribution_reference, Finset.prod_const_one, mul_one]
  change (∏ v : R F, realWeilNormalizedFamily (a F S ω hS hu v).2 (z + (a F S ω hS hu v).1)
      (mixedWeilRealReference F (a F S ω hS hu) v)) *
    (∏ v : C F, complexWeilNormalizedFamily (j F S ω hS hu v).2 (z + (j F S ω hS hu v).1)
      (correctedComplexWeilReference (j F S ω hS hu v).2)) = _
  have hR (v : R F) : realWeilNormalizedFamily (a F S ω hS hu v).2 (z + (a F S ω hS hu v).1)
      (mixedWeilRealReference F (a F S ω hS hu) v) = 1 :=
    (realGammaNormalized_distribution (a F S ω hS hu v).2).choose_spec.choose_spec.2.2.1 _
  have hC (v : C F) : complexWeilNormalizedFamily (j F S ω hS hu v).2 (z + (j F S ω hS hu v).1)
      (correctedComplexWeilReference (j F S ω hS hu v).2) = (2 : ℂ)⁻¹ := by
    change complexWeilNormalizedFamily (j F S ω hS hu v).2 (z + (j F S ω hS hu v).1)
      ((2 : ℂ)⁻¹ • (complexGammaNormalized_distribution (j F S ω hS hu v).2).choose) = _
    rw [map_smul, smul_eq_mul]
    exact mul_one _ |>.symm.trans (congrArg ((2 : ℂ)⁻¹ * ·)
      ((complexGammaNormalized_distribution (j F S ω hS hu v).2).choose_spec.choose_spec.2.2.1 _).symm) |>.symm
  simp only [hR, hC, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ,
    complexReferenceScale, inv_pow]

set_option maxHeartbeats 1800000 in
/-- The corrected global formula of Theorem 3.4.3.3, with the exact
Gaussian scalar, local tensor evaluations, and meromorphic factorization. -/
theorem exists_globalWeil_correctedGaussian_family
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) (globalIdeleTamagawa F) Measure.count
      (globalClassMeasure F ν)) :
    ∃ (L : ℂ → ℂ) (Δ : ℂ → StrongDual ℂ (GlobalBruhat F)),
      EqOn L (fun z => (complexReferenceScale F)⁻¹ *
        (globalWeilTamagawaScale F * globalCompletedHeckeEuler F ω S hS hu z)) {z | 1 < z.re} ∧
      MeromorphicOn L univ ∧ Differentiable ℂ Δ ∧
      (∀ z, Δ z (correctedGlobalWeilGaussian F S ω hS hu).val = 1) ∧
      (∀ z, IsGlobalWeilEigen F ω z (Δ z)) ∧
      (∀ z, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] z] fun w => L w • Δ w) ∧
      (∀ z, globalZetaContinued F ν (correctedGlobalWeilGaussian F S ω hS hu).val
        (compactIdeleClassCharacter F ω) 0 =ᶠ[𝓝[≠] z] L) ∧
      ∀ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
        (huU : globalNormOneCharacter F ω ∈ (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))
        (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) (k : ∀ v : U, FT F U v) (z : ℂ),
        Δ z (sLocalBruhatPure F U (mixedWeilTest F f g) (locallyConstantTestPiProduct k)).val =
          ((∏ v, realWeilNormalizedFamily (a F U ω hU huU v).2 (z + (a F U ω hU huU v).1) (f v)) *
           ∏ v, correctedComplexWeilNormalizedFamily (j F U ω hU huU v).2
              (z + (j F U ω hU huU v).1) (g v)) *
           ∏ v, finiteWeilNormalizedDistribution F v.val (μ F v.val) (χ F U ω hU huU v) z (k v) := by
  obtain ⟨_, L, Δ, hE, hL, hD, _, hfac, _, hcov, hstage⟩ :=
    exists_globalWeilTamagawa_eigenfamily F ω S hS hu ν hν
  let b := complexReferenceScale F
  have hb : b ≠ 0 := pow_ne_zero _ (by norm_num)
  let L' (z : ℂ) := b⁻¹ * L z
  let M := b • ContinuousLinearMap.id ℂ (StrongDual ℂ (GlobalBruhat F))
  let Δ' (z : ℂ) := b • Δ z
  have hD' : Differentiable ℂ Δ' := by
    change Differentiable ℂ (M ∘ Δ)
    intro z
    obtain ⟨D, hDz⟩ := hD z
    refine ⟨M.comp D, HasFDerivAt.of_isLittleOTVS ?_⟩
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using M.isBigOTVS_comp.trans_isLittleOTVS hDz.isLittleOTVS
  have hG (z : ℂ) : Δ' z (correctedGlobalWeilGaussian F S ω hS hu).val = 1 := by
    change b * Δ z _ = 1
    rw [hstage S hS hu, correctedGlobalWeilGaussian_stage_eval F S ω hS hu z, mul_inv_cancel₀ hb]
  have hfac' (c : ℂ) : globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] c] fun w => L' w • Δ' w := by
    filter_upwards [hfac c] with z hz
    rw [hz]
    apply LinearMap.ext
    intro f
    change L z * Δ z f = (b⁻¹ * L z) * (b * Δ z f)
    rw [mul_comm b⁻¹, mul_assoc, ← mul_assoc b⁻¹ b, inv_mul_cancel₀ hb, one_mul]
  refine ⟨L', Δ', fun z hz => congrArg (b⁻¹ * ·) (hE hz),
    fun z hz => (MeromorphicAt.const b⁻¹ z).mul (hL z hz), hD', hG, ?_, hfac', ?_, ?_⟩
  · intro z u φ
    change b * Δ z (GlobalBruhat.leftTranslate F u φ) = globalWeilWeight F ω z u * (b * Δ z φ)
    rw [hcov, mul_left_comm]
    rfl
  · intro c
    filter_upwards [hfac' c] with z hz
    have he := DFunLike.congr_fun hz (correctedGlobalWeilGaussian F S ω hS hu).val
    change globalContinuedMellinEval F ν ω z _ = L' z * Δ' z _ at he
    rw [hG, mul_one] at he
    exact (globalContinuedMellinEval_apply F ν ω z _).symm.trans he
  · intro U hU huU f g k z
    change b * Δ z _ = _
    rw [hstage U hU huU, normalizedStageWeilMellin_separated_eval F U (μ F) ω hU huU _ _ _
      (mixedWeilTest_apply F f g)]
    let X := ∏ v : R F, realWeilNormalizedFamily (a F U ω hU huU v).2
      (z + (a F U ω hU huU v).1) (f v)
    let Y (v : C F) : ℂ := complexWeilNormalizedFamily (j F U ω hU huU v).2
      (z + (j F U ω hU huU v).1) (g v)
    let Z := ∏ v : U, finiteWeilNormalizedDistribution F v.val (μ F v.val) (χ F U ω hU huU v) z (k v)
    change b * (X * (∏ v, Y v) * Z) = (X * (∏ v, (2 : ℂ) * Y v)) * Z
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    change b * (X * (∏ v, Y v) * Z) = X * (b * (∏ v, Y v)) * Z
    ring

private def extendStageWeil (T : StrongDual ℂ (E F S)) : StrongDual ℂ (GlobalBruhat F) :=
  T.comp ((sLocalBruhatProjection F S).codRestrict (E F S) (sLocalBruhatProjection_mem F S))

@[simp] private theorem extendStageWeil_apply (T : StrongDual ℂ (E F S)) (f : E F S) :
    extendStageWeil F S T f.val = T f := by
  apply congrArg T
  exact Subtype.ext (sLocalBruhatProjection_fixes F S f.val f.property)

/-- The real, complex and selected finite tensors determine every continuous
functional on the actual S-local Schwartz–Bruhat space. -/
theorem sLocalWeilFunctional_eq_of_separated (T U : StrongDual ℂ (E F S))
    (he : ∀ f g k,
      T (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)) =
        U (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k))) : T = U := by
  ext f
  simpa only [extendStageWeil_apply] using globalWeil_eqOnStage_of_separated F S
    (extendStageWeil F S T) (extendStageWeil F S U)
      (fun f g k => by simpa only [extendStageWeil_apply] using he f g k) f

/-- A reference with each archimedean Mellin evaluation normalized to one
for the full Deligne Gamma factor, together with the finite reference tests. -/
def sLocalWeilUnitTensor (σ : PontryaginDual (SLocalThetaNormOne F S)) : E F S :=
  sLocalBruhatPure F S (mixedWeilTest F (mixedWeilRealReference F (sLocalRealArchParameters F S σ))
    (mixedWeilComplexReference F (sLocalComplexArchParameters F S σ)))
    (locallyConstantTestPiProduct (fun v => finiteWeilNormalizedTest F v.val (sLocalFiniteZetaPhases F S σ v)))

/-- Every S-local eigendistribution has the prescribed product pairings on
separated tests, up to its value at the common reference. -/
theorem sLocalWeil_stageSeparated_eval
    (σ : PontryaginDual (SLocalThetaNormOne F S)) (z : ℂ) (T : StrongDual ℂ (E F S))
    (hT : ∀ g f, T (sLocalBruhatLeftTranslate F S g f) =
      sLocalZetaWeight F S σ z (QuotientGroup.mk g) * T f)
    (f : R F → 𝓢(ℝ, ℂ)) (g : C F → 𝓢(ℂ, ℂ)) (k : ∀ v : S, FT F S v) :
    T (sLocalBruhatPure F S (mixedWeilTest F f g) (locallyConstantTestPiProduct k)) =
      T (sLocalWeilUnitTensor F S σ) *
        (sLocalNormalizedArchWeilTensor F S σ f g z *
          ∏ v, finiteWeilNormalizedDistribution F v.val (μ F v.val) (sLocalFiniteZetaPhases F S σ v) z (k v)) := by
  let φ := mixedWeilTest F (mixedWeilRealReference F (sLocalRealArchParameters F S σ))
    (mixedWeilComplexReference F (sLocalComplexArchParameters F S σ))
  have he := stageWeil_finiteRestriction_eval F S σ z (extendStageWeil F S T) φ
    (fun v u f => by simpa only [extendStageWeil_apply] using
      sLocalWeil_finiteRestriction_covariance F S σ z T hT v u φ f) k
  simp only [extendStageWeil_apply] at he
  rw [sLocalWeil_archRestriction_eval F S σ z T hT]
  change T (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)) * _ = _
  rw [he]
  unfold sLocalWeilUnitTensor
  ring

end
end Masullo
