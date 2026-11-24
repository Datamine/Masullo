import AdelicDerivatives
import InductiveTensorTopology
import Mathlib.LinearAlgebra.TensorProduct.Basis
import LocallyConstantTests
import SLocalAdditive
import StrictInductiveBounds

open Bornology Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical ContDiff NumberField RestrictedProduct SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F
private abbrev Coordinates (S : Finset (Place F)) := (v : S) → v.val.adicCompletion F

private def finitePad (S : Finset (Place F)) (x : Coordinates F S) : FinAdeles F :=
  finiteCoordinateSplit F S (x, 0)

private def finiteSelected (S : Finset (Place F)) (x : FinAdeles F) : Coordinates F S :=
  (finiteCoordinateSplit F S).symm x |>.1

private theorem finiteSelected_apply (S : Finset (Place F)) (x : FinAdeles F) (v : S) :
    finiteSelected F S x v = x v.val := by
  have he := congrArg (fun a : FinAdeles F => a v.val)
    ((finiteCoordinateSplit F S).apply_symm_apply x)
  change finiteCoordinateSplit F S ((finiteCoordinateSplit F S).symm x) v.val = _ at he
  rw [finiteCoordinateSplit_apply, dite_eq_left v.property] at he
  exact he

private theorem finitePad_apply (S : Finset (Place F)) (x : Coordinates F S) (v : Place F) :
    finitePad F S x v = if h : v ∈ S then x ⟨v, h⟩ else 0 := by
  unfold finitePad
  rw [finiteCoordinateSplit_apply]
  split <;> rfl

private theorem finitePad_integralOutside (S T : Finset (Place F)) (x : Coordinates F T) :
    (∀ w ∉ S, finitePad F T x w ∈ w.adicCompletionIntegers F) ↔
      ∀ w : T, w.val ∉ S → x w ∈ w.val.adicCompletionIntegers F := by
  constructor
  · intro h w hw
    specialize h w.val hw
    rwa [finitePad_apply, dite_eq_left w.property] at h
  · intro h w hw
    rw [finitePad_apply]
    split_ifs with hT
    · exact h ⟨w, hT⟩ hw
    · exact zero_mem _

private theorem finiteSelected_pad (S : Finset (Place F)) (x : Coordinates F S) :
    finiteSelected F S (finitePad F S x) = x :=
  congrArg Prod.fst ((finiteCoordinateSplit F S).symm_apply_apply (x, 0))

private theorem compactSupport_finitePad (S : Finset (Place F)) {ψ : FinAdeles F → ℂ}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (ψ ∘ finitePad F S) := by
  letI : T2Space (FiniteAdeleTail F S) := (finiteProducts_locallyConstantTests_context F S).2.1
  have he : IsClosedEmbedding (fun x : Coordinates F S => (x, (0 : FiniteAdeleTail F S))) :=
    ⟨isEmbedding_prodMkLeft _, by
      convert isClosed_univ.prod (isClosed_singleton (x := (0 : FiniteAdeleTail F S))) using 1
      ext p
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨mem_univ _, rfl⟩
      · rintro ⟨_, hp⟩; exact ⟨p.1, Prod.ext rfl hp.symm⟩⟩
  exact hψ.comp_isClosedEmbedding ((finiteCoordinateSplit F S).toHomeomorph.isClosedEmbedding.comp he)

def restrictFiniteBruhat (S : Finset (Place F)) (ψ : FiniteBruhat F) :
    locallyConstantTests (Coordinates F S) :=
  ⟨ψ.toLocallyConstant ∘ finitePad F S,
    ψ.toLocallyConstant.isLocallyConstant.comp_continuous
      ((finiteCoordinateSplit F S).continuous.comp (continuous_id.prodMk continuous_const)),
    compactSupport_finitePad F S ψ.compactSupport⟩

private def integralTailIndicator (S : Finset (Place F)) :
    locallyConstantTests (FiniteAdeleTail F S) := by
  letI : T2Space (FiniteAdeleTail F S) := (finiteProducts_locallyConstantTests_context F S).2.1
  apply compactOpenIndicator
  refine ⟨(tailIntegralSubmonoid F S : Set (FiniteAdeleTail F S)), tailIntegralSubmonoid_compact F S, ?_⟩
  exact RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

private theorem integralTailIndicator_zero (S : Finset (Place F)) :
    (integralTailIndicator F S).val 0 = 1 := by
  change Set.indicator (tailIntegralSubmonoid F S : Set (FiniteAdeleTail F S))
    (fun _ => (1 : ℂ)) 0 = 1
  exact Set.indicator_of_mem (show (0 : FiniteAdeleTail F S) ∈ tailIntegralSubmonoid F S from
    fun _ => zero_mem _) _

/-- The finite test obtained by padding the selected coordinates with the
integer-ring indicator at every omitted place. -/
def insertFinite (S : Finset (Place F)) (ψ : locallyConstantTests (Coordinates F S)) :
    FiniteBruhat F := by
  let T := FiniteAdeleTail F S
  let e := (finiteCoordinateSplit F S).toHomeomorph
  let k := integralTailIndicator F S
  let f (x : Coordinates F S × T) : ℂ := ψ.val x.1 * k.val x.2
  have hloc : IsLocallyConstant f :=
    (ψ.property.1.comp_continuous continuous_fst).mul (k.property.1.comp_continuous continuous_snd)
  have hcomp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (ψ.property.2.prod k.property.2)
    intro x hx
    exact ⟨subset_tsupport ψ.val (fun h => hx (by simp [f, h])),
      subset_tsupport k.val (fun h => hx (by simp [f, h]))⟩
  exact ⟨⟨f ∘ e.symm, hloc.comp_continuous e.symm.continuous⟩,
    hcomp.comp_isClosedEmbedding e.symm.isClosedEmbedding⟩

private theorem insertFinite_apply (S : Finset (Place F))
    (ψ : locallyConstantTests (Coordinates F S)) (x : FinAdeles F) :
    (insertFinite F S ψ).toLocallyConstant x =
      ψ.val (finiteSelected F S x) *
        if ∀ v ∉ S, x v ∈ v.adicCompletionIntegers F then 1 else 0 := by
  have htail (v : {v : Place F // v ∉ S}) :
      ((finiteCoordinateSplit F S).symm x).2 v = x v.val := by
    have he := congrArg (fun a : FinAdeles F => a v.val)
      ((finiteCoordinateSplit F S).apply_symm_apply x)
    change finiteCoordinateSplit F S ((finiteCoordinateSplit F S).symm x) v.val = _ at he
    rwa [finiteCoordinateSplit_apply, dite_eq_right v.property] at he
  have he : ((finiteCoordinateSplit F S).symm x).2 ∈
      (tailIntegralSubmonoid F S : Set (FiniteAdeleTail F S)) ↔
      ∀ v ∉ S, x v ∈ v.adicCompletionIntegers F := by
    change (∀ v : {v : Place F // v ∉ S},
      ((finiteCoordinateSplit F S).symm x).2 v ∈ v.val.adicCompletionIntegers F) ↔ _
    simp_rw [htail, Subtype.forall]
  change ψ.val (finiteSelected F S x) * (tailIntegralSubmonoid F S : Set (FiniteAdeleTail F S)).indicator
    (fun _ => (1 : ℂ)) ((finiteCoordinateSplit F S).symm x).2 = _
  rw [Set.indicator_apply, he]

/-- The S-local tests embedded in global Schwartz–Bruhat space by insertion
of the indicator of the integral tail. -/
def sLocalBruhatImage (S : Finset (Place F)) : Submodule ℂ (GlobalBruhat F) :=
  Submodule.span ℂ {f | ∃ (ψ : locallyConstantTests (Coordinates F S))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)), GlobalBruhat.pure F (insertFinite F S ψ) φ = f}

/-- Insert an additive S-adele with zero coordinates off S. -/
def sLocalBruhatPad (S : Finset (Place F)) (x : SAdeles F S) : Adeles F :=
  (x.1, finitePad F S x.2)

theorem sLocalBruhatPad_finite (S : Finset (Place F)) (x : SAdeles F S) (v : S) :
    (sLocalBruhatPad F S x).2 v.val = x.2 v :=
  (finitePad_apply F S x.2 v.val).trans (dite_eq_left v.property)

theorem sLocalBruhatPad_mul_project (S : Finset (Place F)) (a : Adeles F) (x : SAdeles F S) :
    sLocalBruhatPad F S (sAdelesProjection F S a * x) = a * sLocalBruhatPad F S x := by
  change ((a.1 * x.1, finitePad F S ((sAdelesProjection F S a * x).2)) : Adeles F) =
    (a.1 * x.1, a.2 * finitePad F S x.2)
  congr 1
  apply DFunLike.ext
  intro v
  change finitePad F S ((sAdelesProjection F S a * x).2) v = a.2 v * finitePad F S x.2 v
  by_cases hv : v ∈ S
  · simp only [finitePad_apply, dite_eq_left hv]
    rfl
  · simp only [finitePad_apply, dite_eq_right hv, mul_zero]

/-- Restriction to the S-local adeles using zero in the complementary coordinates. -/
def sLocalBruhatRestriction (S : Finset (Place F)) :
    GlobalBruhat F →ₗ[ℂ] (SAdeles F S → ℂ) :=
  LinearMap.pi fun x => GlobalBruhat.evaluation F (sLocalBruhatPad F S x)

theorem sLocalBruhatRestriction_pure (S : Finset (Place F))
    (ψ : FiniteBruhat F) (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    sLocalBruhatRestriction F S (GlobalBruhat.pure F ψ φ) =
      fun x => φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * (restrictFiniteBruhat F S ψ).val x.2 :=
  rfl

theorem sLocalBruhatRestriction_continuous (S : Finset (Place F)) (f : GlobalBruhat F) :
    Continuous (sLocalBruhatRestriction F S f) := by
  change Continuous (fun x : SAdeles F S => (GlobalBruhat.algebraicEquiv F f).val
    (x.1, finitePad F S x.2))
  exact (bruhat_continuous F (GlobalBruhat.algebraicEquiv F f).property).comp
    (continuous_fst.prodMk ((finiteCoordinateSplit F S).continuous.comp
      (continuous_snd.prodMk continuous_const)))

theorem sLocalBruhat_derivative_mem (S : Finset (Place F)) (γ : Multiplicative ℝ →* Idele F)
    (hγ : Continuous γ) (f : GlobalBruhat F) (hf : f ∈ sLocalBruhatImage F S) :
    GlobalBruhat.derivative F γ hγ f ∈ sLocalBruhatImage F S := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, φ, rfl⟩ := hf
    change GlobalBruhat.derivativeLinear F γ hγ (GlobalBruhat.pure F (insertFinite F S ψ) φ) ∈ _
    rw [GlobalBruhat.derivativeLinear_pure]
    exact Submodule.subset_span ⟨ψ, _, rfl⟩
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

private def sProjectionFunction (S : Finset (Place F)) : (Adeles F → ℂ) →ₗ[ℂ] (Adeles F → ℂ) where
  toFun f a := f (a.1, finitePad F S (finiteSelected F S a.2)) *
    if ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F then 1 else 0
  map_add' f g := funext fun _ => add_mul _ _ _
  map_smul' c f := by
    funext a
    change (c * f _) * _ = c * (f _ * _)
    exact mul_assoc _ _ _

private theorem sProjectionFunction_pure (S : Finset (Place F))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F) :
    sProjectionFunction F S (bruhatTensor F φ ψ) =
      bruhatTensor F φ (insertFinite F S (restrictFiniteBruhat F S ψ)) := by
  funext a
  unfold sProjectionFunction
  simp only [LinearMap.coe_mk, AddHom.coe_mk, bruhatTensor, insertFinite_apply]
  rw [mul_assoc]
  rfl

private theorem sProjectionFunction_mem (S : Finset (Place F)) {f : Adeles F → ℂ}
    (hf : f ∈ bruhatSubmodule F) : sProjectionFunction F S f ∈ bruhatSubmodule F := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, ψ, rfl⟩ := hf
    rw [sProjectionFunction_pure]
    exact bruhatTensor_mem F _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul c f hf h => rw [map_smul]; exact Submodule.smul_mem _ _ h

/-- The global projection onto the S-local tests evaluates at zero in the tail,
then inserts the integral-tail indicator. -/
def sLocalBruhatProjection (S : Finset (Place F)) : GlobalBruhat F →L[ℂ] GlobalBruhat F := by
  let g := (sProjectionFunction F S).restrict (fun _ h => sProjectionFunction_mem F S h)
  let P := (GlobalBruhat.algebraicEquiv F).symm.toLinearMap.comp
    (g.comp (GlobalBruhat.algebraicEquiv F).toLinearMap)
  refine ⟨P, GlobalBruhat.continuous_of_pure F (PolynormableSpace.withSeminorms ℂ (GlobalBruhat F)) P ?_⟩
  intro ψ
  have he : (fun φ => P (GlobalBruhat.pure F ψ φ)) =
      GlobalBruhat.pure F (insertFinite F S (restrictFiniteBruhat F S ψ)) := by
    funext φ
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    exact sProjectionFunction_pure F S φ ψ
  rw [he]
  exact GlobalBruhat.pure_continuous F _


private theorem sLocalBruhatProjection_apply (S : Finset (Place F))
    (f : GlobalBruhat F) (a : Adeles F) :
    GlobalBruhat.evaluation F a (sLocalBruhatProjection F S f) =
      GlobalBruhat.evaluation F (a.1, finitePad F S (finiteSelected F S a.2)) f *
        if ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F then 1 else 0 := rfl

private theorem sLocalBruhatProjection_pure (S : Finset (Place F))
    (ψ : FiniteBruhat F) (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
    sLocalBruhatProjection F S (GlobalBruhat.pure F ψ φ) =
      GlobalBruhat.pure F (insertFinite F S (restrictFiniteBruhat F S ψ)) φ := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  exact sProjectionFunction_pure F S φ ψ

private theorem restrict_insert (S : Finset (Place F)) (ψ : locallyConstantTests (Coordinates F S)) :
    restrictFiniteBruhat F S (insertFinite F S ψ) = ψ := by
  apply Subtype.ext
  funext x
  change (insertFinite F S ψ).toLocallyConstant (finitePad F S x) = ψ.val x
  rw [insertFinite_apply, finiteSelected_pad]
  have h : ∀ v ∉ S, finitePad F S x v ∈ v.adicCompletionIntegers F := by
    intro v hv
    rw [finitePad_apply, dif_neg hv]
    exact zero_mem _
  rw [if_pos h, mul_one]

private def globalBruhatFunctions : GlobalBruhat F →ₗ[ℂ] (Adeles F → ℂ) :=
  (bruhatSubmodule F).subtype.comp (GlobalBruhat.algebraicEquiv F).toLinearMap

private theorem sLocalBruhatImage_map (S : Finset (Place F)) :
    (sLocalBruhatImage F S).map (globalBruhatFunctions F) =
      Submodule.span ℂ {f | ∃ (ψ : locallyConstantTests (Coordinates F S))
        (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)), bruhatTensor F φ (insertFinite F S ψ) = f} := by
  rw [sLocalBruhatImage, Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨ψ, φ, rfl⟩, rfl⟩
    exact ⟨ψ, φ, rfl⟩
  · rintro ⟨ψ, φ, rfl⟩
    exact ⟨GlobalBruhat.pure F (insertFinite F S ψ) φ, ⟨ψ, φ, rfl⟩, rfl⟩

theorem sLocalBruhatProjection_mem (S : Finset (Place F)) (f : GlobalBruhat F) :
    sLocalBruhatProjection F S f ∈ sLocalBruhatImage F S := by
  let j := globalBruhatFunctions F
  have hj : Injective j := Subtype.val_injective.comp (GlobalBruhat.algebraicEquiv F).injective
  have hspan : j (sLocalBruhatProjection F S f) ∈ (sLocalBruhatImage F S).map j := by
    change sProjectionFunction F S (j f) ∈ (sLocalBruhatImage F S).map (globalBruhatFunctions F)
    rw [sLocalBruhatImage_map]
    have hf : j f ∈ bruhatSubmodule F := (GlobalBruhat.algebraicEquiv F f).property
    apply Submodule.span_induction (p := fun g _ => sProjectionFunction F S g ∈
      Submodule.span ℂ {h | ∃ (ψ : locallyConstantTests (Coordinates F S))
        (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)), bruhatTensor F φ (insertFinite F S ψ) = h})
      _ _ _ _ hf
    · rintro _ ⟨φ, ψ, rfl⟩
      rw [sProjectionFunction_pure]
      exact Submodule.subset_span ⟨restrictFiniteBruhat F S ψ, φ, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro f g hf hg h₁ h₂
      rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    · intro c f hf h
      rw [map_smul]; exact Submodule.smul_mem _ _ h
  obtain ⟨g, hg, he⟩ := hspan
  exact hj he ▸ hg

theorem sLocalBruhatProjection_fixes (S : Finset (Place F)) (f : GlobalBruhat F)
    (hf : f ∈ sLocalBruhatImage F S) : sLocalBruhatProjection F S f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, φ, rfl⟩ := hf
    rw [sLocalBruhatProjection_pure, restrict_insert]
  | zero => exact map_zero _
  | add f g hf hg h₁ h₂ => rw [map_add, h₁, h₂]
  | smul c f hf h => rw [map_smul, h]

theorem sLocalBruhatRestriction_reconstruct (S : Finset (Place F))
    (f : sLocalBruhatImage F S) (a : Adeles F) :
    GlobalBruhat.evaluation F a f.val =
      sLocalBruhatRestriction F S f.val (sAdelesProjection F S a) *
        if ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F then 1 else 0 := by
  have h := sLocalBruhatProjection_apply F S f.val a
  rw [sLocalBruhatProjection_fixes F S f.val f.property] at h
  have hcoords : finiteSelected F S a.2 = (sAdelesProjection F S a).2 := by
    funext v
    exact finiteSelected_apply F S a.2 v
  rw [hcoords] at h
  exact h

theorem sLocalBruhatProjection_range (S : Finset (Place F)) :
    (sLocalBruhatProjection F S).range = sLocalBruhatImage F S := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact sLocalBruhatProjection_mem F S g
  · intro hf
    exact ⟨f, sLocalBruhatProjection_fixes F S f hf⟩

theorem sLocalBruhatProjection_idempotent (S : Finset (Place F)) (f : GlobalBruhat F) :
    sLocalBruhatProjection F S (sLocalBruhatProjection F S f) = sLocalBruhatProjection F S f :=
  sLocalBruhatProjection_fixes F S _ (sLocalBruhatProjection_mem F S f)

private theorem finitePad_selected_comp (S T : Finset (Place F)) (hST : S ⊆ T)
    (x : FinAdeles F) :
    finitePad F S (finiteSelected F S (finitePad F T (finiteSelected F T x))) =
      finitePad F S (finiteSelected F S x) := by
  apply RestrictedProduct.ext
  intro v
  change finitePad F S (finiteSelected F S (finitePad F T (finiteSelected F T x))) v =
    finitePad F S (finiteSelected F S x) v
  simp only [finitePad_apply]
  by_cases hv : v ∈ S
  · simp only [dif_pos hv, finiteSelected_apply, finitePad_apply, dif_pos (hST hv)]
  · simp only [dif_neg hv]

private theorem finitePad_selected_comp_reverse (S T : Finset (Place F)) (hST : S ⊆ T)
    (x : FinAdeles F) :
    finitePad F T (finiteSelected F T (finitePad F S (finiteSelected F S x))) =
      finitePad F S (finiteSelected F S x) := by
  apply RestrictedProduct.ext
  intro v
  change finitePad F T (finiteSelected F T (finitePad F S (finiteSelected F S x))) v =
    finitePad F S (finiteSelected F S x) v
  by_cases hv : v ∈ T
  · simp only [finitePad_apply F T, dif_pos hv, finiteSelected_apply]
  · have hvs : v ∉ S := fun h => hv (hST h)
    simp only [finitePad_apply, dite_eq_right hv, dite_eq_right hvs]

private theorem globalBruhat_ext {f g : GlobalBruhat F}
    (h : ∀ a, GlobalBruhat.evaluation F a f = GlobalBruhat.evaluation F a g) : f = g :=
  (GlobalBruhat.algebraicEquiv F).injective (Subtype.ext (funext h))

theorem sLocalBruhatProjection_comp (S T : Finset (Place F)) (hST : S ⊆ T)
    (f : GlobalBruhat F) :
    sLocalBruhatProjection F S (sLocalBruhatProjection F T f) = sLocalBruhatProjection F S f := by
  apply globalBruhat_ext F
  intro a
  rw [sLocalBruhatProjection_apply F S, sLocalBruhatProjection_apply F T f
    (a.1, finitePad F S (finiteSelected F S a.2)), sLocalBruhatProjection_apply F S f a]
  change (GlobalBruhat.evaluation F (a.1, finitePad F T (finiteSelected F T
    (finitePad F S (finiteSelected F S a.2)))) f *
      (if ∀ v ∉ T, finitePad F S (finiteSelected F S a.2) v ∈ v.adicCompletionIntegers F then 1 else 0)) *
    (if ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F then 1 else 0) = _
  rw [finitePad_selected_comp_reverse F S T hST]
  have h : ∀ v ∉ T, finitePad F S (finiteSelected F S a.2) v ∈ v.adicCompletionIntegers F := by
    intro v hv
    rw [finitePad_apply, dif_neg (fun hs => hv (hST hs))]
    exact zero_mem _
  rw [if_pos h, mul_one]

theorem sLocalBruhatProjection_comp_reverse (S T : Finset (Place F)) (hST : S ⊆ T)
    (f : GlobalBruhat F) :
    sLocalBruhatProjection F T (sLocalBruhatProjection F S f) = sLocalBruhatProjection F S f := by
  apply globalBruhat_ext F
  intro a
  rw [sLocalBruhatProjection_apply F T, sLocalBruhatProjection_apply F S f
    (a.1, finitePad F T (finiteSelected F T a.2)), sLocalBruhatProjection_apply F S f a]
  change (GlobalBruhat.evaluation F (a.1, finitePad F S (finiteSelected F S
    (finitePad F T (finiteSelected F T a.2)))) f *
      (if ∀ v ∉ S, finitePad F T (finiteSelected F T a.2) v ∈ v.adicCompletionIntegers F then 1 else 0)) *
    (if ∀ v ∉ T, a.2 v ∈ v.adicCompletionIntegers F then 1 else 0) = _
  rw [finitePad_selected_comp F S T hST]
  by_cases hT : ∀ v ∉ T, a.2 v ∈ v.adicCompletionIntegers F
  · rw [if_pos hT, mul_one]
    have hcond : (∀ v ∉ S, finitePad F T (finiteSelected F T a.2) v ∈ v.adicCompletionIntegers F) ↔
        ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h v hv
        by_cases ht : v ∈ T
        · simpa [finitePad_apply, ht, finiteSelected_apply] using h v hv
        · exact hT v ht
      · intro h v hv
        by_cases ht : v ∈ T
        · simpa [finitePad_apply, ht, finiteSelected_apply] using h v hv
        · simp [finitePad_apply, ht]
    rw [hcond]
  · have hS : ¬∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F :=
      fun hs => hT (fun v hv => hs v (fun hs' => hv (hST hs')))
    simp only [if_neg hT, if_neg hS, mul_zero]


/-- The locally convex topology on the S-local space is the final topology
for the slices with fixed finite-place input. -/
theorem continuous_sLocal_of_pure (S : Finset (Place F))
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {ι : Type*} {q : SeminormFamily ℂ E ι} (hE : WithSeminorms q)
    (f : sLocalBruhatImage F S →ₗ[ℂ] E)
    (hf : ∀ ψ : locallyConstantTests (Coordinates F S),
      Continuous (fun φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ) =>
        f ⟨GlobalBruhat.pure F (insertFinite F S ψ) φ, Submodule.subset_span ⟨ψ, φ, rfl⟩⟩)) :
    Continuous f := by
  let P := (sLocalBruhatProjection F S).toLinearMap.codRestrict (sLocalBruhatImage F S)
    (sLocalBruhatProjection_mem F S)
  have hc : Continuous (f.comp P) := by
    apply GlobalBruhat.continuous_of_pure F hE
    intro ψ
    convert hf (restrictFiniteBruhat F S ψ) using 1
    funext φ
    apply congrArg f
    exact Subtype.ext (sLocalBruhatProjection_pure F S ψ φ)
  have he : (fun x : sLocalBruhatImage F S => (f.comp P) x.val) = f := by
    funext x
    apply congrArg f
    exact Subtype.ext (sLocalBruhatProjection_fixes F S x.val x.property)
  rw [← he]
  exact hc.comp continuous_subtype_val

/-- The canonical product of an archimedean and a finite S-local test. -/
def sLocalBruhatPure (S : Finset (Place F)) :
    𝓢(mixedEmbedding.mixedSpace F, ℂ) →ₗ[ℂ] locallyConstantTests (Coordinates F S) →ₗ[ℂ]
      sLocalBruhatImage F S := by
  let B (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : locallyConstantTests (Coordinates F S)) :
      sLocalBruhatImage F S :=
    ⟨GlobalBruhat.pure F (insertFinite F S ψ) φ, Submodule.subset_span ⟨ψ, φ, rfl⟩⟩
  have h (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : locallyConstantTests (Coordinates F S))
      (x : Adeles F) :
      (GlobalBruhat.algebraicEquiv F (B φ ψ).val).val x =
        φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
          (ψ.val (finiteSelected F S x.2) *
            (if ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F then 1 else 0)) := by
    change bruhatTensor F φ (insertFinite F S ψ) x = _
    unfold bruhatTensor
    rw [insertFinite_apply]
  let L (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) :
      locallyConstantTests (Coordinates F S) →ₗ[ℂ] sLocalBruhatImage F S :=
    { toFun := B φ
      map_add' := fun ψ ξ => by
        apply Subtype.ext
        apply (GlobalBruhat.algebraicEquiv F).injective
        apply Subtype.ext
        funext x
        simp only [map_add, Submodule.coe_add, Pi.add_apply, h]
        ring
      map_smul' := fun c ψ => by
        apply Subtype.ext
        apply (GlobalBruhat.algebraicEquiv F).injective
        apply Subtype.ext
        funext x
        simp only [map_smul, RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, h, smul_eq_mul]
        ring }
  refine { toFun := L, map_add' := ?_, map_smul' := ?_ }
  · intro φ ξ
    apply LinearMap.ext
    intro ψ
    exact Subtype.ext (map_add (GlobalBruhat.pure F (insertFinite F S ψ)) φ ξ)
  · intro c φ
    apply LinearMap.ext
    intro ψ
    exact Subtype.ext (map_smul (GlobalBruhat.pure F (insertFinite F S ψ)) c φ)

/-- Continuity from the inductive tensor presentation used in (2.1.4.1).
The finite test space has its finest locally convex topology. -/
theorem sLocalBruhatPure_lift_continuous (S : Finset (Place F)) :
    letI : TopologicalSpace (locallyConstantTests (Coordinates F S)) := finestLocallyConvexTopology _
    Continuous[inductiveTensorTopology _ _, inferInstance] (TensorProduct.lift (sLocalBruhatPure F S)) := by
  letI : TopologicalSpace (locallyConstantTests (Coordinates F S)) := finestLocallyConvexTopology _
  letI : IsTopologicalAddGroup (locallyConstantTests (Coordinates F S)) :=
    (finest_withSeminorms _).topologicalAddGroup
  apply (continuous_inductiveTensor_lift_iff (sLocalBruhatPure F S)).mpr
  refine ⟨fun ψ => ?_, fun φ => finest_linear_continuous _⟩
  change Continuous (fun φ =>
    (⟨GlobalBruhat.pure F (insertFinite F S ψ) φ, Submodule.subset_span ⟨ψ, φ, rfl⟩⟩ :
      sLocalBruhatImage F S))
  exact (GlobalBruhat.pure_continuous F (insertFinite F S ψ)).subtype_mk _

theorem sLocalBruhatPure_restrict (S : Finset (Place F))
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : locallyConstantTests (Coordinates F S))
    (x : SAdeles F S) :
    sLocalBruhatRestriction F S (sLocalBruhatPure F S φ ψ).val x =
      φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * ψ.val x.2 := by
  change sLocalBruhatRestriction F S (GlobalBruhat.pure F (insertFinite F S ψ) φ) x = _
  rw [sLocalBruhatRestriction_pure, restrict_insert]

/-- Point evaluations of a separated product detect the coefficients of
a tensor whenever the two families of factor evaluations separate points. -/
theorem tensor_injective_of_separated_evaluations
    {A B E X Y : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup E] [Module ℂ E]
    (L : A ⊗[ℂ] B →ₗ[ℂ] E)
    (a : X → A →ₗ[ℂ] ℂ) (b : Y → B →ₗ[ℂ] ℂ) (e : X → Y → E →ₗ[ℂ] ℂ)
    (ha : ∀ u, (∀ x, a x u = 0) → u = 0)
    (hb : ∀ v, (∀ y, b y v = 0) → v = 0)
    (he : ∀ x y u v, e x y (L (u ⊗ₜ[ℂ] v)) = a x u * b y v) :
    Injective L := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  change L u = 0 at hu
  let basis := Module.Free.chooseBasis ℂ A
  let P : A ⊗[ℂ] B ≃ₗ[ℂ] _ := TensorProduct.equivFinsuppOfBasisLeft basis
  let d := P u
  have hrepr : (∑ i ∈ d.support, basis i ⊗ₜ[ℂ] d i) = u :=
    (TensorProduct.equivFinsuppOfBasisLeft_symm_apply basis d).symm.trans (P.symm_apply_apply u)
  have hs : (∑ i ∈ d.support, L (basis i ⊗ₜ[ℂ] d i)) = 0 := by
    rw [← map_sum, hrepr, hu]
  apply P.injective
  rw [map_zero]
  apply Finsupp.ext
  intro i
  change d i = 0
  apply hb
  intro y
  have hv : (∑ j ∈ d.support, b y (d j) • basis j) = 0 := by
    apply ha
    intro x
    have hx := congrArg (e x y) hs
    simp only [map_sum, map_zero, he] at hx
    simp only [map_sum, map_smul, smul_eq_mul]
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans hx
  have hz : (∑ j ∈ d.support, b y (d j) * basis.coord i (basis j)) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg (basis.coord i) hv
  have hc (j) : basis.coord i (basis j) = if j = i then 1 else 0 := by
    rw [basis.coord_apply, basis.repr_self, Finsupp.single_apply]
  by_cases hi : i ∈ d.support
  · rw [Finset.sum_eq_single i] at hz
    · simpa only [hc, ite_true, mul_one] using hz
    · intro j _ hji
      simp only [hc, ite_eq_right hji, mul_zero]
    · exact fun h => (h hi).elim
  · rw [Finsupp.notMem_support_iff.mp hi, map_zero]

private theorem sLocalBruhatPure_lift_bijective (S : Finset (Place F)) :
    Bijective (TensorProduct.lift (sLocalBruhatPure F S)) := by
  let A := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
  let B := locallyConstantTests (Coordinates F S)
  let L := TensorProduct.lift (sLocalBruhatPure F S)
  constructor
  · let a (x : InfiniteAdeleRing F) : A →ₗ[ℂ] ℂ :=
      { toFun := fun φ => φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let b (y : Coordinates F S) := (LinearMap.proj y).comp B.subtype
    let e (x : InfiniteAdeleRing F) (y : Coordinates F S) :=
      (LinearMap.proj (x, y)).comp ((sLocalBruhatRestriction F S).comp (sLocalBruhatImage F S).subtype)
    apply tensor_injective_of_separated_evaluations L a b e
    · intro φ hφ
      ext x
      obtain ⟨y, rfl⟩ := (InfiniteAdeleRing.ringEquiv_mixedSpace F).surjective x
      exact hφ y
    · intro ψ hψ
      exact Subtype.ext (funext hψ)
    · intro x y φ ψ
      change sLocalBruhatRestriction F S (L (φ ⊗ₜ[ℂ] ψ)).val (x, y) = _
      rw [show L (φ ⊗ₜ[ℂ] ψ) = sLocalBruhatPure F S φ ψ from TensorProduct.lift.tmul _ _,
        sLocalBruhatPure_restrict]
      rfl
  · intro f
    have h : sLocalBruhatImage F S ≤ (LinearMap.range L).map (sLocalBruhatImage F S).subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨ψ, φ, rfl⟩
      refine ⟨L (φ ⊗ₜ[ℂ] ψ), ⟨_, rfl⟩, ?_⟩
      change (L (φ ⊗ₜ[ℂ] ψ)).val = _
      exact congrArg Subtype.val (TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) φ ψ)
    obtain ⟨g, ⟨u, hu⟩, hg⟩ := h f.property
    exact ⟨u, hu.trans (Subtype.ext hg)⟩

/-- The canonical tensor presentation of the actual S-local test space. -/
def sLocalBruhatTensorEquiv (S : Finset (Place F)) :
    let A := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
    let B := locallyConstantTests (Coordinates F S)
    letI : TopologicalSpace B := finestLocallyConvexTopology B
    letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
    (A ⊗[ℂ] B) ≃L[ℂ] sLocalBruhatImage F S := by
  let A := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
  let B := locallyConstantTests (Coordinates F S)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  let W := inductiveTensor_withSeminorms (E := A) (F := B)
  let e := LinearEquiv.ofBijective _ (sLocalBruhatPure_lift_bijective F S)
  refine ⟨e, sLocalBruhatPure_lift_continuous F S, ?_⟩
  change Continuous (e.symm.toLinearMap)
  apply continuous_sLocal_of_pure F S W e.symm.toLinearMap
  intro ψ
  have he (φ : A) :
      e.symm ⟨GlobalBruhat.pure F (insertFinite F S ψ) φ, Submodule.subset_span ⟨ψ, φ, rfl⟩⟩ =
        φ ⊗ₜ[ℂ] ψ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (TensorProduct.lift.tmul (f' := sLocalBruhatPure F S) φ ψ).symm
  simp_rw [LinearEquiv.coe_coe, he]
  exact (W.continuous_iff_continuous_comp ((TensorProduct.mk ℂ A B).flip ψ)).mpr
    fun I => I.first ψ

theorem sLocalBruhatImage_mono {S T : Finset (Place F)} (hST : S ⊆ T) :
    sLocalBruhatImage F S ≤ sLocalBruhatImage F T := by
  intro f hf
  have he := sLocalBruhatProjection_comp_reverse F S T hST f
  rw [sLocalBruhatProjection_fixes F S f hf] at he
  rw [← he]
  exact sLocalBruhatProjection_mem F T f

/-- The canonical transition between two S-local stages. -/
def sLocalBruhatTransition {S T : Finset (Place F)} (hST : S ⊆ T) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F T :=
  ⟨Submodule.inclusion (sLocalBruhatImage_mono F hST), continuous_subtype_val.subtype_mk _⟩

/-- Restrict the globally inserted finite test to a larger coordinate stage. -/
def sLocalFiniteExtend (S T : Finset (Place F)) (ψ : locallyConstantTests (Coordinates F S)) :
    locallyConstantTests (Coordinates F T) :=
  restrictFiniteBruhat F T (insertFinite F S ψ)

theorem sLocalFiniteExtend_apply {S T : Finset (Place F)} (hST : S ⊆ T)
    (ψ : locallyConstantTests (Coordinates F S)) (x : Coordinates F T) :
    (sLocalFiniteExtend F S T ψ).val x =
      ψ.val (fun w : S => x ⟨w.val, hST w.property⟩) *
        (if ∀ w : T, w.val ∉ S → x w ∈ w.val.adicCompletionIntegers F then 1 else 0) := by
  change (insertFinite F S ψ).toLocallyConstant (finitePad F T x) = _
  rw [insertFinite_apply]
  have hx : finiteSelected F S (finitePad F T x) = fun w : S => x ⟨w.val, hST w.property⟩ := by
    funext w
    rw [finiteSelected_apply, finitePad_apply, dite_eq_left (hST w.property)]
  rw [hx, finitePad_integralOutside]
  by_cases h : ∀ w : T, w.val ∉ S → x w ∈ w.val.adicCompletionIntegers F
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem sLocalBruhatTransition_pure {S T : Finset (Place F)} (hST : S ⊆ T)
    (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : locallyConstantTests (Coordinates F S)) :
    sLocalBruhatTransition F hST (sLocalBruhatPure F S φ ψ) =
      sLocalBruhatPure F T φ (sLocalFiniteExtend F S T ψ) := by
  apply Subtype.ext
  let f := sLocalBruhatPure F S φ ψ
  have h := sLocalBruhatProjection_fixes F T f.val
    ((sLocalBruhatImage_mono F hST) f.property)
  change GlobalBruhat.pure F (insertFinite F S ψ) φ =
    GlobalBruhat.pure F (insertFinite F T (sLocalFiniteExtend F S T ψ)) φ
  change sLocalBruhatProjection F T (GlobalBruhat.pure F (insertFinite F S ψ) φ) = _ at h
  rw [sLocalBruhatProjection_pure] at h
  exact h.symm

/-- Proposition 2.1.4.1(3). A transition pads every test in the smaller
stage with the product of the integer indicators. -/
theorem sLocalBruhatTransition_restrict {S T : Finset (Place F)} (hST : S ⊆ T)
    (f : sLocalBruhatImage F S) (x : SAdeles F T) :
    sLocalBruhatRestriction F T (sLocalBruhatTransition F hST f).val x =
      sLocalBruhatRestriction F S f.val
        (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩) *
          if ∀ w : T, w.val ∉ S → x.2 w ∈ w.val.adicCompletionIntegers F then 1 else 0 := by
  change GlobalBruhat.evaluation F (sLocalBruhatPad F T x) f.val = _
  rw [sLocalBruhatRestriction_reconstruct]
  have hx : sAdelesProjection F S (sLocalBruhatPad F T x) =
      (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩) := by
    refine Prod.ext rfl (funext fun w ↦ ?_)
    exact (finitePad_apply F T x.2 w.val).trans (dite_eq_left (hST w.property))
  rw [hx]
  exact congrArg (_ * ·) (if_congr (finitePad_integralOutside F S T x.2) rfl rfl)

/-- Restrict the global projection to a larger S-local stage. -/
def sLocalBruhatStageProjection {S T : Finset (Place F)} (hST : S ⊆ T) :
    sLocalBruhatImage F T →L[ℂ] sLocalBruhatImage F S :=
  ⟨((sLocalBruhatProjection F S).toLinearMap.comp (sLocalBruhatImage F T).subtype).codRestrict
      (sLocalBruhatImage F S) (fun f => sLocalBruhatProjection_mem F S f.val),
    ((sLocalBruhatProjection F S).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem sLocalBruhatStageProjection_leftInverse {S T : Finset (Place F)} (hST : S ⊆ T) :
    LeftInverse (sLocalBruhatStageProjection F hST) (sLocalBruhatTransition F hST) := by
  intro f
  exact Subtype.ext (sLocalBruhatProjection_fixes F S f.val f.property)

/-- Lemma 2.1.4.3. The projection inside a larger stage has image the
embedded smaller stage and is idempotent. -/
theorem sLocalBruhatStageProjection_range_idempotent {S T : Finset (Place F)} (hST : S ⊆ T) :
    let P := (sLocalBruhatTransition F hST).comp (sLocalBruhatStageProjection F hST)
    P.range = (sLocalBruhatTransition F hST).range ∧ P.comp P = P := by
  intro P
  have hP : ∀ x, P x = sLocalBruhatTransition F hST (sLocalBruhatStageProjection F hST x) :=
    fun _ => rfl
  constructor
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨sLocalBruhatStageProjection F hST x, (hP x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨sLocalBruhatTransition F hST x, ?_⟩
      change P (sLocalBruhatTransition F hST x) = sLocalBruhatTransition F hST x
      rw [hP, sLocalBruhatStageProjection_leftInverse]
  · apply ContinuousLinearMap.ext
    intro x
    change P (P x) = P x
    rw [hP (P x), hP x, sLocalBruhatStageProjection_leftInverse]

theorem sLocalBruhatStageProjection_global {S T : Finset (Place F)} (hST : S ⊆ T)
    (x : sLocalBruhatImage F T) :
    (sLocalBruhatStageProjection F hST x).val = sLocalBruhatProjection F S x.val := rfl

/-- Compatibility with enlargement of the stage. Both sides land in the same
smaller stage before it is re-embedded. -/
theorem sLocalBruhatStageProjection_compatible {S T U : Finset (Place F)}
    (hST : S ⊆ T) (hTU : T ⊆ U) :
    (sLocalBruhatStageProjection F (hST.trans hTU)).comp (sLocalBruhatTransition F hTU) =
      sLocalBruhatStageProjection F hST := by
  ext x
  rfl


/-- A finite adelic test is invariant under the tails that are integral
and zero on a sufficiently large finite set of coordinates. -/
private theorem finiteBruhat_invariant_integralTail (ψ : FiniteBruhat F) :
    ∃ S : Finset (Place F), ∀ a d : FinAdeles F, (∀ v : S, d v.val = 0) →
      (∀ v, d v ∈ v.adicCompletionIntegers F) →
      ψ.toLocallyConstant (a + d) = ψ.toLocallyConstant a := by
  let f := ψ.toLocallyConstant
  letI : Fact (∀ v : Place F, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
  letI : IsTopologicalAddGroup (FinAdeles F) :=
    inferInstanceAs (IsTopologicalAddGroup (Πʳ v : Place F,
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  have hlocal (a : FinAdeles F) : ∀ᶠ z : FinAdeles F × FinAdeles F in 𝓝 (0, a),
      f (z.2 + z.1) = f z.2 := by
    have hv : ∀ᶠ x in 𝓝 a, f x = f a := (IsLocallyConstant.iff_eventually_eq f).mp f.isLocallyConstant a
    have h₁ : Tendsto (fun z : FinAdeles F × FinAdeles F => z.2 + z.1) (𝓝 (0, a)) (𝓝 a) :=
      (continuous_snd.add continuous_fst).tendsto' _ _ (add_zero _)
    filter_upwards [h₁.eventually hv, continuous_snd.continuousAt.eventually hv] with z h₁ h₂
    exact h₁.trans h₂.symm
  have hs : ∀ᶠ d in 𝓝 (0 : FinAdeles F), ∀ a ∈ tsupport f, f (a + d) = f a :=
    ψ.compactSupport.eventually_forall_of_forall_eventually fun a _ => hlocal a
  have hsi : ∀ᶠ d in 𝓝 (0 : FinAdeles F), ∀ a ∈ tsupport f, f (a - d) = f a := by
    have hneg : Tendsto (fun d : FinAdeles F => -d) (𝓝 0) (𝓝 0) :=
      continuous_neg.tendsto' _ _ neg_zero
    simpa only [sub_eq_add_neg] using hneg.eventually hs
  have hstab : ∀ᶠ d in 𝓝 (0 : FinAdeles F), ∀ a, f (a + d) = f a := by
    filter_upwards [hs, hsi] with d hd hdi a
    by_cases ha : a ∈ tsupport f
    · exact hd a ha
    · by_cases hda : a + d ∈ tsupport f
      · simpa only [add_sub_cancel_right] using (hdi (a + d) hda).symm
      · rw [image_eq_zero_of_notMem_tsupport hda, image_eq_zero_of_notMem_tsupport ha]
  let O (v : Place F) := v.adicCompletionIntegers F
  let i : (∀ v, O v) → FinAdeles F := RestrictedProduct.structureMap
    (fun v : Place F => v.adicCompletion F) (fun v => O v) cofinite
  have hi : Continuous i := (RestrictedProduct.isOpenEmbedding_structureMap
    (fun v : Place F => Valued.isOpen_valuationSubring (v.adicCompletion F))).continuous
  have hein : ∀ᶠ x in 𝓝 (0 : ∀ v, O v), ∀ a, f (a + i x) = f a :=
    (hi.tendsto' _ _ (by rfl)).eventually hstab
  rw [nhds_pi] at hein
  let hb := Filter.hasBasis_pi (fun v : Place F => (𝓝 (0 : O v)).basis_sets)
  obtain ⟨⟨S, U⟩, ⟨hS, hU⟩, hsU⟩ := hb.mem_iff.mp hein
  refine ⟨hS.toFinset, fun a d hd₀ hd => ?_⟩
  let x (v : Place F) : O v := ⟨d v, hd v⟩
  have hx : x ∈ S.pi U := by
    intro v hv
    have hv₀ := hd₀ ⟨v, hS.mem_toFinset.mpr hv⟩
    have he : x v = 0 := Subtype.ext hv₀
    rw [he]
    exact mem_of_mem_nhds (hU v hv)
  have hix : i x = d := by
    apply DFunLike.ext
    intro v
    rfl
  exact hix ▸ hsU hx a

theorem sLocalBruhatProjection_pure_eventually (ψ : FiniteBruhat F) :
    ∃ S : Finset (Place F), ∀ T : Finset (Place F), S ⊆ T →
      ∀ φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ),
        sLocalBruhatProjection F T (GlobalBruhat.pure F ψ φ) = GlobalBruhat.pure F ψ φ := by
  obtain ⟨S, hS⟩ := finiteBruhat_invariant_integralTail F ψ
  obtain ⟨U, hU⟩ := compact_finiteAdeles_integralOutside ψ.compactSupport
  refine ⟨S ∪ U, fun T hT φ => ?_⟩
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  have hUT : U ⊆ T := Finset.subset_union_right.trans hT
  apply globalBruhat_ext F
  intro a
  rw [sLocalBruhatProjection_apply]
  by_cases h : ∀ v ∉ T, a.2 v ∈ v.adicCompletionIntegers F
  · rw [ite_eq_left h, mul_one]
    let x := finitePad F T (finiteSelected F T a.2)
    let d := a.2 - x
    have hd₀ (v : T) : d v.val = 0 := by
      change a.2 v.val - x v.val = 0
      simp [x, finitePad_apply, v.property, finiteSelected_apply]
    have hd (v : Place F) : d v ∈ v.adicCompletionIntegers F := by
      by_cases hv : v ∈ T
      · rw [hd₀ ⟨v, hv⟩]; exact zero_mem _
      · change a.2 v - x v ∈ v.adicCompletionIntegers F
        rw [show x v = 0 from (finitePad_apply F T _ v).trans (dite_eq_right hv), sub_zero]
        exact h v hv
    have he := hS x d (fun v => hd₀ ⟨v.val, hST v.property⟩) hd
    have hx : x + d = a.2 := by dsimp [d]; abel
    rw [hx] at he
    change φ _ * ψ.toLocallyConstant x = φ _ * ψ.toLocallyConstant a.2
    rw [he]
  · rw [ite_eq_right h, mul_zero]
    have hz : ψ.toLocallyConstant a.2 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      refine fun ha => h fun v hv => hU a.2 ha v (fun hu => hv (hUT hu))
    change 0 = φ _ * ψ.toLocallyConstant a.2
    rw [hz, mul_zero]


private theorem sLocalBruhatClosed (S : Finset (Place F)) :
    IsClosed (sLocalBruhatImage F S : Set (GlobalBruhat F)) := by
  have he : (sLocalBruhatImage F S : Set (GlobalBruhat F)) =
      {f | sLocalBruhatProjection F S f = f} := by
    ext f
    exact ⟨sLocalBruhatProjection_fixes F S f, fun h =>
      h ▸ sLocalBruhatProjection_mem F S f⟩
  rw [he]
  exact isClosed_eq (sLocalBruhatProjection F S).continuous continuous_id

/-- Insert an S-local test into the global space with the integer indicator
at all omitted finite places, as computed by `sLocalBruhatRestriction_reconstruct`. -/
def sLocalBruhatInclusion (S : Finset (Place F)) :
    sLocalBruhatImage F S →L[ℂ] GlobalBruhat F :=
  ⟨(sLocalBruhatImage F S).subtype, continuous_subtype_val⟩

def sLocalBruhatCorestrict (S : Finset (Place F)) :
    GlobalBruhat F →L[ℂ] sLocalBruhatImage F S :=
  ⟨(sLocalBruhatProjection F S).toLinearMap.codRestrict (sLocalBruhatImage F S)
    (sLocalBruhatProjection_mem F S),
    (sLocalBruhatProjection F S).continuous.subtype_mk _⟩

/-- Projecting a global test to the S-local stage leaves its restriction to
the S-adeles unchanged. -/
theorem sLocalBruhatCorestrict_restrict (S : Finset (Place F)) (f : GlobalBruhat F)
    (x : SAdeles F S) :
    sLocalBruhatRestriction F S (sLocalBruhatCorestrict F S f).val x =
      sLocalBruhatRestriction F S f x := by
  change GlobalBruhat.evaluation F (sLocalBruhatPad F S x) (sLocalBruhatProjection F S f) = _
  rw [sLocalBruhatProjection_apply]
  have h : ∀ v ∉ S, (sLocalBruhatPad F S x).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv
    change finitePad F S x.2 v ∈ v.adicCompletionIntegers F
    rw [finitePad_apply, dite_eq_right hv]
    exact zero_mem _
  rw [ite_eq_left h, mul_one]
  change GlobalBruhat.evaluation F (x.1, finitePad F S (finiteSelected F S (finitePad F S x.2))) f = _
  rw [finiteSelected_pad]
  rfl

/-- The canonical padded transition is a closed topological embedding. -/
theorem sLocalBruhatTransition_closed {S T : Finset (Place F)} (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalBruhatTransition F hST) := by
  have hEq : range (sLocalBruhatTransition F hST) =
      (Subtype.val : sLocalBruhatImage F T → GlobalBruhat F) ⁻¹'
        (sLocalBruhatImage F S : Set (GlobalBruhat F)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
  refine ⟨?_, hEq ▸ (sLocalBruhatClosed F S).preimage continuous_subtype_val⟩
  exact (IsEmbedding.of_comp_iff (g := Subtype.val) IsEmbedding.subtypeVal).mp
    (IsEmbedding.subtypeVal (p := fun x : GlobalBruhat F => x ∈ sLocalBruhatImage F S))

/-- A cofinal increasing sequence of finite sets of places. -/
private theorem exists_sBruhatPlaceExhaustion :
    ∃ S : ℕ → Finset (Place F), Monotone S ∧ ∀ T, ∃ n, T ⊆ S n := by
  letI := finitePlaces_countable F
  obtain ⟨e, he⟩ := exists_injective_nat (Place F)
  let finite (n : ℕ) : {v : Place F | e v < n}.Finite :=
    (finite_lt_nat n).preimage he.injOn
  let S (n : ℕ) := (finite n).toFinset
  refine ⟨S, ?_, ?_⟩
  · intro m n h v hv
    have hm : e v < m := (finite m).mem_toFinset.mp hv
    exact (finite n).mem_toFinset.mpr (hm.trans_le h)
  · intro T
    refine ⟨T.sup e + 1, fun v hv => (finite _).mem_toFinset.mpr ?_⟩
    exact (Finset.le_sup hv).trans_lt (Nat.lt_succ_self _)

set_option maxHeartbeats 2000000 in
private theorem sLocalBruhat_exhaust_from
    (S : ℕ → Finset (Place F)) (hS : Monotone S) (hSc : ∀ T, ∃ n, T ⊆ S n)
    (x : GlobalBruhat F) : ∃ n, x ∈ sLocalBruhatImage F (S n) := by
  let e := GlobalBruhat.algebraicEquiv F
  have hm : ∀ (g : Adeles F → ℂ) (hg : g ∈ bruhatSubmodule F),
      ∃ n, e.symm ⟨g, hg⟩ ∈ sLocalBruhatImage F (S n) := by
    intro g hg
    apply Submodule.span_induction
      (p := fun g hg => ∃ n, e.symm ⟨g, hg⟩ ∈ sLocalBruhatImage F (S n)) _ _ _ _ hg
    · rintro _ ⟨φ, ψ, rfl⟩
      obtain ⟨T, hT⟩ := sLocalBruhatProjection_pure_eventually F ψ
      obtain ⟨n, hn⟩ := hSc T
      have he := hT (S n) hn φ
      exact ⟨n, he ▸ sLocalBruhatProjection_mem F (S n) (GlobalBruhat.pure F ψ φ)⟩
    · refine ⟨0, ?_⟩
      change e.symm 0 ∈ sLocalBruhatImage F (S 0)
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy h₁ h₂
      obtain ⟨i, hi⟩ := h₁
      obtain ⟨j, hj⟩ := h₂
      refine ⟨max i j, ?_⟩
      change e.symm ((⟨x, hx⟩ : bruhatSubmodule F) + ⟨y, hy⟩) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ (sLocalBruhatImage_mono F (hS (le_max_left i j)) hi)
        (sLocalBruhatImage_mono F (hS (le_max_right i j)) hj)
    · intro c x hx h
      obtain ⟨n, hn⟩ := h
      refine ⟨n, ?_⟩
      change e.symm (c • (⟨x, hx⟩ : bruhatSubmodule F)) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ _ hn
  have he := hm (e x).val (e x).property
  change ∃ n, e.symm (e x) ∈ sLocalBruhatImage F (S n) at he
  rwa [e.symm_apply_apply] at he

private theorem continuous_of_sLocalStages {R : Type*} [AddCommGroup R] [Module ℂ R]
    [TopologicalSpace R] [PolynormableSpace ℂ R]
    (S : ℕ → Finset (Place F)) (hSc : ∀ T, ∃ n, T ⊆ S n)
    (P : GlobalBruhat F →ₗ[ℂ] R)
    (hP : ∀ n, Continuous (P.comp (sLocalBruhatInclusion F (S n)).toLinearMap)) :
    Continuous P := by
  apply GlobalBruhat.continuous_of_pure F (PolynormableSpace.withSeminorms ℂ R)
  intro ψ
  obtain ⟨T, hT⟩ := sLocalBruhatProjection_pure_eventually F ψ
  obtain ⟨n, hn⟩ := hSc T
  have he : (fun φ => P (GlobalBruhat.pure F ψ φ)) =
      (P.comp (sLocalBruhatInclusion F (S n)).toLinearMap) ∘
        (sLocalBruhatCorestrict F (S n)) ∘ (GlobalBruhat.pure F ψ) := by
    funext φ
    change _ = P (sLocalBruhatProjection F (S n) (GlobalBruhat.pure F ψ φ))
    rw [hT (S n) hn φ]
  rw [he]
  exact (hP n).comp ((sLocalBruhatCorestrict F (S n)).continuous.comp
    (GlobalBruhat.pure_continuous F ψ))

/-- Each global test comes from some finite set of places. -/
theorem globalBruhat_exhausted (x : GlobalBruhat F) :
    ∃ S, ∃ y : sLocalBruhatImage F S, sLocalBruhatInclusion F S y = x := by
  obtain ⟨S, hS, hSc⟩ := exists_sBruhatPlaceExhaustion F
  obtain ⟨n, hn⟩ := sLocalBruhat_exhaust_from F S hS hSc x
  exact ⟨S n, ⟨x, hn⟩, rfl⟩

/-- The global Schwartz–Bruhat topology is the locally convex final topology
along the padded maps from S-local stages. -/
theorem globalBruhat_finalTopology :
    locallyConvexFinalTopology
      (fun S : Finset (Place F) ↦ (sLocalBruhatInclusion F S).toLinearMap) =
        (inferInstance : TopologicalSpace (GlobalBruhat F)) := by
  let j (S : Finset (Place F)) := (sLocalBruhatInclusion F S).toLinearMap
  let G := GlobalBruhat F
  let t : TopologicalSpace G := inferInstance
  change locallyConvexFinalTopology j = t
  apply le_antisymm
  · apply continuous_id_iff_le.mp
    exact (locallyConvexFinal_continuous_iff j (LinearMap.id : G →ₗ[ℂ] G)).mpr
      fun S ↦ (sLocalBruhatInclusion F S).continuous
  · obtain ⟨S, _, hSc⟩ := exists_sBruhatPlaceExhaustion F
    have h : Continuous[t, locallyConvexFinalTopology j] (id : G → G) := by
      have ht : @PolynormableSpace ℂ G _ _ _ (locallyConvexFinalTopology j) :=
        @WithSeminorms.toPolynormableSpace ℂ G _ _ _ _ (locallyConvexFinalTopology j) _
          (locallyConvexFinal_withSeminorms j)
      exact @continuous_of_sLocalStages F _ _ G _ _ (locallyConvexFinalTopology j) ht
        S hSc (LinearMap.id : G →ₗ[ℂ] G)
        fun n ↦ locallyConvexFinal_stage_continuous j (S n)
    exact continuous_id_iff_le.mp h

private def globalBruhat_cofinalPresentation
    (S : ℕ → Finset (Place F)) (hS : Monotone S) (hSc : ∀ T, ∃ n, T ⊆ S n) :
    LinearInductivePresentation (GlobalBruhat F) (fun n => sLocalBruhatImage F (S n)) :=
  { incl := fun n => sLocalBruhatInclusion F (S n)
    transition := fun h => sLocalBruhatTransition F (hS h)
    injective_incl := fun _ => Subtype.val_injective
    incl_transition := fun _ _ => rfl
    exhaust := fun x => by
      obtain ⟨n, hn⟩ := sLocalBruhat_exhaust_from F S hS hSc x
      exact ⟨n, ⟨⟨x, hn⟩, rfl⟩⟩
    continuous_limit := fun l => ⟨fun h n => h.comp (sLocalBruhatInclusion F (S n)).continuous,
      continuous_of_sLocalStages F S hSc l⟩ }

/-- A cofinal tower of S-local spaces presents the global locally convex test space. -/
theorem globalBruhat_exists_cofinalPresentation :
    ∃ (S : ℕ → Finset (Place F))
      (D : LinearInductivePresentation (GlobalBruhat F) (fun n => sLocalBruhatImage F (S n))),
      (∀ n, IsEmbedding (D.incl n)) ∧
      (∀ p : Seminorm ℂ (GlobalBruhat F),
        (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p) := by
  obtain ⟨S, hS, hSc⟩ := exists_sBruhatPlaceExhaustion F
  let D := globalBruhat_cofinalPresentation F S hS hSc
  refine ⟨S, D, (fun _ => IsEmbedding.subtypeVal), fun p hp => ?_⟩
  let L := localBanachDenseMap p
  have hL : Continuous L := by
    apply continuous_of_sLocalStages F S hSc
    intro n
    apply (norm_withSeminorms ℂ (LocalBanach p)).continuous_of_continuous_comp
    intro _
    convert hp n using 1
    exact funext fun x => norm_localBanachDenseMap p (sLocalBruhatInclusion F (S n) x)
  simpa only [L, norm_localBanachDenseMap] using hL.norm

/-- Bounded families of adelic tests are contained in a single S-local
stage. The stage has the topology induced by the global space. -/
theorem sLocalBruhat_bounded_subset (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) :
    ∃ S : Finset (Place F), B ⊆ sLocalBruhatImage F S := by
  obtain ⟨S, hS, hSc⟩ := exists_sBruhatPlaceExhaustion F
  let D := globalBruhat_cofinalPresentation F S hS hSc
  obtain ⟨n, C, _, hC⟩ := (D.strict_bounded_iff
    (fun n => sLocalBruhatTransition_closed F (hS (Nat.le_succ n)))
    (fun n => IsEmbedding.subtypeVal)
    (continuous_of_sLocalStages F S hSc) B).mp hB
  refine ⟨S n, ?_⟩
  rw [← hC]
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Corollary 2.1.4.4. Every such system of continuous projections converges
uniformly on bounded sets, and is eventually the identity on each bounded set. -/
theorem sLocalBruhat_projections_eventually_eqOn_bounded
    (P : ∀ S : Finset (Place F), GlobalBruhat F →L[ℂ] GlobalBruhat F)
    (hP : ∀ S : Finset (Place F), Set.EqOn (P S) id (sLocalBruhatImage F S))
    (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) :
    ∀ᶠ S : Finset (Place F) in atTop, Set.EqOn (P S) id B := by
  obtain ⟨S, hS⟩ := sLocalBruhat_bounded_subset F B hB
  filter_upwards [eventually_ge_atTop S] with T hT
  exact (hP T).mono (hS.trans (sLocalBruhatImage_mono F hT))

end
end Masullo
