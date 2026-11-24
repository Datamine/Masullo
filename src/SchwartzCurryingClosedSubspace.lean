import EuclideanSchwartzUncurrying
import Mathlib.Analysis.LocallyConvex.HahnBanach

open Function Set Topology UniformSpace
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The joint Schwartz space with all second-variable slices in a submodule. -/
def schwartzWithSlicesIn (K : Submodule ℂ 𝓢(Y, ℂ)) : Submodule ℂ 𝓢(X × Y, ℂ) where
  carrier := {f | ∀ x, schwartzSlice x f ∈ K}
  zero_mem' := fun x => by simp
  add_mem' := fun hf hg x => by simpa only [map_add] using K.add_mem (hf x) (hg x)
  smul_mem' := fun c _ hf x => by simpa only [map_smul] using K.smul_mem c (hf x)

theorem isClosed_schwartzWithSlicesIn (K : Submodule ℂ 𝓢(Y, ℂ))
    (hK : IsClosed (K : Set 𝓢(Y, ℂ))) :
    IsClosed (schwartzWithSlicesIn (X := X) K : Set 𝓢(X × Y, ℂ)) := by
  have he : (schwartzWithSlicesIn (X := X) K : Set 𝓢(X × Y, ℂ)) =
      ⋂ x : X, schwartzSlice x ⁻¹' K := by
    ext f
    change (∀ x, schwartzSlice x f ∈ K) ↔ _
    simp only [mem_iInter, mem_preimage, SetLike.mem_coe]
  rw [he]
  exact isClosed_iInter fun x => hK.preimage (schwartzSlice x).continuous

/-- Taking a fixed slice gives a continuous linear map into the chosen subspace. -/
def schwartzWithSlicesIn_slice (K : Submodule ℂ 𝓢(Y, ℂ)) (x : X) :
    schwartzWithSlicesIn (X := X) K →L[ℂ] K :=
  ((schwartzSlice x).comp (schwartzWithSlicesIn (X := X) K).subtypeL).codRestrict K
    (fun f => f.property x)

private theorem exists_schwartz_slice_linear_of_closed_subspace {a : ℕ}
    (K : Submodule ℂ 𝓢(Y, ℂ)) {I : Type*} {p : SeminormFamily ℂ K I}
    (hp : WithSeminorms p) :
    ∃ L : schwartzWithSlicesIn (X := EuclideanSpace ℝ (Fin a)) K →ₗ[ℂ]
        localBanachSchwartz (X := EuclideanSpace ℝ (Fin a)) hp,
      ∀ f x i, (L f).val i x = localBanachDenseMap (p i) (schwartzWithSlicesIn_slice K x f) := by
  let X := EuclideanSpace ℝ (Fin a)
  let A := schwartzWithSlicesIn (X := X) K
  let B := localBanachSchwartz (X := X) hp
  let V (x : X) := schwartzWithSlicesIn_slice K x
  letI : PolynormableSpace ℂ 𝓢(Y, ℂ) := (schwartz_withSeminorms ℂ Y ℂ).toPolynormableSpace
  have h (f : A) := (localBanach_schwartz_iff_scalar hp (fun x => V x f)).mpr (by
    intro l
    obtain ⟨l', hl'⟩ := StrongDual.exists_extension K l
    obtain ⟨g, hg⟩ := exists_schwartz_schwartzSlice_scalar f.val l'
    exact ⟨g, fun x => (hg x).trans (hl' (V x f))⟩)
  have hF (f : A) : ∃ g : B, ∀ x i, g.val i x = localBanachDenseMap (p i) (V x f) := by
    choose F hF using h f
    refine ⟨⟨F, fun x => ⟨V x f, (funext (fun i => hF i x)).symm⟩⟩, fun x i => hF i x⟩
  choose C hC using hF
  let E : A →ₗ[ℂ] B :=
    { toFun := C
      map_add' := fun f g => by
        apply Subtype.ext
        funext i
        apply SchwartzMap.ext
        intro x
        change (C (f + g)).val i x = (C f).val i x + (C g).val i x
        simp only [hC, map_add]
      map_smul' := fun c f => by
        apply Subtype.ext
        funext i
        apply SchwartzMap.ext
        intro x
        change (C (c • f)).val i x = c • (C f).val i x
        simp only [hC, map_smul] }
  exact ⟨E, hC⟩

set_option maxHeartbeats 1500000 in
/-- Euclidean currying with values in a closed subspace of the second
Schwartz space, using a countable defining family on that subspace. -/
theorem exists_schwartzCurry_closedSubspaceEquiv {a b : ℕ} {I : Type*} [Countable I]
    (K : Submodule ℂ 𝓢(EuclideanSpace ℝ (Fin b), ℂ))
    (hK : IsClosed (K : Set 𝓢(EuclideanSpace ℝ (Fin b), ℂ)))
    {p : SeminormFamily ℂ K I} (hp : WithSeminorms p) :
    ∃ C : (schwartzWithSlicesIn (X := EuclideanSpace ℝ (Fin a)) K) ≃L[ℂ]
        (localBanachSchwartz (X := EuclideanSpace ℝ (Fin a)) hp),
      ∀ f x i, (C f).val i x = localBanachDenseMap (p i) (schwartzWithSlicesIn_slice K x f) := by
  let X := EuclideanSpace ℝ (Fin a)
  let Y := EuclideanSpace ℝ (Fin b)
  let A := schwartzWithSlicesIn (X := X) K
  let B := localBanachSchwartz (X := X) hp
  let V (x : X) := schwartzWithSlicesIn_slice K x
  obtain ⟨C, hC⟩ := exists_schwartz_slice_linear_of_closed_subspace (a := a) K hp
  have hai : Injective C := by
    intro f g h
    apply Subtype.ext
    apply SchwartzMap.ext
    rintro ⟨x, y⟩
    have he : V x f = V x g := by
      apply (localBanachDiagonal_isInducing hp).isEmbedding.injective
      funext i
      exact (hC f x i).symm.trans ((congrArg (fun g : B => g.val i x) h).trans (hC g x i))
    exact congrArg (fun z : K => z.val y) he
  have has : Surjective C := by
    intro g
    have hg (x : X) : ∃ u : K, ∀ i, g.val i x = localBanachDenseMap (p i) u := by
      obtain ⟨u, hu⟩ := g.property x
      exact ⟨u, fun i => (congrFun hu i).symm⟩
    choose u hu using hg
    have hweak := (localBanach_schwartz_iff_scalar hp u).mp (fun i => ⟨g.val i, fun x => hu x i⟩)
    have hSch := (localBanach_schwartz_iff_scalar (schwartz_withSeminorms ℂ Y ℂ)
      (fun x => (u x).val)).mpr (fun l => hweak (l.comp K.subtypeL))
    obtain ⟨f, hf⟩ := exists_schwartzUncurry (schwartz_withSeminorms ℂ Y ℂ) _ hSch
    have hs (x : X) : schwartzSlice x f = (u x).val := SchwartzMap.ext (hf x)
    let F : A := ⟨f, fun x => hs x ▸ (u x).property⟩
    refine ⟨F, ?_⟩
    apply Subtype.ext
    funext i
    apply SchwartzMap.ext
    intro x
    rw [hC F x i]
    have he : V x F = u x := Subtype.ext (hs x)
    rw [he]
    exact (hu x i).symm
  have hgraph : IsClosed (C.graph : Set (A × B)) := by
    have he : (C.graph : Set (A × B)) = ⋂ i : I, ⋂ x : X,
        {fg : A × B | fg.2.val i x = localBanachDenseMap (p i) (V x fg.1)} := by
      ext fg
      change fg ∈ C.graph ↔ _
      rw [C.mem_graph_iff, mem_iInter]
      constructor
      · intro he i
        rw [mem_iInter]
        intro x
        exact (congrArg (fun g : B => g.val i x) he).trans (hC fg.1 x i)
      · intro h
        apply Subtype.ext
        funext i
        apply SchwartzMap.ext
        intro x
        exact (mem_iInter.mp (h i) x).trans (hC fg.1 x i).symm
    rw [he]
    refine isClosed_iInter fun i => isClosed_iInter fun x => ?_
    have h₂ : Continuous (fun g : B => g.val i x) :=
      (((BoundedContinuousFunction.evalCLM ℂ x).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X (LocalBanach (p i)))).continuous.comp
        ((continuous_apply i).comp continuous_subtype_val))
    let M := (localBanachMap (p i) (hp.continuous_seminorm i)).comp (V x)
    exact isClosed_eq (h₂.comp continuous_snd) (M.continuous.comp continuous_fst)
  letI : CompleteSpace 𝓢(X × Y, ℂ) := completeSpace_schwartzMap
  letI : CompleteSpace 𝓢(Y, ℂ) := completeSpace_schwartzMap
  letI : CompleteSpace A := (isClosed_schwartzWithSlicesIn (X := X) K hK).isComplete.completeSpace_coe
  letI : CompleteSpace K := hK.isComplete.completeSpace_coe
  letI : IsUniformAddGroup A := IsUniformInducing.isUniformAddGroup A.subtype
    isUniformEmbedding_subtype_val.isUniformInducing
  letI : IsUniformAddGroup K := IsUniformInducing.isUniformAddGroup K.subtype
    isUniformEmbedding_subtype_val.isUniformInducing
  letI : IsUniformAddGroup B := IsUniformInducing.isUniformAddGroup B.subtype
    isUniformEmbedding_subtype_val.isUniformInducing
  letI : @CompleteSpace K (@IsTopologicalAddGroup.rightUniformSpace _ _ _ hp.topologicalAddGroup) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  letI : CompleteSpace B := localBanachSchwartz_complete hp inferInstance
  have hB := localBanachSchwartz_frechet (X := X) hp inferInstance
  letI : TopologicalSpace.MetrizableSpace B := hB.2.2.1
  letI : FirstCountableTopology 𝓢(X × Y, ℂ) :=
    (schwartz_withSeminorms ℂ (X × Y) ℂ).firstCountableTopology
  letI : FirstCountableTopology A := IsInducing.subtypeVal.firstCountableTopology
  letI : ContinuousSMul ℂ B := (schwartzIntoSubmodule_withSeminorms
    (X := X) (localBanachDiagonal hp).range).continuousSMul
  let D : A →L[ℂ] B := ⟨C, frechet_continuous_of_closed_graph C hgraph⟩
  let L := LinearEquiv.ofBijective C ⟨hai, has⟩
  letI : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  letI : (uniformity B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace B := BaireSpace.of_completelyPseudoMetrizable
  have hOpen : IsOpenMap D := isOpenMap_of_surjective_complete_baire D has
  exact ⟨⟨L, D.continuous, L.toEquiv.continuous_symm_iff.mpr hOpen⟩, hC⟩


end
end Masullo
