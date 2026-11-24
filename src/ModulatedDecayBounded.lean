import ModulatedDecayComplete
import ModulatedDecayIsotypes
import BruhatSchwartzStrict

open Bornology Function Set Topology

namespace Masullo

open LinearInductivePresentation

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

set_option maxHeartbeats 1500000 in
/-- Boundedness of one twist puts the entire family in a common decay stage. -/
theorem modulatedDecay_range_stage_of_bounded_twist (hm : IsProperMap m) (hms : Surjective m)
    (a : I) (B : Set (ModulatedExponentialInductive m I))
    (hB : IsVonNBounded ℂ (modulatedDecayTwistCLM m I a '' B)) :
    ∃ p : WholeBruhatStage G,
      B ⊆ range (ModulatedExponentialInductive.stageMap (m := m) (I := I) p) := by
  obtain ⟨q,C₀,_,hC₀⟩ := (bruhatSchwartz_strict (G := G)).2.2 _ hB
  obtain ⟨p,hqp⟩ := exists_wholeBruhatStage_refinement m hm hms q
  let j : WholeBruhatDecayStage m I p →ₗ[ℂ] ModulatedExponentialInductive m I :=
    ModulatedExponentialInductive.stageMap p
  refine ⟨p, ?_⟩
  intro f hf
  have hfa : modulatedDecayTwistCLM m I a f ∈ q.inclusionCLM '' C₀ :=
    hC₀.symm ▸ mem_image_of_mem _ hf
  obtain ⟨v,_,hv⟩ := hfa
  let u := q.transition p.val hqp v
  have he : p.val.realize u = modulatedExponentialWeight m a f.val := by
    have ht := (q.inclusion_transition p.val hqp v).trans hv
    exact congrArg Subtype.val ht
  let w : WholeBruhatDecayStage m I p :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨f.val,
      (Submodule.mem_iInf _).mpr fun b => wholeBruhatStage_exponential_twist_mem_range
        m p ⟨u,he⟩ (modulatedDecayTwistCLM m I b f).property⟩
  exact ⟨w,ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext rfl)⟩

set_option maxHeartbeats 2600000 in
/-- Proposition D.3.3.10. Boundedness of all twists forces a common
whole-group quotient, on which the whole family is bounded. -/
theorem modulatedDecay_bounded_lift_of_twists (hm : IsProperMap m) (hms : Surjective m)
    (hI : I.Nonempty) (B : Set (ModulatedExponentialInductive m I))
    (hB : ∀ a : I, IsVonNBounded ℂ (modulatedDecayTwistCLM m I a '' B)) :
    ∃ (p : WholeBruhatStage G) (C : Set (WholeBruhatDecayStage m I p)),
      IsVonNBounded ℂ C ∧ ModulatedExponentialInductive.stageMap p '' C = B := by
  let a : I := ⟨hI.choose,hI.choose_spec⟩
  obtain ⟨p,hp⟩ := modulatedDecay_range_stage_of_bounded_twist m I hm hms a B (hB a)
  let j : WholeBruhatDecayStage m I p →ₗ[ℂ] ModulatedExponentialInductive m I :=
    ModulatedExponentialInductive.stageMap p
  let C := j ⁻¹' B
  have hC : j '' C = B := image_preimage_eq_of_subset hp
  let T : WholeBruhatDecayStage m I p →L[ℂ] (I → p.val.Space) :=
    ⟨LinearMap.pi (WholeBruhatDecayStage.twist p),
      (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI p).continuous⟩
  have hT : IsEmbedding T := (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI p).isEmbedding
  have hBC : IsVonNBounded ℂ (T '' C) := by
    apply isVonNBounded_pi_iff.mpr
    intro b
    have hb₀ := bounded_preimage_of_embedding p.val.inclusionCLM
      ((bruhatSchwartz_strict (G := G)).2.1 p.val) (hB b)
    apply hb₀.subset
    rintro z ⟨y,⟨f,hf,rfl⟩,hz⟩
    change WholeBruhatDecayStage.twist p b f = z at hz
    subst z
    refine ⟨j f,hf,?_⟩
    apply Subtype.ext
    exact (WholeBruhatDecayStage.realize_twist p b f).symm
  refine ⟨p,C,(bounded_preimage_of_embedding T hT hBC).subset ?_,hC⟩
  exact fun f hf => ⟨f,hf,rfl⟩

/-- Proposition D.3.3.10(2) and the all-abscissae direction of (3).
Boundedness in the inductive limit is detected by the individual twists. -/
theorem modulatedDecay_bounded_iff_twists (hm : IsProperMap m) (hms : Surjective m)
    (hI : I.Nonempty) (B : Set (ModulatedExponentialInductive m I)) :
    IsVonNBounded ℂ B ↔ ∀ a : I, IsVonNBounded ℂ (modulatedDecayTwistCLM m I a '' B) := by
  refine ⟨fun h a => h.image (modulatedDecayTwistCLM m I a),fun h => ?_⟩
  obtain ⟨p,C,hC,he⟩ := modulatedDecay_bounded_lift_of_twists m I hm hms hI B h
  let L : WholeBruhatDecayStage m I p →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨ModulatedExponentialInductive.stageMap p,ModulatedExponentialInductive.stageMap_continuous p⟩
  exact he ▸ hC.image L

/-- The projective and inductive topologies have the same bounded sets. -/
theorem modulatedDecay_bounded_iff_projective (hm : IsProperMap m) (hms : Surjective m)
    (hI : I.Nonempty) (B : Set (ModulatedExponentialInductive m I)) :
    let T (f : ModulatedExponentialInductive m I) (a : I) := modulatedDecayTwistCLM m I a f
    IsVonNBounded ℂ B ↔ @IsVonNBounded ℂ (ModulatedExponentialInductive m I) _ _ _
      (TopologicalSpace.induced T inferInstance) B := by
  intro T
  have hinj : Injective T := by
    intro f g hfg
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext x
    let a : I := ⟨hI.choose,hI.choose_spec⟩
    have he := congrArg (fun v : I → BruhatSchwartz G => (v a).val x) hfg
    change Real.exp (a.val * (m x).toAdd) • f.val x =
      Real.exp (a.val * (m x).toAdd) • g.val x at he
    exact smul_right_injective ℂ (Real.exp_ne_zero _) he
  rw [modulatedDecay_bounded_iff_twists m I hm hms hI B]
  let E := ModulatedExponentialInductive m I
  let T₀ : E →ₗ[ℂ] (I → BruhatSchwartz G) :=
    LinearMap.pi (fun a => (modulatedDecayTwistCLM m I a).toLinearMap)
  let t := TopologicalSpace.induced T inferInstance
  letI : TopologicalSpace E := TopologicalSpace.induced T inferInstance
  let L : E →L[ℂ] (I → BruhatSchwartz G) :=
    ⟨T₀, show Continuous[t,inferInstance] T from continuous_induced_dom⟩
  have hL : IsEmbedding L := ⟨IsInducing.induced T,hinj⟩
  have hImage (a : I) : Function.eval a '' (L '' B) = modulatedDecayTwistCLM m I a '' B :=
    image_image _ _ _
  constructor
  · intro h
    have hB : IsVonNBounded ℂ (L '' B) := isVonNBounded_pi_iff.mpr fun a => hImage a ▸ h a
    have hsub : B ⊆ L ⁻¹' (L '' B) := fun _ hx => mem_image_of_mem L hx
    exact (bounded_preimage_of_embedding L hL hB).subset hsub
  · intro h a
    exact hImage a ▸ (isVonNBounded_pi_iff.mp (h.image L) a)

/-- The intrinsic topology of a fixed whole-group decay stage agrees with
the topology induced by its inclusion into the inductive limit. -/
theorem wholeBruhatDecayStage_isEmbedding (hI : I.Nonempty) (p : WholeBruhatStage G) :
    IsEmbedding (ModulatedExponentialInductive.stageMap (m := m) (I := I) p) := by
  let j := ModulatedExponentialInductive.stageMap (m := m) (I := I) p
  let T (f : ModulatedExponentialInductive m I) (a : I) := modulatedDecayTwistCLM m I a f
  let S (f : WholeBruhatDecayStage m I p) (a : I) := WholeBruhatDecayStage.twist p a f
  let K (v : I → p.val.Space) (a : I) := p.val.inclusionCLM (v a)
  have hK : IsEmbedding K := IsEmbedding.piMap fun _ =>
    (bruhatSchwartz_strict (G := G)).2.1 p.val
  have hKS : IsEmbedding (K ∘ S) := hK.comp
    (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI p).isEmbedding
  have he : T ∘ j = K ∘ S := by
    funext f a
    apply Subtype.ext
    exact (WholeBruhatDecayStage.realize_twist p a f).symm
  have hTj : IsEmbedding (T ∘ j) := he ▸ hKS
  exact ⟨IsInducing.of_comp (ModulatedExponentialInductive.stageMap_continuous p)
    (continuous_pi fun a => (modulatedDecayTwistCLM m I a).continuous) hTj.isInducing,
    hTj.injective.of_comp⟩

end

end Masullo
