import ModulatedDecayBounded
import BruhatWholeQuotientStages
import ElementarySchwartzCutoffs
import ElementarySchwartzStructure
import NuclearCriteria

open Bornology Function Set Topology
open scoped Uniformity

namespace Masullo

open LinearInductivePresentation

noncomputable section

set_option maxHeartbeats 1800000

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) {I : Set ℝ}

namespace WholeBruhatDecayStage

variable (p : WholeBruhatStage G)

private theorem twist_changeAbscissa (a b : I) (f : WholeBruhatDecayStage m I p)
    (y : ElementaryLCAModel p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor) :
    twist p b f y = Real.exp (((b : ℝ) - a) * p.logCoordinate m y) • twist p a f y := by
  obtain ⟨x,hx⟩ := p.coordinates_surjective (Multiplicative.ofAdd y)
  have he : (p.coordinates x).toAdd = y := congrArg Multiplicative.toAdd hx
  rw [← he, p.logCoordinate_coordinates]
  simp only [← p.realize_eq_coordinates, congrFun (realize_twist p b f) x,
    congrFun (realize_twist p a f) x, modulatedExponentialWeight_apply]
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

set_option maxHeartbeats 1500000 in
/-- Continuity of the twist at an intermediate abscissa follows from
continuity at two bracketing abscissae. -/
theorem continuous_twist_of_bracket {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : X →ₗ[ℂ] WholeBruhatDecayStage m I p) {a c b : I} (hac : a ≤ c) (hcb : c ≤ b)
    (ha : Continuous ((twist p a).comp L)) (hb : Continuous ((twist p b).comp L)) :
    Continuous ((twist p c).comp L) := by
  let l := p.logCoordinate m
  have hl : Continuous l := continuous_toAdd.comp
    (((p.val.1.descendHom m (p.val.1.modulation_eq_one_on_kernel m)).continuous.comp
      p.val.2.equiv.symm.continuous).comp continuous_ofAdd)
  apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
  intro i
  obtain ⟨q₁,q₂,h₁,h₂,he⟩ := exists_elementarySchwartz_exponential_between_bound l hl hac hcb i
  refine Seminorm.continuous_of_le (q := q₁.comp ((twist p a).comp L) + q₂.comp ((twist p b).comp L))
    ((h₁.comp ha).add (h₂.comp hb)) fun f => ?_
  exact he (twist p a (L f)) (twist p c (L f)) (twist p b (L f))
    (twist_changeAbscissa m p a c (L f)) (twist_changeAbscissa m p b c (L f))

/-- Restricting the tuple of all twists to a bracketing set preserves
the intrinsic topology of each decay stage. -/
theorem twistTuple_isEmbedding_of_brackets (hI : I.Nonempty) (J : Set I)
    (hJ : ∀ c : I, ∃ a b : J, a.val ≤ c ∧ c ≤ b.val) :
    IsEmbedding (fun (f : WholeBruhatDecayStage m I p) (a : J) => twist p a.val f) := by
  let E := WholeBruhatDecayStage m I p
  let T : E →ₗ[ℂ] (J → p.val.Space) := LinearMap.pi fun a => twist p a.val
  have hc : Continuous T := continuous_pi fun a => (continuous_iff (id : E → E)).mp continuous_id a.val
  have hi : Injective T := by
    intro f g hfg
    obtain ⟨a, _, _, _⟩ := hJ ⟨hI.choose,hI.choose_spec⟩
    apply algebraicEquiv.injective
    apply Subtype.ext
    funext x
    have h := congrArg (fun v : J → p.val.Space => p.val.realize (v a) x) hfg
    change p.val.realize (twist p a.val f) x = p.val.realize (twist p a.val g) x at h
    rw [congrFun (realize_twist p a.val f) x, congrFun (realize_twist p a.val g) x,
      modulatedExponentialWeight_apply, modulatedExponentialWeight_apply] at h
    exact smul_right_injective ℂ (Real.exp_ne_zero _) h
  refine ⟨⟨le_antisymm hc.le_induced ?_⟩,hi⟩
  let E₀ := E
  let t : TopologicalSpace E := inferInstance
  letI : TopologicalSpace E₀ := TopologicalSpace.induced T inferInstance
  letI : IsTopologicalAddGroup E₀ := IsInducing.topologicalAddGroup T.toAddMonoidHom (IsInducing.induced T)
  let L : E₀ →ₗ[ℂ] E := LinearMap.id
  have hL : Continuous[TopologicalSpace.induced T inferInstance,t] L := (continuous_iff L).mpr fun c => by
    obtain ⟨a,b,hac,hcb⟩ := hJ c
    have hT : Continuous (T : E₀ → (J → p.val.Space)) := continuous_induced_dom
    exact continuous_twist_of_bracket m p L hac hcb
      ((continuous_apply a).comp hT) ((continuous_apply b).comp hT)
  change TopologicalSpace.induced T inferInstance ≤ t
  simpa only [show (L : E₀ → E) = id from rfl, induced_id] using hL.le_induced

end WholeBruhatDecayStage

/-- Every real set has a countable bracketing set. Any included
least or greatest point is included in the bracketing set. -/
theorem exists_countable_abscissa_brackets (I : Set ℝ) :
    ∃ J : Set I, J.Countable ∧ ∀ c : I, ∃ a b : J, a.val ≤ c ∧ c ≤ b.val := by
  obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense (α := I)
  let L := {a : I | ∀ b : I, a ≤ b}
  let U := {a : I | ∀ b : I, b ≤ a}
  let J := D ∪ L ∪ U
  have hL : L.Subsingleton := fun _ hx _ hy => le_antisymm (hx _) (hy _)
  have hU : U.Subsingleton := fun _ hx _ hy => le_antisymm (hy _) (hx _)
  refine ⟨J,(hD.union hL.countable).union hU.countable,fun c => ?_⟩
  have hlo : ∃ a : J, a.val ≤ c := by
    by_cases hc : c ∈ L
    · exact ⟨⟨c,Or.inl (Or.inr hc)⟩,le_rfl⟩
    · have hne : (Iio c).Nonempty := by
        by_contra he
        apply hc
        intro b
        exact le_of_not_gt fun hb => he ⟨b,hb⟩
      have ho : IsOpen (Iio c : Set I) :=
        (isOpen_Iio (a := (c : ℝ))).preimage continuous_subtype_val
      obtain ⟨a,hda,ha⟩ := hd.exists_mem_open ho hne
      exact ⟨⟨a,Or.inl (Or.inl hda)⟩,ha.le⟩
  have hhi : ∃ b : J, c ≤ b.val := by
    by_cases hc : c ∈ U
    · exact ⟨⟨c,Or.inr hc⟩,le_rfl⟩
    · have hne : (Ioi c).Nonempty := by
        by_contra he
        apply hc
        intro b
        exact le_of_not_gt fun hb => he ⟨b,hb⟩
      have ho : IsOpen (Ioi c : Set I) :=
        (isOpen_Ioi (a := (c : ℝ))).preimage continuous_subtype_val
      obtain ⟨b,hdb,hb⟩ := hd.exists_mem_open ho hne
      exact ⟨⟨b,Or.inl (Or.inl hdb)⟩,hb.le⟩
  obtain ⟨a,ha⟩ := hlo
  obtain ⟨b,hb⟩ := hhi
  exact ⟨a,b,ha,hb⟩

set_option maxHeartbeats 2800000 in
/-- The boundedness test needs only bracketing twists, including the endpoints
when they belong to the interval. A countable bracketing set always exists. -/
theorem modulatedDecay_bounded_iff_bracketing_twists [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (J : Set I) (hJ : ∀ c : I, ∃ a b : J, a.val ≤ c ∧ c ≤ b.val)
    (B : Set (ModulatedExponentialInductive m I)) :
    IsVonNBounded ℂ B ↔ ∀ a : J, IsVonNBounded ℂ (modulatedDecayTwistCLM m I a.val '' B) := by
  refine ⟨fun h a => h.image (modulatedDecayTwistCLM m I a.val), fun h => ?_⟩
  obtain ⟨a,_,_,_⟩ := hJ ⟨hI.choose,hI.choose_spec⟩
  obtain ⟨p,hp⟩ := modulatedDecay_range_stage_of_bounded_twist m I hm hms a.val B (h a)
  let E := WholeBruhatDecayStage m I p
  let j : E →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨ModulatedExponentialInductive.stageMap p, ModulatedExponentialInductive.stageMap_continuous p⟩
  let C := j ⁻¹' B
  let T : E →L[ℂ] (J → p.val.Space) :=
    ⟨LinearMap.pi (fun b : J => WholeBruhatDecayStage.twist p b.val),
      (WholeBruhatDecayStage.twistTuple_isEmbedding_of_brackets m p hI J hJ).continuous⟩
  have hT : IsEmbedding T := WholeBruhatDecayStage.twistTuple_isEmbedding_of_brackets m p hI J hJ
  have hTC : IsVonNBounded ℂ (T '' C) := by
    apply isVonNBounded_pi_iff.mpr
    intro b
    have H := bounded_preimage_of_embedding p.val.inclusionCLM
      ((bruhatSchwartz_strict (G := G)).2.1 p.val) (h b)
    apply H.subset
    rintro v ⟨_,⟨u,hu,rfl⟩,hv⟩
    change WholeBruhatDecayStage.twist p b.val u = v at hv
    subst v
    refine ⟨j u,hu,?_⟩
    apply Subtype.ext
    exact (WholeBruhatDecayStage.realize_twist p b.val u).symm
  have hsub : C ⊆ T ⁻¹' (T '' C) := fun _ hu => mem_image_of_mem T hu
  have hC := (bounded_preimage_of_embedding T hT hTC).subset hsub
  have he : j '' C = B := image_preimage_eq_of_subset hp
  exact he ▸ hC.image j

/-- A fixed decay stage is metrizable and second-countable. -/
theorem wholeBruhatDecayStage_metrizable_secondCountable
    (hI : I.Nonempty) (p : WholeBruhatStage G) :
    TopologicalSpace.MetrizableSpace (WholeBruhatDecayStage m I p) ∧
      SecondCountableTopology (WholeBruhatDecayStage m I p) := by
  obtain ⟨J,hJ,hab⟩ := exists_countable_abscissa_brackets I
  letI : Countable J := hJ.to_subtype
  let E := p.val.Space
  letI : TopologicalSpace.MetrizableSpace E := elementarySchwartz_isFrechet.2.2.1
  letI : TopologicalSpace.SeparableSpace E :=
    nuclearLocallyConvex_separable_of_firstCountable.{0,u} elementarySchwartz_nuclear
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  have he := WholeBruhatDecayStage.twistTuple_isEmbedding_of_brackets m p hI J hab
  exact ⟨he.metrizableSpace,he.secondCountableTopology⟩

/-- Every fixed quotient decay stage is separable nuclear Fréchet. -/
theorem wholeBruhatDecayStage_separableNuclearFrechet (hI : I.Nonempty) (p : WholeBruhatStage G) :
    TopologicalSpace.SeparableSpace (WholeBruhatDecayStage m I p) ∧
      NuclearLocallyConvex.{u,u} (WholeBruhatDecayStage m I p) ∧
      IsFrechetTVS (WholeBruhatDecayStage m I p) := by
  obtain ⟨hM,hSC⟩ := wholeBruhatDecayStage_metrizable_secondCountable m hI p
  letI := hSC
  let E := WholeBruhatDecayStage m I p
  let T : E →L[ℂ] (I → p.val.Space) :=
    ⟨LinearMap.pi (WholeBruhatDecayStage.twist p),
      (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI p).continuous⟩
  have hT : IsEmbedding T := (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI p).isEmbedding
  let e := LinearEquiv.ofInjective T.toLinearMap hT.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hT.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let eL : E ≃L[ℂ] T.toLinearMap.range := ⟨e,h.continuous,h.symm.continuous⟩
  have hN : NuclearLocallyConvex.{u,0} (I → p.val.Space) :=
    nuclearLocallyConvex_pi fun _ => elementarySchwartz_nuclear
  exact ⟨inferInstance, nuclearLocallyConvex_of_equiv eL.symm
    (nuclearLocallyConvex_submodule hN T.toLinearMap.range),
    ⟨inferInstance,inferInstance,hM,WholeBruhatDecayStage.complete m I hI p⟩⟩

/-- Proposition D.3.3.10(1). Bounded subsets carry a separable metrizable
subspace topology. -/
theorem modulatedDecay_bounded_separable_metrizable [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hI : I.Nonempty)
    (B : Set (ModulatedExponentialInductive m I)) (hB : IsVonNBounded ℂ B) :
    TopologicalSpace.SeparableSpace B ∧ TopologicalSpace.MetrizableSpace B := by
  let a : I := ⟨hI.choose,hI.choose_spec⟩
  obtain ⟨p,hp⟩ := modulatedDecay_range_stage_of_bounded_twist m I hm hms a B
    (hB.image (modulatedDecayTwistCLM m I a))
  obtain ⟨hM,hSC⟩ := wholeBruhatDecayStage_metrizable_secondCountable m hI p
  letI := hM
  letI := hSC
  let e := (wholeBruhatDecayStage_isEmbedding m I hI p).homeomorphOfSubsetRange hp
  letI := e.symm.isEmbedding.secondCountableTopology
  exact ⟨inferInstance,e.symm.isEmbedding.metrizableSpace⟩


end

end Masullo
