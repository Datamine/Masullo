import ModulatedDecayTranslations

open Function Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ)

namespace WholeBruhatDecayStage

set_option maxHeartbeats 1600000 in

/-- Compatible tuples of real twists form a closed subspace of a product
of elementary Schwartz spaces. -/
theorem twistTuple_isClosedEmbedding (hI : I.Nonempty) (p : WholeBruhatStage G) :
    IsClosedEmbedding (fun f : WholeBruhatDecayStage m I p ↦ fun a : I ↦ twist p a f) := by
  obtain ⟨a₀, ha₀⟩ := hI
  let a : I := ⟨a₀, ha₀⟩
  let T (f : WholeBruhatDecayStage m I p) := fun b : I ↦ twist p b f
  let w (b : I) (g : G) := Real.exp ((b : ℝ) * (m g).toAdd)
  have hw (b : I) (g : G) : w b g ≠ 0 := Real.exp_ne_zero _
  have hTw (f : WholeBruhatDecayStage m I p) (b : I) (g : G) :
      p.val.realize (T f b) g = w b g • f.val g :=
    congrFun (realize_twist p b f) g
  have hi : Injective T := by
    intro f h hfh
    apply algebraicEquiv.injective
    apply Subtype.ext
    funext g
    apply smul_right_injective ℂ (hw a g)
    change w a g • f.val g = w a g • h.val g
    exact (hTw f a g).symm.trans ((congrArg (fun u : I → p.val.Space ↦
      p.val.realize (u a) g) hfh).trans (hTw h a g))
  refine ⟨⟨?_, hi⟩, ?_⟩
  · exact inducing_iInf_to_pi (fun b : I ↦ (twist p b : WholeBruhatDecayStage m I p → p.val.Space))
  let S (b : I) (g : G) : Set (I → p.val.Space) :=
    {u | p.val.realize (u b) g = w b g • (w a g)⁻¹ • p.val.realize (u a) g}
  have hs : range T = ⋂ b, ⋂ g, S b g := by
    ext u
    simp only [Set.mem_iInter]
    constructor
    · rintro ⟨f, rfl⟩ b g
      change p.val.realize (T f b) g =
        w b g • (w a g)⁻¹ • p.val.realize (T f a) g
      rw [hTw, hTw, inv_smul_smul₀ (hw a g)]
    · intro hu
      let f (g : G) := (w a g)⁻¹ • p.val.realize (u a) g
      have hf (b : I) : modulatedExponentialWeight m b f ∈ p.val.realize.range :=
        ⟨u b, funext fun g ↦ hu b g⟩
      let F : WholeBruhatDecayStage m I p :=
        algebraicEquiv.symm ⟨f, (Submodule.mem_iInf _).mpr hf⟩
      refine ⟨F, funext fun b ↦ p.val.1.realizeSchwartz_injective p.val.2 ?_⟩
      exact (realize_twist p b F).trans (funext fun g ↦ (hu b g).symm)
  rw [hs]
  refine isClosed_iInter fun b ↦ isClosed_iInter fun g ↦ ?_
  have h (c : I) : Continuous fun u : I → p.val.Space ↦ p.val.realize (u c) g :=
    (p.val.continuous_realize_eval g).comp (continuous_apply c)
  exact isClosed_eq (h b) (((h a).const_smul ((w a g)⁻¹ : ℝ)).const_smul (w b g))

set_option maxHeartbeats 1600000 in
/-- The projective topology on a fixed whole-group decay stage is complete. -/
theorem complete (hI : I.Nonempty) (p : WholeBruhatStage G) :
    letI : UniformSpace (WholeBruhatDecayStage m I p) := IsTopologicalAddGroup.rightUniformSpace _
    CompleteSpace (WholeBruhatDecayStage m I p) := by
  let E := WholeBruhatDecayStage m I p
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let T : E →+ (I → p.val.Space) := {
    toFun f b := twist p b f
    map_zero' := funext fun b ↦ map_zero (twist (m := m) p b)
    map_add' f h := funext fun b ↦ map_add (twist p b) f h }
  have h := twistTuple_isClosedEmbedding m I hI p
  have hu := AddMonoidHom.isUniformInducing_of_isInducing
    (f := T) h.isEmbedding.isInducing
  letI : CompleteSpace p.val.Space := (@elementarySchwartz_isFrechet
    p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor
    p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete (Finite.of_fintype _)).2.2.2
  exact hu.completeSpace h.isClosed_range.isComplete

end WholeBruhatDecayStage

namespace ModulatedExponentialInductive

/-- Evaluation on the actual functions is continuous in the inductive topology. -/
def evaluation (hI : I.Nonempty) (g : G) : ModulatedExponentialInductive m I →L[ℂ] ℂ := by
  let L : ModulatedExponentialInductive m I →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ f.val g, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  refine ⟨L, (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G ↦ stageMap (m := m) (I := I) p) L).mpr fun p ↦ ?_⟩
  obtain ⟨a, ha⟩ := hI
  let b : I := ⟨a, ha⟩
  have hcont : Continuous (WholeBruhatDecayStage.twist p b :
      WholeBruhatDecayStage m I p → p.val.Space) :=
    (WholeBruhatDecayStage.continuous_iff id).mp continuous_id b
  refine (((p.val.continuous_realize_eval g).comp hcont).const_smul
    (Real.exp (a * (m g).toAdd))⁻¹).congr fun f ↦ ?_
  change (Real.exp (a * (m g).toAdd))⁻¹ •
    p.val.realize (WholeBruhatDecayStage.twist p b f) g = f.val g
  rw [congrFun (WholeBruhatDecayStage.realize_twist p b f) g]
  exact inv_smul_smul₀ (Real.exp_ne_zero _) _

theorem t2 (hI : I.Nonempty) : T2Space (ModulatedExponentialInductive m I) := by
  apply T2Space.of_injective_continuous (f := fun f : ModulatedExponentialInductive m I ↦ f.val)
  · intro f h he
    exact algebraicEquiv.injective (Subtype.ext he)
  · exact continuous_pi fun g ↦ (evaluation m I hI g).continuous

end ModulatedExponentialInductive

end
end Masullo
