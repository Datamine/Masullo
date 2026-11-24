import ModulatedExponentialInductive

open Function Set

namespace Masullo

noncomputable section

set_option maxHeartbeats 1000000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

private theorem restrict_decay_weights_le (m : G →ₜ* Multiplicative ℝ)
    {I J : Set ℝ} (hJI : J ⊆ I) :
    modulatedExponentialDecaySubmodule m I ≤ modulatedExponentialDecaySubmodule m J := by
  intro f hf
  refine (Submodule.mem_iInf _).2 fun a ↦ ?_
  exact (Submodule.mem_iInf _).1 hf (⟨a.val, hJI a.property⟩ : I)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem restrict_stage_weights_le (m : G →ₜ* Multiplicative ℝ)
    (p : WholeBruhatStage G) {I J : Set ℝ} (hJI : J ⊆ I) :
    wholeBruhatDecayStageSubmodule m I p ≤ wholeBruhatDecayStageSubmodule m J p := by
  intro f hf
  refine (Submodule.mem_iInf _).2 fun a ↦ ?_
  exact (Submodule.mem_iInf _).1 hf (⟨a.val, hJI a.property⟩ : I)

/-- Restriction of the abscissa set is continuous for the inductive decay
topologies since every stage restriction is continuous in all its twists. -/
def modulatedDecay_restrict (m : G →ₜ* Multiplicative ℝ) {I J : Set ℝ} (hJI : J ⊆ I) :
    ModulatedExponentialInductive m I →L[ℂ] ModulatedExponentialInductive m J := by
  let Ei := ModulatedExponentialInductive.algebraicEquiv (m := m) (I := I)
  let Ej := ModulatedExponentialInductive.algebraicEquiv (m := m) (I := J)
  let L := Ej.symm.toLinearMap.comp ((Submodule.inclusion (restrict_decay_weights_le m hJI)).comp Ei.toLinearMap)
  refine ⟨L, (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G ↦ ModulatedExponentialInductive.stageMap (m := m) (I := I) p) L).2
    fun p ↦ ?_⟩
  let pi := WholeBruhatDecayStage.algebraicEquiv (m := m) (I := I) (p := p)
  let pj := WholeBruhatDecayStage.algebraicEquiv (m := m) (I := J) (p := p)
  let R := pj.symm.toLinearMap.comp
    ((Submodule.inclusion (restrict_stage_weights_le m p hJI)).comp pi.toLinearMap)
  have hR : Continuous R := by
    apply (WholeBruhatDecayStage.continuous_iff _).2
    intro a
    let a' : I := ⟨a.val, hJI a.property⟩
    have he : WholeBruhatDecayStage.twist p a ∘ R = WholeBruhatDecayStage.twist p a' := by
      funext u
      apply p.val.1.realizeSchwartz_injective p.val.2
      change p.val.realize (WholeBruhatDecayStage.twist p a (R u)) =
        p.val.realize (WholeBruhatDecayStage.twist p a' u)
      rw [WholeBruhatDecayStage.realize_twist, WholeBruhatDecayStage.realize_twist]
      rfl
    rw [he]
    exact (WholeBruhatDecayStage.continuous_iff (id : WholeBruhatDecayStage m I p → _)).1 continuous_id a'
  have hst := ModulatedExponentialInductive.stageMap_continuous (m := m) (I := J) p
  exact (hst.comp hR).congr fun f ↦ Ej.injective (Subtype.ext rfl)

@[simp] theorem modulatedDecay_restrict_apply (m : G →ₜ* Multiplicative ℝ) {I J : Set ℝ}
    (hJI : J ⊆ I) (f : ModulatedExponentialInductive m I) :
    (modulatedDecay_restrict m hJI f).val = f.val := rfl

/-- Entire-decay tests are dense in the inductive space for a nonempty
abscissa set, since all compact tests come from the entire-decay space. -/
theorem modulatedDecay_restrict_univ_dense (m : G →ₜ* Multiplicative ℝ)
    (hm : IsProperMap m) (hms : Surjective m) (I : Set ℝ) (hI : I.Nonempty) :
    DenseRange (modulatedDecay_restrict m (subset_univ I)) := by
  have hd := (bruhatCompactTest_inductiveDecay_continuous_injective_dense m I hm hms hI).2.2
  apply hd.mono
  rintro _ ⟨f, rfl⟩
  refine ⟨bruhatCompactTest_toModulatedExponentialInductive m univ f, ?_⟩
  apply ModulatedExponentialInductive.algebraicEquiv.injective
  exact Subtype.ext rfl

/-- A continuous map on an interval-weighted space is determined by its
values on the entire-decay tests. -/
theorem modulatedDecay_continuous_eq_of_entireDecay
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (I : Set ℝ) (hI : I.Nonempty) {A B : ModulatedExponentialInductive m I → Y}
    (hA : Continuous A) (hB : Continuous B)
    (h : ∀ f : ModulatedExponentialInductive m (univ : Set ℝ),
      A (modulatedDecay_restrict m (subset_univ I) f) = B (modulatedDecay_restrict m (subset_univ I) f)) :
    A = B := by
  apply (modulatedDecay_restrict_univ_dense m hm hms I hI).equalizer hA hB
  exact funext h

end

end Masullo
