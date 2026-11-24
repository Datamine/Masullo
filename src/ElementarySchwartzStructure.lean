import ElementarySchwartzComplete
import ElementarySchwartzNuclear
import StrongDualBarrelled

open Function Topology

namespace Masullo

noncomputable section

universe u v
set_option maxSynthPendingDepth 8

variable {m n r : ℕ} {F : Type u} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "E" => ElementarySchwartz m n r F
local notation "D" => StrongDual ℂ (ElementarySchwartz m n r F)

local instance : ContinuousSMul ℂ E :=
  elementarySchwartz_withSeminorms.continuousSMul
local instance : T2Space E := elementarySchwartz_t2

/-- The topology from the mixed seminorms is Fréchet. -/
theorem elementarySchwartz_frechet : IsFrechetTVS E := by
  obtain ⟨_, hp, hm, hc⟩ := elementarySchwartz_isFrechet (m := m) (n := n) (r := r) (F := F)
  refine ⟨inferInstance, hp, hm, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hc

theorem elementarySchwartz_barrelled : BarrelledSpace ℂ E :=
  isFrechetTVS_barrelled elementarySchwartz_frechet

theorem elementarySchwartz_reflexive :
    ∃ e : E ≃L[ℂ] StrongDual ℂ D, ∀ x f, e x f = f x := by
  letI : BarrelledSpace ℂ E := elementarySchwartz_barrelled
  letI : CompleteSpace E := elementarySchwartz_isFrechet.2.2.2
  exact strongBidual_equiv_of_nuclear (elementarySchwartz_nuclear.{u, u} (F := F))

theorem elementarySchwartz_strongDual_nuclear : NuclearLocallyConvex.{v, u} D :=
  strongDual_nuclear_of_nuclear_frechet elementarySchwartz_frechet elementarySchwartz_nuclear

theorem elementarySchwartz_strongDual_complete : CompleteSpace D := by
  letI : TopologicalSpace.MetrizableSpace E := elementarySchwartz_isFrechet.2.2.1
  infer_instance

theorem elementarySchwartz_strongDual_barrelled : BarrelledSpace ℂ D := by
  apply strongDual_barrelled_of_bidually_surjective
  obtain ⟨e, he⟩ := elementarySchwartz_reflexive (m := m) (n := n) (r := r) (F := F)
  intro f
  obtain ⟨x, hx⟩ := e.surjective f
  exact ⟨x, ContinuousLinearMap.ext fun L ↦ (he x L).symm.trans (DFunLike.congr_fun hx L)⟩

theorem elementarySchwartz_strongDual_reflexive :
    ∃ e : D ≃L[ℂ] StrongDual ℂ (StrongDual ℂ D), ∀ x f, e x f = f x := by
  let h := elementarySchwartz_strongDual_nuclear.{u, u} (m := m) (n := n) (r := r) (F := F)
  letI : T2Space D := h.1
  letI : PolynormableSpace ℂ D := h.2.1
  letI : CompleteSpace D := elementarySchwartz_strongDual_complete
  letI : BarrelledSpace ℂ D := elementarySchwartz_strongDual_barrelled
  exact strongBidual_equiv_of_nuclear h

/-- D.1.3.7(3). Completeness, nuclearity, compactness of closed bounded sets
and strong reflexivity hold for both the elementary Schwartz space and its strong dual. -/
theorem elementarySchwartz_montel_structure :
    CompleteSpace E ∧ NuclearLocallyConvex.{u, u} E ∧ MontelSpace ℂ E ∧
      BarrelledSpace ℂ E ∧ (∃ e : E ≃L[ℂ] StrongDual ℂ D, ∀ x f, e x f = f x) ∧
    CompleteSpace D ∧ NuclearLocallyConvex.{u, u} D ∧ MontelSpace ℂ D ∧
      BarrelledSpace ℂ D ∧ (∃ e : D ≃L[ℂ] StrongDual ℂ (StrongDual ℂ D), ∀ x f, e x f = f x) := by
  letI : CompleteSpace E := elementarySchwartz_isFrechet.2.2.2
  letI : CompleteSpace D := elementarySchwartz_strongDual_complete
  have hE : NuclearLocallyConvex.{u, u} E := elementarySchwartz_nuclear
  have hD : NuclearLocallyConvex.{u, u} D := elementarySchwartz_strongDual_nuclear
  exact ⟨inferInstance, hE, ⟨fun _ hc hb ↦
    (nuclearLocallyConvex_totallyBounded hE hb).isCompact_of_isClosed hc⟩,
    elementarySchwartz_barrelled, elementarySchwartz_reflexive,
    inferInstance, hD, ⟨fun _ hc hb ↦
      (nuclearLocallyConvex_totallyBounded hD hb).isCompact_of_isClosed hc⟩,
    elementarySchwartz_strongDual_barrelled, elementarySchwartz_strongDual_reflexive⟩

end
end Masullo
