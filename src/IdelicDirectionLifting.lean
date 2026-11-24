/-
The covering-lift argument is adapted from the Apache-2.0 RiemannMasullo
project, 8ca6820cd7f5468d140ecf8a4122b41fa4cdb1b4,
AppD_SchwartzBruhat/Sec1d.lean. See External/RiemannMasullo.LICENSE.
-/
import BruhatStageDirections
import NormOneClassCompact
import IdeleOneParameter
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

open Function NumberField Set Topology

namespace Masullo

/-- The based continuous lift of a real one-parameter subgroup through a
covering homomorphism is itself multiplicative. -/
theorem exists_oneParameter_lift_covering {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
    (q : G →ₜ* H) (hq : IsCoveringMap q) (c : Multiplicative ℝ →ₜ* H) :
    ∃ a : Multiplicative ℝ →ₜ* G, q.comp a = c := by
  let f : C(ℝ, H) := ⟨fun x => c (Multiplicative.ofAdd x), c.continuous.comp continuous_ofAdd⟩
  obtain ⟨g, ⟨hg₀, hg⟩, _⟩ :=
    hq.existsUnique_continuousMap_lifts f 0 1 ((map_one q).trans (map_one c).symm)
  have hlift (x : ℝ) : q (g x) = c (Multiplicative.ofAdd x) := congrFun hg x
  have hmul : (fun p : ℝ × ℝ => g (p.1 + p.2)) =
      fun p : ℝ × ℝ => g p.1 * g p.2 := by
    refine hq.eq_of_comp_eq (g₁ := fun p : ℝ × ℝ => g (p.1 + p.2))
      (g₂ := fun p : ℝ × ℝ => g p.1 * g p.2)
      (g.continuous.comp (continuous_fst.add continuous_snd))
      ((g.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd))
      ?_ ((0, 0) : ℝ × ℝ) ?_
    · funext p
      change q (g (p.1 + p.2)) = q (g p.1 * g p.2)
      rw [hlift, map_mul, hlift, hlift]
      exact map_mul c (Multiplicative.ofAdd p.1) (Multiplicative.ofAdd p.2)
    · change g (0 + 0) = g 0 * g 0
      rw [zero_add, hg₀, one_mul]
  let a : Multiplicative ℝ →ₜ* G :=
    { toFun := fun t => g t.toAdd
      map_one' := hg₀
      map_mul' := fun s t => congrFun hmul (s.toAdd, t.toAdd)
      continuous_toFun := g.continuous.comp continuous_toAdd }
  exact ⟨a, ContinuousMonoidHom.ext fun t => hlift t.toAdd⟩

/-- Every idele-class direction lifts to a direction supported at the infinite
places. The covering kernel is the discrete group of principal ideles. -/
theorem exists_ideleClass_direction_lift (F : Type*) [Field F] [NumberField F]
    (c : Multiplicative ℝ →ₜ* IdeleClass F) :
    ∃ a : Multiplicative ℝ →ₜ* Idele F,
      (∀ t, ideleClassMap F (a t) = c t) ∧ ∀ t, a t ∈ infinitePlaceIdeles F := by
  letI := principalIdeles_discrete (F := F)
  let q : Idele F →ₜ* IdeleClass F := ⟨ideleClassMap F, ideleClassMap_continuous F⟩
  have hq : IsCoveringMap q :=
    ((principalIdeles F).isQuotientCoveringMap_of_comm
      (isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap
  obtain ⟨a, ha⟩ := exists_oneParameter_lift_covering q hq c
  exact ⟨a, fun t => DFunLike.congr_fun ha t,
    (idele_oneParameter_structure F a.toMonoidHom a.continuous).1⟩

/-- Remark D.1.10.8. A continuous real direction takes values in the identity
component of its target, in particular when the target is the norm-one group. -/
theorem oneParameter_mem_identityComponent {G : Type*} [Group G] [TopologicalSpace G]
    (a : Multiplicative ℝ →ₜ* G) (t : Multiplicative ℝ) :
    a t ∈ connectedComponent (1 : G) := by
  let f : ℝ → G := fun x => a (Multiplicative.ofAdd x)
  have hf : Continuous f := a.continuous.comp continuous_ofAdd
  have h₀ : f 0 = 1 := map_one a
  have h := hf.mapsTo_connectedComponent 0
  rw [h₀, PreconnectedSpace.connectedComponent_eq_univ] at h
  exact h (mem_univ t.toAdd)

section IdeleClassStage

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

set_option maxHeartbeats 4500000 in
/-- Every direction on an elementary idele-class stage lifts to a direction
supported at the infinite places of the original ideles. -/
theorem exists_ideleClassStage_direction_lift (P : WholeBruhatStage (IdeleClass F))
    (c : Multiplicative ℝ →ₜ* Multiplicative P.ElementaryCoordinates) :
    ∃ a : Multiplicative ℝ →ₜ* Idele F,
      (∀ t, P.coordinates (ideleClassMap F (a t)) = c t) ∧
      ∀ t, a t ∈ infinitePlaceIdeles F := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  letI : T2Space P.val.2.finiteFactor := DiscreteTopology.toT2Space
  letI : T2Space P.ElementaryCoordinates := Prod.t2Space
  letI : T2Space (Multiplicative P.ElementaryCoordinates) :=
    inferInstanceAs (T2Space P.ElementaryCoordinates)
  let q : IdeleClass F →ₜ* Multiplicative P.ElementaryCoordinates := P.coordinates
  have hq : IsProperMap q := P.coordinates_proper m hm
  have hs : Surjective q := P.coordinates_surjective
  have hstage : ∃ v : Multiplicative ℝ →ₜ* IdeleClass F, q.comp v = c :=
    @exists_oneParameter_lift_proper (IdeleClass F) (Multiplicative P.ElementaryCoordinates)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance q hq hs c
  obtain ⟨v, hv⟩ := hstage
  have hu : ∃ a : Multiplicative ℝ →ₜ* Idele F,
      (∀ t, ideleClassMap F (a t) = v t) ∧ ∀ t, a t ∈ infinitePlaceIdeles F :=
    exists_ideleClass_direction_lift F v
  obtain ⟨a, ha, hArch⟩ := hu
  refine ⟨a, fun t => ?_, hArch⟩
  change q (ideleClassMap F (a t)) = c t
  rw [ha t]
  exact DFunLike.congr_fun hv t

end IdeleClassStage

end Masullo
