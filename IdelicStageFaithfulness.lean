import IdelicStageRank
import BruhatStageSeparation

open Function NumberField Module Set Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

local notation "Arch" => mixedEmbedding.mixedSpace F

/-- Passing from the ideles to idele classes does not kill any nonzero
archimedean velocity, since the principal ideles are discrete. -/
theorem archimedeanClassExponential_direction_eq_one {x : Arch}
    (h : ∀ t : ℝ, archimedeanClassExponential F (Multiplicative.ofAdd (t • x)) = 1) :
    x = 0 := by
  let g (t : ℝ) := mixedArchExpIdele F (Multiplicative.ofAdd (t • x))
  have hg : Continuous g := (mixedArchExpIdele_continuous F).comp
    (continuous_ofAdd.comp (continuous_id.smul continuous_const))
  have hg₀ : g 0 = 1 := by
    change mixedArchExpIdele F (Multiplicative.ofAdd ((0 : ℝ) • x)) = 1
    rw [zero_smul]
    exact map_one _
  have hgmem (t : ℝ) : g t ∈ principalIdeles F :=
    (QuotientGroup.eq_one_iff _).mp (h t)
  letI := principalIdeles_discrete (F := F)
  let k (t : ℝ) : principalIdeles F := ⟨g t, hgmem t⟩
  have hk : Continuous k := hg.subtype_mk _
  refine mixedArchExpIdele_direction_eq_one F fun t => ?_
  have he := TotallyDisconnectedSpace.eq_of_continuous k hk t 0
  exact (congrArg Subtype.val he).trans hg₀

/-- The elementary global stages jointly detect every nonzero
archimedean velocity. -/
theorem archimedeanClassExponential_stageDirections_separate {x : Arch}
    (h : ∀ (P : WholeBruhatStage (IdeleClass F)) (t : ℝ),
      P.coordinates (archimedeanClassExponential F (Multiplicative.ofAdd (t • x))) = 1) :
    x = 0 := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hs : Surjective m := fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  exact archimedeanClassExponential_direction_eq_one F fun t =>
    WholeBruhatStage.eq_one_of_coordinates_eq_one m hm hs _ (fun P => h P t)

set_option maxHeartbeats 12000000 in
/-- All refinements of one global Bruhat stage retain the entire archimedean
tangent space. A stage with minimal velocity-kernel dimension has trivial
kernel because common refinements separate every nonzero velocity. -/
theorem exists_ideleClassStage_bijective_archimedeanVelocity :
    ∃ P : WholeBruhatStage (IdeleClass F), ∀ Q : WholeBruhatStage (IdeleClass F),
      Q.val.1.kernel ≤ P.val.1.kernel →
      ∃ L : Arch →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin Q.val.2.realDim) × EuclideanSpace ℝ (Fin Q.val.2.torusDim)),
        Bijective L ∧ ∀ x t,
        Q.coordinates (archimedeanClassExponential F (Multiplicative.ofAdd (t • x))) =
          elementaryOneParameter (L x) (Multiplicative.ofAdd t) := by
  classical
  choose L hL hline using exists_ideleClassStage_archimedeanVelocity F
  let K (Q : WholeBruhatStage (IdeleClass F)) : Submodule ℝ Arch := (L Q).ker
  have hK (Q : WholeBruhatStage (IdeleClass F)) (x : Arch) :
      x ∈ K Q ↔ ∀ t : ℝ,
        Q.coordinates (archimedeanClassExponential F (Multiplicative.ofAdd (t • x))) = 1 := by
    constructor
    · intro hx t
      have hx₀ : L Q x = 0 := hx
      rw [hline Q x t, hx₀]
      change Multiplicative.ofAdd (elementaryCoverHom (t • 0)) = _
      rw [smul_zero, map_zero]
      rfl
    · intro hx
      change L Q x = 0
      apply elementaryOneParameter_injective (r := Q.val.2.latticeRank)
        (F := Q.val.2.finiteFactor)
      apply ContinuousMonoidHom.ext
      intro t
      have he := (hline Q x t.toAdd).symm.trans (hx t.toAdd)
      refine he.trans ?_
      change (1 : Multiplicative Q.ElementaryCoordinates) =
        Multiplicative.ofAdd (elementaryCoverHom (t.toAdd • 0))
      rw [smul_zero, map_zero]
      rfl
  have hmono (P Q : WholeBruhatStage (IdeleClass F))
      (hpq : P.val.1.kernel ≤ Q.val.1.kernel) : K P ≤ K Q := by
    intro x hx
    apply (hK Q x).mpr
    intro t
    let y := archimedeanClassExponential F (Multiplicative.ofAdd (t • x))
    have hy : y ∈ P.coordinates.toMonoidHom.ker := (hK P x).mp hx t
    rw [P.coordinates_ker] at hy
    have hy' : y ∈ Q.coordinates.toMonoidHom.ker := Q.coordinates_ker.symm ▸ hpq hy
    exact hy'
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hs : Surjective m := fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  have hstage := @exists_modulatedBruhat_character_stage (IdeleClass F)
    inferInstance inferInstance inferInstance inferInstance inferInstance m hm hs 1
  obtain ⟨S, hS, _⟩ := hstage
  obtain ⟨e⟩ := S.quotient_elementary
  let P₁ : WholeBruhatStage (IdeleClass F) := ⟨⟨S, e⟩, hS⟩
  letI : Nonempty (WholeBruhatStage (IdeleClass F)) := ⟨P₁⟩
  have hdir : Directed (· ≥ ·) K := by
    intro P Q
    have hr := @WholeBruhatStage.exists_common_kernel_refinement (IdeleClass F)
      inferInstance inferInstance inferInstance inferInstance inferInstance P Q
    obtain ⟨R, hRP, hRQ⟩ := hr
    exact ⟨R, hmono R P hRP, hmono R Q hRQ⟩
  have hsep (x : Arch) (hx : ∀ Q, x ∈ K Q) : x = 0 :=
    archimedeanClassExponential_stageDirections_separate F fun Q => (hK Q x).mp (hx Q)
  have hfaithful : ∃ P, K P = ⊥ := WholeBruhatStage.exists_trivial_velocity_kernel K hdir hsep
  obtain ⟨P, hP⟩ := hfaithful
  refine ⟨P, fun Q hQP => ?_⟩
  have hker : K Q = ⊥ := le_antisymm ((hmono Q P hQP).trans hP.le) bot_le
  have hker' : (L Q).ker = ⊥ := hker
  have hinj : Injective (L Q) := LinearMap.ker_eq_bot.mp hker'
  exact ⟨L Q, ⟨hinj, hL Q⟩, hline Q⟩

end
end Masullo
