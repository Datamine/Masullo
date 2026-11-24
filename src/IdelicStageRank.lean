import IdelicDirectionLifting
import ArchimedeanIdeleExponential
import ElementaryVelocity

open Function NumberField Module Set Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

local notation "Arch" => mixedEmbedding.mixedSpace F

/-- The archimedean exponential followed by passage to idele classes. -/
def archimedeanClassExponential : Multiplicative Arch →ₜ* IdeleClass F :=
  (⟨ideleClassMap F, ideleClassMap_continuous F⟩ : Idele F →ₜ* IdeleClass F).comp
    ⟨mixedArchExpIdele F, mixedArchExpIdele_continuous F⟩

/-- Every idele-class direction is the projection of a straight line in
the mixed archimedean tangent space under the exponential. -/
theorem exists_archimedeanClassExponential_direction (a : Multiplicative ℝ →ₜ* IdeleClass F) :
    ∃ x : Arch, ∀ t : ℝ, a (Multiplicative.ofAdd t) =
      archimedeanClassExponential F (Multiplicative.ofAdd (t • x)) := by
  obtain ⟨b, hb, hArch⟩ := exists_ideleClass_direction_lift F a
  obtain ⟨x, hx⟩ := exists_mixedArchExpIdele_direction F b hArch
  refine ⟨x, fun t => ?_⟩
  exact (hb (Multiplicative.ofAdd t)).symm.trans (congrArg (ideleClassMap F) (hx t))

set_option maxHeartbeats 4000000 in
/-- Each global elementary stage is generated at the level of velocities
by a surjective linear map from the mixed archimedean tangent space. -/
theorem exists_ideleClassStage_archimedeanVelocity (P : WholeBruhatStage (IdeleClass F)) :
    ∃ L : Arch →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)),
      Surjective L ∧ ∀ x t,
      P.coordinates (archimedeanClassExponential F (Multiplicative.ofAdd (t • x))) =
        elementaryOneParameter (L x) (Multiplicative.ofAdd t) := by
  let q : Multiplicative Arch →ₜ* Multiplicative P.ElementaryCoordinates :=
    P.coordinates.comp (archimedeanClassExponential F)
  have he := @exists_linear_elementaryVelocity P.val.2.realDim P.val.2.torusDim
    P.val.2.latticeRank P.val.2.finiteFactor inferInstance inferInstance inferInstance
    Arch inferInstance inferInstance inferInstance inferInstance q
  obtain ⟨L, hL⟩ := he
  refine ⟨L, ?_, hL⟩
  intro v
  let c : Multiplicative ℝ →ₜ* Multiplicative P.ElementaryCoordinates :=
    elementaryOneParameter v
  obtain ⟨a, ha, hArch⟩ := exists_ideleClassStage_direction_lift F P c
  obtain ⟨x, hx⟩ := exists_mixedArchExpIdele_direction F a hArch
  refine ⟨x, elementaryOneParameter_injective (r := P.val.2.latticeRank)
    (F := P.val.2.finiteFactor) ?_⟩
  apply ContinuousMonoidHom.ext
  intro t
  have h := (ha t).symm
  rw [show a t = mixedArchExpIdele F (Multiplicative.ofAdd (t.toAdd • x)) from hx t.toAdd] at h
  exact (hL x t.toAdd).symm.trans h.symm

/-- The angular rank of a whole-group elementary idele-class stage is at
most the degree of the number field minus one. -/
theorem ideleClassStage_torusDim_le (P : WholeBruhatStage (IdeleClass F)) :
    P.val.2.torusDim ≤ Module.finrank ℚ F - 1 := by
  obtain ⟨L, hL, _⟩ := exists_ideleClassStage_archimedeanVelocity F P
  have hb := LinearMap.finrank_le_finrank_of_surjective (f := L) hL
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
    mixedEmbedding.finrank] at hb
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hs : Surjective m := fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  rw [(P.logCoordinate_dimensions m hm hs).1] at hb
  omega

private theorem span_linearImage_eq_top {X V I : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup V] [Module ℝ V] (L : X →ₗ[ℝ] V) (hL : Surjective L) (B : Basis I ℝ X) :
    Submodule.span ℝ (range (L ∘ B)) = ⊤ := by
  rw [range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr hL]

set_option maxHeartbeats 6000000 in
/-- One family of norm-one directions, indexed by the field degree minus one,
works simultaneously on all global elementary stages. The radial direction
is the prescribed norm section. -/
theorem exists_ideleClass_spanning_directions
    (τ : Multiplicative ℝ →ₜ* IdeleClass F)
    (hτ : RightInverse τ (ideleClassLogNorm F)) :
    let d := Module.finrank ℚ F - 1
    ∃ γ : Fin (d + 1) → Multiplicative ℝ →ₜ* IdeleClass F,
      γ 0 = τ ∧ (∀ (i : Fin d) t, ideleClassLogNorm F (γ i.succ t) = 1) ∧
      ∀ P : WholeBruhatStage (IdeleClass F),
        ∃ v : Fin (d + 1) →
            EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim),
          Submodule.span ℝ (range v) = ⊤ ∧
          ∀ i, P.coordinates.comp (γ i) = elementaryOneParameter (v i) := by
  dsimp only
  let d := Module.finrank ℚ F - 1
  let e := archimedeanClassExponential F
  let m : IdeleClass F →ₜ* Multiplicative ℝ :=
    ⟨ideleClassLogNorm F, ideleClassLogNorm_continuous F⟩
  let N₀ : Arch →+ ℝ := (m.comp e).toMonoidHom.toAdditive
  let N := (N₀.toRealLinearMap (continuous_toAdd.comp
    (m.continuous.comp (e.continuous.comp continuous_ofAdd)))).toLinearMap
  obtain ⟨x, hx⟩ := exists_archimedeanClassExponential_direction F τ
  have hxN : N x = 1 := by
    have h := congrArg (fun g : IdeleClass F => (m g).toAdd) (hx 1)
    rw [one_smul] at h
    exact h.symm.trans (congrArg Multiplicative.toAdd (hτ (Multiplicative.ofAdd 1)))
  have hd : Module.finrank ℝ Arch = d + 1 := by
    rw [mixedEmbedding.finrank]
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    omega
  obtain ⟨B, hB, hBker⟩ := WholeBruhatStage.exists_radial_basis N x hxN hd
  let line (v : Arch) : Multiplicative ℝ →ₜ* Multiplicative Arch :=
    ⟨((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v).toAddMonoidHom.toMultiplicative,
      (show Continuous (fun t : Multiplicative ℝ => Multiplicative.ofAdd (t.toAdd • v)) from
        continuous_ofAdd.comp (continuous_toAdd.smul continuous_const))⟩
  let γ (i : Fin (d + 1)) := e.comp (line (B i))
  refine ⟨γ, ?_, ?_, fun P => ?_⟩
  · apply ContinuousMonoidHom.ext
    intro t
    change e (Multiplicative.ofAdd (t.toAdd • B 0)) = τ t
    rw [hB]
    exact (hx t.toAdd).symm
  · intro i t
    apply Multiplicative.toAdd.injective
    change N (t.toAdd • B i.succ) = 0
    rw [map_smul, hBker i, smul_zero]
  · obtain ⟨L, hL, h⟩ := exists_ideleClassStage_archimedeanVelocity F P
    have hs := span_linearImage_eq_top L hL B
    refine ⟨L ∘ B, hs, fun i => ?_⟩
    apply ContinuousMonoidHom.ext
    intro t
    change P.coordinates (e (Multiplicative.ofAdd (t.toAdd • B i))) =
      elementaryOneParameter (L (B i)) (Multiplicative.ofAdd t.toAdd)
    exact h (B i) t.toAdd

end
end Masullo
