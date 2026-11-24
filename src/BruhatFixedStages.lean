import BruhatWholeQuotientStages
import BruhatSchwartzStrict

open Function Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace WholeBruhatStage

set_option maxHeartbeats 1600000

variable (P : WholeBruhatStage G)

/-- Schwartz tests fixed by left translation by the structural kernel. -/
def fixedSubmodule : Submodule ℂ (BruhatSchwartz G) where
  carrier := {f | ∀ k : P.val.1.kernel, ∀ x, f.val (k.val * x) = f.val x}
  zero_mem' := by intro k x; rfl
  add_mem' hf hg := by
    intro k x
    simp only [Submodule.coe_add, Pi.add_apply, hf k x, hg k x]
  smul_mem' z f hf := by
    intro k x
    simp only [Submodule.coe_smul, Pi.smul_apply, hf k x]

/-- The Schwartz space on the elementary quotient realizes exactly the
kernel-invariant Schwartz functions on the original group. -/
theorem inclusion_range_eq_fixedSubmodule :
    P.val.inclusionCLM.toLinearMap.range = P.fixedSubmodule := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩ k x
    have hk : P.coordinates k.val = 1 := by
      change k.val ∈ P.coordinates.toMonoidHom.ker
      rw [P.coordinates_ker]
      exact k.property
    change P.val.realize u (k.val * x) = P.val.realize u x
    rw [P.realize_eq_coordinates, P.realize_eq_coordinates, map_mul, hk, one_mul]
  · intro hf
    change ∀ k : P.val.1.kernel, ∀ x, f.val (k.val * x) = f.val x at hf
    obtain ⟨σ, hσ⟩ := P.coordinates_surjective.hasRightInverse
    let v (y : ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank
        P.val.2.finiteFactor) := f.val (σ (Multiplicative.ofAdd y))
    have hv (x : G) : v (P.coordinates x).toAdd = f.val x := by
      let y := σ (P.coordinates x)
      have hk : x / y ∈ P.val.1.kernel := by
        rw [← P.coordinates_ker]
        change P.coordinates (x / y) = 1
        rw [map_div, show P.coordinates y = P.coordinates x from hσ _, div_self']
      have hi := hf ⟨x / y, hk⟩ y
      change f.val (x / y * y) = f.val y at hi
      rw [div_mul_cancel] at hi
      exact hi.symm
    obtain ⟨Q, u, hu⟩ := f.property
    letI := (lcaStructuralPairs_filtered (G := G)).2
    obtain ⟨R, hPR, hQR⟩ := exists_ge_ge P.val.1 Q.1
    obtain ⟨e⟩ := R.quotient_elementary
    let W : WholeBruhatStage G := ⟨⟨R, e⟩, top_unique (P.property ▸ hPR.1)⟩
    let w := BruhatSchwartzStage.transition Q W.val hQR u
    have hw (x : G) : w (W.coordinates x).toAdd = f.val x := by
      rw [← W.realize_eq_coordinates]
      exact (congrArg (fun z : BruhatSchwartz G => z.val x)
        (BruhatSchwartzStage.inclusion_transition Q W.val hQR u)).trans (congrFun hu x)
    let idG := ContinuousMonoidHom.id G
    have hker : W.val.1.kernel ≤ P.val.1.kernel.comap idG.toMonoidHom := hPR.2
    let T := W.coordinateMap P idG hker
    have hT (x : G) : T (W.coordinates x) = P.coordinates x :=
      W.coordinateMap_coordinates P idG hker x
    let φ := T.toMonoidHom.toAdditive
    have hc : Continuous φ := continuous_toAdd.comp (T.continuous.comp continuous_ofAdd)
    have ho : IsOpenMap φ :=
      isOpenMap_toAdd.comp ((W.coordinateMap_isOpenMap P idG hker (fun U h => by
        change IsOpen (id '' U)
        rwa [Set.image_id])).comp isOpenMap_ofAdd)
    have hs : Surjective φ := W.coordinateMap_surjective P idG hker surjective_id
    have he : v ∘ φ = w := by
      funext y
      obtain ⟨x, hx⟩ := W.coordinates_surjective (Multiplicative.ofAdd y)
      have hy : y = (W.coordinates x).toAdd := (congrArg Multiplicative.toAdd hx).symm
      rw [hy]
      change v (T (W.coordinates x)).toAdd = w (W.coordinates x).toAdd
      rw [hT, hv, hw]
    let v₀ : P.val.Space := ⟨v, elementarySchwartz_mem_of_openPullback φ hc ho hs w v he⟩
    refine ⟨v₀, Subtype.ext (funext fun x => ?_)⟩
    exact (P.realize_eq_coordinates v₀ x).trans (hv x)

/-- The quotient Schwartz topology is the inherited topology of the fixed
subspace in the full Schwartz–Bruhat space. -/
def equivFixedSubmodule [SecondCountableTopology G] : P.val.Space ≃L[ℂ] P.fixedSubmodule := by
  let L := P.val.inclusionCLM.toLinearMap.codRestrict P.fixedSubmodule
    (fun v => P.inclusion_range_eq_fixedSubmodule ▸ LinearMap.mem_range_self _ v)
  let e := LinearEquiv.ofBijective L ⟨fun _ _ h => P.val.inclusion_injective (congrArg Subtype.val h),
    fun f => by
      have h : f.val ∈ P.val.inclusionCLM.toLinearMap.range := by
        rw [P.inclusion_range_eq_fixedSubmodule]
        exact f.property
      obtain ⟨v, hv⟩ := h
      exact ⟨v, Subtype.ext hv⟩⟩
  have h₀ : Continuous e := P.val.inclusionCLM.continuous.subtype_mk _
  have he : IsEmbedding (P.val.inclusionCLM : P.val.Space → BruhatSchwartz G) :=
    (bruhatSchwartz_strict (G := G)).2.1 P.val
  refine ⟨e, h₀, he.isInducing.continuous_iff.mpr ?_⟩
  have hcomp : (P.val.inclusionCLM : P.val.Space → BruhatSchwartz G) ∘ e.symm =
      (Subtype.val : P.fixedSubmodule → BruhatSchwartz G) :=
    funext fun u => congrArg Subtype.val (e.apply_symm_apply u)
  change Continuous ((P.val.inclusionCLM : P.val.Space → BruhatSchwartz G) ∘ e.symm)
  rw [hcomp]
  exact continuous_subtype_val

end WholeBruhatStage

end
end Masullo
