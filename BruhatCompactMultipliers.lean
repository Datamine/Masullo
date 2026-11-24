import BruhatCompactSupport
import BruhatSchwartzStrict
import ElementarySchwartzComplete
import FrechetFactorization

open Filter Function Set Topology

namespace Masullo

noncomputable section
set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace BruhatSchwartzStage

/-- Compact support of a realized function implies compact support on its elementary quotient. -/
theorem hasCompactSupport_of_realize (p : BruhatSchwartzStage G) (f : p.Space)
    (hf : HasCompactSupport (p.realize f)) : HasCompactSupport f.val := by
  let q (x : p.1.upper.val) := (p.1.stageCoordinates p.2 x).toAdd
  have hq : Continuous q := continuous_toAdd.comp (p.1.stageCoordinates p.2).continuous
  have hs : Surjective q := Multiplicative.toAdd.surjective.comp
    (p.2.equiv.surjective.comp QuotientGroup.mk_surjective)
  have hc : IsCompact (Subtype.val ⁻¹' tsupport (p.realize f) : Set p.1.upper.val) :=
    (p.1.upper.val.isClosed_of_isOpen p.1.upper.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hf
  apply HasCompactSupport.intro (hc.image hq)
  intro y hy
  obtain ⟨x, rfl⟩ := hs y
  exact (p.1.realizeSchwartz_apply_of_mem p.2 f x).symm.trans
    (image_eq_zero_of_notMem_tsupport fun hx ↦ hy ⟨x, hx, rfl⟩)

/-- Multiplication by an elementary compact Schwartz test is continuous
on its intrinsic stage. -/
def compactMultiplier (p : BruhatSchwartzStage G) (u : p.Space)
    (hu : HasCompactSupport u.val) : p.Space →L[ℂ] p.Space := by
  let E := p.Space
  let M : E →ₗ[ℂ] E :=
    { toFun := fun f ↦ ⟨fun x ↦ u x * f x,
        elementarySchwartz_mem_of_compactSupport _ (hu.mul_right (f' := f.val))
          (fun a b ↦ (u.property.1 a b).mul (f.property.1 a b))⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦ mul_add (u y) (f y) (g y))
      map_smul' := fun c f ↦ Subtype.ext (funext fun y ↦ mul_left_comm (u y) c (f y)) }
  have heval (x : G) : Continuous (fun f : E ↦ p.realize f x) :=
    (bruhatSchwartz_continuous_eval x).comp p.inclusionCLM.continuous
  have hrealize (f : E) (x : G) : p.realize (M f) x = p.realize u x * p.realize f x := by
    by_cases hx : x ∈ p.1.upper.val
    · let y : p.1.upper.val := ⟨x, hx⟩
      change p.realize (M f) y.val = p.realize u y.val * p.realize f y.val
      simp only [BruhatSchwartzStage.realize, LCAStructuralPair.realizeSchwartz_apply_of_mem]
      rfl
    · simp only [BruhatSchwartzStage.realize, p.1.realizeSchwartz_apply_of_not_mem p.2 _ x hx,
        zero_mul]
  have hgraph : (M.graph : Set (E × E)) =
      ⋂ x : G, {z : E × E | p.realize z.2 x = p.realize u x * p.realize z.1 x} := by
    ext z
    simp only [mem_iInter, mem_ofPred_eq]
    change z.2 = M z.1 ↔ ∀ x, p.realize z.2 x = p.realize u x * p.realize z.1 x
    constructor
    · intro h x
      rw [h, hrealize]
    · intro h
      apply p.1.realizeSchwartz_injective p.2
      funext x
      exact (h x).trans (hrealize z.1 x).symm
  letI : CompleteSpace E := completeSpace_elementarySchwartz
  letI : T2Space E := elementarySchwartz_t2
  letI : TopologicalSpace.MetrizableSpace E :=
    (elementarySchwartz_isFrechet (m := p.2.realDim) (n := p.2.torusDim)
      (r := p.2.latticeRank) (F := p.2.finiteFactor)).2.2.1
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  refine ⟨M, frechet_continuous_of_closed_graph M ?_⟩
  rw [hgraph]
  exact isClosed_iInter fun x ↦ isClosed_eq ((heval x).comp continuous_snd)
    (continuous_const.mul ((heval x).comp continuous_fst))

@[simp] theorem compactMultiplier_apply (p : BruhatSchwartzStage G) (u : p.Space)
    (hu : HasCompactSupport u.val) (f : p.Space)
    (x : ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor) :
    p.compactMultiplier u hu f x = u x * f x := rfl

theorem realize_compactMultiplier (p : BruhatSchwartzStage G) (u : p.Space)
    (hu : HasCompactSupport u.val) (f : p.Space) (x : G) :
    p.realize (p.compactMultiplier u hu f) x = p.realize u x * p.realize f x := by
  by_cases hx : x ∈ p.1.upper.val
  · let y : p.1.upper.val := ⟨x, hx⟩
    change p.realize (p.compactMultiplier u hu f) y.val = p.realize u y.val * p.realize f y.val
    simp only [BruhatSchwartzStage.realize, LCAStructuralPair.realizeSchwartz_apply_of_mem,
      compactMultiplier_apply]
  · simp only [BruhatSchwartzStage.realize, p.1.realizeSchwartz_apply_of_not_mem p.2 _ x hx,
      zero_mul]

end BruhatSchwartzStage

/-- Multiplication by a compactly supported Schwartz–Bruhat function is
continuous on the full inductive limit. -/
def bruhatSchwartz_compactMultiplier (u : BruhatSchwartz G)
    (hu : HasCompactSupport u.val) : BruhatSchwartz G →L[ℂ] BruhatSchwartz G := by
  classical
  let F : BruhatSchwartz G →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f x ↦ u.val x * f.val x
      map_add' := fun _ _ ↦ funext fun _ ↦ mul_add ..
      map_smul' := fun _ _ ↦ funext fun _ ↦ mul_left_comm .. }
  have hstage : ∀ q : BruhatSchwartzStage G, ∃ M : q.Space →L[ℂ] BruhatSchwartz G,
      ∀ f x, (M f).val x = u.val x * q.realize f x := by
    obtain ⟨p, w, hw⟩ := u.property
    letI := (lcaStructuralPairs_filtered (G := G)).2
    intro q
    obtain ⟨R, hp, hq⟩ := exists_ge_ge p.1 q.1
    let r : BruhatSchwartzStage G := ⟨R, Classical.choice R.quotient_elementary⟩
    let uR := p.transition r hp w
    have huR : r.realize uR = u.val :=
      (congrArg Subtype.val (p.inclusion_transition r hp w)).trans hw
    have hcompact : HasCompactSupport uR.val :=
      r.hasCompactSupport_of_realize uR (huR.symm ▸ hu)
    let M := r.inclusionCLM.comp ((r.compactMultiplier uR hcompact).comp (q.transition r hq))
    refine ⟨M, fun f x ↦ ?_⟩
    change r.realize (r.compactMultiplier uR hcompact (q.transition r hq f)) x = _
    rw [r.realize_compactMultiplier, huR]
    have he : r.realize (q.transition r hq f) = q.realize f :=
      congrArg Subtype.val (q.inclusion_transition r hq f)
    rw [he]
  have hmem (f : BruhatSchwartz G) : F f ∈ bruhatSchwartzSubmodule (G := G) := by
    obtain ⟨p, g, hg⟩ := f.property
    obtain ⟨M, hM⟩ := hstage p
    have he : (M g).val = F f := funext fun x ↦
      (hM g x).trans (congrArg (u.val x * ·) (congrFun hg x))
    exact he ▸ (M g).property
  let L := F.codRestrict _ hmem
  refine ⟨L, (locallyConvexFinal_continuous_iff (fun q : BruhatSchwartzStage G ↦ q.inclusion) L).mpr ?_⟩
  intro q
  obtain ⟨M, hM⟩ := hstage q
  exact M.continuous.congr (fun f ↦ Subtype.ext (funext (hM f)))

@[simp] theorem bruhatSchwartz_compactMultiplier_apply (u : BruhatSchwartz G)
    (hu : HasCompactSupport u.val) (f : BruhatSchwartz G) (x : G) :
    (bruhatSchwartz_compactMultiplier u hu f).val x = u.val x * f.val x := rfl


end

end Masullo
