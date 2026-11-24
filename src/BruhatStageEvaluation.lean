import BruhatSchwartzStructure
import FrechetFactorization

open Function Set Topology

namespace Masullo

noncomputable section

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- A linear map between elementary Schwartz stages is continuous when
each evaluation of the realized output is continuous. -/
theorem bruhatStage_continuous_of_evaluation (p : BruhatSchwartzStage G)
    (q : BruhatSchwartzStage H) (L : p.Space →ₗ[ℂ] q.Space)
    (hL : ∀ y : H, Continuous (fun f : p.Space ↦ q.realize (L f) y)) : Continuous L := by
  letI : T2Space p.Space := elementarySchwartz_t2
  letI : ContinuousSMul ℂ p.Space := elementarySchwartz_withSeminorms.continuousSMul
  letI : ContinuousSMul ℂ q.Space := elementarySchwartz_withSeminorms.continuousSMul
  letI : FirstCountableTopology p.Space := elementarySchwartz_withSeminorms.firstCountableTopology
  letI : FirstCountableTopology q.Space := elementarySchwartz_withSeminorms.firstCountableTopology
  letI : CompleteSpace p.Space := completeSpace_elementarySchwartz
  letI : CompleteSpace q.Space := completeSpace_elementarySchwartz
  apply frechet_continuous_of_closed_graph
  let W (y : H) : Set (p.Space × q.Space) :=
    {z | q.realize z.2 y = q.realize (L z.1) y}
  have he : (L.graph : Set (p.Space × q.Space)) = ⋂ y, W y := by
    ext z
    change z.2 = L z.1 ↔ z ∈ ⋂ y, W y
    rw [mem_iInter]
    exact ⟨fun h y ↦ congrArg (fun w ↦ q.realize w y) h,
      fun h ↦ q.1.realizeSchwartz_injective q.2 (funext h)⟩
  rw [he]
  exact isClosed_iInter fun y ↦ isClosed_eq
    (((bruhatSchwartz_continuous_eval y).comp q.inclusionCLM.continuous).comp continuous_snd)
    ((hL y).comp continuous_fst)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- A family of continuous scalar functionals is represented by a continuous
linear map between two stages if it has a stage realization at every input. -/
theorem bruhatStage_exists_clm_of_evaluation (p : BruhatSchwartzStage G)
    (q : BruhatSchwartzStage H) {X : Type*} (r : X → H) (hr : Surjective r)
    (A : X → p.Space →L[ℂ] ℂ)
    (hA : ∀ f, ∃ g : q.Space, ∀ x, q.realize g (r x) = A x f) :
    ∃ L : p.Space →L[ℂ] q.Space, ∀ f x, q.realize (L f) (r x) = A x f := by
  classical
  let g (f : p.Space) := (hA f).choose
  have hg (f : p.Space) (x : X) := (hA f).choose_spec x
  have he {u v : q.Space} (h : ∀ x, q.realize u (r x) = q.realize v (r x)) : u = v :=
    q.1.realizeSchwartz_injective q.2 (funext (hr.forall.mpr h))
  let L : p.Space →ₗ[ℂ] q.Space :=
    { toFun := g
      map_add' := fun f f' ↦ he fun x ↦
        (hg (f + f') x).trans (((A x).map_add f f').trans
          ((congrArg₂ (· + ·) (hg f x).symm (hg f' x).symm).trans
            (congrFun (q.realize.map_add _ _) (r x)).symm))
      map_smul' := fun c f ↦ he fun x ↦
        (hg (c • f) x).trans (((A x).map_smul c f).trans
          ((congrArg (c • ·) (hg f x).symm).trans
            (congrFun (q.realize.map_smul _ _) (r x)).symm)) }
  refine ⟨⟨L, bruhatStage_continuous_of_evaluation p q L (hr.forall.mpr ?_)⟩, hg⟩
  intro x
  exact (A x).continuous.congr fun f ↦ (hg f x).symm

/-- Compatible continuous scalar evaluations on Bruhat stages assemble into a
continuous linear map on the full inductive space. -/
theorem bruhatSchwartz_exists_clm_of_stage_evaluation {X : Type*} (r : X → H)
    (hr : Surjective r) (A : X → BruhatSchwartz G →L[ℂ] ℂ)
    (hA : ∀ p : BruhatSchwartzStage G, ∃ (q : BruhatSchwartzStage H) (L : p.Space →L[ℂ] q.Space),
      ∀ f x, q.realize (L f) (r x) = A x (p.inclusion f)) :
    ∃ L : BruhatSchwartz G →L[ℂ] BruhatSchwartz H, ∀ f x, (L f).val (r x) = A x f := by
  classical
  have hVal (f : BruhatSchwartz G) : ∃ g : BruhatSchwartz H, ∀ x, g.val (r x) = A x f := by
    obtain ⟨p, u, hu⟩ := f.property
    obtain ⟨q, L, hL⟩ := hA p
    exact ⟨q.inclusion (L u), fun x ↦
      (hL u x).trans (congrArg (A x) (show p.inclusion u = f from Subtype.ext hu))⟩
  let g (f : BruhatSchwartz G) := (hVal f).choose
  have hg (f : BruhatSchwartz G) (x : X) := (hVal f).choose_spec x
  have he {u v : BruhatSchwartz H} (h : ∀ x, u.val (r x) = v.val (r x)) : u = v :=
    Subtype.ext (funext (hr.forall.mpr h))
  let L : BruhatSchwartz G →ₗ[ℂ] BruhatSchwartz H :=
    { toFun := g
      map_add' := fun f f' ↦ he fun x ↦
        (hg (f + f') x).trans (((A x).map_add f f').trans
          (congrArg₂ (· + ·) (hg f x).symm (hg f' x).symm))
      map_smul' := fun c f ↦ he fun x ↦
        (hg (c • f) x).trans (((A x).map_smul c f).trans (congrArg (c • ·) (hg f x).symm)) }
  refine ⟨⟨L, (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G ↦ p.inclusion) L).2
    fun p ↦ ?_⟩, hg⟩
  obtain ⟨q, B, hB⟩ := hA p
  have hfun : (L.comp p.inclusion : p.Space → BruhatSchwartz H) = q.inclusionCLM ∘ B :=
    funext fun f ↦ he fun x ↦ (hg (p.inclusion f) x).trans (hB f x).symm
  rw [hfun]
  exact q.inclusionCLM.continuous.comp B.continuous

set_option maxHeartbeats 1200000 in
/-- Pointwise stage realizations suffice to assemble a continuous linear map. -/
theorem bruhatSchwartz_exists_clm_of_stage_values {X : Type*} (r : X → H)
    (hr : Surjective r) (A : X → BruhatSchwartz G →L[ℂ] ℂ)
    (hA : ∀ p : BruhatSchwartzStage G, ∃ q : BruhatSchwartzStage H, ∀ f : p.Space,
      ∃ u : q.Space, ∀ x, q.realize u (r x) = A x (p.inclusion f)) :
    ∃ L : BruhatSchwartz G →L[ℂ] BruhatSchwartz H,
      ∀ f x, (L f).val (r x) = A x f := by
  have hStage (p : BruhatSchwartzStage G) :
      ∃ (q : BruhatSchwartzStage H) (L : p.Space →L[ℂ] q.Space),
        ∀ f x, q.realize (L f) (r x) = A x (p.inclusion f) := by
    obtain ⟨q, hq⟩ := hA p
    let B (x : X) := (A x).comp p.inclusionCLM
    have hq' : ∀ f, ∃ u : q.Space, ∀ x, q.realize u (r x) = B x f := hq
    have hL : ∃ L : p.Space →L[ℂ] q.Space,
        ∀ f x, q.realize (L f) (r x) = B x f :=
      bruhatStage_exists_clm_of_evaluation p q r hr B hq'
    exact ⟨q, hL⟩
  exact bruhatSchwartz_exists_clm_of_stage_evaluation r hr A hStage

set_option maxHeartbeats 1000000 in
/-- Stage realizations on a cofinal family suffice for gluing. -/
theorem bruhatSchwartz_exists_clm_of_cofinal_stage_values {X : Type*} (r : X → H)
    (hr : Surjective r) (A : X → BruhatSchwartz G →L[ℂ] ℂ)
    (c : Set (BruhatSchwartzStage G))
    (hcof : ∀ p : BruhatSchwartzStage G, ∃ q : c, p.1 ≤ q.val.1)
    (hA : ∀ p : c, ∃ q : BruhatSchwartzStage H, ∀ f : p.val.Space,
      ∃ u : q.Space, ∀ x, q.realize u (r x) = A x (p.val.inclusion f)) :
    ∃ L : BruhatSchwartz G →L[ℂ] BruhatSchwartz H,
      ∀ f x, (L f).val (r x) = A x f := by
  have hV (p : BruhatSchwartzStage G) : ∃ q : BruhatSchwartzStage H, ∀ f : p.Space,
      ∃ u : q.Space, ∀ x, q.realize u (r x) = A x (p.inclusion f) := by
    obtain ⟨t, ht⟩ := hcof p
    obtain ⟨q, hq⟩ := hA t
    refine ⟨q, fun f ↦ ?_⟩
    let u := p.transition t.val ht f
    have hu : t.val.inclusion u = p.inclusion f := p.inclusion_transition t.val ht f
    obtain ⟨v, hv⟩ := hq u
    exact ⟨v, fun x ↦ (hv x).trans (congrArg (A x) hu)⟩
  exact bruhatSchwartz_exists_clm_of_stage_values r hr A hV

end

end Masullo
