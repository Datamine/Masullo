import BruhatSupportedWindow
import BruhatStageEvaluation

open Function Set Topology

namespace Masullo

noncomputable section

variable {H G : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H]
  [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

private def equivAnnihilator (e : H ≃ₜ* G) (K : Subgroup G) :
    lcaAnnihilator K ≃ₜ* lcaAnnihilator (K.comap e.toMonoidHom) := by
  let r := PontryaginDual.map (e : H →ₜ* G)
  let s := PontryaginDual.map (e.symm : G →ₜ* H)
  have hr (χ : lcaAnnihilator K) : r χ.val ∈ lcaAnnihilator (K.comap e.toMonoidHom) := by
    rw [mem_lcaAnnihilator_iff]
    intro x
    exact (mem_lcaAnnihilator_iff _ _).mp χ.property ⟨e x.val, x.property⟩
  have hs (χ : lcaAnnihilator (K.comap e.toMonoidHom)) : s χ.val ∈ lcaAnnihilator K := by
    rw [mem_lcaAnnihilator_iff]
    intro x
    have hx : e.symm x.val ∈ K.comap e.toMonoidHom := by
      change e (e.symm x.val) ∈ K
      rw [e.apply_symm_apply]
      exact x.property
    exact (mem_lcaAnnihilator_iff _ _).mp χ.property ⟨e.symm x.val, hx⟩
  refine
    { toFun := fun χ => ⟨r χ.val, hr χ⟩
      invFun := fun χ => ⟨s χ.val, hs χ⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := fun x y => Subtype.ext (map_mul r x.val y.val)
      continuous_toFun := (r.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (s.continuous.comp continuous_subtype_val).subtype_mk _ }
  · intro χ
    apply Subtype.ext
    apply PontryaginDual.ext
    intro g
    change χ.val (e (e.symm g)) = χ.val g
    rw [e.apply_symm_apply]
  · intro χ
    apply Subtype.ext
    apply PontryaginDual.ext
    intro h
    change χ.val (e.symm (e h)) = χ.val h
    rw [e.symm_apply_apply]

set_option maxHeartbeats 1300000 in
/-- A topological group isomorphism transports an elementary structural stage.
The transported presentation has the same elementary coordinates. -/
theorem BruhatSchwartzStage.exists_pullback (e : H ≃ₜ* G) (p : BruhatSchwartzStage G) :
    ∃ (q : BruhatSchwartzStage H) (T : p.Space →L[ℂ] q.Space),
      ∀ f x, q.realize (T f) x = p.realize f (e x) := by
  let J := p.1.upper.val
  let K := p.1.kernel
  let J' := J.comap e.toMonoidHom
  let K' := K.comap e.toMonoidHom
  have hJ' (y : J) : e.symm y.val ∈ J' := by
    change e (e.symm y.val) ∈ J
    rw [e.apply_symm_apply]
    exact y.property
  let j : J' ≃ₜ* J :=
    { toFun := fun x => ⟨e x.val, x.property⟩
      invFun := fun y => ⟨e.symm y.val, hJ' y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      map_mul' := fun x y => Subtype.ext (e.map_mul x.val y.val)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk fun x => x.property
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk hJ' }
  have hopen : IsOpen (lcaAnnihilator K' : Set (PontryaginDual H)) := by
    let r := PontryaginDual.map (e.symm : G →ₜ* H)
    have hpre : (lcaAnnihilator K' : Set (PontryaginDual H)) =
        r ⁻¹' (lcaAnnihilator K : Set (PontryaginDual G)) := by
      ext χ
      change χ ∈ lcaAnnihilator K' ↔ r χ ∈ lcaAnnihilator K
      constructor
      · intro h
        apply (mem_lcaAnnihilator_iff K (r χ)).mpr
        intro y
        have hy : e.symm y.val ∈ K' := by
          change e (e.symm y.val) ∈ K
          rw [e.apply_symm_apply]
          exact y.property
        exact (mem_lcaAnnihilator_iff K' χ).mp h ⟨e.symm y.val, hy⟩
      · intro h
        apply (mem_lcaAnnihilator_iff K' χ).mpr
        intro x
        have hx := (mem_lcaAnnihilator_iff K (r χ)).mp h ⟨e x.val, x.property⟩
        change χ (e.symm (e x.val)) = 1 at hx
        rwa [e.symm_apply_apply] at hx
    rw [hpre]
    exact p.1.annihilator_open.preimage r.continuous
  let P : LCAStructuralPair H :=
    ⟨⟨J', p.1.upper.property.1.preimage e.continuous,
      compactGeneration_transport j.symm p.1.upper.property.2⟩,
      K', p.1.kernel_closed.preimage e.continuous, hopen,
      compactGeneration_transport (equivAnnihilator e K) p.1.annihilator_compactlyGenerated,
      fun _ hx => p.1.kernel_le hx⟩
  let N := K.comap J.subtype
  let N' := K'.comap J'.subtype
  have hN : N'.map j.toMonoidHom = N := by
    change (N.comap j.toMonoidHom).map j.toMonoidHom = N
    exact Subgroup.map_comap_eq_self_of_surjective j.surjective N
  let j₀ := QuotientGroup.congr N' N j.toMulEquiv hN
  let j₁ := j₀.toContinuousMulEquiv (fun U => by
    rw [← (QuotientGroup.isQuotientMap_mk N).isCoinducing.isOpen_preimage,
      ← (QuotientGroup.isQuotientMap_mk N').isCoinducing.isOpen_preimage]
    change IsOpen (j ⁻¹' (QuotientGroup.mk ⁻¹' U)) ↔ IsOpen (QuotientGroup.mk ⁻¹' U)
    exact j.toHomeomorph.isOpen_preimage)
  let q : BruhatSchwartzStage H := ⟨P, {p.2 with equiv := j₁.trans p.2.equiv}⟩
  refine ⟨q, ContinuousLinearMap.id ℂ _, fun f x => ?_⟩
  change q.1.realizeSchwartz q.2 f x = p.1.realizeSchwartz p.2 f (e x)
  by_cases hx : e x ∈ J
  · have hx' : x ∈ P.upper.val := hx
    rw [q.1.realizeSchwartz_apply_of_mem q.2 f ⟨x, hx'⟩,
      p.1.realizeSchwartz_apply_of_mem p.2 f ⟨e x, hx⟩]
    rfl
  · have hx' : x ∉ P.upper.val := hx
    exact (q.1.realizeSchwartz_apply_of_not_mem q.2 f x hx').trans
      (p.1.realizeSchwartz_apply_of_not_mem p.2 f (e x) hx).symm

/-- Pullback by a topological group isomorphism is continuous in the full
Schwartz–Bruhat topology. -/
theorem exists_bruhatSchwartz_pullback_continuousLinear (e : H ≃ₜ* G) :
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz H, ∀ f x, (T f).val x = f.val (e x) := by
  let A (x : H) : BruhatSchwartz G →L[ℂ] ℂ :=
    ⟨{ toFun := fun f => f.val (e x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
      bruhatSchwartz_continuous_eval (e x)⟩
  apply bruhatSchwartz_exists_clm_of_stage_evaluation id Function.surjective_id A
  exact fun p => p.exists_pullback e

set_option maxHeartbeats 2400000 in
/-- Pulling an actual Schwartz–Bruhat test back along a topological group
isomorphism preserves the test space. A whole stage pulls back to the
corresponding invariant stage with the same structural kernel under transport. -/
theorem exists_bruhatSchwartz_pullback_equiv
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hs : Surjective m)
    (e : H ≃ₜ* G) (v : BruhatSchwartz G) :
    ∃ u : BruhatSchwartz H, ∀ h, u.val h = v.val (e h) := by
  obtain ⟨p, v₀, hv⟩ := v.property
  obtain ⟨P, hP⟩ := exists_wholeBruhatStage_refinement m hm hs p
  let w := BruhatSchwartzStage.transition p P.val hP v₀
  have hw : P.val.inclusionCLM w = v := by
    rw [show P.val.inclusionCLM w = p.inclusionCLM v₀ from
      BruhatSchwartzStage.inclusion_transition p P.val hP v₀]
    exact Subtype.ext hv
  let K := P.val.1.kernel.comap e.toMonoidHom
  have hcP : IsCompact (P.val.1.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.val.1.kernel P.val.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.val.1.annihilator_open
  have hc : IsCompact (K : Set H) := e.toHomeomorph.isProperMap.isCompact_preimage hcP
  have hgen : IsCompactlyGeneratedGroup (lcaAnnihilator K) :=
    compactGeneration_transport (equivAnnihilator e P.val.1.kernel)
      P.val.1.annihilator_compactlyGenerated
  let j : H →ₜ* G := e
  let mH := m.comp j
  obtain ⟨Q, hQ⟩ := exists_wholeBruhatStage_kernel mH
    (hm.comp e.toHomeomorph.isProperMap) (hs.comp e.surjective) K hc hgen
  have hker : Q.val.1.kernel ≤ P.val.1.kernel.comap j.toMonoidHom := hQ.le
  let T := Q.coordinateMap P j hker
  have hT := Q.coordinateMap_coordinates P j hker
  have hsurj : Surjective T := Q.coordinateMap_surjective P j hker e.surjective
  have hopen : IsOpenMap T := Q.coordinateMap_isOpenMap P j hker e.toHomeomorph.isOpenMap
  have hinj : Injective T := (injective_iff_map_eq_one T).mpr <| by
    intro y hy
    obtain ⟨z, rfl⟩ := Q.coordinates_surjective y
    rw [hT] at hy
    have hz : j z ∈ P.coordinates.toMonoidHom.ker := hy
    rw [P.coordinates_ker] at hz
    have hz' : z ∈ Q.val.1.kernel := hQ.symm ▸ hz
    rw [← Q.coordinates_ker] at hz'
    exact hz'
  let E := (Equiv.ofBijective T ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen T.continuous hopen
  let φ := T.toMonoidHom.toAdditive
  have hp : IsProperMap φ := E.isProperMap
  let u₀ := elementarySchwartz_properPullback φ hp w
  refine ⟨Q.val.inclusionCLM u₀, fun x => ?_⟩
  have hx := congrArg (fun v : BruhatSchwartz G => v.val (e x)) hw
  change _ = v.val (e x) at hx
  rw [← hx]
  change Q.val.realize u₀ x = P.val.realize w (e x)
  rw [Q.realize_eq_coordinates, P.realize_eq_coordinates]
  change w (φ (Q.coordinates x).toAdd) = w (P.coordinates (e x)).toAdd
  exact congrArg (fun y => w y.toAdd) (hT x)

end
end Masullo
