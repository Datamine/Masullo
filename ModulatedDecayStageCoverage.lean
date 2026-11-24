import ModulatedDecaySplitProducts
import PontryaginAnnihilators
import ModulatedDecayTopology

open Filter Function Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Every compact subgroup with compactly generated orthogonal appears as a
whole-group quotient stage for the modulated decay space. -/
theorem exists_wholeBruhatStage_of_compact_kernel
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m) (k : Subgroup G)
    (hk : IsCompact (k : Set G)) (horth : IsCompactlyGeneratedGroup (lcaAnnihilator k)) :
    ∃ q : WholeBruhatStage G, q.val.1.kernel = k := by
  obtain ⟨J, hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  let Q : LCAStructuralPair G :=
    ⟨J, k, hk.isClosed, isOpen_lcaAnnihilator k hk, horth, by rw [hJ]; exact le_top⟩
  obtain ⟨e⟩ := Q.quotient_elementary
  exact ⟨⟨⟨Q, e⟩, hJ⟩, rfl⟩

set_option maxHeartbeats 900000 in
/-- Every whole-group quotient stage has an angular stage with the same
kernel, transported through the inclusion of the modulus kernel. -/
theorem exists_angularStage_matching_decayStage
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (q : WholeBruhatStage G) :
    ∃ p : WholeBruhatStage m.toMonoidHom.ker,
      q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype := by
  let K := m.toMonoidHom.ker
  let P := q.val.1
  let N := P.kernel
  let L := N.comap K.subtype
  have hK : IsCompact (K : Set G) :=
    hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ)))
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hN : IsCompact (N : Set G) := by
    change IsCompact (P.kernel : Set G)
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  have hL : IsCompact (L : Set K) := hK.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hN
  let A := lcaAnnihilator N
  let B := lcaAnnihilator L
  let f := PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
  let j : A →* B := (f.toMonoidHom.comp A.subtype).codRestrict B fun χ ↦
    (mem_lcaAnnihilator_iff L _).mpr fun x ↦
      (mem_lcaAnnihilator_iff N χ.val).mp χ.property ⟨(x.val : G), x.property⟩
  have hj : Continuous j := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hs : Surjective j := by
    intro χ
    obtain ⟨ψ, hψ, hψN⟩ := exists_pontryaginDual_extension_trivial_on_compact K N hK.isClosed hN χ.val
      (fun x hx ↦ (mem_lcaAnnihilator_iff L χ.val).mp χ.property ⟨x, hx⟩)
    exact ⟨⟨ψ, (mem_lcaAnnihilator_iff N ψ).mpr hψN⟩, Subtype.ext (PontryaginDual.ext hψ)⟩
  have hB : IsCompactlyGeneratedGroup B := by
    obtain ⟨C, hC, hCc, hgen⟩ := P.annihilator_compactlyGenerated
    refine ⟨j '' C, mem_nhds_discrete.mpr ⟨1, mem_of_mem_nhds hC, map_one j⟩,
      hCc.image hj, ?_⟩
    rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ hs]
  let eTop : (⊤ : Subgroup K) ≃ₜ* K :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  have hgenK : IsCompactlyGeneratedGroup K :=
    ⟨univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩
  let J : OpenCompactlyGeneratedSubgroups K :=
    ⟨⊤, isOpen_univ, compactGeneration_transport eTop.symm hgenK⟩
  let Q : LCAStructuralPair K := ⟨J, L, hL.isClosed, isOpen_lcaAnnihilator _ hL, hB, le_top⟩
  obtain ⟨b⟩ := Q.quotient_elementary
  refine ⟨⟨⟨Q, b⟩, rfl⟩, ?_⟩
  change N = L.map K.subtype
  ext g
  constructor
  · intro hg
    let u : K := ⟨g, P.modulation_eq_one_on_kernel m ⟨g, hg⟩⟩
    exact ⟨u, hg, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact hu

set_option maxHeartbeats 600000 in
/-- Every full-space decay test is represented on a whole-group stage
whose kernel is the image of an angular stage kernel. -/
theorem exists_matchingStages_of_decayTest
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (I : Set ℝ) (hI : I.Nonempty) (f : ModulatedExponentialInductive m I) :
    ∃ (p : WholeBruhatStage m.toMonoidHom.ker) (q : WholeBruhatStage G)
      (u : WholeBruhatDecayStage m I q),
      q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype ∧
        ModulatedExponentialInductive.stageMap q u = f := by
  obtain ⟨q, hq⟩ := exists_wholeBruhatStage_decay m I hm hms hI
    (ModulatedExponentialInductive.algebraicEquiv f)
  obtain ⟨p, hp⟩ := exists_angularStage_matching_decayStage m hm q
  let u : WholeBruhatDecayStage m I q :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨f.val, (Submodule.mem_iInf _).mpr hq⟩
  exact ⟨p, q, u, hp, ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext rfl)⟩


omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Refinement of matching whole-group stages implies refinement of their angular stages. -/
theorem angularStage_le_of_matching
    (m : G →ₜ* Multiplicative ℝ)
    (p p' : WholeBruhatStage m.toMonoidHom.ker) (q q' : WholeBruhatStage G)
    (hp : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (hp' : q'.val.1.kernel = p'.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (hq : q.val.1 ≤ q'.val.1) : p.val.1 ≤ p'.val.1 := by
  refine ⟨?_, ?_⟩
  · change p.val.1.upper.val ≤ p'.val.1.upper.val
    rw [p'.property]
    exact le_top
  · intro u hu
    have hnu : u.val ∈ q'.val.1.kernel := hp'.symm ▸ ⟨u, hu, rfl⟩
    have hku : u.val ∈ q.val.1.kernel := hq.2 hnu
    obtain ⟨v, hv, he⟩ := hp ▸ hku
    exact (Subtype.ext he : v = u) ▸ hv

/-- An increasing sequence of whole-group stages has matching increasing
angular stages, with the same kernels after inclusion. -/
theorem exists_matching_angularStages
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (q : ℕ → WholeBruhatStage G) (hq : Monotone (fun n => (q n).val.1)) :
    ∃ p : ℕ → WholeBruhatStage m.toMonoidHom.ker,
      Monotone (fun n => (p n).val.1) ∧
      ∀ n, (q n).val.1.kernel = (p n).val.1.kernel.map m.toMonoidHom.ker.subtype := by
  choose p hker using fun n : ℕ => exists_angularStage_matching_decayStage m hm (q n)
  exact ⟨p, fun k n hkn => angularStage_le_of_matching m (p k) (p n) (q k) (q n)
    (hker k) (hker n) (hq hkn), hker⟩

set_option maxHeartbeats 650000 in
/-- Cofinal angular and whole-group stages can be indexed by a common
increasing sequence with matched kernels at every index. -/
theorem exists_cofinal_matchingStageSequences [SecondCountableTopology G]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    [LocallyCompactSpace m.toMonoidHom.ker] :
    ∃ (p : ℕ → WholeBruhatStage m.toMonoidHom.ker) (q : ℕ → WholeBruhatStage G),
      Monotone (fun n => (p n).val.1) ∧ Monotone (fun n => (q n).val.1) ∧
      (∀ v : BruhatSchwartzStage m.toMonoidHom.ker, ∃ n, v.1 ≤ (p n).val.1) ∧
      (∀ w : WholeBruhatStage G, ∃ n, w.val.1 ≤ (q n).val.1) ∧
      ∀ n, (q n).val.1.kernel = (p n).val.1.kernel.map m.toMonoidHom.ker.subtype := by
  let K := m.toMonoidHom.ker
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  obtain ⟨q, hq, hCov⟩ := exists_wholeBruhatStage_cofinal m hm hτ.surjective
  obtain ⟨p, hp, hker⟩ := exists_matching_angularStages m hm q hq
  refine ⟨p, q, hp, hq, ?_, hCov, hker⟩
  intro v
  obtain ⟨w, hw⟩ := exists_wholeBruhatStage_refinement_of_compact v
  obtain ⟨q₀, hq₀⟩ := exists_splitStage_exact_kernel m τ hτ hm w
  obtain ⟨n, hn⟩ := hCov q₀
  exact ⟨n, hw.trans (angularStage_le_of_matching m w (p n) q₀ (q n) hq₀ (hker n) hn)⟩

end
end Masullo
