import ModulatedDecayStructure
import ModulatedJumpPoisson
import TorusLocalCharts

open Function Set Topology
open scoped Manifold

namespace Masullo

noncomputable section

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ)

private theorem locallyEuclidean_real_prod {K : Type*} [TopologicalSpace K]
    (hK : IsLocallyEuclidean K) : IsLocallyEuclidean (ℝ × K) := by
  obtain ⟨n,⟨c⟩⟩ := hK
  letI := c
  let V := EuclideanSpace ℝ (Fin n)
  let a : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique _ _
  let b : (Fin n → ℝ) ≃ₜ V := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.symm
  let e : EuclideanSpace ℝ (Fin (1+n)) ≃ₜ (ℝ × V) :=
    (EuclideanSpace.equiv (Fin (1+n)) ℝ).toHomeomorph.trans
      ((Fin.appendHomeomorph (X := ℝ) 1 n).symm.trans (a.prodCongr b))
  let e' : EuclideanSpace ℝ (Fin (1+n)) ≃ₜ ModelProd ℝ V := e
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (1+n))) (ModelProd ℝ V) := e'.chartedSpace
  letI : ChartedSpace (ModelProd ℝ V) (ℝ × K) :=
    prodChartedSpace ℝ ℝ V K
  exact ⟨1+n,⟨ChartedSpace.comp _ (ModelProd ℝ V) _⟩⟩

private theorem dual_compactlyGenerated_of_kernel (hm : IsProperMap m) (hms : Surjective m)
    (hK : IsCompactlyGeneratedGroup (PontryaginDual m.toMonoidHom.ker)) :
    IsCompactlyGeneratedGroup (PontryaginDual G) := by
  let K := m.toMonoidHom.ker
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp (hm.isCompact_preimage (K := {1}) isCompact_singleton)
  obtain ⟨eK,_⟩ := pontryaginDual_bidual (G := K)
  obtain ⟨n,⟨c⟩⟩ := isLocallyEuclidean_dual_of_compactlyGenerated hK
  letI := c
  have hlocK : IsLocallyEuclidean K := ⟨n,⟨eK.symm.toHomeomorph.chartedSpace⟩⟩
  obtain ⟨τ,hτ⟩ := exists_realModulation_section m hm hms
  obtain ⟨r,⟨d⟩⟩ := locallyEuclidean_real_prod hlocK
  letI := d
  obtain ⟨eG,_⟩ := pontryaginDual_bidual (G := G)
  let e := (modulatedLogSplit m τ hτ).trans eG.toHomeomorph
  exact (isCompactlyGeneratedGroup_iff_dual_locallyEuclidean (G := PontryaginDual G)).mpr
    ⟨r,⟨e.chartedSpace⟩⟩

/-- Compact generation of the kernel dual gives a whole-group quotient
with trivial structural kernel. -/
theorem exists_wholeBruhatStage_trivial_kernel (hm : IsProperMap m) (hms : Surjective m)
    (hK : IsCompactlyGeneratedGroup (PontryaginDual m.toMonoidHom.ker)) :
    ∃ p : WholeBruhatStage G, p.val.1.kernel = ⊥ := by
  obtain ⟨X,_,hX,hgen⟩ := dual_compactlyGenerated_of_kernel m hm hms hK
  obtain ⟨H,hH⟩ := exists_openCompactlyGeneratedSubgroup_contains hX
  have hle : Subgroup.closure X ≤ H.val := (Subgroup.closure_le (K := H.val)).mpr hH
  have htop : H.val = ⊤ := top_unique (hgen ▸ hle)
  obtain ⟨J,hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  let P := LCAStructuralPair.ofDual J H (show lcaDualAnnihilator H.val ≤ J.val from hJ ▸ le_top)
  have hbot : P.kernel = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    apply Subgroup.mem_bot.mpr
    by_contra hne
    obtain ⟨χ,hχ⟩ := exists_pontryaginDual_apply_ne_one hne
    exact hχ ((mem_lcaDualAnnihilator_iff H.val g).mp hg ⟨χ,htop.symm ▸ Subgroup.mem_top χ⟩)
  obtain ⟨e⟩ := P.quotient_elementary
  exact ⟨⟨⟨P,e⟩,hJ⟩,hbot⟩

set_option maxHeartbeats 1800000 in
/-- Under the compact-generation hypothesis of Theorem D.3.3.7(2),
the full inductive decay space is nuclear Fréchet. -/
theorem modulatedDecay_nuclearFrechet_of_compactlyGeneratedKernelDual [SecondCountableTopology G]
    (I : Set ℝ) (hI : I.Nonempty) (hm : IsProperMap m) (hms : Surjective m)
    (hK : IsCompactlyGeneratedGroup (PontryaginDual m.toMonoidHom.ker)) :
    NuclearLocallyConvex.{u,u} (ModulatedExponentialInductive m I) ∧
      IsFrechetTVS (ModulatedExponentialInductive m I) := by
  obtain ⟨p,hp⟩ := exists_wholeBruhatStage_trivial_kernel m hm hms hK
  let E := ModulatedExponentialInductive m I
  let X := WholeBruhatDecayStage m I p
  let j : X →L[ℂ] E :=
    ⟨ModulatedExponentialInductive.stageMap p, ModulatedExponentialInductive.stageMap_continuous p⟩
  have hEmb : IsEmbedding j := wholeBruhatDecayStage_isEmbedding m I hI p
  have hSurj : Surjective j := by
    intro f
    obtain ⟨q,hq⟩ := exists_wholeBruhatStage_decay m I hm hms hI
      (ModulatedExponentialInductive.algebraicEquiv f)
    have hqp : q.val.1 ≤ p.val.1 := by
      change q.val.1.upper.val ≤ p.val.1.upper.val ∧ p.val.1.kernel ≤ q.val.1.kernel
      rw [p.property, hp]
      exact ⟨le_top,bot_le⟩
    have hmem (a : I) : modulatedExponentialWeight m a f.val ∈ p.val.realize.range := by
      obtain ⟨w,hw⟩ := hq a
      have h := q.val.inclusion_transition p.val hqp w
      exact ⟨q.val.transition p.val hqp w,
        (congrArg (fun u : BruhatSchwartz G => u.val) h).trans hw⟩
    let z : wholeBruhatDecayStageSubmodule m I p := ⟨f.val,(Submodule.mem_iInf _).mpr hmem⟩
    let g : X := WholeBruhatDecayStage.algebraicEquiv.symm z
    exact ⟨g, ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext rfl)⟩
  letI : TopologicalSpace.MetrizableSpace X :=
    (wholeBruhatDecayStage_metrizable_secondCountable m hI p).1
  have hM : TopologicalSpace.MetrizableSpace E := (hEmb.toHomeomorphOfSurjective hSurj).symm.isEmbedding.metrizableSpace
  obtain ⟨hc,hn,_⟩ := modulatedDecay_complete_nuclear_montel m I hm hms hI
  exact ⟨hn,⟨(PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup,inferInstance,hM,hc⟩⟩

end

end Masullo
