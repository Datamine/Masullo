import CompactElementaryFourierDecay
import BruhatSchwartzReflexivity
import DyninMityagin

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 8

section Compact

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Every Schwartz–Bruhat test on a compact group is represented on a stage
whose upper subgroup is the whole group. -/
theorem exists_compactBruhat_wholeStage (f : BruhatSchwartz G) :
    ∃ (P : WholeBruhatStage G) (u : P.val.Space), P.val.inclusion u = f := by
  obtain ⟨p, u, hu⟩ := f.property
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains (K := (univ : Set G)) isCompact_univ
  have htop : J.val = ⊤ := top_unique fun _ _ ↦ hJ (mem_univ _)
  let Q : LCAStructuralPair G :=
    ⟨J, p.1.kernel, p.1.kernel_closed, p.1.annihilator_open, p.1.annihilator_compactlyGenerated,
      by rw [htop]; exact le_top⟩
  obtain ⟨q⟩ := Q.quotient_elementary
  obtain ⟨L, _, hL⟩ := p.1.schwartz_refinement_closedEmbedding Q
    (show p.1.upper.val ≤ J.val by rw [htop]; exact le_top) le_rfl p.2 q
  exact ⟨⟨⟨Q, q⟩, htop⟩, L u, Subtype.ext ((hL u).trans hu)⟩

variable (μ : Measure G) [μ.IsHaarMeasure]

private theorem summable_compactBruhatFourierSeries_stage
    (P : WholeBruhatStage G) (u : P.val.Space) :
    Summable (fun χ : PontryaginDual G ↦
      compactBruhatFourierCoeff μ χ (P.val.inclusion u) • compactBruhatCharacter χ⁻¹) := by
  let A := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim
    P.val.2.latticeRank P.val.2.finiteFactor
  letI : CompactSpace (Multiplicative A) :=
    P.coordinates_surjective.compactSpace P.coordinates.continuous
  letI : CompactSpace A := Multiplicative.toAdd.surjective.compactSpace continuous_toAdd
  letI : MeasurableSpace (Multiplicative A) := borel _
  letI : BorelSpace (Multiplicative A) := ⟨rfl⟩
  let ν : Measure (Multiplicative A) := μ.map P.coordinates
  letI : ν.IsHaarMeasure := μ.isHaarMeasure_map_of_isFiniteMeasure P.coordinates.toMonoidHom
    P.coordinates.continuous P.coordinates_surjective
  let t (θ : PontryaginDual (Multiplicative A)) : PontryaginDual G := θ.comp P.coordinates
  have ht : Injective t := by
    intro θ η h
    ext z
    obtain ⟨x, rfl⟩ := P.coordinates_surjective z
    exact congrArg (fun χ : PontryaginDual G ↦ (χ x : ℂ)) h
  let g (χ : PontryaginDual G) :=
    compactBruhatFourierCoeff μ χ (P.val.inclusion u) • compactBruhatCharacter χ⁻¹
  have hz (χ : PontryaginDual G) (hχ : χ ∉ range t) : g χ = 0 := by
    have h : ∃ a ∈ P.val.1.kernel, χ a ≠ 1 := by
      by_contra! hh
      obtain ⟨θ, hθ, _⟩ := wholeBruhatStage_character_descends P χ hh
      exact hχ ⟨θ, hθ⟩
    exact (congrArg (· • compactBruhatCharacter χ⁻¹)
      (compactBruhatFourierCoeff_eq_zero_off_stage_annihilator μ P u χ h)).trans (zero_smul _ _)
  let L : P.val.Space →L[ℂ] BruhatSchwartz G := (μ.real univ : ℂ)⁻¹ • P.val.inclusionCLM
  have hsum := L.summable (summable_elementaryFourierSeries_of_compact ν u)
  obtain ⟨f, hf⟩ := hsum
  refine ⟨f, (ht.hasSum_iff hz).mp (hf.congr_fun fun θ ↦ ?_)⟩
  have hv : P.val.inclusionCLM (compactElementaryInverseCharacterTest θ) = compactBruhatCharacter (t θ)⁻¹ := by
    apply Subtype.ext
    funext x
    exact P.realize_eq_coordinates _ x
  symm
  change L (elementaryFourierPairing ν θ u • compactElementaryInverseCharacterTest θ) = g (t θ)
  rw [show g (t θ) =
    compactBruhatFourierCoeff μ (θ.comp P.coordinates) (P.val.inclusion u) •
      compactBruhatCharacter (t θ)⁻¹ from rfl, compactBruhatFourierCoeff_stage]
  simp only [L, smul_apply, map_smul, hv, smul_smul]
  exact congrArg (· • compactBruhatCharacter (t θ)⁻¹)
    (mul_comm (elementaryFourierPairing ν θ u) (μ.real univ : ℂ)⁻¹)

/-- The normalized inverse character series reconstructs every compact
Schwartz–Bruhat test in its original topology. -/
theorem hasSum_compactBruhatFourierSeries (f : BruhatSchwartz G) :
    HasSum (fun χ : PontryaginDual G ↦
      compactBruhatFourierCoeff μ χ f • compactBruhatCharacter χ⁻¹) f := by
  classical
  obtain ⟨P, u, rfl⟩ := exists_compactBruhat_wholeStage f
  obtain ⟨v, hv⟩ := summable_compactBruhatFourierSeries_stage μ P u
  suffices he : v = P.val.inclusion u by simpa only [he] using hv
  apply sub_eq_zero.mp
  apply compactBruhatFourierCoeff_separate μ
  intro ψ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have h := hv.mapL (compactBruhatFourierCoeff μ ψ)
  refine h.unique ((hasSum_ite_eq ψ (compactBruhatFourierCoeff μ ψ (P.val.inclusion u))).congr_fun ?_)
  intro χ
  rw [map_smul, compactBruhatFourierCoeff_character]
  split_ifs with hχ
  · subst χ
    simp
  · simp

variable [SecondCountableTopology G]

/-- Any enumeration of the characters gives an absolute Schauder basis,
whose coefficient functionals form an unconditional basis of the strong dual. -/
theorem compactBruhatFourierSeries_absoluteBasis (e : ℕ ≃ PontryaginDual G) :
    let x := fun n ↦ compactBruhatCharacter (e n)⁻¹
    let a := fun n ↦ compactBruhatFourierCoeff μ (e n)
    IsSchauderBasis x a ∧ IsAbsolute x a ∧ IsShrinking x a ∧
      IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
  classical
  dsimp only
  let x := fun n ↦ compactBruhatCharacter (e n)⁻¹
  let a := fun n ↦ compactBruhatFourierCoeff μ (e n)
  letI : T2Space (BruhatSchwartz G) := bruhatSchwartz_t2
  letI : BarrelledSpace ℂ (BruhatSchwartz G) := bruhatSchwartz_barrelled
  letI : ContinuousSMul ℂ (BruhatSchwartz G) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz G)).continuousSMul
  have hb : IsSchauderBasis x a := by
    refine ⟨fun m n ↦ ?_, fun f ↦ ?_⟩
    · rw [show a m (x n) = compactBruhatFourierCoeff μ (e m) (compactBruhatCharacter (e n)⁻¹) from rfl,
        compactBruhatFourierCoeff_character]
      simp [eq_comm]
    · exact Tendsto.mono_left (e.hasSum_iff.mpr (hasSum_compactBruhatFourierSeries μ f))
        (SummationFilter.conditional ℕ).le_atTop
  have ha : IsAbsolute x a :=
    isAbsolute_of_isNuclearTVS bruhatSchwartz_nuclear hb (schauderBasis_equicontinuous_of_barrelled hb)
  obtain ⟨j, hj⟩ := bruhatSchwartz_reflexive (G := G)
  have hEval : IsHomeomorph (strongBidualEvaluation (E := BruhatSchwartz G)) := by
    have he : (strongBidualEvaluation (E := BruhatSchwartz G) :
        BruhatSchwartz G → StrongDual ℂ (StrongDual ℂ (BruhatSchwartz G))) = j := by
      funext f
      ext l
      exact (hj f l).symm
    rw [he]
    exact j.toHomeomorph.isHomeomorph
  exact ⟨hb, ha, isShrinking_of_isAbsolute hEval hb ha,
    strongDual_isUnconditional_of_isAbsolute hEval hb ha⟩

end Compact

end

end Masullo
