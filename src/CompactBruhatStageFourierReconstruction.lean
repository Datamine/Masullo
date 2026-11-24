import CompactBruhatFourierSynthesis
import ModulatedDecaySplitCoordinates

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [T2Space K] [LocallyCompactSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
  (ν : Measure K) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]

set_option maxHeartbeats 2500000 in
/-- Fourier expansion converges in the intrinsic topology of a compact
Schwartz–Bruhat stage. -/
theorem hasSum_compactBruhatStage_elementaryFourier
    (p : WholeBruhatStage K) [CompactSpace p.CoordinateModel] (a : p.val.Space) :
    HasSum (fun θ : PontryaginDual (Multiplicative p.CoordinateModel) =>
      compactBruhatFourierCoeff ν (θ.comp p.coordinates) (p.val.inclusion a) •
        (compactElementaryInverseCharacterTest θ : p.val.Space)) a := by
  let A := p.CoordinateModel
  let Ω := PontryaginDual (Multiplicative A)
  letI : CompactSpace (Multiplicative A) := p.coordinates_surjective.compactSpace p.coordinates.continuous
  letI : MeasurableSpace (Multiplicative A) := borel _
  letI : BorelSpace (Multiplicative A) := ⟨rfl⟩
  let η : Measure (Multiplicative A) := ν.map p.coordinates
  letI : η.IsHaarMeasure := ν.isHaarMeasure_map_of_isFiniteMeasure p.coordinates.toMonoidHom
    p.coordinates.continuous p.coordinates_surjective
  let t (θ : Ω) : PontryaginDual K := θ.comp p.coordinates
  let B (θ : Ω) : p.val.Space := compactElementaryInverseCharacterTest θ
  let u (θ : Ω) := compactBruhatFourierCoeff ν (t θ) (p.val.inclusion a) • B θ
  have hν : (ν.real univ : ℂ)⁻¹ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one, Complex.ofReal_one, inv_one]
  have hu (θ : Ω) : u θ = elementaryFourierPairing η θ a • B θ := by
    have h := compactBruhatFourierCoeff_stage p ν θ a
    change compactBruhatFourierCoeff ν (t θ) (p.val.inclusion a) = _ at h
    rw [hν, one_mul] at h
    exact congrArg (fun c : ℂ => c • B θ) h
  have hsum : Summable (fun θ : Ω => elementaryFourierPairing η θ a • B θ) :=
    summable_elementaryFourierSeries_of_compact η a
  obtain ⟨z, hz⟩ := hsum
  have hs : HasSum u z := hz.congr_fun hu
  have ht : Injective t := by
    intro θ θ' he
    ext x
    obtain ⟨k, rfl⟩ := p.coordinates_surjective x
    exact congrArg (fun ψ : PontryaginDual K => (ψ k : ℂ)) he
  let v (χ : PontryaginDual K) := compactBruhatFourierCoeff ν χ (p.val.inclusion a) •
    compactBruhatCharacter χ⁻¹
  have hv (χ : PontryaginDual K) (hχ : χ ∉ range t) : v χ = 0 := by
    have hd : ∃ k ∈ p.val.1.kernel, χ k ≠ 1 := by
      by_contra! hh
      obtain ⟨θ, hθ, _⟩ := wholeBruhatStage_character_descends p χ hh
      exact hχ ⟨θ,hθ⟩
    exact (congrArg (· • compactBruhatCharacter χ⁻¹)
      (compactBruhatFourierCoeff_eq_zero_off_stage_annihilator ν p a χ hd)).trans (zero_smul _ _)
  have hincl (θ : Ω) : p.val.inclusionCLM (B θ) = compactBruhatCharacter (t θ)⁻¹ := by
    apply Subtype.ext
    funext k
    exact p.realize_eq_coordinates _ _
  have h1 : HasSum (v ∘ t) (p.val.inclusion z) := by
    refine (hs.mapL p.val.inclusionCLM).congr_fun fun θ => ?_
    rw [show (v ∘ t) θ = compactBruhatFourierCoeff ν (t θ) (p.val.inclusion a) •
      compactBruhatCharacter (t θ)⁻¹ from rfl, ← hincl θ]
    exact (map_smul p.val.inclusionCLM _ _).symm
  have h2 : HasSum (v ∘ t) (p.val.inclusion a) :=
    (ht.hasSum_iff hv).mpr (hasSum_compactBruhatFourierSeries ν (p.val.inclusion a))
  letI : T2Space (BruhatSchwartz K) := bruhatSchwartz_t2
  have he : z = a := p.val.1.realizeSchwartz_injective p.val.2 (congrArg Subtype.val (h1.unique h2))
  rw [he] at hs
  exact hs

end

end Masullo
