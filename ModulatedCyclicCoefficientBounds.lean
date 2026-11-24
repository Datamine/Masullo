import ModulatedCyclicFourier
import BruhatIsotypeComparison

open Bornology Function MeasureTheory Set Topology

namespace Masullo

noncomputable section
set_option maxHeartbeats 1200000

variable {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] [LocallyCompactSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

local instance {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] : UniformSpace (BruhatSchwartz X) :=
  bruhatSchwartzUniformSpace

local instance {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] : IsUniformAddGroup (BruhatSchwartz X) :=
  isUniformAddGroup_of_addCommGroup

local instance {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] : ContinuousSMul ℂ (BruhatSchwartz X) :=
  (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz X)).continuousSMul

local instance {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] (H : Submodule ℂ (BruhatSchwartz X)) :
    AddCommGroup H := H.addCommGroup

/-- The normalized Fourier coefficients of a compact Schwartz–Bruhat group
are pointwise bounded independently of the character. Adapted from
mccorvie/riemann-masullo, commit 0d4907c (Apache-2.0). -/
theorem compactBruhatFourierCoeff_norm_le (ν : Measure Q) [IsFiniteMeasure ν]
    (ψ : PontryaginDual Q) (f : BruhatSchwartz Q) :
    ‖compactBruhatFourierCoeff ν ψ f‖ ≤
      ‖(ν.real univ : ℂ)⁻¹‖ * ∫ q, ‖f.val q‖ ∂ν := by
  rw [compactBruhatFourierCoeff_apply, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [norm_mul, Circle.norm_coe, mul_one] using
    (norm_integral_le_integral_norm (μ := ν) (fun q ↦ f.val q * (ψ q : ℂ)))

/-- Compact Fourier coefficients form an equicontinuous family and are bounded
in the strong dual. The same holds on every subspace with its induced topology. -/
theorem compactBruhatFourierCoeff_family {ι : Type*}
    (ν : Measure Q) [IsFiniteMeasure ν] (ψ : ι → PontryaginDual Q)
    (H : Submodule ℂ (BruhatSchwartz Q)) :
    IsVonNBounded ℂ (range (fun i ↦ compactBruhatFourierCoeff ν (ψ i))) ∧
    IsVonNBounded ℂ (range (fun i ↦ (compactBruhatFourierCoeff ν (ψ i)).comp H.subtypeL)) ∧
    Equicontinuous (fun (i : ι) (f : H) ↦ compactBruhatFourierCoeff ν (ψ i) f.val) := by
  let E := BruhatSchwartz Q
  letI : BarrelledSpace ℂ E := bruhatSchwartz_barrelled
  let a (i : ι) : E →L[ℂ] ℂ := compactBruhatFourierCoeff ν (ψ i)
  have hp (f : E) : IsVonNBounded ℂ (range fun i ↦ a i f) := by
    apply (NormedSpace.isVonNBounded_iff' ℂ).2
    refine ⟨‖(ν.real univ : ℂ)⁻¹‖ * ∫ q, ‖f.val q‖ ∂ν, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact compactBruhatFourierCoeff_norm_le ν (ψ i) f
  have hu := PolynormableSpace.banach_steinhaus (𝓕 := a) hp
  obtain ⟨p, hpcont, hle⟩ :=
    ((norm_withSeminorms ℂ ℂ).uniformEquicontinuous_iff_exists_continuous_seminorm
      (fun i ↦ (a i).toLinearMap)).1 hu 0
  have hb : IsVonNBounded ℂ (range a) := by
    apply ContinuousLinearMap.isVonNBounded_iff.2
    intro S hS
    let j := localBanachMap p hpcont
    obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℂ).1 (hS.image j)
    apply (NormedSpace.isVonNBounded_iff' ℂ).2
    refine ⟨R, ?_⟩
    rintro _ ⟨_, ⟨i, rfl⟩, x, hx, rfl⟩
    have hxR := hR (j x) (mem_image_of_mem j hx)
    change ‖localBanachDenseMap p x‖ ≤ R at hxR
    rw [norm_localBanachDenseMap] at hxR
    exact (hle i x).trans hxR
  refine ⟨hb, ?_, ?_⟩
  · let L : StrongDual ℂ E →L[ℂ] StrongDual ℂ H := H.subtypeL.precomp ℂ
    change IsVonNBounded ℂ (range (L ∘ a))
    rw [range_comp]
    exact Bornology.IsVonNBounded.image (𝕜₁ := ℂ) (𝕜₂ := ℂ) (E := StrongDual ℂ E)
      (F := StrongDual ℂ H) hb L
  · intro f U hU
    exact (continuous_subtype_val.tendsto f).eventually (hu.equicontinuous f.val U hU)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Corollary 4.5.1.5. The normalized cyclic coefficient family on the
Schwartz–Bruhat quotient is strongly bounded. Its restrictions to the
norm-one character isotype are strongly bounded and equicontinuous. -/
theorem modulatedCyclicFourierCoeff_bounded_equicontinuous
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd)
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [CompactSpace (G ⧸ Subgroup.zpowers γ)] [MeasurableSpace (G ⧸ Subgroup.zpowers γ)]
    [BorelSpace (G ⧸ Subgroup.zpowers γ)]
    (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure] (χ : CircleCharacter G) :
    let Q := G ⧸ Subgroup.zpowers γ
    let ρ := bruhatSchwartzTranslationAction (G := Q)
    let qK := (QuotientGroup.mk' (Subgroup.zpowers γ)).comp m.toMonoidHom.ker.subtype
    let A := twistedCircleAction (χ.toMonoidHom.comp m.toMonoidHom.ker.subtype) (ρ.comp qK)
    let H := fixedSubmodule A
    let a (n : ℤ) := compactBruhatFourierCoeff ν (modulatedCyclicCharacter m γ hγ χ n)
    IsClosed (H : Set (BruhatSchwartz Q)) ∧
    (∀ n f, a n f = modulatedCyclicFourierCoeff m γ hγ ν χ n f) ∧
    IsVonNBounded ℂ (range a) ∧
    IsVonNBounded ℂ (range (fun n ↦ (a n).comp H.subtypeL)) ∧
    Equicontinuous (fun (n : ℤ) (f : H) ↦ a n f.val) := by
  dsimp only
  letI : T2Space (BruhatSchwartz (G ⧸ Subgroup.zpowers γ)) := bruhatSchwartz_t2
  exact ⟨fixedSubmodule_isClosed _,
    fun n f ↦ (modulatedCyclicFourierCoeff_eq_compact m γ hγ ν χ n f).symm,
    compactBruhatFourierCoeff_family ν (modulatedCyclicCharacter m γ hγ χ) _⟩

end

end Masullo
