import BruhatSupportedCompactQuotient
import BruhatSupportedFixedWindow

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 2500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
variable (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)
variable (K : Subgroup G) (hK : IsCompact (K : Set G)) (hKm : K ≤ m.toMonoidHom.ker)
variable (hgen : IsCompactlyGeneratedGroup (lcaAnnihilator (K.comap m.toMonoidHom.ker.subtype)))

local notation "logModulus" => (fun x : G ↦ Multiplicative.toAdd (m x))
local notation "E" => ModulatedExponentialInductive m univ

variable (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "N" => (K ⊔ Subgroup.zpowers γ : Subgroup G)
local notation "JointQuotient" => G ⧸ N

include hm hτ hK hKm hgen hγ in
/-- Proposition 4.5.2.1(2)–(3) with the corrected support interval for
compact division. The kernel quotient is the actual compact-quotient
Schwartz–Bruhat space and its canonical map is the orbit sum. -/
theorem bruhatSupportedInvariant_periodicQuotient (a b : ℝ) (hab : a + (m γ).toAdd < b) :
    letI : IsClosed (N : Set G) := modulatedCompactCyclicSubgroup_isClosed m K hK hKm γ hγ
    let U := bruhatSupportedInvariant m K (logModulus ⁻¹' Icc a b)
    (QuotientGroup.mk : G → G ⧸ Subgroup.zpowers γ) '' (logModulus ⁻¹' Icc a b) = univ ∧
      ∃ (T : U →L[ℂ] BruhatSchwartz JointQuotient) (e : (U ⧸ T.ker) ≃L[ℂ] BruhatSchwartz JointQuotient),
        (∀ f : U, e (T.ker.mkQ f) = T f) ∧
        (∀ (f : U) (x : G), (T f).val (QuotientGroup.mk x) = ∑' j : ℤ, f.val.val (γ ^ j * x)) ∧
        ∀ f : U, T f = 0 →
          ∃ v : bruhatSupportedInvariant m K (logModulus ⁻¹' Icc (a + (m γ).toAdd) b),
            ∀ x, v.val.val x - v.val.val (γ * x) = f.val.val x := by
  letI : IsClosed (N : Set G) := modulatedCompactCyclicSubgroup_isClosed m K hK hKm γ hγ
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : ContinuousSMul ℂ (BruhatSchwartz JointQuotient) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz JointQuotient)).continuousSMul
  let U := bruhatSupportedInvariant m K (logModulus ⁻¹' Icc a b)
  have hms : Surjective m := fun t ↦ ⟨τ t, hτ t⟩
  have hGen := modulatedAnnihilator_compactlyGenerated m τ hτ K hK hKm hgen
  obtain ⟨P, hP⟩ := exists_wholeBruhatStage_kernel m hm hms K hK hGen
  obtain ⟨T, S, hS, hT⟩ := exists_supportedCompactQuotient_periodization_section
    m hm γ hγ K hms hK hKm P hP a b hab
  obtain ⟨e, he⟩ := splitQuotientEquiv_scaled (X := ↥U) (Y := BruhatSchwartz JointQuotient) T S hS 1 one_ne_zero
  refine ⟨bruhatCyclicQuotient_image_window m γ hγ a b hab, T, e,
    fun f ↦ (he f).trans (one_smul ℂ (T f)), hT, fun f hf ↦ ?_⟩
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  have hzero (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x (J f.val) = 0 := by
    exact (bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x (J f.val)).trans
      ((hT f x).symm.trans (congrArg (fun g : BruhatSchwartz JointQuotient ↦
        g.val (QuotientGroup.mk x)) hf))
  obtain ⟨v, hvs, hvi, hv⟩ := bruhatCyclicInvariantCompact_difference m hm hms
    γ hγ K (J f.val) a b f.property.1 f.property.2 hzero
  exact ⟨⟨v, hvs, hvi⟩, hv⟩

end

end Masullo
