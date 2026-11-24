import BruhatCyclicProductSections
import BruhatCyclicProductIsotypes
import BruhatCyclicResidual

open Function Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)

include hm hms in
private theorem exists_cyclicProduct_representative
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd) :
    ∃ R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I,
      (∀ f, f - modulatedDecay_zeroInclusion m I h0 (R f) ∈ (bruhatSchwartzDifferenceProduct gs).range) ∧
      ∀ w f, CyclicNormOneIsotypic m w f.val → CyclicNormOneIsotypic m w (R f).val := by
  exact exists_modulatedDecay_cyclicDifferenceProduct_representativeMap m hm hms I h0 gs
    (fun γ hγ ↦ exists_bruhatCyclic_split m hm hms γ (hgs γ hγ) I h0)

/-- Corollary 4.6.3.1, pp. 219–220. The canonical comparisons between
the three full finite-difference quotients are topological isomorphisms,
and carry each norm-one isotype image onto its counterpart. -/
theorem bruhatCyclicProduct_corollary
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd) :
    let W₀ := (modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs).range
    let W := (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range
    let V := (bruhatSchwartzDifferenceProduct gs).range
    ∃ (D : (ModulatedExponentialInductive m univ ⧸ W₀) ≃L[ℂ] (ModulatedExponentialInductive m I ⧸ W))
      (C : (ModulatedExponentialInductive m I ⧸ W) ≃L[ℂ] (BruhatSchwartz G ⧸ V)),
      (∀ f, D (W₀.mkQ f) = W.mkQ (modulatedDecay_restrict m (subset_univ I) f)) ∧
      (∀ f, C (W.mkQ f) = V.mkQ (modulatedDecay_zeroInclusion m I h0 f)) ∧
      ∀ w : PontryaginDual m.toMonoidHom.ker,
        D '' (W₀.mkQ '' (modulatedDecayIsotype m w univ : Set _)) =
          W.mkQ '' (modulatedDecayIsotype m w I : Set _) ∧
        C '' (W.mkQ '' (modulatedDecayIsotype m w I : Set _)) = V.mkQ '' {f : BruhatSchwartz G | CyclicNormOneIsotypic m w f.val} := by
  intro W₀ W V
  obtain ⟨R₀, hR₀, hR₀iso⟩ := exists_cyclicProduct_representative m hm hms univ (mem_univ 0) gs hgs
  obtain ⟨R, hR, hRiso⟩ := exists_cyclicProduct_representative m hm hms I h0 gs hgs
  obtain ⟨D, C, hD, hC⟩ :=
    exists_modulatedDecay_cyclicDifferenceProduct_quotientEquivs_of_representativeMaps
      m hm hms I h0 gs hgs R₀ R hR₀ hR
  exact ⟨D, C, hD, hC, fun w ↦
    cyclicDifferenceProduct_quotientComparisons_preserve_isotypes m hm hms w I h0 gs
      R₀ R hR₀ hR (hR₀iso w) (hRiso w)
      D.toContinuousLinearMap C.toContinuousLinearMap hD hC C.injective⟩

end

end Masullo
