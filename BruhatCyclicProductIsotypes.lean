import BruhatCyclicProductSections
import ModulatedDecayIsotypes

open Function Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (w : PontryaginDual m.toMonoidHom.ker)

private theorem cyclicDifferenceProduct_isotypeClasses
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G)
    (R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
    (hR : ∀ f, f - modulatedDecay_zeroInclusion m I h0 (R f) ∈
      (bruhatSchwartzDifferenceProduct gs).range)
    (hRiso : ∀ f, CyclicNormOneIsotypic m w f.val → CyclicNormOneIsotypic m w (R f).val) :
    let V := (bruhatSchwartzDifferenceProduct gs).range
    (V.mkQ ∘ modulatedDecay_zeroInclusion m I h0) '' (modulatedDecayIsotype m w I : Set _) =
      V.mkQ '' {f : BruhatSchwartz G | CyclicNormOneIsotypic m w f.val} := by
  intro V
  let J := modulatedDecay_zeroInclusion m I h0
  apply subset_antisymm
  · rintro y ⟨f, hf, rfl⟩
    exact ⟨J f, hf, rfl⟩
  · rintro y ⟨f, hf, rfl⟩
    refine ⟨R f, hRiso f hf, (Submodule.Quotient.eq V).2 ?_⟩
    change J (R f) - f ∈ V
    simpa only [neg_sub] using V.neg_mem (hR f)

include hm hms in
/-- The canonical ambient quotient comparisons carry the images of the
norm-one isotypes exactly onto the corresponding images in the targets. -/
theorem cyclicDifferenceProduct_quotientComparisons_preserve_isotypes
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G)
    (R₀ : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m univ)
    (R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
    (hR₀ : ∀ f, f - modulatedDecay_zeroInclusion m univ (mem_univ 0) (R₀ f) ∈
      (bruhatSchwartzDifferenceProduct gs).range)
    (hR : ∀ f, f - modulatedDecay_zeroInclusion m I h0 (R f) ∈
      (bruhatSchwartzDifferenceProduct gs).range)
    (hR₀iso : ∀ f, CyclicNormOneIsotypic m w f.val → CyclicNormOneIsotypic m w (R₀ f).val)
    (hRiso : ∀ f, CyclicNormOneIsotypic m w f.val → CyclicNormOneIsotypic m w (R f).val) :
    let W₀ := (modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs).range
    let W := (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range
    let V := (bruhatSchwartzDifferenceProduct gs).range
    ∀ (D : (ModulatedExponentialInductive m univ ⧸ W₀) →L[ℂ] (ModulatedExponentialInductive m I ⧸ W))
      (C : (ModulatedExponentialInductive m I ⧸ W) →L[ℂ] (BruhatSchwartz G ⧸ V)),
      (∀ f, D (W₀.mkQ f) = W.mkQ (modulatedDecay_restrict m (subset_univ I) f)) →
      (∀ f, C (W.mkQ f) = V.mkQ (modulatedDecay_zeroInclusion m I h0 f)) →
      Injective C →
      D '' (W₀.mkQ '' (modulatedDecayIsotype m w univ : Set _)) =
        W.mkQ '' (modulatedDecayIsotype m w I : Set _) ∧
      C '' (W.mkQ '' (modulatedDecayIsotype m w I : Set _)) =
        V.mkQ '' {f : BruhatSchwartz G | CyclicNormOneIsotypic m w f.val} := by
  intro W₀ W V D C hD hC hi
  let E := modulatedDecayIsotype m w univ
  let F := modulatedDecayIsotype m w I
  have hCF : C '' (W.mkQ '' (F : Set _)) =
      (V.mkQ ∘ modulatedDecay_zeroInclusion m I h0) '' (F : Set _) := by
    rw [image_image]
    exact image_congr fun f _ ↦ hC f
  have hDE : (C ∘ D) '' (W₀.mkQ '' (E : Set _)) =
      (V.mkQ ∘ modulatedDecay_zeroInclusion m univ (mem_univ 0)) '' (E : Set _) := by
    rw [image_image]
    apply image_congr
    intro f _
    have hr : modulatedDecay_zeroInclusion m I h0 (modulatedDecay_restrict m (subset_univ I) f) =
        modulatedDecay_zeroInclusion m univ (mem_univ 0) f :=
      Subtype.ext (modulatedDecay_restrict_apply m (subset_univ I) f)
    exact (congrArg C (hD f)).trans ((hC _).trans (congrArg V.mkQ hr))
  have h₂ := hCF.trans (cyclicDifferenceProduct_isotypeClasses m w I h0 gs R hR hRiso)
  refine ⟨?_, h₂⟩
  apply image_injective.mpr hi
  rw [image_image]
  exact (hDE.trans (cyclicDifferenceProduct_isotypeClasses m w univ (mem_univ 0) gs R₀ hR₀ hR₀iso)).trans h₂.symm

end

end Masullo
