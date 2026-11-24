import BruhatCyclicProductQuotients
import BruhatCyclicResidual

open Function Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)

include hm hms in
/-- A continuously split cyclic difference for each generator gives a continuous
choice of representative in the decay space for the full product quotient. -/
theorem exists_modulatedDecay_cyclicDifferenceProduct_representativeMap
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G)
    (hs : ∀ g ∈ gs, ∃ (S : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
      (D : BruhatSchwartz G →L[ℂ] BruhatSchwartz G),
        (∀ f, bruhatSchwartzDifference g (D f) =
          f - modulatedDecay_zeroInclusion m I h0 (S f)) ∧
        ∀ w f, CyclicNormOneIsotypic m w f.val →
          CyclicNormOneIsotypic m w (S f).val ∧ CyclicNormOneIsotypic m w (D f).val) :
    ∃ R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I,
      (∀ f, f - modulatedDecay_zeroInclusion m I h0 (R f) ∈ (bruhatSchwartzDifferenceProduct gs).range) ∧
      ∀ w f, CyclicNormOneIsotypic m w f.val → CyclicNormOneIsotypic m w (R f).val := by
  let J := modulatedDecay_zeroInclusion m I h0
  letI : IsTopologicalAddGroup (ModulatedExponentialInductive m I) :=
    (PolynormableSpace.withSeminorms ℂ _).topologicalAddGroup
  induction gs with
  | nil =>
    refine ⟨0, fun f ↦ ⟨f - J 0, rfl⟩, fun w f _ a x ↦ ?_⟩
    exact (mul_zero (w a : ℂ)).symm
  | cons g gs ih =>
    obtain ⟨S, D, hSD, hSDiso⟩ := hs g List.mem_cons_self
    obtain ⟨R, hR, hRiso⟩ := ih (fun a ha ↦ hs a (List.mem_cons_of_mem _ ha))
    let A := bruhatSchwartzDifference g
    let B := modulatedDecay_cyclicDifference m hm hms g I h0
    have hJ (u : ModulatedExponentialInductive m I) : J (B u) = A (J u) :=
      modulatedDecay_zeroInclusion_cyclicDifferenceProduct m hm hms I h0 [g] u
    refine ⟨S + B.comp (R.comp D), fun f ↦ ?_, fun w f hf a x ↦ ?_⟩
    · obtain ⟨v, hv⟩ := hR (D f)
      refine ⟨v, ?_⟩
      change A (bruhatSchwartzDifferenceProduct gs v) = f - J (S f + B (R (D f)))
      change bruhatSchwartzDifferenceProduct gs v = D f - J (R (D f)) at hv
      rw [hv, map_sub, hSD, map_add, hJ, sub_sub]
    · let u := R (D f)
      have hu := hRiso w (D f) (hSDiso w f hf).2
      have hBu (y : G) : (B u).val y = u.val y - u.val (g * y) :=
        modulatedDecay_cyclicDifference_apply m hm hms g I h0 u y
      have hBiso : CyclicNormOneIsotypic m w (B u).val := by
        intro k y
        rw [hBu, hBu, mul_left_comm g, hu, hu, mul_sub]
      change (S f).val (a.val⁻¹ * x) + (B u).val (a.val⁻¹ * x) =
        (w a : ℂ) * ((S f).val x + (B u).val x)
      exact (congrArg₂ (· + ·) ((hSDiso w f hf).1 a x) (hBiso a x)).trans (mul_add _ _ _).symm

include hm hms in
/-- A continuous representative map makes the canonical comparison a
topological isomorphism. -/
theorem exists_modulatedDecay_cyclicDifferenceProduct_quotientEquiv_of_representativeMap
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd)
    (R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
    (hR : ∀ f, f - modulatedDecay_zeroInclusion m I h0 (R f) ∈ (bruhatSchwartzDifferenceProduct gs).range) :
    let W := (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range
    let V := (bruhatSchwartzDifferenceProduct gs).range
    ∃ C : (ModulatedExponentialInductive m I ⧸ W) ≃L[ℂ] (BruhatSchwartz G ⧸ V),
      ∀ f, C (W.mkQ f) = V.mkQ (modulatedDecay_zeroInclusion m I h0 f) := by
  intro W V
  let J := modulatedDecay_zeroInclusion m I h0
  obtain ⟨C, hC, hCJ⟩ := exists_modulatedDecay_cyclicDifferenceProduct_quotientComparison m hm hms I h0 gs hgs
  let L := W.mkQL.comp R
  have hCL (f : BruhatSchwartz G) : C (L f) = V.mkQ f := by
    change C (W.mkQ (R f)) = V.mkQ f
    exact (hCJ (R f)).trans ((Submodule.Quotient.eq V).2 (by
      simpa only [neg_sub] using V.neg_mem (hR f)))
  have hL : V ≤ L.ker := by
    intro f hf
    apply hC.injective
    change C (L f) = C 0
    rw [map_zero, hCL]
    exact (Submodule.Quotient.mk_eq_zero V).2 hf
  let U := V.liftQL L hL
  have hright : RightInverse U C := by
    intro q
    obtain ⟨f, rfl⟩ := V.mkQ_surjective q
    exact hCL f
  have hleft : LeftInverse U C := fun q ↦ hC.injective (hright (C q))
  exact ⟨⟨LinearEquiv.ofLinear C.toLinearMap U.toLinearMap
    (LinearMap.ext hright) (LinearMap.ext hleft), C.continuous, U.continuous⟩, hCJ⟩

include hm hms in
/-- Representative maps at the two sets of abscissae give the two canonical
topological comparisons of (4.6.3.1). Both send a test to its own quotient class. -/
theorem exists_modulatedDecay_cyclicDifferenceProduct_quotientEquivs_of_representativeMaps
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd)
    (R₀ : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m univ)
    (R : BruhatSchwartz G →L[ℂ] ModulatedExponentialInductive m I)
    (hR₀ : ∀ f, f - modulatedDecay_zeroInclusion m univ (mem_univ 0) (R₀ f) ∈
      (bruhatSchwartzDifferenceProduct gs).range)
    (hR : ∀ f, f - modulatedDecay_zeroInclusion m I h0 (R f) ∈ (bruhatSchwartzDifferenceProduct gs).range) :
    let W₀ := (modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs).range
    let W := (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range
    let V := (bruhatSchwartzDifferenceProduct gs).range
    ∃ (D : (ModulatedExponentialInductive m univ ⧸ W₀) ≃L[ℂ] (ModulatedExponentialInductive m I ⧸ W))
      (C : (ModulatedExponentialInductive m I ⧸ W) ≃L[ℂ] (BruhatSchwartz G ⧸ V)),
      (∀ f, D (W₀.mkQ f) = W.mkQ (modulatedDecay_restrict m (subset_univ I) f)) ∧
      ∀ f, C (W.mkQ f) = V.mkQ (modulatedDecay_zeroInclusion m I h0 f) := by
  intro W₀ W V
  obtain ⟨C₀, hC₀⟩ := exists_modulatedDecay_cyclicDifferenceProduct_quotientEquiv_of_representativeMap
    m hm hms univ (mem_univ 0) gs hgs R₀ hR₀
  obtain ⟨C, hC⟩ := exists_modulatedDecay_cyclicDifferenceProduct_quotientEquiv_of_representativeMap
    m hm hms I h0 gs hgs R hR
  refine ⟨C₀.trans C.symm, C, ?_, hC⟩
  intro f
  apply C.injective
  change C (C.symm (C₀ (W₀.mkQ f))) = C (W.mkQ (modulatedDecay_restrict m (subset_univ I) f))
  rw [C.apply_symm_apply]
  have hr : modulatedDecay_zeroInclusion m I h0 (modulatedDecay_restrict m (subset_univ I) f) =
      modulatedDecay_zeroInclusion m univ (mem_univ 0) f :=
    Subtype.ext (modulatedDecay_restrict_apply m (subset_univ I) f)
  exact (hC₀ f).trans ((congrArg V.mkQ hr.symm).trans (hC _).symm)

end

end Masullo
