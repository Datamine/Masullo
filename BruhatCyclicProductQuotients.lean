import BruhatCyclicProductRepresentatives
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

open Function Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)

/-- In the cancellation step of Corollary 4.6.3.1, cancelling the first
difference leaves the product over the tail of the list. -/
theorem bruhatSchwartzDifferenceProduct_cancel_first (γ : G)
    (hγ : 0 < (m γ).toAdd) (gs : List G) (f : BruhatSchwartz G) :
    bruhatSchwartzDifference γ f ∈ (bruhatSchwartzDifferenceProduct (γ :: gs)).range ↔
      f ∈ (bruhatSchwartzDifferenceProduct gs).range := by
  have hinj : Injective (bruhatSchwartzDifference γ) :=
    bruhatSchwartzDifferenceProduct_injective m [γ] (by simpa using hγ)
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hinj hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, congrArg (bruhatSchwartzDifference γ) hv⟩

include hm hms in
/-- The canonical comparison from any decay space containing zero weight
is a continuous linear bijection onto the ordinary product quotient. -/
theorem exists_modulatedDecay_cyclicDifferenceProduct_quotientComparison
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd) :
    let W := (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range
    let V := (bruhatSchwartzDifferenceProduct gs).range
    ∃ C : (ModulatedExponentialInductive m I ⧸ W) →L[ℂ] (BruhatSchwartz G ⧸ V),
      Bijective C ∧ ∀ f, C (W.mkQ f) = V.mkQ (modulatedDecay_zeroInclusion m I h0 f) := by
  intro W V
  let J := modulatedDecay_zeroInclusion m I h0
  have hr (f : ModulatedExponentialInductive m I) : J f ∈ V ↔ f ∈ W :=
    modulatedDecay_cyclicDifferenceProduct_range_preimage m hm hms I h0 gs hgs f
  let L := V.mkQL.comp J
  have hL : W ≤ L.ker := fun f hf ↦ (Submodule.Quotient.mk_eq_zero V).2 ((hr f).2 hf)
  let C := W.liftQL L hL
  refine ⟨C, ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · intro a b hab
    obtain ⟨f, rfl⟩ := W.mkQ_surjective a
    obtain ⟨g, rfl⟩ := W.mkQ_surjective b
    apply (Submodule.Quotient.eq W).2
    apply (hr (f - g)).1
    rw [map_sub]
    exact (Submodule.Quotient.eq V).1 hab
  · intro a
    obtain ⟨f, rfl⟩ := V.mkQ_surjective a
    obtain ⟨u, v, hu, hf⟩ := exists_bruhatCyclicProduct_compact_representative m hm hms gs hgs f
    have huI : u.val ∈ modulatedExponentialDecaySubmodule m I :=
      modulatedExponentialDecay_mem_of_smooth_compactSupport m I
        (bruhatSchwartz_le_smooth u.property) hu
    let uI : ModulatedExponentialInductive m I :=
      ModulatedExponentialInductive.algebraicEquiv.symm ⟨u.val, huI⟩
    refine ⟨W.mkQ uI, (Submodule.Quotient.eq V).2 ?_⟩
    have hJu : J uI = u := Subtype.ext rfl
    change J uI - f ∈ V
    rw [hJu]
    have hv : f - u = bruhatSchwartzDifferenceProduct gs v := by
      rw [hf]
      abel
    have hmem : f - u ∈ V := ⟨v, hv.symm⟩
    simpa only [neg_sub] using V.neg_mem hmem

include hm hms in
/-- Restricting the abscissae induces the first continuous linear bijection
in (4.6.3.1), from the entire-decay to the interval-decay quotient. -/
theorem exists_modulatedDecay_cyclicDifferenceProduct_quotientRestriction
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd) :
    let W₀ := (modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs).range
    let W := (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range
    ∃ D : (ModulatedExponentialInductive m univ ⧸ W₀) →L[ℂ] (ModulatedExponentialInductive m I ⧸ W),
      Bijective D ∧ ∀ f, D (W₀.mkQ f) = W.mkQ (modulatedDecay_restrict m (subset_univ I) f) := by
  intro W₀ W
  let V := (bruhatSchwartzDifferenceProduct gs).range
  let j₀ := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let j := modulatedDecay_zeroInclusion m I h0
  let r := modulatedDecay_restrict m (subset_univ I)
  have hr (f : ModulatedExponentialInductive m univ) : j (r f) = j₀ f :=
    Subtype.ext (modulatedDecay_restrict_apply m (subset_univ I) f)
  let L := W.mkQL.comp r
  have hL : W₀ ≤ L.ker := by
    intro f hf
    apply (Submodule.Quotient.mk_eq_zero W).2
    apply (modulatedDecay_cyclicDifferenceProduct_range_preimage m hm hms I h0 gs hgs (r f)).1
    change j (r f) ∈ V
    rw [hr]
    exact (modulatedDecay_cyclicDifferenceProduct_range_preimage m hm hms univ (mem_univ 0) gs hgs f).2 hf
  let D := W₀.liftQL L hL
  obtain ⟨C₀, hC₀, h₀⟩ := exists_modulatedDecay_cyclicDifferenceProduct_quotientComparison
    m hm hms univ (mem_univ 0) gs hgs
  obtain ⟨C, hC, h⟩ := exists_modulatedDecay_cyclicDifferenceProduct_quotientComparison
    m hm hms I h0 gs hgs
  have hD (a : ModulatedExponentialInductive m univ ⧸ W₀) : C (D a) = C₀ a := by
    obtain ⟨f, rfl⟩ := W₀.mkQ_surjective a
    change C (W.mkQ (r f)) = C₀ (W₀.mkQ f)
    exact (h (r f)).trans ((congrArg V.mkQ (hr f)).trans (h₀ f).symm)
  refine ⟨D, ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · intro a b hab
    exact hC₀.1 ((hD a).symm.trans ((congrArg C hab).trans (hD b)))
  · intro b
    obtain ⟨a, ha⟩ := hC₀.2 (C b)
    exact ⟨a, hC.1 ((hD a).trans ha)⟩

end

end Masullo
