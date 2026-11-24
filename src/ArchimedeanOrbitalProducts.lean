import ArchimedeanFundamentalDomain
import Mathlib.Topology.Algebra.IsOpenUnits

open Function NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The total logarithmic modulus on the infinite ideles. -/
def infiniteIdeleLogNorm : InfiniteIdeles F →* Multiplicative ℝ :=
  (archTotalLogHom F).comp (infiniteAdeleUnitsMixed F).toMonoidHom

theorem infiniteIdeleLogNorm_continuous : Continuous (infiniteIdeleLogNorm F) :=
  (archTotalLogHom_continuous F).comp (infiniteAdeleUnitsMixed F).continuous

theorem infiniteIdeleLogNorm_eq (a : InfiniteIdeles F) :
    infiniteIdeleLogNorm F a = Multiplicative.ofAdd (Real.log ‖a.val‖) := by
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (archTotalLogHom F (infiniteAdeleUnitsMixed F a)) = _
  rw [archTotalLogHom_apply]
  exact congrArg Real.log (archModulus_of_infiniteAdele F a.val)

def infiniteIdeleSplit (s : Multiplicative ℝ →* InfiniteIdeles F)
    (hs : ∀ t, infiniteIdeleLogNorm F (s t) = t) (hc : Continuous s) :
    Multiplicative ℝ × archNormOne F ≃ₜ InfiniteIdeles F where
  toEquiv := (splitNormMulEquiv (infiniteIdeleLogNorm F) s hs).toEquiv
  continuous_toFun := (hc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (infiniteIdeleLogNorm_continuous F).prodMk
    ((continuous_id.div' (hc.comp (infiniteIdeleLogNorm_continuous F))).subtype_mk _)

theorem infiniteIdeleSection_embedding (s : Multiplicative ℝ →* InfiniteIdeles F)
    (hs : ∀ t, infiniteIdeleLogNorm F (s t) = t) (hc : Continuous s) :
    IsEmbedding s :=
  (show LeftInverse (infiniteIdeleLogNorm F) s from hs).isEmbedding
    (infiniteIdeleLogNorm_continuous F) hc

theorem infiniteIdele_value_openEmbedding :
    IsOpenEmbedding (Units.val : InfiniteIdeles F → InfiniteAdeleRing F) := by
  let p : InfiniteIdeles F ≃ₜ ((v : InfinitePlace F) → (v.Completion)ˣ) :=
    ContinuousMulEquiv.piUnits.toHomeomorph
  have h : IsOpenEmbedding (fun a : (v : InfinitePlace F) → (v.Completion)ˣ =>
        fun v => (a v).val) :=
    IsOpenEmbedding.piMap fun _ => IsOpenUnits.isOpenEmbedding_unitsVal
  exact h.comp p.isOpenEmbedding

/-- The product with the closed fundamental domain, expressed in the
section's logarithmic parameter. -/
def archSectionDomainProduct (v : InfinitePlace F)
    (s : Multiplicative ℝ →* InfiniteIdeles F) (K : Set (Multiplicative ℝ)) :
    Set (InfiniteIdeles F) :=
  (fun p : Multiplicative ℝ × archNormOne F => s p.1 * p.2.val) ''
    (K ×ˢ closure (archFundamentalDomain F v))

/-- Lemma A.2.3.13. The product is compact and avoids all coordinate
hyperplanes. Nonempty parameter interior gives both interior conclusions. -/
theorem archSectionDomainProduct_properties (v : InfinitePlace F)
    (s : Multiplicative ℝ →* InfiniteIdeles F)
    (hs : ∀ t, infiniteIdeleLogNorm F (s t) = t) (hc : Continuous s)
    {K : Set (Multiplicative ℝ)} (hK : IsCompact K) :
    IsCompact (archSectionDomainProduct F v s K) ∧
    ((interior K).Nonempty → (interior (archSectionDomainProduct F v s K)).Nonempty) ∧
    (∀ a ∈ Units.val '' archSectionDomainProduct F v s K, ∀ w : InfinitePlace F, a w ≠ 0) ∧
    ((interior K).Nonempty →
      (interior (Units.val '' archSectionDomainProduct F v s K)).Nonempty) := by
  let e := infiniteIdeleSplit F s hs hc
  let B := K ×ˢ closure (archFundamentalDomain F v)
  have hB : archSectionDomainProduct F v s K = e '' B := rfl
  have hi : (interior K).Nonempty → (interior (archSectionDomainProduct F v s K)).Nonempty := by
    rintro ⟨t, ht⟩
    obtain ⟨a, ha⟩ := archFundamentalDomain_interior F v
    let O := interior K ×ˢ interior (archFundamentalDomain F v)
    have ho : IsOpen (e '' O) := e.isOpenMap _ (isOpen_interior.prod isOpen_interior)
    have hOB : e '' O ⊆ archSectionDomainProduct F v s K := by
      rw [hB]
      exact image_mono (prod_mono interior_subset (interior_subset.trans subset_closure))
    exact ⟨e (t, a), interior_maximal hOB ho ⟨(t, a), ⟨ht, ha⟩, rfl⟩⟩
  refine ⟨hB ▸ (hK.prod (archFundamentalDomain_compact_closure F v)).image e.continuous, hi, ?_, ?_⟩
  · rintro a ⟨u, _, rfl⟩ w
    exact infiniteCoord_nonzero F u w
  · intro h
    obtain ⟨a, ha⟩ := hi h
    have ho := (infiniteIdele_value_openEmbedding F).isOpenMap _ (isOpen_interior (s :=
      archSectionDomainProduct F v s K))
    exact ⟨a.val, interior_maximal (image_mono interior_subset) ho ⟨a, ha, rfl⟩⟩

end

end Masullo
