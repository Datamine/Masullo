import BruhatQuotientStages
import ElementarySchwartzFiberMeasure
import LFOpenMapping

open Filter Function MeasureTheory Set Topology
open scoped ComplexOrder ZeroAtInfty

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (K : Subgroup G) (hK : IsClosed (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]

local instance : MeasurableSpace (G ⧸ K) := borel _
local instance : BorelSpace (G ⧸ K) := ⟨rfl⟩

include hK

set_option maxHeartbeats 1350000 in
/-- On every translated coset of a closed subgroup, a realized elementary
stage is integrable. The coset integral is continuous on the quotient. -/
theorem BruhatSchwartzStage.coset_integrable_continuous
    (p : BruhatSchwartzStage G) (s : p.Space) :
    (∀ x : G, Integrable (fun k : K => p.realize s (x * k.val)) μK) ∧
      Continuous (lcaCosetIntegral K μK (p.realize s)) := by
  let J := p.1.upper.val
  let N := p.1.kernel.comap J.subtype
  let A := p.1.StageQuotient
  letI : IsClosed (N : Set J) := p.1.kernel_closed.preimage continuous_subtype_val
  letI : LocallyCompactSpace J := p.1.upper.property.1.locallyCompactSpace
  letI : MeasurableSpace A := borel _
  letI : BorelSpace A := ⟨rfl⟩
  let π : J →ₜ* A := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  have hN : IsCompact (N : Set J) := by
    apply (J.isClosed_of_isOpen p.1.upper.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage
      (K := (p.1.kernel : Set G))
    rw [← lcaDualAnnihilator_annihilator p.1.kernel p.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ p.1.annihilator_open
  have hp : IsProperMap π := (lcaQuotient_isProper_iff N).mpr hN
  let g (y : A) := s (p.2.equiv y).toAdd
  have hgc : Continuous g := by
    have hc : Continuous (p.realize s) := bruhatSchwartz_continuous (p.inclusion s)
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact (hc.comp continuous_subtype_val).congr
      (fun x => p.1.realizeSchwartz_apply_of_mem p.2 s x)
  obtain ⟨ν, hν, hL, hνeq⟩ :=
    exists_haar_imageFiber_integral K J hK p.1.upper.property.1 π hp μK _ rfl
  letI := hν
  obtain ⟨hi, hc⟩ := elementarySchwartz_fibre_integrable_continuous p.2
    ((K.comap J.subtype).map π.toMonoidHom) hL ν s
  let a := lcaCosetIntegral K μK (p.realize s)
  have hf0 (x : G) (hx : x ∉ J) : p.realize s x = 0 :=
    p.1.realizeSchwartz_apply_of_not_mem p.2 s x hx
  have hfp (x : J) : p.realize s x.val = g (π x) :=
    p.1.realizeSchwartz_apply_of_mem p.2 s x
  have hinner (x : J) := hνeq hgc hf0 hfp x
  let q := QuotientGroup.mk' K
  let J' := J.map q
  let qJ := q.subgroupMap J
  have hqJ (x : J) : a (qJ x).val = ∫ z, g (π x * z.val) ∂ν := by
    change a (QuotientGroup.mk x.val) = _
    exact (lcaCosetIntegral_mk K μK (p.realize s) x.val).trans (hinner x).2
  have hout (x : G) (hx : q x ∉ J') (k : K) : p.realize s (x * k.val) = 0 := by
    apply hf0
    intro hk
    apply hx
    refine ⟨x * k.val, hk, ?_⟩
    have hk1 : q k.val = 1 := (QuotientGroup.eq_one_iff k.val).mpr k.property
    rw [map_mul, hk1, mul_one]
  constructor
  · intro x
    by_cases hx : q x ∈ J'
    · obtain ⟨y, hy, h⟩ := hx
      have hiy :=
        (lcaCosetIntegrable_mk K μK _ y).mpr ((hinner ⟨y, hy⟩).1.mpr (hi (π ⟨y, hy⟩)))
      change QuotientGroup.mk y = QuotientGroup.mk x at h
      rw [h] at hiy
      exact (lcaCosetIntegrable_mk K μK _ x).mp hiy
    · rw [show (fun k : K => p.realize s (x * k.val)) = 0 from funext (hout x hx)]
      exact integrable_zero _ _ _
  · have ho : IsOpen (J' : Set (G ⧸ K)) :=
      QuotientGroup.isOpenMap_coe _ p.1.upper.property.1
    have hclosed := J'.isClosed_of_isOpen ho
    have hz (y : G ⧸ K) (hy : y ∉ J') : a y = 0 := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      refine (lcaCosetIntegral_mk K μK (p.realize s) x).trans ?_
      rw [show (fun k : K => p.realize s (x * k.val)) = 0 from funext (hout x hy)]
      exact integral_zero _ _
    have hqjc : Continuous qJ := (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
    have hqjo : IsOpenMap qJ := by
      intro U hU
      have hO : IsOpen (q '' (Subtype.val '' U)) :=
        QuotientGroup.isOpenMap_coe _ (p.1.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ hU)
      have he : qJ '' U = (Subtype.val : J' → G ⧸ K) ⁻¹' (q '' (Subtype.val '' U)) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩
          exact ⟨x, hx, Subtype.ext hy⟩
      rw [he]
      exact hO.preimage continuous_subtype_val
    have hcont : ContinuousOn a (J' : Set (G ⧸ K)) := by
      rw [continuousOn_iff_continuous_domRestrict]
      apply (hqjo.isQuotientMap hqjc (q.subgroupMap_surjective J)).continuous_iff.mpr
      exact (hc.comp π.continuous).congr fun x => (hqJ x).symm
    have hA := continuous_indicator (s := (J' : Set (G ⧸ K))) (f := a)
      (by rw [frontier, hclosed.closure_eq, ho.interior_eq, sdiff_self]; simp)
      (by rwa [hclosed.closure_eq])
    have hEq : (J' : Set (G ⧸ K)).indicator a = a := by
      funext y
      by_cases hy : y ∈ J'
      · exact indicator_of_mem hy _
      · rw [indicator_of_notMem hy, hz y hy]
    rwa [hEq] at hA

/-- Every Schwartz–Bruhat test is absolutely integrable on each coset of
a closed subgroup, with a continuous quotient function. -/
theorem bruhatSchwartz_coset_integrable_continuous (f : BruhatSchwartz G) :
    (∀ x : G, Integrable (fun k : K => f.val (x * k.val)) μK) ∧
      Continuous (lcaCosetIntegral K μK f.val) := by
  obtain ⟨p, s, hs⟩ := f.property
  rw [← hs]
  exact p.coset_integrable_continuous K hK μK s

/-- Restriction of a Schwartz–Bruhat test to a closed subgroup is integrable
for any Borel presentation of Haar measure on the subgroup. -/
theorem bruhatSchwartz_integrable_closedSubgroup
    [m : MeasurableSpace K] [b : BorelSpace K]
    (τ : Measure K) [τ.IsHaarMeasure] (f : BruhatSchwartz G) :
    Integrable (fun k : K => f.val k.val) τ := by
  have he : m = MeasurableSpace.comap (Subtype.val : K → G) ‹MeasurableSpace G› := by
    rw [b.measurable_eq, BorelSpace.measurable_eq (α := G)]
    exact borel_comap
  cases he
  have h := (bruhatSchwartz_coset_integrable_continuous K hK τ f).1 1
  simpa only [one_mul] using h

local instance : MeasurableSpace (PontryaginDual (G ⧸ K)) := borel _
local instance : BorelSpace (PontryaginDual (G ⧸ K)) := ⟨rfl⟩
local instance : MeasurableSpace (lcaAnnihilator K) := borel _
local instance : BorelSpace (lcaAnnihilator K) := ⟨rfl⟩

set_option maxHeartbeats 1000000 in
/-- D.1.7.1(1). Distributional Poisson summation holds pointwise for
every Schwartz–Bruhat test. The dual measure is the quotient Plancherel
measure transported to the annihilator of the closed subgroup. -/
theorem bruhatSchwartz_poisson_closedSubgroup
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μK.Regular]
    (ν : Measure (G ⧸ K)) (hν : IsWeilQuotientMeasure K μ μK ν)
    (νDual : Measure (PontryaginDual (G ⧸ K))) (hνDual : IsLCAPlancherelMeasure ν νDual)
    (f : BruhatSchwartz G) :
    ∃ e : PontryaginDual (G ⧸ K) ≃ₜ* lcaAnnihilator K,
      let νA := Measure.map e νDual
      νA.IsHaarMeasure ∧ νA.Regular ∧
      (∀ χ x, (e χ).val x = χ (QuotientGroup.mk x)) ∧
      Integrable (fun χ : lcaAnnihilator K => lcaFourier μ f.val χ.val) νA ∧
      ∀ x : G,
        (∫ k : K, f.val (x * k.val) ∂μK) =
          ∫ χ : lcaAnnihilator K, lcaFourier μ f.val χ.val * (χ.val x : ℂ) ∂νA := by
  letI : IsClosed (K : Set G) := hK
  letI : MeasurableSpace (PontryaginDual G) := borel _
  letI : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hf := bruhatSchwartz_integrable μ f
  obtain ⟨e, ha, hr, he, -, hP⟩ := weilQuotient_poisson_annihilator K hK μ μK ν hν νDual hνDual hf
  letI := ha
  obtain ⟨F, hF⟩ := exists_bruhatFourier_continuousLinear μ
  let D := lcaAnnihilator K
  have hD : IsClosed (D : Set (PontryaginDual G)) := by
    let r := PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    change IsClosed (r ⁻¹' {1})
    exact isClosed_singleton.preimage r.continuous
  have hi : Integrable (fun χ : D => lcaFourier μ f.val χ.val) (Measure.map e νDual) :=
    (bruhatSchwartz_integrable_closedSubgroup D hD (Measure.map e νDual) (F f)).congr
      (.of_forall fun χ => hF f χ.val)
  obtain ⟨P, -, hvalue, -, heval⟩ := hP hi
  have hc :=
    (bruhatSchwartz_coset_integrable_continuous K hK μK f).2.comp
      (QuotientGroup.continuous_mk : Continuous (QuotientGroup.mk : G → G ⧸ K))
  have hcont : Continuous (fun x : G => ∫ k : K, f.val (x * k.val) ∂μK) :=
    hc.congr (fun x => lcaCosetIntegral_mk K μK f.val x)
  exact ⟨e, ha, hr, he, hi, fun x => (heval hcont x).trans (hvalue x)⟩

omit hK

set_option maxHeartbeats 1400000 in
/-- A surjective continuous linear map between full Schwartz–Bruhat
spaces of second-countable groups is open. -/
theorem bruhatSchwartz_isOpenMap_of_surjective
    {A B : Type*}
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A]
    [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] [LocallyCompactSpace B]
    [SecondCountableTopology B]
    (T : BruhatSchwartz A →L[ℂ] BruhatSchwartz B) (hT : Surjective T) :
    IsOpenMap T := by
  classical
  obtain ⟨P, hP, hPA⟩ := lcaStructuralPairs_cofinalSequence (G := A)
  obtain ⟨Q, hQ, hQB⟩ := lcaStructuralPairs_cofinalSequence (G := B)
  let a (n : ℕ) : BruhatSchwartzStage A := ⟨P n, Classical.choice (P n).quotient_elementary⟩
  let b (n : ℕ) : BruhatSchwartzStage B := ⟨Q n, Classical.choice (Q n).quotient_elementary⟩
  let X := bruhatSchwartz_countablePresentation a hP hPA
  let Y := bruhatSchwartz_countablePresentation b hQ hQB
  letI : IsTopologicalAddGroup (BruhatSchwartz A) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz A)).topologicalAddGroup
  letI : IsTopologicalAddGroup (BruhatSchwartz B) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz B)).topologicalAddGroup
  letI : T2Space (BruhatSchwartz B) := bruhatSchwartz_t2
  letI (n : ℕ) : ContinuousSMul ℂ (a n).Space := elementarySchwartz_withSeminorms.continuousSMul
  letI (n : ℕ) : ContinuousSMul ℂ (b n).Space := elementarySchwartz_withSeminorms.continuousSMul
  letI (n : ℕ) : FirstCountableTopology (a n).Space :=
    elementarySchwartz_withSeminorms.firstCountableTopology
  letI (n : ℕ) : FirstCountableTopology (b n).Space :=
    elementarySchwartz_withSeminorms.firstCountableTopology
  letI (n : ℕ) : CompleteSpace (a n).Space := completeSpace_elementarySchwartz
  letI (n : ℕ) : CompleteSpace (b n).Space := completeSpace_elementarySchwartz
  letI (n : ℕ) : T2Space (b n).Space := elementarySchwartz_t2
  letI (n : ℕ) : LocallyConvexSpace ℂ (b n).Space := by
    letI : LocallyConvexSpace ℝ (b n).Space :=
      elementarySchwartz_withSeminorms.toLocallyConvexSpace
    exact LocallyConvexSpace.ofBasisZero ℂ (b n).Space id
      (fun s : Set (b n).Space => s ∈ nhds 0 ∧ Convex ℝ s)
      (LocallyConvexSpace.convex_basis_zero ℝ (b n).Space)
      (fun _ h => convex_of_nonneg_surjective_algebraMap ℂ
        (fun _ h => RCLike.nonneg_iff_exists_ofReal.mp h) h.2)
  exact (lf_open_mapping Y.incl X.incl Y.exhaust X.exhaust
    (bruhatSchwartz_seminorm_continuous_of_cofinal b hQB) T hT).1

end
end Masullo
