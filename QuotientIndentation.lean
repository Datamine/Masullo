import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Compactness.LocallyFinite

open Filter Function MeasureTheory Set Topology TopologicalSpace

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

private abbrev quotientMap (H : Subgroup G) := (QuotientGroup.mk : G → G ⧸ H)

include hH in
/-- An open set that meets every coset supports a nonnegative continuous
indentation whose integral is one on each coset. -/
theorem exists_quotientIndentation_supported {B : Set G} (hB : IsOpen B)
    (hcoverB : ∀ z : G ⧸ H, ∃ x ∈ B, quotientMap H x = z) :
    ∃ u₀ : C(G, ℝ), (∀ x, 0 ≤ u₀ x) ∧ tsupport u₀ ⊆ B ∧
      (∀ K : Set (G ⧸ H), IsCompact K →
        IsCompact (tsupport u₀ ∩ quotientMap H ⁻¹' K)) ∧
      ∀ x : G, Integrable (fun h : H => u₀ ((h : G)⁻¹ * x)) μ ∧
        (∫ h : H, u₀ ((h : G)⁻¹ * x) ∂μ) = 1 := by
  classical
  let Q := G ⧸ H
  let q : G → Q := quotientMap H
  have hq : Continuous q := QuotientGroup.continuous_mk
  letI : T1Space Q := QuotientGroup.t1Space_iff.mpr hH
  letI : LocallyCompactSpace H := hH.locallyCompactSpace
  letI : SecondCountableTopology H := Subtype.secondCountableTopology (H : Set G)
  letI : TopologicalSpace.PseudoMetrizableSpace H :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology H
  letI : Measure.Regular μ := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hbump (x : B) : ∃ b : CompactlySupportedContinuousMap G ℝ,
      (∀ y, 0 ≤ b y) ∧ tsupport b ⊆ B ∧ 0 < ses.pushforward μ b (q x) := by
    obtain ⟨b, hbx, hbK, hbB, hbn⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      (K := {(x : G)}) (V := B) isCompact_singleton hB
      (singleton_subset_iff.mpr x.property)
    let b₀ : CompactlySupportedContinuousMap G ℝ := ⟨b, hbK⟩
    refine ⟨b₀, fun y => (hbn y).1, hbB, ?_⟩
    change 0 < ses.pushforward μ b₀ (QuotientGroup.mk' H x)
    rw [ses.pushforward_apply_apply]
    let f := ses.pullback b₀ x
    apply (integral_pos_iff_support_of_nonneg (f := f) (fun y => (hbn _).1) f.integrable).mpr
    have hone : f 1 = 1 := by
      change b (x * (↑(1 : H) : G)) = 1
      simpa using hbx (mem_singleton (x : G))
    have ho : IsOpen (support f) := isClosed_eq f.continuous continuous_const |>.isOpen_compl
    exact ho.measure_pos μ ⟨1, by simp [mem_support, hone]⟩
  choose b hbn hbB hbx using hbump
  let a (i : B) : CompactlySupportedContinuousMap Q ℝ := ses.pushforward μ (b i)
  have ha_nonneg (i : B) (z : Q) : 0 ≤ a i z := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    change 0 ≤ ses.pushforward μ (b i) (QuotientGroup.mk' H x)
    rw [ses.pushforward_apply_apply]
    exact integral_nonneg fun h => hbn i _
  let U (i : B) := {z : Q | 0 < a i z}
  have hUo (i : B) : IsOpen (U i) := isOpen_lt continuous_const (a i).continuous
  have hcover : (univ : Set Q) ⊆ ⋃ i, U i := by
    intro z _
    obtain ⟨x, hxB, rfl⟩ := hcoverB z
    exact mem_iUnion.mpr ⟨⟨x, hxB⟩, hbx ⟨x, hxB⟩⟩
  obtain ⟨P, hP⟩ := PartitionOfUnity.exists_isSubordinate (s := (univ : Set Q))
    isClosed_univ U hUo hcover
  let f (i : B) (y : G) := P i (q y) * b i y / a i (q y)
  have hfn (i : B) (y : G) : 0 ≤ f i y :=
    div_nonneg (mul_nonneg (P.nonneg i _) (hbn i y)) (ha_nonneg i _)
  have hfc (i : B) : Continuous (f i) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : q x ∈ tsupport (P i)
    · exact (((P i).continuous.comp hq).mul (b i).continuous).continuousAt.div
        ((a i).continuous.comp hq).continuousAt (show 0 < a i (q x) from hP i hx).ne'
    · have hn : ∀ᶠ y in 𝓝 x, q y ∉ tsupport (P i) :=
        hq.continuousAt ((isClosed_tsupport _).isOpen_compl.mem_nhds hx)
      have hz {y : G} (hy : q y ∉ tsupport (P i)) : f i y = 0 := by
        simp [f, image_eq_zero_of_notMem_tsupport hy]
      rw [ContinuousAt, hz hx]
      exact tendsto_const_nhds.congr' (hn.mono fun y hy => (hz hy).symm)
  let V (i : B) := tsupport (b i) ∩ q ⁻¹' tsupport (P i)
  have hVc (i : B) : IsCompact (V i) :=
    (b i).hasCompactSupport.inter_right ((isClosed_tsupport _).preimage hq)
  have hfV (i : B) : tsupport (f i) ⊆ V i := by
    apply closure_minimal _ (hVc i).isClosed
    intro x hx
    constructor
    · by_contra h
      exact hx (by simp [f, image_eq_zero_of_notMem_tsupport h])
    · by_contra h
      exact hx (by simp [f, image_eq_zero_of_notMem_tsupport h])
  have hloc : LocallyFinite V := by
    refine (P.locallyFinite_tsupport.preimage_continuous hq).subset ?_
    exact fun i => inter_subset_right
  let u : C(G, ℝ) :=
    ⟨fun x => ∑ᶠ i, f i x, continuous_finsum hfc
      (hloc.subset fun i => (subset_tsupport _).trans (hfV i))⟩
  have huV : tsupport u ⊆ ⋃ i, V i := by
    apply closure_minimal _ (hloc.isClosed_iUnion fun i => (hVc i).isClosed)
    intro x hx
    by_contra hn
    have hz (i : B) : f i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hfV i hi⟩))
    exact hx (show (∑ᶠ i, f i x) = 0 from by simp [hz])
  have huB : tsupport u ⊆ B :=
    huV.trans (iUnion_subset fun i => inter_subset_left.trans (hbB i))
  refine ⟨u, fun x => finsum_nonneg fun i => hfn i x, huB, ?_, ?_⟩
  · intro K hK
    let s := (P.locallyFinite_tsupport.finite_nonempty_inter_compact hK).toFinset
    apply (s.isCompact_biUnion fun i _ => hVc i).of_isClosed_subset
      ((isClosed_tsupport _).inter (hK.isClosed.preimage hq))
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (huV hx.1)
    exact mem_iUnion₂.mpr ⟨i, by simpa [s] using (show
      (tsupport (P i) ∩ K).Nonempty from ⟨q x, hi.2, hx.2⟩), hi⟩
  · intro x
    let s := (P.locallyFinite_tsupport.point_finite (q x)).toFinset
    have hqmul (h : H) : q (x * (h : G)) = q x := by
      change QuotientGroup.mk (x * (h : G)) = QuotientGroup.mk x
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr h.property, mul_one]
    have hterm (i : B) (h : H) :
        f i (x * (h : G)) = (P i (q x) / a i (q x)) * b i (x * (h : G)) := by
      simp only [f, hqmul]
      ring
    have heq (h : H) : u (x * (h : G)) = ∑ i ∈ s, f i (x * (h : G)) := by
      change (∑ᶠ i, f i (x * (h : G))) = _
      apply finsum_eq_sum_of_support_subset
      intro i hi
      have hp : q x ∈ tsupport (P i) := by
        by_contra hn
        apply hi
        change f i (x * (h : G)) = 0
        rw [hterm, image_eq_zero_of_notMem_tsupport hn, zero_div, zero_mul]
      simpa [s] using hp
    have hfi (i : B) : Integrable (fun h : H => f i (x * (h : G))) μ := by
      simp_rw [hterm]
      exact (ses.pullback (b i) x).integrable.const_mul _
    have hi (i : B) : (∫ h : H, f i (x * (h : G)) ∂μ) = P i (q x) := by
      simp_rw [hterm]
      rw [integral_const_mul]
      have hbint : (∫ h : H, b i (x * (h : G)) ∂μ) = a i (q x) :=
        (ses.pushforward_apply_apply μ (b i) x).symm
      rw [hbint]
      by_cases hn : q x ∈ tsupport (P i)
      · exact div_mul_cancel₀ _ (show 0 < a i (q x) from hP i hn).ne'
      · rw [image_eq_zero_of_notMem_tsupport hn, zero_div, zero_mul]
    have hI : Integrable (fun h : H => u (x * (h : G))) μ := by
      simp_rw [heq]
      exact integrable_finsetSum _ fun i _ => hfi i
    have hone : (∫ h : H, u (x * (h : G)) ∂μ) = 1 := by
      simp_rw [heq]
      rw [integral_finsetSum _ (fun i _ => hfi i)]
      simp_rw [hi]
      rw [← finsum_eq_sum_of_support_subset (fun i => P i (q x)) (fun i hi => by
        have hmem : q x ∈ tsupport (P i) := subset_tsupport _ hi
        simpa [s] using hmem)]
      exact P.sum_eq_one (mem_univ _)
    have he (h : H) : u ((h : G)⁻¹ * x) = (fun k : H => u (x * (k : G))) h⁻¹ := by
      rw [mul_comm]
      rfl
    simp_rw [he]
    refine ⟨(Measure.measurePreserving_inv μ).integrable_comp_of_integrable hI, ?_⟩
    exact (integral_inv_eq_self (fun h : H => u (x * (h : G))) μ).trans hone


include hH in
/-- Lemma 12.2.1.1. There is a nonnegative continuous function with proper
support over the quotient, whose integral on every coset is one. -/
theorem exists_quotientIndentation :
    ∃ u₀ : C(G, ℝ), (∀ x, 0 ≤ u₀ x) ∧
      (∀ K : Set (G ⧸ H), IsCompact K →
        IsCompact (tsupport u₀ ∩ quotientMap H ⁻¹' K)) ∧
      ∀ x : G, Integrable (fun h : H => u₀ ((h : G)⁻¹ * x)) μ ∧
        (∫ h : H, u₀ ((h : G)⁻¹ * x) ∂μ) = 1 := by
  obtain ⟨u, hu₀, _, hp, hf⟩ := exists_quotientIndentation_supported H hH μ (B := univ)
    isOpen_univ (fun q => ⟨q.out, mem_univ _, Quotient.out_eq' q⟩)
  exact ⟨u, hu₀, hp, hf⟩


omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace H] [μ.IsHaarMeasure] in
/-- The indentation is an exact right inverse to coset integration on
continuous functions pulled back from the quotient, including unbounded ones. -/
theorem quotientIndentation_reproduces (u : G → ℝ)
    (hu : ∀ x : G, Integrable (fun h : H => u ((h : G)⁻¹ * x)) μ ∧
        (∫ h : H, u ((h : G)⁻¹ * x) ∂μ) = 1)
    (w : C(G ⧸ H, ℂ)) (x : G) :
    Integrable (fun h : H => (u ((h : G)⁻¹ * x) : ℂ) * w (quotientMap H ((h : G)⁻¹ * x))) μ ∧
    (∫ h : H, (u ((h : G)⁻¹ * x) : ℂ) * w (quotientMap H ((h : G)⁻¹ * x)) ∂μ) =
      w (quotientMap H x) := by
  have hq (h : H) : quotientMap H ((h : G)⁻¹ * x) = quotientMap H x := by
    unfold quotientMap
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff _).mpr h.property, inv_one, one_mul]
  simp_rw [hq]
  refine ⟨(hu x).1.ofReal.mul_const _, ?_⟩
  rw [integral_mul_const, integral_complex_ofReal, (hu x).2, Complex.ofReal_one, one_mul]

end
end Masullo
