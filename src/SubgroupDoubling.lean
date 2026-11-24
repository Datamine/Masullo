import TranslateDoubling
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Measure.Haar.Quotient

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H K : Subgroup G}

theorem compactOpen_finiteRelIndex (hH : IsOpen (H : Set G))
    (hK : IsCompact (K : Set G)) : (H.subgroupOf K).FiniteIndex := by
  let J := H.subgroupOf K
  have hJ : IsOpen (J : Set K) := hH.preimage continuous_subtype_val
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact Subgroup.finiteIndex_iff_finite_quotient.mpr (J.quotient_finite_of_isOpen hJ)

theorem compactOpen_relativeIndex_mul_measure [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (hHK : H ≤ K)
    (hH : IsOpen (H : Set G)) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    (H.relIndex K : ℝ≥0∞) * μ (H : Set G) = μ (K : Set G) := by
  let J := H.subgroupOf K
  letI : MeasurableSpace K := Subtype.instMeasurableSpace
  letI : BorelSpace K := inferInstance
  letI : J.FiniteIndex := compactOpen_finiteRelIndex hH hKc
  have he : MeasurableEmbedding K.subtype := hKo.isOpenEmbedding_subtypeVal.measurableEmbedding
  letI := Measure.IsMulLeftInvariant.comap μ (f := K.subtype) he
  have h := J.index_mul_measure (hH.measurableSet.preimage measurable_subtype_coe)
    (μ.comap K.subtype)
  rw [he.comap_apply, he.comap_apply] at h
  have h₁ : K.subtype '' (J : Set K) = (H : Set G) := by
    ext x
    exact ⟨by rintro ⟨⟨_, _⟩, hx, rfl⟩; exact hx, fun hx => ⟨⟨x, hHK hx⟩, hx, rfl⟩⟩
  have h₂ : K.subtype '' (Set.univ : Set K) = (K : Set G) := by
    rw [image_univ]
    exact Subtype.range_coe_subtype
  rw [h₁, h₂] at h
  exact h

/-- A compact open subgroup basis can be a D-sequence only when
the indices of adjacent subgroups have a uniform bound. -/
theorem compactOpen_doubling_relativeIndex_bounded [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : ℕ → Subgroup G)
    (hKc : ∀ k, IsCompact (K k : Set G)) (hKo : ∀ k, IsOpen (K k : Set G))
    (hD : DoublingSequence μ (fun k => (K k : Set G))) :
    ∃ N : ℕ, ∀ k, (K (k + 1)).relIndex (K k) ≤ N := by
  obtain ⟨C, _, hc⟩ := hD.doubling
  obtain ⟨N, hN⟩ := exists_nat_gt C
  refine ⟨N, fun k => ?_⟩
  have hstep : K (k + 1) ≤ K k := hD.decreasing (Nat.le_succ k)
  have hm : (K (k + 1) : Set G) * (K k : Set G) = (K k : Set G) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact (K k).mul_mem (hstep hx) hy
    · exact fun y hy => ⟨1, (K (k + 1)).one_mem, y, hy, one_mul y⟩
  have hb := (hc k).2
  change μ ((K (k + 1) : Set G) * (K k : Set G)) < (C : ℝ≥0∞) * μ (K (k + 1) : Set G) at hb
  rw [hm, ← compactOpen_relativeIndex_mul_measure μ hstep (hKo (k + 1)) (hKo k) (hKc k)] at hb
  by_contra! hx
  have hcN : (C : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hN.le
  have hx' : (N : ℝ≥0∞) ≤ ((K (k + 1)).relIndex (K k) : ℝ≥0∞) := by exact_mod_cast hx.le
  have hm' : (C : ℝ≥0∞) * μ (K (k + 1) : Set G) ≤
      ((K (k + 1)).relIndex (K k) : ℝ≥0∞) * μ (K (k + 1) : Set G) := by
    gcongr
    exact hcN.trans hx'
  exact (not_lt_of_ge hm') hb

theorem compactOpen_subgroup_translateBasis (K : ℕ → Subgroup G)
    (hKc : ∀ k, IsCompact (K k : Set G)) (hKo : ∀ k, IsOpen (K k : Set G))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set G)))
    (hidx : ∃ N : ℕ, ∀ k, (K (k + 1)).relIndex (K k) ≤ N) :
    OpenTranslateBasis (fun k => (K k : Set G)) := by
  apply compactOpen_translateBasis K hKc hKo hdec hcof
  obtain ⟨N, hN⟩ := hidx
  refine ⟨N + 1, fun k => ?_⟩
  let J := (K (k + 1)).subgroupOf (K k)
  letI : J.FiniteIndex := compactOpen_finiteRelIndex (hKo (k + 1)) (hKc k)
  letI := J.fintypeQuotientOfFiniteIndex
  let e := Fintype.equivFin (K k ⧸ J)
  have hcard : Fintype.card (K k ⧸ J) ≤ N := by
    rw [← Nat.card_eq_fintype_card]
    exact hN k
  let t (i : Fin (N + 1)) : G :=
    if h : i.val < Fintype.card (K k ⧸ J) then
      ((QuotientGroup.mk_surjective (e.symm ⟨i.val, h⟩)).choose : K k).val else 1
  refine ⟨t, ?_⟩
  intro x hx
  let y : K k := ⟨x, hx⟩
  let a := e (QuotientGroup.mk y)
  let j : Fin (N + 1) := ⟨a.val, a.isLt.trans (hcard.trans_lt (Nat.lt_succ_self _))⟩
  let z := (QuotientGroup.mk_surjective (e.symm a)).choose
  have ht : t j = z.val := by simp only [t, j, dite_eq_left a.isLt, Fin.eta, z]
  have hz : (QuotientGroup.mk z : K k ⧸ J) = QuotientGroup.mk y := by
    exact ((QuotientGroup.mk_surjective (e.symm a)).choose_spec).trans (e.symm_apply_apply _)
  have hk : z⁻¹ * y ∈ J := QuotientGroup.eq.mp hz
  refine mem_iUnion.mpr ⟨j, (z⁻¹ * y).val, hk, ?_⟩
  change t j * (z.val⁻¹ * x) = x
  rw [ht, mul_inv_cancel_left]

end

end Masullo
