import DiscreteQuotient
import DoublingSequences

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

local notation "q" => (QuotientGroup.mk' H)

/-- Representatives in the specified transversal of a quotient subset. -/
def transversalSlice (E : Set G) (A : Set (G ⧸ H)) : Set G := q ⁻¹' A ∩ E

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
private theorem image_slice {E : Set G} (hE : BijOn q E univ) (A : Set (G ⧸ H)) :
    q '' transversalSlice H E A = A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro hy
    obtain ⟨x, hx, he⟩ := hE.surjOn (mem_univ y)
    exact ⟨x, ⟨show q x ∈ A by rw [he]; exact hy, hx⟩, he⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
private theorem image_slice_mul {E : Set G} (hE : BijOn q E univ) (A B : Set (G ⧸ H)) :
    q '' (transversalSlice H E A * transversalSlice H E B) = A * B := by
  rw [image_mul, image_slice H hE, image_slice H hE]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
private theorem subset_finite_translate_union {C D : Set G}
    (S T : Set G) (hS : S ⊆ C) (hT : T ⊆ D) (himage : q '' S ⊆ q '' T)
    {I : Finset G} (hI : (H : Set G) ∩ (C * D⁻¹) ⊆ (I : Set G)) :
    S ⊆ ⋃ g ∈ I, g • T := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := himage ⟨s, hs, rfl⟩
  let a := s * t⁻¹
  have ha : a ∈ H := by
    apply (QuotientGroup.eq_one_iff a).mp
    change q a = 1
    dsimp only [a]
    rw [map_mul, map_inv, hst, mul_inv_cancel]
  have ha' : a ∈ C * D⁻¹ := mul_mem_mul (hS hs) (mem_inv.mpr (by simpa using hT ht))
  have haI : a ∈ I := hI ⟨ha, ha'⟩
  apply mem_iUnion.mpr
  refine ⟨a, mem_iUnion.mpr ⟨haI, ?_⟩⟩
  exact ⟨t, ht, by simp [a]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [BorelSpace G] [SecondCountableTopology G] in
private theorem measure_finite_translate_union (μ : Measure G) [μ.IsMulLeftInvariant]
    (T : Set G) (I : Finset G) :
    μ (⋃ g ∈ I, g • T) ≤ (I.card : ℝ≥0∞) * μ T := by
  calc
    _ ≤ ∑ g ∈ I, μ (g • T) := measure_biUnion_finset_le _ _
    _ = _ := by simp [measure_smul, nsmul_eq_mul]

omit [T2Space G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
/-- Products of transversal slices are comparable in outer measure to
the slice of the quotient product. Finitely many kernel translates suffice,
uniformly over all subsets of the quotient. -/
theorem quotient_slice_mul_comparable (μ : Measure G) [μ.IsMulLeftInvariant]
    (hH : IsClosed (H : Set G)) (hd : IsDiscrete (H : Set G))
    {E : Set G} (hE : BijOn q E univ) (hc : IsCompact (closure E)) :
    ∃ N : ℕ, 0 < N ∧ ∀ A B : Set (G ⧸ H),
      μ (transversalSlice H E A * transversalSlice H E B) ≤ (N : ℝ≥0∞) * μ (transversalSlice H E (A * B)) ∧
      μ (transversalSlice H E (A * B)) ≤ (N : ℝ≥0∞) * μ (transversalSlice H E A * transversalSlice H E B) := by
  classical
  let C := closure E
  let L := (H : Set G) ∩ ((C * C * C⁻¹) ∪ (C * (C * C)⁻¹))
  have hC := ((hc.mul hc).mul hc.inv).union (hc.mul (hc.mul hc).inv)
  have hL : IsCompact L := hC.inter_left hH
  have hLd : IsDiscrete L := hd.mono inter_subset_left
  let I := (hL.finite hLd).toFinset
  refine ⟨I.card + 1, Nat.succ_pos _, fun A B => ?_⟩
  let S := transversalSlice H E A * transversalSlice H E B
  let T := transversalSlice H E (A * B)
  have hS : S ⊆ C * C := mul_subset_mul (inter_subset_right.trans subset_closure)
    (inter_subset_right.trans subset_closure)
  have hT : T ⊆ C := inter_subset_right.trans subset_closure
  have he : q '' S = q '' T := (image_slice_mul H hE A B).trans (image_slice H hE (A * B)).symm
  have hI₁ : (H : Set G) ∩ ((C * C) * C⁻¹) ⊆ (I : Set G) := by
    intro x hx
    have h : x ∈ L := ⟨hx.1, Or.inl hx.2⟩
    simpa [I] using h
  have hI₂ : (H : Set G) ∩ (C * (C * C)⁻¹) ⊆ (I : Set G) := by
    intro x hx
    have h : x ∈ L := ⟨hx.1, Or.inr hx.2⟩
    simpa [I] using h
  have h₁ := subset_finite_translate_union H S T hS hT he.le hI₁
  have h₂ := subset_finite_translate_union H T S hT hS he.symm.le hI₂
  have hcast : (I.card : ℝ≥0∞) ≤ (↑(I.card + 1) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ _
  exact ⟨(measure_mono h₁).trans ((measure_finite_translate_union μ T I).trans
      (by gcongr)),
    (measure_mono h₂).trans ((measure_finite_translate_union μ S I).trans
      (by gcongr))⟩

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
private theorem cofinal_slice_iff {E : Set G} (hE : BijOn q E univ) (he : E ∈ 𝓝 (1 : G))
    (U : ℕ → Set (G ⧸ H)) :
    CofinalAtOne U ↔ CofinalAtOne (fun k => transversalSlice H E (U k)) := by
  constructor
  · intro hu V hV
    obtain ⟨W, hWE, hWo, hW⟩ := mem_nhds_iff.mp (inter_mem hV he)
    have hIm : q '' W ∈ 𝓝 (1 : G ⧸ H) :=
      (QuotientGroup.isOpenMap_coe W hWo).mem_nhds ⟨1, hW, QuotientGroup.mk_one H⟩
    obtain ⟨k, hk⟩ := hu _ hIm
    refine ⟨k, fun g hg => ?_⟩
    obtain ⟨w, hw, heq⟩ := hk hg.1
    have h := hE.injOn (hWE hw).2 hg.2 heq
    exact h ▸ (hWE hw).1
  · intro hu V hV
    have hp : q ⁻¹' V ∈ 𝓝 (1 : G) := by
      exact QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds (by simpa using hV)
    obtain ⟨k, hk⟩ := hu _ hp
    refine ⟨k, ?_⟩
    rw [← image_slice H hE (U k)]
    exact image_subset_iff.mpr hk

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] in
private theorem symmetric_slice_iff {E : Set G} (hE : BijOn q E univ) (hs : E⁻¹ = E)
    (A : Set (G ⧸ H)) :
    A⁻¹ = A ↔ (transversalSlice H E A)⁻¹ = transversalSlice H E A := by
  have he : (transversalSlice H E A)⁻¹ = transversalSlice H E A⁻¹ := by
    ext g
    change q g⁻¹ ∈ A ∧ g⁻¹ ∈ E ↔ (q g)⁻¹ ∈ A ∧ g ∈ E
    have hh : g⁻¹ ∈ E ↔ g ∈ E := by rw [← Set.mem_inv, hs]
    rw [map_inv, hh]
  constructor
  · intro h
    rw [he, h]
  · intro h
    have hh : transversalSlice H E A⁻¹ = transversalSlice H E A := he.symm.trans h
    calc
      A⁻¹ = q '' transversalSlice H E A⁻¹ := (image_slice H hE A⁻¹).symm
      _ = q '' transversalSlice H E A := congrArg (fun S => q '' S) hh
      _ = A := image_slice H hE A

omit [T2Space G] in
/-- Proposition A.5.2.6. The D and D′ conditions descend and lift across
the Borel transversal. The doubling constant may change by a finite
factor depending on the relatively compact transversal. -/
theorem quotient_transversal_doubling_iff (μ : Measure G) [μ.IsMulLeftInvariant]
    (hH : IsClosed (H : Set G)) (hd : IsDiscrete (H : Set G))
    {E : Set G} (hE : BijOn q E univ) (hc : IsCompact (closure E)) (hm : MeasurableSet E)
    (he : E ∈ 𝓝 (1 : G)) (ν : Measure (G ⧸ H))
    (hν : ν = (μ.restrict E).map q)
    {U : ℕ → Set (G ⧸ H)} (hU : ∀ k, MeasurableSet (U k)) :
    (DoublingSequence ν U ↔ DoublingSequence μ (fun k => transversalSlice H E (U k))) ∧
    (CofinalAtOne U ↔ CofinalAtOne (fun k => transversalSlice H E (U k))) ∧
    (E⁻¹ = E → ∀ k, (U k)⁻¹ = U k ↔ (transversalSlice H E (U k))⁻¹ = transversalSlice H E (U k)) := by
  obtain ⟨N, hN, hcomp⟩ := quotient_slice_mul_comparable H μ hH hd hE hc
  have hmeasure (A : Set (G ⧸ H)) : ν A = μ (transversalSlice H E A) := by
    rw [hν]
    exact transversal_pushforward_apply H hd μ hm hE.injOn A
  have hpos : (0 : ℝ≥0) < N := by exact_mod_cast hN
  have h1 : (1 : G) ∈ E := mem_of_mem_nhds he
  have hM (k : ℕ) : MeasurableSet (transversalSlice H E (U k)) :=
    ((hU k).preimage QuotientGroup.continuous_mk.measurable).inter hm
  have hl (k : ℕ) : 1 ∈ U k ↔ 1 ∈ transversalSlice H E (U k) := by
    simp [transversalSlice, h1]
  have hdoub (A B : Set (G ⧸ H)) :
      μ (transversalSlice H E A * transversalSlice H E B) ≤ (N : ℝ≥0∞) * ν (A * B) ∧
      ν (A * B) ≤ (N : ℝ≥0∞) * μ (transversalSlice H E A * transversalSlice H E B) := by
    rw [hmeasure]
    exact hcomp A B
  refine ⟨⟨?_, ?_⟩, cofinal_slice_iff H hE he U, fun hs k => symmetric_slice_iff H hE hs (U k)⟩
  · intro h
    refine ⟨fun k => (hl k).mp (h.one_mem k), hM, fun k => hmeasure (U k) ▸ h.positive k,
      fun k => hmeasure (U k) ▸ h.finite k, fun i j hij _ hg => ⟨h.decreasing hij hg.1, hg.2⟩, ?_⟩
    obtain ⟨C, hC, hCd⟩ := h.doubling
    refine ⟨(N : ℝ≥0) * C, mul_pos hpos hC, fun k => ⟨?_, ?_⟩⟩
    · have hs : transversalSlice H E (U (k + 1)) ⊆ transversalSlice H E (U (k + 1)) * transversalSlice H E (U k) :=
        fun x hx => ⟨x, hx, 1, (hl k).mp (h.one_mem k), mul_one _⟩
      exact (hmeasure (U (k + 1)) ▸ h.positive (k + 1)).trans_le (measure_mono hs)
    · have hh := (hdoub (U (k + 1)) (U k)).1
      refine hh.trans_lt ?_
      rw [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc, ← hmeasure]
      exact ENNReal.mul_lt_mul_right (show (N : ℝ≥0∞) ≠ 0 by exact_mod_cast hN.ne')
        (ENNReal.natCast_ne_top N) (hCd k).2
  · intro h
    refine ⟨fun k => (hl k).mpr (h.one_mem k), hU, fun k => by rw [hmeasure]; exact h.positive k,
      fun k => by rw [hmeasure]; exact h.finite k, ?_, ?_⟩
    · intro i j hij
      rw [← image_slice H hE (U i), ← image_slice H hE (U j)]
      exact image_mono (h.decreasing hij)
    · obtain ⟨C, hC, hCd⟩ := h.doubling
      refine ⟨(N : ℝ≥0) * C, mul_pos hpos hC, fun k => ⟨?_, ?_⟩⟩
      · have hs : U (k + 1) ⊆ U (k + 1) * U k :=
          fun x hx => ⟨x, hx, 1, (hl k).mpr (h.one_mem k), mul_one _⟩
        exact ((hmeasure (U (k + 1))).symm ▸ h.positive (k + 1)).trans_le (measure_mono hs)
      · have hh := (hdoub (U (k + 1)) (U k)).2
        refine hh.trans_lt ?_
        rw [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc, hmeasure (U (k + 1))]
        exact ENNReal.mul_lt_mul_right (show (N : ℝ≥0∞) ≠ 0 by exact_mod_cast hN.ne')
          (ENNReal.natCast_ne_top N) (hCd k).2

omit [T2Space G] in
/-- The same comparison with the quotient measure normalized by the scalar
Weil formula with counting measure on the discrete subgroup. -/
theorem quotient_transversal_doubling_iff_of_Weil (μ : Measure G) [μ.IsMulLeftInvariant] [SigmaFinite μ]
    (hH : IsClosed (H : Set G)) (hd : IsDiscrete (H : Set G))
    {E : Set G} (hE : BijOn q E univ) (hc : IsCompact (closure E)) (hm : MeasurableSet E)
    (he : E ∈ 𝓝 (1 : G)) (ν : Measure (G ⧸ H))
    (hWeil : ∀ f : G → ℂ, Measurable f → Integrable f μ → ∀ F : G ⧸ H → ℂ,
      (∀ g : G, F (q g) = ∑' h : H, f (g * h)) →
      Integrable F ν ∧ ∫ g, f g ∂μ = ∫ y, F y ∂ν)
    {U : ℕ → Set (G ⧸ H)} (hU : ∀ k, MeasurableSet (U k)) :
    (DoublingSequence ν U ↔ DoublingSequence μ (fun k => transversalSlice H E (U k))) ∧
    (CofinalAtOne U ↔ CofinalAtOne (fun k => transversalSlice H E (U k))) ∧
    (E⁻¹ = E → ∀ k, (U k)⁻¹ = U k ↔
      (transversalSlice H E (U k))⁻¹ = transversalSlice H E (U k)) :=
  quotient_transversal_doubling_iff H μ hH hd hE hc hm he ν
    (quotient_measure_eq_transversal_pushforward H hd μ ν hm hE hWeil) hU

end Masullo
