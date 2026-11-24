import WeilQuotientIntegral
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Algebra.OpenSubgroup

open Filter MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Every sequence of compact sets lies in an open sigma-compact subgroup. -/
theorem exists_open_sigmaCompact_subgroup_of_compact_sequence
    (K : ℕ → Set G) (hK : ∀ n, IsCompact (K n)) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsSigmaCompact (H : Set G) ∧
      ∀ n, K n ⊆ H := by
  obtain ⟨V, hV, hVn⟩ := exists_compact_mem_nhds (1 : G)
  let L (n : ℕ) : Set G := {1} ∪ V ∪ V⁻¹ ∪
      ⋃ i ∈ Finset.range (n + 1), K i ∪ (K i)⁻¹
  have hL (n : ℕ) : IsCompact (L n) :=
    ((isCompact_singleton.union hV).union hV.inv).union
      ((Finset.range (n + 1)).isCompact_biUnion fun i _ => (hK i).union (hK i).inv)
  have hLmono : Monotone L := by
    intro m n h x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hc, hi⟩ := Set.mem_iUnion.mp hi
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨Finset.range_mono (Nat.succ_le_succ h) hc, hi⟩⟩)
  have hLinv (n : ℕ) {x : G} (hx : x ∈ L n) : x⁻¹ ∈ L n := by
    rcases hx with ((hx | hx) | hx) | hx
    · have he : x = 1 := Set.mem_singleton_iff.mp hx
      subst x
      exact Or.inl (Or.inl (Or.inl (by simp)))
    · exact Or.inl (Or.inr (Set.inv_mem_inv.mpr hx))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_inv.mp hx)))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hc, hi | hi⟩ := Set.mem_iUnion.mp hi
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
          ⟨hc, Or.inr (Set.inv_mem_inv.mpr hi)⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
          ⟨hc, Or.inl (Set.mem_inv.mp hi)⟩⟩)
  let H : Subgroup G :=
    { carrier := ⋃ p : ℕ × ℕ, L p.1 ^ p.2
      one_mem' := Set.mem_iUnion.mpr ⟨(0, 0), by simp⟩
      mul_mem' := by
        intro x y hx hy
        obtain ⟨⟨i, n⟩, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨⟨j, m⟩, hy⟩ := Set.mem_iUnion.mp hy
        refine Set.mem_iUnion.mpr ⟨(max i j, n + m), ?_⟩
        change x * y ∈ L (max i j) ^ (n + m)
        rw [pow_add]
        exact Set.mul_mem_mul
          (Set.pow_subset_pow_left (hLmono (le_max_left i j)) hx)
          (Set.pow_subset_pow_left (hLmono (le_max_right i j)) hy)
      inv_mem' := by
        intro x hx
        obtain ⟨⟨i, n⟩, hx⟩ := Set.mem_iUnion.mp hx
        refine Set.mem_iUnion.mpr ⟨(i, n), ?_⟩
        change x⁻¹ ∈ L i ^ n
        have hi : (L i)⁻¹ ⊆ L i := fun a ha => by
          simpa using hLinv i (Set.mem_inv.mp ha)
        have he : x⁻¹ ∈ (L i ^ n)⁻¹ := Set.inv_mem_inv.mpr hx
        rw [← inv_pow] at he
        exact Set.pow_subset_pow_left hi he }
  have hVsub : V ⊆ H := fun x hx => Set.mem_iUnion.mpr ⟨(0, 1), by
    change x ∈ L 0 ^ 1
    rw [pow_one]
    exact Or.inl (Or.inl (Or.inr hx))⟩
  refine ⟨H, H.isOpen_of_mem_nhds (Filter.mem_of_superset hVn hVsub), ?_, ?_⟩
  · apply isSigmaCompact_iUnion_of_isCompact
    intro p
    induction p.2 with
    | zero => rw [pow_zero]; exact isCompact_singleton (x := (1 : G))
    | succ n ih => rw [pow_succ]; exact ih.mul (hL p.1)
  · intro n x hx
    refine Set.mem_iUnion.mpr ⟨(n, 1), ?_⟩
    change x ∈ L n ^ 1
    rw [pow_one]
    exact Or.inr (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), Or.inl hx⟩⟩)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Restricting a measure finite on compact sets to a sigma-compact set gives
a sigma-finite measure, even when the ambient group is much larger. -/
theorem sigmaFinite_restrict_of_isSigmaCompact [IsFiniteMeasureOnCompacts μ]
    {S : Set G} (hS : IsSigmaCompact S) : SigmaFinite (μ.restrict S) := by
  obtain ⟨K, hK, hcover⟩ := hS
  have hm : MeasurableSet S := hcover ▸ MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet
  refine ⟨⟨⟨fun n => K n ∪ Sᶜ, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hm.compl),
      union_inter_distrib_right, compl_inter_self, union_empty]
    exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
  · rw [← iUnion_union, hcover, union_compl_self]

variable [μ.IsHaarMeasure] [μ.Regular]

/-- A countable family of finite-outer-measure sets lies pointwise in an open
sigma-compact subgroup. Outer regularity covers even nonmeasurable subsets. -/
theorem exists_open_sigmaCompact_subgroup_of_lt_top
    (A : ℕ → Set G) (hA : ∀ n, μ (A n) < ∞) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsSigmaCompact (H : Set G) ∧
      ∀ n, A n ⊆ H := by
  choose U hAU hUo hUfinite using fun n => (A n).exists_isOpen_lt_of_lt ∞ (hA n)
  let ε (n : ℕ) : ℝ≥0∞ := (↑(n + 1) : ℝ≥0∞)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hex (m n : ℕ) : ∃ K, K ⊆ U m ∧ IsCompact K ∧ μ (U m \ K) < ε n :=
    (hUo m).measurableSet.exists_isCompact_sdiff_lt (hUfinite m).ne (by simp [ε])
  choose K _ hK hrem using hex
  let e := Nat.pairEquiv
  obtain ⟨H, hHo, hHσ, hHK⟩ :=
    exists_open_sigmaCompact_subgroup_of_compact_sequence
      (fun n => K (e.symm n).1 (e.symm n).2) (fun n => hK _ _)
  refine ⟨H, hHo, hHσ, fun m => (hAU m).trans ?_⟩
  have hKsub (n : ℕ) : K m n ⊆ H := by simpa using hHK (e (m, n))
  have h0 : μ (U m \ (H : Set G)) = 0 := by
    refine le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hε fun n => ?_) bot_le
    exact (measure_mono (sdiff_subset_sdiff_right (hKsub n))).trans (hrem m n).le
  have he : U m \ (H : Set G) = ∅ := by
    by_contra hn
    exact ((hUo m).sdiff (H.isClosed_of_isOpen hHo)).measure_pos μ
      (Set.nonempty_iff_ne_empty.mpr hn) |>.ne' h0
  intro x hx
  by_contra hn
  have hmem : x ∈ U m \ (H : Set G) := ⟨hx, hn⟩
  simpa [he] using hmem

/-- An integrable function on a group with regular Haar measure vanishes
pointwise outside some open sigma-compact subgroup. -/
theorem exists_open_sigmaCompact_subgroup_of_integrable
    {E : Type*} [NormedAddCommGroup E] {f : G → E} (hf : Integrable f μ) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsSigmaCompact (H : Set G) ∧
      Function.support f ⊆ H := by
  let d (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  let A (n : ℕ) : Set G := {x | d n ≤ ‖f x‖}
  have hA (n : ℕ) : μ (A n) < ∞ := hf.measure_norm_ge_lt_top (by dsimp [d]; positivity)
  obtain ⟨H, hHo, hHσ, hHA⟩ := exists_open_sigmaCompact_subgroup_of_lt_top μ A hA
  refine ⟨H, hHo, hHσ, fun x hx => ?_⟩
  have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr hx
  obtain ⟨n, hn⟩ := exists_nat_gt (‖f x‖⁻¹)
  have hd : d n ≤ ‖f x‖ := by
    dsimp [d]
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    have h := (inv_lt_iff_one_lt_mul₀ hpos).mp hn
    nlinarith
  exact hHA n hd

end
end Masullo
