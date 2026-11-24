import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.ZMod.Basic

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

/-- A D-sequence in the sense of Definition A.5.2.1. The adjacent-stage
condition is indexed by `k + 1, k` so it starts with the first pair. -/
structure DoublingSequence {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G) (U : ℕ → Set G) : Prop where
  one_mem : ∀ k, 1 ∈ U k
  measurable : ∀ k, MeasurableSet (U k)
  positive : ∀ k, 0 < μ (U k)
  finite : ∀ k, μ (U k) < ⊤
  decreasing : Antitone U
  doubling : ∃ C : ℝ≥0, 0 < C ∧ ∀ k, 0 < μ (U (k + 1) * U k) ∧
    μ (U (k + 1) * U k) < C * μ (U (k + 1))

/-- The additional cofinality condition for a D′-sequence. -/
def CofinalAtOne {G : Type*} [One G] [TopologicalSpace G] (U : ℕ → Set G) : Prop :=
  ∀ V ∈ 𝓝 (1 : G), ∃ k, U k ⊆ V

/-- A tail of a D′-sequence in a locally compact Hausdorff group has compact closure
at its first stage. -/
theorem exists_compact_doublingTail {G : Type*} [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] {μ : Measure G}
    {U : ℕ → Set G} (hU : DoublingSequence μ U) (hcof : CofinalAtOne U) :
    ∃ m : ℕ, DoublingSequence μ (fun n => U (n + m)) ∧
      CofinalAtOne (fun n => U (n + m)) ∧ IsCompact (closure (U m)) := by
  obtain ⟨K, hK, hKm⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨m, hm⟩ := hcof K hKm
  refine ⟨m, ?_, ?_, hK.of_isClosed_subset isClosed_closure (closure_minimal hm hK.isClosed)⟩
  · refine ⟨fun n => hU.one_mem (n + m), fun n => hU.measurable (n + m),
      fun n => hU.positive (n + m), fun n => hU.finite (n + m),
      fun _ _ h => hU.decreasing (Nat.add_le_add_right h m), ?_⟩
    obtain ⟨C, hC, hbound⟩ := hU.doubling
    exact ⟨C, hC, fun n => by simpa only [Nat.add_right_comm] using hbound (n + m)⟩
  · intro V hV
    obtain ⟨n, hn⟩ := hcof V hV
    exact ⟨n, (hU.decreasing (Nat.le_add_right n m)).trans hn⟩

section Product

variable {G H : Type*} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
  {μ : Measure G} {ν : Measure H} {τ : Measure (G × H)} {U : ℕ → Set G} {V : ℕ → Set H}

omit [MeasurableSpace G] [MeasurableSpace H] in
private theorem rectangle_mul (A B : Set G) (C D : Set H) :
    (A ×ˢ C) * (B ×ˢ D) = (A * B) ×ˢ (C * D) := by
  ext p
  constructor
  · rintro ⟨⟨a, c⟩, ⟨ha, hc⟩, ⟨b, d⟩, ⟨hb, hd⟩, rfl⟩
    exact ⟨mul_mem_mul ha hb, mul_mem_mul hc hd⟩
  · rintro ⟨⟨a, ha, b, hb, hab⟩, ⟨c, hc, d, hd, hcd⟩⟩
    exact ⟨(a, c), ⟨ha, hc⟩, (b, d), ⟨hb, hd⟩, Prod.ext hab hcd⟩

/-- The D-sequence statement of Lemma A.5.2.5. The rectangle identity
expresses the normalization of the product Haar measure. -/
theorem doublingSequence_prod (hτ : ∀ A B, τ (A ×ˢ B) = μ A * ν B)
    (hU : DoublingSequence μ U) (hV : DoublingSequence ν V) :
    DoublingSequence τ (fun k => U k ×ˢ V k) := by
  refine ⟨fun k => ⟨hU.one_mem k, hV.one_mem k⟩, fun k => (hU.measurable k).prod (hV.measurable k),
    fun k => ?_, fun k => ?_, fun _ _ h => Set.prod_mono (hU.decreasing h) (hV.decreasing h), ?_⟩
  · rw [hτ]
    exact ENNReal.mul_pos (hU.positive k).ne' (hV.positive k).ne'
  · rw [hτ]
    exact ENNReal.mul_lt_top (hU.finite k) (hV.finite k)
  · obtain ⟨C, hC, hCk⟩ := hU.doubling
    obtain ⟨D, hD, hDk⟩ := hV.doubling
    refine ⟨C * D, mul_pos hC hD, fun k => ?_⟩
    rw [rectangle_mul, hτ, hτ]
    refine ⟨ENNReal.mul_pos (hCk k).1.ne' (hDk k).1.ne', ?_⟩
    simpa only [ENNReal.coe_mul, mul_mul_mul_comm] using ENNReal.mul_lt_mul (hCk k).2 (hDk k).2

omit [MeasurableSpace G] [MeasurableSpace H] in
/-- The D′-sequence, openness and symmetry assertions of Lemma A.5.2.5. -/
theorem doublingSequence_prod_properties [TopologicalSpace G] [TopologicalSpace H] :
    (Antitone U → Antitone V → CofinalAtOne U → CofinalAtOne V →
      CofinalAtOne (fun k => U k ×ˢ V k)) ∧
      ((∀ k, IsOpen (U k)) → (∀ k, IsOpen (V k)) → ∀ k, IsOpen (U k ×ˢ V k)) ∧
      ((∀ k, (U k)⁻¹ = U k) → (∀ k, (V k)⁻¹ = V k) → ∀ k, (U k ×ˢ V k)⁻¹ = U k ×ˢ V k) := by
  refine ⟨?_, fun hU hV k => (hU k).prod (hV k), ?_⟩
  · intro hUd hVd hU hV W hW
    change W ∈ 𝓝 ((1 : G), (1 : H)) at hW
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hW
    obtain ⟨P, hP, Q, hQ, hW⟩ := hW
    obtain ⟨i, hi⟩ := hU P hP
    obtain ⟨j, hj⟩ := hV Q hQ
    exact ⟨max i j, (Set.prod_mono ((hUd (le_max_left i j)).trans hi)
      ((hVd (le_max_right i j)).trans hj)).trans hW⟩
  · intro hU hV k
    ext x
    change (x.1 ∈ (U k)⁻¹ ∧ x.2 ∈ (V k)⁻¹) ↔ (x.1 ∈ U k ∧ x.2 ∈ V k)
    rw [hU k, hV k]

theorem doublingSequence_measure_prod [SFinite ν]
    (hU : DoublingSequence μ U) (hV : DoublingSequence ν V) :
    DoublingSequence (μ.prod ν) (fun k => U k ×ˢ V k) :=
  doublingSequence_prod (fun A B => Measure.prod_prod A B) hU hV

end Product

section CompactOpenBasis

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

/-- D′′ data from a decreasing compact open subgroup basis with a
uniform bound on adjacent Haar measure ratios. -/
theorem compactOpenBasis_doublingSequence (μ : Measure G) [μ.IsHaarMeasure]
    (K : ℕ → Subgroup G) (hKc : ∀ k, IsCompact (K k : Set G))
    (hKo : ∀ k, IsOpen (K k : Set G)) (hdec : Antitone K)
    (hcof : CofinalAtOne (fun k => (K k : Set G)))
    (C : ℝ≥0) (hC : ∀ k, μ (K k : Set G) ≤ C * μ (K (k + 1) : Set G)) :
    let U (k : ℕ) := (K k : Set G)
    let V (k : ℕ) := U (k + 1)
    DoublingSequence μ U ∧ CofinalAtOne U ∧ (∀ k, IsOpen (U k)) ∧ (∀ k, (U k)⁻¹ = U k) ∧
      (∀ k, MeasurableSet (V k)) ∧
      (∀ k, V (k + 1) * V k ⊆ U (k + 1) ∧ μ (U k) ≤ C * μ (V k)) := by
  let U (k : ℕ) := (K k : Set G)
  have hpos (k : ℕ) : 0 < μ (U k) := (hKo k).measure_pos μ ⟨1, (K k).one_mem⟩
  have hfin (k : ℕ) : μ (U k) < ⊤ := (hKc k).measure_lt_top
  have hmul (k : ℕ) : U (k + 1) * U k = U k := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact (K k).mul_mem (hdec (Nat.le_succ k) hx) hy
    · exact fun x hx => ⟨1, (K (k + 1)).one_mem, x, hx, one_mul x⟩
  refine ⟨⟨fun k => (K k).one_mem, fun k => (hKo k).measurableSet, hpos, hfin,
    fun _ _ h => hdec h, ?_⟩, hcof, hKo, ?_, fun k => (hKo (k + 1)).measurableSet, ?_⟩
  · refine ⟨C + 1, by positivity, fun k => ?_⟩
    change 0 < μ (U (k + 1) * U k) ∧ μ (U (k + 1) * U k) < ↑(C + 1) * μ (U (k + 1))
    rw [hmul]
    refine ⟨hpos k, (hC k).trans_lt ?_⟩
    exact ENNReal.mul_lt_mul_left (hpos (k + 1)).ne' (hfin (k + 1)).ne
      (by exact_mod_cast (lt_add_one C))
  · intro k
    ext x
    exact ⟨fun h => by simpa using (K k).inv_mem h, (K k).inv_mem⟩
  · exact fun k => ⟨(hmul (k + 1)).le, hC k⟩

end CompactOpenBasis

section OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The open-subgroup comparison in Proposition A.5.2.3(2). Haar
measure on the subgroup is normalized by restriction. -/
theorem openSubgroup_doublingSequence_iff (μ : Measure G) (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (U : ℕ → Set H) :
    let V (k : ℕ) := H.subtype '' U k
    (DoublingSequence (μ.comap H.subtype) U ↔ DoublingSequence μ V) ∧
    (CofinalAtOne U ↔ CofinalAtOne V) ∧
    ((∀ k, IsOpen (U k)) ↔ ∀ k, IsOpen (V k)) ∧
    ((∀ k, (U k)⁻¹ = U k) ↔ ∀ k, (V k)⁻¹ = V k) := by
  let V (k : ℕ) := H.subtype '' U k
  have he : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  have hm : MeasurableEmbedding H.subtype := he.measurableEmbedding
  have hmeasure (S : Set H) : μ.comap H.subtype S = μ (H.subtype '' S) := hm.comap_apply μ S
  have hOne (k : ℕ) : (1 : G) ∈ V k ↔ (1 : H) ∈ U k := by
    refine ⟨?_, fun h => ⟨1, h, H.subtype.map_one⟩⟩
    rintro ⟨x, hx, heq⟩
    exact he.injective (heq.trans H.subtype.map_one.symm) ▸ hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    exact ⟨fun k => (hOne k).mpr (h.one_mem k), fun k => hm.measurableSet_image.mpr (h.measurable k),
      fun k => hmeasure _ ▸ h.positive k, fun k => hmeasure _ ▸ h.finite k,
      fun _ _ hk => image_mono (h.decreasing hk), by simpa only [hmeasure, Set.image_mul] using h.doubling⟩
  · intro h
    exact ⟨fun k => (hOne k).mp (h.one_mem k), fun k => hm.measurableSet_image.mp (h.measurable k),
      fun k => (hmeasure _).symm ▸ h.positive k, fun k => (hmeasure _).symm ▸ h.finite k,
      fun _ _ hk => (Set.image_subset_image_iff he.injective).mp (h.decreasing hk),
      by simpa only [hmeasure, Set.image_mul] using h.doubling⟩
  · intro h W hW
    have hpre : H.subtype ⁻¹' W ∈ 𝓝 (1 : H) := he.continuous.continuousAt.preimage_mem_nhds hW
    obtain ⟨k, hk⟩ := h _ hpre
    exact ⟨k, image_subset_iff.mpr hk⟩
  · intro h W hW
    have himage : H.subtype '' W ∈ 𝓝 (1 : G) := he.image_mem_nhds.mpr hW
    obtain ⟨k, hk⟩ := h _ himage
    exact ⟨k, (Set.image_subset_image_iff he.injective).mp hk⟩
  · exact forall_congr' fun _ => he.isOpen_iff_image_isOpen
  · refine forall_congr' fun k => ?_
    change (U k)⁻¹ = U k ↔ (H.subtype '' U k)⁻¹ = H.subtype '' U k
    rw [← Set.image_inv H.subtype]
    exact he.injective.image_injective.eq_iff.symm

omit [MeasurableSpace G] [BorelSpace G] in
/-- The literal equality of successive open sets in Proposition A.5.2.3(1)
would force the neutral element to be open. -/
theorem constant_cofinal_open_basis_isOpen_singleton [T1Space G]
    (U : ℕ → Set G) (hu : ∀ k, 1 ∈ U k) (ho : IsOpen (U 0))
    (hconst : ∀ k, U (k + 1) = U k) (hcof : CofinalAtOne U) : IsOpen ({1} : Set G) := by
  have he (k : ℕ) : U k = U 0 := by
    induction k with
    | zero => rfl
    | succ k ih => exact (hconst k).trans ih
  have hs : U 0 = ({1} : Set G) := by
    ext x
    refine ⟨fun hx => mem_singleton_iff.mpr ?_, fun hx => (mem_singleton_iff.mp hx).symm ▸ hu 0⟩
    by_contra hneq
    have hne : (1 : G) ≠ x := fun heq => hneq heq.symm
    obtain ⟨k, hk⟩ := hcof {x}ᶜ (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hne))
    exact (hk (he k ▸ hx)) (mem_singleton x)
  exact hs ▸ ho

end OpenSubgroup

section FiniteCover

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  (μ : Measure G) [μ.IsMulLeftInvariant]

private theorem halfPow_level_le (i j : ℕ) (h : (1 / 2 : ℝ) ^ i ≤ (3 / 2) * (1 / 2) ^ j) :
    j ≤ i := by
  by_contra hij
  have hpow := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num) (Nat.succ_le_iff.mpr (lt_of_not_ge hij))
  rw [pow_succ] at hpow
  have hpos : 0 < (1 / 2 : ℝ) ^ i := by positivity
  linarith

omit [MeasurableSpace G] [MeasurableMul G] in
private theorem center_mem_enlargement {U : ℕ → Set G} (hU : Antitone U) {i j : ℕ} (hij : j ≤ i)
    {x y : G} (h : (x • U i ∩ y • U j).Nonempty) : x ∈ y • (U j * (U j)⁻¹) := by
  rcases h with ⟨z, ⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
  change x * a = z at haz
  change y * b = z at hbz
  have hmem : a⁻¹ ∈ (U j)⁻¹ := inv_mem_inv.mpr (hU hij ha)
  refine ⟨b * a⁻¹, mul_mem_mul hb hmem, ?_⟩
  change y * (b * a⁻¹) = x
  rw [← mul_assoc, hbz, ← haz, mul_inv_cancel_right]

/-- A finite covering lemma repairing Theorem A.5.3.1. The proof uses
control of the same-stage difference sets, including at stage zero.
A nonempty set of centers is required for the strict estimate. -/
theorem doublingSequence_finite_cover {U : ℕ → Set G} (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {B : Set G} (hB : B.Nonempty) (hfin : μ (B * U 0) < ⊤) (F : Set (Set G))
    (hF : ∀ x ∈ B, ∃ k, x • U k ∈ F) :
    ∃ s : Finset (G × ℕ), (∀ p ∈ s, p.1 ∈ B ∧ p.1 • U p.2 ∈ F) ∧
      (s : Set (G × ℕ)).PairwiseDisjoint (fun p => p.1 • U p.2) ∧
      μ B / (C : ℝ≥0∞) < ∑ p ∈ s, μ (U p.2) := by
  classical
  let I : Set (G × ℕ) := {p | p.1 ∈ B ∧ p.1 • U p.2 ∈ F}
  let cover (p : G × ℕ) : Set G := p.1 • U p.2
  let δ (p : G × ℕ) : ℝ := (1 / 2) ^ p.2
  have hne (p : G × ℕ) : (cover p).Nonempty :=
    ⟨p.1, ⟨1, hU.one_mem p.2, mul_one p.1⟩⟩
  obtain ⟨J, hJI, hdis, hlarge⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    cover I δ (3 / 2) (by norm_num) (fun p _ => by dsimp [δ]; positivity) 1
    (fun p _ => pow_le_one₀ (by norm_num) (by norm_num)) (fun p _ => hne p)
  let expanded (p : J) : Set G := p.val.1 • (U p.val.2 * (U p.val.2)⁻¹)
  have hcover (x : G) (hx : x ∈ B) : ∃ p : J, x ∈ expanded p := by
    obtain ⟨k, hk⟩ := hF x hx
    obtain ⟨p, hp, hpinter, hpδ⟩ := hlarge (x, k) ⟨hx, hk⟩
    exact ⟨⟨p, hp⟩, center_mem_enlargement hU.decreasing (halfPow_level_le k p.2 hpδ) hpinter⟩
  obtain ⟨x, hx⟩ := hB
  obtain ⟨p₀, _⟩ := hcover x hx
  have hm (p : J) : MeasurableSet (cover p.val) := (hU.measurable p.val.2).const_smul p.val.1
  have hdis' : Pairwise (fun p q : J => Disjoint (cover p.val) (cover q.val)) :=
    fun _ _ hab => hdis (Subtype.property _) (Subtype.property _) (fun h => hab (Subtype.ext h))
  have hμsmall : μ (⋃ p : J, cover p.val) < ⊤ := by
    refine (measure_mono (iUnion_subset fun p => ?_)).trans_lt hfin
    rintro y ⟨a, ha, rfl⟩
    exact mul_mem_mul ((hJI p.property).1) (hU.decreasing (Nat.zero_le p.val.2) ha)
  have hJ := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ hm hdis' hμsmall.ne
  have hpos (p : J) : 0 < μ (cover p.val) := by
    rw [show cover p.val = p.val.1 • U p.val.2 from rfl, measure_smul]
    exact hU.positive _
  haveI : Countable J := countable_univ_iff.mp (Set.Countable.mono (fun p _ => hpos p) hJ)
  have hsum : (∑' p : J, μ (U p.val.2)) < ⊤ := by
    calc
      _ = ∑' p : J, μ (cover p.val) := by simp [cover, measure_smul]
      _ = μ (⋃ p : J, cover p.val) := (measure_iUnion hdis' hm).symm
      _ < ⊤ := hμsmall
  have hsumC : (∑' p : J, (C : ℝ≥0∞) * μ (U p.val.2)) < ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hsum
  have hterm (p : J) : μ (expanded p) < (C : ℝ≥0∞) * μ (U p.val.2) := by
    simpa [expanded, measure_smul] using hDiff p.val.2
  have hsle : (∑' p : J, μ (expanded p)) ≤ ∑' p : J, (C : ℝ≥0∞) * μ (U p.val.2) :=
    ENNReal.tsum_le_tsum (fun p => (hterm p).le)
  have hslt := ENNReal.tsum_lt_tsum (hsle.trans_lt hsumC).ne (fun p => (hterm p).le) (hterm p₀)
  rw [ENNReal.tsum_mul_left] at hslt
  have hBlt : μ B < (C : ℝ≥0∞) * ∑' p : J, μ (U p.val.2) := by
    have hsub : B ⊆ ⋃ p : J, expanded p := by
      intro y hy
      obtain ⟨p, hp⟩ := hcover y hy
      exact mem_iUnion.mpr ⟨p, hp⟩
    exact (measure_mono hsub).trans_lt ((measure_iUnion_le expanded).trans_lt hslt)
  have hcne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hratio : μ B / (C : ℝ≥0∞) < ∑' p : J, μ (U p.val.2) :=
    (ENNReal.div_lt_iff (.inl hcne) (.inl ENNReal.coe_ne_top)).mpr (by simpa only [mul_comm] using hBlt)
  rw [ENNReal.tsum_eq_iSup_sum] at hratio
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hratio
  let incl : J ↪ G × ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨s.map incl, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
    exact hJI q.property
  · intro p hp q hq hneq
    obtain ⟨p', _, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q', _, rfl⟩ := Finset.mem_map.mp hq
    exact hdis p'.property q'.property hneq
  · simpa [incl, Finset.sum_map] using hs

end FiniteCover

section MaximalFunction

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- The upper limit of the translated local averages in (A.5.3.2). -/
noncomputable def doublingMaximal (μ ν : Measure G) (U : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  limsup (fun k => ν (x • U k) / μ (U k)) atTop

omit [MeasurableMul G] in
theorem measurable_translated_measure_div [MeasurableInv G] [MeasurableMul₂ G]
    (μ ν : Measure G) [SFinite ν] {V : Set G} (hV : MeasurableSet V) :
    Measurable fun x : G => ν (x • V) / μ V := by
  apply Measurable.div_const
  let T : Set (G × G) := (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' V
  have hT : MeasurableSet T := hV.preimage ((measurable_fst.inv).mul measurable_snd)
  have hm : Measurable fun x => ν (Prod.mk x ⁻¹' T) := measurable_measure_prodMk_left hT
  have he (x : G) : x • V = Prod.mk x ⁻¹' T := by
    ext y
    change y ∈ x • V ↔ x⁻¹ * y ∈ V
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · exact fun hy => ⟨x⁻¹ * y, hy, mul_inv_cancel_left x y⟩
  simpa only [he] using hm

omit [MeasurableMul G] in
theorem measurable_doublingMaximal [MeasurableInv G] [MeasurableMul₂ G] (μ ν : Measure G) [SFinite ν]
    {U : ℕ → Set G} (hU : ∀ k, MeasurableSet (U k)) : Measurable (doublingMaximal μ ν U) :=
  Measurable.limsup fun k => measurable_translated_measure_div μ ν (hU k)

omit [MeasurableMul G] in
private theorem exists_above_threshold_of_doublingMaximal {μ ν : Measure G}
    {U : ℕ → Set G} {x : G} {a : ℝ≥0∞} (h : a < doublingMaximal μ ν U x) :
    ∃ k, a < ν (x • U k) / μ (U k) := by
  by_contra hnot
  push Not at hnot
  exact (not_lt_of_ge (limsup_le_of_le (h := Filter.Eventually.of_forall hnot))) h

/-- A covering bound when each center has at least one window above the threshold. -/
theorem doublingSequence_measure_bound_of_exists (μ ν : Measure G) [μ.IsMulLeftInvariant]
    {U : ℕ → Set G} (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {E : Set G} (hfin : μ (E * U 0) < ⊤) {α : ℝ≥0∞} (hα : 0 < α) (hαfin : α ≠ ⊤)
    (hEavg : ∀ x ∈ E, ∃ k, α < ν (x • U k) / μ (U k)) :
    μ E ≤ (C : ℝ≥0∞) / α * ν (E * U 0) ∧
      (μ E = (C : ℝ≥0∞) / α * ν (E * U 0) ↔ E = ∅) := by
  classical
  by_cases hE : E = ∅
  · simp [hE]
  let F : Set (Set G) := {S | ∃ p : G × ℕ, p.1 ∈ E ∧ S = p.1 • U p.2 ∧
    α * μ S < ν S}
  have hF (x : G) (hx : x ∈ E) : ∃ k, x • U k ∈ F := by
    obtain ⟨k, hk⟩ := hEavg x hx
    have hlt := (ENNReal.lt_div_iff_mul_lt (.inl (hU.positive k).ne') (.inl (hU.finite k).ne)).mp hk
    exact ⟨k, ⟨(x, k), hx, rfl, by simpa [measure_smul, mul_comm] using hlt⟩⟩
  obtain ⟨S, hmem, hd, hstrict⟩ :=
    doublingSequence_finite_cover μ hU hC hDiff (nonempty_iff_ne_empty.mpr hE) hfin F hF
  have hterm (p : G × ℕ) (hp : p ∈ S) : α * μ (U p.2) ≤ ν (p.1 • U p.2) := by
    obtain ⟨_, _, _, hlt⟩ := (hmem p hp).2
    simpa [measure_smul] using hlt.le
  have hin : (⋃ p ∈ S, p.1 • U p.2) ⊆ E * U 0 := by
    apply iUnion₂_subset
    intro p hp x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact mul_mem_mul (hmem p hp).1 (hU.decreasing (Nat.zero_le p.2) hy)
  have hsum : α * (∑ p ∈ S, μ (U p.2)) ≤ ν (E * U 0) := by
    calc
      _ = ∑ p ∈ S, α * μ (U p.2) := Finset.mul_sum ..
      _ ≤ ∑ p ∈ S, ν (p.1 • U p.2) := Finset.sum_le_sum hterm
      _ = ν (⋃ p ∈ S, p.1 • U p.2) :=
        (measure_biUnion_finset (μ := ν) hd (fun p _ => (hU.measurable p.2).const_smul p.1)).symm
      _ ≤ _ := measure_mono hin
  have hαle : (∑ p ∈ S, μ (U p.2)) ≤ ν (E * U 0) / α :=
    (ENNReal.le_div_iff_mul_le (.inl hα.ne') (.inl hαfin)).mpr (by simpa only [mul_comm] using hsum)
  have hCc : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hlt : μ E < (C : ℝ≥0∞) / α * ν (E * U 0) := by
    have h₁ := (ENNReal.div_lt_iff (.inl hCc) (.inl ENNReal.coe_ne_top)).mp hstrict
    calc
      μ E < (C : ℝ≥0∞) * (∑ p ∈ S, μ (U p.2)) := by simpa only [mul_comm] using h₁
      _ ≤ (C : ℝ≥0∞) * (ν (E * U 0) / α) := mul_le_mul_of_nonneg_left hαle zero_le
      _ = _ := by simp only [div_eq_mul_inv, mul_comm, mul_assoc]
  exact ⟨hlt.le, ⟨fun he => (hlt.ne he).elim, fun he => (hE he).elim⟩⟩

/-- Corrected Theorem A.5.3.4(1). The strict maximal bound uses the
same-stage difference-set hypothesis of the finite covering lemma. -/
theorem doublingMaximal_measure_bound (μ ν : Measure G) [μ.IsMulLeftInvariant]
    {U : ℕ → Set G} (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {B : Set G} (hfin : μ (B * U 0) < ⊤) {α : ℝ≥0∞} (hα : 0 < α) (hαfin : α ≠ ⊤) :
    let E := B ∩ {x | α < doublingMaximal μ ν U x}
    μ E ≤ (C : ℝ≥0∞) / α * ν (E * U 0) ∧
      (μ E = (C : ℝ≥0∞) / α * ν (E * U 0) ↔ E = ∅) :=
  doublingSequence_measure_bound_of_exists μ ν hU hC hDiff
    ((measure_mono (Set.mul_subset_mul inter_subset_left Subset.rfl)).trans_lt hfin) hα hαfin
    fun _ hx => exists_above_threshold_of_doublingMaximal hx.2

/-- A maximal function with a witness window at each exceeded threshold is finite almost
everywhere if the initial window is contained in a compact set. -/
theorem doublingSequence_ae_lt_top_of_threshold [TopologicalSpace G] [ContinuousMul G] [SigmaCompactSpace G]
    (μ ν : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : ℕ → Set G} (hU : DoublingSequence μ U) {K₀ : Set G} (hK₀ : IsCompact K₀)
    (hU₀ : U 0 ⊆ K₀)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (M : G → ℝ≥0∞)
    (hM : ∀ x a, a < M x → ∃ k, a < ν (x • U k) / μ (U k)) :
    ∀ᵐ x ∂μ, M x < ⊤ := by
  let E : Set G := {x | M x = ⊤}
  have hlocal (K : Set G) (hK : IsCompact K) : μ (K ∩ E) = 0 := by
    by_contra hnonzero
    have hproduct : IsCompact (K * K₀) := hK.mul hK₀
    have hsub : K * U 0 ⊆ K * K₀ := Set.mul_subset_mul Subset.rfl hU₀
    have hνfin : ν (K * U 0) < ⊤ := (measure_mono hsub).trans_lt hproduct.measure_lt_top
    have hnum : (C : ℝ≥0∞) * ν (K * U 0) < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hνfin
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hnum.ne hnonzero).ne
    have hnpos : 0 < (n : ℝ≥0∞) := zero_le.trans_lt hn
    have hnfin : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    let T := K ∩ {x | (n : ℝ≥0∞) < M x}
    have hT : K ∩ E ⊆ T := by
      intro x hx
      have hm : M x = ⊤ := hx.2
      refine ⟨hx.1, ?_⟩
      change (n : ℝ≥0∞) < M x
      rw [hm]
      exact lt_top_iff_ne_top.mpr hnfin
    have hbound : μ T ≤ (C : ℝ≥0∞) / n * ν (T * U 0) :=
      (doublingSequence_measure_bound_of_exists μ ν hU hC hDiff
        ((measure_mono ((Set.mul_subset_mul (show T ⊆ K from inter_subset_left) Subset.rfl).trans
          hsub)).trans_lt hproduct.measure_lt_top) hnpos hnfin (fun x hx => hM x n hx.2)).1
    have hupper : μ (K ∩ E) ≤ (C : ℝ≥0∞) / n * ν (K * U 0) :=
      (measure_mono hT).trans (hbound.trans
        (mul_le_mul_of_nonneg_left (measure_mono (Set.mul_subset_mul inter_subset_left Subset.rfl)) zero_le))
    have hscale : (n : ℝ≥0∞) * μ (K ∩ E) ≤ (C : ℝ≥0∞) * ν (K * U 0) := by
      apply (mul_le_mul_of_nonneg_left hupper (show (0 : ℝ≥0∞) ≤ n from zero_le)).trans
      rw [← mul_assoc, ENNReal.mul_div_cancel hnpos.ne' hnfin]
    have hn' := (ENNReal.div_lt_iff (.inl hnonzero)
      (.inl (ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono inter_subset_left)))).mp hn
    exact (not_lt_of_ge hscale) (by simpa only [mul_comm] using hn')
  have hsub : E ⊆ ⋃ n, compactCovering G n ∩ E := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_compactCovering x
    exact mem_iUnion.mpr ⟨n, hn, hx⟩
  have hE : μ E = 0 := le_antisymm ((measure_mono hsub).trans_eq
    (measure_iUnion_null fun n => hlocal _ (isCompact_compactCovering G n))) zero_le
  simpa only [ae_iff, not_lt, top_le_iff, E] using hE

/-- The almost-everywhere finiteness assertion of the corrected maximal theorem. -/
theorem doublingMaximal_ae_lt_top [TopologicalSpace G] [ContinuousMul G] [SigmaCompactSpace G]
    (μ ν : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : ℕ → Set G} (hU : DoublingSequence μ U) (hU₀ : IsCompact (U 0))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k)) :
    ∀ᵐ x ∂μ, doublingMaximal μ ν U x < ⊤ :=
  doublingSequence_ae_lt_top_of_threshold μ ν hU hU₀ Subset.rfl hC hDiff
    (doublingMaximal μ ν U) fun _ _ => exists_above_threshold_of_doublingMaximal

/-- Corrected Theorem A.5.3.5. Cofinality lets the maximal estimate
on a compact set depend only on the measure of that compact set. -/
theorem doublingMaximal_compact_bound [TopologicalSpace G] [ContinuousMul G] [LocallyCompactSpace G]
    (μ ν : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [ν.OuterRegular]
    {U : ℕ → Set G} (hU : DoublingSequence μ U) (hcof : CofinalAtOne U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {K : Set G} (hK : IsCompact K) {α : ℝ≥0∞} (hα : 0 < α) (hαfin : α ≠ ⊤) :
    μ (K ∩ {x | α < doublingMaximal μ ν U x}) ≤ (C : ℝ≥0∞) / α * ν K := by
  let E := K ∩ {x | α < doublingMaximal μ ν U x}
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hratio := (ENNReal.div_pos hCne hαfin).ne'
  have hratiofin : (C : ℝ≥0∞) / α ≠ ⊤ := (ENNReal.div_lt_top ENNReal.coe_ne_top hα.ne').ne
  apply (ENNReal.div_le_iff' hratio hratiofin).mp
  rw [K.measure_eq_iInf_isOpen ν]
  refine le_iInf fun O => le_iInf fun hKO => le_iInf fun hO => ?_
  apply (ENNReal.div_le_iff' hratio hratiofin).mpr
  have hpre : IsOpen ((fun p : G × G => p.1 * p.2) ⁻¹' O) := hO.preimage continuous_mul
  have hpro : K ×ˢ ({1} : Set G) ⊆ (fun p : G × G => p.1 * p.2) ⁻¹' O := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy' : y = 1 := hy
    subst y
    simpa using hKO hx
  obtain ⟨V, W, _, hWo, hKV, hOne, hVW⟩ := generalized_tube_lemma hK isCompact_singleton hpre hpro
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨n, hn⟩ := hcof (W ∩ N) (inter_mem (hWo.mem_nhds (hOne (mem_singleton 1))) hN)
  have hKO' : K * U n ⊆ O := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hVW (show (x, y) ∈ V ×ˢ W from ⟨hKV hx, (hn hy).1⟩)
  have hfin : μ (K * U n) < ⊤ :=
    (measure_mono (Set.mul_subset_mul Subset.rfl (fun _ hy => (hn hy).2))).trans_lt
      (hK.mul hNc).measure_lt_top
  let tail (k : ℕ) := U (k + n)
  have htail : DoublingSequence μ tail := by
    refine ⟨fun k => hU.one_mem (k+n), fun k => hU.measurable (k+n), fun k => hU.positive (k+n),
      fun k => hU.finite (k+n), fun _ _ h => hU.decreasing (Nat.add_le_add_right h n), ?_⟩
    obtain ⟨D, hDpos, hD⟩ := hU.doubling
    exact ⟨D, hDpos, fun k => by simpa only [tail, Nat.add_right_comm] using hD (k+n)⟩
  have hM (x : G) : doublingMaximal μ ν tail x = doublingMaximal μ ν U x :=
    limsup_nat_add (fun k => ν (x • U k) / μ (U k)) n
  have hmeasure := (doublingMaximal_measure_bound μ ν htail hC (fun k => hDiff (k+n))
    (B := K) (by simpa [tail] using hfin) hα hαfin).1
  have hbound : μ E ≤ (C : ℝ≥0∞) / α * ν (E * U n) := by
    simpa only [hM, tail, zero_add, E] using hmeasure
  have hEO : E * U n ⊆ O := (Set.mul_subset_mul inter_subset_left Subset.rfl).trans hKO'
  exact hbound.trans (mul_le_mul_of_nonneg_left (measure_mono hEO) zero_le)

end MaximalFunction

section CyclicSevenCounterexample

private def cyclicSevenSet : Finset (ZMod 7) := {0, 1, 3}

private theorem cyclicSevenSet_add : cyclicSevenSet + cyclicSevenSet = {0, 1, 2, 3, 4, 6} := by
  decide

private theorem cyclicSevenSet_sub : cyclicSevenSet - cyclicSevenSet = Finset.univ := by
  decide

/-- A nonempty counterexample to the printed covering constant in A.5.3.1.
The stage is constant on the cyclic group of order seven. Its sumset has
size six and every two of its translates intersect. -/
theorem cyclicSeven_finite_cover_obstruction :
    let U := (cyclicSevenSet : Set (ZMod 7))
    0 ∈ U ∧ cyclicSevenSet.card = 3 ∧ (cyclicSevenSet + cyclicSevenSet).card = 6 ∧
    (∀ x y : ZMod 7, ((x +ᵥ U) ∩ (y +ᵥ U)).Nonempty) ∧
    ¬ ∃ s : Finset (ZMod 7 × ℕ),
      (s : Set (ZMod 7 × ℕ)).PairwiseDisjoint (fun p => p.1 +ᵥ U) ∧
      (7 : ℝ) / (9 / 4) < ∑ _p ∈ s, (cyclicSevenSet.card : ℝ) := by
  let U := (cyclicSevenSet : Set (ZMod 7))
  have hU : cyclicSevenSet.card = 3 := by decide
  have hInter (x y : ZMod 7) : ((x +ᵥ U) ∩ (y +ᵥ U)).Nonempty := by
    have hmem : y - x ∈ (↑(cyclicSevenSet - cyclicSevenSet) : Set (ZMod 7)) := by
      rw [cyclicSevenSet_sub, Finset.coe_univ]
      trivial
    rw [Finset.coe_sub] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    change a - b = y - x at hab
    refine ⟨x + a, ⟨a, ha, rfl⟩, b, hb, ?_⟩
    change y + b = x + a
    calc
      y + b = (y - x) + x + b := by abel
      _ = (a - b) + x + b := by rw [hab]
      _ = x + a := by abel
  refine ⟨by decide, hU, by rw [cyclicSevenSet_add]; decide, hInter, ?_⟩
  rintro ⟨s, hd, hsum⟩
  have hcard : s.card ≤ 1 := Finset.card_le_one_iff.mpr fun {p q} hp hq => by
    by_contra hne
    obtain ⟨z, hzp, hzq⟩ := hInter p.1 q.1
    exact Set.disjoint_left.mp (hd hp hq hne) hzp hzq
  have hle : (s.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  simp only [hU, Nat.cast_ofNat, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

end CyclicSevenCounterexample

end Masullo
