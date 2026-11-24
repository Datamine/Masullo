import OpenBoxDoubling

open Filter Function MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- A uniform bound on the number of translates needed to cover
each adjacent-stage product. -/
def AdjacentTranslateCover (U : ℕ → Set G) : Prop :=
  ∃ N : ℕ, ∀ k, ∃ t : Fin N → G, U (k + 1) * U k ⊆ ⋃ j, t j • U (k + 1)

/-- An open basis with compact bounds and uniform finite translate covers. -/
structure OpenTranslateBasis (U : ℕ → Set G) : Prop where
  one_mem : ∀ k, 1 ∈ U k
  open_set : ∀ k, IsOpen (U k)
  decreasing : Antitone U
  symmetric : ∀ k, (U k)⁻¹ = U k
  compact_bound : ∀ k, ∃ K : Set G, IsCompact K ∧ U k ⊆ K
  cofinal : CofinalAtOne U
  translates : AdjacentTranslateCover U

theorem OpenTranslateBasis.doubling {U : ℕ → Set G} (h : OpenTranslateBasis U)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    DoublingSequence μ U := by
  have hp (k : ℕ) : 0 < μ (U k) := (h.open_set k).measure_pos μ ⟨1, h.one_mem k⟩
  have hf (k : ℕ) : μ (U k) < ⊤ := by
    obtain ⟨K, hc, hs⟩ := h.compact_bound k
    exact (measure_mono hs).trans_lt hc.measure_lt_top
  refine ⟨h.one_mem, fun k => (h.open_set k).measurableSet, hp, hf, h.decreasing, ?_⟩
  obtain ⟨N, hN⟩ := h.translates
  refine ⟨(N : ℝ≥0) + 1, by positivity, fun k => ⟨?_, ?_⟩⟩
  · have hs : U (k + 1) ⊆ U (k + 1) * U k :=
      fun x hx => ⟨x, hx, 1, h.one_mem k, mul_one x⟩
    exact (hp (k + 1)).trans_le (measure_mono hs)
  · obtain ⟨t, ht⟩ := hN k
    have hm : μ (U (k + 1) * U k) ≤ (N : ℝ≥0∞) * μ (U (k + 1)) :=
      (measure_mono ht).trans ((measure_iUnion_fintype_le μ _).trans_eq (by
        simp [measure_smul, nsmul_eq_mul]))
    exact hm.trans_lt (ENNReal.mul_lt_mul_left (hp _).ne' (hf _).ne
      (by exact_mod_cast (lt_add_one (N : ℝ≥0))))

theorem OpenTranslateBasis.image {U : ℕ → Set G} (h : OpenTranslateBasis U)
    (f : G →* H) (hf : Continuous f) (ho : IsOpenMap f) :
    OpenTranslateBasis (fun k => f '' U k) := by
  refine ⟨fun k => ⟨1, h.one_mem k, f.map_one⟩, fun k => ho _ (h.open_set k),
    fun _ _ hk => image_mono (h.decreasing hk), ?_, ?_, ?_, ?_⟩
  · intro k
    have hi : f '' (U k)⁻¹ = (f '' U k)⁻¹ := Set.image_inv f (U k)
    rw [← hi, h.symmetric]
  · intro k
    obtain ⟨K, hK, hs⟩ := h.compact_bound k
    exact ⟨f '' K, hK.image hf, image_mono hs⟩
  · intro W hW
    obtain ⟨k, hk⟩ := h.cofinal _ (hf.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hW))
    exact ⟨k, image_subset_iff.mpr hk⟩
  · obtain ⟨N, hN⟩ := h.translates
    refine ⟨N, fun k => ?_⟩
    obtain ⟨t, ht⟩ := hN k
    refine ⟨f ∘ t, ?_⟩
    rw [← Set.image_mul f]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨i, b, hb, he⟩ := mem_iUnion.mp (ht ha)
    exact mem_iUnion.mpr ⟨i, f b, ⟨b, hb, rfl⟩, by
      change f (t i) * f b = f a
      rw [← map_mul, show t i * b = a from he]⟩

theorem OpenTranslateBasis.prod {U : ℕ → Set G} {V : ℕ → Set H}
    (h : OpenTranslateBasis U) (g : OpenTranslateBasis V) :
    OpenTranslateBasis (fun k => U k ×ˢ V k) := by
  have props := doublingSequence_prod_properties (U := U) (V := V)
  refine ⟨fun k => ⟨h.one_mem k, g.one_mem k⟩, props.2.1 h.open_set g.open_set,
    fun _ _ hk => Set.prod_mono (h.decreasing hk) (g.decreasing hk),
    props.2.2 h.symmetric g.symmetric, ?_, props.1 h.decreasing g.decreasing h.cofinal g.cofinal, ?_⟩
  · intro k
    obtain ⟨K, hc, hk⟩ := h.compact_bound k
    obtain ⟨L, hd, hl⟩ := g.compact_bound k
    exact ⟨K ×ˢ L, hc.prod hd, Set.prod_mono hk hl⟩
  · obtain ⟨N, hN⟩ := h.translates
    obtain ⟨M, hM⟩ := g.translates
    let e := Fintype.equivFin (Fin N × Fin M)
    refine ⟨Fintype.card (Fin N × Fin M), fun k => ?_⟩
    obtain ⟨a, ha⟩ := hN k
    obtain ⟨b, hb⟩ := hM k
    refine ⟨fun j => (a (e.symm j).1, b (e.symm j).2), ?_⟩
    rintro _ ⟨⟨x₁, y₁⟩, ⟨hx₁, hy₁⟩, ⟨x₂, y₂⟩, ⟨hx₂, hy₂⟩, rfl⟩
    obtain ⟨i, x, hx, he⟩ := mem_iUnion.mp (ha (mul_mem_mul hx₁ hx₂))
    obtain ⟨j, y, hy, hf⟩ := mem_iUnion.mp (hb (mul_mem_mul hy₁ hy₂))
    refine mem_iUnion.mpr ⟨e (i,j), (x,y), ⟨hx,hy⟩, ?_⟩
    change (a (e.symm (e (i,j))).1 * x, b (e.symm (e (i,j))).2 * y) = (x₁ * x₂, y₁ * y₂)
    rw [Equiv.symm_apply_apply]
    exact Prod.ext he hf

theorem groupBox_translateBasis {I : Type*} [Fintype I]
    (p : Multiplicative (I → ℝ) →* G) (hp : Continuous p) (ho : IsOpenMap p)
    {c : ℝ} (hc : 0 < c) :
    OpenTranslateBasis (fun k => groupBox p (boxRadius c k)) := by
  have hd : Antitone (boxRadius c) := by
    intro i j hij
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    exact add_le_add_left (by exact_mod_cast hij : (i : ℝ) ≤ j) 1
  refine ⟨fun k => groupBox_one p (boxRadius_pos hc k),
    fun k => groupBox_isOpen p ho _, fun _ _ hk => groupBox_mono p (hd hk),
    fun k => groupBox_inv p _, ?_, ?_, ?_⟩
  · intro k
    refine ⟨(fun x : I → ℝ => p (Multiplicative.ofAdd x)) '' Metric.closedBall 0 (boxRadius c k),
      (isCompact_closedBall _ _).image (hp.comp continuous_ofAdd), image_mono ball_subset_closedBall⟩
  · intro S hS
    have h := (hp.comp continuous_ofAdd).continuousAt.preimage_mem_nhds
      (show S ∈ 𝓝 (p (Multiplicative.ofAdd (0 : I → ℝ))) by
        change S ∈ 𝓝 (p 1)
        rwa [map_one])
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
    obtain ⟨k, hk⟩ := exists_nat_gt (c / ε)
    use k
    have hkr : boxRadius c k < ε := by
      unfold boxRadius
      apply (div_lt_iff₀ (by positivity)).mpr
      have hh := (div_lt_iff₀ hε).mp hk
      nlinarith
    rintro _ ⟨x, hx, rfl⟩
    exact hball (ball_subset_ball hkr.le hx)
  · let e := Fintype.equivFin (BoxShift I)
    refine ⟨Fintype.card (BoxShift I), fun k => ?_⟩
    let r := boxRadius c (k + 1)
    refine ⟨fun j => p (Multiplicative.ofAdd (boxCenter r (e.symm j))), ?_⟩
    have hs := (groupBox_mul_subset p _ _).trans (groupBox_mono p (boxRadius_adjacent hc k))
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (groupBox_grid_subset p (boxRadius_pos hc _) (hs hx))
    exact mem_iUnion.mpr ⟨e j, by simpa only [Equiv.symm_apply_apply] using hj⟩

/-- For a compact open subgroup basis the adjacent translate condition is
the uniform finite-index bound. -/
theorem compactOpen_translateBasis (K : ℕ → Subgroup G)
    (hKc : ∀ k, IsCompact (K k : Set G)) (hKo : ∀ k, IsOpen (K k : Set G))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set G)))
    (hcov : ∃ N : ℕ, ∀ k, ∃ t : Fin N → G, (K k : Set G) ⊆ ⋃ j, t j • (K (k + 1) : Set G)) :
    OpenTranslateBasis (fun k => (K k : Set G)) := by
  refine ⟨fun k => (K k).one_mem, hKo, hdec, ?_, fun k => ⟨_, hKc k, subset_rfl⟩, hcof, ?_⟩
  · intro k
    ext x
    exact ⟨fun h => by simpa using (K k).inv_mem h, (K k).inv_mem⟩
  · obtain ⟨N, hN⟩ := hcov
    refine ⟨N, fun k => ?_⟩
    obtain ⟨t, ht⟩ := hN k
    exact ⟨t, fun _ ⟨a, ha, b, hb, he⟩ => he ▸ ht ((K k).mul_mem (hdec (Nat.le_succ k) ha) hb)⟩

end

end Masullo
