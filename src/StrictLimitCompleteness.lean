import SeminormGluing

open Bornology Filter Function Set Topology UniformSpace
open scoped Pointwise NNReal Uniformity

namespace Masullo

noncomputable section

namespace LinearInductivePresentation

variable {E : Type*} {X : ℕ → Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
variable (D : LinearInductivePresentation E X)

-- The completion separation argument follows the proof in original
-- AppC_LCTVS/Sec1.lean at 30bbc8e0e958b158ff78c0727f1cb1a66d487ca7 (Apache-2.0).
/-- Seminorms that vanish on successively larger stages admit a continuous upper bound
on the limit, since only finitely many contribute on any one stage. -/
private theorem exists_seminorm_ge_of_vanishing_on_stages [∀ k, IsTopologicalAddGroup (X k)]
    (hlimit : ∀ p : Seminorm ℂ E, (∀ k, Continuous (p.comp (D.incl k).toLinearMap)) → Continuous p)
    (q : ℕ → Seminorm ℂ E) (hq : ∀ n, Continuous (q n)) (hz : ∀ n z, q n (D.incl n z) = 0) :
    ∃ P : Seminorm ℂ E, Continuous P ∧ ∀ n, q n ≤ P := by
  classical
  let S (k : ℕ) : Submodule ℂ E := (D.incl k).toLinearMap.range
  have hmono : Monotone S := fun _ _ h ↦ D.range_incl_mono h
  let M (k : ℕ) := (Finset.range k).sup (fun n ↦ (q n).comp (D.incl k).toLinearMap)
  have hM (k n : ℕ) (y : X k) : q n (D.incl k y) ≤ M k y := by
    by_cases hn : n < k
    · exact (Finset.le_sup (f := fun n ↦ (q n).comp (D.incl k).toLinearMap)
        (Finset.mem_range.mpr hn) : _ ≤ M k) y
    · obtain ⟨z, hzy⟩ := hmono (Nat.le_of_not_gt hn) (show D.incl k y ∈ S k from ⟨y, rfl⟩)
      change D.incl n z = D.incl k y at hzy
      rw [← hzy, hz]
      exact apply_nonneg _ _
  have hb : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun y ↦ by
    obtain ⟨k, z, rfl⟩ := D.exhaust y
    exact ⟨M k z, forall_mem_range.mpr fun n ↦ hM k n z⟩
  let P : Seminorm ℂ E := ⨆ n, q n
  refine ⟨P, hlimit P (fun k ↦ ?_), fun n ↦ le_ciSup hb n⟩
  have hcont : Continuous (M k) := Seminorm.continuous_finsetSup fun n _ ↦ (hq n).comp (D.incl k).continuous
  refine Seminorm.continuous_of_le (p := P.comp (D.incl k).toLinearMap) hcont
    (Seminorm.le_def.mpr fun y ↦ ?_)
  change P (D.incl k y) ≤ M k y
  rw [Seminorm.iSup_apply hb]
  exact ciSup_le fun n ↦ hM k n y

/-- A countable locally convex inductive limit of complete stages is
complete when the stage inclusions are embeddings. The uniformity is the
additive uniformity of the given locally convex topology. -/
theorem complete_of_strict
    [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [∀ k, IsTopologicalAddGroup (X k)]
    (hc : ∀ k, @CompleteSpace (X k) (IsTopologicalAddGroup.rightUniformSpace (X k)))
    (hemb : ∀ k, IsEmbedding (D.incl k))
    (hlimit : ∀ p : Seminorm ℂ E, (∀ k, Continuous (p.comp (D.incl k).toLinearMap)) → Continuous p) :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
  classical
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : ∀ k, UniformSpace (X k) := fun k ↦ IsTopologicalAddGroup.rightUniformSpace (X k)
  let : ∀ k, IsUniformAddGroup (X k) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ k, CompleteSpace (X k) := hc
  let S (k : ℕ) : Submodule ℂ E := (D.incl k).toLinearMap.range
  have hcomplete (k : ℕ) : IsComplete (S k : Set E) := by
    have hi : IsUniformInducing (D.incl k) :=
      AddMonoidHom.isUniformInducing_of_isInducing (hemb k).isInducing
    exact hi.isComplete_range
  let e : E →+ UniformSpace.Completion E := UniformSpace.Completion.toCompl
  have he : IsUniformInducing e := UniformSpace.Completion.isUniformInducing_coe E
  have hd : DenseRange e := UniformSpace.Completion.denseRange_coe
  suffices hs : Function.Surjective e by exact (he.completeSpace_congr hs).mpr inferInstance
  intro x
  by_contra hx
  -- Separate a point outside the completion image from each complete stage.
  have hsep (k : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧
      (∀ y ∈ S k, q y = 0) ∧ x ∉ closure (e '' q.ball 0 1) := by
    have hclosed : IsClosed (e '' (S k : Set E)) :=
      (he.isComplete_iff.mpr (hcomplete k)).isClosed
    have hout : x ∉ e '' (S k : Set E) := fun ⟨y, _, hy⟩ ↦ hx ⟨y, hy⟩
    let C := e '' (S k : Set E)
    have hsub : (fun z : Completion E × Completion E ↦ z.1 - z.2) ⁻¹' Cᶜ ∈
        𝓝 ((x, 0) : Completion E × Completion E) :=
      continuous_sub.continuousAt.preimage_mem_nhds (by
        simpa only [sub_zero] using hclosed.isOpen_compl.mem_nhds hout)
    obtain ⟨V, hV, U, hU, hVU⟩ := mem_nhds_prod_iff.mp hsub
    have hxU : x ∉ closure (C + U) := by
      intro hx
      obtain ⟨w, hw, c, hc, u, hu, rfl⟩ := mem_closure_iff_nhds.mp hx V hV
      have hc' : (c+u)-u ∈ Cᶜ := hVU (show (c+u, u) ∈ V ×ˢ U from ⟨hw, hu⟩)
      exact hc' (by simpa only [add_sub_cancel_right] using hc)
    have hpre : e ⁻¹' U ∈ 𝓝 (0 : E) := by
      apply he.uniformContinuous.continuous.continuousAt.preimage_mem_nhds
      simpa only [map_zero] using hU
    obtain ⟨⟨J, r⟩, hr, hball⟩ :=
      (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball.mem_iff.mp hpre
    let p := J.sup (fun v : {p : Seminorm ℂ E // Continuous p} ↦ v.val)
    have hp : Continuous p := Seminorm.continuous_finsetSup (fun v _ ↦ v.property)
    obtain ⟨q, hqp, hzero, hqball⟩ := exists_seminorm_thickening p (S k)
    let c : ℝ≥0 := ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
    let q' := c • q
    have hc : Continuous q' := (Seminorm.continuous_of_le hp hqp).const_smul c
    have hEq : q'.ball 0 1 = q.ball 0 r := by
      ext y
      simp only [Seminorm.mem_ball_zero, q', smul_apply, NNReal.smul_def, smul_eq_mul]
      change r⁻¹ * q y < 1 ↔ q y < r
      rw [inv_mul_lt_iff₀ hr, mul_one]
    refine ⟨q', hc, fun y hy ↦ by simp only [q', smul_apply, hzero y hy, smul_zero], ?_⟩
    intro hxball
    apply hxU (closure_mono ?_ hxball)
    rw [hEq, hqball r]
    rintro _ ⟨_, ⟨y, hy, z, hz, rfl⟩, rfl⟩
    rw [map_add]
    exact add_mem_add (mem_image_of_mem _ hy) (hball hz)
  choose q hq hzero hout using hsep
  -- Each stage sees only a finite supremum of the weighted seminorms.
  let Q (n : ℕ) : Seminorm ℂ E := ((n : NNReal) + 1) • q n
  obtain ⟨P, hP, hle⟩ := D.exists_seminorm_ge_of_vanishing_on_stages hlimit Q
    (fun n ↦ (hq n).const_smul ((n : NNReal) + 1)) (fun n z ↦ by
      have hz : q n (D.incl n z) = 0 := hzero n _ ⟨z, rfl⟩
      simp only [Q, smul_apply, hz, smul_zero])
  have hUC : UniformContinuous P := Seminorm.uniformContinuous_of_continuousAt_zero hP.continuousAt
  let v : UniformSpace.Completion E → ℝ := UniformSpace.Completion.extension P
  have hv : Continuous v := UniformSpace.Completion.continuous_extension
  have hvcoe (y : E) : v (e y) = P y := UniformSpace.Completion.extension_coe hUC y
  obtain ⟨n, hn⟩ := exists_nat_gt (v x)
  have hlarge : v x < (n : ℝ) + 1 := hn.trans (lt_add_one _)
  have hnear : (closure (e '' (q n).ball 0 1))ᶜ ∩ v ⁻¹' Iio ((n : ℝ) + 1) ∈ 𝓝 x :=
    inter_mem (isClosed_closure.isOpen_compl.mem_nhds (hout n))
      ((isOpen_Iio.preimage hv).mem_nhds hlarge)
  obtain ⟨_, hy, y, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hnear
  have hy' : P y < (n : ℝ) + 1 := by
    simpa only [mem_preimage, mem_Iio, hvcoe] using hy.2
  apply hy.1 (subset_closure (mem_image_of_mem _ ((q n).mem_ball_zero.mpr ?_)))
  have hbound := (hle n y).trans_lt hy'
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  apply (mul_lt_mul_iff_right₀ hpos).mp
  simpa only [Q, smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, mul_one]
    using hbound

end LinearInductivePresentation

end

end Masullo
