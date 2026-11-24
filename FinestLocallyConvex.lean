import TopologicalLinearLimits
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Basis.VectorSpace

open Filter Function Module Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

abbrev finestLocallyConvexTopology (E : Type*) [AddCommGroup E] [Module ℂ E] :
    TopologicalSpace E :=
  (SeminormFamily.moduleFilterBasis (fun p : Seminorm ℂ E => p)).topology

theorem finest_withSeminorms (E : Type*) [AddCommGroup E] [Module ℂ E] :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    WithSeminorms (fun p : Seminorm ℂ E => p) :=
  by
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    exact ⟨rfl⟩

theorem finest_linear_continuous {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]
    (L : E →ₗ[ℂ] F) : Continuous[finestLocallyConvexTopology E, inferInstance] L := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  letI : IsTopologicalAddGroup E := (finest_withSeminorms E).topologicalAddGroup
  refine ((PolynormableSpace.withSeminorms ℂ F).continuous_iff_continuous_comp L).2 ?_
  intro q
  exact (finest_withSeminorms E).continuous_seminorm (q.val.comp L)

variable {I : Type*}

abbrev ScalarLone (I : Type*) := lp (fun _ : I => ℂ) 1

/-- Multiplication by arbitrary coordinate weights sends finitely supported
vectors into the Banach space of absolutely summable families. -/
def weightedLone (w : I → ℂ) : (I →₀ ℂ) →ₗ[ℂ] ScalarLone I where
  toFun x := ⟨fun i => w i * x i, by
    apply memℓp_gen
    apply summable_of_ne_finset_zero (s := x.support)
    intro i hi
    simp [Finsupp.notMem_support_iff.mp hi]⟩
  map_add' x y := by
    ext i
    change w i * (x i + y i) = w i * x i + w i * y i
    exact mul_add ..
  map_smul' a x := by
    ext i
    change w i * (a * x i) = a * (w i * x i)
    ring

@[simp] theorem weightedLone_apply (w : I → ℂ) (x : I →₀ ℂ) (i : I) :
    weightedLone w x i = w i * x i := rfl

abbrev weightedLoneSeminorm (w : I → ℂ) : Seminorm ℂ (I →₀ ℂ) :=
  (normSeminorm ℂ (ScalarLone I)).comp (weightedLone w)

theorem weightedLone_norm (w : I → ℂ) (x : I →₀ ℂ) :
    ‖weightedLone w x‖ = ∑ i ∈ x.support, ‖w i‖ * ‖x i‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, weightedLone_apply, norm_mul]
  apply tsum_eq_sum
  intro i hi
  simp [Finsupp.notMem_support_iff.mp hi]

theorem finsupp_seminorm_le_mul_weightedLone (q : Seminorm ℂ (I →₀ ℂ)) (w : I → ℂ)
    (C : ℝ) (hw : ∀ i, q (Finsupp.single i 1) ≤ C * ‖w i‖) (x : I →₀ ℂ) :
    q x ≤ C * ‖weightedLone w x‖ := by
  classical
  rw [weightedLone_norm, Finset.mul_sum]
  have hx : ∑ i ∈ x.support, x i • Finsupp.single i (1 : ℂ) = x := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.sum_single x
  have hs (s : Finset I) :
      q (∑ i ∈ s, x i • Finsupp.single i (1 : ℂ)) ≤
        ∑ i ∈ s, C * (‖w i‖ * ‖x i‖) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine (map_add_le_add q _ _).trans (add_le_add ?_ ih)
      rw [map_smul_eq_mul, mul_comm, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)
  exact (congrArg q hx.symm).le.trans (hs x.support)

theorem finsupp_seminorm_le_weightedLone (q : Seminorm ℂ (I →₀ ℂ)) (w : I → ℂ)
    (hw : ∀ i, q (Finsupp.single i 1) ≤ ‖w i‖) (x : I →₀ ℂ) :
    q x ≤ ‖weightedLone w x‖ := by
  simpa only [one_mul] using finsupp_seminorm_le_mul_weightedLone q w 1
    (fun i => by simpa only [one_mul] using hw i) x

theorem finest_seminorm_le_weightedLone (q : Seminorm ℂ (I →₀ ℂ)) :
    ∃ w, q ≤ weightedLoneSeminorm w := by
  let w : I → ℂ := fun i => ↑(q (Finsupp.single i 1))
  refine ⟨w, fun x => finsupp_seminorm_le_weightedLone q w (fun i => ?_) x⟩
  change _ ≤ ‖((↑(q (Finsupp.single i 1)) : ℂ))‖
  rw [Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q _)]

abbrev finestUniformSpace (E : Type*) [AddCommGroup E] [Module ℂ E] : UniformSpace E := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  exact @IsTopologicalAddGroup.rightUniformSpace E _ (finestLocallyConvexTopology E)
    (finest_withSeminorms E).topologicalAddGroup

theorem finest_finsupp_complete :
    letI : UniformSpace (I →₀ ℂ) := finestUniformSpace (I →₀ ℂ)
    CompleteSpace (I →₀ ℂ) := by
  classical
  letI : UniformSpace (I →₀ ℂ) := finestUniformSpace (I →₀ ℂ)
  letI : IsUniformAddGroup (I →₀ ℂ) :=
    @isUniformAddGroup_of_addCommGroup _ _ (finestLocallyConvexTopology _)
      (finest_withSeminorms _).topologicalAddGroup
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have W : WithSeminorms (fun p : Seminorm ℂ (I →₀ ℂ) => p) := finest_withSeminorms _
  constructor
  intro l hl
  have hlimit (w : I → ℂ) : ∃ y : ScalarLone I, Tendsto (weightedLone w) l (𝓝 y) := by
    have hc : Continuous (weightedLone w) := finest_linear_continuous (weightedLone w)
    have hu : UniformContinuous (weightedLone w) :=
      uniformContinuous_of_continuousAt_zero (weightedLone w) hc.continuousAt
    exact CompleteSpace.complete (hl.map hu)
  choose y hy using hlimit
  haveI : NeBot l := hl.1
  let x : I → ℂ := y (fun _ => 1)
  have hycoord (w : I → ℂ) (i : I) : y w i = w i * x i := by
    let e := lp.evalCLM ℂ (fun _ : I => ℂ) 1 i
    have h₁ : Tendsto (fun a : I →₀ ℂ => w i * a i) l (𝓝 (y w i)) := by
      simpa [e, Function.comp_def, lp.evalCLM] using
        e.continuous.continuousAt.tendsto.comp (hy w)
    have h₂ : Tendsto (fun a : I →₀ ℂ => a i) l (𝓝 (x i)) := by
      simpa [x, e, Function.comp_def, lp.evalCLM] using
        e.continuous.continuousAt.tendsto.comp (hy (fun _ => 1))
    exact tendsto_nhds_unique h₁ (tendsto_const_nhds.mul h₂)
  let w : I → ℂ := fun i => ↑(‖x i‖⁻¹)
  have hs : Summable (fun i => ‖y w i‖) := by
    simpa using (lp.memℓp (y w)).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  have hfinite : (support x).Finite := by
    have he := hs.tendsto_cofinite_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    apply (eventually_cofinite.mp he).subset
    intro i hi
    have hx : x i ≠ 0 := hi
    have hp : 0 < ‖x i‖ := norm_pos_iff.mpr hx
    have eq : ‖y w i‖ = 1 := by
      rw [hycoord, norm_mul]
      simp [w, inv_mul_cancel₀ hp.ne']
    simp [eq]
  let a : I →₀ ℂ := Finsupp.ofSupportFinite x hfinite
  have ha (w : I → ℂ) : y w = weightedLone w a := by
    ext i
    exact hycoord w i
  refine ⟨a, (W.tendsto_nhds id a).2 fun q ε hε => ?_⟩
  obtain ⟨v, hv⟩ := finest_seminorm_le_weightedLone q
  have ht := Metric.tendsto_nhds.mp (hy v) ε hε
  filter_upwards [ht] with b hb
  apply (hv (b - a)).trans_lt
  change ‖weightedLone v (b - a)‖ < ε
  rw [map_sub, ← ha]
  rwa [dist_eq_norm] at hb

theorem finest_finsupp_bounded_support {B : Set (I →₀ ℂ)}
    (hB : @Bornology.IsVonNBounded ℂ (I →₀ ℂ) _ _ _ (finestLocallyConvexTopology _) B) :
    {i | ∃ x ∈ B, x i ≠ 0}.Finite := by
  classical
  letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
  letI : IsTopologicalAddGroup (I →₀ ℂ) := (finest_withSeminorms _).topologicalAddGroup
  letI : ContinuousSMul ℂ (I →₀ ℂ) := (finest_withSeminorms _).continuousSMul
  let S : Set I := {i | ∃ x ∈ B, x i ≠ 0}
  by_contra! h
  let e : ℕ ↪ S := h.natEmbedding S
  let j : ℕ → I := fun n => e n
  have hj : Injective j := fun _ _ hnm => e.injective (Subtype.ext hnm)
  have hsel (n : ℕ) : ∃ x ∈ B, x (j n) ≠ 0 := (e n).property
  choose x hx hne using hsel
  let a (n : ℕ) : ℂ := ↑((n : ℝ) / ‖x n (j n)‖)
  let w : I → ℂ := Function.extend j a (fun _ => 0)
  have hw (n : ℕ) : w (j n) = a n := hj.extend_apply a _ n
  obtain ⟨R, _, hR⟩ := (finest_withSeminorms (I →₀ ℂ)).isVonNBounded_iff_seminorm_bounded.mp
    hB (weightedLoneSeminorm w)
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hp : 0 < ‖x n (j n)‖ := norm_pos_iff.mpr (hne n)
  have hnorm : ‖weightedLone w (x n) (j n)‖ = (n : ℝ) := by
    rw [weightedLone_apply, hw, norm_mul]
    simp [a, hp.ne']
  have hcoord := lp.norm_apply_le_norm (by simp : (1 : ℝ≥0∞) ≠ 0) (weightedLone w (x n)) (j n)
  exact (not_le_of_gt hn) ((hnorm ▸ hcoord).trans (hR _ (hx n)).le)

theorem finest_complete (E : Type*) [AddCommGroup E] [Module ℂ E] :
    letI : UniformSpace E := finestUniformSpace E
    CompleteSpace E := by
  let b := Basis.ofVectorSpace ℂ E
  let I := Basis.ofVectorSpaceIndex ℂ E
  letI : UniformSpace E := finestUniformSpace E
  letI : UniformSpace (I →₀ ℂ) := finestUniformSpace _
  letI : IsUniformAddGroup E :=
    @isUniformAddGroup_of_addCommGroup _ _ (finestLocallyConvexTopology _)
      (finest_withSeminorms _).topologicalAddGroup
  letI : IsUniformAddGroup (I →₀ ℂ) :=
    @isUniformAddGroup_of_addCommGroup _ _ (finestLocallyConvexTopology _)
      (finest_withSeminorms _).topologicalAddGroup
  letI : PolynormableSpace ℂ E := (finest_withSeminorms E).toPolynormableSpace
  letI : PolynormableSpace ℂ (I →₀ ℂ) := (finest_withSeminorms _).toPolynormableSpace
  letI : CompleteSpace (I →₀ ℂ) := finest_finsupp_complete
  have hc : UniformContinuous b.repr :=
    uniformContinuous_of_continuousAt_zero b.repr.toLinearMap
      (finest_linear_continuous b.repr.toLinearMap).continuousAt
  have hi : UniformContinuous b.repr.symm :=
    uniformContinuous_of_continuousAt_zero b.repr.symm.toLinearMap
      (finest_linear_continuous b.repr.symm.toLinearMap).continuousAt
  constructor
  intro l hl
  obtain ⟨y, hy⟩ := CompleteSpace.complete (hl.map hc)
  refine ⟨b.repr.symm y, ?_⟩
  change Tendsto (fun x : E => x) l (𝓝 (b.repr.symm y))
  simpa only [Filter.map_map, Function.comp_def, LinearEquiv.symm_apply_apply, Filter.map_id] using
    hi.continuous.continuousAt.tendsto.comp hy

theorem finest_t2 (E : Type*) [AddCommGroup E] [Module ℂ E] :
    @T2Space E (finestLocallyConvexTopology E) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let b := Basis.ofVectorSpace ℂ E
  exact T2Space.of_injective_continuous (f := fun x i => b.repr x i)
    (fun _ _ h => b.repr.injective (Finsupp.ext (congrFun h)))
    (continuous_pi fun i => finest_linear_continuous (b.coord i))

end
end Masullo
