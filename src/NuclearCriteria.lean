import NuclearIntegralOperators
import InductiveTensorTopology
import NuclearFactorization

/-! # Nuclearity and the canonical comparison of completed tensors -/

open Filter Function Set TopologicalSpace Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

universe u v

section Comparison

variable {E F : Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]

private def projectiveToInjectiveMap :
    @ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ)
      (E ⊗[ℂ] F) (projectiveTensorTopology E F) _
      (E ⊗[ℂ] F) (injectiveTensorTopology E F) _ _ _ :=
  @ContinuousLinearMap.mk ℂ ℂ _ _ (RingHom.id ℂ)
    (E ⊗[ℂ] F) (projectiveTensorTopology E F) _
    (E ⊗[ℂ] F) (injectiveTensorTopology E F) _ _ _
    LinearMap.id (projective_to_injective_continuous (E := E) (F := F))

/-- The canonical projective-to-injective map on separated tensor completions. -/
def completedTensorComparison :
    (projectiveTensorModuleStructure E F).Completed →L[ℂ] (injectiveTensorStructure E F).Completed := by
  let P := projectiveTensorModuleStructure E F
  let I := injectiveTensorStructure E F
  exact @ContinuousLinearMap.completion (E ⊗[ℂ] F) (E ⊗[ℂ] F) ℂ ℂ
    P.uniformSpace _ P.uniformGroup _ _ P.uniformConstSmul _ I.uniformSpace _ I.uniformGroup
    _ I.uniformConstSmul _ (projectiveToInjectiveMap (E := E) (F := F))

@[simp] theorem completedTensorComparison_incl (z : E ⊗[ℂ] F) :
    completedTensorComparison ((projectiveTensorModuleStructure E F).incl z) =
      (injectiveTensorStructure E F).incl z := by
  let P := projectiveTensorModuleStructure E F
  let I := injectiveTensorStructure E F
  exact @ContinuousLinearMap.completion_apply_coe (E ⊗[ℂ] F) (E ⊗[ℂ] F) ℂ ℂ
    P.uniformSpace _ P.uniformGroup _ _ P.uniformConstSmul _ I.uniformSpace _ I.uniformGroup
    _ I.uniformConstSmul _ (projectiveToInjectiveMap (E := E) (F := F)) z

/-- The comparison is a topological isomorphism precisely when the algebraic
tensor topologies agree. The converse uses the inducing maps to completion. -/
theorem completedTensorComparison_iff :
    (∃ e : (projectiveTensorModuleStructure E F).Completed ≃L[ℂ]
      (injectiveTensorStructure E F).Completed, e.toContinuousLinearMap = completedTensorComparison) ↔
      projectiveTensorTopology E F = injectiveTensorTopology E F := by
  let P := projectiveTensorModuleStructure E F
  let I := injectiveTensorStructure E F
  have hp : @IsInducing _ _ P.topology _ P.incl := by
    letI : UniformSpace (E ⊗[ℂ] F) := P.uniformSpace
    exact (Completion.isUniformInducing_coe (E ⊗[ℂ] F)).isInducing
  have hi : @IsInducing _ _ I.topology _ I.incl := by
    letI : UniformSpace (E ⊗[ℂ] F) := I.uniformSpace
    exact (Completion.isUniformInducing_coe (E ⊗[ℂ] F)).isInducing
  constructor
  · rintro ⟨e, he⟩
    have hcomp : e ∘ P.incl = I.incl := funext fun z => by
      change e.toContinuousLinearMap (P.incl z) = I.incl z
      rw [he, completedTensorComparison_incl]
    have hind : @IsInducing _ _ P.topology _ (e ∘ P.incl) := by
      letI : TopologicalSpace (E ⊗[ℂ] F) := P.topology
      exact e.toHomeomorph.isInducing.comp hp
    rw [hcomp] at hind
    exact (@IsInducing.eq_induced _ _ P.topology _ _ hind).trans
      (@IsInducing.eq_induced _ _ I.topology _ _ hi).symm
  · intro h
    let e := TopologicalModuleStructure.completionEquiv (D := P) (D' := I) h
    refine ⟨e, DFunLike.coe_injective ?_⟩
    apply @Completion.ext _ P.uniformSpace _ _ _ _ _ e.continuous completedTensorComparison.continuous
    intro z
    exact (TopologicalModuleStructure.completionEquiv_incl h z).trans
      (completedTensorComparison_incl z).symm

end Comparison

section Characterization

variable (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [PolynormableSpace ℂ E]

/-- The local operator condition on balanced convex zero-neighborhoods. -/
def HasNuclearLocalTransitions : Prop :=
  ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
    ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
      Nonempty (BanachNuclearExpansion (localBanachTransition
        (neighborhoodGauge hU bU cU) (neighborhoodGauge hV bV cV) (neighborhoodGauge_mono hVU)))

/-- The local operator condition written as the null-sequence series
(C.2.4.2) in the manuscript. -/
theorem hasNuclearLocalTransitions_iff_null_series :
    HasNuclearLocalTransitions E ↔
      ∀ (U : Set E) (hU : U ∈ 𝓝 0) (bU : Balanced ℂ U) (cU : Convex ℝ U),
        ∃ (V : Set E) (hV : V ∈ 𝓝 0) (bV : Balanced ℂ V) (cV : Convex ℝ V) (hVU : V ⊆ U),
          let p := neighborhoodGauge hV bV cV
          let q := neighborhoodGauge hU bU cU
          let T := localBanachTransition q p (neighborhoodGauge_mono hVU)
          ∃ (c : ℕ → ℂ) (f : ℕ → LocalBanach p →L[ℂ] ℂ) (w : ℕ → LocalBanach q),
            Summable (fun n => ‖c n‖) ∧ Tendsto f atTop (𝓝 0) ∧ Tendsto w atTop (𝓝 0) ∧
              ∀ x, HasSum (fun n => (c n * f n x) • w n) (T x) := by
  constructor
  · intro h U hU bU cU
    obtain ⟨V, hV, bV, cV, hVU, hT⟩ := h U hU bU cU
    exact ⟨V, hV, bV, cV, hVU, BanachNuclearExpansion.nonempty_iff_null_series.mp hT⟩
  · intro h U hU bU cU
    obtain ⟨V, hV, bV, cV, hVU, hT⟩ := h U hU bU cU
    exact ⟨V, hV, bV, cV, hVU, BanachNuclearExpansion.nonempty_iff_null_series.mpr hT⟩

/-- The completed tensor comparison is a continuous linear isomorphism. -/
def IsCompletedTensorIso (F : Type (max u v)) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [PolynormableSpace ℂ F] : Prop :=
  ∃ e : (projectiveTensorModuleStructure E F).Completed ≃L[ℂ] (injectiveTensorStructure E F).Completed,
    e.toContinuousLinearMap = completedTensorComparison

/-- Theorem C.2.4.2. Nuclearity is equivalent to the local Banach transition
criterion and to each of the two completed tensor comparison criteria. -/
theorem nuclearLocallyConvex_characterizations [T2Space E] :
    (NuclearLocallyConvex.{max u v, u} E ↔ HasNuclearLocalTransitions E) ∧
    (NuclearLocallyConvex.{max u v, u} E ↔
      ∀ (F : Type (max u v)) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F],
        letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
        IsCompletedTensorIso E F) ∧
    (NuclearLocallyConvex.{max u v, u} E ↔
      ∀ (F : Type (max u v)) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
        [T2Space F] [PolynormableSpace ℂ F], IsCompletedTensorIso E F) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h U hU bU cU
    obtain ⟨V, hV, bV, cV, hVU, _, f, w, hn, hs⟩ :=
      nuclearLocallyConvex_exists_rankOneLocalBanach h U hU bU cU
    exact ⟨V, hV, bV, cV, hVU, BanachNuclearExpansion.nonempty_of_rankOne_hasSum f w hn hs⟩
  · intro h
    apply nuclearLocallyConvex_iff_integralLocalBanach.mpr
    intro U hU bU cU
    obtain ⟨V, hV, bV, cV, hVU, ⟨R⟩⟩ := h U hU bU cU
    refine ⟨V, hV, bV, cV, hVU, isIntegralOperator_of_rankOne_hasSum
      (fun n => R.coeff n • R.functional n) R.vector ?_ ?_⟩
    · apply R.coeff_summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      intro n
      rw [norm_smul, mul_assoc]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (by simpa using mul_le_mul (R.functional_bound n) (R.vector_bound n) (norm_nonneg _) zero_le_one)
    · have hf (n : ℕ) :
          (R.coeff n • R.functional n).smulRight (R.vector n) =
            R.coeff n • (R.functional n).smulRight (R.vector n) := by
        ext x
        simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, mul_smul]
      simpa only [hf] using R.hasSum
  · intro h F _ _ _
    letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
    exact completedTensorComparison_iff.mpr (h.2.2 F)
  · intro h
    apply nuclearLocallyConvex_of_integralTransition
    apply exists_integralTransition_of_banach_tensor_topologies.{u, v}
    intro F _ _ _
    letI : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
    exact completedTensorComparison_iff.mp (h F)
  · intro h F _ _ _ _ _
    exact completedTensorComparison_iff.mpr (h.2.2 F)
  · intro h
    refine ⟨inferInstance, inferInstance, fun F _ _ _ _ _ => ?_⟩
    exact completedTensorComparison_iff.mp (h F)

end Characterization


/-- Example C.1.5.10. In a nuclear space, each continuous seminorm has a
zero-neighborhood with relatively compact image in its local Banach space.
The proof uses the compact gauge transition, as in original commit 8ef3cde. -/
theorem nuclearLocallyConvex_schwartz {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : NuclearLocallyConvex.{max u v, u} E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ U ∈ 𝓝 (0 : E), IsCompact (closure (localBanachDenseMap q '' U)) := by
  letI : PolynormableSpace ℂ E := hE.2.1
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  obtain ⟨p, hp, hqp, ι, f, w, _, hsum⟩ := nuclearLocallyConvex_exists_rankOneTransition hE q hq
  have hcompact : IsCompactOperator (localBanachTransition q p hqp) := by
    apply isCompactOperator_of_tendsto hsum
    apply Eventually.of_forall
    intro S
    classical
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact isCompactOperator_zero
    | insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact ((isCompactOperator_of_locallyCompactSpace_dom (f j)).clm_comp
        ((ContinuousLinearMap.id ℂ ℂ).smulRight (w j))).add ih
  have h := hcompact.comp_clm (localBanachMap p hp)
  obtain ⟨U, hU, hK⟩ := (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mp h
  refine ⟨U, hU, ?_⟩
  convert hK using 3
  exact (localBanachTransition_denseMap q p hqp _).symm

/-- A first-countable nuclear locally convex space is separable. Each
continuous seminorm has a separable local Banach space, and a countable
neighborhood basis only requires countably many such seminorms. -/
theorem nuclearLocallyConvex_separable_of_firstCountable {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [FirstCountableTopology E]
    (hE : NuclearLocallyConvex.{max u v, u} E) : SeparableSpace E := by
  classical
  letI : PolynormableSpace ℂ E := hE.2.1
  let hw := PolynormableSpace.withSeminorms ℂ E
  letI := hw.topologicalAddGroup
  letI := hw.continuousSMul
  have hsep (q : Seminorm ℂ E) (hq : Continuous q) : SeparableSpace (LocalBanach q) := by
    obtain ⟨U, hU, hK⟩ := nuclearLocallyConvex_schwartz hE q hq
    have hspan : Submodule.span ℂ U = ⊤ :=
      ((absorbent_nhds_zero (𝕜 := ℂ) hU).mono (Submodule.subset_span (R := ℂ))).submodule_eq_top
    have hR := (isSeparable_closure.mp hK.isSeparable).span (R := ℂ)
    rw [← Submodule.map_span, hspan, Submodule.map_top] at hR
    exact isSeparable_univ_iff.mp (by
      rw [← (localBanachDenseMap_dense q).closure_range]
      exact isSeparable_closure.mpr hR)
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hex (n : ℕ) :
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∃ r > 0, q.ball 0 r ⊆ U n := by
    obtain ⟨s, r, hr, hs⟩ := (hw.mem_nhds_iff 0 (U n)).mp (hU.mem n)
    exact ⟨s.sup fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.val,
      Seminorm.continuous_finsetSup fun p _ ↦ p.property, r, hr, hs⟩
  choose q hq r hr hsub using hex
  have hd (n : ℕ) : ∃ d : ℕ → E, ∀ x : E, ∃ m, q n (d m - x) < r n := by
    letI := hsep (q n) (hq n)
    let p := localBanachDenseMap (q n)
    let j (x : E) : Set.range p := ⟨p x, Set.mem_range_self x⟩
    letI : Nonempty (Set.range p) := ⟨j 0⟩
    obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (Set.range p)
    choose d h using fun m ↦ (a m).property
    refine ⟨d, fun x ↦ ?_⟩
    obtain ⟨m, hm⟩ := ha.exists_dist_lt (j x) (hr n)
    have he : dist (p (d m)) (p x) < r n := by
      rw [h]
      rw [Subtype.dist_eq, dist_comm] at hm
      exact hm
    rw [dist_eq_norm, ← map_sub, norm_localBanachDenseMap] at he
    exact ⟨m, he⟩
  choose d hd using hd
  refine ⟨Set.range fun k : ℕ × ℕ ↦ d k.1 k.2, Set.countable_range _, ?_⟩
  intro x
  rw [mem_closure_iff_nhds]
  intro V hV
  have hV₀ : (fun y ↦ x + y) ⁻¹' V ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨n, -, hn⟩ := hU.1.mem_iff.mp hV₀
  obtain ⟨m, hm⟩ := hd n x
  have hmem : d n m - x ∈ U n := hsub n (by simpa [Seminorm.mem_ball] using hm)
  exact ⟨d n m, by simpa [add_comm x] using hn hmem, ⟨(n, m), rfl⟩⟩

end

end Masullo
