import StrongDualBoundedSeries
import CompletedProjectiveTensorSums
import NuclearApproximation
import ProjectiveTensorTopology

/-!
# Nuclearity of the strong dual of a nuclear Fréchet space

The bounded inclusion and series arguments adapt the Apache-2.0 original
proof of Lemma C.2.4.11 in `RiemannMasullo/AppC_LCTVS/Sec2b.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`.
-/

open Bornology Filter Function Set Topology UniformSpace
open scoped BoundedContinuousFunction NNReal PointwiseConvergenceCLM TensorProduct

namespace Masullo

noncomputable section

open InjectiveTensorTools

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

private def restrictDualToBounded [TopologicalSpace E] (B : Set E) (hB : IsVonNBounded ℂ B) :
    StrongDual ℂ E →ₗ[ℂ] (B →ᵇ ℂ) where
  toFun f := by
    let h := (NormedSpace.isVonNBounded_iff' ℂ).mp (hB.image f)
    exact BoundedContinuousFunction.ofNormedAddCommGroup (fun x : B ↦ f x)
      (f.continuous.comp continuous_subtype_val) h.choose
      (fun x ↦ h.choose_spec _ ⟨x, x.property, rfl⟩)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private def evalBoundedTensor [TopologicalSpace E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] {B : Set E} (b : B) :
    letI : TopologicalSpace (E ⊗[ℂ] (B →ᵇ ℂ)) := projectiveTensorTopology E (B →ᵇ ℂ)
    (E ⊗[ℂ] (B →ᵇ ℂ)) →L[ℂ] E := by
  let Y := B →ᵇ ℂ
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  letI : TopologicalSpace (E ⊗[ℂ] Y) := projectiveTensorTopology E Y
  let L := LinearMap.mk₂ ℂ (fun (x : E) (f : Y) ↦ f b • x)
    (fun _ _ _ ↦ smul_add _ _ _) (fun _ _ _ ↦ smul_comm _ _ _)
    (fun _ _ _ ↦ add_smul _ _ _) (fun _ _ _ ↦ mul_smul _ _ _)
  refine ⟨TensorProduct.lift L, continuous_projectiveTensor_lift L ?_⟩
  exact ((BoundedContinuousFunction.evalCLM ℂ b).continuous.comp
    (continuous_snd : Continuous (Prod.snd : E × Y → Y))).smul continuous_fst

private def projectiveCompletionInclusion {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] :
    let D := projectiveTensorModuleStructure X Y
    letI : UniformSpace (X ⊗[ℂ] Y) := D.uniformSpace
    (X ⊗[ℂ] Y) →L[ℂ] D.Completed := by
  let T := X ⊗[ℂ] Y
  let D := projectiveTensorModuleStructure X Y
  letI : UniformSpace T := D.uniformSpace
  letI : IsUniformAddGroup T := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ T := D.uniformConstSmul
  exact ⟨{ toFun := D.incl
           map_add' := Completion.coe_add
           map_smul' := Completion.coe_smul }, Completion.continuous_coe T⟩

private def evalCompletedBoundedTensor [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    {B : Set E} (b : B) : (projectiveTensorModuleStructure E (B →ᵇ ℂ)).Completed →L[ℂ] E := by
  let T := E ⊗[ℂ] (B →ᵇ ℂ)
  let D := projectiveTensorModuleStructure E (B →ᵇ ℂ)
  letI : UniformSpace T := D.uniformSpace
  letI : IsUniformAddGroup T := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ T := D.uniformConstSmul
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : ContinuousConstSMul ℂ D.Completed :=
    ⟨fun c ↦ (Completion.uniformContinuous_map (f := fun z : T ↦ c • z)).continuous⟩
  exact (evalBoundedTensor b).extend projectiveCompletionInclusion

private theorem evalCompletedBoundedTensor_incl [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    {B : Set E} (b : B) (z : E ⊗[ℂ] (B →ᵇ ℂ)) :
    evalCompletedBoundedTensor b ((projectiveTensorModuleStructure E (B →ᵇ ℂ)).incl z) =
      evalBoundedTensor b z := by
  let T := E ⊗[ℂ] (B →ᵇ ℂ)
  let D := projectiveTensorModuleStructure E (B →ᵇ ℂ)
  letI : UniformSpace T := D.uniformSpace
  letI : IsUniformAddGroup T := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ T := D.uniformConstSmul
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : ContinuousConstSMul ℂ D.Completed :=
    ⟨fun c ↦ (Completion.uniformContinuous_map (f := fun z : T ↦ c • z)).continuous⟩
  unfold evalCompletedBoundedTensor
  change (_ : _ →L[ℂ] E) (projectiveCompletionInclusion z) = _
  apply ContinuousLinearMap.extend_eq
  · exact Completion.denseRange_coe
  · exact Completion.isUniformInducing_coe _

set_option maxHeartbeats 1600000 in
private theorem exists_tensor_of_bounded_inclusion [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    [FirstCountableTopology E] [CompleteSpace E] (hN : NuclearLocallyConvex.{u, u} E)
    (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ w : (projectiveTensorModuleStructure E (B →ᵇ ℂ)).Completed, ∀ b : B,
      evalCompletedBoundedTensor b w = (b : E) := by
  classical
  let Y := B →ᵇ ℂ
  let T := E ⊗[ℂ] Y
  let D := projectiveTensorModuleStructure E Y
  letI : UniformSpace T := D.uniformSpace
  letI : IsUniformAddGroup T := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ T := D.uniformConstSmul
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let lift := (TensorProduct.map LinearMap.id (restrictDualToBounded B hB)).comp
    (TensorProduct.comm ℂ (StrongDual ℂ E) E).toLinearMap
  have hEval (z : StrongDual ℂ E ⊗[ℂ] E) (b : B) :
      evalBoundedTensor b (lift z) = tensorOperator E E z b := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul f x => rfl
    | add z w hz hw =>
      simp only [map_add, add_apply, hz, hw]
  let contract (φ : E →Lₚₜ[ℂ] ℂ) : T →ₗ[ℂ] Y :=
    (TensorProduct.lid ℂ Y).toLinearMap.comp (φ.toLinearMap.rTensor Y)
  have hPair (φ : E →Lₚₜ[ℂ] ℂ) (ψ : Y →Lₚₜ[ℂ] ℂ) (z : T) :
      dualPair φ ψ z = ψ (contract φ z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x g =>
      rw [dualPair_tmul]
      change φ x * ψ g = ψ (φ x • g)
      rw [map_smul]
      rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  have hContract (φ : E →Lₚₜ[ℂ] ℂ) (z : T) (b : B) :
      contract φ z b = φ (evalBoundedTensor b z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | tmul x g =>
      change φ x * g b = φ (g b • x)
      rw [map_smul, smul_eq_mul, mul_comm]
    | add z w hz hw =>
      simp only [map_add]
      change contract φ z b + contract φ w b = _
      rw [hz, hw]
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  choose z hz using fun n ↦ nuclearLocallyConvex_approxOn_bounded hN hB
    (hU.1.mem_of_mem (i := n) trivial)
  let a (n : ℕ) : T := lift (z n)
  have hCa : CauchySeq a := by
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero T, tendsto_comap_iff]
    change Tendsto (fun p : ℕ × ℕ ↦ a p.2 - a p.1) (atTop ×ˢ atTop)
      (@nhds T (projectiveTensorTopology E Y) 0)
    rw [hN.2.2 Y]
    letI : TopologicalSpace T := injectiveTensorTopology E Y
    have hW : WithSeminorms (injectiveTensorSeminorm (E := E) (F := Y)) :=
      injectiveTensor_withSeminorms
    exact (hW.tendsto_nhds _ _).mpr (by
      intro I ε hε
      let P := injectiveAsProjectiveTest I
      obtain ⟨s, C, _, hs⟩ :=
        Seminorm.bound_of_continuous (norm_withSeminorms ℂ Y) P.second P.second_continuous
      have hC (y : Y) : P.second y ≤ (C : ℝ) * ‖y‖ :=
        (hs y).trans (mul_le_mul_of_nonneg_left
          ((Finset.sup_le (fun _ _ ↦ le_rfl :
            ∀ i ∈ s, normSeminorm ℂ Y ≤ normSeminorm ℂ Y)) y) C.coe_nonneg)
      let δ := ε / (4 * ((C : ℝ) + 1))
      have hδ : 0 < δ := by positivity
      obtain ⟨m, _, hm⟩ := hU.1.mem_iff.mp (P.first.ball_mem_nhds P.first_continuous hδ)
      have htail : ∀ᶠ p : ℕ × ℕ in atTop ×ˢ atTop, m ≤ p.1 ∧ m ≤ p.2 :=
        (eventually_ge_atTop m).prod_mk (eventually_ge_atTop m)
      filter_upwards [htail] with p hp
      rw [sub_zero]
      refine lt_of_le_of_lt (injectiveTensorSeminorm_le I.1 I.2 _ (r := (C : ℝ) * (δ + δ))
        (mul_nonneg C.coe_nonneg (add_nonneg hδ.le hδ.le)) ?_) ?_
      · intro φ hφ ψ hψ
        rw [hPair]
        refine ((dualTestSeminorm_dom I.2 ⟨ψ, hψ⟩ _).trans (hC _)).trans
          (mul_le_mul_of_nonneg_left ((BoundedContinuousFunction.norm_le (add_nonneg hδ.le hδ.le)).mpr
            fun b ↦ ?_) C.coe_nonneg)
        rw [hContract, map_sub, hEval, hEval]
        rw [show tensorOperator E E (z p.2) b - tensorOperator E E (z p.1) b =
            (tensorOperator E E (z p.2) b - b.val) - (tensorOperator E E (z p.1) b - b.val) by abel]
        have he (n : ℕ) (hn : m ≤ n) :
            ‖φ (tensorOperator E E (z n) b - b.val)‖ ≤ δ :=
          (dualTestSeminorm_dom I.1 ⟨φ, hφ⟩ _).trans
            ((P.first.mem_ball_zero.mp (hm (hU.antitone hn (hz n b b.property)))).le)
        rw [map_sub]
        exact (norm_sub_le _ _).trans (add_le_add (he _ hp.2) (he _ hp.1))
      · dsimp only [δ]
        rw [← add_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg C.coe_nonneg hε.le])
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    ((Completion.uniformContinuous_coe T).comp_cauchySeq hCa)
  refine ⟨w, fun b ↦ ?_⟩
  have hx : Tendsto (fun n ↦ tensorOperator E E (z n) b - (b : E)) atTop (𝓝 0) :=
    hU.1.tendsto_right_iff.mpr fun m _ ↦ (eventually_ge_atTop m).mono
      (fun n hn ↦ hU.antitone hn (hz n b b.property))
  have hx' : Tendsto (fun n ↦ tensorOperator E E (z n) b) atTop (𝓝 (b : E)) := by
    simpa only [sub_add_cancel, zero_add] using
      hx.add (tendsto_const_nhds (x := (b : E)) (f := atTop))
  refine tendsto_nhds_unique (((evalCompletedBoundedTensor b).continuous.tendsto w).comp hw)
    (hx'.congr fun n ↦ ?_)
  change _ = evalCompletedBoundedTensor b (D.incl (a n))
  rw [evalCompletedBoundedTensor_incl]
  exact (hEval (z n) b).symm

/-- Each bounded set in a nuclear Fréchet space is covered by the series with
coefficients in the unit disk of one absolutely weighted bounded sequence. -/
theorem bounded_series_cover_of_nuclear_frechet [TopologicalSpace E] (hE : IsFrechetTVS E)
    (hN : NuclearLocallyConvex.{u, u} E) (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E), Summable (fun k ↦ ‖c k‖) ∧ IsVonNBounded ℂ (range x) ∧
      ∀ y ∈ B, ∃ a : ℕ → ℂ, (∀ k, ‖a k‖ ≤ 1) ∧ HasSum (fun k ↦ (c k * a k) • x k) y := by
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ := hE
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : T2Space E := hN.1
  let Y := B →ᵇ ℂ
  letI : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  obtain ⟨z, hz⟩ := exists_tensor_of_bounded_inclusion hN B hB
  obtain ⟨c, x, g, hc, hx, hg, hs⟩ := completedProjectiveTensor_exists_series z
  obtain ⟨M, hM⟩ := (show Tendsto (fun n ↦ ‖g n‖) atTop (𝓝 0) by simpa using hg.norm).bddAbove_range
  let k : ℂ := (max 1 M : ℝ)
  have hk : 0 < max 1 M := zero_lt_one.trans_le (le_max_left _ _)
  have hnorm : ‖k‖ = max 1 M := Complex.norm_of_nonneg hk.le
  have hk0 : k ≠ 0 := norm_pos_iff.mp (hnorm ▸ hk)
  refine ⟨c, fun n ↦ k • x n, hc, ?_, fun y hy ↦ ?_⟩
  · apply Filter.Tendsto.isVonNBounded_range ℂ (x := 0)
    simpa using hx.const_smul k
  · let b : B := ⟨y, hy⟩
    refine ⟨fun n ↦ g n b / k, fun n ↦ ?_, ?_⟩
    · rw [norm_div, hnorm, div_le_one hk]
      exact ((g n).norm_coe_le_norm b).trans ((hM (mem_range_self n)).trans (le_max_right _ _))
    · let D := projectiveTensorModuleStructure E Y
      letI : UniformSpace (E ⊗[ℂ] Y) := D.uniformSpace
      letI : IsUniformAddGroup (E ⊗[ℂ] Y) := D.uniformGroup
      letI : UniformContinuousConstSMul ℂ (E ⊗[ℂ] Y) := D.uniformConstSmul
      let ev := evalCompletedBoundedTensor b
      rw [← show ev z = y from hz b]
      refine (ev.hasSum hs).congr_fun fun n ↦ ?_
      change (c n * (g n b / k)) • k • x n =
        ev (D.incl (c n • (x n ⊗ₜ[ℂ] g n)))
      dsimp only [ev]
      rw [evalCompletedBoundedTensor_incl, map_smul]
      change _ = c n • g n b • x n
      simp only [smul_smul, mul_assoc, div_mul_cancel₀ _ hk0]

/-- Forward implication of Lemma C.2.4.11. -/
theorem strongDual_nuclear_of_nuclear_frechet [TopologicalSpace E] (hE : IsFrechetTVS E)
    (hN : NuclearLocallyConvex.{u, u} E) : NuclearLocallyConvex.{v, u} (StrongDual ℂ E) := by
  letI : IsTopologicalAddGroup E := hE.choose
  letI : PolynormableSpace ℂ E := hE.choose_spec.1
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  exact strongDual_nuclear_of_bounded_series_cover (bounded_series_cover_of_nuclear_frechet hE hN)

end

end Masullo
