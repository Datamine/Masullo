/-
The product and Baire arguments adapt RiemannMasullo's
ForMathlib/Analysis/Normed/Module/Seminorm/Pi.lean at a7b1173a562c5c6b1ed3dad4ca8bb7ca5de64452
and AppC_LCTVS/Sec2a_part2.lean at a0dc549ec3ffa52882b705f89d500e7ab8fe5074
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import InductiveTensorLimitTopology

open Filter Function Set Topology TopologicalSpace UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
  [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]

private theorem productSeminorm_finiteCoordinates (p : Seminorm ℂ (∀ i, X i))
    (hp : Continuous p) :
    ∃ s : Finset I, ∀ x, (∀ i ∈ s, x i = 0) → p x = 0 := by
  have hU := p.ball_mem_nhds hp one_pos
  rw [nhds_pi] at hU
  obtain ⟨s, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
  refine ⟨s, fun x hx => ?_⟩
  by_contra h
  have hxpos := lt_of_le_of_ne (apply_nonneg p x) (Ne.symm h)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℂ ((p x)⁻¹)
  have hcx : c • x ∈ p.ball 0 1 := hsub fun i hi => by
    change c • x i ∈ W i
    rw [hx i hi, smul_zero]
    exact mem_of_mem_nhds (hW i)
  have hlt := p.mem_ball_zero.mp hcx
  rw [map_smul_eq_mul, ← lt_div_iff₀ hxpos, one_div] at hlt
  exact hlt.asymm hc

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [BaireSpace F]

/-- Separate continuity against a Baire factor gives a common finite set of
product coordinates on which the tensor seminorm depends. -/
theorem inductiveTensorTest_finiteCoordinates (p : InductiveTensorTest (∀ i, X i) F) :
    ∃ s : Finset I, ∀ x : ∀ i, X i, (∀ i ∈ s, x i = 0) →
      ∀ y : F, p.tensor (x ⊗ₜ[ℂ] y) = 0 := by
  classical
  let A : Set I := {i | ∃ (a : X i) (b : F), p.tensor (Pi.single i a ⊗ₜ[ℂ] b) ≠ 0}
  let r (y : F) := p.tensor.comp ((TensorProduct.mk ℂ (∀ i, X i) F).flip y)
  choose s hs using fun y => productSeminorm_finiteCoordinates (r y) (p.first y)
  have hfinite : A.Finite := by
    by_contra hinf
    let k := Set.Infinite.natEmbedding A hinf
    choose a b hn using fun n : ℕ => (k n).property
    let q (n : ℕ) := p.tensor.comp (TensorProduct.mk ℂ _ F (Pi.single (k n).val (a n)))
    let φ (n : ℕ) := localBanachMap (q n) (p.second _)
    let K (n : ℕ) := (φ n).ker
    letI : NeBot (𝓝[{c : ℂ | IsUnit c}] 0) := NormedField.nhdsWithin_isUnit_neBot
    have hd (n : ℕ) : Dense (K n : Set F)ᶜ := by
      rw [← interior_eq_empty_iff_dense_compl]
      by_contra h
      have htop := (K n).eq_top_of_nonempty_interior' (nonempty_iff_ne_empty.mpr h)
      have hz : b n ∈ K n := htop.symm ▸ Submodule.mem_top
      have he : φ n (b n) = 0 := LinearMap.mem_ker.mp hz
      apply hn n
      change q n (b n) = 0
      rw [← norm_localBanachDenseMap, show localBanachDenseMap (q n) (b n) = φ n (b n) from rfl,
        he, norm_zero]
    obtain ⟨y, hy⟩ := (dense_iInter_of_isOpen_nat (fun n => (φ n).isClosed_ker.isOpen_compl) hd).nonempty
    have hmem (n : ℕ) : (k n).val ∈ s y := by
      by_contra h
      have hzero := hs y (Pi.single (k n).val (a n)) fun i hi =>
        Pi.single_eq_of_ne (fun (he : i = (k n).val) => h (he ▸ hi)) _
      have hnorm : ‖φ n y‖ = r y (Pi.single (k n).val (a n)) :=
        norm_localBanachDenseMap (q n) y
      have hz : φ n y = 0 := norm_eq_zero.mp (hnorm.trans hzero)
      exact (mem_iInter.mp hy n) (LinearMap.mem_ker.mpr hz)
    let emb : ℕ ↪ I := k.trans (Function.Embedding.subtype _)
    exact Set.infinite_range_of_injective emb.injective
      ((s y).finite_toSet.subset (range_subset_iff.mpr hmem))
  refine ⟨hfinite.toFinset, fun x hx y => ?_⟩
  let z : ∀ i, X i := ∑ i ∈ s y, Pi.single i (x i)
  have hdiff : r y (x - z) = 0 := hs y _ fun i hi => by
    simp only [z, Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem i hi, Pi.single_eq_same, sub_self]
    exact fun j _ hj => Pi.single_eq_of_ne hj.symm _
  have hz : r y z ≤ 0 := by
    apply (Finset.le_sum_of_subadditive (r y) (map_zero _).le (map_add_le_add _) (s y)
      (fun i => Pi.single i (x i))).trans
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : i ∈ A
    · simp [hx i (hfinite.mem_toFinset.mpr hi)]
    · exact le_of_eq (not_ne_iff.mp fun hn => hi ⟨x i, y, hn⟩)
  have hle := map_add_le_add (r y) (x-z) z
  rw [sub_add_cancel, hdiff, zero_add] at hle
  exact le_antisymm (hle.trans hz) (apply_nonneg _ _)


end

noncomputable section

variable {I : Type*} (X : I → Type*) (F : Type*)
  [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, IsTopologicalAddGroup (X i)]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]

abbrev productTensorCoordinates :
    ((∀ i, X i) ⊗[ℂ] F) →ₗ[ℂ] (∀ i, X i ⊗[ℂ] F) :=
  LinearMap.pi fun i => TensorProduct.map (LinearMap.proj i) LinearMap.id

/-- For a Baire factor, the coordinate maps induce the uniformity on the
algebraic inductive tensor with a product. -/
theorem productTensorCoordinates_uniformInducing [BaireSpace F] [ContinuousSMul ℂ F] :
    letI : UniformSpace ((∀ i, X i) ⊗[ℂ] F) :=
      (inductiveTensorModuleStructure (∀ i, X i) F).uniformSpace
    letI (i : I) : UniformSpace (X i ⊗[ℂ] F) :=
      (inductiveTensorModuleStructure (X i) F).uniformSpace
    IsUniformInducing (productTensorCoordinates X F) := by
  classical
  let A := (∀ i, X i) ⊗[ℂ] F
  let B (i : I) := X i ⊗[ℂ] F
  let D := inductiveTensorModuleStructure (∀ i, X i) F
  let C (i : I) := inductiveTensorModuleStructure (X i) F
  letI : UniformSpace A := D.uniformSpace
  letI : IsUniformAddGroup A := D.uniformGroup
  letI (i : I) : UniformSpace (B i) := (C i).uniformSpace
  letI (i : I) : IsUniformAddGroup (B i) := (C i).uniformGroup
  let W := inductiveTensor_withSeminorms (E := ∀ i, X i) (F := F)
  let P := productTensorCoordinates X F
  let L (i : I) : B i →ₗ[ℂ] A :=
    TensorProduct.map (LinearMap.single ℂ X i) LinearMap.id
  let f (i : I) : (∀ i, X i) →L[ℂ] X i := ContinuousLinearMap.proj i
  let g (i : I) : X i →L[ℂ] (∀ i, X i) :=
    ⟨LinearMap.single ℂ X i, by
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        exact continuous_id.congr fun a => (Pi.single_eq_same i a).symm
      · exact continuous_const.congr fun a => (Pi.single_eq_of_ne h a).symm⟩
  have hP : Continuous P := continuous_pi fun i =>
    continuous_inductiveTensorStageMap (I := Unit) (J := Unit)
      (fun _ => f i) (fun _ => ContinuousLinearMap.id ℂ F) () ()
  have hL (i : I) : Continuous (L i) :=
    continuous_inductiveTensorStageMap (I := Unit) (J := Unit)
      (fun _ => g i) (fun _ => ContinuousLinearMap.id ℂ F) () ()
  change IsUniformInducing P
  apply AddMonoidHom.isUniformInducing_of_isInducing (f := P.toAddMonoidHom)
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm ((hP.tendsto' 0 0 (map_zero P)).le_comap) ?_
  apply W.hasBasis_zero_ball.ge_iff.mpr
  rintro ⟨t, ε⟩ hε
  let p := t.sup (InductiveTensorTest.tensor (E := ∀ i, X i) (F := F))
  have hp : Continuous p := Seminorm.continuous_finsetSup fun q _ => W.continuous_seminorm q
  let q : InductiveTensorTest (∀ i, X i) F :=
    { tensor := p
      first := fun y =>
        hp.comp ((W.continuous_iff_continuous_comp ((TensorProduct.mk ℂ _ F).flip y)).mpr
          fun r => r.first y)
      second := fun x =>
        hp.comp ((W.continuous_iff_continuous_comp (TensorProduct.mk ℂ _ F x)).mpr
          fun r => r.second x) }
  obtain ⟨s, hs⟩ := inductiveTensorTest_finiteCoordinates q
  let lift : (∀ i, B i) →ₗ[ℂ] A := ∑ i ∈ s, (L i).comp (LinearMap.proj i)
  have hlift : Continuous lift := by
    change Continuous (fun w => lift w)
    simp only [lift, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact continuous_finsetSum _ fun i _ => (hL i).comp (continuous_apply i)
  let R : A →ₗ[ℂ] A := LinearMap.id - lift.comp P
  have hz (z : A) : q.tensor (R z) = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x y =>
      let xs : ∀ i, X i := ∑ i ∈ s, Pi.single i (x i)
      have htail : ∀ i ∈ s, (x - xs) i = 0 := by
        intro i hi
        simp only [Pi.sub_apply, xs, Finset.sum_apply]
        rw [Finset.sum_eq_single_of_mem i hi, Pi.single_eq_same, sub_self]
        exact fun k _ hk => Pi.single_eq_of_ne hk.symm _
      have he : R (x ⊗ₜ[ℂ] y) = (x - xs) ⊗ₜ[ℂ] y := by
        change x ⊗ₜ[ℂ] y - lift (P (x ⊗ₜ[ℂ] y)) = _
        rw [TensorProduct.sub_tmul, sub_right_inj, show xs ⊗ₜ[ℂ] y =
          ∑ i ∈ s, Pi.single i (x i) ⊗ₜ[ℂ] y from TensorProduct.sum_tmul _ _ _]
        simp only [lift, P, L, LinearMap.sum_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, productTensorCoordinates, LinearMap.pi_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [TensorProduct.map_tmul, LinearMap.id_apply]
        rfl
      rw [he]
      exact hs _ htail y
    | add z w hz hw =>
      apply le_antisymm _ (apply_nonneg _ _)
      rw [map_add]
      exact (map_add_le_add q.tensor _ _).trans (by rw [hz, hw, add_zero])
  refine mem_comap.mpr
    ⟨lift ⁻¹' q.tensor.ball 0 ε, (hlift.tendsto' 0 0 (map_zero lift)).eventually
      (q.tensor.ball_mem_nhds (W.continuous_seminorm q) hε), fun z hz' => ?_⟩
  have he : R z + lift (P z) = z := sub_add_cancel _ _
  have hle := map_add_le_add q.tensor (R z) (lift (P z))
  rw [he, hz, zero_add] at hle
  exact q.tensor.mem_ball_zero.mpr (hle.trans_lt (q.tensor.mem_ball_zero.mp hz'))


/-- Completed inductive tensoring with a Baire topological vector space
commutes with arbitrary products, via the canonical coordinate projections. -/
theorem completedInductiveTensor_product_of_baire [BaireSpace F] [ContinuousSMul ℂ F] :
    IsHomeomorph (fun (z : (inductiveTensorModuleStructure (∀ i, X i) F).Completed) i =>
      completedInductiveTensor_map (ContinuousLinearMap.proj i : (∀ i, X i) →L[ℂ] X i)
        (ContinuousLinearMap.id ℂ F) z) := by
  classical
  let A := (∀ i, X i) ⊗[ℂ] F
  let B (i : I) := X i ⊗[ℂ] F
  let D := inductiveTensorModuleStructure (∀ i, X i) F
  let C (i : I) := inductiveTensorModuleStructure (X i) F
  letI : UniformSpace A := D.uniformSpace
  letI (i : I) : UniformSpace (B i) := (C i).uniformSpace
  let P := productTensorCoordinates X F
  have hP : IsUniformInducing P := productTensorCoordinates_uniformInducing X F
  have hd : DenseRange P := by
    intro w
    apply mem_closure_iff_nhds.mpr
    intro U hU
    rw [nhds_pi] at hU
    obtain ⟨s, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
    let L (i : I) : B i →ₗ[ℂ] A :=
      (LinearMap.single ℂ X i).rTensor F
    let z : A := ∑ i ∈ s, L i (w i)
    refine ⟨P z, hsub (fun i hi => ?_), z, rfl⟩
    suffices he : P z i = w i by
      rw [he]
      exact mem_of_mem_nhds (hW i)
    let proj := LinearMap.proj (R := ℂ) (φ := X)
    have hc (i j : I) : P (L j (w j)) i =
        ((proj i).comp (LinearMap.single ℂ X j)).rTensor F (w j) := by
      change (proj i).rTensor F ((LinearMap.single ℂ X j).rTensor F (w j)) = _
      exact (LinearMap.rTensor_comp_apply F _ _ _).symm
    simp only [z, map_sum, Finset.sum_apply, hc]
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [proj, LinearMap.proj_comp_single_same]
    · intro j _ hj
      simp [proj, LinearMap.proj_comp_single_ne ℂ X _ _ hj.symm]
  let Q (w : ∀ i, B i) (i : I) : (C i).Completed := (C i).incl (w i)
  have hQ : IsUniformInducing Q := by
    have h (i : I) := (Completion.isUniformInducing_coe (α := B i)).comap_uniformity
    rw [isUniformInducing_iff, Pi.uniformity, Filter.comap_iInf, Pi.uniformity]
    simp_rw [Filter.comap_comap, ← h, Filter.comap_comap]
    rfl
  letI (i : I) : CompleteSpace ((C i).Completed) :=
    @Completion.completeSpace (B i) (C i).uniformSpace
  letI (i : I) : T0Space ((C i).Completed) := Completion.t0Space (B i)
  let pkg : AbstractCompletion A :=
    { space := ∀ i, (C i).Completed
      coe := Q ∘ P
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hQ.comp hP
      dense := (DenseRange.piMap fun i => Completion.denseRange_coe (α := B i)).comp hd
        hQ.uniformContinuous.continuous }
  let e : D.Completed ≃ᵤ (∀ i, (C i).Completed) := Completion.cPkg.compareEquiv pkg
  let T (i : I) := completedInductiveTensor_map
    (ContinuousLinearMap.proj i : (∀ i, X i) →L[ℂ] X i) (ContinuousLinearMap.id ℂ F)
  have he : (fun (z : D.Completed) i => T i z) = e := by
    refine Completion.ext (continuous_pi fun i => (T i).continuous) e.continuous fun z => ?_
    change (fun i => T i (D.incl z)) = Completion.cPkg.compare pkg (Completion.cPkg.coe z)
    rw [AbstractCompletion.compare_coe]
    funext i
    exact completedInductiveTensor_map_incl
      (ContinuousLinearMap.proj i : (∀ i, X i) →L[ℂ] X i) (ContinuousLinearMap.id ℂ F) z
  change IsHomeomorph (fun (z : D.Completed) i => T i z)
  rw [he]
  exact e.toHomeomorph.isHomeomorph

omit [IsTopologicalAddGroup F] in
/-- Proposition C.2.3.13(1). The canonical map on completions is a linear
topological isomorphism when the fixed factor is Fréchet. -/
theorem exists_completedInductiveTensor_productEquiv (hF : IsFrechetTVS F) :
    letI : IsTopologicalAddGroup F := hF.choose
    ∃ L : (inductiveTensorModuleStructure (∀ i, X i) F).Completed
        ≃L[ℂ] (∀ i, (inductiveTensorModuleStructure (X i) F).Completed),
      ∀ z i, L z i = completedInductiveTensor_map
        (ContinuousLinearMap.proj i : (∀ i, X i) →L[ℂ] X i)
        (ContinuousLinearMap.id ℂ F) z := by
  letI : IsTopologicalAddGroup F := hF.choose
  letI : PolynormableSpace ℂ F := hF.choose_spec.1
  letI : MetrizableSpace F := hF.choose_spec.2.1
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace F := hF.choose_spec.2.2
  letI : ContinuousSMul ℂ F := (PolynormableSpace.withSeminorms ℂ F).continuousSMul
  haveI : (uniformity F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  letI : BaireSpace F := BaireSpace.of_completelyPseudoMetrizable
  let q := ContinuousLinearMap.pi (fun i => completedInductiveTensor_map
    (ContinuousLinearMap.proj i : (∀ i, X i) →L[ℂ] X i)
    (ContinuousLinearMap.id ℂ F))
  have hq : IsHomeomorph q := completedInductiveTensor_product_of_baire X F
  let e := LinearEquiv.ofBijective q.toLinearMap hq.bijective
  let L : (inductiveTensorModuleStructure (∀ i, X i) F).Completed
      ≃L[ℂ] (∀ i, (inductiveTensorModuleStructure (X i) F).Completed) :=
    ⟨e, q.continuous, by
      have he : IsHomeomorph e := hq
      let H := IsHomeomorph.homeomorph e he
      have hEq : H.toEquiv = e.toEquiv := Equiv.ext fun _ => rfl
      have hc : Continuous H.toEquiv.symm := H.symm.continuous
      rw [hEq] at hc
      exact hc⟩
  exact ⟨L, fun _ _ => rfl⟩

end
end Masullo
