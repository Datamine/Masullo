import FinestNuclear
import InductiveTensorTopology
import NormedTensorLimits

open Function Module Set Topology
open scoped TensorProduct

namespace Masullo

noncomputable section

variable {I J E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

theorem finest_projectiveTensorTopology (b : Basis I ℂ E) (c : Basis J ℂ F)
    (i : I ↪ ℕ) (j : J ↪ ℕ) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    letI : TopologicalSpace F := finestLocallyConvexTopology F
    projectiveTensorTopology E F = finestLocallyConvexTopology (E ⊗[ℂ] F) := by
  classical
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  letI : TopologicalSpace F := finestLocallyConvexTopology F
  let T := E ⊗[ℂ] F
  let π := projectiveTensorTopology E F
  let τ := finestLocallyConvexTopology T
  let Wπ := projectiveTensor_withSeminorms (E := E) (F := F)
  let Wτ := finest_withSeminorms T
  have hq (Q : Seminorm ℂ T) : Continuous[π, inferInstance] Q := by
    letI : TopologicalSpace T := π
    let a (m n : ℕ) : ℝ := Function.extend i
      (fun u => Function.extend j (fun v => Q (b u ⊗ₜ[ℂ] c v)) (fun _ => 0) n) (fun _ => 0) m
    obtain ⟨u, v, hu, hv, h⟩ := exists_positive_separate_weights a
    let w (k : I) : ℂ := ↑(u (i k))
    let w' (l : J) : ℂ := ↑(v (j l))
    have hb (k : I) (l : J) : Q (b k ⊗ₜ[ℂ] c l) ≤ ‖w k‖ * ‖w' l‖ := by
      change _ ≤ ‖(↑(u (i k)) : ℂ)‖ * ‖(↑(v (j l)) : ℂ)‖
      rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hu _).le,
        Real.norm_of_nonneg (hv _).le]
      simpa [a, i.injective.extend_apply, j.injective.extend_apply] using h (i k) (j l)
    let p := (weightedLoneSeminorm w).comp b.repr.toLinearMap
    let r := (weightedLoneSeminorm w').comp c.repr.toLinearMap
    have hleft (x : E) (l : J) : Q (x ⊗ₜ[ℂ] c l) ≤ ‖w' l‖ * p x := by
      let R := (Q.comp ((TensorProduct.mk ℂ E F).flip (c l))).comp b.repr.symm.toLinearMap
      have hR (k : I) : R (Finsupp.single k 1) ≤ ‖w' l‖ * ‖w k‖ := by
        change Q (b.repr.symm (Finsupp.single k 1) ⊗ₜ[ℂ] c l) ≤ _
        rw [b.repr_symm_single, one_smul, mul_comm]
        exact hb k l
      have hh := finsupp_seminorm_le_mul_weightedLone R w _ hR (b.repr x)
      change Q (x ⊗ₜ[ℂ] c l) ≤ ‖w' l‖ * ‖weightedLone w (b.repr x)‖
      simpa only [R, Seminorm.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.flip_apply, TensorProduct.mk_apply] using hh
    let P : ProjectiveTensorTest E F := ⟨Q, p, r,
      (finest_withSeminorms E).continuous_seminorm p, (finest_withSeminorms F).continuous_seminorm r,
      fun x y => by
        let S := (Q.comp (TensorProduct.mk ℂ E F x)).comp c.repr.symm.toLinearMap
        have hS (l : J) : S (Finsupp.single l 1) ≤ p x * ‖w' l‖ := by
          change Q (x ⊗ₜ[ℂ] c.repr.symm (Finsupp.single l 1)) ≤ _
          rw [c.repr_symm_single, one_smul, mul_comm]
          exact hleft x l
        have hh := finsupp_seminorm_le_mul_weightedLone S w' _ hS (c.repr y)
        change Q (x ⊗ₜ[ℂ] y) ≤ p x * ‖weightedLone w' (c.repr y)‖
        change Q (x ⊗ₜ[ℂ] c.repr.symm (c.repr y)) ≤ _ at hh
        rwa [LinearEquiv.symm_apply_apply] at hh⟩
    exact Wπ.continuous_seminorm P
  have forward : Continuous[π, τ] (id : T → T) := by
    letI : TopologicalSpace T := π
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ T T
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ π Wπ.topologicalAddGroup τ Wτ LinearMap.id).mpr hq
  have back : Continuous[τ, π] (id : T → T) := by
    letI : TopologicalSpace T := τ
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ T T
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ τ Wτ.topologicalAddGroup π Wπ LinearMap.id).mpr
      (fun P => Wτ.continuous_seminorm P.tensor)
  exact le_antisymm (continuous_id_iff_le.mp forward) (continuous_id_iff_le.mp back)

/-- Lemma C.2.5.2. The three algebraic tensor topologies of two countably
generated finest spaces are finest, and their common uniformity is complete. -/
theorem finest_tensor_topologies (b : Basis I ℂ E) (c : Basis J ℂ F)
    (i : I ↪ ℕ) (j : J ↪ ℕ) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    letI : TopologicalSpace F := finestLocallyConvexTopology F
    let τ := finestLocallyConvexTopology (E ⊗[ℂ] F)
    projectiveTensorTopology E F = τ ∧ injectiveTensorTopology E F = τ ∧
      inductiveTensorTopology E F = τ ∧
        @CompleteSpace (E ⊗[ℂ] F) (finestUniformSpace _) := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  letI : TopologicalSpace F := finestLocallyConvexTopology F
  letI : IsTopologicalAddGroup E := (finest_withSeminorms E).topologicalAddGroup
  letI : IsTopologicalAddGroup F := (finest_withSeminorms F).topologicalAddGroup
  letI : PolynormableSpace ℂ F := (finest_withSeminorms F).toPolynormableSpace
  let T := E ⊗[ℂ] F
  let τ := finestLocallyConvexTopology T
  let π := projectiveTensorTopology E F
  let ι := inductiveTensorTopology E F
  have hπ : π = τ := finest_projectiveTensorTopology b c i j
  have hε : injectiveTensorTopology E F = τ := (finest_tensorTopologies_equal b i).symm.trans hπ
  have hI := inductiveTensor_withSeminorms (E := E) (F := F)
  have hP := projectiveTensor_withSeminorms (E := E) (F := F)
  have hτ := finest_withSeminorms T
  have h₁ : Continuous[ι, π] (id : T → T) := by
    letI : TopologicalSpace T := ι
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ T T
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ ι hI.topologicalAddGroup π hP LinearMap.id).mpr
      (fun P => hI.continuous_seminorm P.toInductive)
  have h₂ : Continuous[τ, ι] (id : T → T) := by
    letI : TopologicalSpace T := τ
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ T T
      _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ τ hτ.topologicalAddGroup ι hI LinearMap.id).mpr
      (fun P => hτ.continuous_seminorm P.tensor)
  refine ⟨hπ, hε, le_antisymm ?_ (continuous_id_iff_le.mp h₂), finest_complete T⟩
  change ι ≤ τ
  rw [← hπ]
  exact continuous_id_iff_le.mp h₁

/-- Extract a countable basis from any countable spanning set. -/
theorem countable_basis_of_countable_generating_set
    {X : Type u} [AddCommGroup X] [Module ℂ X]
    (S : Set X) (hS : S.Countable) (hspan : Submodule.span ℂ S = ⊤) :
    ∃ (I : Type u) (_ : Basis I ℂ X), Nonempty (I ↪ ℕ) := by
  let b := Basis.ofVectorSpace ℂ X
  let I := Basis.ofVectorSpaceIndex ℂ X
  letI : Countable S := hS.to_subtype
  let U : Set I := ⋃ x : S, ((b.repr (x : X)).support : Set I)
  have hU : U.Countable := countable_iUnion fun x => (Finset.finite_toSet _).countable
  have hsub : S ⊆ Submodule.span ℂ (b '' U) := by
    intro x hx
    apply b.mem_span_image.mpr
    exact subset_iUnion (fun y : S => ((b.repr (y : X)).support : Set I)) ⟨x, hx⟩
  have hall : (⊤ : Submodule ℂ X) ≤ Submodule.span ℂ (b '' U) :=
    hspan ▸ Submodule.span_le.mpr hsub
  have huniv : U = univ := by
    apply eq_univ_of_forall
    intro i
    have hi := b.mem_span_image.mp (hall (Submodule.mem_top (x := b i)))
    apply hi
    simp
  have hI : Countable I := Set.countable_univ_iff.mp (huniv ▸ hU)
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat I
  exact ⟨I, b, ⟨⟨f, hf⟩⟩⟩

theorem countablyGenerated_finest_tensor_topologies
    (S : Set E) (R : Set F) (hS : S.Countable) (hR : R.Countable)
    (hE : Submodule.span ℂ S = ⊤) (hF : Submodule.span ℂ R = ⊤) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    letI : TopologicalSpace F := finestLocallyConvexTopology F
    let τ := finestLocallyConvexTopology (E ⊗[ℂ] F)
    projectiveTensorTopology E F = τ ∧ injectiveTensorTopology E F = τ ∧
      inductiveTensorTopology E F = τ ∧
        @CompleteSpace (E ⊗[ℂ] F) (finestUniformSpace _) := by
  obtain ⟨I, b, ⟨i⟩⟩ := countable_basis_of_countable_generating_set S hS hE
  obtain ⟨J, c, ⟨j⟩⟩ := countable_basis_of_countable_generating_set R hR hF
  exact finest_tensor_topologies b c i j

end

end Masullo
