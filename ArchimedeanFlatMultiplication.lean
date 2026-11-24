import ArchimedeanFlatQuasiCharacter
import ArchimedeanLogarithms

open Function NumberField Set
open scoped Classical SchwartzMap NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev X := mixedEmbedding.mixedSpace F
private abbrev A := archimedeanFlatTestSubspace F

private def realProj (v : R F) : X F →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ _ _)

private def complexProj (v : C F) : X F →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj v).comp (ContinuousLinearMap.snd ℝ _ _)

private def realIn (v : R F) : ℝ →L[ℝ] X F :=
  (ContinuousLinearMap.inl ℝ _ _).comp (ContinuousLinearMap.single ℝ (fun _ : R F ↦ ℝ) v)

private def complexIn (v : C F) : ℂ →L[ℝ] X F :=
  (ContinuousLinearMap.inr ℝ _ _).comp (ContinuousLinearMap.single ℝ (fun _ : C F ↦ ℂ) v)

/-- Multiplication by a character in one real coordinate of a jointly flat test. -/
theorem exists_realCoordinateQuasiCharacter_mulCLM (v : R F) (χ : ℝˣ →ₜ* ℂ) :
    ∃ M : A F →L[ℂ] A F, ∀ f : A F, ∀ x : X F, (M f).val x =
      unitCharacterZeroExtend χ (x.1 v) * f.val x := by
  have hpi : LeftInverse (realProj F v) (realIn F v) := by
    intro x
    change Pi.single (M := fun _ : R F ↦ ℝ) v x v = x
    rw [Pi.single_eq_same]
  have hp (x : X F) : ‖realProj F v x‖ ≤ ‖x‖ := by
    change ‖x.1 v‖ ≤ _
    exact (norm_le_pi_norm x.1 v).trans (norm_fst_le x)
  have hi (y : ℝ) : ‖realIn F v y‖ ≤ ‖y‖ := by
    change ‖(Pi.single (M := fun _ : R F ↦ ℝ) v y, (0 : C F → ℂ))‖ ≤ ‖y‖
    rw [Prod.norm_def, Pi.norm_single, norm_zero, max_eq_left (norm_nonneg _)]
  exact exists_coordinateQuasiCharacter_mulCLM χ (realUnitCharacterZeroExtend_contDiffOn χ)
    (realUnitCharacterZeroExtend_jet_bounds χ) (realProj F v) (realIn F v) hpi hp hi _
    (fun x hx ↦ Or.inl ⟨v, hx⟩)

/-- Multiplication by a character in one complex coordinate of a jointly flat test. -/
theorem exists_complexCoordinateQuasiCharacter_mulCLM (v : C F) (χ : ℂˣ →ₜ* ℂ) :
    ∃ M : A F →L[ℂ] A F, ∀ f : A F, ∀ x : X F, (M f).val x =
      unitCharacterZeroExtend χ (x.2 v) * f.val x := by
  have hpi : LeftInverse (complexProj F v) (complexIn F v) := by
    intro x
    change Pi.single (M := fun _ : C F ↦ ℂ) v x v = x
    rw [Pi.single_eq_same]
  have hp (x : X F) : ‖complexProj F v x‖ ≤ ‖x‖ := by
    change ‖x.2 v‖ ≤ _
    exact (norm_le_pi_norm x.2 v).trans (norm_snd_le x)
  have hi (y : ℂ) : ‖complexIn F v y‖ ≤ ‖y‖ := by
    change ‖((0 : R F → ℝ), Pi.single (M := fun _ : C F ↦ ℂ) v y)‖ ≤ ‖y‖
    rw [Prod.norm_def, Pi.norm_single, norm_zero, max_eq_right (norm_nonneg _)]
  exact exists_coordinateQuasiCharacter_mulCLM χ (complexUnitCharacterZeroExtend_contDiffOn χ)
    (complexUnitCharacterZeroExtend_jet_bounds χ) (complexProj F v) (complexIn F v) hpi hp hi _
    (fun x hx ↦ Or.inr ⟨v, hx⟩)

private theorem exists_flat_multiplier_finset {ι : Type*} (b : ι → X F → ℂ)
    (h : ∀ v, ∃ M : A F →L[ℂ] A F, ∀ f : A F, ∀ x : X F, (M f).val x = b v x * f.val x)
    (I : Finset ι) :
    ∃ M : A F →L[ℂ] A F, ∀ f : A F, ∀ x : X F, (M f).val x = (∏ v ∈ I, b v x) * f.val x := by
  induction I using Finset.induction_on with
  | empty => exact ⟨ContinuousLinearMap.id ℂ _, fun _ _ ↦ by simp⟩
  | insert v I hv ih =>
    obtain ⟨M, hM⟩ := h v
    obtain ⟨N, hN⟩ := ih
    refine ⟨M.comp N, fun f x ↦ ?_⟩
    change (M (N f)).val x = _
    rw [hM, hN, Finset.prod_insert hv, mul_assoc]

/-- A product of the coordinate quasi-characters acts on the jointly flat
Schwartz subspace by continuous pointwise multiplication. -/
theorem exists_archimedeanCoordinateQuasiCharacter_mulCLM
    (a : R F → ℝˣ →ₜ* ℂ) (b : C F → ℂˣ →ₜ* ℂ) :
    ∃ M : A F →L[ℂ] A F, ∀ f : A F, ∀ x : X F, (M f).val x =
      ((∏ v : R F, unitCharacterZeroExtend (a v) (x.1 v)) *
        (∏ v : C F, unitCharacterZeroExtend (b v) (x.2 v))) * f.val x := by
  obtain ⟨M, hM⟩ := exists_flat_multiplier_finset F (fun v x ↦ unitCharacterZeroExtend (a v) (x.1 v))
    (fun v ↦ exists_realCoordinateQuasiCharacter_mulCLM F v (a v)) Finset.univ
  obtain ⟨N, hN⟩ := exists_flat_multiplier_finset F (fun v x ↦ unitCharacterZeroExtend (b v) (x.2 v))
    (fun v ↦ exists_complexCoordinateQuasiCharacter_mulCLM F v (b v)) Finset.univ
  refine ⟨M.comp N, fun f x ↦ ?_⟩
  change (M (N f)).val x = _
  rw [hM, hN, mul_assoc]

private abbrev U := (R F → ℝˣ) × (C F → ℂˣ)

private def unitPoint (u : U F) : X F := (fun v ↦ (u.1 v : ℝ), fun v ↦ (u.2 v : ℂ))

private def realInsert (v : R F) : ℝˣ →ₜ* U F where
  toFun u := (Pi.mulSingle v u, 1)
  map_one' := by simp
  map_mul' u w := by simp [Pi.mulSingle_mul]
  continuous_toFun := (continuous_mulSingle (A := fun _ : R F ↦ ℝˣ) v).prodMk continuous_const

private def complexInsert (v : C F) : ℂˣ →ₜ* U F where
  toFun u := (1, Pi.mulSingle v u)
  map_one' := by simp
  map_mul' u w := by simp [Pi.mulSingle_mul]
  continuous_toFun := continuous_const.prodMk (continuous_mulSingle (A := fun _ : C F ↦ ℂˣ) v)

private def complexUnitVal : ℂˣ →ₜ* ℂ :=
  ⟨{ toFun := Units.val, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }, Units.continuous_val⟩

private theorem character_factor (χ : U F →ₜ* ℂ) (u : U F) :
    (∏ v : R F, χ (realInsert F v (u.1 v))) *
      (∏ v : C F, χ (complexInsert F v (u.2 v))) = χ u := by
  rw [← map_prod, ← map_prod, ← map_mul]
  congr 1
  apply Prod.ext
  · change (MonoidHom.fst (R F → ℝˣ) (C F → ℂˣ)) (_ * _) = _
    rw [map_mul, map_prod, map_prod]
    change (∏ v : R F, Pi.mulSingle v (u.1 v)) * (∏ _ : C F, 1) = u.1
    rw [Finset.prod_const_one, mul_one, Finset.univ_prod_mulSingle]
  · change (MonoidHom.snd (R F → ℝˣ) (C F → ℂˣ)) (_ * _) = _
    rw [map_mul, map_prod, map_prod]
    change (∏ _ : R F, 1) * (∏ v : C F, Pi.mulSingle v (u.2 v)) = u.2
    rw [Finset.prod_const_one, one_mul, Finset.univ_prod_mulSingle]

private theorem exists_archimedeanUnits_mulCLM (χ : U F →ₜ* ℂˣ) :
    ∃ M : A F →L[ℂ] A F, ∀ f : A F, ∀ u : U F, (M f).val (unitPoint F u) =
      (χ u : ℂ) * f.val (unitPoint F u) := by
  let c := complexUnitVal.comp χ
  obtain ⟨M, hM⟩ := exists_archimedeanCoordinateQuasiCharacter_mulCLM F
    (fun v ↦ c.comp (realInsert F v)) (fun v ↦ c.comp (complexInsert F v))
  refine ⟨M, fun f u ↦ ?_⟩
  rw [hM]
  change ((∏ v : R F, unitCharacterZeroExtend _ (u.1 v).val) *
    (∏ v : C F, unitCharacterZeroExtend _ (u.2 v).val)) * f.val _ = _
  simp only [unitCharacterZeroExtend_apply_units]
  exact congrArg (· * f.val (unitPoint F u)) (character_factor F c u)

private theorem flat_ext_of_units (f g : A F)
    (h : ∀ u : U F, f.val (unitPoint F u) = g.val (unitPoint F u)) : f = g := by
  apply Subtype.ext
  apply SchwartzMap.ext
  intro x
  by_cases hx : (∃ v : R F, x.1 v = 0) ∨ ∃ v : C F, x.2 v = 0
  · have hz (a : A F) : a.val x = 0 := by
      have hD := (mem_schwartzFlatSubspace _ _).mp a.property x hx 0
      exact norm_eq_zero.mp (by simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm hD)
    rw [hz f, hz g]
  · have hr (v : R F) : x.1 v ≠ 0 := fun hv ↦ hx (Or.inl ⟨v, hv⟩)
    have hc (v : C F) : x.2 v ≠ 0 := fun hv ↦ hx (Or.inr ⟨v, hv⟩)
    exact h (fun v ↦ Units.mk0 (x.1 v) (hr v), fun v ↦ Units.mk0 (x.2 v) (hc v))

/-- Every archimedean quasi-character acts by a continuous linear
automorphism on the jointly flat subspace of the mixed Schwartz space. -/
theorem exists_archimedeanQuasiCharacter_mulEquiv (χ : (InfiniteAdeleRing F)ˣ →ₜ* ℂˣ) :
    ∃ M : A F ≃L[ℂ] A F, ∀ f : A F, ∀ u : (InfiniteAdeleRing F)ˣ,
      (M f).val (InfiniteAdeleRing.ringEquiv_mixedSpace F u.val) =
        (χ u : ℂ) * f.val (InfiniteAdeleRing.ringEquiv_mixedSpace F u.val) := by
  let e := infiniteAdeleUnitsCoordinates F
  let c := χ.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  obtain ⟨M, hM⟩ := exists_archimedeanUnits_mulCLM F c
  obtain ⟨N, hN⟩ := exists_archimedeanUnits_mulCLM F c⁻¹
  have hl (f : A F) : N (M f) = f := by
    apply flat_ext_of_units F
    intro u
    rw [hN, hM]
    change (↑((c u)⁻¹) : ℂ) * ((c u : ℂ) * f.val _) = f.val _
    rw [← mul_assoc, Units.inv_mul, one_mul]
  have hr (f : A F) : M (N f) = f := by
    apply flat_ext_of_units F
    intro u
    rw [hM, hN]
    change (c u : ℂ) * ((↑((c u)⁻¹) : ℂ) * f.val _) = f.val _
    rw [← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨⟨{ M.toLinearMap with invFun := N, left_inv := hl, right_inv := hr },
    M.continuous, N.continuous⟩, fun f u ↦ ?_⟩
  have hu := hM f (e u)
  change (M f).val (unitPoint F (e u)) = (χ u : ℂ) * f.val (unitPoint F (e u))
  change (M f).val (unitPoint F (e u)) =
    (χ (e.symm (e u)) : ℂ) * f.val (unitPoint F (e u)) at hu
  rwa [e.symm_apply_apply] at hu

end

end Masullo
