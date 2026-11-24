import Mathlib.Analysis.InnerProductSpace.Dual

open Filter Function Set Topology
open scoped Classical InnerProductSpace

namespace Masullo
noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A dense collection of tests with finitely supported coefficients makes
the projected interpolation tests total in the Hilbert annihilator. -/
theorem hilbert_moment_markushevich [DecidableEq ι]
    (R : Submodule ℂ E) (hR : IsClosed (R : Set E))
    (r q : ι → E) (hr : ∀ i, r i ∈ Rᗮ)
    (hker : ∀ x : E, x ∈ R ↔ ∀ i, ⟪r i,x⟫_ℂ = 0)
    (hbi : ∀ i j, ⟪r j,q i⟫_ℂ = if j = i then 1 else 0)
    (X : Set E) (hX : Dense X)
    (hfin : ∀ x ∈ X, {i | ⟪r i,x⟫_ℂ ≠ 0}.Finite) :
    let e : ι → Rᗮ := fun i ↦ ⟨r i, hr i⟩
    ∃ φ : ι → Rᗮ →L[ℂ] ℂ,
      (∀ i j, φ i (e j) = if j = i then 1 else 0) ∧
      Dense (Submodule.span ℂ (range e) : Set Rᗮ) ∧
      ∀ v : Rᗮ, (∀ i, φ i v = 0) → v = 0 := by
  classical
  intro e
  let D := Rᗮ
  letI : IsClosed (R : Set E) := hR
  letI : CompleteSpace D := R.isClosed_orthogonal.completeSpace_coe
  let p (i : ι) := D.orthogonalProjectionOnto (q i)
  have hp (i : ι) (x : D) : ⟪p i,x⟫_ℂ = ⟪q i,x.val⟫_ℂ := by
    exact D.inner_orthogonalProjectionOnto_eq_of_mem_right x (q i)
  refine ⟨fun i ↦ innerSL ℂ (p i), ?_, ?_, ?_⟩
  · intro i j
    change ⟪p i,e j⟫_ℂ = _
    rw [hp, ← inner_conj_symm, hbi]
    by_cases h : j = i <;> simp [h]
  · let U := (Submodule.span ℂ (range e)).topologicalClosure
    letI : CompleteSpace U := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    have hU : Uᗮ = ⊥ := by
      apply (Submodule.eq_bot_iff _).2
      intro v hv
      have hz (i : ι) : ⟪r i,v.val⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal U v).mp hv (e i)
          (Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self i)))
      have hRv := (hker v.val).2 hz
      apply Subtype.ext
      exact inner_self_eq_zero.mp ((R.mem_orthogonal v.val).mp v.property v.val hRv)
    have ht := (Submodule.orthogonal_eq_bot_iff (K := U)).mp hU
    intro v
    change v ∈ U
    rw [ht]
    exact Submodule.mem_top
  · intro v hv
    have hq (i : ι) : ⟪q i,v.val⟫_ℂ = 0 := (hp i v).symm.trans (hv i)
    have hz (x : E) (hx : x ∈ X) : ⟪x,v.val⟫_ℂ = 0 := by
      let A := (hfin x hx).toFinset
      let y := ∑ i ∈ A, ⟪r i,x⟫_ℂ • q i
      have hY : x - y ∈ R := by
        apply (hker _).2
        intro j
        rw [inner_sub_right]
        change ⟪r j,x⟫_ℂ - ⟪r j,∑ i ∈ A, ⟪r i,x⟫_ℂ • q i⟫_ℂ = 0
        rw [inner_sum]
        simp only [inner_smul_right, hbi, mul_ite, mul_one, mul_zero]
        by_cases hj : j ∈ A
        · simp [Finset.sum_ite_eq, hj]
        · have he : ⟪r j,x⟫_ℂ = 0 := by
            by_contra hn
            exact hj ((hfin x hx).mem_toFinset.mpr hn)
          simp [Finset.sum_ite_eq, hj, he]
      have hzero := (R.mem_orthogonal v.val).mp v.property _ hY
      rw [inner_sub_left] at hzero
      have hy : ⟪y,v.val⟫_ℂ = 0 := by
        simp [y, sum_inner, inner_smul_left, hq]
      rw [hy, sub_zero] at hzero
      exact hzero
    have h0 : v.val = 0 := hX.eq_zero_of_inner_right ℂ hz
    exact Subtype.ext h0


/-- The annihilator in the strong continuous dual equipped with the inherited topology. -/
def hilbertStrongAnnihilator (R : Submodule ℂ E) : Submodule ℂ (StrongDual ℂ E) where
  carrier := {f | ∀ u ∈ R, f u = 0}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' := fun hf hg u hu ↦ by simp [hf u hu, hg u hu]
  smul_mem' := fun a f hf u hu ↦ by simp [hf u hu]

private theorem hilbertStrongAnnihilator_eq_map (R : Submodule ℂ E) :
    Rᗮ.map (InnerProductSpace.toDual ℂ E).toLinearEquiv.toLinearMap =
      hilbertStrongAnnihilator R := by
  ext f
  constructor
  · rintro ⟨v, hv, rfl⟩ u hu
    exact inner_eq_zero_symm.mp ((R.mem_orthogonal v).mp hv u hu)
  · intro h
    obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ E).surjective f
    refine ⟨v, (R.mem_orthogonal v).mpr (fun u hu ↦ ?_), rfl⟩
    exact inner_eq_zero_symm.mp (h u hu)

/-- Riesz representation identifies the Hilbert orthogonal and strong-dual annihilator
by a conjugate-linear isometric equivalence. -/
def hilbertStrongAnnihilatorEquiv (R : Submodule ℂ E) :
    Rᗮ ≃ₗᵢ⋆[ℂ] hilbertStrongAnnihilator R :=
  ((InnerProductSpace.toDual ℂ E).submoduleMap Rᗮ).trans
    (LinearIsometryEquiv.ofEq _ _ (hilbertStrongAnnihilator_eq_map R))

theorem hilbertStrongAnnihilatorEquiv_apply (R : Submodule ℂ E) (v : Rᗮ) (u : E) :
    (hilbertStrongAnnihilatorEquiv R v).val u = ⟪v.val,u⟫_ℂ := by
  rw [hilbertStrongAnnihilatorEquiv]
  exact InnerProductSpace.toDual_apply_apply (𝕜 := ℂ) (x := v.val) (y := u)

/-- The strong-dual topology of a Hilbert space inherits the basis properties
through conjugate-linear Riesz representation. -/
theorem hilbertStrongAnnihilator_markushevich [DecidableEq ι] (R : Submodule ℂ E)
    (e : ι → Rᗮ) (φ : ι → Rᗮ →L[ℂ] ℂ)
    (hbi : ∀ i j, φ i (e j) = if j = i then 1 else 0)
    (hd : Dense (Submodule.span ℂ (range e) : Set Rᗮ))
    (ht : ∀ v : Rᗮ, (∀ i, φ i v = 0) → v = 0) :
    let T := hilbertStrongAnnihilatorEquiv R
    ∃ ψ : ι → hilbertStrongAnnihilator R →L[ℂ] ℂ,
      (∀ i j, ψ i (T (e j)) = if j = i then 1 else 0) ∧
      Dense (Submodule.span ℂ (range (T ∘ e)) : Set (hilbertStrongAnnihilator R)) ∧
      ∀ v : hilbertStrongAnnihilator R, (∀ i, ψ i v = 0) → v = 0 := by
  intro T
  let c : ℂ →L⋆[ℂ] ℂ := ⟨
    { toFun := star, map_add' := star_add, map_smul' := by
        intro a z
        change star (a*z) = star a * star z
        exact star_mul' a z }, continuous_star⟩
  let ψ (i : ι) : hilbertStrongAnnihilator R →L[ℂ] ℂ :=
    c.comp ((φ i).comp T.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro i j
    change star (φ i (T.symm (T (e j)))) = _
    rw [LinearIsometryEquiv.symm_apply_apply, hbi]
    by_cases h : j = i <;> simp [h]
  · have he := Submodule.map_span T.toLinearEquiv.toLinearMap (range e)
    rw [← range_comp] at he
    change Submodule.map T.toLinearEquiv.toLinearMap (Submodule.span ℂ (range e)) =
      Submodule.span ℂ (range (T ∘ e)) at he
    rw [← he]
    exact T.surjective.denseRange.dense_image T.continuous hd
  · intro v hv
    apply T.symm.injective
    rw [show T.symm (0 : hilbertStrongAnnihilator R) = 0 from T.symm.toLinearEquiv.map_zero]
    apply ht
    intro i
    have hi := hv i
    change star (φ i (T.symm v)) = 0 at hi
    exact star_eq_zero.mp hi

end
end Masullo
