import ElementaryDirectionalDerivatives

open Function Set

namespace Masullo

noncomputable section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]

local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "A" => ElementaryLCAModel m n r F

omit [DiscreteTopology F] in
/-- A velocity is determined by its entire one-parameter subgroup, including
in the periodic coordinates. -/
theorem elementaryOneParameter_injective :
    Injective (elementaryOneParameter (m := m) (n := n) (r := r) (F := F)) := by
  intro v w h
  have ht (t : ℝ) := congrArg (fun c : Multiplicative ℝ →ₜ* Multiplicative A =>
    (c (Multiplicative.ofAdd t)).toAdd) h
  have hcover (t : ℝ) : (elementaryCoverHom (t • v) : A) = elementaryCoverHom (t • w) := ht t
  refine Prod.ext ?_ ?_
  · have h₁ := congrArg Prod.fst (hcover 1)
    change (1 : ℝ) • v.1 = (1 : ℝ) • w.1 at h₁
    simpa only [one_smul] using h₁
  · apply PiLp.ext
    intro i
    by_contra hi
    let t : ℝ := (2 * (v.2 i - w.2 i))⁻¹
    have hz : ((t * v.2 i : ℝ) : AddCircle (1 : ℝ)) =
        ((t * w.2 i : ℝ) : AddCircle (1 : ℝ)) :=
      congrArg (fun z : A => z.2.1 i) (hcover t)
    have he : t * (v.2 i - w.2 i) = 1 / 2 := by
      dsimp [t]
      field_simp [sub_ne_zero.mpr hi]
    have hn : (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
      rw [← he, mul_sub, AddCircle.coe_sub, hz, sub_self]
    exact (by norm_num : (1 / 2 : ℝ) ≠ 0)
      ((AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp hn)

omit [DiscreteTopology F] in
/-- The zero velocity gives the constant identity direction. -/
theorem elementaryOneParameter_zero_apply (t : Multiplicative ℝ) :
    elementaryOneParameter (m := m) (n := n) (r := r) (F := F) 0 t = 1 := by
  change Multiplicative.ofAdd (elementaryCoverHom (t.toAdd • (0 : X))) = _
  rw [smul_zero, map_zero]
  rfl

omit [DiscreteTopology F] in
theorem elementaryOneParameter_eq_one_iff (v : X) :
    (∀ t : ℝ, elementaryOneParameter (r := r) (F := F) v (Multiplicative.ofAdd t) = 1) ↔
      v = 0 := by
  constructor
  · intro h
    apply elementaryOneParameter_injective (r := r) (F := F)
    exact ContinuousMonoidHom.ext fun t => (h t.toAdd).trans (elementaryOneParameter_zero_apply t).symm
  · rintro rfl t
    exact elementaryOneParameter_zero_apply _

/-- A continuous homomorphism from a real vector space to an elementary
group induces a linear map of covering velocities. -/
theorem exists_linear_elementaryVelocity {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousSMul ℝ V]
    (q : Multiplicative V →ₜ* Multiplicative A) :
    ∃ L : V →ₗ[ℝ] X, ∀ x t, q (Multiplicative.ofAdd (t • x)) =
      elementaryOneParameter (L x) (Multiplicative.ofAdd t) := by
  let line (x : V) : Multiplicative ℝ →ₜ* Multiplicative V :=
    ⟨((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight x).toAddMonoidHom.toMultiplicative,
      (show Continuous (fun t : Multiplicative ℝ => Multiplicative.ofAdd (t.toAdd • x)) from
        continuous_ofAdd.comp (continuous_toAdd.smul continuous_const))⟩
  choose v hv using fun x => elementaryOneParameter_lift (q.comp (line x))
  have h (x : V) (t : ℝ) : q (Multiplicative.ofAdd (t • x)) =
      elementaryOneParameter (v x) (Multiplicative.ofAdd t) :=
    Multiplicative.toAdd.injective (hv x t)
  have hAdd (x y : V) : v (x + y) = v x + v y := by
    apply elementaryOneParameter_injective (r := r) (F := F)
    apply ContinuousMonoidHom.ext
    intro t
    change elementaryOneParameter (v (x + y)) (Multiplicative.ofAdd t.toAdd) = _
    rw [← h (x + y) t.toAdd, smul_add]
    change q (Multiplicative.ofAdd (t.toAdd • x) * Multiplicative.ofAdd (t.toAdd • y)) = _
    rw [map_mul, h, h]
    apply Multiplicative.toAdd.injective
    change (elementaryCoverHom (t.toAdd • v x) : A) + elementaryCoverHom (t.toAdd • v y) =
      elementaryCoverHom (t.toAdd • (v x + v y))
    rw [smul_add, map_add]
  have hSmul (s : ℝ) (x : V) : v (s • x) = s • v x := by
    apply elementaryOneParameter_injective (r := r) (F := F)
    apply ContinuousMonoidHom.ext
    intro t
    change elementaryOneParameter (v (s • x)) (Multiplicative.ofAdd t.toAdd) = _
    rw [← h (s • x) t.toAdd, smul_smul, h]
    apply Multiplicative.toAdd.injective
    change (elementaryCoverHom ((t.toAdd * s) • v x) : A) = elementaryCoverHom (t.toAdd • (s • v x))
    rw [smul_smul]
  exact ⟨⟨⟨v, hAdd⟩, hSmul⟩, h⟩

end
end Masullo
