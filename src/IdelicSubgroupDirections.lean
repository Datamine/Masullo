import IdelicStageFaithfulness

open Function NumberField Set Topology

namespace Masullo

noncomputable section

/-- A continuous homomorphism with image in a topologically embedded
subgroup factors continuously through that subgroup. -/
theorem exists_continuousHom_factor_embedding {A H J : Type*}
    [Monoid A] [TopologicalSpace A] [Monoid H] [TopologicalSpace H]
    [Monoid J] [TopologicalSpace J]
    (i : H →ₜ* J) (hi : IsEmbedding i) (e : A →ₜ* J)
    (he : ∀ x, e x ∈ range i) :
    ∃ f : A →ₜ* H, ∀ x, i (f x) = e x := by
  choose r hr using he
  let f : A →ₜ* H :=
    { toFun := r
      map_one' := hi.injective (by rw [hr 1, map_one e, map_one i])
      map_mul' := fun x y => hi.injective (by rw [hr (x * y), map_mul e, map_mul i, hr x, hr y])
      continuous_toFun := hi.isInducing.continuous_iff.mpr (by
        rw [show i ∘ r = e from funext hr]
        exact e.continuous) }
  exact ⟨f, hr⟩

variable (F : Type*) [Field F] [NumberField F]

local notation "Arch" => mixedEmbedding.mixedSpace F

/-- The archimedean exponential into idele classes has connected image
containing the identity. -/
theorem archimedeanClassExponential_mem_identityComponent (x : Multiplicative Arch) :
    archimedeanClassExponential F x ∈ connectedComponent (1 : IdeleClass F) := by
  let e := archimedeanClassExponential F
  let e₀ (v : Arch) := e (Multiplicative.ofAdd v)
  have h₀ : e₀ 0 = 1 := map_one e
  have hc := (e.continuous.comp
    (continuous_ofAdd : Continuous (Multiplicative.ofAdd : Arch → Multiplicative Arch)))
  change Continuous e₀ at hc
  have h := hc.mapsTo_connectedComponent 0
  rw [h₀, PreconnectedSpace.connectedComponent_eq_univ] at h
  exact h (mem_univ x.toAdd)

/-- A subgroup of the idele class group containing the archimedean
exponential inherits its faithful parametrization of real one-parameter
subgroups. This applies to the identity component and each S-local group. -/
theorem exists_idelic_subgroupDirectionParametrization {H : Type*}
    [CommGroup H] [TopologicalSpace H]
    (i : H →ₜ* IdeleClass F) (hi : IsEmbedding i)
    (himage : ∀ x : Multiplicative Arch, archimedeanClassExponential F x ∈ range i) :
    ∃ e : Multiplicative Arch →ₜ* H,
      (∀ x, i (e x) = archimedeanClassExponential F x) ∧
      (∀ c : Multiplicative ℝ →ₜ* H, ∃ x : Arch, ∀ t : ℝ,
        c (Multiplicative.ofAdd t) = e (Multiplicative.ofAdd (t • x))) ∧
      (∀ x : Arch, (∀ t : ℝ, e (Multiplicative.ofAdd (t • x)) = 1) → x = 0) := by
  obtain ⟨e, he⟩ := exists_continuousHom_factor_embedding i hi
    (archimedeanClassExponential F) himage
  refine ⟨e, he, fun c => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hc⟩ := exists_archimedeanClassExponential_direction F (i.comp c)
    exact ⟨x, fun t => hi.injective ((hc t).trans (he _).symm)⟩
  · apply archimedeanClassExponential_direction_eq_one F
    intro t
    rw [← he, hx t, map_one]

end
end Masullo
