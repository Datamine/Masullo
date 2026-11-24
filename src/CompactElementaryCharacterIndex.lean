import BruhatDirectionalDerivatives

open Function Set Topology

namespace Masullo

noncomputable section

variable {n : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel 0 n 0 F
local notation "X" => EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n)

/-- The unit velocity in one torus coordinate. -/
def elementaryTorusVelocity (i : Fin n) : X := (0, EuclideanSpace.single i 1)

theorem sum_elementaryTorusVelocity (u : X) :
    (∑ i : Fin n, u.2 i • elementaryTorusVelocity i) = u := by
  classical
  apply Prod.ext (Subsingleton.elim _ _)
  change AddMonoidHom.snd (EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin n))
    (∑ i : Fin n, u.2 i • elementaryTorusVelocity i) = u.2
  rw [map_sum]
  change (∑ i : Fin n, u.2 i • EuclideanSpace.single i (1 : ℝ)) = u.2
  ext j
  simp [Pi.single_apply, mul_ite]

/-- A linear phase lifting a compact elementary character to the Euclidean cover. -/
def compactElementaryCharacterPhase (χ : PontryaginDual (Multiplicative A)) : X →L[ℝ] ℝ :=
  (elementaryCharacter_phase χ).choose

theorem compactElementaryCharacterPhase_spec (χ : PontryaginDual (Multiplicative A)) (u : X) :
    χ (Multiplicative.ofAdd (elementaryCoverHom u)) = Circle.exp (compactElementaryCharacterPhase χ u) :=
  (elementaryCharacter_phase χ).choose_spec u

theorem exists_compactElementaryCharacter_frequency
    (χ : PontryaginDual (Multiplicative A)) (i : Fin n) :
    ∃ k : ℤ, compactElementaryCharacterPhase χ (elementaryTorusVelocity i) = 2 * Real.pi * k := by
  classical
  have he : (elementaryCoverHom (m := 0) (r := 0) (F := F)) (elementaryTorusVelocity i) = 0 := by
    change (0, (fun j ↦ ((EuclideanSpace.single i (1 : ℝ)) j : AddCircle (1 : ℝ))), 0, 0) = _
    change (0, (fun j ↦ ((EuclideanSpace.single i (1 : ℝ)) j : AddCircle (1 : ℝ))), 0, 0) =
      ((0, 0, 0, 0) : A)
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext j
    change ((EuclideanSpace.single i (1 : ℝ)) j : AddCircle (1 : ℝ)) = 0
    by_cases h : j = i
    · subst j
      simp [AddCircle.coe_period]
    · simp [h]
  have hp := compactElementaryCharacterPhase_spec χ (elementaryTorusVelocity i)
  rw [he, show (Multiplicative.ofAdd (0 : A)) = 1 from rfl, map_one] at hp
  have hc := congrArg (fun z : Circle ↦ (z : ℂ)) hp.symm
  rw [Circle.coe_exp, Circle.coe_one] at hc
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hc
  have h := congrArg Complex.im hk
  simp [Complex.mul_im, Complex.mul_re] at h
  refine ⟨k, ?_⟩
  convert h using 1
  ring

/-- The integral frequency of an elementary character on each unit period. -/
def compactElementaryCharacter_frequency (χ : PontryaginDual (Multiplicative A)) (i : Fin n) : ℤ :=
  (exists_compactElementaryCharacter_frequency χ i).choose

theorem compactElementaryCharacter_frequency_spec
    (χ : PontryaginDual (Multiplicative A)) (i : Fin n) :
    compactElementaryCharacterPhase χ (elementaryTorusVelocity i) =
      2 * Real.pi * (compactElementaryCharacter_frequency χ i) :=
  (exists_compactElementaryCharacter_frequency χ i).choose_spec

/-- The embedding of the finite component of a compact elementary group. -/
def compactElementaryFiniteComponent : Multiplicative F →ₜ* Multiplicative A where
  toFun b := Multiplicative.ofAdd (0, 0, 0, b.toAdd)
  map_one' := rfl
  map_mul' a b := by change Multiplicative.ofAdd (0, 0, 0, a.toAdd + b.toAdd) =
    Multiplicative.ofAdd ((0, 0, 0, a.toAdd) + (0, 0, 0, b.toAdd)); simp
  continuous_toFun := continuous_of_discreteTopology

/-- A character is determined by the torus frequencies and its restriction
to the finite component. -/
theorem compactElementaryCharacter_index_injective :
    Injective (fun χ : PontryaginDual (Multiplicative A) ↦
      (compactElementaryCharacter_frequency χ, PontryaginDual.map compactElementaryFiniteComponent χ)) := by
  classical
  intro χ ψ h
  have hi (i : Fin n) : compactElementaryCharacter_frequency χ i =
      compactElementaryCharacter_frequency ψ i := congrFun (congrArg Prod.fst h) i
  have hF (b : F) : χ (compactElementaryFiniteComponent (Multiplicative.ofAdd b)) =
      ψ (compactElementaryFiniteComponent (Multiplicative.ofAdd b)) :=
    congrArg (fun g : PontryaginDual (Multiplicative F) ↦ g (Multiplicative.ofAdd b))
      (congrArg Prod.snd h)
  have hphase (u : X) : compactElementaryCharacterPhase χ u = compactElementaryCharacterPhase ψ u := by
    conv_lhs => rw [← sum_elementaryTorusVelocity u, map_sum]
    conv_rhs => rw [← sum_elementaryTorusVelocity u, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_smul, compactElementaryCharacter_frequency_spec, hi i]
  ext x
  let y : A := x.toAdd
  obtain ⟨u, hu⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  have hz : elementaryCoverHom (y.1, u) + (0, 0, 0, y.2.2.2) = y := by
    change elementaryCover (y.1, u) 0 0 + (0, 0, 0, y.2.2.2) = y
    convert hu using 1
    have ht : y.2.2.1 = 0 := Subsingleton.elim _ _
    simp [elementaryCover, ht, add_zero, zero_add]
  have hx : x = Multiplicative.ofAdd (elementaryCoverHom (y.1, u)) *
      compactElementaryFiniteComponent (Multiplicative.ofAdd y.2.2.2) :=
    congrArg (Multiplicative.ofAdd : A → Multiplicative A) hz.symm
  rw [hx, map_mul, map_mul, compactElementaryCharacterPhase_spec, compactElementaryCharacterPhase_spec,
    hphase]
  rw [hF]

end

end Masullo
