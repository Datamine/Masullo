import CompactElementaryCharacterIndex
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Homotopy.Lifting

open Function Set Topology
open scoped BigOperators

namespace Masullo

noncomputable section

variable {n : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel 0 n 0 F
local notation "D" => Additive (PontryaginDual (Multiplicative F))

private theorem circle_exp_slopes_injective {a b : ℝ}
    (h : ∀ t : ℝ, Circle.exp (t * a) = Circle.exp (t * b)) : a = b := by
  have he := Circle.isCoveringMap_exp.eq_of_comp_eq
    (continuous_id.mul (continuous_const (y := a)))
    (continuous_id.mul (continuous_const (y := b)))
    (funext h) 0 (by simp)
  simpa using congrFun he 1

/-- The character with prescribed integer torus frequencies and finite
component. -/
def compactElementaryCharacterFromIndex (k : Fin n → ℤ) (η : PontryaginDual (Multiplicative F)) :
    PontryaginDual (Multiplicative A) where
  toFun x := (∏ i, AddCircle.toCircle (x.toAdd.2.1 i) ^ k i) * η (Multiplicative.ofAdd x.toAdd.2.2.2)
  map_one' := by
    change (∏ i, AddCircle.toCircle (0 : AddCircle (1 : ℝ)) ^ k i) * η 1 = 1
    simp
  map_mul' x y := by
    change (∏ i, AddCircle.toCircle (x.toAdd.2.1 i + y.toAdd.2.1 i) ^ k i) *
      η (Multiplicative.ofAdd (x.toAdd.2.2.2 + y.toAdd.2.2.2)) = _
    rw [show Multiplicative.ofAdd (x.toAdd.2.2.2 + y.toAdd.2.2.2) =
      Multiplicative.ofAdd x.toAdd.2.2.2 * Multiplicative.ofAdd y.toAdd.2.2.2 from rfl, map_mul]
    simp only [AddCircle.toCircle_add, mul_zpow, Finset.prod_mul_distrib]
    ac_rfl
  continuous_toFun := by
    have hcoord (i : Fin n) : Continuous (fun x : Multiplicative A ↦ x.toAdd.2.1 i) :=
      (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_toAdd))
    refine (continuous_finsetProd _ fun i _ ↦ (AddCircle.continuous_toCircle.comp (hcoord i)).zpow _).mul ?_
    exact η.continuous.comp (continuous_ofAdd.comp
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))))

theorem compactElementaryCharacterFromIndex_frequency (k : Fin n → ℤ)
    (η : PontryaginDual (Multiplicative F)) (i : Fin n) :
    compactElementaryCharacter_frequency (compactElementaryCharacterFromIndex k η) i = k i := by
  classical
  let χ := compactElementaryCharacterFromIndex k η
  have he (t : ℝ) :
      Circle.exp (t * compactElementaryCharacterPhase χ (elementaryTorusVelocity i)) =
        Circle.exp (t * (2 * Real.pi * k i)) := by
    rw [← smul_eq_mul, ← map_smul, ← compactElementaryCharacterPhase_spec]
    have hcoord (j : Fin n) : (t • elementaryTorusVelocity i).2 j = if j = i then t else 0 := by
      simp [elementaryTorusVelocity, mul_ite]
    change (∏ j, AddCircle.toCircle (↑((t • elementaryTorusVelocity i).2 j) : AddCircle (1 : ℝ)) ^
      k j) * η 1 = _
    simp only [hcoord, map_one, mul_one]
    rw [Finset.prod_eq_single i]
    · simp only [ite_true, AddCircle.toCircle_apply_mk, div_one, ← Circle.exp_zsmul, zsmul_eq_mul]
      congr 1
      ring
    · intro j _ hj
      simp [hj]
    · simp
  have hh := circle_exp_slopes_injective he
  rw [compactElementaryCharacter_frequency_spec] at hh
  exact_mod_cast (mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) hh)

omit [Finite F] in
@[simp] theorem compactElementaryCharacterFromIndex_finite (k : Fin n → ℤ)
    (η : PontryaginDual (Multiplicative F)) :
    PontryaginDual.map compactElementaryFiniteComponent (compactElementaryCharacterFromIndex k η) = η := by
  ext x
  change (((∏ i, AddCircle.toCircle (0 : AddCircle (1 : ℝ)) ^ k i) * η x : Circle) : ℂ) = _
  simp

theorem compactElementaryCharacterFromIndex_bijective :
    Bijective (fun p : (Fin n → ℤ) × PontryaginDual (Multiplicative F) ↦
      compactElementaryCharacterFromIndex p.1 p.2) := by
  let e (χ : PontryaginDual (Multiplicative A)) :=
    (compactElementaryCharacter_frequency χ, PontryaginDual.map compactElementaryFiniteComponent χ)
  have h (p : (Fin n → ℤ) × PontryaginDual (Multiplicative F)) :
      e (compactElementaryCharacterFromIndex p.1 p.2) = p :=
    Prod.ext (funext (compactElementaryCharacterFromIndex_frequency p.1 p.2))
      (compactElementaryCharacterFromIndex_finite p.1 p.2)
  refine ⟨fun a b hab ↦ (h a).symm.trans ((congrArg e hab).trans (h b)), fun χ ↦ ?_⟩
  exact ⟨e χ, compactElementaryCharacter_index_injective (h (e χ))⟩

/-- The discrete coordinates of the dual of a torus times a finite group. -/
def compactElementaryDualEquiv [CompactSpace (Multiplicative A)] :
    Multiplicative (ElementaryLCAModel 0 0 n D) ≃ₜ* PontryaginDual (Multiplicative A) := by
  let H := Multiplicative (ElementaryLCAModel 0 0 n D)
  letI : Finite (Multiplicative F) := Finite.of_equiv F Multiplicative.ofAdd
  letI : CompactSpace (Multiplicative F) := Finite.compactSpace
  letI : DiscreteTopology (ElementaryLCAModel 0 0 n D) := inferInstance
  let h : H →* PontryaginDual (Multiplicative A) :=
    { toFun x := compactElementaryCharacterFromIndex x.toAdd.2.2.1 x.toAdd.2.2.2.toMul
      map_one' := by
        ext x
        change (((∏ i : Fin n, AddCircle.toCircle (x.toAdd.2.1 i) ^ (0 : ℤ)) * (1 : Circle) : Circle) : ℂ) = _
        simp
      map_mul' := by
        intro x y
        ext z
        change (((∏ i, AddCircle.toCircle (z.toAdd.2.1 i) ^ (x.toAdd.2.2.1 i + y.toAdd.2.2.1 i)) *
          (x.toAdd.2.2.2.toMul (Multiplicative.ofAdd z.toAdd.2.2.2) *
            y.toAdd.2.2.2.toMul (Multiplicative.ofAdd z.toAdd.2.2.2)) : Circle) : ℂ) = _
        simp only [zpow_add, Finset.prod_mul_distrib]
        apply congrArg (fun q : Circle ↦ (q : ℂ))
        change _ = ((∏ i, AddCircle.toCircle (z.toAdd.2.1 i) ^ x.toAdd.2.2.1 i) *
          x.toAdd.2.2.2.toMul (Multiplicative.ofAdd z.toAdd.2.2.2)) *
          ((∏ i, AddCircle.toCircle (z.toAdd.2.1 i) ^ y.toAdd.2.2.1 i) *
            y.toAdd.2.2.2.toMul (Multiplicative.ofAdd z.toAdd.2.2.2))
        ac_rfl }
  let e := MulEquiv.ofBijective h (by
    refine ⟨fun x y hxy ↦ ?_, fun χ ↦ ?_⟩
    · have hp := compactElementaryCharacterFromIndex_bijective.1 hxy
      exact Multiplicative.toAdd.injective
        (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) hp))
    · obtain ⟨p, hp⟩ := compactElementaryCharacterFromIndex_bijective.2 χ
      exact ⟨Multiplicative.ofAdd (0, 0, p.1, Additive.ofMul p.2), hp⟩)
  exact { e with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

theorem compactElementaryDualEquiv_frequency [CompactSpace (Multiplicative A)]
    (x : Multiplicative (ElementaryLCAModel 0 0 n D)) (i : Fin n) :
    compactElementaryCharacter_frequency (compactElementaryDualEquiv x) i = x.toAdd.2.2.1 i :=
  compactElementaryCharacterFromIndex_frequency _ _ _

/-- A box of integral torus frequencies leaves only the free choice of a
character of the finite component. -/
def compactElementaryCharacter_boxEquiv (T : ℕ) :
    {χ : PontryaginDual (Multiplicative A) // ∀ i, |compactElementaryCharacter_frequency χ i| ≤ (T : ℤ)} ≃
      ((Fin n → ↥(Finset.Icc (-(T : ℤ)) (T : ℤ))) × PontryaginDual (Multiplicative F)) where
  toFun χ := ⟨fun i => ⟨compactElementaryCharacter_frequency χ.val i,
      Finset.mem_Icc.mpr (abs_le.mp (χ.property i))⟩,
    PontryaginDual.map compactElementaryFiniteComponent χ.val⟩
  invFun p := ⟨compactElementaryCharacterFromIndex (fun i => (p.1 i).val) p.2, fun i => by
    rw [compactElementaryCharacterFromIndex_frequency]
    exact abs_le.mpr (Finset.mem_Icc.mp (p.1 i).property)⟩
  left_inv χ := by
    apply Subtype.ext
    apply compactElementaryCharacter_index_injective
    exact Prod.ext (funext (compactElementaryCharacterFromIndex_frequency _ _))
      (compactElementaryCharacterFromIndex_finite _ _)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact Subtype.ext (compactElementaryCharacterFromIndex_frequency _ _ _)
    · exact compactElementaryCharacterFromIndex_finite _ _

/-- The number of characters in the frequency box is polynomial in its
radius, with degree the number of torus factors. -/
theorem compactElementaryCharacter_card_box (T : ℕ) :
    Nat.card {χ : PontryaginDual (Multiplicative A) //
      ∀ i, |compactElementaryCharacter_frequency χ i| ≤ (T : ℤ)} =
      (2 * T + 1) ^ n * Nat.card (PontryaginDual (Multiplicative F)) := by
  have hc : Nat.card ↥(Finset.Icc (-(T : ℤ)) (T : ℤ)) = 2 * T + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
    omega
  rw [Nat.card_congr (compactElementaryCharacter_boxEquiv (F := F) (n := n) T),
    Nat.card_prod, Nat.card_fun, Nat.card_fin, hc]

end

end Masullo
