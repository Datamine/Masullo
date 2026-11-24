import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Maps.Strict.Group

open Filter Function Set Topology

namespace Masullo

noncomputable section

/-- A closed subgroup of the circle is either the circle or a finite group. -/
theorem closed_circleSubgroup_eq_top_or_finite (S : Subgroup Circle)
    (hS : IsClosed (S : Set Circle)) : S = ⊤ ∨ Set.Finite (S : Set Circle) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have he (x : AddCircle (1 : ℝ)) : e x = AddCircle.toCircle x :=
    AddCircle.homeomorphCircle_apply one_ne_zero x
  let A : AddSubgroup (AddCircle (1 : ℝ)) :=
    { carrier := e ⁻¹' (S : Set Circle)
      zero_mem' := by rw [mem_preimage, he, AddCircle.toCircle_zero]; exact S.one_mem
      add_mem' := by
        intro x y hx hy
        change e x ∈ S at hx
        change e y ∈ S at hy
        change e (x + y) ∈ S
        rw [he, AddCircle.toCircle_add, ← he, ← he]
        exact S.mul_mem hx hy
      neg_mem' := by
        intro x hx
        change e x ∈ S at hx
        change e (-x) ∈ S
        rw [he, AddCircle.toCircle_neg, ← he]
        exact S.inv_mem hx }
  have hA : IsClosed (A : Set (AddCircle (1 : ℝ))) := hS.preimage e.continuous
  have himage : e '' (A : Set (AddCircle (1 : ℝ))) = (S : Set Circle) := by
    apply e.surjective.image_preimage
  by_cases hd : Dense (A : Set (AddCircle (1 : ℝ)))
  · left
    have hfull : (A : Set (AddCircle (1 : ℝ))) = univ := hA.closure_eq.symm.trans hd.closure_eq
    apply SetLike.coe_injective
    rw [← himage, hfull, image_univ, e.surjective.range_eq, Subgroup.coe_top]
  · right
    obtain ⟨a, ha, hgen⟩ :
        ∃ a : AddCircle (1 : ℝ), addOrderOf a ≠ 0 ∧ A = AddSubgroup.zmultiples a := by
      have hn := mt ((AddCircle.dense_addSubgroup_iff_ne_zmultiples (s := A)).mpr) hd
      push Not at hn
      exact hn
    have hfinite : Set.Finite (A : Set (AddCircle (1 : ℝ))) := by
      rw [hgen]
      exact (addOrderOf_pos_iff.mp (Nat.pos_of_ne_zero ha)).finite_zmultiples
    rw [← himage]
    exact hfinite.image e

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

/-- A compact character descends through its actual kernel quotient. -/
def compactCharacter_quotientRange (χ : PontryaginDual K) :
    K ⧸ χ.toMonoidHom.ker ≃ₜ* χ.toMonoidHom.range :=
  ContinuousMulEquiv.quotientKerEquivRange
    (χ.continuous.isClosedMap.isStrictMap χ.continuous)

omit [IsTopologicalGroup K] in
theorem compactCharacter_quotientRange_apply (χ : PontryaginDual K) (x : K) :
    (compactCharacter_quotientRange χ (QuotientGroup.mk x)).val = χ x := rfl

omit [IsTopologicalGroup K] in
/-- The compact quotient through which a character factors is a circle or a
finite group. -/
theorem compactCharacter_quotient_circle_or_finite (χ : PontryaginDual K) :
    χ.toMonoidHom.range = ⊤ ∨ Set.Finite (χ.toMonoidHom.range : Set Circle) :=
  closed_circleSubgroup_eq_top_or_finite _ (isCompact_range χ.continuous).isClosed

end

end Masullo
