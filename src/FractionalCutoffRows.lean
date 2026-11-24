import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Algebra.Exact.Basic
import Mathlib.Topology.Algebra.Module.Equiv

open Function Set Topology

namespace Masullo
noncomputable section

section Transport

variable {A B C D E F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Two cutoff rows and the Mellin equivalences between their terms. -/
structure FractionalCutoffRows (A B C D E F : Type*)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup C] [NormedSpace ℂ C] [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] where
  physicalInclusion : A →L[ℂ] B
  physicalProjection : B →L[ℂ] C
  leftMellin : A ≃L[ℂ] D
  middleMellin : B ≃L[ℂ] E
  rightMellin : C ≃L[ℂ] F
  analyticInclusion : D →L[ℂ] E
  analyticProjection : E →L[ℂ] F
  inclusionCommutes : ∀ x, middleMellin (physicalInclusion x) = analyticInclusion (leftMellin x)
  projectionCommutes : ∀ x, rightMellin (physicalProjection x) = analyticProjection (middleMellin x)
  physicalExact : Injective physicalInclusion ∧ IsClosed (range physicalInclusion) ∧
    Exact physicalInclusion physicalProjection ∧ Surjective physicalProjection ∧ IsOpenMap physicalProjection
  analyticExact : Injective analyticInclusion ∧ IsClosed (range analyticInclusion) ∧
    Exact analyticInclusion analyticProjection ∧ Surjective analyticProjection ∧ IsOpenMap analyticProjection

private theorem transport_cutoff_exact (i : A →L[ℂ] B) (p : B →L[ℂ] C)
    (eA : A ≃L[ℂ] D) (eB : B ≃L[ℂ] E) (eC : C ≃L[ℂ] F)
    (hi : Injective i) (hc : IsClosed (range i)) (he : Exact i p)
    (hp : Surjective p) (ho : IsOpenMap p) :
    ∃ (j : D →L[ℂ] E) (q : E →L[ℂ] F),
      (∀ x, eB (i x) = j (eA x)) ∧ (∀ x, eC (p x) = q (eB x)) ∧
      Injective j ∧ IsClosed (range j) ∧ Exact j q ∧ Surjective q ∧ IsOpenMap q := by
  let j := eB.toContinuousLinearMap.comp (i.comp eA.symm.toContinuousLinearMap)
  let q := eC.toContinuousLinearMap.comp (p.comp eB.symm.toContinuousLinearMap)
  have hj (x : A) : j (eA x) = eB (i x) := by
    change eB (i (eA.symm (eA x))) = _
    rw [eA.symm_apply_apply]
  have hq (x : B) : q (eB x) = eC (p x) := by
    change eC (p (eB.symm (eB x))) = _
    rw [eB.symm_apply_apply]
  refine ⟨j, q, fun x => (hj x).symm, fun x => (hq x).symm,
    eB.injective.comp (hi.comp eA.symm.injective), ?_, ?_,
    eC.surjective.comp (hp.comp eB.symm.surjective),
    eC.toHomeomorph.isOpenMap.comp (ho.comp eB.symm.toHomeomorph.isOpenMap)⟩
  · have hr : range j = eB '' range i := by
      rw [show (j : D → E) = eB ∘ i ∘ eA.symm from rfl, range_comp, range_comp,
        eA.symm.surjective.range_eq, image_univ]
    rw [hr]
    exact eB.toHomeomorph.isClosedMap _ hc
  · intro y
    obtain ⟨x, rfl⟩ := eB.surjective y
    rw [hq, ← eC.map_zero, eC.injective.eq_iff, he x]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨eA v, hj v⟩
    · rintro ⟨w, hw⟩
      obtain ⟨v, rfl⟩ := eA.surjective w
      exact ⟨v, eB.injective ((hj v).symm.trans hw)⟩

theorem assemble_fractionalCutoffRows {J : Type*} (e : A ≃L[ℂ] B)
    (S : J → Set A) (T : J → Submodule ℂ B) (l m r : J) (P : A → A → Prop)
    (hMap : ∀ j (X : Submodule ℂ A), (X : Set A) = S j → X.map e.toLinearMap = T j)
    (hPhysical : ∃ (L M R : Submodule ℂ A) (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (L : Set A) = S l ∧ (M : Set A) = S m ∧ (R : Set A) = S r ∧
      (∀ x, (i x).val = x.val) ∧ (∀ x, P (p x).val x.val) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p) :
    ∃ (L M R : Submodule ℂ A) (D : FractionalCutoffRows L M R (T l) (T m) (T r)),
      (L : Set A) = S l ∧ (M : Set A) = S m ∧ (R : Set A) = S r ∧
      (∀ x, (D.physicalInclusion x).val = x.val) ∧
      (∀ x, P (D.physicalProjection x).val x.val) ∧
      (∀ x, (D.leftMellin x).val = e x.val) ∧
      (∀ x, (D.middleMellin x).val = e x.val) ∧
      (∀ x, (D.rightMellin x).val = e x.val) := by
  obtain ⟨L, M, R, i, p, hL, hM, hR, hi, hp, hI, hC, hE, hP, hO⟩ := hPhysical
  let eL := e.ofSubmodules L (T l) (hMap l L hL)
  let eM := e.ofSubmodules M (T m) (hMap m M hM)
  let eR := e.ofSubmodules R (T r) (hMap r R hR)
  obtain ⟨j, q, hj, hq, hExact⟩ := transport_cutoff_exact i p eL eM eR hI hC hE hP hO
  let D : FractionalCutoffRows L M R (T l) (T m) (T r) :=
    ⟨i, p, eL, eM, eR, j, q, hj, hq, ⟨hI, hC, hE, hP, hO⟩, hExact⟩
  exact ⟨L, M, R, D, hL, hM, hR, hi, hp, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end Transport
end
end Masullo
