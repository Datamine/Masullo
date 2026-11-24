import FiniteProductLaurent
import SLocalBruhatTailTensor

open Function IsDedekindDomain NumberField Topology
open scoped BigOperators Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Test (S : Finset (Place F)) : Type _ := sLocalBruhatImage F S
private abbrev Coord (S : Finset (Place F)) := (w : S) → w.val.adicCompletion F

variable {S T : Finset (Place F)} (hST : S ⊆ T)

private def oldCoordinates (x : SAdeles F T) : SAdeles F S :=
  (x.1, fun w => x.2 ⟨w.val, hST w.property⟩)

private def newCoordinates (x : SAdeles F T) : Coord F (T \ S) :=
  fun w => x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩

/-- The tests invariant under the units at newly adjoined places, expressed
as constancy on the orbits of fixed norms in the new coordinates. -/
def sLocalBruhatRelativeRadial : Submodule ℂ (Test F T) where
  carrier := {f | ∀ x y : SAdeles F T, oldCoordinates F hST x = oldCoordinates F hST y →
    (∀ w : (T \ S : Finset _), ‖newCoordinates F x w‖ = ‖newCoordinates F y w‖) →
      sLocalBruhatRestriction F T f.val x = sLocalBruhatRestriction F T f.val y}
  zero_mem' := by
    change ∀ (x y : SAdeles F T), _ → _ → sLocalBruhatRestriction F T 0 x = _
    intros
    rw [map_zero]
    rfl
  add_mem' := by
    intro f g hf hg x y h hnorm
    change sLocalBruhatRestriction F T (f.val + g.val) x =
      sLocalBruhatRestriction F T (f.val + g.val) y
    simp only [map_add, Pi.add_apply, hf x y h hnorm, hg x y h hnorm]
  smul_mem' := by
    intro c f hf x y h hnorm
    change sLocalBruhatRestriction F T (c • f.val) x = sLocalBruhatRestriction F T (c • f.val) y
    simp only [map_smul, Pi.smul_apply, hf x y h hnorm]

/-- Multiply the new coordinates by local units and leave the old ones fixed. -/
def relativeUnitMultiply (u : ∀ w : (T \ S : Finset _), (w.val.adicCompletion F)ˣ)
    (x : SAdeles F T) : SAdeles F T :=
  (x.1, fun w => if hw : w.val ∈ S then x.2 w else
    let i : (T \ S : Finset _) := ⟨w.val, Finset.mem_sdiff.mpr ⟨w.property, hw⟩⟩
    (u i).val * x.2 w)

theorem sLocalBruhatRelativeRadial_iff_units (f : Test F T) :
    f ∈ sLocalBruhatRelativeRadial F hST ↔
      ∀ (u : ∀ w : (T \ S : Finset _), (w.val.adicCompletion F)ˣ),
        (∀ w, ‖(u w).val‖ = 1) → ∀ x : SAdeles F T,
        sLocalBruhatRestriction F T f.val (relativeUnitMultiply F u x) =
          sLocalBruhatRestriction F T f.val x := by
  constructor
  · intro hf u hu x
    apply hf (relativeUnitMultiply F u x) x
    · refine Prod.ext rfl (funext fun w => ?_)
      exact dite_eq_left w.property
    · intro w
      change ‖(if hw : w.val ∈ S then _ else _)‖ = ‖newCoordinates F x w‖
      rw [dite_eq_right (Finset.mem_sdiff.mp w.property).2]
      change ‖(u w).val * newCoordinates F x w‖ = ‖newCoordinates F x w‖
      rw [norm_mul, hu, one_mul]
  · intro hf x y hxy hn
    have h (w : (T \ S : Finset _)) :
        ∃ u : (w.val.adicCompletion F)ˣ, ‖u.val‖ = 1 ∧
          u.val * newCoordinates F y w = newCoordinates F x w := by
      let a := newCoordinates F x w
      let b := newCoordinates F y w
      have hab : ‖a‖ = ‖b‖ := hn w
      by_cases hb : b = 0
      · have ha : a = 0 := norm_eq_zero.mp (by simpa [hb] using hab)
        exact ⟨1, norm_one, by change 1 * b = a; rw [ha, hb, mul_zero]⟩
      · have ha : a ≠ 0 := fun ha => hb (norm_eq_zero.mp (by simpa [ha] using hab.symm))
        refine ⟨Units.mk0 (a / b) (div_ne_zero ha hb), ?_, div_mul_cancel₀ _ hb⟩
        change ‖a / b‖ = 1
        rw [norm_div, hab, div_self (norm_ne_zero_iff.mpr hb)]
    choose u hu huv using h
    have he : relativeUnitMultiply F u y = x := by
      refine Prod.ext (congrArg (fun z : SAdeles F S => z.1) hxy).symm (funext fun w => ?_)
      change (if hw : w.val ∈ S then y.2 w else _) = x.2 w
      split_ifs with hw
      · exact (congrFun (congrArg Prod.snd hxy) ⟨w.val, hw⟩).symm
      · exact huv ⟨w.val, Finset.mem_sdiff.mpr ⟨w.property, hw⟩⟩
    exact he ▸ hf u hu y

private theorem restriction_injective :
    Injective ((sLocalBruhatRestriction F T).comp (sLocalBruhatImage F T).subtype) := by
  intro f g h
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  change GlobalBruhat.evaluation F a f.val = GlobalBruhat.evaluation F a g.val
  rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatRestriction_reconstruct]
  exact congrArg (fun k : SAdeles F T → ℂ => k (sAdelesProjection F T a) * _) h

variable (π : ∀ w : (T \ S : Finset _), (w.val.adicCompletion F)ˣ)
variable (hπ : ∀ w : (T \ S : Finset _), Valued.v.IsUniformizer (π w).val)

private def relativeRepresentative (x : SAdeles F T) : SAdeles F T :=
  (x.1, fun w => if hw : w.val ∈ S then x.2 w else
    let i : (T \ S : Finset _) := ⟨w.val, Finset.mem_sdiff.mpr ⟨w.property, hw⟩⟩
    uniformizerRepresentative F w.val (π i) (hπ i) (x.2 w))

private theorem old_relativeRepresentative (x : SAdeles F T) :
    oldCoordinates F hST (relativeRepresentative F π hπ x) = oldCoordinates F hST x := by
  refine Prod.ext rfl (funext fun w => ?_)
  exact dite_eq_left w.property

private theorem new_relativeRepresentative (x : SAdeles F T) (w : (T \ S : Finset _)) :
    newCoordinates F (relativeRepresentative F π hπ x) w =
      uniformizerRepresentative F w.val (π w) (hπ w) (newCoordinates F x w) := by
  exact dite_eq_right (Finset.mem_sdiff.mp w.property).2

private theorem relativeRepresentative_congr {x y : SAdeles F T}
    (h : oldCoordinates F hST x = oldCoordinates F hST y)
    (hnorm : ∀ w, ‖newCoordinates (S := S) F x w‖ = ‖newCoordinates F y w‖) :
    relativeRepresentative F π hπ x = relativeRepresentative F π hπ y := by
  refine Prod.ext (congrArg (fun z : SAdeles F S => z.1) h) (funext fun w => ?_)
  change (if hw : w.val ∈ S then x.2 w else _) = (if hw : w.val ∈ S then y.2 w else _)
  split_ifs with hw
  · exact congrFun (congrArg Prod.snd h) ⟨w.val, hw⟩
  · let i : (T \ S : Finset _) := ⟨w.val, Finset.mem_sdiff.mpr ⟨w.property, hw⟩⟩
    exact uniformizerRepresentative_eq_of_norm_eq F w.val (π i) (hπ i) (hnorm i)

private abbrev H := locallyConstantTests (Coord F (T \ S))
private abbrev P := FiniteLaurent F (T \ S)

include hπ in
set_option maxHeartbeats 1000000 in
/-- Corrected Lemma 6.1.2.2(2). For the inductive tensor topology,
the canonical Laurent monomials give a unique linear homeomorphism
onto the relative unit invariants. -/
theorem sLocalBruhatRelativeLaurent :
    letI : TopologicalSpace (P (S := S) (T := T) F) := finestLocallyConvexTopology _
    letI : TopologicalSpace (Test F S ⊗[ℂ] P (S := S) (T := T) F) := inductiveTensorTopology _ _
    ∃! e : (Test F S ⊗[ℂ] P (S := S) (T := T) F) ≃L[ℂ] sLocalBruhatRelativeRadial F hST,
      ∀ (f : Test F S) (n : (T \ S : Finset _) → ℤ) (x : SAdeles F T),
        sLocalBruhatRestriction F T (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single n 1)).val.val x =
          sLocalBruhatRestriction F S f.val (oldCoordinates F hST x) *
            ∏ w : (T \ S : Finset _),
              (finitePlaceLaurentBall F w.val (π w) (n w)).val.val (newCoordinates F x w) := by
  let A := Test F S
  let B : Type _ := H (S := S) (T := T) F
  let C := P (S := S) (T := T) F
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace C := finestLocallyConvexTopology C
  letI : PolynormableSpace ℂ B := (finest_withSeminorms B).toPolynormableSpace
  letI : PolynormableSpace ℂ C := (finest_withSeminorms C).toPolynormableSpace
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  letI : IsTopologicalAddGroup C := (finest_withSeminorms C).topologicalAddGroup
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : TopologicalSpace (A ⊗[ℂ] C) := inductiveTensorTopology A C
  obtain ⟨⟨E, hE⟩, _⟩ := sLocalBruhatDifferenceTensor F hST
  let L := finiteLaurentToTests F (T \ S) π hπ
  let R := finiteLaurentFromTests F (T \ S) π hπ
  let i : (A ⊗[ℂ] C) →L[ℂ] (A ⊗[ℂ] B) :=
    ⟨L.lTensor A, continuous_inductiveTensor_lTensor (A := A) (B := C) (C := B) L
      (finest_linear_continuous (E := C) (F := B) L)⟩
  let p : (A ⊗[ℂ] B) →L[ℂ] (A ⊗[ℂ] C) :=
    ⟨R.lTensor A, continuous_inductiveTensor_lTensor (A := A) (B := B) (C := C) R
      (finest_linear_continuous (E := B) (F := C) R)⟩
  have hi (f : A) (g : C) : i (f ⊗ₜ[ℂ] g) = f ⊗ₜ[ℂ] L g := rfl
  have hp (f : A) (g : B) : p (f ⊗ₜ[ℂ] g) = f ⊗ₜ[ℂ] R g := rfl
  have hleft : p.toLinearMap.comp i.toLinearMap = LinearMap.id := by
    apply TensorProduct.ext'
    intro f g
    change p (i (f ⊗ₜ[ℂ] g)) = f ⊗ₜ[ℂ] g
    rw [hi, hp, finiteLaurentFromTests_leftInverse F (T \ S) π hπ g]
  let I := E.toContinuousLinearMap.comp i
  let Q := p.comp E.symm.toContinuousLinearMap
  have hproj (f : Test F T) (x : SAdeles F T) :
      sLocalBruhatRestriction F T (I (Q f)).val x =
        sLocalBruhatRestriction F T f.val (relativeRepresentative F π hπ x) := by
    let ev (y : SAdeles F T) : Test F T →ₗ[ℂ] ℂ :=
      (LinearMap.proj y).comp ((sLocalBruhatRestriction F T).comp (sLocalBruhatImage F T).subtype)
    have h : (ev x).comp (E.toLinearEquiv.toLinearMap.comp (i.toLinearMap.comp p.toLinearMap)) =
        (ev (relativeRepresentative F π hπ x)).comp E.toLinearEquiv.toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      change sLocalBruhatRestriction F T (E (i (p (a ⊗ₜ[ℂ] b)))).val x =
        sLocalBruhatRestriction F T (E (a ⊗ₜ[ℂ] b)).val (relativeRepresentative F π hπ x)
      rw [hp, hi, hE, hE]
      change (sLocalBruhatRestriction F S a.val (oldCoordinates F hST x)) * (L (R b)).val (newCoordinates F x) =
        sLocalBruhatRestriction F S a.val (oldCoordinates F hST (relativeRepresentative F π hπ x)) *
          b.val (newCoordinates F (relativeRepresentative F π hπ x))
      rw [old_relativeRepresentative, finiteLaurentToTests_fromTests_apply]
      congr 1
      exact congrArg b.val (funext fun w => (new_relativeRepresentative F π hπ x w).symm)
    have hz := DFunLike.congr_fun h (E.symm f)
    change ev x (E (i (p (E.symm f)))) =
      ev (relativeRepresentative F π hπ x) (E (E.symm f)) at hz
    rw [E.apply_symm_apply] at hz
    exact hz
  have hQI (u : A ⊗[ℂ] C) : Q (I u) = u := by
    change p (E.symm (E (i u))) = u
    rw [E.symm_apply_apply]
    exact DFunLike.congr_fun hleft u
  have hmem (u : A ⊗[ℂ] C) : I u ∈ sLocalBruhatRelativeRadial F hST := by
    intro x y hxy hn
    have hx := hproj (I u) x
    have hy := hproj (I u) y
    rw [hQI] at hx hy
    exact hx.trans ((congrArg (sLocalBruhatRestriction F T (I u).val)
      (relativeRepresentative_congr F hST π hπ hxy hn)).trans hy.symm)
  have hIQ (u : sLocalBruhatRelativeRadial F hST) : I (Q u.val) = u.val := by
    apply restriction_injective F (T := T)
    funext x
    change sLocalBruhatRestriction F T (I (Q u.val)).val x = sLocalBruhatRestriction F T u.val.val x
    rw [hproj]
    exact u.property _ _ (old_relativeRepresentative F hST π hπ x) (fun w => by
      rw [new_relativeRepresentative, norm_uniformizerRepresentative])
  let j : (A ⊗[ℂ] C) →L[ℂ] sLocalBruhatRelativeRadial F hST :=
    ⟨I.toLinearMap.codRestrict _ hmem, I.continuous.subtype_mk _⟩
  let q : sLocalBruhatRelativeRadial F hST →L[ℂ] (A ⊗[ℂ] C) :=
    ⟨Q.toLinearMap.comp (sLocalBruhatRelativeRadial F hST).subtype,
      Q.continuous.comp continuous_subtype_val⟩
  let e : (A ⊗[ℂ] C) ≃L[ℂ] sLocalBruhatRelativeRadial F hST :=
    ⟨LinearEquiv.ofLinear j.toLinearMap q.toLinearMap (LinearMap.ext fun x => Subtype.ext (hIQ x))
      (LinearMap.ext hQI), j.continuous, q.continuous⟩
  have he (f : A) (n : (T \ S : Finset _) → ℤ) (x : SAdeles F T) :
      sLocalBruhatRestriction F T (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single n 1)).val.val x =
        sLocalBruhatRestriction F S f.val (oldCoordinates F hST x) *
          ∏ w : (T \ S : Finset _),
            (finitePlaceLaurentBall F w.val (π w) (n w)).val.val (newCoordinates F x w) := by
    change sLocalBruhatRestriction F T (E (i (f ⊗ₜ[ℂ] AddMonoidAlgebra.single n 1))).val x = _
    rw [hi, hE]
    exact congrArg (_ * ·) (finiteLaurentToTests_single F (T \ S) π hπ n (newCoordinates F x))
  refine ⟨e, he, ?_⟩
  intro e' he'
  suffices h : e'.toLinearEquiv.toLinearMap = e.toLinearEquiv.toLinearMap from
    ContinuousLinearEquiv.ext (funext fun u => DFunLike.congr_fun h u)
  apply TensorProduct.ext'
  intro f
  have hB : e'.toLinearEquiv.toLinearMap.comp (TensorProduct.mk ℂ A C f) =
      e.toLinearEquiv.toLinearMap.comp (TensorProduct.mk ℂ A C f) := by
    apply (AddMonoidAlgebra.basis ((T \ S : Finset _) → ℤ) ℂ).ext
    intro n
    apply Subtype.ext
    apply restriction_injective F (T := T)
    funext x
    exact (he' f n x).trans (he f n x).symm
  intro g
  exact DFunLike.congr_fun hB g

end
end Masullo
