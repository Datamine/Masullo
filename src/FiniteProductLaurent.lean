import FinitePlaceLaurent
import LocallyConstantFiniteTensor
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open Function IsDedekindDomain NumberField
open scoped BigOperators Classical NumberField TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Coord (S : Finset (Place F)) := (w : S) → w.val.adicCompletion F
private abbrev Test (S : Finset (Place F)) : Type _ := locallyConstantTests (Coord F S)
private abbrev FullTensor (S : Finset (Place F)) :=
  ⨂[ℂ] w : S, locallyConstantTests (w.val.adicCompletion F)
private abbrev RadialTensor (S : Finset (Place F)) :=
  ⨂[ℂ] w : S, finitePlaceRadial F w.val

abbrev FiniteLaurent (S : Finset (Place F)) := AddMonoidAlgebra ℂ (S → ℤ)

variable (S : Finset (Place F))
variable (π : ∀ w : S, (w.val.adicCompletion F)ˣ)
variable (hπ : ∀ w : S, Valued.v.IsUniformizer (π w).val)

private def fullEquiv : FullTensor F S ≃ₗ[ℂ] Test F S :=
  (exists_locallyConstantTestFiniteTensorEquiv (X := fun w : Place F => w.adicCompletion F) S).choose

private theorem fullEquiv_apply (g : ∀ w : S, locallyConstantTests (w.val.adicCompletion F))
    (x : Coord F S) :
    (fullEquiv F S (⨂ₜ[ℂ] w, g w)).val x = ∏ w, (g w).val (x w) :=
  (exists_locallyConstantTestFiniteTensorEquiv (X := fun w : Place F => w.adicCompletion F)
    S).choose_spec g x

private def radialBasis :
    Module.Basis (S → ℤ) ℂ (RadialTensor F S) := by
  letI (w : S) : TopologicalSpace (locallyConstantTests (w.val.adicCompletion F)) :=
    finestLocallyConvexTopology _
  letI : TopologicalSpace (LaurentPolynomial ℂ) := finestLocallyConvexTopology _
  exact Basis.piTensorProduct fun w =>
    (AddMonoidAlgebra.basis ℤ ℂ).map (finitePlaceLaurentEquiv F w.val (π w) (hπ w)).toLinearEquiv

private theorem radialBasis_apply (n : S → ℤ) :
    radialBasis F S π hπ n = ⨂ₜ[ℂ] w, finitePlaceLaurentBall F w.val (π w) (n w) := by
  unfold radialBasis
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext w
  exact finitePlaceLaurentEquiv_monomial F w.val (π w) (hπ w) (n w)

private def laurentEquiv : FiniteLaurent F S ≃ₗ[ℂ] RadialTensor F S :=
  (AddMonoidAlgebra.basis (S → ℤ) ℂ).equiv (radialBasis F S π hπ) (Equiv.refl _)

private theorem laurentEquiv_single (n : S → ℤ) :
    laurentEquiv F S π hπ (AddMonoidAlgebra.single n 1) =
      ⨂ₜ[ℂ] w, finitePlaceLaurentBall F w.val (π w) (n w) := by
  change (laurentEquiv F S π hπ) ((AddMonoidAlgebra.basis (S → ℤ) ℂ) n) = _
  rw [laurentEquiv, Module.Basis.equiv_apply]
  exact radialBasis_apply F S π hπ n

/-- The multiplication map from multivariate Laurent monomials to products of
finite-place ball indicators. -/
def finiteLaurentToTests : FiniteLaurent F S →ₗ[ℂ] Test F S :=
  (fullEquiv F S).toLinearMap.comp
    ((PiTensorProduct.map fun w : S => (finitePlaceRadial F w.val).subtype).comp
      (laurentEquiv F S π hπ).toLinearMap)

/-- The radial projection of product tests, expressed in Laurent coordinates. -/
def finiteLaurentFromTests : Test F S →ₗ[ℂ] FiniteLaurent F S :=
  (laurentEquiv F S π hπ).symm.toLinearMap.comp
    ((PiTensorProduct.map fun w : S => finitePlaceRadialProjection F w.val (π w) (hπ w)).comp
      (fullEquiv F S).symm.toLinearMap)

theorem finiteLaurentToTests_single (n : S → ℤ) (x : Coord F S) :
    (finiteLaurentToTests F S π hπ (AddMonoidAlgebra.single n 1)).val x =
      ∏ w : S, (finitePlaceLaurentBall F w.val (π w) (n w)).val.val (x w) := by
  simp only [finiteLaurentToTests, LinearMap.comp_apply, LinearEquiv.coe_coe,
    laurentEquiv_single, PiTensorProduct.map_tprod, fullEquiv_apply]
  rfl

theorem finiteLaurentFromTests_leftInverse :
    LeftInverse (finiteLaurentFromTests F S π hπ) (finiteLaurentToTests F S π hπ) := by
  have h :
      (PiTensorProduct.map fun w : S => finitePlaceRadialProjection F w.val (π w) (hπ w)).comp
        (PiTensorProduct.map fun w : S => (finitePlaceRadial F w.val).subtype) =
      (LinearMap.id : RadialTensor F S →ₗ[ℂ] RadialTensor F S) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro g
    change PiTensorProduct.map _ (PiTensorProduct.map _ (⨂ₜ[ℂ] w, g w)) = ⨂ₜ[ℂ] w, g w
    rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext w
    exact finitePlaceRadialProjection_fixes F w.val (π w) (hπ w) (g w)
  intro P
  simp only [finiteLaurentFromTests, finiteLaurentToTests, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change (laurentEquiv F S π hπ).symm (((PiTensorProduct.map _).comp
    (PiTensorProduct.map _)) (laurentEquiv F S π hπ P)) = P
  rw [h, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- Radialization is evaluation at the tuple of equal-norm uniformizer representatives. -/
theorem finiteLaurentToTests_fromTests_apply (g : Test F S) (x : Coord F S) :
    (finiteLaurentToTests F S π hπ (finiteLaurentFromTests F S π hπ g)).val x =
      g.val (fun w => uniformizerRepresentative F w.val (π w) (hπ w) (x w)) := by
  let y : Coord F S := fun w => uniformizerRepresentative F w.val (π w) (hπ w) (x w)
  let ev (z : Coord F S) : Test F S →ₗ[ℂ] ℂ :=
    (LinearMap.proj z).comp (locallyConstantTests (Coord F S)).subtype
  let L := (ev x).comp ((finiteLaurentToTests F S π hπ).comp (finiteLaurentFromTests F S π hπ))
  have h : L.comp (fullEquiv F S).toLinearMap = (ev y).comp (fullEquiv F S).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    change (finiteLaurentToTests F S π hπ
      (finiteLaurentFromTests F S π hπ (fullEquiv F S (⨂ₜ[ℂ] w, a w)))).val x =
        (fullEquiv F S (⨂ₜ[ℂ] w, a w)).val y
    simp only [finiteLaurentToTests, finiteLaurentFromTests, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      PiTensorProduct.map_tprod, fullEquiv_apply]
    rfl
  have he := DFunLike.congr_fun h ((fullEquiv F S).symm g)
  change L g = ev y g
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using he

end
end Masullo
