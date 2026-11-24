import SLocalWeilFamily

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev Θ := SLocalThetaQuotient F S
private abbrev M := (sLocalThetaOperator F S).ker
private abbrev Q := SIdeleQuotient F S
private abbrev Characters := PontryaginDual (SLocalThetaNormOne F S)

/-- Every S-local eigenfunctional is determined by its Gaussian reference value. -/
theorem sLocalWeil_eq_normalized (ω : Characters F S) (z : ℂ)
    (T : StrongDual ℂ (E F S))
    (hT : ∀ g f, T (sLocalBruhatLeftTranslate F S g f) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) * T f) :
    T = T (sLocalWeilReference F S ω) • sLocalNormalizedWeil F S ω z := by
  let V := sLocalNormalizedWeil F S ω z
  let r := sLocalWeilReference F S ω
  let r₀ := sLocalWeilUnitTensor F S ω
  have hv : V r = 1 := sLocalNormalizedWeil_reference F S ω z
  have hV := sLocalWeil_stageSeparated_eval F S ω z V (sLocalNormalizedWeil_translate F S ω z)
  have hVr : V r₀ ≠ 0 := by
    intro h
    have he := hV (mixedWeilRealReference F (sLocalRealArchParameters F S ω))
      (fun v => correctedComplexWeilReference (sLocalComplexArchParameters F S ω v).2)
      (fun v => finiteWeilNormalizedTest F v.val (sLocalFiniteZetaPhases F S ω v))
    change V r = V r₀ * _ at he
    rw [hv, h, zero_mul] at he
    exact one_ne_zero he
  let c := T r₀ / V r₀
  have he : T = c • V := by
    apply sLocalWeilFunctional_eq_of_separated F S
    intro f g k
    have h₁ := sLocalWeil_stageSeparated_eval F S ω z T hT f g k
    have h₂ := hV f g k
    change _ = c * V _
    rw [h₁, h₂]
    change T r₀ * _ = c * (V r₀ * _)
    rw [← mul_assoc c, div_mul_cancel₀ _ hVr]
  have hcoef := DFunLike.congr_fun he r
  change T r = c * V r at hcoef
  rw [hv, mul_one] at hcoef
  exact he.trans (congrArg (· • V) hcoef.symm)

/-- The test-space eigenspace of an actual S-local quasi-character. -/
def sLocalWeilEigenspace (c : QuasiCharacter (Q F S)) : Submodule ℂ (StrongDual ℂ (E F S)) where
  carrier := {T | ∀ g f, T (sLocalBruhatLeftTranslate F S g f) = c (QuotientGroup.mk g) * T f}
  zero_mem' := by intro g f; simp
  add_mem' {T U} hT hU := by
    intro g f
    change T (sLocalBruhatLeftTranslate F S g f) + U (sLocalBruhatLeftTranslate F S g f) =
      c (QuotientGroup.mk g) * (T f + U f)
    rw [hT g f, hU g f, mul_add]
  smul_mem' b T hT := by
    intro g f
    change b * T (sLocalBruhatLeftTranslate F S g f) =
      c (QuotientGroup.mk g) * (b * T f)
    rw [hT g f, mul_left_comm]

/-- The transpose identifies covariance in the quotient with covariance upstairs. -/
theorem sLocalThetaTranspose_eigen_iff (c : QuasiCharacter (Q F S)) (T : StrongDual ℂ (Θ F S)) :
    sLocalThetaTranspose F S T ∈ sLocalWeilEigenspace F S c ↔
      ∀ q f, T (sLocalThetaTranslate F S q f) = c q * T f := by
  constructor
  · intro h q x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨f, rfl⟩ := (M F S).mkQ_surjective x
    change T (sLocalThetaTranslateIdeles F S g (Submodule.Quotient.mk f)) = _
    rw [sLocalThetaTranslateIdeles_mk]
    exact h g f
  · intro h g f
    change T (Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S g f)) = _
    rw [← sLocalThetaTranslateIdeles_mk]
    exact h (QuotientGroup.mk g) (Submodule.Quotient.mk f)

def sLocalThetaWeilEigenspace (c : QuasiCharacter (Q F S)) :
    Submodule ℂ (StrongDual ℂ (Θ F S)) :=
  (sLocalWeilEigenspace F S c).comap (sLocalThetaTranspose F S).toLinearMap

private theorem sLocalWeil_generator (c : QuasiCharacter (Q F S)) :
    ∃ (r : E F S) (A : sLocalWeilEigenspace F S c) (B : sLocalThetaWeilEigenspace F S c),
      A.val r = 1 ∧ sLocalThetaTranspose F S B.val = A.val ∧
      ∀ T : sLocalWeilEigenspace F S c, T = T.val r • A := by
  obtain ⟨ω, z, h, _⟩ := sLocalZetaWeight_represents F S c
  let r := sLocalWeilReference F S ω
  let A : sLocalWeilEigenspace F S c :=
    ⟨sLocalNormalizedWeil F S ω z, fun g f =>
      (sLocalNormalizedWeil_translate F S ω z g f).trans (by rw [h])⟩
  let B : sLocalThetaWeilEigenspace F S c :=
    ⟨sLocalThetaWeil F S ω z, by
      change sLocalThetaTranspose F S (sLocalThetaWeil F S ω z) ∈ sLocalWeilEigenspace F S c
      rw [sLocalThetaWeil_transpose]
      exact A.property⟩
  refine ⟨r, A, B, sLocalNormalizedWeil_reference F S ω z, sLocalThetaWeil_transpose F S ω z, ?_⟩
  intro T
  apply Subtype.ext
  exact sLocalWeil_eq_normalized F S ω z T.val (fun g f => (T.property g f).trans (by rw [h]))

/-- The test-space dimension-one assertion of Theorem 5.5.1.2. -/
theorem sLocalWeilEigenspace_finrank (c : QuasiCharacter (Q F S)) :
    Module.finrank ℂ (sLocalWeilEigenspace F S c) = 1 := by
  obtain ⟨r, A, _, hr, _, hA⟩ := sLocalWeil_generator F S c
  let e : sLocalWeilEigenspace F S c ≃ₗ[ℂ] ℂ :=
    { toFun := fun T => T.val r
      invFun := fun b => b • A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun T => (hA T).symm
      right_inv := fun b => by
        change b * A.val r = b
        rw [hr, mul_one] }
  exact e.finrank_eq.trans (Module.finrank_self ℂ)

/-- Every continuous S-local eigendistribution descends, uniquely, to the
actual theta quotient for its quasi-character. -/
theorem sLocalThetaWeil_existsUnique_lift (c : QuasiCharacter (Q F S))
    (T : StrongDual ℂ (E F S)) (hT : T ∈ sLocalWeilEigenspace F S c) :
    ∃! U : StrongDual ℂ (Θ F S), sLocalThetaTranspose F S U = T ∧ U ∈ sLocalThetaWeilEigenspace F S c := by
  obtain ⟨r, A, B, _, hB, hA⟩ := sLocalWeil_generator F S c
  let U := T r • B
  have hU : sLocalThetaTranspose F S U.val = T := by
    change sLocalThetaTranspose F S (T r • B.val) = T
    rw [map_smul, hB]
    exact congrArg Subtype.val (hA ⟨T, hT⟩).symm
  refine ⟨U.val, ⟨hU, U.property⟩, fun W hW => ?_⟩
  exact sLocalThetaTranspose_injective F S (hW.1.trans hU.symm)

/-- The S-local transpose is an isomorphism on each pair of eigenspaces. -/
def sLocalThetaWeilEigenspace_equiv (c : QuasiCharacter (Q F S)) :
    sLocalThetaWeilEigenspace F S c ≃ₗ[ℂ] sLocalWeilEigenspace F S c := by
  let L : sLocalThetaWeilEigenspace F S c →ₗ[ℂ] sLocalWeilEigenspace F S c :=
    ((sLocalThetaTranspose F S).toLinearMap.comp (sLocalThetaWeilEigenspace F S c).subtype).codRestrict
      (sLocalWeilEigenspace F S c) fun U => U.property
  apply LinearEquiv.ofBijective L
  constructor
  · intro U V h
    exact Subtype.ext (sLocalThetaTranspose_injective F S (congrArg Subtype.val h))
  · intro T
    obtain ⟨U, hU, _⟩ := sLocalThetaWeil_existsUnique_lift F S c T.val T.property
    exact ⟨⟨U, hU.2⟩, Subtype.ext hU.1⟩

theorem sLocalThetaWeilEigenspace_finrank (c : QuasiCharacter (Q F S)) :
    Module.finrank ℂ (sLocalThetaWeilEigenspace F S c) = 1 :=
  (sLocalThetaWeilEigenspace_equiv F S c).finrank_eq.trans (sLocalWeilEigenspace_finrank F S c)

end
end Masullo
