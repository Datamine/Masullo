import SLocalIdelic

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev N := (ideleLogNorm F).ker
private abbrev Place := HeightOneSpectrum (𝓞 F)

variable [MeasurableSpace (N F)]

/-- The literal product of indicators in (11.3.2.2), with the same principal
multiplier and norm-one translate in both arguments. -/
def printedOrbitalSectionWeight (η : Measure (N F)) (E : Set (N F))
    (τ : Multiplicative ℝ →* Idele F) (x y : Idele F) : ℝ :=
  ∑' ξ : Fˣ, ∫ g in E,
    (range τ).indicator (fun _ ↦ (1 : ℝ)) (principalIdele F ξ * g.val * x) *
      (range τ).indicator (fun _ ↦ (1 : ℝ)) (principalIdele F ξ * g.val * y) ∂η

/-- The indicated weight vanishes off the ordinary diagonal on each
same-modulus fibre. This uses the section property alone. -/
theorem printedOrbitalSectionWeight_eq_zero_of_same_modulus (η : Measure (N F))
    (E : Set (N F)) (τ : Multiplicative ℝ →* Idele F)
    (hτ : RightInverse τ (ideleLogNorm F)) {x y : Idele F}
    (hxy : ideleLogNorm F x = ideleLogNorm F y) (hne : x ≠ y) :
    printedOrbitalSectionWeight F η E τ x y = 0 := by
  classical
  unfold printedOrbitalSectionWeight
  have hterm (ξ : Fˣ) (g : N F) :
      (range τ).indicator (fun _ ↦ (1 : ℝ)) (principalIdele F ξ * g.val * x) *
      (range τ).indicator (fun _ ↦ (1 : ℝ)) (principalIdele F ξ * g.val * y) = 0 := by
    let a := principalIdele F ξ * g.val
    by_cases hx : a * x ∈ range τ
    · have hy : a * y ∉ range τ := by
        rintro ⟨t,ht⟩
        obtain ⟨s,hs⟩ := hx
        have hst : s = t := calc
          s = ideleLogNorm F (a * x) := (hτ s).symm.trans (congrArg (ideleLogNorm F) hs)
          _ = ideleLogNorm F (a * y) := ((ideleLogNorm F).map_mul a x).trans
            ((congrArg ((ideleLogNorm F) a * ·) hxy).trans ((ideleLogNorm F).map_mul a y).symm)
          _ = t := (congrArg (ideleLogNorm F) ht).symm.trans (hτ t)
        exact hne (mul_left_cancel (hs.symm.trans (hst ▸ ht)))
      rw [indicator_of_notMem hy, mul_zero]
    · rw [indicator_of_notMem hx, zero_mul]
  simp_rw [hterm, integral_zero, tsum_zero]

/-- A divisorial indicator tests for integral units at the selected places. -/
def orbitalDivisorialIndicator (A : Finset (Place F)) (x : Idele F) : ℝ :=
  ({g : Idele F | ∀ v ∈ A, ideleOrder F g v = 0}).indicator (fun _ ↦ 1) x

omit [MeasurableSpace (N F)] in
/-- The additional late divisorial indicator in (11.3.2.3) kills the
shell difference when it tests every place already present in that shell. -/
theorem orbitalDivisorialDifference_mul_late (A B C : Finset (Place F))
    (hAB : A ⊆ B) (hBC : B ⊆ C) (g : Idele F) :
    (orbitalDivisorialIndicator F B g - orbitalDivisorialIndicator F A g) *
      orbitalDivisorialIndicator F C g = 0 := by
  classical
  by_cases hC : ∀ v ∈ C, ideleOrder F g v = 0
  · have hB : g ∈ {x : Idele F | ∀ v ∈ B, ideleOrder F x v = 0} := fun v hv ↦ hC v (hBC hv)
    have hA : g ∈ {x : Idele F | ∀ v ∈ A, ideleOrder F x v = 0} := fun v hv ↦ hB v (hAB hv)
    unfold orbitalDivisorialIndicator
    rw [indicator_of_mem hA, indicator_of_mem hB, sub_self, zero_mul]
  · have hc : g ∉ {x : Idele F | ∀ v ∈ C, ideleOrder F x v = 0} := hC
    unfold orbitalDivisorialIndicator
    rw [indicator_of_notMem hc, mul_zero]

omit [MeasurableSpace (N F)] in
private theorem orbitalDivisorialIndicator_section (A : Finset (Place F)) (t : Multiplicative ℝ) :
    orbitalDivisorialIndicator F A (ideleExpSection F t) = 1 := by
  apply indicator_of_mem
  intro v _
  apply (ideleOrder_eq_zero_iff F _ _).mpr
  have hv : (ideleExpSection F t).val.2 v = 1 :=
    congrArg (fun a : FiniteAdeleRing (𝓞 F) F ↦ a v) (ideleExpSection_components F t).2
  rw [hv, map_one]

/-- On the evaluation pairs used by (11.3.2.1), the literal indentation
kills each divisorial difference pointwise for the canonical section.
This holds for every kernel and every measure on the norm-one variable. -/
theorem printedOrbitalShellIntegrand_eq_zero (η : Measure (N F)) (E : Set (N F))
    (A B : Finset (Place F)) (K : Idele F → Idele F → ℂ)
    (t : Multiplicative ℝ) (ξ : Fˣ) (g : N F) :
    let x := ideleExpSection F t
    let y := principalIdele F ξ * g.val * x
    ((orbitalDivisorialIndicator F B y - orbitalDivisorialIndicator F A y : ℝ) : ℂ) *
      (printedOrbitalSectionWeight F η E (ideleExpSection F) x y : ℂ) * K x y = 0 := by
  intro x y
  have hmod : ideleLogNorm F x = ideleLogNorm F y := by
    have hξ : ideleLogNorm F (principalIdele F ξ) = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleNorm F (principalIdele F ξ))) = _
      rw [ideleNorm_principal, Real.log_one]
      rfl
    have hg : ideleLogNorm F g.val = 1 := g.property
    change ideleLogNorm F x = ideleLogNorm F (principalIdele F ξ * g.val * x)
    rw [map_mul, map_mul, hξ,hg,one_mul,one_mul]
  by_cases hxy : x = y
  · rw [← hxy]
    change ((orbitalDivisorialIndicator F B (ideleExpSection F t) -
      orbitalDivisorialIndicator F A (ideleExpSection F t) : ℝ) : ℂ) * _ * _ = 0
    rw [orbitalDivisorialIndicator_section, orbitalDivisorialIndicator_section, sub_self]
    simp
  · have hs : RightInverse (ideleExpSection F) (ideleLogNorm F) := by
      intro t
      change Multiplicative.ofAdd (Real.log (ideleNorm F (ideleExpSection F t))) = t
      rw [ideleNorm_expSection, Real.log_exp]
      rfl
    rw [printedOrbitalSectionWeight_eq_zero_of_same_modulus F η E (ideleExpSection F) hs hmod hxy]
    simp

/-- Consequently every integrated shell using the printed weight and the
canonical section is zero, even after inserting any auxiliary cutoff. -/
theorem printedOrbitalShellIntegral_eq_zero [MeasurableSpace (Multiplicative ℝ)]
    (η : Measure (N F)) (E : Set (N F)) (dt : Measure (Multiplicative ℝ))
    (A B : Finset (Place F)) (K : Idele F → Idele F → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
      let x := ideleExpSection F t
      let y := principalIdele F ξ * g.val * x
      ((orbitalDivisorialIndicator F B y - orbitalDivisorialIndicator F A y : ℝ) : ℂ) *
        (printedOrbitalSectionWeight F η E (ideleExpSection F) x y : ℂ) * K x y ∂η ∂dt) = 0 := by
  simp only [printedOrbitalShellIntegrand_eq_zero, integral_zero, tsum_zero]

end
end Masullo
