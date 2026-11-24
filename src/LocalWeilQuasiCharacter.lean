import PrintedComplexWeilReference

open Filter IsDedekindDomain MeasureTheory NumberField Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

/-- The local eigenspace in terms of an actual archimedean quasi-character. -/
def archWeilQuasiEigenspace (V : Type*) [NormedField V] [NormedAlgebra ℝ V]
    (c : Vˣ →ₜ* ℂ) : Submodule ℂ (StrongDual ℂ 𝓢(V, ℂ)) where
  carrier := {T | ∀ u f, T (archSchwartzDilation u f) = c u * T f}
  zero_mem' := by intro u f; simp
  add_mem' {T U} hT hU := by
    intro u f
    change T (archSchwartzDilation u f) + U (archSchwartzDilation u f) =
      c u * (T f + U f)
    rw [hT u f, hU u f, mul_add]
  smul_mem' b T hT := by
    intro u f
    change b * T (archSchwartzDilation u f) = c u * (b * T f)
    rw [hT u f, mul_left_comm]

theorem realWeilQuasiEigenspace_finrank (c : ℝˣ →ₜ* ℂ) :
    Module.finrank ℂ (archWeilQuasiEigenspace ℝ c) = 1 := by
  obtain ⟨p, hp, _⟩ := existsUnique_realUnits_quasiCharacter_parameters c
  have h (u : ℝˣ) : c u = realArchUnitWeight p.2.val p.1 u := by
    rw [hp, realArchUnitWeight, Real.norm_eq_abs]
    rcases lt_or_gt_of_ne u.ne_zero with h | h
    · simp [h, h.not_gt]
    · simp [h, h.not_gt]
  have he : archWeilQuasiEigenspace ℝ c = realWeilEigenspace p.2.val p.1 := by
    ext T
    change (∀ u f, T (archSchwartzDilation u f) = c u * T f) ↔ _
    simp_rw [h]
    rfl
  rw [he]
  exact realWeilEigenspace_finrank _ _

theorem complexWeilQuasiEigenspace_finrank (c : ℂˣ →ₜ* ℂ) :
    Module.finrank ℂ (archWeilQuasiEigenspace ℂ c) = 1 := by
  obtain ⟨p, hp, _⟩ := existsUnique_complexUnits_quasiCharacter_parameters c
  have he : archWeilQuasiEigenspace ℂ c = complexWeilEigenspace p.2 p.1 := by
    ext T
    change (∀ u f, T (archSchwartzDilation u f) = c u * T f) ↔ _
    simp_rw [hp]
    rfl
  rw [he]
  exact complexWeilEigenspace_finrank _ _

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev E := locallyConstantTests (K F v)
private abbrev Phase := PontryaginDual (K F v)ˣ

local instance : TopologicalSpace (E F v) := finestLocallyConvexTopology _
variable [MeasurableSpace (K F v)ˣ] [BorelSpace (K F v)ˣ]
variable (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]

def finiteWeilQuasiEigenspace (c : (K F v)ˣ →ₜ* ℂ) :
    Submodule ℂ (StrongDual ℂ (E F v)) where
  carrier := {T | ∀ u f, T (locallyConstantTestTranslate (K F v) u f) = c u * T f}
  zero_mem' := by intro u f; simp
  add_mem' {T U} hT hU := by
    intro u f
    change T (locallyConstantTestTranslate _ u f) + U (locallyConstantTestTranslate _ u f) =
      c u * (T f + U f)
    rw [hT u f, hU u f, mul_add]
  smul_mem' b T hT := by
    intro u f
    change b * T (locallyConstantTestTranslate _ u f) = c u * (b * T f)
    rw [hT u f, mul_left_comm]

include μ in
theorem finiteWeilQuasiEigenspace_finrank (c : (K F v)ˣ →ₜ* ℂ) :
    Module.finrank ℂ (finiteWeilQuasiEigenspace F v c) = 1 := by
  obtain ⟨χ, z, _, h, _⟩ := finiteZeta_represents_quasiCharacter F v c
  have he : finiteWeilQuasiEigenspace F v c = finiteWeilEigenspace F v χ z := by
    ext T
    change (∀ u f, T (locallyConstantTestTranslate (K F v) u f) = c u * T f) ↔ _
    simp_rw [h]
    rfl
  rw [he]
  exact finiteWeilEigenspace_finrank F v μ χ z

/-- The entire lift descends along the finite-place quasi-character cylinder. -/
theorem finiteWeilNormalizedDistribution_eq_of_fixed_phase_twist_eq (χ : Phase F v) (z w : ℂ)
    (he : ∀ u, ((χ u : ℂ) * finiteZetaWeight F v z u) =
      (χ u : ℂ) * finiteZetaWeight F v w u) :
    finiteWeilNormalizedDistribution F v μ χ z = finiteWeilNormalizedDistribution F v μ χ w := by
  have hcov (u : (K F v)ˣ) (f : E F v) :
      finiteWeilNormalizedDistribution F v μ χ z (locallyConstantTestTranslate (K F v) u f) =
      ((χ u : ℂ) * finiteZetaWeight F v w u) * finiteWeilNormalizedDistribution F v μ χ z f :=
    (finiteWeilNormalizedDistribution_translate F v μ χ z u f).trans
      (congrArg (· * finiteWeilNormalizedDistribution F v μ χ z f) (he u))
  have h := finiteWeilEigen_distribution_eq F v μ χ w (finiteWeilNormalizedDistribution F v μ χ z) hcov
  have h1 : finiteWeilNormalizedDistribution F v μ χ z (finiteWeilNormalizedTest F v χ) = 1 :=
    finiteWeilNormalizedDistribution_reference F v μ χ z
  rw [h1, one_smul] at h
  exact h

/-- The meromorphic strong-dual representative of the finite local Tate distribution. -/
def finiteWeilZetaDistribution (χ : Phase F v) (z : ℂ) : StrongDual ℂ (E F v) :=
  ((μ.real (finitePlaceIntegralUnits F v) : ℂ) / finiteZetaWeilMultiplier F v χ z) •
    finiteWeilNormalizedDistribution F v μ χ z

/-- At regular parameters the same strong-dual identity represents the actual
finite zeta continuation on every test at once. -/
theorem finiteWeilZetaDistribution_apply (χ : Phase F v) (z : ℂ)
    (hz : finiteZetaWeilMultiplier F v χ z ≠ 0) (f : E F v) :
    finiteWeilZetaDistribution F v μ χ z f = finiteZetaContinuation F v μ χ f z := by
  have hm : (μ.real (finitePlaceIntegralUnits F v) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v μ).ne'
  by_cases h : finiteZetaUnramified F v χ
  · have hn : finiteZetaRatio F v χ z ≠ 1 := by
      intro he
      apply hz
      simp [finiteZetaWeilMultiplier, h, he]
    simp only [finiteWeilZetaDistribution, finiteWeilNormalizedDistribution,
      finiteZetaWeilMultiplier, dite_eq_left h, ite_eq_left h]
    change (_ / finiteZetaDenominator F v χ z) *
      ((_ : ℂ)⁻¹ * finiteZetaClearedDistribution F v μ χ z f) = _
    rw [← finiteZetaClearedDistribution_recovers F v μ χ z hn f]
    change _ = _ / finiteZetaDenominator F v χ z
    field_simp
  · simp only [finiteWeilZetaDistribution, finiteWeilNormalizedDistribution,
      finiteZetaWeilMultiplier, dite_eq_right h, ite_eq_right h]
    change (_ / 1) * ((_ : ℂ)⁻¹ * finiteZetaContinuation F v μ χ f z) = _
    rw [div_one, ← mul_assoc, mul_inv_cancel₀ hm, one_mul]

/-- The finite local zeta identity holds on a single punctured neighborhood
simultaneously for all tests. -/
theorem finiteWeilZetaDistribution_germ_apply (χ : Phase F v) (c : ℂ) :
    ∀ᶠ z in 𝓝[≠] c, ∀ f : E F v,
      finiteWeilZetaDistribution F v μ χ z f = finiteZetaContinuation F v μ χ f z := by
  let D := finiteZetaWeilMultiplier F v χ
  have hA : AnalyticOnNhd ℂ D Set.univ := finiteZetaWeilMultiplier_analytic F v χ
  have hne : D 1 ≠ 0 := by
    by_cases h : finiteZetaUnramified F v χ
    · simpa only [D, finiteZetaWeilMultiplier, ite_eq_left h, finiteZetaDenominator] using
        finiteZetaDenominator_ne_zero_of_pos F v χ 1 (by simp)
    · simp [D, finiteZetaWeilMultiplier, h]
  have hpunctured : ∀ᶠ z in 𝓝[≠] c, D z ≠ 0 := by
    rcases (hA c trivial).eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · exact (hne (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ c) hz (Set.mem_univ 1))).elim
    · exact hz
  filter_upwards [hpunctured] with z hz
  exact finiteWeilZetaDistribution_apply F v μ χ z hz

end
end Masullo
