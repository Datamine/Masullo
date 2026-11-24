import GlobalOrbitalMarkushevich
import ManuscriptHeckeCharacterChart
import Mathlib.Analysis.InnerProductSpace.Dual

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical InnerProductSpace NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance manuscriptOrbitalQMeasurable : MeasurableSpace (Q F) := borel _
local instance manuscriptOrbitalQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance manuscriptOrbitalQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance manuscriptOrbitalQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance manuscriptOrbitalQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

private abbrev ω (χ : PontryaginDual (Q F)) := heckeNormOneRestriction F χ
private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I
private abbrev it (t : ℝ) : ℂ := (t : ℂ) * Complex.I

/-- The indices with actual Euler multiplicity in the original Hecke character coordinate. -/
def orbitalEulerMomentIndices (A : Finset (Place F)) (χ : PontryaginDual (Q F)) : Set (ℂ × ℕ) :=
  {i | i.2 < analyticOrderNatAt (orbitalEulerDenominator F A χ) i.1}

private theorem unramified_restriction (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    ∀ v ∈ A, (ω F χ).comp (globalSobolevFiniteUnitInclusion F v) = 1 :=
  fun v hv ↦ (globalSobolevFiniteUnitInclusion_trivial_iff F (ω F χ) χ (fun _ ↦ rfl) v).mpr (hχ v hv)

/-- Removing the Hecke height preserves the radial phase after translating the exponent. -/
theorem orbitalMomentPhase_heckeHeight (χ : PontryaginDual (Q F)) (t : ℝ)
    (ht : HasHeckeHeight F χ t) (z : ℂ) (g : Q F) :
    orbitalMomentPhase F χ z g =
      orbitalMomentPhase F (normOneEulerCharacter F (ω F χ)) (z-it t) g := by
  let r : ℂ := ↑(Real.log (ideleClassNorm F g))
  change (χ g : ℂ) * Complex.exp (z*r) =
    (normOneEulerCharacter F (ω F χ) g : ℂ) * Complex.exp ((z-it t)*r)
  rw [ht g]
  change (_ * Complex.exp (-it t*r)) * Complex.exp (z*r) = _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem heckeHeight_multiplicity (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (t : ℝ) (ht : HasHeckeHeight F χ t) (z : ℂ) :
    analyticOrderNatAt (orbitalEulerDenominator F A χ) z =
      globalWeilMomentMultiplicity F A (ω F χ) (normOneEulerCharacter F (ω F χ)) (z-it t) := by
  have h := globalWeilMomentMultiplicity_eq_eulerOrder F A (ω F χ) χ z
    (unramified_restriction F A χ hχ)
  unfold analyticOrderNatAt
  rw [← h, ENat.toNat_natCast]
  unfold globalWeilMomentMultiplicity
  congr 1
  apply Finset.filter_congr
  intro v _
  change (_ ∧ orbitalMomentPhase F χ z (globalUniformizerClass F v) = 1) ↔
    (_ ∧ orbitalMomentPhase F (normOneEulerCharacter F (ω F χ)) (z-it t)
      (globalUniformizerClass F v) = 1)
  rw [orbitalMomentPhase_heckeHeight F χ t ht]

/-- A positive Euler moment label lies over a zero of the actual reciprocal product. -/
theorem orbitalEulerMoment_zero (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (i : orbitalEulerMomentIndices F A χ) : orbitalEulerDenominator F A χ i.val.1 = 0 := by
  by_contra hz
  have h := orbitalEulerDenominator_order_eq_card F A χ i.val.1
  have hS : A.filter (fun v ↦ 1 - (χ (ideleClassMap F
      (singleFiniteIdele F v (chosenFiniteUniformizer F v))) : ℂ) *
      Complex.exp (-i.val.1 * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro v hv hzero
    apply hz
    exact Finset.prod_eq_zero hv hzero
  have hi := i.property
  change i.val.2 < (analyticOrderAt (orbitalEulerDenominator F A χ) i.val.1).toNat at hi
  rw [h, hS, Finset.card_empty, ENat.toNat_natCast] at hi
  exact (Nat.not_lt_zero _) hi

private theorem eulerMoment_re (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (i : orbitalEulerMomentIndices F A χ) : i.val.1.re = 0 :=
  orbitalEulerDenominator_zero_re F A χ (orbitalEulerMoment_zero F A χ i)

private abbrev frequencyOf (t : ℝ) (z : ℂ) : ℝ := (t-z.im)/(2*Real.pi)

private theorem zAt_frequencyOf (t : ℝ) (z : ℂ) (hz : z.re = 0) :
    zAt (frequencyOf t z) = z - it t := by
  have hπ : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hh : -2 * Real.pi * frequencyOf t z = z.im-t := by
    dsimp only [frequencyOf]
    field_simp
    ring
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_self, Complex.sub_re, hz]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, Complex.sub_im]
    exact hh

/-- Removing the Hecke height bijectively reindexes the zero-line moments. -/
def orbitalEulerMomentEquiv (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (t : ℝ) (ht : HasHeckeHeight F χ t) :
    orbitalEulerMomentIndices F A χ ≃ globalWeilMomentIndices F A (ω F χ) := by
  let f := frequencyOf t
  have hπ : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hif (ξ : ℝ) : f (zAt ξ + it t) = ξ := by
    apply (div_eq_iff hπ).mpr
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
    ring
  refine ⟨fun i ↦ ⟨(f i.val.1, i.val.2), ?_⟩, fun i ↦ ⟨(zAt i.val.1+it t,i.val.2), ?_⟩, ?_, ?_⟩
  · have hi := i.property
    change i.val.2 < analyticOrderNatAt (orbitalEulerDenominator F A χ) i.val.1 at hi
    change i.val.2 < globalWeilMomentMultiplicity F A (ω F χ)
      (normOneEulerCharacter F (ω F χ)) (zAt (f i.val.1))
    rw [zAt_frequencyOf t _ (eulerMoment_re F A χ i), ← heckeHeight_multiplicity F A χ hχ t ht]
    exact hi
  · change i.val.2 < analyticOrderNatAt (orbitalEulerDenominator F A χ) (zAt i.val.1+it t)
    rw [heckeHeight_multiplicity F A χ hχ t ht, add_sub_cancel_right]
    exact i.property
  · intro i
    apply Subtype.ext
    apply Prod.ext
    · change zAt (f i.val.1) + it t = i.val.1
      rw [zAt_frequencyOf t _ (eulerMoment_re F A χ i), sub_add_cancel]
    · rfl
  · intro i
    apply Subtype.ext
    exact Prod.ext (hif _) rfl


/-- The frequency reindexing translates each exponent by the Hecke height. -/
theorem orbitalEulerMomentEquiv_exponent (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (t : ℝ) (ht : HasHeckeHeight F χ t) (i : orbitalEulerMomentIndices F A χ) :
    zAt ((orbitalEulerMomentEquiv F A χ hχ t ht i).val.1) = i.val.1 - it t :=
  zAt_frequencyOf t i.val.1 (eulerMoment_re F A χ i)

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev H (χ : PontryaginDual (Q F)) := globalOrbitalSobolevIsotype F μ s hs (ω F χ)
private abbrev R (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :=
  globalWeilIsotypeClosedRange F μ s hs A (ω F χ)
private abbrev D (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :=
  hilbertStrongAnnihilator (R F μ s hs A χ)

local instance manuscriptOrbitalHComplete (χ : PontryaginDual (Q F)) :
    CompleteSpace (H F μ s hs χ) :=
  (globalOrbitalSobolevIsotype_isClosed F μ s hs (ω F χ)).completeSpace_coe

include hs in
/-- Corrected membership clause of Theorem 11.2.0.2, including every nonnegative degree. -/
theorem orbitalEulerMoment_mem_iff (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (i : orbitalEulerMomentIndices F A χ) :
    MemLp (orbitalSobolevMoment F χ s i.val.1 i.val.2) 2 μ ↔
      (i.val.2 : ℝ) < (s-1)/2 :=
  orbitalSobolevMoment_memLp_iff F μ χ hs (eulerMoment_re F A χ i) i.val.2

private theorem eulerMoment_admissible (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) (hA : 2 * (A.card : ℝ) ≤ s)
    (i : orbitalEulerMomentIndices F A χ) : (i.val.2 : ℝ) < (s-1)/2 := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  have hi := i.property
  change i.val.2 < analyticOrderNatAt (orbitalEulerDenominator F A χ) i.val.1 at hi
  rw [heckeHeight_multiplicity F A χ hχ t ht] at hi
  exact globalWeilMoment_admissible F s A (ω F χ) _ _ hA i.val.2 hi

private def eulerMomentVector (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (i : orbitalEulerMomentIndices F A χ) (hi : (i.val.2 : ℝ) < (s-1)/2) : H F μ s hs χ :=
  ⟨globalOrbitalMomentRieszVector F μ s hs χ i.val.1 (eulerMoment_re F A χ i) i.val.2 hi,
    globalOrbitalMomentRieszVector_mem F μ s hs χ (ω F χ) (fun _ ↦ rfl)
      i.val.1 (eulerMoment_re F A χ i) i.val.2 hi⟩

/-- Each admissible reciprocal-weight representative belongs to the positive isotype
after conjugation, for all nonnegative Sobolev degrees. -/
theorem orbitalEulerMoment_riesz_mem (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (i : orbitalEulerMomentIndices F A χ) (hi : (i.val.2 : ℝ) < (s-1)/2) :
    globalOrbitalMomentRieszVector F μ s hs χ i.val.1 (eulerMoment_re F A χ i) i.val.2 hi ∈
      globalOrbitalSobolevIsotype F μ s hs (ω F χ) :=
  (eulerMomentVector F μ s hs A χ i hi).property

private theorem eulerMomentVector_eq_canonical (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) (t : ℝ) (ht : HasHeckeHeight F χ t)
    (i : orbitalEulerMomentIndices F A χ) :
    eulerMomentVector F μ s hs A χ i (eulerMoment_admissible F s A χ hχ hA i) =
      globalWeilMomentRepresentative F μ s hs A hA (ω F χ)
        (orbitalEulerMomentEquiv F A χ hχ t ht i) := by
  let j := orbitalEulerMomentEquiv F A χ hχ t ht i
  have hz : zAt j.val.1 = i.val.1 - it t :=
    zAt_frequencyOf t i.val.1 (eulerMoment_re F A χ i)
  apply Subtype.ext
  apply ext_inner_right (𝕜 := ℂ)
  intro u
  change ⟪globalOrbitalMomentRieszVector F μ s hs χ i.val.1 (eulerMoment_re F A χ i)
    i.val.2 (eulerMoment_admissible F s A χ hχ hA i), u⟫_ℂ =
    ⟪(globalWeilMomentRepresentative F μ s hs A hA (ω F χ) j).val,u⟫_ℂ
  unfold globalWeilMomentRepresentative
  simp only [globalOrbitalMomentRieszVector_inner]
  have hj : j.val.2 = i.val.2 := rfl
  change (∫ g, u g * orbitalSobolevMoment F χ s i.val.1 i.val.2 g ∂μ) =
    ∫ g, u g * orbitalSobolevMoment F (normOneEulerCharacter F (ω F χ)) s (zAt j.val.1) j.val.2 g ∂μ
  rw [hz, hj]
  congr 1
  funext g
  let x : ℝ := (ideleClassLogNorm F g).toAdd
  change u g * (↑((1 + ‖x‖^2)^(-s/4) : ℝ) * orbitalMomentPhase F χ i.val.1 g * (x : ℂ)^i.val.2) =
    u g * (↑((1 + ‖x‖^2)^(-s/4) : ℝ) *
      orbitalMomentPhase F (normOneEulerCharacter F (ω F χ)) (i.val.1 - it t) g * (x : ℂ)^i.val.2)
  rw [orbitalMomentPhase_heckeHeight F χ t ht]

/-- A source-indexed orbital functional in the strong annihilator of the actual completed Weil range. -/
def orbitalEulerMomentFunctional (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) (i : orbitalEulerMomentIndices F A χ) : D F μ s hs A χ :=
  hilbertStrongAnnihilatorEquiv (R F μ s hs A χ)
    ⟨eulerMomentVector F μ s hs A χ i (eulerMoment_admissible F s A χ hχ hA i), by
      obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
      rw [eulerMomentVector_eq_canonical F μ s hs A χ hχ hA t ht i]
      exact globalWeilMomentRepresentative_mem_orthogonal F μ s hs A hA (ω F χ) _⟩

/-- The basis vectors are the manuscript's moment integrals in the Sobolev amplitude chart. -/
theorem orbitalEulerMomentFunctional_apply (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) (i : orbitalEulerMomentIndices F A χ)
    (u : H F μ s hs χ) :
    (orbitalEulerMomentFunctional F μ s hs A χ hχ hA i).val u =
      ∫ g, u.val g * orbitalSobolevMoment F χ s i.val.1 i.val.2 g ∂μ := by
  unfold orbitalEulerMomentFunctional
  rw [hilbertStrongAnnihilatorEquiv_apply]
  exact globalOrbitalMomentRieszVector_inner F μ s hs χ i.val.1 (eulerMoment_re F A χ i)
    i.val.2 (eulerMoment_admissible F s A χ hχ hA i) u.val


set_option maxHeartbeats 1000000 in
/-- Corrected Theorem 11.2.0.2. Every enumeration of the zero-line Euler moments
gives a Markushevich basis of the strong-dual annihilator of the actual Weil range. -/
theorem orbitalEulerMoment_markushevich {ι : Type*} [DecidableEq ι]
    (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) (a : ι ≃ orbitalEulerMomentIndices F A χ) :
    let e := orbitalEulerMomentFunctional F μ s hs A χ hχ hA ∘ a
    ∃ φ : ι → D F μ s hs A χ →L[ℂ] ℂ,
      (∀ i j, φ i (e j) = if j = i then 1 else 0) ∧
      Dense (Submodule.span ℂ (range e) : Set (D F μ s hs A χ)) ∧
      ∀ v : D F μ s hs A χ, (∀ i, φ i v = 0) → v = 0 := by
  intro e
  let W := R F μ s hs A χ
  let r (k : globalWeilMomentIndices F A (ω F χ)) : Wᗮ :=
    ⟨globalWeilMomentRepresentative F μ s hs A hA (ω F χ) k,
      globalWeilMomentRepresentative_mem_orthogonal F μ s hs A hA (ω F χ) k⟩
  obtain ⟨φ, hbi, hd, htotal⟩ := globalWeilMoment_markushevich F μ s hs A hA (ω F χ)
  obtain ⟨ψ, hbi', hd', htotal'⟩ := hilbertStrongAnnihilator_markushevich W r φ hbi hd htotal
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  let b := a.trans (orbitalEulerMomentEquiv F A χ hχ t ht)
  let T := hilbertStrongAnnihilatorEquiv W
  have he (i : ι) : e i = T (r (b i)) := by
    apply congrArg T
    apply Subtype.ext
    exact eulerMomentVector_eq_canonical F μ s hs A χ hχ hA t ht (a i)
  refine ⟨fun i ↦ ψ (b i), ?_, ?_, ?_⟩
  · intro i j
    change ψ (b i) (e j) = _
    rw [he, hbi']
    by_cases h : j = i
    · subst j
      simp
    · rw [ite_eq_right h, ite_eq_right (fun he ↦ h (b.injective he))]
  · have hrange : range e = range (T ∘ r) := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, (he i).symm⟩
      · rintro ⟨k, rfl⟩
        obtain ⟨i, rfl⟩ := b.surjective k
        exact ⟨i, he i⟩
    rw [hrange]
    exact hd'
  · intro v hv
    apply htotal' v
    intro k
    obtain ⟨i, rfl⟩ := b.surjective k
    exact hv i

/-- The original complex exponent and moment indices form a countable set. -/
theorem orbitalEulerMomentIndices_countable (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    (orbitalEulerMomentIndices F A χ).Countable := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  have hc := globalWeilMomentIndices_countable F A (ω F χ)
  letI := hc.to_subtype
  haveI : Countable (orbitalEulerMomentIndices F A χ) :=
    (orbitalEulerMomentEquiv F A χ hχ t ht).injective.countable
  exact Set.countable_coe_iff.mp inferInstance

/-- Corrected Corollary 11.2.0.5. The basis in Theorem 11.2.0.2 has
a uniform positive lower and a uniform finite upper bound in the strong-dual norm. -/
theorem orbitalEulerMoment_markushevich_normBounds (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : orbitalEulerMomentIndices F A χ,
      C⁻¹ ≤ ‖orbitalEulerMomentFunctional F μ s hs A χ hχ hA i‖ ∧
      ‖orbitalEulerMomentFunctional F μ s hs A χ hχ hA i‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := imaginaryOrbitalSobolevMoments_uniform_norm F μ hs'
  refine ⟨C, hC, fun i ↦ ?_⟩
  let hi := eulerMoment_admissible F s A χ hχ hA i
  obtain ⟨h, hh⟩ := hnorm χ i.val.1 (eulerMoment_re F A χ i) i.val.2 hi
  have he : ‖orbitalEulerMomentFunctional F μ s hs A χ hχ hA i‖ =
      ‖globalOrbitalMomentRieszVector F μ s hs χ i.val.1 (eulerMoment_re F A χ i) i.val.2 hi‖ := by
    unfold orbitalEulerMomentFunctional
    exact (hilbertStrongAnnihilatorEquiv (R F μ s hs A χ)).norm_map _
  rw [he, globalOrbitalMomentRieszVector_norm F μ s hs χ _ _ _ hi h]
  exact hh


/-- Distinct source indices give distinct functionals, so an enumeration of
the family can equally be specified by its Euler exponents and moment orders. -/
theorem orbitalEulerMomentFunctional_injective (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) :
    Injective (orbitalEulerMomentFunctional F μ s hs A χ hχ hA) := by
  obtain ⟨φ, hbi, _, _⟩ := orbitalEulerMoment_markushevich F μ s hs A χ hχ hA (Equiv.refl _)
  intro i j hij
  by_contra hn
  have h₁ := hbi i i
  have h₀ := hbi i j
  simp only [Function.comp_apply, Equiv.refl_apply, ite_true] at h₁
  simp only [Function.comp_apply, Equiv.refl_apply, ite_eq_right (Ne.symm hn)] at h₀
  exact one_ne_zero (h₁.symm.trans ((congrArg (φ i) hij).trans h₀))

set_option maxHeartbeats 1000000 in
/-- Corrected Corollary 11.2.0.5 in the strong annihilator, with the
two-sided norm collar on every enumeration of the basis. -/
theorem orbitalEulerMoment_normalized_markushevich {ι : Type*} [DecidableEq ι]
    (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (hA : 2 * (A.card : ℝ) ≤ s) (hs' : 1 < s) (a : ι ≃ orbitalEulerMomentIndices F A χ) :
    let e := orbitalEulerMomentFunctional F μ s hs A χ hχ hA ∘ a
    ∃ (C : ℝ) (φ : ι → D F μ s hs A χ →L[ℂ] ℂ),
      0 < C ∧ (∀ i, C⁻¹ ≤ ‖e i‖ ∧ ‖e i‖ ≤ C) ∧
      (∀ i j, φ i (e j) = if j = i then 1 else 0) ∧
      Dense (Submodule.span ℂ (range e) : Set (D F μ s hs A χ)) ∧
      ∀ v : D F μ s hs A χ, (∀ i, φ i v = 0) → v = 0 := by
  intro e
  obtain ⟨C, hC, hc⟩ := orbitalEulerMoment_markushevich_normBounds F μ s hs A χ hχ hA hs'
  obtain ⟨φ, hbi, hd, ht⟩ := orbitalEulerMoment_markushevich F μ s hs A χ hχ hA a
  exact ⟨C, φ, hC, fun i ↦ hc (a i), hbi, hd, ht⟩

end
end Masullo
