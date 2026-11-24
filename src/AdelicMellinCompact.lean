import ThetaMellinQuotients

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Characters := PontryaginDual (K F)
local instance adelicMellinCompact_measurable : MeasurableSpace (K F) := borel _
local instance adelicMellinCompact_borel : BorelSpace (K F) := ⟨rfl⟩

/-- The parameter set used by global compact convergence. Only the two
possible poles of the trivial character are deleted. -/
def globalMellinRegularSet : Set (Characters F × ℂ) :=
  {p | p.1 = 1 → p.2 ≠ 0 ∧ p.2 ≠ 1}

private theorem globalZetaContinued_nontrivial_seminorm_bound (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : Characters F) (hω : ω ≠ 1) {T : Set ℂ} (hT : IsCompact T) :
    ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
      ∀ f : GlobalBruhat F, ∀ z ∈ T, ‖globalZetaContinued F ν f
        (compactIdeleClassCharacter F ω) 0 z‖ ≤ p f := by
  let χ := compactIdeleClassCharacter F ω
  let χ' := compactIdeleClassCharacter F ω⁻¹
  let A := GlobalBruhat.fourier F
  have ha : (∫ k : K F, (χ k.val : ℂ) ∂ν) = 0 := by
    exact (compactIdeleClassCharacter_integral F ν ω).trans (ite_eq_right hω)
  obtain ⟨B, hB⟩ := hT.exists_bound_of_continuousOn Complex.continuous_re.continuousOn
  obtain ⟨p, hp, hP⟩ := thetaZetaUpper_seminorm_bound F ν χ
    (compactIdeleClassCharacter_unitary F ω) B
  obtain ⟨r, hr, hR⟩ := thetaZetaUpper_seminorm_bound F ν χ'
    (compactIdeleClassCharacter_unitary F ω⁻¹) (1 + B)
  refine ⟨p + r.comp A.toLinearMap, hp.add (hr.comp A.continuous), fun f z hz => ?_⟩
  have hb₀ : z.re ≤ B := (le_abs_self _).trans (hB z hz)
  have hb₁ : (1 - z).re ≤ 1 + B := by
    rw [Complex.sub_re, Complex.one_re, sub_eq_add_neg]
    exact add_le_add_right ((neg_le_abs _).trans (hB z hz)) _
  change ‖globalZetaContinued F ν f χ 0 z‖ ≤ p f + r (A f)
  rw [show globalZetaContinued F ν f χ 0 z =
      thetaZetaUpper F ν f χ z + thetaZetaUpper F ν (A f) χ' (1 - z) by
    unfold globalZetaContinued
    rw [← show χ' = χ⁻¹ from compactIdeleClassCharacter_inv F ω, ha]
    simp only [A, zero_mul, zero_div, add_zero, sub_zero]]
  exact (norm_add_le _ _).trans (add_le_add (hP f z hb₀) (hR (A f) (1 - z) hb₁))

private theorem isCompact_activeChart {C : Set (Characters F × ℂ)} (hC : IsCompact C)
    (ω : Characters F) : IsCompact ((fun z : ℂ => (ω, z)) ⁻¹' C) := by
  have hclosed : IsClosed ({ω} : Set (Characters F)) := isClosed_singleton
  have h := (hC.inter_right (hclosed.preimage continuous_fst)).image continuous_snd
  convert h using 1
  ext z
  change (ω, z) ∈ C ↔ _
  constructor
  · intro hz
    exact ⟨(ω, z), ⟨hz, mem_singleton _⟩, rfl⟩
  · rintro ⟨⟨ω', z'⟩, ⟨hz, hω'⟩, rfl⟩
    change ω' = ω at hω'
    exact hω' ▸ hz

/-- One continuous seminorm bounds the continued global Mellin transform on
every compact parameter set in its regular domain. -/
theorem globalContinuedMellin_compact_seminorm (ν : Measure (K F)) [ν.IsHaarMeasure]
    {C : Set (Characters F × ℂ)} (hC : IsCompact C) (hreg : C ⊆ globalMellinRegularSet F) :
    ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
      ∀ f : GlobalBruhat F, ∀ x ∈ C, ‖globalContinuedMellinEval F ν x.1 x.2 f‖ ≤ p f := by
  letI : T1Space (IdeleClass F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  letI : T2Space (K F) := inferInstance
  letI := normOneIdeleClass_compact F
  letI : DiscreteTopology (Characters F) := inferInstance
  have hfib (ω : Characters F) :
      ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
        ∀ f : GlobalBruhat F, ∀ z : ℂ, (ω, z) ∈ C →
          ‖globalContinuedMellinEval F ν ω z f‖ ≤ p f := by
    let T := (fun z : ℂ => (ω, z)) ⁻¹' C
    have hT : IsCompact T := isCompact_activeChart F hC ω
    have he : ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
        ∀ f : GlobalBruhat F, ∀ z ∈ T,
          ‖globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z‖ ≤ p f := by
      by_cases hω : ω = 1
      · exact globalContinuedMellin_seminorm_bound F ν ω hT
          (fun z hz => (hreg hz hω).1) (fun z hz => (hreg hz hω).2)
      · exact globalZetaContinued_nontrivial_seminorm_bound F ν ω hω hT
    obtain ⟨p, hp, hP⟩ := he
    refine ⟨p, hp, fun f z hz => ?_⟩
    rw [globalContinuedMellinEval_apply]
    exact hP f z hz
  choose p hp hP using hfib
  let S := ((hC.image continuous_fst).finite_of_discrete).toFinset
  let P : Seminorm ℂ (GlobalBruhat F) := S.sup p
  refine ⟨P, Seminorm.continuous_finsetSup fun ω _ => hp ω, fun f x hx => ?_⟩
  have hmem : x.1 ∈ S := (Set.Finite.mem_toFinset _).mpr ⟨x, hx, rfl⟩
  exact (hP x.1 f x.2 hx).trans ((Finset.le_sup hmem : p x.1 ≤ P) f)

/-- Pointwise analyticity at every regular parameter on its character component. -/
theorem globalContinuedMellinEval_regular_analytic (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (x : Characters F × ℂ) (hx : x ∈ globalMellinRegularSet F) :
    AnalyticAt ℂ (fun z => globalContinuedMellinEval F ν x.1 z f) x.2 := by
  simp only [globalContinuedMellinEval_apply]
  by_cases he : x.1 = 1
  · exact globalZetaContinued_analyticAt F ν f _ (compactIdeleClassCharacter_unitary F x.1) 0 x.2
      (by simpa using (hx he).1) (by simpa using sub_ne_zero.mpr (hx he).2)
  · apply globalZetaContinued_entire_of_polar_zero F ν f _
      (compactIdeleClassCharacter_unitary F x.1) 0 _ x.2 (mem_univ _)
    exact Or.inl ((compactIdeleClassCharacter_integral F ν x.1).trans (ite_eq_right he))

/-- Restricting to any compact subset of the regular parameter domain is
continuous for the uniform norm on continuous functions on that compact set. -/
def globalContinuedMellinOnCompact (ν : Measure (K F)) [ν.IsHaarMeasure]
    (C : Set (Characters F × ℂ)) (hC : IsCompact C) (hreg : C ⊆ globalMellinRegularSet F) :
    GlobalBruhat F →L[ℂ] C(C, ℂ) := by
  letI : T1Space (IdeleClass F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  letI : T2Space (K F) := inferInstance
  letI := normOneIdeleClass_compact F
  letI : DiscreteTopology (Characters F) := inferInstance
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let L : GlobalBruhat F →ₗ[ℂ] C(C, ℂ) :=
    { toFun := fun f =>
        ⟨fun x => globalContinuedMellinEval F ν x.val.1 x.val.2 f, by
          apply continuous_iff_continuousAt.mpr
          intro x
          have H := (globalContinuedMellinEval_regular_analytic F ν f x.val (hreg x.property)).continuousAt
          have hc : Continuous (fun y : C => y.val.2) := continuous_snd.comp continuous_subtype_val
          have hc' : ContinuousAt (fun y : C => y.val.2) x := hc.continuousAt
          have hcomp : ContinuousAt (fun y : C => globalContinuedMellinEval F ν x.val.1 y.val.2 f) x :=
            ContinuousAt.comp' (f := fun y : C => y.val.2) (x := x) H hc'
          apply hcomp.congr_of_eventuallyEq
          have ht : Continuous (fun y : C => y.val.1) := continuous_fst.comp continuous_subtype_val
          have ht' : ContinuousAt (fun y : C => y.val.1) x := ht.continuousAt
          have hn : ∀ᶠ y : C in 𝓝 x, y.val.1 ∈ ({x.val.1} : Set (Characters F)) :=
            ht'.eventually ((isOpen_discrete {x.val.1}).mem_nhds (mem_singleton _))
          filter_upwards [hn] with y hy
          change y.val.1 = x.val.1 at hy
          rw [hy]⟩
      map_add' := fun f g => ContinuousMap.ext fun x => by
        change globalContinuedMellinEval F ν x.val.1 x.val.2 (f + g) =
          globalContinuedMellinEval F ν x.val.1 x.val.2 f +
            globalContinuedMellinEval F ν x.val.1 x.val.2 g
        exact map_add _ _ _
      map_smul' := fun c f => ContinuousMap.ext fun x => by
        change globalContinuedMellinEval F ν x.val.1 x.val.2 (c • f) =
          c • globalContinuedMellinEval F ν x.val.1 x.val.2 f
        exact map_smul _ _ _ }
  refine ⟨L, ?_⟩
  obtain ⟨p, hp, hP⟩ := globalContinuedMellin_compact_seminorm F ν hC hreg
  apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ _) L
  intro i
  apply Seminorm.continuous_of_le hp
  intro f
  apply (ContinuousMap.norm_le _ (apply_nonneg p f)).mpr
  intro x
  exact hP f x.val x.property

@[simp] theorem globalContinuedMellinOnCompact_apply (ν : Measure (K F)) [ν.IsHaarMeasure]
    (C : Set (Characters F × ℂ)) (hC : IsCompact C) (hreg : C ⊆ globalMellinRegularSet F)
    (f : GlobalBruhat F) (x : C) :
    globalContinuedMellinOnCompact F ν C hC hreg f x =
      globalContinuedMellinEval F ν x.val.1 x.val.2 f := rfl

/-- The compact convergence maps also descend continuously to the theta quotient. -/
def globalQuotientMellinOnCompact (ν : Measure (K F)) [ν.IsHaarMeasure]
    (C : Set (Characters F × ℂ)) (hC : IsCompact C) (hreg : C ⊆ globalMellinRegularSet F) :
    GlobalThetaQuotient F →L[ℂ] C(C, ℂ) := by
  apply Submodule.liftQL _ (globalContinuedMellinOnCompact F ν C hC hreg)
  intro f hf
  apply LinearMap.mem_ker.mpr
  apply ContinuousMap.ext
  intro x
  have he := (adelicTheta_zero_iff_continuedZeta F ν f).mp
    (fun q => congrFun (LinearMap.mem_ker.mp hf) q)
  change globalContinuedMellinOnCompact F ν C hC hreg f x = 0
  rw [globalContinuedMellinOnCompact_apply, globalContinuedMellinEval_apply]
  exact he x.val.1 x.val.2


end

end Masullo
