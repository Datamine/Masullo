import IdelicFundamentalDomain
import ShellIsotypes
import Mathlib.MeasureTheory.Group.FundamentalDomain

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private theorem normOneIdelesToClasses_principal (t : Fˣ) :
    normOneIdelesToClasses F (principalNormOne F t) = 1 := by
  apply Subtype.ext
  change ideleClassMap F (principalIdele F t) = 1
  exact (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩

/-- Pushing Haar measure restricted to the actual representative region
down to the norm-one class group gives Haar measure. -/
theorem ideleFundamentalDomain_haar
    [MeasurableSpace (NormOneIdeles F)] [BorelSpace (NormOneIdeles F)]
    [MeasurableSpace (IdeleClass F)] [BorelSpace (IdeleClass F)]
    (v : InfinitePlace F) (g : ClassGroup (𝓞 F) → NormOneIdeles F)
    (hg : ∀ c, normOneIdealClass F (g c) = c)
    (μ : Measure (NormOneIdeles F)) [μ.IsHaarMeasure] :
    ((μ.restrict (ideleFundamentalDomain F v g)).map (normOneIdelesToClasses F)).IsHaarMeasure := by
  classical
  letI : Countable F :=
    (Module.finBasis ℚ F).equivFun.injective.countable
  letI : Countable Fˣ := (Units.val_injective (α := F)).countable
  letI : MulAction Fˣ (NormOneIdeles F) :=
    MulAction.compHom (NormOneIdeles F) (principalNormOne F)
  letI : MeasurableConstSMul Fˣ (NormOneIdeles F) :=
    ⟨fun t => (continuous_const.mul (f := fun _ => principalNormOne F t) continuous_id).measurable⟩
  letI : SMulInvariantMeasure Fˣ (NormOneIdeles F) μ :=
    ⟨fun t _ hA => (measurePreserving_mul_left μ (principalNormOne F t)).measure_preimage hA.nullMeasurableSet⟩
  haveI : SMulCommClass (NormOneIdeles F) Fˣ (NormOneIdeles F) :=
    ⟨fun a t x => mul_left_comm a (principalNormOne F t) x⟩
  let D := ideleFundamentalDomain F v g
  have hD := ideleFundamentalDomain_measurable F v g
  have hFD : IsFundamentalDomain Fˣ D μ :=
    IsFundamentalDomain.mk' hD.nullMeasurableSet (ideleFundamentalDomain_unique F v g hg)
  let p := normOneIdelesToClasses F
  have hp : Continuous p := (normOneIdelesToClasses_openQuotient F).continuous
  have hps : Surjective p := (normOneIdelesToClasses_openQuotient F).surjective
  let ν := (μ.restrict D).map p
  have hinv (T : Set (normOneIdeleClass F)) :
      ∀ t : Fˣ, (fun x : NormOneIdeles F => t • x) ⁻¹' (p ⁻¹' T) = p ⁻¹' T := by
    intro t
    ext x
    change p (principalNormOne F t * x) ∈ T ↔ p x ∈ T
    rw [map_mul, normOneIdelesToClasses_principal, one_mul]
  letI : ν.IsMulLeftInvariant := ⟨fun y => by
    obtain ⟨b, rfl⟩ := hps y
    let e := Homeomorph.mulLeft b
    change ν.map (fun z => p b * z) = ν
    ext T hT
    rw [Measure.map_apply (measurable_const_mul _) hT, Measure.map_apply hp.measurable
      ((measurable_const_mul _ ) hT), Measure.map_apply hp.measurable hT]
    have hm : MeasurableSet (p ⁻¹' T) := hp.measurable hT
    have he : MeasurableSet (e ⁻¹' (p ⁻¹' T)) := e.continuous.measurable hm
    have hpre : p ⁻¹' ((fun z => p b * z) ⁻¹' T) = e ⁻¹' (p ⁻¹' T) := by
      ext x
      change p b * p x ∈ T ↔ p (b * x) ∈ T
      rw [map_mul]
    rw [hpre, Measure.restrict_apply he, Measure.restrict_apply hm]
    have he' : e ⁻¹' ((p ⁻¹' T) ∩ b • D) = e ⁻¹' (p ⁻¹' T) ∩ D := by
      rw [preimage_inter]
      congr 1
      exact e.injective.preimage_image D
    have hsm : MeasurableSet ((p ⁻¹' T) ∩ b • D) :=
      hm.inter (e.toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr hD)
    rw [← he']
    change μ ((fun x : NormOneIdeles F => b * x) ⁻¹' ((p ⁻¹' T) ∩ b • D)) = _
    rw [(measurePreserving_mul_left μ b).measure_preimage hsm.nullMeasurableSet]
    exact (hFD.measure_set_eq (hFD.smul_of_comm b) hm (hinv T)).symm⟩
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  have hν : ν univ = μ D := by
    rw [Measure.map_apply hp.measurable MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior ν univ isCompact_univ (by simp)
  · rw [hν]
    intro h
    exact (isOpen_interior.measure_ne_zero μ (ideleFundamentalDomain_topology F v g).2)
      (measure_mono_null interior_subset h)
  · rw [hν]
    exact ((measure_mono subset_closure).trans_lt
      (ideleFundamentalDomain_topology F v g).1.measure_lt_top).ne


/-- The scale of the pushed-forward Haar measure is the mass of the
representative domain. -/
theorem ideleFundamentalDomain_haar_mass
    [MeasurableSpace (NormOneIdeles F)] [BorelSpace (NormOneIdeles F)]
    [MeasurableSpace (IdeleClass F)] [BorelSpace (IdeleClass F)]
    (v : InfinitePlace F) (g : ClassGroup (𝓞 F) → NormOneIdeles F)
    (μ : Measure (NormOneIdeles F)) :
    ((μ.restrict (ideleFundamentalDomain F v g)).map (normOneIdelesToClasses F)) univ =
      μ (ideleFundamentalDomain F v g) := by
  rw [Measure.map_apply (normOneIdelesToClasses_openQuotient F).continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

end

end Masullo
