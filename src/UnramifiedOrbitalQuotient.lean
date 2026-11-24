import GlobalOrbitalMarkushevich

open Function IsDedekindDomain MeasureTheory NumberField
open scoped NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance unramifiedOrbitalQMeasure : MeasurableSpace (Q F) := borel _
local instance unramifiedOrbitalQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance unramifiedOrbitalQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance unramifiedOrbitalQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance unramifiedOrbitalQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)
private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F μ s hs ω
private abbrev N := globalThetaSobolevCompletion F μ 0 0 0 s hs

/-- At unramified places the actual Weil product on the isotype is the manuscript's
finite product of uniformizer differences. -/
theorem globalWeilIsotypeProduct_eq_unramified (A : Finset (Place F))
    (ω : PontryaginDual (K F))
    (hA : ∀ v ∈ A, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1) :
    globalWeilIsotypeProduct F μ s hs A ω = globalIsotypicPrincipalValues F μ s hs ω A := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have he : globalThetaSobolevWeilPrincipalValues F μ s hs ∅ = 1 :=
      Finset.noncommProd_empty _ _
    have hd : globalIsotypicPrincipalValues F μ s hs ω ∅ = 1 :=
      Finset.noncommProd_empty _ _
    apply ContinuousLinearMap.ext
    intro u
    have h := congrArg (fun L : N F μ s hs →L[ℂ] N F μ s hs ↦
      (L ⟨u.val,u.property.1⟩).val) he
    rw [hd]
    exact Subtype.ext h
  | @insert v A hv ih =>
    have ih' := ih fun w hw ↦ hA w (Finset.mem_insert_of_mem hw)
    have hunit := hA v (Finset.mem_insert_self v A)
    have he : globalThetaSobolevWeilPrincipalValues F μ s hs (insert v A) =
        (globalThetaSobolevWeilPrincipalValue F μ s hs v).comp
          (globalThetaSobolevWeilPrincipalValues F μ s hs A) :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ hv
    have hd : globalIsotypicPrincipalValues F μ s hs ω (insert v A) =
        (globalIsotypicPrincipalValue F μ s hs ω v).comp
          (globalIsotypicPrincipalValues F μ s hs ω A) :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ hv
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    rw [hd, ← ih']
    let x := (globalWeilIsotypeProduct F μ s hs A ω) u
    have hdiff := globalSobolevWeilPrincipalValue_of_isotype F μ s hs v ω x.val x.property.2
    rw [ite_eq_left hunit] at hdiff
    calc
      _ = globalSobolevWeilPrincipalValue F μ s hs v x.val :=
        congrArg (fun L : N F μ s hs →L[ℂ] N F μ s hs ↦
          (L ⟨u.val,u.property.1⟩).val) he
      _ = _ := hdiff

theorem globalWeilIsotypeClosedRange_eq_unramified (A : Finset (Place F))
    (ω : PontryaginDual (K F))
    (hA : ∀ v ∈ A, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1) :
    globalWeilIsotypeClosedRange F μ s hs A ω =
      (globalClosedPrincipalValueRange F μ s hs ω A).toSubmodule := by
  unfold globalWeilIsotypeClosedRange
  rw [globalWeilIsotypeProduct_eq_unramified F μ s hs A ω hA]
  rfl

end
end Masullo
