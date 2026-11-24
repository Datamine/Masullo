import GlobalThetaSobolev
import CompactHilbertIsotypes

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal InnerProductSpace NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 425000

section Global

variable (F : Type*) [Field F] [NumberField F]

private abbrev GQ := IdeleClass F
private abbrev GK := normOneIdeleClass F

local instance thetaIso_globalMeasurable : MeasurableSpace (GQ F) := borel _
local instance thetaIso_globalBorel : BorelSpace (GQ F) := ⟨rfl⟩
local instance : MeasurableSpace (GK F) := borel _
local instance : BorelSpace (GK F) := ⟨rfl⟩
local instance thetaIso_globalT1 : T1Space (GQ F) :=
  QuotientGroup.t1Space_iff.mpr principalIdeles_closed
local instance thetaIso_globalLocallyCompact : LocallyCompactSpace (GQ F) :=
  ideleClasses_locallyCompact
local instance thetaIso_globalSecondCountable : SecondCountableTopology (GQ F) := by
  letI : SecondCountableTopology (AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))
local instance thetaIso_globalKernelSecondCountable : SecondCountableTopology (GK F) :=
  (show IsEmbedding (Subtype.val : GK F → GQ F) from IsEmbedding.subtypeVal).secondCountableTopology
local instance thetaIso_globalCompact : CompactSpace (GK F) := normOneIdeleClass_compact F

variable (μ : Measure (GQ F)) [μ.IsHaarMeasure] (a l r s : ℝ) (hs : 0 ≤ s)

private abbrev GlobalCompletion := globalThetaSobolevCompletion F μ a l r s hs

local instance thetaIso_globalComplete : CompleteSpace (GlobalCompletion F μ a l r s hs) :=
  globalThetaSobolevCompletion_complete F μ a l r s hs

/-- The norm-one idele classes act on the completed global polar-free theta space. -/
def globalThetaSobolevNormOneAction :
    GK F →* (GlobalCompletion F μ a l r s hs →L[ℂ] GlobalCompletion F μ a l r s hs) := by
  let V : Submodule ℂ (Lp ℂ 2 μ) := GlobalCompletion F μ a l r s hs
  let T := hardySobolevMulTranslation (G := GQ F) μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs
  have h (k : GK F) : MapsTo (T k.val) (V : Set (Lp ℂ 2 μ)) V :=
    globalThetaSobolevCompletion_mapsTo F μ a l r s hs k.val
  change GK F →* (V →L[ℂ] V)
  exact hardySobolevRestrictedAction (G := GQ F) μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs (GK F) V h

theorem globalThetaSobolev_normOne_decomposition
    (ν : Measure (GK F)) [ν.IsHaarMeasure] [IsProbabilityMeasure ν] :
    HasCompactIsotypeDecomposition (globalThetaSobolevNormOneAction F μ a l r s hs) ν := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hk (k : GK F) : ideleClassLogNorm F k.val = 1 := by
    have he : ideleClassNorm F k.val = 1 := k.property
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = 1
    rw [he, Real.log_one]
    rfl
  let V : Submodule ℂ (Lp ℂ 2 μ) := GlobalCompletion F μ a l r s hs
  let T := hardySobolevMulTranslation (G := GQ F) μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) l r s hs
  have h (k : GK F) : MapsTo (T k.val) (V : Set (Lp ℂ 2 μ)) V :=
    globalThetaSobolevCompletion_mapsTo F μ a l r s hs k.val
  exact hasCompactIsotypeDecomposition _
    (hardySobolevRestrictedAction_continuous μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) l r s hs (GK F) V h)
    (hardySobolevRestrictedAction_norm μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) l r s hs (GK F) V h hk) ν

/-- The restricted action is the one on the actual dense polar-free theta tests. -/
theorem globalThetaSobolevNormOneAction_dense (k : GK F) (u : GlobalPolarTheta F) :
    globalThetaSobolevNormOneAction F μ a l r s hs k
        (globalThetaSobolevDenseMap F μ a l r s hs u) =
      globalThetaSobolevDenseMap F μ a l r s hs (globalPolarThetaTranslate F k.val u) := by
  apply Subtype.ext
  have h := globalThetaSobolevMap_translate F μ a l r s hs k.val u
  have hk : (ideleClassLogNorm F k.val).toAdd = 0 := by
    have hnorm : ideleClassNorm F k.val = 1 := k.property
    change Real.log (ideleClassNorm F k.val) = 0
    rw [hnorm, Real.log_one]
  change _ = (Real.exp (-a * (ideleClassLogNorm F k.val).toAdd) : ℂ) • _ at h
  rw [hk, mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul] at h
  exact h

end Global

end
end Masullo
