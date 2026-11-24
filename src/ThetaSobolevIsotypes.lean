import GlobalThetaSobolevIsotypes
import SLocalThetaSobolev

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal InnerProductSpace NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 425000

section SLocal

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev SQ := SIdeleQuotient F S
private abbrev SK := SLocalThetaNormOne F S

local instance thetaIso_slocalMeasurable : MeasurableSpace (SQ F S) := borel _
local instance thetaIso_slocalBorel : BorelSpace (SQ F S) := ⟨rfl⟩
local instance thetaIso_slocalT1 : T1Space (SQ F S) :=
  QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
local instance thetaIso_slocalLocallyCompact : LocallyCompactSpace (SQ F S) := by
  letI := sLocalIdeles_locallyCompact F S
  exact (QuotientGroup.isOpenQuotientMap_mk (N := sUnitImage F S)).locallyCompactSpace
local instance thetaIso_slocalSecondCountable : SecondCountableTopology (SQ F S) := by
  letI := sLocalIdeles_secondCountable F S
  exact (QuotientGroup.isOpenQuotientMap_mk (N := sUnitImage F S)).isQuotientMap.secondCountableTopology
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap
local instance thetaIso_slocalKernelSecondCountable : SecondCountableTopology (SK F S) :=
  (show IsEmbedding (Subtype.val : SK F S → SQ F S) from IsEmbedding.subtypeVal).secondCountableTopology
local instance thetaIso_slocalCompact : CompactSpace (SK F S) := sLocalThetaNormOne_compact F S

variable (η : Measure (SK F S)) [η.IsHaarMeasure]
  (a l r s : ℝ) (ha : 0 < a + l) (hlr : l ≤ r) (hs : 0 ≤ s)

local instance thetaIso_slocalHaar : (sLocalClassHaar F S η).IsHaarMeasure :=
  sLocalClassHaar_isHaar F S η

private abbrev SLocalCompletion := sLocalThetaSobolevCompletion F S η a l r s ha hlr hs

local instance thetaIso_slocalComplete : CompleteSpace (SLocalCompletion F S η a l r s ha hlr hs) :=
  sLocalThetaSobolevCompletion_complete F S η a l r s ha hlr hs

/-- The norm-one S-idele classes act on the completed S-local theta space. -/
def sLocalThetaSobolevNormOneAction :
    SK F S →* (SLocalCompletion F S η a l r s ha hlr hs →L[ℂ]
      SLocalCompletion F S η a l r s ha hlr hs) := by
  let μ := sLocalClassHaar F S η
  let V : Submodule ℂ (Lp ℂ 2 μ) := SLocalCompletion F S η a l r s ha hlr hs
  let T := sLocalHardySobolevTranslation F S η l r s hs
  have h (k : SK F S) : MapsTo (T k.val) (V : Set (Lp ℂ 2 μ)) V :=
    sLocalThetaSobolevCompletion_mapsTo F S η a l r s ha hlr hs k.val
  change SK F S →* (V →L[ℂ] V)
  exact hardySobolevRestrictedAction (G := SQ F S) μ (sLocalThetaSobolevLogNorm F S)
    (continuous_sLocalThetaSobolevLogNorm F S) l r s hs (SK F S) V h

theorem sLocalThetaSobolev_normOne_decomposition
    (ν : Measure (SK F S)) [ν.IsHaarMeasure] [IsProbabilityMeasure ν] :
    HasCompactIsotypeDecomposition (sLocalThetaSobolevNormOneAction F S η a l r s ha hlr hs) ν := by
  let μ := sLocalClassHaar F S η
  letI : (sLocalClassHaar F S η).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let V : Submodule ℂ (Lp ℂ 2 μ) := SLocalCompletion F S η a l r s ha hlr hs
  let T := sLocalHardySobolevTranslation F S η l r s hs
  have h (k : SK F S) : MapsTo (T k.val) (V : Set (Lp ℂ 2 μ)) V :=
    sLocalThetaSobolevCompletion_mapsTo F S η a l r s ha hlr hs k.val
  have hd := hardySobolevRestrictedAction_decomposition (G := SQ F S) μ
    (sLocalThetaSobolevLogNorm F S) (continuous_sLocalThetaSobolevLogNorm F S) l r s hs
    (SK F S) V h (sLocalThetaSobolevLogNorm_normOne F S) ν
  exact hd

/-- The dense embedding of the actual S-local theta quotient. -/
def sLocalThetaSobolevDenseMap :
    SLocalThetaQuotient F S →L[ℂ] SLocalCompletion F S η a l r s ha hlr hs :=
  (sLocalThetaSobolevMap F S η a l r s ha hlr hs).codRestrict _
    (fun u => subset_closure ⟨u, rfl⟩)

theorem sLocalThetaSobolevDenseMap_dense :
    DenseRange (sLocalThetaSobolevDenseMap F S η a l r s ha hlr hs) :=
  sLocalThetaSobolevCompletion_dense F S η a l r s ha hlr hs

/-- The restricted action agrees with S-idelic translation on the dense theta tests. -/
theorem sLocalThetaSobolevNormOneAction_dense (k : SK F S)
    (g : (SAdeles F S)ˣ) (hg : (QuotientGroup.mk g : SQ F S) = k.val)
    (u : SLocalThetaQuotient F S) :
    sLocalThetaSobolevNormOneAction F S η a l r s ha hlr hs k
        (sLocalThetaSobolevDenseMap F S η a l r s ha hlr hs u) =
      sLocalThetaSobolevDenseMap F S η a l r s ha hlr hs (sLocalSobolevThetaTranslateIdeles F S g u) := by
  have h := sLocalThetaSobolevMap_translate F S η a l r s ha hlr hs g u
  apply Subtype.ext
  change sLocalHardySobolevTranslation F S η l r s hs (QuotientGroup.mk g) _
    = (Real.exp (-a * (sLocalThetaSobolevLogNorm F S (QuotientGroup.mk g)).toAdd) : ℂ) • _ at h
  have hk : (sLocalThetaSobolevLogNorm F S k.val).toAdd = 0 :=
    congrArg Multiplicative.toAdd (sLocalThetaSobolevLogNorm_normOne F S k)
  rw [hg, hk, mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul] at h
  exact h

end SLocal

end

end Masullo
