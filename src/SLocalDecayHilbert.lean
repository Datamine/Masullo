import SLocalCech
import BruhatIntervalInclusion
import SLocalThetaSobolev

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 800000 in
private theorem exists_modulatedCentralHilbertInclusion {X : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (m₀ : X →ₜ* Multiplicative ℝ) [CompactSpace m₀.toMonoidHom.ker]
    (τ : Multiplicative ℝ →ₜ* X) (hτ : RightInverse τ m₀)
    (κ : Measure m₀.toMonoidHom.ker) [IsFiniteMeasure κ] [κ.IsHaarMeasure] [κ.WeaklyRegular]
    (hm : IsProperMap m₀) (I : Set ℝ) (hI : (1/2 : ℝ) ∈ I) :
    let W := hardySobolevMeasure (modulatedLogMeasure m₀ τ hτ κ) (modulatedLog m₀) (1/2) (1/2) 0
    ∃ j : ModulatedExponentialInductive m₀ I →L[ℂ] Lp ℂ 2 W,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : X → ℂ) =ᵐ[W] f.val := by
  intro W
  let U := modulatedLogMeasure m₀ τ hτ κ
  let j := bruhatCompactIntervalGroupInclusion m₀ τ hτ κ hI hI le_rfl 0
  have hj (f : ModulatedExponentialInductive m₀ I) : (j f : X → ℂ) =ᵐ[W] f.val :=
    bruhatCompactIntervalGroupInclusion_ae m₀ τ hτ κ hI hI le_rfl 0 f
  have hd : DenseRange j :=
    bruhatCompactIntervalGroupInclusion_dense m₀ τ hτ κ hm hI hI le_rfl 0
  refine ⟨j,?_,hd,hj⟩
  letI : U.IsHaarMeasure := modulatedLogMeasure_isHaar m₀ τ hτ κ
  have hUW : U ≪ W := by
    change U ≪ U.withDensity _
    apply withDensity_absolutelyContinuous'
    · exact ((continuous_hardySobolevWeight _ _ _).comp
        (continuous_toAdd.comp m₀.continuous)).measurable.ennreal_ofReal.aemeasurable
    · exact Eventually.of_forall fun q ↦ ENNReal.ofReal_ne_zero_iff.mpr (by
        unfold hardySobolevWeight
        positivity)
  have hc (f : ModulatedExponentialInductive m₀ I) : Continuous f.val := by
    let a : I := ⟨1/2,hI⟩
    let Fw := modulatedDecayTwistCLM m₀ I a f
    have hw (q : X) : Fw.val q = (Real.exp (a.val * (m₀ q).toAdd) : ℂ) * f.val q := rfl
    have he : f.val = fun q ↦ (Real.exp (-(a.val * (m₀ q).toAdd)) : ℂ) * Fw.val q := by
      funext q
      rw [hw, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one, one_mul]
    rw [he]
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_toAdd.comp m₀.continuous)).neg))).mul
        (bruhatSchwartz_continuous Fw)
  intro f g he
  apply ModulatedExponentialInductive.algebraicEquiv.injective
  apply Subtype.ext
  exact ((hc f).ae_eq_iff_eq U (hc g)).mp
    (hUW.ae_eq ((hj f).symm.trans (he ▸ hj g)))

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Class" => SIdeleQuotient F S
local notation "m" => sLocalCechModulation F S
private abbrev centralKernel := (sLocalCechModulation F S).toMonoidHom.ker
local notation "K" => centralKernel F S

local instance : LocallyCompactSpace (SAdeles F S)ˣ := sLocalIdeles_locallyCompact F S
local instance : SecondCountableTopology (SAdeles F S)ˣ := sLocalIdeles_secondCountable F S
local instance : LocallyCompactSpace Class := QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace
local instance : SecondCountableTopology Class :=
  TopologicalSpace.Quotient.secondCountableTopology (QuotientGroup.isOpenMap_coe (N := sUnitImage F S))
local instance : T2Space Class := by
  letI : T1Space Class := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  exact inferInstance

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

private def normSection : Multiplicative ℝ →ₜ* Class :=
  ⟨(QuotientGroup.mk' (sUnitImage F S)).comp (sLocalExpSection F S),
    QuotientGroup.continuous_mk.comp (sLocalExpSection_continuous F S)⟩

private theorem normSection_rightInverse : RightInverse (normSection F S) m := by
  intro t
  exact congrArg Multiplicative.ofAdd ((congrArg Real.log (sLocalIdeleNorm_expSection F S t.toAdd)).trans
    (Real.log_exp _))

/-- Haar in the canonical logarithmic coordinates. -/
def sLocalDecayHaarMeasure (κ : Measure K) : Measure Class :=
  @modulatedLogMeasure Class inferInstance inferInstance inferInstance inferInstance
    m (normSection F S) (normSection_rightInverse F S) κ

/-- The weighted Hilbert measure in Proposition 5.4.2.1(2), using the
selected kernel Haar normalization. -/
def sLocalDecayHilbertMeasure (κ : Measure K) : Measure Class :=
  hardySobolevMeasure (sLocalDecayHaarMeasure F S κ)
    (modulatedLog m) (1/2) (1/2) 0

/-- The weight is exactly the idelic modulus. -/
theorem sLocalDecayHilbertMeasure_eq (κ : Measure K) :
    sLocalDecayHilbertMeasure F S κ =
      (sLocalDecayHaarMeasure F S κ).withDensity
        (fun q ↦ ENNReal.ofReal (sLocalClassModulus F S q)) := by
  unfold sLocalDecayHilbertMeasure hardySobolevMeasure
  congr 1
  funext q
  apply congrArg ENNReal.ofReal
  have h : modulatedLog m q = Real.log (sLocalClassModulus F S q) := rfl
  simp only [hardySobolevWeight, mul_one, max_self, zero_div, Real.rpow_zero]
  rw [show (2 : ℝ) * (1/2) = 1 by norm_num, one_mul, h, Real.exp_log (sLocalClassModulus_pos F S q)]

set_option maxHeartbeats 950000 in
/-- The entire weighted Schwartz–Bruhat space embeds continuously and
densely in the central weighted Haar Hilbert space if the interval
contains one half. The embedding takes the almost-everywhere class. -/
theorem exists_sLocalDecayHilbertInclusion (κ : Measure K) [κ.IsHaarMeasure]
    (I : Set ℝ) (hI : (1/2 : ℝ) ∈ I) :
    ∃ j : ModulatedExponentialInductive m I →L[ℂ] Lp ℂ 2 (sLocalDecayHilbertMeasure F S κ),
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : Class → ℂ) =ᵐ[sLocalDecayHilbertMeasure F S κ] f.val := by
  have hm := sLocalCechModulation_proper F S
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  letI : TopologicalSpace.PseudoMetrizableSpace K := inferInstance
  letI : IsFiniteMeasure κ := by infer_instance
  letI : κ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  exact @exists_modulatedCentralHilbertInclusion Class inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance m inferInstance
    (normSection F S) (normSection_rightInverse F S) κ inferInstance inferInstance inferInstance hm I hI

private theorem modulus_log_kernel (q : Class) :
    m q = 1 ↔ sQuotientNorm F S q = 1 := by
  have he : m q = 1 ↔ Real.log (sLocalClassModulus F S q) = 0 :=
    ⟨fun h ↦ congrArg Multiplicative.toAdd h, fun h ↦ congrArg Multiplicative.ofAdd h⟩
  rw [he]
  constructor
  · intro h
    apply Units.ext
    apply NNReal.eq
    change sLocalClassModulus F S q = 1
    exact (Real.exp_log (sLocalClassModulus_pos F S q)).symm.trans (h ▸ Real.exp_zero)
  · intro h
    have hmod : sLocalClassModulus F S q = 1 := by simp [sLocalClassModulus,h]
    rw [hmod, Real.log_one]

private def kernelChart : SLocalThetaNormOne F S ≃ₜ* K where
  toFun k := ⟨k.val,(modulus_log_kernel F S k.val).mpr k.property⟩
  invFun k := ⟨k.val,(modulus_log_kernel F S k.val).mp k.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

set_option maxHeartbeats 1600000 in
private theorem normalized_kernel_measure (ν : Measure (SLocalThetaNormOne F S))
    [ν.IsHaarMeasure] [IsFiniteMeasure ν] :
    sLocalDecayHilbertMeasure F S (Measure.map (kernelChart F S) ν) =
      sLocalClassHardySobolevMeasure F S ν (1/2) (1/2) 0 := by
  let e := kernelChart F S
  let e₀ : SLocalThetaNormOne F S → K := e
  have he₀ : Measurable e₀ := e.continuous.measurable
  let g := Prod.map (id : ℝ → ℝ) e₀
  have hg : Measurable g := measurable_id.prodMap he₀
  have hp : (volume : Measure ℝ).prod (Measure.map e₀ ν) =
      Measure.map g (volume.prod ν) := by
    have h := Measure.map_prod_map (volume : Measure ℝ) ν measurable_id he₀
    simpa only [Measure.map_id] using h
  let D : ℝ × K ≃ₜ Class :=
    @modulatedLogSplit Class inferInstance inferInstance inferInstance m
      (normSection F S) (normSection_rightInverse F S)
  have hD : Measurable (D : ℝ × K → Class) := D.continuous.measurable
  have h : sLocalDecayHaarMeasure F S (Measure.map e ν) = sLocalClassHaar F S ν := by
    calc
      _ = Measure.map D (volume.prod (Measure.map e₀ ν)) := rfl
      _ = Measure.map D (Measure.map g (volume.prod ν)) := congrArg (Measure.map D) hp
      _ = Measure.map (D ∘ g) (volume.prod ν) := Measure.map_map hD hg
      _ = _ := rfl
  exact congrArg (fun M : Measure Class ↦ hardySobolevMeasure M (modulatedLog m) (1/2) (1/2) 0) h

set_option maxHeartbeats 1600000 in
/-- The central inclusion uses the same Haar normalization and physical
measure as the S-local theta Hilbert completion. -/
theorem exists_sLocalDecayHilbertInclusion_normalized (ν : Measure (SLocalThetaNormOne F S))
    [ν.IsHaarMeasure] (I : Set ℝ) (hI : (1/2 : ℝ) ∈ I) :
    let W := sLocalClassHardySobolevMeasure F S ν (1/2) (1/2) 0
    ∃ j : ModulatedExponentialInductive m I →L[ℂ] Lp ℂ 2 W,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : Class → ℂ) =ᵐ[W] f.val := by
  let e := kernelChart F S
  let κ := Measure.map e ν
  letI : κ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μ := ν) e
  letI : CompactSpace (SLocalThetaNormOne F S) := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure ν := by infer_instance
  rw [← normalized_kernel_measure F S ν]
  exact exists_sLocalDecayHilbertInclusion F S κ I hI

end

end Masullo
