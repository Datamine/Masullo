import GlobalSobolevPrincipalValues
import CompactBruhatFourierStages

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev U (v : Place F) := ↥(principalIntegralUnits F v)

local instance sobolevUnitMeasurableSpace : MeasurableSpace (Q F) := borel _
local instance sobolevUnitBorelSpace : BorelSpace (Q F) := ⟨rfl⟩
local instance sobolevUnitLocallyCompactSpace : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance sobolevUnitT2Space : T2Space (Q F) := ideleClasses_hausdorff
local instance sobolevUnitSecondCountableTopology : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance sobolevUnitCompactSpaceOnUnits (v : Place F) : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance sobolevUnitMeasurableSpaceOnUnits (v : Place F) : MeasurableSpace (U F v) := borel _
local instance sobolevUnitBorelSpaceOnUnits (v : Place F) : BorelSpace (U F v) := ⟨rfl⟩

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev L := Lp ℂ 2 μ
private abbrev N := globalThetaSobolevCompletion F μ 0 0 0 s hs
private abbrev T (g : Q F) := hardySobolevMulTranslation μ (ideleClassLogNorm F)
  (ideleClassLogNorm_continuous F) 0 0 s hs g

/-- Insertion of a finite integral unit gives a norm-one idele class. -/
def globalSobolevFiniteUnitInclusion (v : Place F) : U F v →ₜ* K F :=
  let a : U F v →* Q F := (finitePlaceInsertion F v).toMonoidHom.comp (principalIntegralUnits F v).subtype
  ⟨a.codRestrict (K F) (fun u => by
    change ideleClassNorm F (finitePlaceInsertion F v u.val) = 1
    rw [finitePlaceInsertion_apply, ideleClassNorm_mk, singleFiniteIdele_norm]
    exact u.property),
    ((finitePlaceInsertion F v).continuous.comp continuous_subtype_val).subtype_mk _⟩

private abbrev unitClass (v : Place F) (u : U F v) : Q F :=
  (globalSobolevFiniteUnitInclusion F v u).val

local instance sobolevUnitCompleteSpace : CompleteSpace (N F μ s hs) :=
  (globalThetaSobolevCompletion_isClosed F μ 0 0 0 s hs).completeSpace_coe

private theorem unitOrbit_integrable (v : Place F) (x : L F μ) :
    Integrable (fun u : U F v => T F μ s hs (unitClass F v u) x) (principalUnitHaar F v) := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hU : Continuous (unitClass F v) :=
    continuous_subtype_val.comp (globalSobolevFiniteUnitInclusion F v).continuous
  have hc := (continuous_hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs).comp (hU.prodMk (continuous_const (y := x)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem unitOrbit_norm (v : Place F) (u : U F v) (x : L F μ) :
    ‖T F μ s hs (unitClass F v u) x‖ = ‖x‖ := by
  apply hardySobolevMulTranslation_norm_of_normOne
  change Multiplicative.ofAdd (Real.log (ideleClassNorm F (unitClass F v u))) = 1
  rw [show ideleClassNorm F (unitClass F v u) = 1 from (globalSobolevFiniteUnitInclusion F v u).property,
    Real.log_one]
  rfl

/-- Average the translations by the integral units at one finite place on
the ambient zero-line Sobolev space. -/
def globalSobolevFiniteUnitAverage (v : Place F) : L F μ →L[ℂ] L F μ := by
  let P : L F μ →ₗ[ℂ] L F μ :=
    { toFun := fun x => ∫ u : U F v, T F μ s hs (unitClass F v u) x ∂principalUnitHaar F v
      map_add' := fun x y => by
        simpa only [map_add] using integral_add
          (unitOrbit_integrable F μ s hs v x) (unitOrbit_integrable F μ s hs v y)
      map_smul' := fun c x => by simp only [map_smul, integral_smul, RingHom.id_apply] }
  refine P.mkContinuous 1 fun x => ?_
  change ‖∫ u : U F v, T F μ s hs (unitClass F v u) x ∂principalUnitHaar F v‖ ≤ 1 * ‖x‖
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp_rw [unitOrbit_norm F μ s hs v]
  rw [integral_const, measureReal_def, principalUnitHaar_univ, ENNReal.toReal_one, one_smul, one_mul]

theorem globalSobolevFiniteUnitAverage_apply (v : Place F) (x : L F μ) :
    globalSobolevFiniteUnitAverage F μ s hs v x =
      ∫ u : U F v, T F μ s hs (unitClass F v u) x ∂principalUnitHaar F v := rfl

/-- Finite integral-unit averaging commutes with every weighted translation. -/
theorem globalSobolevFiniteUnitAverage_commute_translate (v : Place F) (g : Q F) :
    Commute (globalSobolevFiniteUnitAverage F μ s hs v) (T F μ s hs g) := by
  ext x : 1
  change globalSobolevFiniteUnitAverage F μ s hs v (T F μ s hs g x) =
    T F μ s hs g (globalSobolevFiniteUnitAverage F μ s hs v x)
  rw [globalSobolevFiniteUnitAverage_apply, globalSobolevFiniteUnitAverage_apply,
    ← (T F μ s hs g).integral_comp_comm (unitOrbit_integrable F μ s hs v x)]
  apply integral_congr_ae
  exact .of_forall fun u => by
    change T F μ s hs (unitClass F v u) (T F μ s hs g x) =
      T F μ s hs g (T F μ s hs (unitClass F v u) x)
    rw [← hardySobolevMulTranslation_mul, ← hardySobolevMulTranslation_mul, mul_comm g]

/-- The average is the projection onto the vectors fixed by the selected
finite integral units. -/
theorem globalSobolevFiniteUnitAverage_idempotent (v : Place F) (x : L F μ) :
    globalSobolevFiniteUnitAverage F μ s hs v (globalSobolevFiniteUnitAverage F μ s hs v x) =
      globalSobolevFiniteUnitAverage F μ s hs v x := by
  let P := globalSobolevFiniteUnitAverage F μ s hs v
  have hfix (u : U F v) : T F μ s hs (unitClass F v u) (P x) = P x := by
    dsimp only [P]
    rw [globalSobolevFiniteUnitAverage_apply,
      ← (T F μ s hs (unitClass F v u)).integral_comp_comm (unitOrbit_integrable F μ s hs v x)]
    calc
      _ = ∫ w : U F v, T F μ s hs (unitClass F v (u * w)) x ∂principalUnitHaar F v := by
        apply integral_congr_ae
        exact .of_forall fun w => by
          change T F μ s hs (unitClass F v u) (T F μ s hs (unitClass F v w) x) = _
          rw [← hardySobolevMulTranslation_mul]
          congr 2
          exact congrArg Subtype.val ((globalSobolevFiniteUnitInclusion F v).map_mul u w).symm
      _ = _ := integral_mul_left_eq_self (μ := principalUnitHaar F v)
        (fun w : U F v => T F μ s hs (unitClass F v w) x) u
  change globalSobolevFiniteUnitAverage F μ s hs v (P x) = P x
  rw [globalSobolevFiniteUnitAverage_apply]
  simp_rw [hfix, integral_const, measureReal_def, principalUnitHaar_univ, ENNReal.toReal_one, one_smul]

private theorem unitOrbit_theta_integrable (v : Place F) (x : N F μ s hs) :
    Integrable (fun u : U F v => (⟨T F μ s hs (unitClass F v u) x.val,
      globalThetaSobolevCompletion_mapsTo F μ 0 0 0 s hs (unitClass F v u) x.property⟩ :
      N F μ s hs)) (principalUnitHaar F v) := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hU : Continuous (unitClass F v) :=
    continuous_subtype_val.comp (globalSobolevFiniteUnitInclusion F v).continuous
  have hc := (continuous_hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs).comp (hU.prodMk (continuous_const (y := x.val)))
  exact (hc.subtype_mk _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem globalSobolevFiniteUnitAverage_mapsTo_theta (v : Place F) :
    MapsTo (globalSobolevFiniteUnitAverage F μ s hs v) (N F μ s hs) (N F μ s hs) := by
  intro x hx
  let y : N F μ s hs := ⟨x, hx⟩
  let f (u : U F v) : N F μ s hs := ⟨T F μ s hs (unitClass F v u) x,
    globalThetaSobolevCompletion_mapsTo F μ 0 0 0 s hs (unitClass F v u) hx⟩
  have e := ((N F μ s hs).subtypeL.integral_comp_comm (unitOrbit_theta_integrable F μ s hs v y)).symm
  change (N F μ s hs).subtypeL (∫ u, f u ∂principalUnitHaar F v) =
    ∫ u : U F v, T F μ s hs (unitClass F v u) x ∂principalUnitHaar F v at e
  rw [globalSobolevFiniteUnitAverage_apply, ← e]
  exact (∫ u, f u ∂principalUnitHaar F v).property

/-- The unit average is identity on the unramified isotypes and zero on the
ramified isotypes. -/
theorem globalSobolevFiniteUnitAverage_of_isotype (v : Place F) (ω : PontryaginDual (K F))
    (x : L F μ) (hx : x ∈ globalAmbientSobolevIsotype F ω μ 0 0 s hs) :
    globalSobolevFiniteUnitAverage F μ s hs v x =
      if ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 then x else 0 := by
  let θ : PontryaginDual (U F v) := ω.comp (globalSobolevFiniteUnitInclusion F v)
  have he (u : U F v) : T F μ s hs (unitClass F v u) x = (θ u : ℂ) • x :=
    (mem_thetaCharacterSubspace _ _ _).mp hx (globalSobolevFiniteUnitInclusion F v u)
  rw [globalSobolevFiniteUnitAverage_apply]
  simp_rw [he, integral_smul_const]
  change (∫ u : U F v, (θ u : ℂ) ∂principalUnitHaar F v) • x = if θ = 1 then x else 0
  by_cases ht : θ = 1
  · simp only [ht, PontryaginDual.one_apply, Circle.coe_one, integral_const, measureReal_def,
      principalUnitHaar_univ, ENNReal.toReal_one, one_smul, ite_eq_left]
  · obtain ⟨u, hu⟩ : ∃ u, θ u ≠ 1 := by
      by_contra! h
      exact ht (PontryaginDual.ext h)
    have hzero : (∫ a : U F v, (θ a : ℂ) ∂principalUnitHaar F v) = 0 := by
      simpa only [one_mul] using integral_character_eq_zero_of_invariant
        (principalUnitHaar F v) θ (fun _ => (1 : ℂ)) u (fun _ => rfl) hu
    rw [hzero, zero_smul, ite_eq_right ht]

/-- The Weil correction uses the finite-unit average before translating by
a uniformizer. -/
def globalSobolevWeilPrincipalValue (v : Place F) : L F μ →L[ℂ] L F μ :=
  1 - (T F μ s hs (globalUniformizerClass F v)).comp
    (globalSobolevFiniteUnitAverage F μ s hs v)

theorem globalSobolevWeilPrincipalValue_mapsTo_theta (v : Place F) :
    MapsTo (globalSobolevWeilPrincipalValue F μ s hs v) (N F μ s hs) (N F μ s hs) := by
  intro x hx
  exact (N F μ s hs).sub_mem hx (globalThetaSobolevCompletion_mapsTo F μ 0 0 0 s hs
    (globalUniformizerClass F v) (globalSobolevFiniteUnitAverage_mapsTo_theta F μ s hs v hx))

/-- On each isotype the actual averaging prescription gives the previously
constructed difference in the unramified case and identity in the ramified case. -/
theorem globalSobolevWeilPrincipalValue_of_isotype (v : Place F) (ω : PontryaginDual (K F))
    (x : L F μ) (hx : x ∈ globalAmbientSobolevIsotype F ω μ 0 0 s hs) :
    globalSobolevWeilPrincipalValue F μ s hs v x =
      if ω.comp (globalSobolevFiniteUnitInclusion F v) = 1 then
        globalSobolevPrincipalValue F μ s hs v x else x := by
  change x - T F μ s hs (globalUniformizerClass F v) (globalSobolevFiniteUnitAverage F μ s hs v x) = _
  rw [globalSobolevFiniteUnitAverage_of_isotype F μ s hs v ω x hx]
  split
  · rfl
  · rw [map_zero, sub_zero]

theorem globalSobolevWeilPrincipalValue_mapsTo_isotype (v : Place F) (ω : PontryaginDual (K F)) :
    MapsTo (globalSobolevWeilPrincipalValue F μ s hs v)
      (globalAmbientSobolevIsotype F ω μ 0 0 s hs) (globalAmbientSobolevIsotype F ω μ 0 0 s hs) := by
  intro x hx
  rw [globalSobolevWeilPrincipalValue_of_isotype F μ s hs v ω x hx]
  split
  · exact globalSobolevPrincipalValue_mapsTo_isotype F μ s hs ω v hx
  · exact hx

end
end Masullo
