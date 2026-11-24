import GlobalSobolevWeilUnitAverage
import GlobalWeilUnitAverage

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev U (v : Place F) := ↥(principalIntegralUnits F v)
private abbrev P := (GlobalBruhat.polarEvaluation F).ker

local instance sobolevExtensionMeasurableSpace : MeasurableSpace (Q F) := borel _
local instance sobolevExtensionBorelSpace : BorelSpace (Q F) := ⟨rfl⟩
local instance sobolevExtensionLocallyCompactSpace : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance sobolevExtensionT2Space : T2Space (Q F) := ideleClasses_hausdorff
local instance sobolevExtensionSecondCountableTopology : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance sobolevExtensionCompactSpaceOnUnits (v : Place F) : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance sobolevExtensionMeasurableSpaceOnUnits (v : Place F) : MeasurableSpace (U F v) := borel _
local instance sobolevExtensionBorelSpaceOnUnits (v : Place F) : BorelSpace (U F v) := ⟨rfl⟩

private def polarTestClass : P F →L[ℂ] GlobalPolarTheta F :=
  ((globalThetaOperator F).ker.mkQL.comp (P F).subtypeL).codRestrict _ (fun f => f.property)

private theorem translate_mem_polar (g : Idele F) (f : P F) :
    GlobalBruhat.leftTranslate F g f.val ∈ P F := by
  change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F g f.val) = 0
  rw [polarEvaluation_leftTranslate, show GlobalBruhat.polarEvaluation F f.val = 0 from f.property]
  simp

private def polarTestTranslate (g : Idele F) : P F →L[ℂ] P F :=
  ((GlobalBruhat.leftTranslate F g).comp (P F).subtypeL).codRestrict _ (translate_mem_polar F g)

private theorem polarTestClass_translate (g : Idele F) (f : P F) :
    polarTestClass F (polarTestTranslate F g f) =
      globalPolarThetaTranslate F (ideleClassMap F g) (polarTestClass F f) := by
  apply Subtype.ext
  change Submodule.Quotient.mk (GlobalBruhat.leftTranslate F g f.val) =
    globalThetaTranslate F (ideleClassMap F g) (Submodule.Quotient.mk f.val)
  rw [globalThetaTranslate_class, globalThetaTranslateIdeles_mk]

/-- Unit averaging preserves the two-evaluation kernel. -/
theorem globalFiniteUnitAverage_mem_polar (v : Place F) (f : P F) :
    globalFiniteUnitAverage F v f.val ∈ P F := by
  let e := (GlobalBruhat.polarEvaluation F).toLinearMap
  let a := (LinearMap.fst ℂ ℂ ℂ).comp e
  let b := (LinearMap.snd ℂ ℂ ℂ).comp e
  have h (u : U F v) : e (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f.val) = 0 :=
    translate_mem_polar F (singleFiniteIdele F v u.val) f
  have ha := (globalFiniteUnitAverage_pairing F v f.val a).2
  have hb := (globalFiniteUnitAverage_pairing F v f.val b).2
  change e (globalFiniteUnitAverage F v f.val) = 0
  apply Prod.ext
  · change a (globalFiniteUnitAverage F v f.val) = 0
    rw [ha]
    have hzero (u : U F v) : a (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f.val) = 0 :=
      congrArg Prod.fst (h u)
    simp_rw [hzero, integral_zero]
  · change b (globalFiniteUnitAverage F v f.val) = 0
    rw [hb]
    have hzero (u : U F v) : b (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f.val) = 0 :=
      congrArg Prod.snd (h u)
    simp_rw [hzero, integral_zero]

private def polarTestUnitAverage (v : Place F) : P F →L[ℂ] P F :=
  ((globalFiniteUnitAverage F v).comp (P F).subtypeL).codRestrict _ (globalFiniteUnitAverage_mem_polar F v)

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev J := (globalThetaSobolevMap F μ 0 0 0 s hs).comp (polarTestClass F)

/-- The Sobolev image of a translated polar-free test is the weighted
translation on the zero line. -/
theorem globalThetaSobolevPolarTest_translate (g : Idele F) (f : P F) :
    J F μ s hs (polarTestTranslate F g f) =
      hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
        0 0 s hs (ideleClassMap F g) (J F μ s hs f) := by
  simpa only [J, ContinuousLinearMap.comp_apply, polarTestClass_translate, neg_zero,
    zero_mul, Real.exp_zero, Complex.ofReal_one, one_smul] using
    (globalThetaSobolevMap_translate F μ 0 0 0 s hs (ideleClassMap F g) (polarTestClass F f)).symm

set_option maxHeartbeats 1000000 in
/-- The bounded unit average agrees with the global adelic test average. -/
theorem globalSobolevFiniteUnitAverage_on_polarTests (v : Place F) (f : P F) :
    globalSobolevFiniteUnitAverage F μ s hs v (J F μ s hs f) =
      J F μ s hs (polarTestUnitAverage F v f) := by
  let A (u : U F v) := hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs (globalSobolevFiniteUnitInclusion F v u).val (J F μ s hs f)
  have hA (u : U F v) :
      A u = J F μ s hs (polarTestTranslate F (singleFiniteIdele F v u.val) f) := by
    have he : (globalSobolevFiniteUnitInclusion F v u).val = ideleClassMap F (singleFiniteIdele F v u.val) :=
      finitePlaceInsertion_apply F v u.val
    dsimp only [A]
    rw [he, globalThetaSobolevPolarTest_translate]
  rw [globalSobolevFiniteUnitAverage_apply]
  change (∫ u, A u ∂principalUnitHaar F v) = _
  apply ext_inner_left ℂ
  intro y
  let l := innerSL ℂ y
  let w := l.toLinearMap.comp (J F μ s hs).toLinearMap
  obtain ⟨L, hL⟩ := w.exists_extend
  have hL' (g : P F) : L g.val = l (J F μ s hs g) := LinearMap.congr_fun hL g
  have hi : Integrable A (principalUnitHaar F v) := by
    letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    have hU : Continuous (fun u : U F v => (globalSobolevFiniteUnitInclusion F v u).val) :=
      continuous_subtype_val.comp (globalSobolevFiniteUnitInclusion F v).continuous
    have hc := (continuous_hardySobolevMulTranslation μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 s hs).comp (hU.prodMk (continuous_const (y := J F μ s hs f)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change l (∫ u, A u ∂principalUnitHaar F v) = l (J F μ s hs (polarTestUnitAverage F v f))
  rw [← l.integral_comp_comm hi, ← hL' (polarTestUnitAverage F v f)]
  change (∫ u, l (A u) ∂principalUnitHaar F v) = L (globalFiniteUnitAverage F v f.val)
  rw [(globalFiniteUnitAverage_pairing F v f.val L).2]
  apply integral_congr_ae
  exact .of_forall fun u => (congrArg l (hA u)).trans (hL' _).symm

/-- The actual Weil operator preserves polar-free tests. -/
theorem globalWeilPrincipalValue_mem_polar (v : Place F) (f : P F) :
    globalWeilPrincipalValue F v f.val ∈ P F := by
  rw [globalWeilPrincipalValue_eq_unitAverage]
  exact (P F).sub_mem f.property (translate_mem_polar F _ (polarTestUnitAverage F v f))

/-- The corrected bounded operator restricts to the original Weil operation
on the dense polar-free test space. -/
theorem globalSobolevWeilPrincipalValue_on_polarTests (v : Place F) (f : P F) :
    globalSobolevWeilPrincipalValue F μ s hs v (J F μ s hs f) =
      J F μ s hs ⟨globalWeilPrincipalValue F v f.val, globalWeilPrincipalValue_mem_polar F v f⟩ := by
  let g := singleFiniteIdele F v (chosenFiniteUniformizer F v)
  have htest : (⟨globalWeilPrincipalValue F v f.val, globalWeilPrincipalValue_mem_polar F v f⟩ : P F) =
      f - polarTestTranslate F g (polarTestUnitAverage F v f) := by
    apply Subtype.ext
    exact globalWeilPrincipalValue_eq_unitAverage F v f.val
  change J F μ s hs f - hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
    0 0 s hs (ideleClassMap F g) (globalSobolevFiniteUnitAverage F μ s hs v (J F μ s hs f)) = _
  rw [htest, globalSobolevFiniteUnitAverage_on_polarTests, map_sub, globalThetaSobolevPolarTest_translate]

/-- On tests fixed by finite unit averaging the bounded operator agrees
with the ordinary uniformizer difference. -/
theorem globalSobolevWeilPrincipalValue_of_average_fixed (v : Place F) (f : P F)
    (hf : globalFiniteUnitAverage F v f.val = f.val) :
    globalSobolevWeilPrincipalValue F μ s hs v (J F μ s hs f) =
      globalSobolevPrincipalValue F μ s hs v (J F μ s hs f) := by
  have he : polarTestUnitAverage F v f = f := Subtype.ext hf
  have hA := globalSobolevFiniteUnitAverage_on_polarTests F μ s hs v f
  rw [he] at hA
  change J F μ s hs f - (hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs (globalUniformizerClass F v))
      (globalSobolevFiniteUnitAverage F μ s hs v (J F μ s hs f)) = _
  rw [hA]
  rfl

private abbrev N := globalThetaSobolevCompletion F μ 0 0 0 s hs

private def polarWeilTest (v : Place F) : P F →L[ℂ] P F :=
  ((globalWeilPrincipalValue F v).comp (P F).subtypeL).codRestrict _
    (globalWeilPrincipalValue_mem_polar F v)

private abbrev embedPolarTest := (globalThetaSobolevDenseMap F μ 0 0 0 s hs).comp (polarTestClass F)

private theorem embedPolarTest_dense : DenseRange (embedPolarTest F μ s hs) := by
  have h : Surjective (polarTestClass F) :=
    ((globalThetaOperator F).ker.isOpenQuotientMap_mkQL.restrictPreimage (GlobalPolarTheta F)).surjective
  exact (globalThetaSobolevCompletion_dense F μ 0 0 0 s hs).comp h.denseRange
    (globalThetaSobolevDenseMap F μ 0 0 0 s hs).continuous

/-- Restrict the bounded Weil operator to the intrinsic theta completion. -/
def globalThetaSobolevWeilPrincipalValue (v : Place F) : N F μ s hs →L[ℂ] N F μ s hs :=
  ((globalSobolevWeilPrincipalValue F μ s hs v).comp (N F μ s hs).subtypeL).codRestrict _
    (fun x => globalSobolevWeilPrincipalValue_mapsTo_theta F μ s hs v x.property)

theorem globalThetaSobolevWeilPrincipalValue_on_polarTests (v : Place F) (f : P F) :
    globalThetaSobolevWeilPrincipalValue F μ s hs v (embedPolarTest F μ s hs f) =
      embedPolarTest F μ s hs (polarWeilTest F v f) :=
  Subtype.ext (globalSobolevWeilPrincipalValue_on_polarTests F μ s hs v f)

/-- Density makes the bounded extension of the original test operator unique. -/
theorem globalThetaSobolevWeilPrincipalValue_unique (v : Place F)
    (A : N F μ s hs →L[ℂ] N F μ s hs)
    (hA : ∀ f : P F, A (embedPolarTest F μ s hs f) = embedPolarTest F μ s hs (polarWeilTest F v f)) :
    A = globalThetaSobolevWeilPrincipalValue F μ s hs v := by
  apply DFunLike.coe_injective
  exact (embedPolarTest_dense F μ s hs).equalizer A.continuous
    (globalThetaSobolevWeilPrincipalValue F μ s hs v).continuous
    (funext fun f => (hA f).trans (globalThetaSobolevWeilPrincipalValue_on_polarTests F μ s hs v f).symm)

private theorem thetaSobolevWeil_commute (v w : Place F) :
    Commute (globalThetaSobolevWeilPrincipalValue F μ s hs v)
      (globalThetaSobolevWeilPrincipalValue F μ s hs w) := by
  let X := globalThetaSobolevWeilPrincipalValue F μ s hs v
  let Y := globalThetaSobolevWeilPrincipalValue F μ s hs w
  change X.comp Y = Y.comp X
  apply DFunLike.coe_injective
  exact (embedPolarTest_dense F μ s hs).equalizer (X.comp Y).continuous (Y.comp X).continuous
    (funext fun f => by
      change X (Y (embedPolarTest F μ s hs f)) = Y (X (embedPolarTest F μ s hs f))
      dsimp only [X, Y]
      simp only [globalThetaSobolevWeilPrincipalValue_on_polarTests]
      apply congrArg (embedPolarTest F μ s hs)
      apply Subtype.ext
      exact DFunLike.congr_fun (globalWeilPrincipalValue_commute F v w).eq f.val)

/-- The finite product of the bounded Weil operators on the theta completion. -/
def globalThetaSobolevWeilPrincipalValues (S : Finset (Place F)) : N F μ s hs →L[ℂ] N F μ s hs :=
  S.noncommProd (globalThetaSobolevWeilPrincipalValue F μ s hs)
    (fun v _ w _ _ => thetaSobolevWeil_commute F μ s hs v w)

private theorem polarWeilTest_commute (v w : Place F) : Commute (polarWeilTest F v) (polarWeilTest F w) := by
  ext f : 1
  apply Subtype.ext
  exact DFunLike.congr_fun (globalWeilPrincipalValue_commute F v w).eq f.val

private def polarWeilTests (S : Finset (Place F)) : P F →L[ℂ] P F :=
  S.noncommProd (polarWeilTest F) (fun v _ w _ _ => polarWeilTest_commute F v w)

theorem globalThetaSobolevWeilPrincipalValues_on_polarTests (S : Finset (Place F)) (f : P F) :
    globalThetaSobolevWeilPrincipalValues F μ s hs S (embedPolarTest F μ s hs f) =
      embedPolarTest F μ s hs (polarWeilTests F S f) ∧
    (polarWeilTests F S f).val = globalWeilPrincipalValues F S f.val := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
    have hW : globalThetaSobolevWeilPrincipalValues F μ s hs ∅ = 1 :=
      Finset.noncommProd_empty _ _
    have hP : polarWeilTests F ∅ = 1 := Finset.noncommProd_empty _ _
    have hG : globalWeilPrincipalValues F ∅ = 1 := Finset.noncommProd_empty _ _
    rw [hW, hP, hG]
    exact ⟨rfl, rfl⟩
  | @insert v S hv ih =>
    have hW : globalThetaSobolevWeilPrincipalValues F μ s hs (insert v S) =
        (globalThetaSobolevWeilPrincipalValues F μ s hs S).comp
          (globalThetaSobolevWeilPrincipalValue F μ s hs v) :=
      Finset.noncommProd_insert_of_notMem' _ _ _ _ hv
    have hP : polarWeilTests F (insert v S) = (polarWeilTests F S).comp (polarWeilTest F v) :=
      Finset.noncommProd_insert_of_notMem' _ _ _ _ hv
    have hG : globalWeilPrincipalValues F (insert v S) =
        (globalWeilPrincipalValues F S).comp (globalWeilPrincipalValue F v) :=
      Finset.noncommProd_insert_of_notMem' _ _ _ _ hv
    rw [hW, hP, hG]
    simp only [ContinuousLinearMap.comp_apply]
    obtain ⟨h₁, h₂⟩ := ih (polarWeilTest F v f)
    exact ⟨(congrArg (globalThetaSobolevWeilPrincipalValues F μ s hs S)
      (globalThetaSobolevWeilPrincipalValue_on_polarTests F μ s hs v f)).trans h₁, h₂⟩

/-- The product extension preserves the norm-one isotype of each vector. -/
theorem globalThetaSobolevWeilPrincipalValues_preserves_isotype (S : Finset (Place F))
    (ω : PontryaginDual (K F)) (x : N F μ s hs)
    (hx : x.val ∈ globalAmbientSobolevIsotype F ω μ 0 0 s hs) :
    (globalThetaSobolevWeilPrincipalValues F μ s hs S x).val ∈
      globalAmbientSobolevIsotype F ω μ 0 0 s hs := by
  induction S using Finset.induction_on generalizing x with
  | empty =>
    have hW : globalThetaSobolevWeilPrincipalValues F μ s hs ∅ = 1 := Finset.noncommProd_empty _ _
    rw [hW]
    exact hx
  | @insert v S hv ih =>
    have hW : globalThetaSobolevWeilPrincipalValues F μ s hs (insert v S) =
        (globalThetaSobolevWeilPrincipalValues F μ s hs S).comp
          (globalThetaSobolevWeilPrincipalValue F μ s hs v) :=
      Finset.noncommProd_insert_of_notMem' _ _ _ _ hv
    rw [hW]
    exact ih (globalThetaSobolevWeilPrincipalValue F μ s hs v x)
      (globalSobolevWeilPrincipalValue_mapsTo_isotype F μ s hs v ω hx)

/-- The finite product is the unique continuous extension of its test action. -/
theorem globalThetaSobolevWeilPrincipalValues_unique (S : Finset (Place F))
    (A : N F μ s hs →L[ℂ] N F μ s hs)
    (hA : ∀ f : P F, A (embedPolarTest F μ s hs f) = embedPolarTest F μ s hs (polarWeilTests F S f)) :
    A = globalThetaSobolevWeilPrincipalValues F μ s hs S := by
  apply DFunLike.coe_injective
  exact (embedPolarTest_dense F μ s hs).equalizer A.continuous
    (globalThetaSobolevWeilPrincipalValues F μ s hs S).continuous
    (funext fun f => (hA f).trans (globalThetaSobolevWeilPrincipalValues_on_polarTests F μ s hs S f).1.symm)

/-- Completing the test image gives the closure of the operator range. -/
theorem globalThetaSobolevWeilPrincipalValues_closure (S : Finset (Place F)) :
    closure (range fun f : P F => embedPolarTest F μ s hs (polarWeilTests F S f)) =
      closure (range (globalThetaSobolevWeilPrincipalValues F μ s hs S)) := by
  let A := globalThetaSobolevWeilPrincipalValues F μ s hs S
  let J := embedPolarTest F μ s hs
  let B := range (fun f : P F => J (polarWeilTests F S f))
  have htest (f : P F) : A (J f) = J (polarWeilTests F S f) :=
    (globalThetaSobolevWeilPrincipalValues_on_polarTests F μ s hs S f).1
  change closure B = closure (range A)
  apply le_antisymm
  · apply closure_mono
    rintro _ ⟨f, rfl⟩
    exact ⟨J f, htest f⟩
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨x, rfl⟩
    exact (embedPolarTest_dense F μ s hs).induction_on x
      (isClosed_closure.preimage A.continuous) fun f =>
        subset_closure ⟨f, (htest f).symm⟩

end
end Masullo
