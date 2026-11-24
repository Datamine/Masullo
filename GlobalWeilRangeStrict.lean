import UnramifiedOrbitalQuotient
import SLocalEulerPoles

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField FourierTransform SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev S := 𝓢(ℝ, ℂ)
private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I

local instance strictWeilQMeasure : MeasurableSpace (Q F) := borel _
local instance strictWeilQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance strictWeilQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance strictWeilQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance strictWeilQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance strictWeilKMeasure : MeasurableSpace (K F) := borel _
local instance strictWeilKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance strictWeilKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)
local instance strictWeilKFinite : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
private abbrev μ := globalClassMeasure F ν
local instance strictWeilSplitHaar : (μ F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν
private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F (μ F ν) s hs ω

set_option maxHeartbeats 1400000 in
/-- A zero added by the larger product, absent from the smaller product,
separates their closed ranges before multiplication by the cutoffs. -/
theorem globalClosedPrincipalValueRange_lt_of_new_zero
    {A B : Finset (Place F)} (hAB : A ⊆ B) (hs₁ : 1 < s)
    (ω : PontryaginDual (K F))
    (hB : ∀ v ∈ B, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (ξ : ℝ)
    (hA₀ : globalWeilMomentMultiplicity F A ω (normOneEulerCharacter F ω) (zAt ξ) = 0)
    (hB₀ : 0 < globalWeilMomentMultiplicity F B ω (normOneEulerCharacter F ω) (zAt ξ)) :
    globalClosedPrincipalValueRange F (μ F ν) s hs ω B <
      globalClosedPrincipalValueRange F (μ F ν) s hs ω A := by
  classical
  let P (D : Finset (Place F)) := globalWeilIsotypeProduct F (μ F ν) s hs D ω
  let J := globalWeilSchwartzTest F s hs ν ω
  let J₀ := globalZeroLineSchwartzIsotype F ν s ω⁻¹
  obtain ⟨as,_,ha,hca⟩ := exists_globalZeroLineWeil_shiftModel F ν s hs A ω
  obtain ⟨bs,hb,_,hcb⟩ := exists_globalZeroLineWeil_shiftModel F ν s hs B ω
  let i : radialWeilJetIndices bs := ⟨(ξ,0),by
    change 0 < bs.countP _
    rw [hcb]
    exact hB₀⟩
  obtain ⟨b,_,hbi⟩ := exists_radialWeilJet_frequency_interpolant bs hb i
  let f : S := 𝓕⁻ b
  have hf : 𝓕 f ξ = 1 := by
    have h := hbi i
    simp only [ite_true] at h
    rw [show 𝓕 f = b from FourierTransform.fourier_fourierInv_eq b]
    exact h
  have hsym : radialWeilProductSymbol as ξ ≠ 0 := by
    have hzero := (hca ξ).trans hA₀
    have hn (p : ℝ × ℂ) (hp : p ∈ as) : radialWeilDifferenceSymbol p.1 p.2 ξ ≠ 0 := by
      have h := List.countP_eq_zero.mp hzero p hp
      simpa only [decide_eq_true_eq] using h
    unfold radialWeilProductSymbol
    apply List.prod_ne_zero
    intro hz
    obtain ⟨p,hp,hp₀⟩ := List.mem_map.mp hz
    exact hn p hp hp₀
  let x := (P A (J f)).val
  let p := radialWeilDifferenceProduct as f
  have hAf : x = J₀ p := ha f
  let χ := normOneEulerCharacter F ω
  have hre : (zAt ξ).re = 0 := by simp [Complex.mul_re]
  have hm : ((0 : ℕ) : ℝ) < (s-1)/2 := by push_cast; linarith
  let M := orbitalSobolevMomentCLM F (μ F ν) s hs χ (zAt ξ) hre 0 hm
  have hM : M x ≠ 0 := by
    rw [hAf, orbitalSobolevMomentCLM_apply, globalZeroLineSchwartzIsotype_moment F ν s ω p]
    have he := radialSchwartz_fourierJet_eq_moment p 0 ξ
    simp only [iteratedDeriv_zero, pow_zero, one_mul] at he
    simp only [pow_zero, one_mul]
    rw [← he, show p = radialWeilDifferenceProduct as f from rfl,
      fourier_radialWeilDifferenceProduct, hf, mul_one]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := ν)).ne') hsym
  apply lt_of_le_of_ne (globalClosedPrincipalValueRange_antitone F (μ F ν) s hs ω hAB)
  intro hEq
  have ha : P A (J f) ∈ globalWeilIsotypeClosedRange F (μ F ν) s hs A ω :=
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)
  have hb' : P A (J f) ∈ globalWeilIsotypeClosedRange F (μ F ν) s hs B ω := by
    rw [globalWeilIsotypeClosedRange_eq_unramified F (μ F ν) s hs B ω hB, hEq]
    rw [globalWeilIsotypeClosedRange_eq_unramified F (μ F ν) s hs A ω
      (fun v hv ↦ hB v (hAB hv))] at ha
    exact ha
  have hx : x ∈ closure (range fun u : H F ν s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs B ⟨u.val,u.property.1⟩).val) := by
    have he : P A (J f) ∈ closure (range (P B)) := hb'
    rw [closure_subtype, ← range_comp] at he
    exact he
  exact hM (globalClosedWeilIsotypeRange_moment_zero F (μ F ν) s hs B ω χ (zAt ξ)
    hre 0 hm hB₀ x hx)

set_option maxHeartbeats 1300000 in
/-- Before the cutoff, adding a place with a new rational residue prime
makes the inclusion of the completed principal-value images strict. -/
theorem globalClosedPrincipalValueRange_lt_of_new_residuePrime
    {A B : Finset (Place F)} (hAB : A ⊆ B) (hs₁ : 1 < s)
    (ω : PontryaginDual (K F))
    (hB : ∀ v ∈ B, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (v : Place F) (hv : v ∈ B) (hnew : ∀ w ∈ A, finiteResiduePrime F v ≠ finiteResiduePrime F w) :
    globalClosedPrincipalValueRange F (μ F ν) s hs ω B <
      globalClosedPrincipalValueRange F (μ F ν) s hs ω A := by
  classical
  let χ := normOneEulerCharacter F ω
  have hχ (k : K F) : ω k = χ k.val := by
    change ω k = ω (ideleClassNormOnePart F k.val)
    congr 1
    apply Subtype.ext
    change k.val = k.val / ideleClassExpSection F (ideleClassLogNorm F k.val)
    have hk : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = _
      rw [k.property, Real.log_one]
      rfl
    rw [hk, map_one, div_one]
  have hu (w : Place F) (hw : w ∈ B) : unramifiedFiniteCharacter F χ w :=
    (globalSobolevFiniteUnitInclusion_trivial_iff F ω χ hχ w).mp (hB w hw)
  let C (w : Place F) := {z : ℂ | v ∈ globalFiniteHeckeEulerPoles F χ z ∧
    w ∈ globalFiniteHeckeEulerPoles F χ z}
  have hfin : (⋃ w ∈ (A : Set (Place F)), C w).Finite :=
    A.finite_toSet.biUnion (fun w hw ↦
      (globalFiniteHeckeEuler_commonPoles F χ v w (hnew w hw)).finite)
  obtain ⟨z, hz, hmiss⟩ :=
    ((globalFiniteHeckeEuler_poleParameters_infinite F χ v (hu v hv)).sdiff hfin).nonempty
  have hlocal (w : Place F) (hw : w ∈ B) :
      w ∈ globalFiniteHeckeEulerPoles F χ z ↔ orbitalEulerDenominator F {w} χ z = 0 := by
    rw [orbitalEulerDenominator_eq_hecke F {w} χ
      (fun a ha ↦ hu a ((Finset.mem_singleton.mp ha).symm ▸ hw)) z, Finset.prod_singleton]
    rfl
  have hzv : orbitalEulerDenominator F {v} χ z = 0 := (hlocal v hv).mp hz
  have hzre := orbitalEulerDenominator_zero_re F {v} χ hzv
  let ξ := -z.im / (2 * Real.pi)
  have he : zAt ξ = z := by
    apply Complex.ext
    · simpa [Complex.mul_re] using hzre.symm
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      dsimp [ξ]
      field_simp [Real.pi_ne_zero]
  let D (w : Place F) : Prop := orbitalEulerDenominator F {w} χ z = 0
  have hCount (W : Finset (Place F)) (hW : W ⊆ B) :
      globalWeilMomentMultiplicity F W ω χ z = (W.filter D).card := by
    have hcast : (globalWeilMomentMultiplicity F W ω χ z : ℕ∞) = ((W.filter D).card : ℕ∞) := by
      rw [globalWeilMomentMultiplicity_eq_eulerOrder F W ω χ z (fun w hw ↦ hB w (hW hw)),
        orbitalEulerDenominator_order_eq_card]
      apply congrArg (fun U : Finset (Place F) ↦ (U.card : ℕ∞))
      apply Finset.filter_congr
      intro w _
      simp [D, orbitalEulerDenominator]
    exact_mod_cast hcast
  apply globalClosedPrincipalValueRange_lt_of_new_zero F ν s hs hAB hs₁ ω hB ξ <;> rw [he]
  · rw [hCount A hAB, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hzero
    exact hmiss (mem_iUnion₂.mpr ⟨w,hw,hz,(hlocal w (hAB hw)).mpr hzero⟩)
  · rw [hCount B (subset_refl _), Finset.card_pos]
    exact ⟨v,Finset.mem_filter.mpr ⟨hv,hzv⟩⟩

end
end Masullo
