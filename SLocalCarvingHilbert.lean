import SLocalCarvingOrbit
import GlobalOrbitalHomogeneousDensity
import GlobalMellinPadding

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev r (q : Q F) := (ideleClassLogNorm F q).toAdd

local instance : MeasurableSpace (Q F) := borel _
local instance : BorelSpace (Q F) := ⟨rfl⟩
local instance : T2Space (Q F) := ideleClasses_hausdorff
local instance : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : CompactSpace (K F) := normOneIdeleClass_compact F
local instance (S : Finset (Place F)) : MeasurableSpace (SLocalThetaNormOne F S) := borel _
local instance (S : Finset (Place F)) : BorelSpace (SLocalThetaNormOne F S) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
local instance : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
private abbrev μ := globalClassMeasure F ν
local instance : (μ F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν

private theorem logNorm_preserving :
    MeasurePreserving (r F) (μ F ν) (ν univ • (volume : Measure ℝ)) := by
  have hr : Measurable (r F) := (continuous_toAdd.comp (ideleClassLogNorm_continuous F)).measurable
  refine ⟨hr, ?_⟩
  unfold μ globalClassMeasure
  rw [Measure.map_map hr (ideleClassLogCoordinates F).continuous.measurable]
  have he : r F ∘ ideleClassLogCoordinates F = Prod.fst := funext (log_norm_coordinates F)
  rw [he, Measure.map_fst_prod]

private theorem carving_amplitude_pos (s t : ℝ) : 0 < hardySobolevAmplitude 0 0 s t := by
  unfold hardySobolevAmplitude hardySobolevWeight
  exact Real.sqrt_pos.mpr (mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _))

private theorem amplitude_le_exp_abs (s : ℝ) (hs : 0 ≤ s) (t : ℝ) :
    hardySobolevAmplitude 0 0 s t ≤ Real.exp ((s/2) * |t|) := by
  have ht : 1 + |t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
  have he : 1 + t^2 ≤ Real.exp (2 * |t|) := by
    calc
      1 + t^2 ≤ (1 + |t|)^2 := by
        nlinarith [abs_nonneg t, sq_abs t]
      _ ≤ Real.exp |t| ^ 2 := pow_le_pow_left₀ (by positivity) ht _
      _ = _ := by rw [pow_two, ← Real.exp_add]; ring_nf
  have hp := Real.rpow_le_rpow (show 0 ≤ 1 + t^2 by positivity) he (show 0 ≤ s/4 by positivity)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hp
  have hForm : hardySobolevAmplitude 0 0 s t = (1+t^2) ^ (s/4) := by
    simp only [hardySobolevAmplitude, hardySobolevWeight, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul,
      Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hForm]
  rw [show 2 * |t| * (s/4) = (s/2) * |t| by ring] at hp
  exact hp

private theorem amp_exp_ratio_bounded (s : ℝ) (hs : 0 ≤ s) (a t : ℝ) (ht : a ≤ t) :
    hardySobolevAmplitude 0 0 s t ≤
      Real.exp ((s+1) * |a|) * Real.exp ((s/2+1) * t) := by
  apply (amplitude_le_exp_abs s hs t).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases hz : 0 ≤ t
  · rw [abs_of_nonneg hz]
    nlinarith [mul_nonneg (show 0 ≤ s+1 by positivity) (abs_nonneg a)]
  · rw [abs_of_neg (lt_of_not_ge hz)]
    have hh : -t ≤ |a| := (neg_le_neg ht).trans (neg_le_abs a)
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ s+1 by positivity)]

variable (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
  (ω : PontryaginDual (K F))
  (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (Q F))))

private abbrev m := globalNormOneToSLocal F S hS
private abbrev η := Measure.map (m F S hS) ν
private abbrev σ := sLocalNormOneCharacterOfGlobal F ω S hS hω

local instance : (η F ν S hS).IsHaarMeasure :=
  ν.isHaarMeasure_map_of_isFiniteMeasure (m F S hS).toMonoidHom (m F S hS).continuous
    (globalNormOneToSLocal_surjective F S hS)

private abbrev θ (f : sLocalBruhatImage F S) (t : ℝ) :=
  sLocalHomogeneousTheta F S (η F ν S hS) (σ F S hS ω hω) f.val (sLocalLogNormRay F S t)

private theorem theta_continuous (f : sLocalBruhatImage F S) :
    Continuous (θ F ν S hS ω hω f) :=
  (sLocalHomogeneousTheta_continuous F S (η F ν S hS) (σ F S hS ω hω) f.val).comp
    (QuotientGroup.continuous_mk.comp ((sLocalExpSection_continuous F S).comp continuous_ofAdd))

variable (s : ℝ) (hs : 0 ≤ s)
variable (U : Set (Q F)) (hU : MeasurableSet U)
private abbrev ρ := U.indicator (fun _ ↦ (1 : ℝ))
private abbrev amp (q : Q F) := hardySobolevAmplitude 0 0 s (r F q)
private abbrev generator (f : sLocalBruhatImage F S) (q : Q F) : ℂ :=
  (ρ F U q : ℂ) * ((amp F s q : ℂ) * sLocalCarvingAverage F S ω ν f q)

include hS hω hs hU in
set_option maxHeartbeats 1800000 in
private theorem generator_memLp (a : ℝ) (hSupp : ∀ q ∈ U, a ≤ r F q)
    (f : sLocalBruhatImage F S) :
    MemLp (generator F ν S ω s U f) 2 (μ F ν) := by
  classical
  let α := s/2 + 1
  have hα : 0 < α := by dsimp [α]; linarith
  obtain ⟨c,C,hc,hC,hI,hθ⟩ := sLocalRadialMellin_strip_majorant F S (sLocalExpSection F S)
    (sLocalIdeleNorm_expSection F S) (η F ν S hS) (σ F S hS ω hω) {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) α α hα
  let D := Real.exp ((s+1)*|a|)
  let B (t : ℝ) := D * (C * Real.exp (-c * |t|))
  have hBcont : Continuous B := by dsimp [B]; fun_prop
  have hBInt : Integrable B := hI.const_mul D
  have hBpos (t) : 0 ≤ B t := by dsimp [B,D]; positivity
  have hBbd (t) : B t ≤ D*C := by
    dsimp [B]
    have he := Real.exp_le_one_iff.mpr (show -c * |t| ≤ 0 by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (abs_nonneg t))
    have hDC : 0 ≤ D*C := mul_nonneg (Real.exp_pos _).le hC.le
    nlinarith [mul_le_mul_of_nonneg_left he hDC]
  have hB2 : MemLp B 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq_norm hBcont.aestronglyMeasurable).2
    apply (hBInt.const_mul (D*C)).mono'
    · fun_prop
    · exact .of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (hBpos t), Real.norm_of_nonneg (sq_nonneg (B t)), pow_two]
        exact mul_le_mul_of_nonneg_right (hBbd t) (hBpos t)
  have hMp : MemLp (B ∘ r F) 2 (μ F ν) :=
    (hB2.smul_measure (measure_ne_top ν univ)).comp_measurePreserving (logNorm_preserving F ν)
  have hθCont : Continuous (sLocalCarvingAverage F S ω ν f) := by
    exact ((sLocalHomogeneousTheta_continuous F S (η F ν S hS) (σ F S hS ω hω) f.val).comp
      (sLocalCarvingClassMap F S hS).continuous).congr
        (fun q ↦ (sLocalCarvingTheta_average_eq_local F S hS ω hω ν f q).symm)
  have haCont : Continuous (amp F s) :=
    (Real.continuous_sqrt.comp (continuous_hardySobolevWeight 0 0 s)).comp
      (continuous_toAdd.comp (ideleClassLogNorm_continuous F))
  have hρ : Measurable (ρ F U) := measurable_const.indicator hU
  refine hMp.mono' (((Complex.continuous_ofReal.measurable.comp hρ).mul
    ((Complex.continuous_ofReal.comp haCont).mul hθCont).measurable).aestronglyMeasurable) ?_
  exact .of_forall fun q ↦ by
    by_cases hq : q ∈ U
    · have hb := hθ f (mem_singleton f) (α : ℂ) (by simp) (by simp) (r F q)
      rw [norm_mul, Complex.norm_exp, show ((↑α : ℂ) * ↑(r F q)).re = α * r F q by
        simp [Complex.mul_re]] at hb
      change ‖(ρ F U q : ℂ) * ((amp F s q : ℂ) * sLocalCarvingAverage F S ω ν f q)‖ ≤ B (r F q)
      rw [show ρ F U q = 1 from indicator_of_mem hq _, Complex.ofReal_one, one_mul,
        sLocalCarvingAverage_radial F S hS ω hω ν, norm_mul, norm_mul, norm_inv, Circle.norm_coe,
        inv_one, one_mul, Complex.norm_real, Real.norm_of_nonneg (carving_amplitude_pos s (r F q)).le]
      calc
        _ ≤ (D * Real.exp (α * r F q)) * ‖θ F ν S hS ω hω f (r F q)‖ :=
          mul_le_mul_of_nonneg_right (amp_exp_ratio_bounded s hs a (r F q) (hSupp q hq)) (norm_nonneg _)
        _ ≤ B (r F q) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    · change ‖(ρ F U q : ℂ) * _‖ ≤ B (r F q)
      rw [show ρ F U q = 0 from indicator_of_notMem hq _, Complex.ofReal_zero, zero_mul, norm_zero]
      exact hBpos _

variable (a : ℝ) (hSupp : ∀ q ∈ U, a ≤ r F q)

private abbrev L := Lp ℂ 2 (μ F ν)
private abbrev H := globalOrbitalSobolevIsotype F (μ F ν) s hs ω
private abbrev P := ((GlobalBruhat.polarEvaluation F).comp (sLocalBruhatImage F S).subtypeL).ker

/-- The projected outside-unit orbit sum in the weighted zero-line Hilbert
chart, after cutting off below a finite logarithmic modulus. -/
def sLocalCutoffCarvingGenerator (f : sLocalBruhatImage F S) : L F ν :=
  (generator_memLp F ν S hS ω hω s hs U hU a hSupp f).toLp (generator F ν S ω s U f)

theorem sLocalCutoffCarvingGenerator_ae (f : sLocalBruhatImage F S) :
    (sLocalCutoffCarvingGenerator F ν S hS ω hω s hs U hU a hSupp f : Q F → ℂ) =ᵐ[μ F ν]
      fun q ↦ (ρ F U q : ℂ) * ((amp F s q : ℂ) * sLocalCarvingAverage F S ω ν f q) :=
  (generator_memLp F ν S hS ω hω s hs U hU a hSupp f).coeFn_toLp

variable (hInv : ∀ (k : K F) (q : Q F), k.val⁻¹ * q ∈ U ↔ q ∈ U)
variable (h₀ : ∀ q, 0 ≤ ρ F U q) (h₁ : ∀ q, ρ F U q ≤ 1)
private abbrev M : L F ν →L[ℂ] L F ν :=
  cutoffOperator (ρ F U) (measurable_const.indicator hU) h₀ h₁

include hInv in
set_option maxHeartbeats 1800000 in
private theorem generator_mem_cutoff_range (f : sLocalBruhatImage F S) :
    sLocalCutoffCarvingGenerator F ν S hS ω hω s hs U hU a hSupp f ∈
      range (fun z : H F ν ω s hs ↦ M F ν U hU h₀ h₁ z.val) := by
  let v := sLocalCutoffCarvingGenerator F ν S hS ω hω s hs U hU a hSupp f
  let A := sLocalCarvingAverage F S ω ν f
  have hv := sLocalCutoffCarvingGenerator_ae F ν S hS ω hω s hs U hU a hSupp f
  have hvIso : v ∈ globalAmbientSobolevIsotype F ω (μ F ν) 0 0 s hs := by
    apply (mem_thetaCharacterSubspace _ _ _).mpr
    intro k
    let g : Q F := k.val
    let T := hardySobolevMulTranslation (μ F ν) (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 s hs g
    have hg : ideleClassLogNorm F g = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = _
      rw [k.property, Real.log_one]
      rfl
    have hgpart : ideleClassNormOnePart F g = k := by
      apply Subtype.ext
      change g / ideleClassExpSection F (ideleClassLogNorm F g) = g
      rw [hg, map_one, div_one]
    change T v = (ω k : ℂ) • v
    apply Lp.ext
    filter_upwards [hardySobolevMulTranslation_ae (μ F ν) (ideleClassLogNorm F)
        (ideleClassLogNorm_continuous F) 0 0 s hs g v,
      (measurePreserving_mul_left (μ F ν) g⁻¹).quasiMeasurePreserving.ae_eq_comp hv,
      Lp.coeFn_smul (ω k : ℂ) v, hv] with q ht hx hsml hq
    have hr : r F (g⁻¹ * q) = r F q := by
      change (ideleClassLogNorm F (g⁻¹ * q)).toAdd = _
      rw [map_mul, map_inv, hg, inv_one, one_mul]
    have hp : ideleClassNormOnePart F (g⁻¹ * q) = k⁻¹ * ideleClassNormOnePart F q := by
      let N := (MonoidHom.fst (K F) (Multiplicative ℝ)).comp (ideleClassSplit F).toMonoidHom
      change N (g⁻¹ * q) = k⁻¹ * N q
      rw [map_mul, map_inv, show N g = k from hgpart]
    have hρ : ρ F U (g⁻¹ * q) = ρ F U q := by
      by_cases hqU : q ∈ U
      · have hxU : g⁻¹ * q ∈ U := (hInv k q).mpr hqU
        rw [show ρ F U (g⁻¹ * q) = 1 from indicator_of_mem hxU _,
          show ρ F U q = 1 from indicator_of_mem hqU _]
      · have hxU : g⁻¹ * q ∉ U := fun hh ↦ hqU ((hInv k q).mp hh)
        rw [show ρ F U (g⁻¹ * q) = 0 from indicator_of_notMem hxU _,
          show ρ F U q = 0 from indicator_of_notMem hqU _]
    have hA : A (g⁻¹ * q) = (ω k : ℂ) * A q := by
      change sLocalCarvingAverage F S ω ν f (g⁻¹ * q) =
        (ω k : ℂ) * sLocalCarvingAverage F S ω ν f q
      rw [sLocalCarvingAverage_radial F S hS ω hω ν, sLocalCarvingAverage_radial F S hS ω hω ν]
      change (((ω (ideleClassNormOnePart F (g⁻¹ * q)) : Circle) : ℂ)⁻¹) *
          θ F ν S hS ω hω f (r F (g⁻¹ * q)) =
        (ω k : ℂ) * ((((ω (ideleClassNormOnePart F q) : Circle) : ℂ)⁻¹) *
          θ F ν S hS ω hω f (r F q))
      rw [hr, hp, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_inv_rev, inv_inv]
      ring
    change v (g⁻¹ * q) = (ρ F U (g⁻¹ * q) : ℂ) * ((amp F s (g⁻¹ * q) : ℂ) * A (g⁻¹ * q)) at hx
    change v q = (ρ F U q : ℂ) * ((amp F s q : ℂ) * A q) at hq
    change T v q = ((ω k : ℂ) • v : L F ν) q
    rw [ht, hx, hsml, Pi.smul_apply, hq, hρ, hA]
    change ((amp F s q / amp F s (g⁻¹ * q) : ℝ) : ℂ) *
      ((ρ F U q : ℂ) * ((amp F s (g⁻¹ * q) : ℂ) * ((ω k : ℂ) * A q))) =
      (ω k : ℂ) * ((ρ F U q : ℂ) * ((amp F s q : ℂ) * A q))
    have ha : amp F s (g⁻¹ * q) = amp F s q := congrArg (hardySobolevAmplitude 0 0 s) hr
    rw [ha, div_self (carving_amplitude_pos s (r F q)).ne', Complex.ofReal_one, one_mul]
    ring
  refine ⟨⟨v, globalThetaSobolevMap_zeroLine_dense_of_haar F (μ F ν) s hs v, hvIso⟩, ?_⟩
  change M F ν U hU h₀ h₁ v = v
  apply Lp.ext
  filter_upwards [cutoffOperator_ae (ρ F U) (measurable_const.indicator hU) h₀ h₁ v, hv] with q hcut hq
  rw [hcut, hq]
  by_cases hqU : q ∈ U
  · rw [show ρ F U q = 1 from indicator_of_mem hqU _]
    simp
  · rw [show ρ F U q = 0 from indicator_of_notMem hqU _]
    simp

include hInv in
set_option maxHeartbeats 1700000 in
/-- For any invariant measurable modulus cutoff bounded below, the actual
S-local two-evaluation generators are dense in the entire cutoff isotype. -/
theorem sLocalCutoffCarvingGenerator_closure :
    closure (range fun f : P F S ↦ sLocalCutoffCarvingGenerator F ν S hS ω hω s hs U hU a hSupp f.val) =
      range (fun z : H F ν ω s hs ↦ M F ν U hU h₀ h₁ z.val) := by
  let C := M F ν U hU h₀ h₁
  let X := closure (range fun f : P F S ↦ sLocalCutoffCarvingGenerator F ν S hS ω hω s hs U hU a hSupp f.val)
  let J := globalZeroLineSchwartzIsotype F ν s ω⁻¹
  apply le_antisymm
  · apply closure_minimal _ (isClosed_globalOrbitalIsotype_cutoff_range F s hs (μ F ν) ω U hU hInv h₀ h₁)
    rintro _ ⟨f,rfl⟩
    exact generator_mem_cutoff_range F ν S hS ω hω s hs U hU a hSupp hInv h₀ h₁ f.val
  · have hCompact (p : 𝓢(ℝ, ℂ)) (hp : HasCompactSupport p) : C (J p) ∈ X := by
      obtain ⟨f,hf,hProfile⟩ :=
        exists_sLocalCarvingPolarFree_on_halfline F S hS ω hω ν p.smooth' hp a
      apply subset_closure
      refine ⟨⟨f,hf⟩, ?_⟩
      apply Lp.ext
      filter_upwards [sLocalCutoffCarvingGenerator_ae F ν S hS ω hω s hs U hU a hSupp f,
        cutoffOperator_ae (ρ F U) (measurable_const.indicator hU) h₀ h₁ (J p),
        globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ p] with q hgen hcut hj
      rw [hgen, hcut, hj]
      by_cases hq : q ∈ U
      · rw [hProfile q (hSupp q hq)]
        rw [show (ω⁻¹ (ideleClassNormOnePart F q) : ℂ) =
          ((ω (ideleClassNormOnePart F q) : Circle) : ℂ)⁻¹ from Circle.coe_inv _]
        rfl
      · rw [show ρ F U q = 0 from indicator_of_notMem hq _, Complex.ofReal_zero, zero_mul, zero_mul]
    have hAll : MapsTo C (range J) X := by
      rintro _ ⟨p,rfl⟩
      have hconv := ((C.comp J).continuous.continuousAt.tendsto.comp (truncateSchwartz_tendsto p))
      exact isClosed_closure.mem_of_tendsto hconv
        (Eventually.of_forall fun n ↦ hCompact _ (truncateSchwartz_hasCompactSupport n p))
    rintro _ ⟨z,rfl⟩
    have hz := globalZeroLineSchwartzIsotype_dense_in_ambient F ν s hs ω z.val z.property.2
    exact (closure_minimal hAll (isClosed_closure.preimage C.continuous)) hz

end
end Masullo
