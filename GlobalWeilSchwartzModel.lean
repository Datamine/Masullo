import GlobalZeroLineFrequencyCutoffs
import GlobalOrbitalSobolevMomentKernels
import RadialWeilFrequencyDivision

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical FourierTransform InnerProductSpace NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev S := 𝓢(ℝ, ℂ)
private abbrev r (q : Q F) := (ideleClassLogNorm F q).toAdd

local instance weilModelMeasurable : MeasurableSpace (Q F) := borel _
local instance weilModelBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance weilModelT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance weilModelLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance weilModelSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance weilModelKMeasurable : MeasurableSpace (K F) := borel _
local instance weilModelKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilModelKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

local instance weilModelKFinite : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
local instance weilModelHaar : (globalClassMeasure F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν

private abbrev μ := globalClassMeasure F ν
private abbrev W (ω : PontryaginDual (K F)) := globalAmbientSobolevIsotype F ω (μ F ν) 0 0 s hs
private abbrev J (ω : PontryaginDual (K F)) := globalZeroLineSchwartzIsotype F ν s ω⁻¹
private abbrev T (g : Q F) := hardySobolevMulTranslation (μ F ν)
  (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs g

private theorem logNorm_eq_one (k : K F) : ideleClassLogNorm F k.val = 1 := by
  change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = Multiplicative.ofAdd 0
  rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]

/-- The separated Schwartz profile with angular factor `ω⁻¹` belongs
to the norm-one eigenspace with translation character `ω`. -/
theorem globalZeroLineSchwartzIsotype_mem_ambient (ω : PontryaginDual (K F)) (p : S) :
    J F ν s ω p ∈ W F ν s hs ω := by
  apply (mem_thetaCharacterSubspace _ _ _).mpr
  intro k
  have h := globalZeroLineSchwartzIsotype_translate_normOne F ν s hs ω⁻¹ p k
  change T F ν s hs k.val (J F ν s ω p) = _ at h
  rw [h]
  change ((ω k : ℂ)⁻¹)⁻¹ • J F ν s ω p = (ω k : ℂ) • J F ν s ω p
  rw [inv_inv]

private theorem orthogonal_of_distinct_circle_eigenvalues {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (a b : Circle) (hab : a ≠ b) (x y : E)
    (hx : A x = (a : ℂ) • x) (hy : A y = (b : ℂ) • y) : ⟪x,y⟫_ℂ = 0 := by
  let I : E →ₗᵢ[ℂ] E := ⟨A.toLinearMap, hA⟩
  have h : ⟪A x, A y⟫_ℂ = ⟪x,y⟫_ℂ := I.inner_map_map x y
  rw [hx, hy, inner_smul_left, inner_smul_right, ← mul_assoc, ← Circle.coe_inv_eq_conj] at h
  have hn : ((a⁻¹ : Circle) : ℂ) * (b : ℂ) - 1 ≠ 0 := by
    intro hv
    apply hab
    have he : a⁻¹ * b = 1 := Subtype.ext (sub_eq_zero.mp hv)
    exact inv_mul_eq_one.mp he
  apply (mul_eq_zero.mp (show _ * ⟪x,y⟫_ℂ = 0 by rw [sub_mul, one_mul, h, sub_self])).resolve_left hn

set_option maxHeartbeats 1400000 in
private theorem isotype_mem_orthogonal {ω ψ : PontryaginDual (K F)} (hne : ω ≠ ψ)
    (u : Lp ℂ 2 (μ F ν)) (hu : u ∈ W F ν s hs ψ) : u ∈ (W F ν s hs ω)ᗮ := by
  apply (Submodule.mem_orthogonal (W F ν s hs ω) u).mpr
  intro v hv
  obtain ⟨k, hk⟩ : ∃ k, ω k ≠ ψ k := by
    by_contra! h
    exact hne (PontryaginDual.ext h)
  let L := T F ν s hs k.val
  have hn (x : Lp ℂ 2 (μ F ν)) : ‖L x‖ = ‖x‖ := by
    apply hardySobolevMulTranslation_norm_of_normOne
    exact logNorm_eq_one F k
  have hv' : L v = (ω k : ℂ) • v := (mem_thetaCharacterSubspace _ _ _).mp hv k
  have hu' : L u = (ψ k : ℂ) • u := (mem_thetaCharacterSubspace _ _ _).mp hu k
  exact orthogonal_of_distinct_circle_eigenvalues L hn (ω k) (ψ k) hk v u hv' hu'

/-- Separated radial Schwartz vectors are dense in the specified ambient isotype. -/
theorem globalZeroLineSchwartzIsotype_dense_in_ambient (ω : PontryaginDual (K F))
    (u : Lp ℂ 2 (μ F ν)) (hu : u ∈ W F ν s hs ω) :
    u ∈ closure (range (J F ν s ω)) := by
  let V := W F ν s hs ω
  letI : IsClosed (V : Set (Lp ℂ 2 (μ F ν))) :=
    globalAmbientSobolevIsotype_isClosed F ω (μ F ν) 0 0 s hs
  let P := V.starProjection
  let A := Submodule.span ℂ (range fun p : PontryaginDual (K F) × S ↦
    globalZeroLineSchwartzIsotype F ν s p.1 p.2)
  have hA : u ∈ closure (A : Set (Lp ℂ 2 (μ F ν))) :=
    globalZeroLineSchwartzIsotypes_span_dense F ν s u
  have hmap : MapsTo P (A : Set (Lp ℂ 2 (μ F ν))) (range (J F ν s ω)) := by
    have hle : A ≤ (J F ν s ω).range.comap P.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨χ,p⟩, rfl⟩
      by_cases he : χ = ω⁻¹
      · subst χ
        have hv : J F ν s ω p ∈ V := globalZeroLineSchwartzIsotype_mem_ambient F ν s hs ω p
        exact ⟨p, (Submodule.starProjection_eq_self_iff.mpr hv).symm⟩
      · have hn : ω ≠ χ⁻¹ := fun h ↦ he (by rw [h, inv_inv])
        have hv := globalZeroLineSchwartzIsotype_mem_ambient F ν s hs χ⁻¹ p
        have hv' : globalZeroLineSchwartzIsotype F ν s χ p ∈ W F ν s hs χ⁻¹ := by
          simpa only [J, inv_inv] using hv
        have hp : P (globalZeroLineSchwartzIsotype F ν s χ p) = 0 :=
          Submodule.eq_starProjection_of_mem_orthogonal (V.zero_mem)
            (by simpa only [sub_zero] using isotype_mem_orthogonal F ν s hs hn _ hv')
        exact ⟨0, (map_zero _).trans hp.symm⟩
    exact fun x hx ↦ hle hx
  have hu' : P u = u := Submodule.starProjection_eq_self_iff.mpr hu
  rw [← hu']
  exact hmap.closure P.continuous hA

/-- For a band-limited kernel, the cutoff of a general isotype vector
belongs to the closure of separated Schwartz vectors in the same fixed window. -/
theorem globalZeroLineRadialCutoff_mem_frequencyWindow (ω : PontryaginDual (K F))
    (u : Lp ℂ 2 (μ F ν)) (hu : u ∈ W F ν s hs ω) (φ : S) :
    globalZeroLineRadialCutoff F (μ F ν) s hs φ u ∈
      closure ((J F ν s ω) '' {p : S | tsupport ((𝓕 p : S) : ℝ → ℂ) ⊆ tsupport ((𝓕 φ : S) : ℝ → ℂ)}) := by
  apply MapsTo.closure _ (globalZeroLineRadialCutoff F (μ F ν) s hs φ).continuous
    (globalZeroLineSchwartzIsotype_dense_in_ambient F ν s hs ω u hu)
  rintro _ ⟨p,rfl⟩
  refine ⟨SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) p φ, ?_, ?_⟩
  · have he : ((𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) p φ) : S) : ℝ → ℂ) =
        ((𝓕 p : S) : ℝ → ℂ) * ((𝓕 φ : S) : ℝ → ℂ) := by
      rw [SchwartzMap.fourier_convolution]
      funext t
      exact SchwartzMap.pairing_apply_apply .. 
    change tsupport ((𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) p φ) : S) : ℝ → ℂ) ⊆
      tsupport ((𝓕 φ : S) : ℝ → ℂ)
    rw [he]
    exact tsupport_mul_subset_right
  · exact (globalZeroLineRadialCutoff_on_Schwartz F s hs ν φ ω⁻¹ p).symm

private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I
private abbrev C (ω : PontryaginDual (K F)) := normOneEulerCharacter F ω
private abbrev N := globalThetaSobolevCompletion F (μ F ν) 0 0 0 s hs

private def intoTheta : Lp ℂ 2 (μ F ν) →L[ℂ] N F ν s hs :=
  (ContinuousLinearMap.id ℂ _).codRestrict _
    (globalThetaSobolevMap_zeroLine_dense_of_haar F (μ F ν) s hs)

/-- The actual Weil product on the ambient chart, using verified theta density. -/
def globalZeroLineWeilProduct (A : Finset (Place F)) :
    Lp ℂ 2 (μ F ν) →L[ℂ] Lp ℂ 2 (μ F ν) :=
  (N F ν s hs).subtypeL.comp
    ((globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs A).comp (intoTheta F ν s hs))

private abbrev shift (ω : PontryaginDual (K F)) (v : Place F) : ℝ × ℂ :=
  (r F (globalUniformizerClass F v), (C F ω (globalUniformizerClass F v) : ℂ))

private theorem shift_nonzero (ω : PontryaginDual (K F)) (v : Place F) :
    (shift F ω v).1 ≠ 0 := by
  change Real.log (ideleClassNorm F (ideleClassMap F
    (singleFiniteIdele F v (chosenFiniteUniformizer F v)))) ≠ 0
  rw [ideleClassNorm_mk, singleFiniteIdele_norm,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), Real.log_inv, neg_ne_zero]
  exact (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).ne'

private theorem shift_symbol_eq_zero_iff (ω : PontryaginDual (K F)) (v : Place F) (ξ : ℝ) :
    radialWeilDifferenceSymbol (shift F ω v).1 (shift F ω v).2 ξ = 0 ↔
      orbitalMomentPhase F (C F ω) (zAt ξ) (globalUniformizerClass F v) = 1 := by
  let d := r F (globalUniformizerClass F v)
  have he : ((↑(-2 * Real.pi * d) : ℂ) * Complex.I) * (ξ : ℂ) =
      zAt ξ * (d : ℂ) := by
    dsimp only [zAt]
    push_cast
    ring
  change (1 - (shift F ω v).2 * Complex.exp (((↑(-2 * Real.pi * d) : ℂ) * Complex.I) * (ξ : ℂ))) = 0 ↔
    (shift F ω v).2 * Complex.exp (zAt ξ * (d : ℂ)) = 1
  rw [he, sub_eq_zero]
  exact eq_comm

/-- The product on the actual isotype is intertwined with a finite
radial difference product whose Fourier order is the Weil multiplicity. -/
theorem exists_globalZeroLineWeil_shiftModel (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    ∃ ds : List (ℝ × ℂ), (∀ p ∈ ds, p.1 ≠ 0) ∧
      (∀ p : S, globalZeroLineWeilProduct F ν s hs A (J F ν s ω p) =
        J F ν s ω (radialWeilDifferenceProduct ds p)) ∧
      ∀ ξ : ℝ, ds.countP (fun p ↦ decide (radialWeilDifferenceSymbol p.1 p.2 ξ = 0)) =
        globalWeilMomentMultiplicity F A ω (C F ω) (zAt ξ) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨[], by simp, fun p ↦ ?_, fun ξ ↦ by simp [globalWeilMomentMultiplicity]⟩
    change (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs ∅ (intoTheta F ν s hs (J F ν s ω p))).val = _
    have he : globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs ∅ = 1 :=
      Finset.noncommProd_empty _ _
    rw [he]
    rfl
  | @insert v A hv ih =>
    obtain ⟨ds, hd, hprod, hcount⟩ := ih
    let hu := ω.comp (globalSobolevFiniteUnitInclusion F v) = 1
    have hStep (p : S) : globalZeroLineWeilProduct F ν s hs (insert v A) (J F ν s ω p) =
        globalSobolevWeilPrincipalValue F (μ F ν) s hs v
          (J F ν s ω (radialWeilDifferenceProduct ds p)) := by
      have he : globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs (insert v A) =
          (globalThetaSobolevWeilPrincipalValue F (μ F ν) s hs v).comp
            (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs A) :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ hv
      change (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs (insert v A)
        (intoTheta F ν s hs (J F ν s ω p))).val = _
      rw [he, ContinuousLinearMap.comp_apply]
      change globalSobolevWeilPrincipalValue F (μ F ν) s hs v
        (globalZeroLineWeilProduct F ν s hs A (J F ν s ω p)) = _
      rw [hprod]
    have hStep' (p : S) := globalSobolevWeilPrincipalValue_of_isotype F (μ F ν) s hs v ω
      (J F ν s ω p) (globalZeroLineSchwartzIsotype_mem_ambient F ν s hs ω p)
    have hMult (ξ : ℝ) :
        globalWeilMomentMultiplicity F (insert v A) ω (C F ω) (zAt ξ) =
          globalWeilMomentMultiplicity F A ω (C F ω) (zAt ξ) +
            if hu ∧ orbitalMomentPhase F (C F ω) (zAt ξ) (globalUniformizerClass F v) = 1
            then 1 else 0 := by
      unfold globalWeilMomentMultiplicity
      rw [Finset.filter_insert]
      split
      · rw [Finset.card_insert_of_notMem (fun H ↦ hv (Finset.mem_filter.mp H).1)]
      · rw [add_zero]
    by_cases hU : hu
    · refine ⟨shift F ω v :: ds, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact shift_nonzero F ω v
        · exact hd p hp
      · intro p
        let q := radialWeilDifferenceProduct ds p
        rw [hStep, hStep' q, ite_eq_left hU]
        change J F ν s ω q - T F ν s hs (globalUniformizerClass F v) (J F ν s ω q) =
          J F ν s ω (q - (shift F ω v).2 • q.compSubConstCLM ℂ (shift F ω v).1)
        rw [map_sub, map_smul, globalZeroLineSchwartzIsotype_translate]
        change J F ν s ω q - (((ω (ideleClassNormOnePart F (globalUniformizerClass F v)) : ℂ)⁻¹)⁻¹ • _) = _
        rw [inv_inv]
        rfl
      · intro ξ
        rw [hMult, List.countP_cons, hcount]
        by_cases hr : radialWeilDifferenceSymbol (shift F ω v).1 (shift F ω v).2 ξ = 0
        · have hp := (shift_symbol_eq_zero_iff F ω v ξ).mp hr
          simp [hr, hU, hp]
        · have hp : orbitalMomentPhase F (C F ω) (zAt ξ) (globalUniformizerClass F v) ≠ 1 :=
            fun h ↦ hr ((shift_symbol_eq_zero_iff F ω v ξ).mpr h)
          simp [hr, hU, hp]
    · refine ⟨ds, hd, fun p ↦ ?_, fun ξ ↦ ?_⟩
      · rw [hStep, hStep', ite_eq_right hU]
      · rw [hcount, hMult]
        simp [hU]

private theorem radial_mass_ne_zero : (ν.real univ : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := ν)).ne'

private theorem zAt_re (ξ : ℝ) : (zAt ξ).re = 0 := by simp [zAt, Complex.mul_re]

private theorem amplitude_eq (q : Q F) :
    hardySobolevAmplitude 0 0 s (r F q) = (1+(r F q)^2)^(s/4) := by
  simp only [hardySobolevAmplitude, hardySobolevWeight, mul_zero, zero_mul,
    Real.exp_zero, max_self, one_mul, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Pairing a separated isotype vector with the canonical global moment
is the radial moment times the Haar mass of the norm-one factor. -/
theorem globalZeroLineSchwartzIsotype_moment (ω : PontryaginDual (K F))
    (p : S) (ξ : ℝ) (m : ℕ) :
    (∫ q, (J F ν s ω p) q * orbitalSobolevMoment F (C F ω) s (zAt ξ) m q ∂μ F ν) =
      (ν.real univ : ℂ) *
        ∫ t : ℝ, (t : ℂ)^m * p t * Complex.exp (radialFourierSlope t * (ξ : ℂ)) := by
  let e := (ideleClassLogCoordinates F).toMeasurableEquiv
  let H (t : ℝ) : ℂ := (t : ℂ)^m * p t * Complex.exp (radialFourierSlope t * (ξ : ℂ))
  have he : (fun q : Q F ↦ (J F ν s ω p) q * orbitalSobolevMoment F (C F ω) s (zAt ξ) m q) =ᵐ[μ F ν]
      fun q ↦ H (r F q) := by
    filter_upwards [globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ p] with q hq
    let k := ideleClassNormOnePart F q
    let t := r F q
    let a : ℝ := (1 + t^2) ^ (s/4)
    have ha : a ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    have hpow : (1 + ‖t‖^2) ^ (-s / 4) = a⁻¹ := by
      dsimp [a]
      rw [sq_abs, ← Real.rpow_neg (by positivity)]
      congr 1
      ring
    have hphase : zAt ξ * (t : ℂ) = radialFourierSlope t * (ξ : ℂ) := by
      dsimp only [zAt, radialFourierSlope]
      push_cast
      ring
    have hχ : (C F ω q : ℂ) = (ω k : ℂ) := rfl
    have hq' : (J F ν s ω p) q = (a : ℂ) * ((ω k : ℂ)⁻¹ * p t) := by
      change _ = (hardySobolevAmplitude 0 0 s t : ℂ) * ((ω⁻¹ k : ℂ) * p t) at hq
      rw [amplitude_eq F s q] at hq
      exact hq
    have hm : orbitalSobolevMoment F (C F ω) s (zAt ξ) m q =
        ((a : ℂ)⁻¹ * ((ω k : ℂ) * Complex.exp (radialFourierSlope t * (ξ : ℂ)))) * (t : ℂ)^m := by
      unfold orbitalSobolevMoment
      change ((1+‖t‖^2)^(-s/4) : ℝ) * ((C F ω q : ℂ) * Complex.exp (zAt ξ * (t : ℂ))) * (t : ℂ)^m = _
      rw [hpow, Complex.ofReal_inv, hχ, hphase]
    rw [hq', hm]
    dsimp only [H, t]
    field_simp [Complex.ofReal_ne_zero.mpr ha, Circle.coe_ne_zero (ω k)]
  calc
    _ = ∫ q, H (r F q) ∂μ F ν := integral_congr_ae he
    _ = ∫ p : ℝ × K F, H p.1 * (1 : ℂ) ∂volume.prod ν := by
      change (∫ q, H (r F q) ∂Measure.map e (volume.prod ν)) = _
      rw [integral_map_equiv]
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        change H (Real.log (ideleClassNorm F (ideleClassLogCoordinates F y))) = H y.1 * 1
        rw [log_norm_coordinates, mul_one]
    _ = _ := by
      rw [integral_prod_mul H (fun _ : K F ↦ (1 : ℂ)), integral_const, Complex.real_smul, mul_one, mul_comm]

/-- In the actual global Sobolev isotype the closure of the Weil range
contains each vector satisfying the corrected Euler moment conditions. -/
theorem mem_globalClosedWeilIsotypeRange_of_moments
    (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (u : Lp ℂ 2 (μ F ν)) (hu : u ∈ W F ν s hs ω)
    (hmom : ∀ (ξ : ℝ) (j : ℕ), j < globalWeilMomentMultiplicity F A ω (C F ω) (zAt ξ) →
      (∫ q, u q * orbitalSobolevMoment F (C F ω) s (zAt ξ) j q ∂μ F ν) = 0) :
    u ∈ closure (range fun v : globalOrbitalSobolevIsotype F (μ F ν) s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs A ⟨v.val,v.property.1⟩).val) := by
  classical
  let V := W F ν s hs ω
  letI : IsClosed (V : Set (Lp ℂ 2 (μ F ν))) :=
    globalAmbientSobolevIsotype_isClosed F ω (μ F ν) 0 0 s hs
  let P := (globalZeroLineWeilProduct F ν s hs A).comp V.starProjection
  have hPRange : range P ⊆ range (fun v : globalOrbitalSobolevIsotype F (μ F ν) s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs A ⟨v.val,v.property.1⟩).val) := by
    rintro _ ⟨x,rfl⟩
    let y := V.starProjection x
    have hy : y ∈ V := V.starProjection_apply_mem x
    have hNy := globalThetaSobolevMap_zeroLine_dense_of_haar F (μ F ν) s hs y
    exact ⟨⟨y, hNy, hy⟩, rfl⟩
  apply closure_mono hPRange
  obtain ⟨ds, hd, hp, hcount⟩ := exists_globalZeroLineWeil_shiftModel F ν s hs A ω
  have hP (f : S) : P (J F ν s ω f) = J F ν s ω (radialWeilDifferenceProduct ds f) := by
    change globalZeroLineWeilProduct F ν s hs A (V.starProjection (J F ν s ω f)) = _
    rw [Submodule.starProjection_eq_self_iff.mpr (globalZeroLineSchwartzIsotype_mem_ambient F ν s hs ω f), hp]
  let M (k : ℝ × ℕ) : Lp ℂ 2 (μ F ν) →L[ℂ] ℂ :=
    if h : (k.2 : ℝ) < (s - 1)/2 then
      (radialFourierSlope 1 ^ k.2 / (ν.real univ : ℂ)) •
        orbitalSobolevMomentCLM F (μ F ν) s hs (C F ω) (zAt k.1) (zAt_re k.1) k.2 h
    else 0
  have hadm (k : ℝ × ℕ)
      (hk : k.2 < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 k.1 = 0))) :
      (k.2 : ℝ) < (s - 1)/2 :=
    globalWeilMoment_admissible F s A ω (C F ω) (zAt k.1) hA k.2 ((hcount k.1) ▸ hk)
  have hM (k : ℝ × ℕ) (hk : k.2 < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 k.1 = 0)))
      (f : S) : M k (J F ν s ω f) = iteratedDeriv k.2 ((𝓕 f : S) : ℝ → ℂ) k.1 := by
    have h := hadm k hk
    dsimp only [M]
    rw [dite_eq_left h, _root_.smul_apply, smul_eq_mul, orbitalSobolevMomentCLM_apply,
      globalZeroLineSchwartzIsotype_moment F ν s ω f, radialSchwartz_fourierJet_eq_moment]
    rw [← mul_assoc, div_mul_cancel₀ _ (radial_mass_ne_zero F ν)]
  apply Metric.mem_closure_iff.mpr
  intro ε he
  obtain ⟨φ, hφ, hn⟩ := exists_bandlimited_globalZeroLineRadialCutoff_near F (μ F ν) s hs u
    (show 0 < ε/2 by positivity)
  let w := globalZeroLineRadialCutoff F (μ F ν) s hs φ u
  let Y := tsupport ((𝓕 φ : S) : ℝ → ℂ)
  have hw : w ∈ closure (range P) := by
    apply mem_closure_difference_range_of_frequencyWindow ds hd Y hφ (J F ν s ω).toLinearMap P hP M
      (fun k _ hk f ↦ hM k hk f) w (globalZeroLineRadialCutoff_mem_frequencyWindow F ν s hs ω u hu φ)
    intro k _ hk
    dsimp only [M]
    rw [dite_eq_left (hadm k hk), _root_.smul_apply,
      globalZeroLineRadialCutoff_moment_zero F (μ F ν) s hs φ (C F ω)
        (zAt k.1) (zAt_re k.1) k.2 (hadm k hk) u, smul_zero]
    intro j hj
    exact hmom k.1 j (hj.trans_lt ((hcount k.1) ▸ hk))
  obtain ⟨x,hx,hdist⟩ := Metric.mem_closure_iff.mp hw (ε/2) (by positivity)
  exact ⟨x, hx, (dist_triangle u w x).trans_lt (by
    have hne : dist u w < ε/2 := by rw [dist_comm u w, dist_eq_norm]; exact hn
    linarith)⟩

/-- The corrected moment kernel equals the actual closed log-Sobolev
Weil range on the indicated norm-one character isotype. -/
theorem mem_globalClosedWeilIsotypeRange_iff_moments
    (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (u : Lp ℂ 2 (μ F ν)) (hu : u ∈ W F ν s hs ω) :
    u ∈ closure (range fun v : globalOrbitalSobolevIsotype F (μ F ν) s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F (μ F ν) s hs A ⟨v.val,v.property.1⟩).val) ↔
    ∀ (ξ : ℝ) (j : ℕ), j < globalWeilMomentMultiplicity F A ω (C F ω) (zAt ξ) →
      (∫ q, u q * orbitalSobolevMoment F (C F ω) s (zAt ξ) j q ∂μ F ν) = 0 := by
  refine ⟨fun h ξ j hj ↦ ?_, mem_globalClosedWeilIsotypeRange_of_moments F ν s hs A hA ω u hu⟩
  have ha := globalWeilMoment_admissible F s A ω (C F ω) (zAt ξ) hA j hj
  exact (orbitalSobolevMomentCLM_apply F (μ F ν) s hs (C F ω) (zAt ξ) (zAt_re ξ) j ha u).symm.trans
    (globalClosedWeilIsotypeRange_moment_zero F (μ F ν) s hs A ω (C F ω) (zAt ξ) (zAt_re ξ) j ha hj u h)

omit [ν.IsHaarMeasure] in
/-- Every idele-class Haar normalization is the split measure with a suitably
scaled Haar measure on the compact norm-one group. -/
theorem exists_globalClassMeasure_of_haar (ρ : Measure (Q F)) [ρ.IsHaarMeasure] :
    ∃ ν : Measure (K F), ν.IsHaarMeasure ∧ globalClassMeasure F ν = ρ := by
  let ν₀ : Measure (K F) := Measure.haar
  letI : ν₀.IsHaarMeasure := inferInstance
  let ρ₀ := globalClassMeasure F ν₀
  letI : ρ₀.IsHaarMeasure := globalClassMeasure_isHaar F ν₀
  letI : ρ₀.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ρ₀
  let c := Measure.haarScalarFactor ρ ρ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure ρ ρ₀).ne'
  refine ⟨c • ν₀, Measure.IsHaarMeasure.nnreal_smul ν₀ hc, ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular ρ ρ₀]
  unfold globalClassMeasure ρ₀
  rw [Measure.prod_smul_right, Measure.map_smul]
  rfl

omit [ν.IsHaarMeasure] in
/-- The corrected Euler moment kernel identifies the closed global Weil
range for any Haar normalization on the idele class group. -/
theorem mem_globalClosedWeilIsotypeRange_iff_moments_of_haar
    (ρ : Measure (Q F)) [ρ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)
    (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (u : Lp ℂ 2 ρ)
    (hu : u ∈ globalAmbientSobolevIsotype F ω ρ 0 0 s hs) :
    u ∈ closure (range fun v : globalOrbitalSobolevIsotype F ρ s hs ω ↦
      (globalThetaSobolevWeilPrincipalValues F ρ s hs A ⟨v.val,v.property.1⟩).val) ↔
    ∀ (ξ : ℝ) (j : ℕ), j < globalWeilMomentMultiplicity F A ω (C F ω) (zAt ξ) →
      (∫ q, u q * orbitalSobolevMoment F (C F ω) s (zAt ξ) j q ∂ρ) = 0 := by
  obtain ⟨ν₀, hν₀, hρ⟩ := exists_globalClassMeasure_of_haar F ρ
  letI : ν₀.IsHaarMeasure := hν₀
  have h (σ : Measure (Q F)) [σ.IsHaarMeasure] (he : globalClassMeasure F ν₀ = σ)
      (x : Lp ℂ 2 σ) (hx : x ∈ globalAmbientSobolevIsotype F ω σ 0 0 s hs) :
      x ∈ closure (range fun v : globalOrbitalSobolevIsotype F σ s hs ω ↦
        (globalThetaSobolevWeilPrincipalValues F σ s hs A ⟨v.val,v.property.1⟩).val) ↔
      ∀ (ξ : ℝ) (j : ℕ), j < globalWeilMomentMultiplicity F A ω (C F ω) (zAt ξ) →
        (∫ q, x q * orbitalSobolevMoment F (C F ω) s (zAt ξ) j q ∂σ) = 0 := by
    subst σ
    exact mem_globalClosedWeilIsotypeRange_iff_moments F ν₀ s hs A hA ω x hx
  exact h ρ hρ u hu

end
end Masullo
