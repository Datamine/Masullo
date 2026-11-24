import GlobalWeilSchwartzModel
import RadialWeilJetInterpolation
import HilbertMomentMarkushevich

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical FourierTransform InnerProductSpace NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev S := 𝓢(ℝ, ℂ)

local instance orbitalBasisQMeasurable : MeasurableSpace (Q F) := borel _
local instance orbitalBasisQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance orbitalBasisQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance orbitalBasisQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance orbitalBasisQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance orbitalBasisKMeasurable : MeasurableSpace (K F) := borel _
local instance orbitalBasisKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance orbitalBasisKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I
private theorem zAt_re (ξ : ℝ) : (zAt ξ).re = 0 := by simp [zAt, Complex.mul_re]
private abbrev C (ω : PontryaginDual (K F)) := normOneEulerCharacter F ω

/-- The orbital moment index uses distinct frequencies and one index for
each allowed moment below the actual Euler multiplicity. -/
def globalWeilMomentIndices (A : Finset (Place F)) (ω : PontryaginDual (K F)) : Set (ℝ × ℕ) :=
  {i | i.2 < globalWeilMomentMultiplicity F A ω (C F ω) (zAt i.1)}

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)

private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F μ s hs ω
private abbrev W (ω : PontryaginDual (K F)) := globalAmbientSobolevIsotype F ω μ 0 0 s hs
private abbrev N := globalThetaSobolevCompletion F μ 0 0 0 s hs

local instance orbitalBasisHComplete (ω : PontryaginDual (K F)) : CompleteSpace (H F μ s hs ω) :=
  (globalOrbitalSobolevIsotype_isClosed F μ s hs ω).completeSpace_coe

private def inTheta (ω : PontryaginDual (K F)) : H F μ s hs ω →L[ℂ] N F μ s hs :=
  (H F μ s hs ω).subtypeL.codRestrict _ (fun u ↦ u.property.1)

/-- The genuine completed Weil product restricted to the indicated isotype. -/
def globalWeilIsotypeProduct (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    H F μ s hs ω →L[ℂ] H F μ s hs ω := by
  let P := globalThetaSobolevWeilPrincipalValues F μ s hs A
  exact ((N F μ s hs).subtypeL.comp (P.comp (inTheta F μ s hs ω))).codRestrict _
    (fun u ↦ ⟨(P (inTheta F μ s hs ω u)).property,
      globalThetaSobolevWeilPrincipalValues_preserves_isotype F μ s hs A ω _ u.property.2⟩)

/-- The closure of the actual Weil product range in the Hilbert isotype. -/
def globalWeilIsotypeClosedRange (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    Submodule ℂ (H F μ s hs ω) :=
  (globalWeilIsotypeProduct F μ s hs A ω).range.topologicalClosure

private theorem mem_closedRange_iff_moments
    (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (u : H F μ s hs ω) :
    u ∈ globalWeilIsotypeClosedRange F μ s hs A ω ↔
      ∀ i : globalWeilMomentIndices F A ω,
        (∫ q, u.val q * orbitalSobolevMoment F (C F ω) s (zAt i.val.1) i.val.2 q ∂μ) = 0 := by
  have he :=
    mem_globalClosedWeilIsotypeRange_iff_moments_of_haar F μ s hs A hA ω u.val u.property.2
  change u ∈ closure (range (globalWeilIsotypeProduct F μ s hs A ω)) ↔ _
  rw [closure_subtype, ← range_comp]
  change u.val ∈ closure (range fun v : H F μ s hs ω ↦
    (globalThetaSobolevWeilPrincipalValues F μ s hs A ⟨v.val,v.property.1⟩).val) ↔ _
  exact he.trans ⟨fun h i ↦ h i.val.1 i.val.2 i.property,
    fun h ξ j hj ↦ h ⟨(ξ,j),hj⟩⟩

private abbrev admissible (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : globalWeilMomentIndices F A ω) :
    (i.val.2 : ℝ) < (s-1)/2 :=
  globalWeilMoment_admissible F s A ω (C F ω) (zAt i.val.1) hA i.val.2 i.property

/-- In the positive amplitude chart the moment's Hilbert representative
is the conjugate of its reciprocal-amplitude function. -/
def globalOrbitalMomentRieszVector (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (hm : (m : ℝ) < (s-1)/2) : Lp ℂ 2 μ :=
  let h := ((orbitalSobolevMoment_memLp_iff F μ χ hs hz m).mpr hm).star
  h.toLp (fun q ↦ star (orbitalSobolevMoment F χ s z m q))

private theorem globalOrbitalMomentRieszVector_ae (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (hm : (m : ℝ) < (s-1)/2) :
    (globalOrbitalMomentRieszVector F μ s hs χ z hz m hm : Q F → ℂ) =ᵐ[μ]
      fun q ↦ star (orbitalSobolevMoment F χ s z m q) :=
  (((orbitalSobolevMoment_memLp_iff F μ χ hs hz m).mpr hm).star).coeFn_toLp

/-- Conjugation preserves the negative Sobolev norm in the reciprocal chart. -/
theorem globalOrbitalMomentRieszVector_norm (χ : PontryaginDual (Q F)) (z : ℂ) (hz : z.re = 0)
    (m : ℕ) (hm : (m : ℝ) < (s-1)/2)
    (h : MemLp (orbitalSobolevMoment F χ s z m) 2 μ) :
    ‖globalOrbitalMomentRieszVector F μ s hs χ z hz m hm‖ = ‖h.toLp _‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [globalOrbitalMomentRieszVector_ae F μ s hs χ z hz m hm, h.coeFn_toLp] with g hg hh
  rw [hg, hh, norm_star]

/-- The conjugated reciprocal-weight representative belongs to the positive
Sobolev isotype of the restricted character. -/
theorem globalOrbitalMomentRieszVector_mem (χ : PontryaginDual (Q F)) (ω : PontryaginDual (K F))
    (hχω : ∀ k : K F, χ k.val = ω k)
    (z : ℂ) (hz : z.re = 0) (m : ℕ) (hm : (m : ℝ) < (s-1)/2) :
    globalOrbitalMomentRieszVector F μ s hs χ z hz m hm ∈ H F μ s hs ω := by
  let v := globalOrbitalMomentRieszVector F μ s hs χ z hz m hm
  refine ⟨globalThetaSobolevMap_zeroLine_dense_of_haar F μ s hs v, ?_⟩
  apply (mem_thetaCharacterSubspace _ _ _).mpr
  intro k
  let T := hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs k.val
  let f := orbitalSobolevMoment F χ s z m
  let a (q : Q F) := hardySobolevAmplitude 0 0 s (ideleClassLogNorm F q).toAdd
  have hvae := globalOrbitalMomentRieszVector_ae F μ s hs χ z hz m hm
  change T v = (ω k : ℂ) • v
  apply Lp.ext
  filter_upwards [hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs k.val v,
    (measurePreserving_mul_left μ k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hvae,
    Lp.coeFn_smul (ω k : ℂ) v, hvae] with q hT hshift hSmul hq
  have hk : ideleClassLogNorm F k.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = Multiplicative.ofAdd 0
    rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
  have ha : a (k.val⁻¹ * q) = a q := by simp [a, map_mul, map_inv, hk]
  have hp : 0 < a q := by
    dsimp only [a, hardySobolevAmplitude]
    apply Real.sqrt_pos.mpr
    unfold hardySobolevWeight
    positivity
  have hphase : f (k.val⁻¹ * q) = ((ω k : ℂ)⁻¹) * f q := by
    have h := orbitalSobolevMoment_isotypic F χ s z m q k⁻¹
    change f (q*k.val⁻¹) = (χ (k.val⁻¹) : ℂ) * f q at h
    rw [mul_comm q, map_inv, hχω k, Circle.coe_inv] at h
    exact h
  have hstar : star ((ω k : ℂ)⁻¹) = (ω k : ℂ) := by
    rw [← Circle.coe_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  change T v q = ((a q / a (k.val⁻¹ * q) : ℝ) : ℂ) * v (k.val⁻¹ * q) at hT
  change v (k.val⁻¹ * q) = star (f (k.val⁻¹ * q)) at hshift
  change ((ω k : ℂ) • v : Lp ℂ 2 μ) q = (ω k : ℂ) * v q at hSmul
  change v q = star (f q) at hq
  rw [hT, ha, div_self hp.ne', Complex.ofReal_one, one_mul, hshift, hSmul, hq, hphase, star_mul', hstar, mul_comm]

/-- The Hilbert pairing represents the original bilinear orbital moment. -/
theorem globalOrbitalMomentRieszVector_inner (χ : PontryaginDual (Q F))
    (z : ℂ) (hz : z.re = 0) (m : ℕ) (hm : (m : ℝ) < (s-1)/2) (u : Lp ℂ 2 μ) :
    ⟪globalOrbitalMomentRieszVector F μ s hs χ z hz m hm,u⟫_ℂ =
      ∫ q, u q * orbitalSobolevMoment F χ s z m q ∂μ :=
  orbitalSobolevMomentCLM_apply F μ s hs χ z hz m hm u


private theorem canonicalCharacter_restrict (ω : PontryaginDual (K F)) (k : K F) :
    C F ω k.val = ω k := by
  change ω (ideleClassNormOnePart F k.val) = ω k
  congr 1
  have h : ideleClassLogNorm F k.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = Multiplicative.ofAdd 0
    rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
  apply Subtype.ext
  change k.val / ideleClassExpSection F (ideleClassLogNorm F k.val) = k.val
  rw [h, map_one, div_one]

/-- The canonical moment vectors in the actual Hilbert isotype. -/
def globalWeilMomentRepresentative (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : globalWeilMomentIndices F A ω) : H F μ s hs ω :=
  ⟨globalOrbitalMomentRieszVector F μ s hs (C F ω) (zAt i.val.1) (zAt_re _) i.val.2
      (admissible F s A hA ω i),
    globalOrbitalMomentRieszVector_mem F μ s hs (C F ω) ω (canonicalCharacter_restrict F ω)
      (zAt i.val.1) (zAt_re _) i.val.2 (admissible F s A hA ω i)⟩

/-- The closed Weil range is the common kernel of the Hilbert moment pairings. -/
theorem mem_globalWeilIsotypeClosedRange_iff_inner (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (u : H F μ s hs ω) :
    u ∈ globalWeilIsotypeClosedRange F μ s hs A ω ↔
      ∀ i, ⟪globalWeilMomentRepresentative F μ s hs A hA ω i,u⟫_ℂ = 0 := by
  rw [mem_closedRange_iff_moments F μ s hs A hA ω u]
  exact forall_congr' fun i ↦ (globalOrbitalMomentRieszVector_inner F μ s hs (C F ω) (zAt i.val.1)
    (zAt_re _) i.val.2 (admissible F s A hA ω i) u.val).symm ▸ Iff.rfl

/-- The actual closed Weil range is orthogonal to each canonical moment vector. -/
theorem globalWeilMomentRepresentative_mem_orthogonal
    (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : globalWeilMomentIndices F A ω) :
    globalWeilMomentRepresentative F μ s hs A hA ω i ∈
      (globalWeilIsotypeClosedRange F μ s hs A ω)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro u hu
  exact inner_eq_zero_symm.mp ((mem_globalWeilIsotypeClosedRange_iff_inner F μ s hs A hA ω u).mp hu i)

section SplitHaar

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

local instance orbitalBasisSplitHaar : (globalClassMeasure F ν).IsHaarMeasure :=
  globalClassMeasure_isHaar F ν

/-- The separated radial Schwartz chart in the completed Weil isotype. -/
abbrev globalWeilSchwartzTest (ω : PontryaginDual (K F)) : S →L[ℂ] H F (globalClassMeasure F ν) s hs ω :=
  (globalZeroLineSchwartzIsotype F ν s ω⁻¹).codRestrict _ fun p ↦
    ⟨globalThetaSobolevMap_zeroLine_dense_of_haar F (globalClassMeasure F ν) s hs _,
      globalZeroLineSchwartzIsotype_mem_ambient F ν s hs ω p⟩

private def bandTests (ω : PontryaginDual (K F)) : Set (H F (globalClassMeasure F ν) s hs ω) :=
  globalWeilSchwartzTest F s hs ν ω '' {p | HasCompactSupport ((𝓕 p : S) : ℝ → ℂ)}

private theorem dense_bandTests (ω : PontryaginDual (K F)) : Dense (bandTests F s hs ν ω) := by
  have hd : DenseRange (globalWeilSchwartzTest F s hs ν ω) := by
    intro u
    rw [closure_subtype, ← range_comp]
    exact globalZeroLineSchwartzIsotype_dense_in_ambient F ν s hs ω u.val u.property.2
  intro u
  refine closure_minimal ?_ isClosed_closure (hd u)
  rintro _ ⟨p,rfl⟩
  apply mem_closure_of_tendsto ((globalWeilSchwartzTest F s hs ν ω).continuous.continuousAt.tendsto.comp
    (fourierWindow_tendsto p))
  exact Eventually.of_forall fun n ↦ ⟨fourierWindow p n, fourierWindow_hasCompactSpectrum p n, rfl⟩

/-- The scalar converting a radial moment into its Fourier jet. -/
abbrev globalWeilJetScale (i : ℝ × ℕ) : ℂ := radialFourierSlope 1 ^ i.2 / (ν.real univ : ℂ)

theorem globalWeilJetScale_ne_zero (i : ℝ × ℕ) : globalWeilJetScale F ν i ≠ 0 := by
  have h : radialFourierSlope 1 ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (by simp [Real.pi_ne_zero])) Complex.I_ne_zero
  exact div_ne_zero (pow_ne_zero _ h)
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := ν)).ne')

/-- The canonical moment and its Fourier jet differ by the explicit scalar. -/
theorem globalWeilSchwartzTest_scaled_inner_eq_jet (A : Finset (Place F)) (hA : 2 * (A.card : ℝ) ≤ s)
    (ω : PontryaginDual (K F)) (i : globalWeilMomentIndices F A ω) (p : S) :
    globalWeilJetScale F ν i.val *
      ⟪globalWeilMomentRepresentative F (globalClassMeasure F ν) s hs A hA ω i,
        globalWeilSchwartzTest F s hs ν ω p⟫_ℂ = iteratedDeriv i.val.2 ((𝓕 p : S) : ℝ → ℂ) i.val.1 := by
  change globalWeilJetScale F ν i.val * ⟪globalOrbitalMomentRieszVector F (globalClassMeasure F ν)
    s hs (C F ω) (zAt i.val.1) (zAt_re _) i.val.2 (admissible F s A hA ω i),
    globalZeroLineSchwartzIsotype F ν s ω⁻¹ p⟫_ℂ = _
  rw [globalOrbitalMomentRieszVector_inner, globalZeroLineSchwartzIsotype_moment F ν s ω p,
    radialSchwartz_fourierJet_eq_moment]
  rw [← mul_assoc, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := ν)).ne')]


/-- The indexed moment representatives are complete and minimal, and the
biorthogonal functionals separate points of the annihilator. -/
theorem globalWeilMoment_markushevich_split (A : Finset (Place F))
    (hA : 2 * (A.card : ℝ) ≤ s) (ω : PontryaginDual (K F)) :
    let R := globalWeilIsotypeClosedRange F (globalClassMeasure F ν) s hs A ω
    let e : globalWeilMomentIndices F A ω → Rᗮ := fun i ↦
      ⟨globalWeilMomentRepresentative F (globalClassMeasure F ν) s hs A hA ω i,
        globalWeilMomentRepresentative_mem_orthogonal F (globalClassMeasure F ν) s hs A hA ω i⟩
    ∃ φ : globalWeilMomentIndices F A ω → Rᗮ →L[ℂ] ℂ,
      (∀ i j, φ i (e j) = if j = i then 1 else 0) ∧
      Dense (Submodule.span ℂ (range e) : Set Rᗮ) ∧
      ∀ v : Rᗮ, (∀ i, φ i v = 0) → v = 0 := by
  classical
  intro R e
  let r := globalWeilMomentRepresentative F (globalClassMeasure F ν) s hs A hA ω
  have hk := mem_globalWeilIsotypeClosedRange_iff_inner F (globalClassMeasure F ν) s hs A hA ω
  have hr := globalWeilMomentRepresentative_mem_orthogonal F (globalClassMeasure F ν) s hs A hA ω
  obtain ⟨ds, hd, _, hc⟩ := exists_globalZeroLineWeil_shiftModel F ν s hs A ω
  have hI : globalWeilMomentIndices F A ω = radialWeilJetIndices ds := by
    ext k
    change k.2 < globalWeilMomentMultiplicity F A ω (C F ω) (zAt k.1) ↔ _
    exact (hc k.1).symm ▸ Iff.rfl
  let E := Equiv.setCongr hI
  choose b hb hj using fun i : globalWeilMomentIndices F A ω ↦
    exists_radialWeilJet_frequency_interpolant ds hd (E i)
  let p (i : globalWeilMomentIndices F A ω) : S := 𝓕⁻ (b i)
  let q (i : globalWeilMomentIndices F A ω) := globalWeilJetScale F ν i.val • globalWeilSchwartzTest F s hs ν ω (p i)
  have hbi (i j : globalWeilMomentIndices F A ω) :
      ⟪r j,q i⟫_ℂ = if j = i then 1 else 0 := by
    have he := globalWeilSchwartzTest_scaled_inner_eq_jet F s hs ν A hA ω j (p i)
    change globalWeilJetScale F ν j.val * ⟪r j,globalWeilSchwartzTest F s hs ν ω (p i)⟫_ℂ = _ at he
    rw [show 𝓕 (p i) = b i from FourierTransform.fourier_fourierInv_eq _] at he
    have hdj := hj i (E j)
    change iteratedDeriv j.val.2 (b i : ℝ → ℂ) j.val.1 = _ at hdj
    rw [hdj] at he
    calc
      ⟪r j, q i⟫_ℂ = globalWeilJetScale F ν i.val * ⟪r j,globalWeilSchwartzTest F s hs ν ω (p i)⟫_ℂ :=
        inner_smul_right (r j) (globalWeilSchwartzTest F s hs ν ω (p i)) (globalWeilJetScale F ν i.val)
      _ = _ := by
        by_cases h : j = i
        · subst j
          simpa using he
        · rw [ite_eq_right (fun e ↦ h (E.injective e))] at he
          rw [(mul_eq_zero.mp he).resolve_left (globalWeilJetScale_ne_zero F ν j.val), mul_zero, ite_eq_right h]
  refine hilbert_moment_markushevich R (Submodule.isClosed_topologicalClosure _) r q hr hk hbi
    (bandTests F s hs ν ω) (dense_bandTests F s hs ν ω) ?_
  rintro x ⟨p, hp, rfl⟩
  let Y := tsupport ((𝓕 p : S) : ℝ → ℂ)
  have hY := radialWeilProduct_finite_moment_indices ds hd Y hp
  apply (hY.preimage Subtype.val_injective.injOn).subset
  intro i hi
  have hmem : i.val.1 ∈ Y := by
    by_contra hn
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).iteratedDeriv_eq i.val.2
    have hz' : iteratedDeriv i.val.2 ((𝓕 p : S) : ℝ → ℂ) i.val.1 = 0 := by simpa using hz
    exact hi ((mul_eq_zero.mp ((globalWeilSchwartzTest_scaled_inner_eq_jet F s hs ν A hA ω i p).trans hz')).resolve_left
      (globalWeilJetScale_ne_zero F ν i.val))
  exact ⟨hmem, (E i).property⟩

/-- The frequencies and moments of an orbital isotype are countable. -/
theorem globalWeilMomentIndices_countable (A : Finset (Place F)) (ω : PontryaginDual (K F)) :
    (globalWeilMomentIndices F A ω).Countable := by
  obtain ⟨ds, hd, _, hc⟩ := exists_globalZeroLineWeil_shiftModel F Measure.haar 0 le_rfl A ω
  apply (radialWeilJetIndices_countable ds hd).mono
  intro i hi
  change i.2 < globalWeilMomentMultiplicity F A ω (C F ω) (zAt i.1) at hi
  change i.2 < ds.countP (fun d ↦ decide (radialWeilDifferenceSymbol d.1 d.2 i.1 = 0))
  rw [hc]
  exact hi

end SplitHaar


/-- The orbital Markushevich basis in the canonical chart, for every Haar normalization. -/
theorem globalWeilMoment_markushevich (A : Finset (Place F))
    (hA : 2 * (A.card : ℝ) ≤ s) (ω : PontryaginDual (K F)) :
    let R := globalWeilIsotypeClosedRange F μ s hs A ω
    let e : globalWeilMomentIndices F A ω → Rᗮ := fun i ↦
      ⟨globalWeilMomentRepresentative F μ s hs A hA ω i,
        globalWeilMomentRepresentative_mem_orthogonal F μ s hs A hA ω i⟩
    ∃ φ : globalWeilMomentIndices F A ω → Rᗮ →L[ℂ] ℂ,
      (∀ i j, φ i (e j) = if j = i then 1 else 0) ∧
      Dense (Submodule.span ℂ (range e) : Set Rᗮ) ∧
      ∀ v : Rᗮ, (∀ i, φ i v = 0) → v = 0 := by
  obtain ⟨ν, hν, he⟩ := exists_globalClassMeasure_of_haar F μ
  letI : ν.IsHaarMeasure := hν
  have h (σ : Measure (Q F)) [σ.IsHaarMeasure] (hσ : globalClassMeasure F ν = σ) :
      let R := globalWeilIsotypeClosedRange F σ s hs A ω
      let e : globalWeilMomentIndices F A ω → Rᗮ := fun i ↦
        ⟨globalWeilMomentRepresentative F σ s hs A hA ω i,
          globalWeilMomentRepresentative_mem_orthogonal F σ s hs A hA ω i⟩
      ∃ φ : globalWeilMomentIndices F A ω → Rᗮ →L[ℂ] ℂ,
        (∀ i j, φ i (e j) = if j = i then 1 else 0) ∧
        Dense (Submodule.span ℂ (range e) : Set Rᗮ) ∧
        ∀ v : Rᗮ, (∀ i, φ i v = 0) → v = 0 := by
    subst σ
    exact globalWeilMoment_markushevich_split F s hs ν A hA ω
  exact h μ he

end
end Masullo
