import GlobalWeilHalfline
import GlobalWeilRangeStrict

open Filter Function MeasureTheory NumberField Set Topology
open scoped InnerProductSpace NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev P := (GlobalBruhat.polarEvaluation F).ker

local instance orbitalHomogeneousQMeasure : MeasurableSpace (Q F) := borel _
local instance orbitalHomogeneousQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance orbitalHomogeneousQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance orbitalHomogeneousQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance orbitalHomogeneousQSecondCountable : SecondCountableTopology (Q F) :=
  ideleClass_secondCountable F
local instance orbitalHomogeneousKMeasure : MeasurableSpace (K F) := borel _
local instance orbitalHomogeneousKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance orbitalHomogeneousKCompact : CompactSpace (K F) := normOneIdeleClass_compact F
local instance orbitalHomogeneousKSecondCountable : SecondCountableTopology (K F) :=
  IsEmbedding.subtypeVal.secondCountableTopology

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)
local instance orbitalHomogeneousνFinite : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩

private abbrev μ := globalClassMeasure F ν
local instance orbitalHomogeneousHaar : (μ F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν
private abbrev L := Lp ℂ 2 (μ F ν)
private abbrev H (ω : PontryaginDual (K F)) := globalOrbitalSobolevIsotype F (μ F ν) s hs ω
private abbrev V (ω : PontryaginDual (K F)) := globalAmbientSobolevIsotype F ω (μ F ν) 0 0 s hs
private abbrev amp (q : Q F) := hardySobolevAmplitude 0 0 s (ideleClassLogNorm F q).toAdd
private abbrev T (q : Q F) := hardySobolevMulTranslation (μ F ν) (ideleClassLogNorm F)
  (ideleClassLogNorm_continuous F) 0 0 s hs q

/-- A polar-free test in the homogeneous averaging chart. -/
def globalOrbitalHomogeneousTest (ω : PontryaginDual (K F)) (f : P F) : H F ν s hs ω :=
  globalWeilSchwartzTest F s hs ν ω (polarFreeThetaRadialSchwartz F ν ω f.val f.property)

private theorem homogeneousTest_ae (ω : PontryaginDual (K F)) (f : P F) :
    ((globalOrbitalHomogeneousTest F ν s hs ω f).val : Q F → ℂ) =ᵐ[μ F ν] fun q ↦
      (amp F s q : ℂ) * adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q := by
  let g := polarFreeThetaRadialSchwartz F ν ω f.val f.property
  filter_upwards [globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ g] with q hq
  change (globalZeroLineSchwartzIsotype F ν s ω⁻¹ g) q =
    (amp F s q : ℂ) * adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q
  rw [hq]
  have h := adelicHomogeneousTheta_twisted_radialSchwartz F ν ω f.val
    (Or.inr ⟨congrArg Prod.fst f.property,congrArg Prod.snd f.property⟩) q
  change (ω (ideleClassNormOnePart F q) : ℂ) *
    adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q =
      g (ideleClassLogNorm F q).toAdd at h
  rw [← h]
  change (_ : ℂ) * ((ω (ideleClassNormOnePart F q) : ℂ)⁻¹ * (_ * _)) = _
  rw [inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]

private def polarClass (f : P F) : GlobalPolarTheta F :=
  ⟨(globalThetaOperator F).ker.mkQL f.val, f.property⟩

private theorem polarClass_surjective : Surjective (polarClass F) := by
  intro u
  obtain ⟨f,hf⟩ := (globalThetaOperator F).ker.mkQ_surjective u.val
  have hp := u.property
  change globalThetaPolarEvaluation F u.val = 0 at hp
  rw [← hf] at hp
  exact ⟨⟨f,hp⟩,Subtype.ext hf⟩

private theorem starProjection_smul_eq_integral_of_fixed
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [MeasurableSpace Y] (η : Measure Y) (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (D : Y → E →ₗᵢ[ℂ] E) (x : E) (hI : Integrable (fun k ↦ D k x) η)
    (hw : (∫ k, D k x ∂η) ∈ V) (hfix : ∀ k y, y ∈ V → D k y = y) :
    V.starProjection ((η.real univ : ℂ) • x) = ∫ k, D k x ∂η := by
  apply V.eq_starProjection_of_mem_of_inner_eq_zero hw
  intro y hy
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right, inner_smul_right]
  change (η.real univ : ℂ) * ⟪y,x⟫_ℂ - (innerSL ℂ y) (∫ k, D k x ∂η) = 0
  rw [← (innerSL ℂ y).integral_comp_comm hI]
  have hconst (k : Y) : (innerSL ℂ y) (D k x) = ⟪y,x⟫_ℂ := by
    change ⟪y,D k x⟫_ℂ = ⟪y,x⟫_ℂ
    conv_lhs => rw [← hfix k y hy]
    exact (D k).inner_map_map y x
  simp_rw [hconst, integral_const, Complex.real_smul, sub_self]

set_option maxHeartbeats 2400000 in
private theorem translation_norm (q : Q F) (hq : ideleClassLogNorm F q = 1) (x : L F ν) :
    ‖T F ν s hs q x‖ = ‖x‖ := by
  apply hardySobolevMulTranslation_norm_of_normOne
  exact hq

set_option maxHeartbeats 4000000 in
private theorem homogeneousTest_eq_projection (ω : PontryaginDual (K F)) (f : P F) :
    (globalOrbitalHomogeneousTest F ν s hs ω f).val =
      (ν.real univ : ℂ) • globalAmbientSobolevIsotypeProjection F ω (μ F ν) 0 0 s hs
        (globalThetaSobolevMap F (μ F ν) 0 0 0 s hs (polarClass F f)) := by
  let u := globalThetaSobolevMap F (μ F ν) 0 0 0 s hs (polarClass F f)
  let w := (globalOrbitalHomogeneousTest F ν s hs ω f).val
  let g (k : K F) : Q F := k.val⁻¹
  let χ (k : K F) : ℂ := ω k
  let v := globalThetaOperator F f.val
  let V₀ := V F ν s hs ω
  letI : IsClosed (V₀ : Set (L F ν)) :=
    globalAmbientSobolevIsotype_isClosed F ω (μ F ν) 0 0 s hs
  have hg : Continuous g := (continuous_subtype_val : Continuous (fun k : K F ↦ k.val)).inv
  have hχ : Continuous χ := continuous_subtype_val.comp ω.continuous
  have hnorm (k : K F) : ideleClassLogNorm F (g k) = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val⁻¹)) = Multiplicative.ofAdd 0
    rw [map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, Real.log_one]
  have hI : Integrable (fun k ↦ χ k • T F ν s hs (g k) u) ν := by
    apply integrable_globalZeroLine_translate F (μ F ν) ν s hs g hg χ hχ.aestronglyMeasurable u
    · exact subset_closure ⟨polarClass F f,rfl⟩
    · simp only [hnorm, toAdd_one, abs_zero, add_zero, Real.one_rpow, mul_one, χ, Circle.norm_coe]
      exact integrable_const _
  have hw : (∫ k, χ k • T F ν s hs (g k) u ∂ν) = w := by
    have hv : Continuous v := adelicTheta_continuous F
      (bruhat_theta_continuous_and_invariant (GlobalBruhat.algebraicEquiv F f.val).property).1
    apply globalZeroLine_integral_translate_eq F (μ F ν) ν s hs g hg.measurable χ hχ.measurable u w v hv.measurable
    · have he := globalThetaSobolevMap_ae F (μ F ν) 0 0 0 s hs (polarClass F f)
      change (u : Q F → ℂ) =ᵐ[μ F ν] fun q ↦
        (amp F s q * Real.exp (0 * (ideleClassLogNorm F q).toAdd)) • v q at he
      simpa only [zero_mul, Real.exp_zero, mul_one, Complex.real_smul] using he
    · apply (homogeneousTest_ae F ν s hs ω f).mono
      intro q hq
      change w q = _ at hq
      have hForm : adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q =
          ∫ k : K F, χ k * v ((g k)⁻¹ * q) ∂ν := by
        change (∫ k : K F, χ k * v (k.val * q) ∂ν) = _
        apply integral_congr_ae
        exact .of_forall fun k ↦ by
          change χ k * v (k.val * q) = χ k * v ((k.val⁻¹)⁻¹ * q)
          exact congrArg (fun a : Q F ↦ χ k * v (a * q)) (inv_inv (k.val : Q F)).symm
      exact hq.trans (congrArg ((amp F s q : ℂ) * ·) hForm)
    · exact hI
  have hfix (k : K F) (y : L F ν) (hy : y ∈ V₀) : χ k • T F ν s hs (g k) y = y := by
    have he := (mem_thetaCharacterSubspace _ _ _).mp hy k⁻¹
    change T F ν s hs (g k) y = ((ω (k⁻¹) : Circle) : ℂ) • y at he
    rw [he, map_inv, Circle.coe_inv, smul_smul, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul]
  let D (k : K F) : L F ν →ₗᵢ[ℂ] L F ν :=
    ⟨(χ k • T F ν s hs (g k)).toLinearMap, fun x ↦ by
      change ‖χ k • T F ν s hs (g k) x‖ = ‖x‖
      have hχnorm : ‖χ k‖ = 1 := Circle.norm_coe (ω k)
      rw [norm_smul, hχnorm, one_mul]
      exact translation_norm F ν s hs (g k) (hnorm k) x⟩
  have hwMem : (∫ k, D k u ∂ν) ∈ V₀ := by
    change (∫ k, χ k • T F ν s hs (g k) u ∂ν) ∈ V₀
    rw [hw]
    exact (globalOrbitalHomogeneousTest F ν s hs ω f).property.2
  have hp : V₀.starProjection ((ν.real univ : ℂ) • u) = w :=
    (starProjection_smul_eq_integral_of_fixed ν V₀ D u hI hwMem hfix).trans hw
  exact hp.symm.trans (V₀.starProjection.map_smul _ _)

/-- The represented homogeneous polar-free tests are dense in the completed
isotype, including with an arbitrary Haar normalization of their angular average. -/
theorem globalOrbitalHomogeneousTest_dense (ω : PontryaginDual (K F)) :
    DenseRange (globalOrbitalHomogeneousTest F ν s hs ω) := by
  let V₀ := V F ν s hs ω
  let M := globalAmbientSobolevIsotypeProjection F ω (μ F ν) 0 0 s hs
  let c : ℂ := ν.real univ
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := ν)).ne'
  have hSource : DenseRange (fun f : P F ↦
      globalThetaSobolevMap F (μ F ν) 0 0 0 s hs (polarClass F f)) := by
    intro x
    change x ∈ closure (range (globalThetaSobolevMap F (μ F ν) 0 0 0 s hs ∘ polarClass F))
    rw [range_comp, (polarClass_surjective F).range_eq, image_univ]
    exact globalThetaSobolevMap_zeroLine_dense_of_haar F (μ F ν) s hs x
  intro u
  rw [closure_subtype, ← range_comp]
  have hmap : MapsTo (c • M) (range fun f : P F ↦ globalThetaSobolevMap F (μ F ν) 0 0 0 s hs
      (polarClass F f)) (range ((↑) ∘ globalOrbitalHomogeneousTest F ν s hs ω)) := by
    rintro _ ⟨f,rfl⟩
    exact ⟨f,homogeneousTest_eq_projection F ν s hs ω f⟩
  have hx := (hmap.closure (c • M).continuous) (hSource (c⁻¹ • u.val))
  change c • M (c⁻¹ • u.val) ∈ _ at hx
  rw [M.map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul] at hx
  letI : IsClosed ((V F ν s hs ω) : Set (L F ν)) :=
    globalAmbientSobolevIsotype_isClosed F ω (μ F ν) 0 0 s hs
  have hu : M u.val = u.val := Submodule.starProjection_eq_self_iff.mpr u.property.2
  rwa [hu] at hx

private theorem closure_homogeneousTests_range_comp (ω : PontryaginDual (K F))
    (D : H F ν s hs ω →L[ℂ] L F ν) :
    closure (range (D ∘ globalOrbitalHomogeneousTest F ν s hs ω)) = closure (range D) := by
  let J := globalOrbitalHomogeneousTest F ν s hs ω
  apply le_antisymm
  · apply closure_mono
    rintro _ ⟨f,rfl⟩
    exact ⟨J f,rfl⟩
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨u,rfl⟩
    have hMap : MapsTo D (range J) (range (D ∘ J)) := by
      rintro _ ⟨f,rfl⟩
      exact ⟨f,rfl⟩
    exact (hMap.closure D.continuous) (globalOrbitalHomogeneousTest_dense F ν s hs ω u)

set_option maxHeartbeats 1200000 in
/-- All finite stages have the same closed cutoff image on the original
homogeneous polar-free tests. The image is the whole cutoff isotype. -/
theorem cutoff_homogeneousPolarTests_range_closure_eq_cutoff_range
    (A : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (ω : PontryaginDual (K F))
    (hA : ∀ v ∈ A, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (Λ : ℝ) (hΛ : 0 < Λ) (b : Option ℝ) :
    let ρ : Q F → ℝ := ((ideleClassNorm F) ⁻¹' (Ici Λ⁻¹ ∩ b.elim univ Iic)).indicator (fun _ ↦ 1)
    ∃ (hρ : Measurable ρ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₁ : ∀ q, ρ q ≤ 1),
      let M : L F ν →L[ℂ] L F ν := cutoffOperator ρ hρ hρ₀ hρ₁
      let J := globalOrbitalHomogeneousTest F ν s hs ω
      closure (range fun f : P F ↦ M (globalIsotypicPrincipalValues F (μ F ν) s hs ω A (J f)).val) =
        range (fun u : H F ν s hs ω ↦ M u.val) := by
  intro ρ
  obtain ⟨hρ,hρ₀,hρ₁,h⟩ :=
    cutoff_globalPrincipalValues_range_closure_eq_cutoff_range F s hs (μ F ν) A ω hA Λ hΛ b
  refine ⟨hρ,hρ₀,hρ₁,?_⟩
  let M : L F ν →L[ℂ] L F ν := cutoffOperator ρ hρ hρ₀ hρ₁
  let D := M.comp ((H F ν s hs ω).subtypeL.comp (globalIsotypicPrincipalValues F (μ F ν) s hs ω A))
  exact (closure_homogeneousTests_range_comp F ν s hs ω D).trans h

set_option maxHeartbeats 1200000 in
/-- The cutoff equality holds already for the images of the original
homogeneous polar-free tests under the finite unramified Weil products. -/
theorem cutoff_homogeneousPolarTests_range_closure_eq
    (A B : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (ω : PontryaginDual (K F))
    (hA : ∀ v ∈ A, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (hB : ∀ v ∈ B, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (Λ : ℝ) (hΛ : 0 < Λ) (b : Option ℝ) :
    let ρ : Q F → ℝ := ((ideleClassNorm F) ⁻¹' (Ici Λ⁻¹ ∩ b.elim univ Iic)).indicator (fun _ ↦ 1)
    ∃ (hρ : Measurable ρ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₁ : ∀ q, ρ q ≤ 1),
      let M : L F ν →L[ℂ] L F ν := cutoffOperator ρ hρ hρ₀ hρ₁
      let J := globalOrbitalHomogeneousTest F ν s hs ω
      closure (range fun f : P F ↦ M (globalIsotypicPrincipalValues F (μ F ν) s hs ω A (J f)).val) =
        closure (range fun f : P F ↦ M (globalIsotypicPrincipalValues F (μ F ν) s hs ω B (J f)).val) := by
  intro ρ
  obtain ⟨hρ,hρ₀,hρ₁,hLeft⟩ :=
    cutoff_homogeneousPolarTests_range_closure_eq_cutoff_range F ν s hs A ω hA Λ hΛ b
  obtain ⟨_,_,_,hRight⟩ :=
    cutoff_homogeneousPolarTests_range_closure_eq_cutoff_range F ν s hs B ω hB Λ hΛ b
  exact ⟨hρ,hρ₀,hρ₁,hLeft.trans hRight.symm⟩

set_option maxHeartbeats 1400000 in
/-- The source's uncut homogeneous test closures are strictly nested when
the larger stage introduces a place over a new rational prime. -/
theorem homogeneousPolarTests_range_closure_lt_of_new_residuePrime
    {A B : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))} (hAB : A ⊆ B) (hs₁ : 1 < s)
    (ω : PontryaginDual (K F))
    (hB : ∀ v ∈ B, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hv : v ∈ B)
    (hnew : ∀ w ∈ A, finiteResiduePrime F v ≠ finiteResiduePrime F w) :
    closure (range fun f : P F ↦
      (globalIsotypicPrincipalValues F (μ F ν) s hs ω B (globalOrbitalHomogeneousTest F ν s hs ω f)).val) <
    closure (range fun f : P F ↦
      (globalIsotypicPrincipalValues F (μ F ν) s hs ω A (globalOrbitalHomogeneousTest F ν s hs ω f)).val) := by
  let J := globalOrbitalHomogeneousTest F ν s hs ω
  let H₀ := H F ν s hs ω
  let R := globalClosedPrincipalValueRange F (μ F ν) s hs ω
  let T := globalIsotypicPrincipalValues F (μ F ν) s hs ω
  let val : H₀ → L F ν := Subtype.val
  have hClosed : IsClosedEmbedding val :=
    (globalOrbitalSobolevIsotype_isClosed F (μ F ν) s hs ω).isClosedEmbedding_subtypeVal
  have he (D : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
      closure (range (val ∘ T D ∘ J)) = val '' (R D : Set H₀) := by
    have h := closure_homogeneousTests_range_comp F ν s hs ω (H₀.subtypeL.comp (T D))
    change closure (range (val ∘ T D ∘ J)) = closure (range (val ∘ T D)) at h
    rw [h, range_comp, hClosed.closure_image_eq]
    rfl
  change closure (range (val ∘ T B ∘ J)) < closure (range (val ∘ T A ∘ J))
  rw [he A, he B]
  exact hClosed.injective.image_strictMono
    (globalClosedPrincipalValueRange_lt_of_new_residuePrime F ν s hs hAB hs₁ ω hB v hv hnew)

end
end Masullo
