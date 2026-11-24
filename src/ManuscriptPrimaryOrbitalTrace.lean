import GlobalPrimaryOrbitalTraceContinuity
import ManuscriptOrbitalMarkushevich
import UnramifiedOrbitalQuotient
import BoundedBasisLifts

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical CompactlySupported NumberField

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev zAt (ξ : ℝ) : ℂ := (↑(-2 * Real.pi * ξ) : ℂ) * Complex.I
private abbrev ω (χ : PontryaginDual (Q F)) := heckeNormOneRestriction F χ

local instance manuscriptPrimaryTraceQMeasure : MeasurableSpace (Q F) := borel _
local instance manuscriptPrimaryTraceQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance manuscriptPrimaryTraceQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance manuscriptPrimaryTraceQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance manuscriptPrimaryTraceQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F

variable (μ : Measure (Q F)) [μ.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)
private abbrev H (χ : PontryaginDual (Q F)) := globalOrbitalSobolevIsotype F μ s hs (ω F χ)
private abbrev R (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :=
  globalWeilIsotypeClosedRange F μ s hs A (ω F χ)
private abbrev R₀ (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :=
  (globalClosedPrincipalValueRange F μ s hs (ω F χ) A).toSubmodule

local instance manuscriptPrimaryTraceHComplete (χ : PontryaginDual (Q F)) :
    CompleteSpace (H F μ s hs χ) :=
  (globalOrbitalSobolevIsotype_isClosed F μ s hs (ω F χ)).completeSpace_coe
local instance manuscriptPrimaryTraceR₀Closed (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :
    IsClosed (R₀ F μ s hs A χ : Set (H F μ s hs χ)) :=
  (globalClosedPrincipalValueRange F μ s hs (ω F χ) A).isClosed

private theorem range_eq (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    R F μ s hs A χ = R₀ F μ s hs A χ := by
  apply globalWeilIsotypeClosedRange_eq_unramified
  exact fun v hv ↦ (globalSobolevFiniteUnitInclusion_trivial_iff F (ω F χ) χ
    (fun _ ↦ rfl) v).mpr (hχ v hv)

private abbrev Z (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :=
  {z : ℂ // orbitalEulerDenominator F A χ z = 0}
private abbrev m (A : Finset (Place F)) (χ : PontryaginDual (Q F)) (z : Z F A χ) :=
  analyticOrderNatAt (orbitalEulerDenominator F A χ) z.val

private def momentSigmaEquiv (A : Finset (Place F)) (χ : PontryaginDual (Q F)) :
    orbitalEulerMomentIndices F A χ ≃ (Σ z : Z F A χ, Fin (m F A χ z)) where
  toFun i := ⟨⟨i.val.1,orbitalEulerMoment_zero F A χ i⟩,⟨i.val.2,i.property⟩⟩
  invFun i := ⟨(i.1.val,i.2.val),i.2.isLt⟩
  left_inv i := Subtype.ext rfl
  right_inv i := by rcases i with ⟨⟨z,hz⟩,j⟩; rfl

set_option maxHeartbeats 1600000 in
/-- The orthogonal realization used in the trace calculation agrees, by an
intertwining linear isometry, with the manuscript's completed orbital quotient. -/
theorem exists_primaryOrbitalQuotient_intertwiner (A : Finset (Place F)) (χ : PontryaginDual (Q F))
    (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    ∃ E : (H F μ s hs χ ⧸ R₀ F μ s hs A χ) ≃ₗᵢ[ℂ] (R F μ s hs A χ)ᗮ,
      ∀ (φ : C_c(Q F, ℂ)) u,
        E (globalOrbitalQuotientConvolution F μ s hs (ω F χ) φ A u) =
          primaryOrbitalCompressedConvolution F μ s hs A (ω F χ) φ (E u) := by
  let W := R₀ F μ s hs A χ
  have hR := range_eq F μ s hs A χ hχ
  obtain ⟨_,_,E,hE,hProj,_⟩ := hilbert_quotient_projection W
  let V := LinearIsometryEquiv.ofEq Wᗮ (R F μ s hs A χ)ᗮ
    (congrArg Submodule.orthogonal hR.symm)
  refine ⟨E.trans V,fun φ u ↦ ?_⟩
  apply Subtype.ext
  let B := globalIsotypicOrbitalConvolution F μ s hs (ω F χ) φ
  have hquot : globalOrbitalQuotientConvolution F μ s hs (ω F χ) φ A u = W.mkQL (B (E u).val) := by
    conv_lhs => rw [← hE u]
    rfl
  have hv (v : Wᗮ) : (V v).val = v.val := LinearIsometryEquiv.coe_ofEq_apply _ _
  change (V (E _)).val =
    ((R F μ s hs A χ)ᗮ.orthogonalProjectionOnto (B (V (E u)).val)).val
  rw [hv,hquot,hProj,hv]
  exact congrArg (fun P : Submodule ℂ (H F μ s hs χ) ↦
    (Pᗮ.starProjection (B (E u).val))) hR.symm

omit [μ.IsHaarMeasure] in
set_option maxHeartbeats 1000000 in
private theorem primaryOrbitalEulerSum_regroup (A : Finset (Place F))
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v)
    (φ : BruhatCompactTest (Q F))
    (hSum : Summable (fun i : globalWeilMomentIndices F A (ω F χ) ↦
      ‖orbitalConvolutionCoefficient F μ φ.val.val (normOneEulerCharacter F (ω F χ)) (zAt i.val.1) 0‖)) :
    Summable (fun z : Z F A χ ↦ ‖(m F A χ z : ℂ) *
      orbitalConvolutionCoefficient F μ φ.val.val χ z.val 0‖) ∧
    (∑' i : globalWeilMomentIndices F A (ω F χ),
      orbitalConvolutionCoefficient F μ φ.val.val (normOneEulerCharacter F (ω F χ)) (zAt i.val.1) 0) =
      ∑' z : Z F A χ, (m F A χ z : ℂ) * orbitalConvolutionCoefficient F μ φ.val.val χ z.val 0 := by
  obtain ⟨t,ht,_⟩ := existsUnique_heckeHeight F χ
  let e := (momentSigmaEquiv F A χ).symm.trans (orbitalEulerMomentEquiv F A χ hχ t ht)
  let c (z : Z F A χ) := orbitalConvolutionCoefficient F μ φ.val.val χ z.val 0
  let f (i : globalWeilMomentIndices F A (ω F χ)) :=
    orbitalConvolutionCoefficient F μ φ.val.val (normOneEulerCharacter F (ω F χ)) (zAt i.val.1) 0
  have he (i : Σ z : Z F A χ, Fin (m F A χ z)) : f (e i) = c i.1 := by
    have hz := orbitalEulerMomentEquiv_exponent F A χ hχ t ht ((momentSigmaEquiv F A χ).symm i)
    change zAt (e i).val.1 = i.1.val - (t : ℂ) * Complex.I at hz
    change orbitalConvolutionCoefficient F μ φ.val.val (normOneEulerCharacter F (ω F χ))
      (zAt (e i).val.1) 0 = orbitalConvolutionCoefficient F μ φ.val.val χ i.1.val 0
    unfold orbitalConvolutionCoefficient
    rw [hz]
    apply integral_congr_ae
    exact .of_forall fun g ↦ by
      simp only [pow_zero, mul_one]
      rw [orbitalMomentPhase_heckeHeight F χ t ht i.1.val g]
  have hN : Summable (fun i : Σ z : Z F A χ, Fin (m F A χ z) ↦ ‖c i.1‖) := by
    have h := e.summable_iff.mpr hSum
    have heq : (fun i : Σ z : Z F A χ, Fin (m F A χ z) ↦ ‖f (e i)‖) =
        (fun i ↦ ‖c i.1‖) := funext (fun i ↦ congrArg norm (he i))
    change Summable (fun i ↦ ‖f (e i)‖) at h
    rwa [heq] at h
  constructor
  · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      norm_mul, Complex.norm_natCast] using hN.sigma
  · change (∑' i, f i) = ∑' z : Z F A χ, (m F A χ z : ℂ) * c z
    refine (e.tsum_eq f).symm.trans ((tsum_congr he).trans ?_)
    rw [hN.of_norm.tsum_sigma]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The place set used in the whole primary factor is finite. -/
theorem exists_globalPrimaryPlaces {p : ℕ} (hp : p.Prime) :
    ∃ A : Finset (Place F), ∀ v : Place F, v ∈ A ↔ v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  classical
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  let S : Set (Place F) := {v | v.asIdeal.under ℤ = P}
  have hp₀ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hP₀ : P ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hp₀
  have hP : P.IsPrime := (Ideal.span_singleton_prime hp₀).mpr (Nat.prime_iff_prime_int.mp hp)
  letI : P.IsMaximal := hP.isMaximal hP₀
  let A := IsDedekindDomain.primesOverFinset P (𝓞 F)
  have hmap : MapsTo (fun v : Place F ↦ v.asIdeal) S A := by
    intro v hv
    exact (IsDedekindDomain.mem_primesOverFinset_iff hP₀ (𝓞 F)).mpr
      ⟨v.isPrime, ⟨hv.symm⟩⟩
  have hS := (A.finite_toSet.subset hmap.image_subset).of_finite_image
    HeightOneSpectrum.asIdeal_injective.injOn
  exact ⟨hS.toFinset, fun v ↦ hS.mem_toFinset⟩

omit [μ.IsHaarMeasure] in
/-- The order-zero convolution coefficient has the printed complex-power form. -/
theorem orbitalConvolutionCoefficient_zero_eq_integral (φ : Q F → ℂ)
    (χ : PontryaginDual (Q F)) (z : ℂ) :
    orbitalConvolutionCoefficient F μ φ χ z 0 =
      ∫ g, φ g * (χ g : ℂ) * (ideleClassNorm F g : ℂ)^z ∂μ := by
  unfold orbitalConvolutionCoefficient
  apply integral_congr_ae
  refine .of_forall fun g ↦ ?_
  have h : 0 < ideleClassNorm F g := ideleClassNorm_pos F g
  simp only [orbitalMomentPhase, pow_zero, mul_one]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'),
    ← Complex.ofReal_log h.le, mul_comm ((Real.log (ideleClassNorm F g) : ℝ) : ℂ) z, mul_assoc]
  rfl

set_option maxHeartbeats 1700000 in
/-- Corrected Theorem 11.2.2.1. Compact Bruhat convolution on the completed orbital
quotient is continuous in trace norm and its trace is the Euler-zero sum with
the full analytic multiplicity. -/
theorem exists_manuscriptPrimaryOrbitalTrace (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s) (hs' : 1 < s)
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    ∃ L : BruhatCompactTest (Q F) →L[ℂ] TraceClass ((R F μ s hs A χ)ᗮ),
      ∀ φ : BruhatCompactTest (Q F),
        (L φ).toOperator = primaryOrbitalCompressedConvolution F μ s hs A (ω F χ)
          (primaryOrbitalBruhatDensity F φ) ∧
        Summable (fun z : Z F A χ ↦ ‖(m F A χ z : ℂ) *
          orbitalConvolutionCoefficient F μ φ.val.val χ z.val 0‖) ∧
        (L φ).traceValue = ∑' z : Z F A χ, (m F A χ z : ℂ) *
          orbitalConvolutionCoefficient F μ φ.val.val χ z.val 0 := by
  have hcard : 2 * (A.card : ℝ) ≤ s := by
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast globalPrimaryPlaces_card_le_degree F A hp hA)
      (show (0 : ℝ) ≤ 2 by norm_num)).trans hdeg
  obtain ⟨L,hL⟩ := exists_primaryOrbitalBruhat_traceClassCLM F μ s hs A hp hA hcard hs' (ω F χ)
  refine ⟨L, fun φ ↦ ?_⟩
  obtain ⟨hL', hSum, hTr⟩ := hL φ
  obtain ⟨hAbs, hRegroup⟩ := primaryOrbitalEulerSum_regroup F μ A χ hχ φ hSum
  exact ⟨hL', hAbs, hTr.trans hRegroup⟩

set_option maxHeartbeats 1500000 in
/-- The trace on the actual quotient is a distribution in the topology of the
compact Bruhat tests, with the absolutely convergent primary Euler-zero formula. -/
theorem exists_manuscriptPrimaryOrbitalTrace_distribution (A : Finset (Place F))
    {p : ℕ} (hp : p.Prime)
    (hA : ∀ v ∈ A, v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s) (hs' : 1 < s)
    (χ : PontryaginDual (Q F)) (hχ : ∀ v ∈ A, unramifiedFiniteCharacter F χ v) :
    ∃ E : (H F μ s hs χ ⧸ R₀ F μ s hs A χ) ≃ₗᵢ[ℂ] (R F μ s hs A χ)ᗮ,
    ∃ L : BruhatCompactTest (Q F) →L[ℂ] TraceClass ((R F μ s hs A χ)ᗮ),
    ∃ τ : StrongDual ℂ (BruhatCompactTest (Q F)),
      ∀ φ : BruhatCompactTest (Q F),
        (∀ u, E (globalOrbitalQuotientConvolution F μ s hs (ω F χ)
          (primaryOrbitalBruhatDensity F φ) A u) = (L φ).toOperator (E u)) ∧
        τ φ = (L φ).traceValue ∧
        Summable (fun z : Z F A χ ↦ ‖(m F A χ z : ℂ) *
          (∫ g, φ.val.val g * (χ g : ℂ) * (ideleClassNorm F g : ℂ)^z.val ∂μ)‖) ∧
        τ φ = ∑' z : Z F A χ, (m F A χ z : ℂ) *
          ∫ g, φ.val.val g * (χ g : ℂ) * (ideleClassNorm F g : ℂ)^z.val ∂μ := by
  obtain ⟨E,hE⟩ := exists_primaryOrbitalQuotient_intertwiner F μ s hs A χ hχ
  obtain ⟨L,hL⟩ := exists_manuscriptPrimaryOrbitalTrace F μ s hs A hp hA hdeg hs' χ hχ
  refine ⟨E,L,TraceClass.traceCLM.comp L,fun φ ↦ ?_⟩
  obtain ⟨hOp,hAbs,hSum⟩ := hL φ
  refine ⟨fun u ↦ ?_,rfl,?_,?_⟩
  · rw [hOp]
    exact hE (primaryOrbitalBruhatDensity F φ) u
  · simpa only [orbitalConvolutionCoefficient_zero_eq_integral F μ] using hAbs
  · change (L φ).traceValue = _
    simpa only [orbitalConvolutionCoefficient_zero_eq_integral F μ] using hSum

end
end Masullo
