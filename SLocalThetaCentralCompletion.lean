import SLocalDecayFourier
import SLocalDecayHilbert
import SLocalThetaStageProbe
import ModulatedSobolevTests
import ModulatedSobolevCoefficients

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev C := SIdeleQuotient F S
private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S
private abbrev Theta := SLocalThetaQuotient F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

local instance : CompactSpace (K F S) := sLocalThetaNormOne_compact F S

local instance : LocallyCompactSpace (SAdeles F S)ˣ := sLocalIdeles_locallyCompact F S
local instance : LocallyCompactSpace (C F S) := QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace
local instance : SecondCountableTopology (SAdeles F S)ˣ := sLocalIdeles_secondCountable F S
local instance : SecondCountableTopology (C F S) :=
  TopologicalSpace.Quotient.secondCountableTopology (QuotientGroup.isOpenMap_coe (N := sUnitImage F S))
local instance : T2Space (C F S) := by
  letI : T1Space (C F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  exact inferInstance

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

local instance : IsFiniteMeasure ν := by infer_instance

private theorem thetaFunction_translate_class (c x : C F S) (u : Theta F S) :
    sLocalThetaFunction F S (sLocalThetaTranslate F S c u) x =
      sLocalThetaFunction F S u (c⁻¹ * x) := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F S).ker u
  exact sLocalThetaOperator_leftTranslate F S g f x

private theorem thetaFunction_normOne (ω : PontryaginDual (K F S)) (u : Theta F S)
    (hu : ∀ k, sLocalNormOneAction F S k u = (ω k : ℂ) • u) (k : K F S) (x : C F S) :
    sLocalThetaFunction F S u (k.val*x) = ((ω k : ℂ)⁻¹) * sLocalThetaFunction F S u x := by
  have he := thetaFunction_translate_class F S (k⁻¹).val x u
  have hk : (k⁻¹).val⁻¹ = k.val := inv_inv k.val
  rw [hk] at he
  change sLocalThetaFunction F S (sLocalNormOneAction F S k⁻¹ u) x =
    sLocalThetaFunction F S u (k.val*x) at he
  rw [hu k⁻¹, map_smul, map_inv, Circle.coe_inv] at he
  exact he.symm

/-- The homogeneous character average is an actual ordinary theta function.
The scalar undoes the normalization of the continuous isotypic section. -/
theorem exists_sLocalTheta_homogeneousLift (ω : PontryaginDual (K F S)) :
    ∃ L : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] Theta F S,
      (∀ f x, sLocalThetaFunction F S (L (Submodule.Quotient.mk f)) x =
        sLocalHomogeneousTheta F S ν ω f.val x) ∧
      (∀ u, sLocalThetaToComponent F S ν ω (L u) = (ν.real univ : ℂ) • u) ∧
      ∀ u k, sLocalNormOneAction F S k (L u) = (ω k : ℂ) • L u := by
  obtain ⟨s,hs,hEig,_⟩ := sLocalThetaComponent_isotypicSection F S ν ω
  let L := ((ν.real univ : ℝ) : ℂ) • s
  refine ⟨L,?_,?_,?_⟩
  · intro f x
    let u := s (Submodule.Quotient.mk f)
    obtain ⟨g,hg⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F S).ker u
    have hgf : (Submodule.Quotient.mk g : SLocalHomogeneousThetaQuotient F S ν ω) =
        Submodule.Quotient.mk f :=
      (congrArg (sLocalThetaToComponent F S ν ω) hg).trans (hs (Submodule.Quotient.mk f))
    have hdiff := (mem_sLocalHomogeneousThetaKernel_iff F S ν ω (g-f)).mp
      ((Submodule.Quotient.eq _).mp hgf)
    have heq : sLocalHomogeneousTheta F S ν ω g.val x =
        sLocalHomogeneousTheta F S ν ω f.val x := by
      have hz := hdiff x
      change sLocalHomogeneousThetaEvalLinear F S ν ω x (g-f) = 0 at hz
      rw [map_sub,sub_eq_zero] at hz
      exact hz
    have hprofile : sLocalHomogeneousTheta F S ν ω g.val x =
        (ν.real univ : ℂ) * sLocalThetaFunction F S u x := by
      change (∫ k : K F S, (ω k : ℂ) *
          sLocalThetaFunction F S (Submodule.Quotient.mk g) (k.val*x) ∂ν) = _
      rw [hg]
      calc
        _ = ∫ _ : K F S, sLocalThetaFunction F S u x ∂ν := by
          apply integral_congr_ae
          exact Eventually.of_forall fun k ↦ by
            change (ω k : ℂ) * sLocalThetaFunction F S u (k.val*x) = sLocalThetaFunction F S u x
            rw [thetaFunction_normOne F S ω u (hEig _) k x, ← mul_assoc,
              mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]
        _ = _ := by rw [integral_const, Complex.real_smul]
    change sLocalThetaFunction F S (((ν.real univ : ℝ) : ℂ) • u) x = _
    rw [map_smul]
    exact hprofile.symm.trans heq
  · intro u
    change sLocalThetaToComponent F S ν ω ((ν.real univ : ℂ) • s u) = _
    rw [map_smul, hs u]
  · intro u k
    change sLocalNormOneAction F S k (((ν.real univ : ℝ) : ℂ) • s u) =
      (ω k : ℂ) • (((ν.real univ : ℝ) : ℂ) • s u)
    rw [map_smul,hEig,smul_comm]

private abbrev ClassL2 := Lp ℂ 2 (sLocalClassHaar F S ν)
private abbrev ProductL2 := Lp ℂ 2 (ν.prod (volume : Measure ℝ))
private abbrev ScalarL2 := Lp ℂ 2 (volume : Measure ℝ)

private def centralChart : K F S × ℝ ≃ₜ C F S :=
  (Homeomorph.prodComm (K F S) ℝ).trans (sLocalZetaSplit F S)

private theorem centralChart_preserving :
    MeasurePreserving (centralChart F S) (ν.prod (volume : Measure ℝ)) (sLocalClassHaar F S ν) := by
  let e := sLocalZetaSplit F S
  have h : MeasurePreserving e ((volume : Measure ℝ).prod ν) (sLocalClassHaar F S ν) :=
    ⟨e.continuous.measurable,rfl⟩
  exact h.comp Measure.measurePreserving_swap

/-- Pullback to the canonical norm section and the compact norm-one group. -/
def sLocalCentralProductEquiv : ClassL2 F S ν ≃ₗᵢ[ℂ] ProductL2 F S ν := by
  let e := centralChart F S
  let h := centralChart_preserving F S ν
  let h' := h.symm e.toMeasurableEquiv
  let A : ClassL2 F S ν →ₗᵢ[ℂ] ProductL2 F S ν := Lp.compMeasurePreservingₗᵢ ℂ e h
  let B : ProductL2 F S ν →ₗᵢ[ℂ] ClassL2 F S ν := Lp.compMeasurePreservingₗᵢ ℂ e.symm h'
  apply LinearIsometryEquiv.ofSurjective A
  intro u
  refine ⟨B u,Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving (B u) h,
    h.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u h')] with p hp hp'
  change A (B u) p = u p
  exact hp.trans (hp'.trans (congrArg u (e.symm_apply_apply p)))

theorem sLocalCentralProductEquiv_ae (u : ClassL2 F S ν) :
    (sLocalCentralProductEquiv F S ν u : K F S × ℝ → ℂ) =ᵐ[ν.prod (volume : Measure ℝ)]
      fun p ↦ u (sLocalZetaSplit F S (p.2,p.1)) :=
  Lp.coeFn_compMeasurePreserving u (centralChart_preserving F S ν)

/-- The central theta map in the unweighted Haar realization. -/
abbrev sLocalCentralThetaMap :=
  sLocalThetaSobolevMap F S ν (1/2) 0 0 0 (by norm_num) le_rfl le_rfl

private abbrev productTheta :=
  (sLocalCentralProductEquiv F S ν).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sLocalCentralThetaMap F S ν)

private theorem centralTheta_ae (u : Theta F S) :
    (sLocalCentralThetaMap F S ν u : C F S → ℂ) =ᵐ[sLocalClassHaar F S ν]
      fun q ↦ (Real.exp (Real.log (sLocalClassModulus F S q)/2) : ℂ) *
        sLocalThetaFunction F S u q := by
  filter_upwards [sLocalThetaSobolevMap_ae F S ν (1/2) 0 0 0 (by norm_num) le_rfl le_rfl u] with q hq
  refine hq.trans ?_
  change (hardySobolevAmplitude 0 0 0 (Real.log (sLocalClassModulus F S q)) *
      Real.exp (1/2 * Real.log (sLocalClassModulus F S q))) • (sLocalThetaFunction F S u q) = _
  simp only [hardySobolevAmplitude, hardySobolevWeight,mul_zero,zero_mul,Real.exp_zero,
    zero_div,Real.rpow_zero,mul_one,max_self,Real.sqrt_one,one_mul,Complex.real_smul]
  rw [show (1/2 : ℝ) * Real.log (sLocalClassModulus F S q) =
    Real.log (sLocalClassModulus F S q) / 2 by ring]

private theorem productTheta_ae (u : Theta F S) :
    (productTheta F S ν u : K F S × ℝ → ℂ) =ᵐ[ν.prod (volume : Measure ℝ)]
      fun p ↦ (Real.exp (p.2/2) : ℂ) * sLocalThetaFunction F S u (sLocalZetaSplit F S (p.2,p.1)) := by
  have h := (centralChart_preserving F S ν).quasiMeasurePreserving.ae_eq_comp (centralTheta_ae F S ν u)
  filter_upwards [sLocalCentralProductEquiv_ae F S ν (sLocalCentralThetaMap F S ν u),h] with p hp he
  refine hp.trans (he.trans ?_)
  change ((Real.exp (Real.log (sLocalClassModulus F S (sLocalZetaSplit F S (p.2,p.1)))/2) : ℝ) : ℂ) *
    sLocalThetaFunction F S u (sLocalZetaSplit F S (p.2,p.1)) = _
  rw [sLocalZetaSplit_logModulus]

set_option maxHeartbeats 1000000 in
private theorem separated_mem_productTheta_range (ω : PontryaginDual (K F S))
    (φ : PositiveRealExponentialDecay univ) :
    lpTwoProduct (compactCharacterLp ν ω)
      (sLocalDecayCentralTrace (I := univ) (mem_univ _) φ) ∈ (productTheta F S ν).range := by
  obtain ⟨f,hf⟩ := exists_sLocalHomogeneousTheta_polarFree_of_profile F S ν ω⁻¹ φ
  obtain ⟨L,hL,_⟩ := exists_sLocalTheta_homogeneousLift F S ν ω⁻¹
  let u := L (Submodule.Quotient.mk f.val)
  refine ⟨u,Lp.ext ?_⟩
  let ψ := sLocalDecayCentralTrace (I := univ) (mem_univ _) φ
  filter_upwards [productTheta_ae F S ν u, lpTwoProduct_ae (compactCharacterLp ν ω) ψ,
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := (volume : Measure ℝ))).ae_eq_comp
      (compactCharacterLp_ae ν ω),
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := (volume : Measure ℝ))).ae_eq_comp
      (sLocalDecayCentralTrace_ae (I := univ) (mem_univ _) φ)] with p h₁ h₂ h₃ h₄
  change compactCharacterLp ν ω p.1 = (ω p.1 : ℂ) at h₃
  change ψ p.2 = (Real.exp (p.2/2) : ℂ) * φ.val p.2 at h₄
  change productTheta F S ν u p = lpTwoProduct (compactCharacterLp ν ω) ψ p
  rw [h₁,h₂,h₃,h₄]
  have hs : sLocalZetaSplit F S (p.2,p.1) = p.1.val * sLocalLogNormRay F S p.2 :=
    mul_comm (sLocalLogNormRay F S p.2) p.1.val
  have hθ := hL f.val (sLocalZetaSplit F S (p.2,p.1))
  change sLocalThetaFunction F S u (sLocalZetaSplit F S (p.2,p.1)) = _ at hθ
  rw [hθ,hs,sLocalHomogeneousTheta_translate,hf]
  have he : ((ω⁻¹ p.1 : ℂ)⁻¹) = (ω p.1 : ℂ) :=
    (congrArg (fun z : ℂ ↦ z⁻¹) (Circle.coe_inv (ω p.1))).trans (inv_inv _)
  rw [he]
  ring

set_option maxHeartbeats 1500000 in
/-- The actual S-local theta image is dense in the central Hilbert norm. -/
theorem sLocalCentralThetaMap_dense : DenseRange (sLocalCentralThetaMap F S ν) := by
  letI : SecondCountableTopology (K F S) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : TopologicalSpace.PseudoMetrizableSpace (K F S) := inferInstance
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let A := range (compactCharacterLp ν)
  let B := range (sLocalDecayCentralTrace (I := univ) (mem_univ _))
  let tm (p : Lp ℂ 2 ν × ScalarL2) := p.1 ⊗ₜ[ℂ] p.2
  let D := Submodule.span ℂ (tm '' (A ×ˢ B))
  let T := (lpTwoTensorIsometry (μ := ν) (ν := (volume : Measure ℝ))).toContinuousLinearMap
  have hB : (Submodule.span ℂ B).topologicalClosure = ⊤ := by
    apply eq_top_iff.mpr
    intro v _
    exact closure_mono Submodule.subset_span (sLocalDecayCentralTrace_dense (I := univ) (mem_univ _) v)
  have hD : D.topologicalClosure = ⊤ := by
    have h : Dense (D : Set (Lp ℂ 2 ν ⊗[ℂ] ScalarL2)) :=
      dense_span_tmul (dense_span_compactCharacterLp ν) hB
    apply SetLike.coe_injective
    rw [Submodule.topologicalClosure_coe, Submodule.top_coe]
    exact dense_iff_closure_eq.mp h
  have hT : DenseRange T := denseRange_lpTwoTensorIsometry
  have hTD := hT.topologicalClosure_map_submodule hD
  have hsub : D.map T.toLinearMap ≤ (productTheta F S ν).range := by
    change (Submodule.span ℂ (tm '' (A ×ˢ B))).map T.toLinearMap ≤ _
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨⟨_,_⟩,⟨⟨ω,rfl⟩,⟨φ,rfl⟩⟩,rfl⟩,rfl⟩
    exact separated_mem_productTheta_range F S ν ω φ
  have hprod : DenseRange (productTheta F S ν) := by
    intro v
    apply closure_mono (show (D.map T.toLinearMap : Set (ProductL2 F S ν)) ⊆ _ from hsub)
    change v ∈ (D.map T.toLinearMap).topologicalClosure
    rw [hTD]
    trivial
  let e := sLocalCentralProductEquiv F S ν
  have hh := e.symm.surjective.denseRange.dense_image e.symm.continuous hprod
  apply hh.mono
  rintro _ ⟨_,⟨u,rfl⟩,rfl⟩
  exact ⟨u,(e.symm_apply_apply _).symm⟩

/-- In the central norm the completed theta subspace is the entire Haar space. -/
theorem sLocalCentralThetaCompletion_eq_top :
    sLocalThetaSobolevCompletion F S ν (1/2) 0 0 0 (by norm_num) le_rfl le_rfl = ⊤ := by
  apply SetLike.coe_injective
  rw [sLocalThetaSobolevCompletion, Submodule.topologicalClosure_coe, Submodule.top_coe]
  exact dense_iff_closure_eq.mp (sLocalCentralThetaMap_dense F S ν)

/-- Selected-place Fourier on ordinary theta with the local additive normalization. -/
def sLocalCentralThetaFourier : Theta F S →L[ℂ] Theta F S :=
  (((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹) • sLocalThetaCompressedFourier F S

@[simp] theorem sLocalCentralThetaFourier_mk (f : E F S) :
    sLocalCentralThetaFourier F S (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalSelectedFourier F S f) := by
  change (((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹) •
    sLocalThetaCompressedFourier F S (Submodule.Quotient.mk f) = _
  rw [sLocalThetaCompressedFourier_mk]
  rfl

set_option maxHeartbeats 1400000 in
private theorem exists_fourierThetaLift (ω : PontryaginDual (K F S)) :
    ∃ L : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] Theta F S,
      (∀ f x, sLocalThetaFunction F S (L (Submodule.Quotient.mk f)) x =
        sLocalHomogeneousTheta F S ν ω f.val x) ∧
      ∀ f x, sLocalThetaFunction F S (sLocalCentralThetaFourier F S (L (Submodule.Quotient.mk f))) x =
        sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val x := by
  obtain ⟨L,hL,hp,hEig⟩ := exists_sLocalTheta_homogeneousLift F S ν ω
  obtain ⟨L',hL',hp',hEig'⟩ := exists_sLocalTheta_homogeneousLift F S ν ω⁻¹
  obtain ⟨H,hH⟩ := exists_sLocalHomogeneousFourier F S ν ω
  let Q := sLocalCentralThetaFourier F S
  let p := sLocalThetaToComponent F S ν ω
  let p' := sLocalThetaToComponent F S ν ω⁻¹
  let c : ℂ := ((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹
  have hcomm (u : Theta F S) : (c • H) (p u) = p' (Q u) := by
    have he := congrArg (fun D : Theta F S →L[ℂ] SLocalHomogeneousThetaQuotient F S ν ω⁻¹ ↦ D u) hH
    change H (p u) = p' (sLocalThetaCompressedFourier F S u) at he
    change c • H (p u) = p' (c • sLocalThetaCompressedFourier F S u)
    rw [map_smul,he]
  have hcov (k : K F S) (u : Theta F S) :
      Q (sLocalNormOneAction F S k u) = sLocalNormOneAction F S k⁻¹ (Q u) := by
    change c • sLocalThetaCompressedFourier F S (sLocalNormOneAction F S k u) =
      sLocalNormOneAction F S k⁻¹ (c • sLocalThetaCompressedFourier F S u)
    rw [compressedFourier_translate_normOne,map_smul]
  obtain ⟨j,_,_,_,hFix,_⟩ := sLocalThetaComponent_pettisSection F S ν ω⁻¹
  refine ⟨L,hL,fun f x ↦ ?_⟩
  let u := L (Submodule.Quotient.mk f)
  let v := L' (Submodule.Quotient.mk (sLocalSelectedFourier F S f))
  have hU (k : K F S) : sLocalNormOneAction F S k (Q u) = (ω⁻¹ k : ℂ) • Q u := by
    have h := hcov k⁻¹ u
    rw [inv_inv] at h
    rw [← h, hEig (Submodule.Quotient.mk f) k⁻¹,map_smul,map_inv]
    rfl
  have hpU : p' (Q u) = p' v := by
    calc
      _ = (c • H) (p u) := (hcomm u).symm
      _ = (ν.real univ : ℂ) • (c • H) (Submodule.Quotient.mk f) := by
        change (c • H) (p (L (Submodule.Quotient.mk f))) = _
        rw [hp,map_smul]
      _ = (ν.real univ : ℂ) • p' (Submodule.Quotient.mk (sLocalSelectedFourier F S f)) :=
        congrArg ((ν.real univ : ℂ) • ·) ((hcomm (Submodule.Quotient.mk f)).trans
          (congrArg p' (sLocalCentralThetaFourier_mk F S f)))
      _ = _ := (hp' _).symm
  have he : Q u = v := (hFix (Q u) hU).symm.trans
    ((congrArg j hpU).trans (hFix v (hEig' _)))
  exact (congrArg (fun q : Theta F S ↦ sLocalThetaFunction F S q x) he).trans (hL' _ x)

private abbrev thetaCoefficient (ω : PontryaginDual (K F S)) (u : Theta F S) : ScalarL2 :=
  lpTwoCharacterCoefficient (μ := ν) (ν := (volume : Measure ℝ)) ω (productTheta F S ν u)

set_option maxHeartbeats 900000 in
private theorem thetaCoefficient_mk (ω : PontryaginDual (K F S)) (f : E F S) :
    (thetaCoefficient F S ν ω (Submodule.Quotient.mk f) : ℝ → ℂ) =ᵐ[volume]
      fun t ↦ (Real.exp (t/2) : ℂ) *
        sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t) := by
  let u : Theta F S := Submodule.Quotient.mk f
  have hs : MeasurePreserving (Prod.swap : ℝ × K F S → K F S × ℝ)
      ((volume : Measure ℝ).prod ν) (ν.prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  have h := Measure.ae_ae_of_ae_prod
    (hs.quasiMeasurePreserving.ae_eq_comp (productTheta_ae F S ν u))
  filter_upwards [h,lpTwoCharacterCoefficient_ae ω (productTheta F S ν u)] with t ht hcoef
  refine hcoef.2.trans ?_
  unfold sLocalHomogeneousTheta
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ht] with k hk
  change productTheta F S ν u (k,t) = (Real.exp (t/2) : ℂ) *
    sLocalThetaFunction F S u (sLocalZetaSplit F S (t,k)) at hk
  change (ω k : ℂ) * productTheta F S ν u (k,t) = _
  rw [hk]
  have he : sLocalZetaSplit F S (t,k) = k.val * sLocalLogNormRay F S t :=
    mul_comm (sLocalLogNormRay F S t) k.val
  rw [he]
  change (ω k : ℂ) * ((Real.exp (t/2) : ℂ) * sLocalThetaOperator F S f
      (k.val * sLocalLogNormRay F S t)) =
    (Real.exp (t/2) : ℂ) * ((ω k : ℂ) * sLocalThetaOperator F S f (k.val * sLocalLogNormRay F S t))
  ring

private theorem thetaCoefficient_parseval (u : Theta F S) :
    (∑' ω : PontryaginDual (K F S), ‖thetaCoefficient F S ν ω u‖^2) =
      ν.real univ * ‖sLocalCentralThetaMap F S ν u‖^2 := by
  letI : SecondCountableTopology (K F S) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : TopologicalSpace.PseudoMetrizableSpace (K F S) := inferInstance
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let g := productTheta F S ν u
  have h := tsum_sq_character_integral_prod ν (Lp.memLp g)
    (fun ω ↦ thetaCoefficient F S ν ω⁻¹ u) (fun ω ↦ by
      filter_upwards [lpTwoCharacterCoefficient_ae ω⁻¹ g] with t ht
      refine ht.2.trans (integral_congr_ae (Eventually.of_forall fun k ↦ ?_))
      change (ω⁻¹ k : ℂ) * g (k,t) = star (ω k : ℂ) * g (k,t)
      have hk : (ω⁻¹ k : ℂ) = star (ω k : ℂ) := Circle.coe_inv_eq_conj _
      rw [hk])
  have hn : ‖g‖^2 = ∫ p, ‖g p‖^2 ∂ν.prod (volume : Measure ℝ) := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp g)
  rw [← hn] at h
  have he : ‖g‖ = ‖sLocalCentralThetaMap F S ν u‖ :=
    (sLocalCentralProductEquiv F S ν).norm_map _
  rw [he] at h
  exact ((Equiv.inv (PontryaginDual (K F S))).tsum_eq
    (fun ω ↦ ‖thetaCoefficient F S ν ω u‖^2)).symm.trans h

section Tate

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

private abbrev V (v : S) := v.val.adicCompletion F

variable [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  (μ : ∀ v : S, Measure (V F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (hν : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)) Measure.count
    (sLocalClassHaar F S ν))
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]

set_option maxHeartbeats 1000000 in
include hν in
private theorem centralThetaFourier_norm (u : Theta F S) :
    ‖sLocalCentralThetaMap F S ν (sLocalCentralThetaFourier F S u)‖ =
      ‖sLocalCentralThetaMap F S ν u‖ := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F S).ker u
  let I := Ioo (0 : ℝ) 1
  let J := sLocalReflectedExponents I
  have hi : (1/2 : ℝ) ∈ I := ⟨by norm_num,by norm_num⟩
  have hj : (1/2 : ℝ) ∈ J := by change (1-(1/2) : ℝ) ∈ I; convert hi using 1; norm_num
  let u : Theta F S := Submodule.Quotient.mk f
  let v := sLocalCentralThetaFourier F S u
  have hcoord (ω : PontryaginDual (K F S)) : ‖thetaCoefficient F S ν ω⁻¹ v‖ =
      ‖thetaCoefficient F S ν ω u‖ := by
    obtain ⟨T,hT,hN⟩ :=
      exists_sLocalDecayFourier_profiles F S μ ν hν ω I isOpen_Ioo ordConnected_Ioo ⟨_,hi⟩ Subset.rfl
    obtain ⟨p,hp,hq⟩ := hT f
    have h₁ : thetaCoefficient F S ν ω u = sLocalDecayCentralTrace hi p := by
      apply Lp.ext
      filter_upwards [thetaCoefficient_mk F S ν ω f,sLocalDecayCentralTrace_ae hi p] with t ht ht'
      exact ht.trans ((congrArg ((Real.exp (t/2) : ℂ) * ·) (hp t).symm).trans ht'.symm)
    have hv : v = Submodule.Quotient.mk (sLocalSelectedFourier F S f) := sLocalCentralThetaFourier_mk F S f
    have h₂ : thetaCoefficient F S ν ω⁻¹ v = sLocalDecayCentralTrace hj (T p) := by
      rw [hv]
      apply Lp.ext
      filter_upwards [thetaCoefficient_mk F S ν ω⁻¹ (sLocalSelectedFourier F S f),
        sLocalDecayCentralTrace_ae hj (T p)] with t ht ht'
      exact ht.trans ((congrArg ((Real.exp (t/2) : ℂ) * ·) (hq t).symm).trans ht'.symm)
    rw [h₁,h₂]
    exact hN hi hj p
  have he : ν.real univ * ‖sLocalCentralThetaMap F S ν v‖^2 =
      ν.real univ * ‖sLocalCentralThetaMap F S ν u‖^2 := by
    rw [← thetaCoefficient_parseval F S ν v, ← thetaCoefficient_parseval F S ν u,
      ← (Equiv.inv (PontryaginDual (K F S))).tsum_eq
        (fun ω ↦ ‖thetaCoefficient F S ν ω v‖^2)]
    exact tsum_congr fun ω ↦ congrArg (·^2) (hcoord ω)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (mul_left_cancel₀ (measureReal_univ_ne_zero (μ := ν)) he)

set_option maxHeartbeats 1000000 in
include hν in
/-- A unitary extension of the actual selected-place Fourier operator
on the central theta Hilbert completion. -/
theorem exists_sLocalCentralFourier :
    ∃ U : ClassL2 F S ν ≃ₗᵢ[ℂ] ClassL2 F S ν,
      ∀ u, U (sLocalCentralThetaMap F S ν u) =
        sLocalCentralThetaMap F S ν (sLocalCentralThetaFourier F S u) := by
  let J := (sLocalCentralThetaMap F S ν).toLinearMap
  let Q := sLocalCentralThetaFourier F S
  let G := J.comp Q.toLinearMap
  let A := G.extendOfNorm J
  have hd : DenseRange J := sLocalCentralThetaMap_dense F S ν
  have hnorm (u : Theta F S) : ‖G u‖ = ‖J u‖ := centralThetaFourier_norm F S ν μ hν u
  have hA (u : Theta F S) : A (J u) = G u :=
    LinearMap.extendOfNorm_eq hd ⟨1,fun q ↦ by rw [one_mul,hnorm]⟩ u
  have hiso : ∀ u, ‖A u‖ = ‖u‖ := by
    intro x
    refine closure_minimal (t := {u | ‖A u‖ = ‖u‖}) ?_
      (isClosed_eq A.continuous.norm continuous_norm) (hd x)
    rintro _ ⟨u,rfl⟩
    exact (congrArg norm (hA u)).trans (hnorm u)
  let B : ClassL2 F S ν →ₗᵢ[ℂ] ClassL2 F S ν :=
    { toLinearMap := A.toLinearMap, norm_map' := hiso }
  have hs : Surjective Q := by
    intro u
    obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F S).ker u
    obtain ⟨f,hf⟩ := sLocalSelectedFourier_surjective F S g
    exact ⟨Submodule.Quotient.mk f,(sLocalCentralThetaFourier_mk F S f).trans
      (congrArg Submodule.Quotient.mk hf)⟩
  have hsurj : Surjective B := by
    intro x
    apply closure_minimal ?_ B.isometry.isClosedEmbedding.isClosed_range (hd x)
    rintro _ ⟨u,rfl⟩
    obtain ⟨v,rfl⟩ := hs u
    exact ⟨J v,hA v⟩
  exact ⟨LinearIsometryEquiv.ofSurjective B hsurj,hA⟩

private abbrev centralWeight :=
  sLocalClassHardySobolevMeasure F S ν (1/2) (1/2) 0

private abbrev WeightedL2 := Lp ℂ 2 (centralWeight F S ν)

set_option maxHeartbeats 1100000 in
include hν in
private theorem weightedThetaFourier :
    ∃ (j : Theta F S →L[ℂ] WeightedL2 F S ν)
      (U : WeightedL2 F S ν ≃ₗᵢ[ℂ] WeightedL2 F S ν),
      Injective j ∧ DenseRange j ∧
      (∀ u, (j u : C F S → ℂ) =ᵐ[centralWeight F S ν] sLocalThetaFunction F S u) ∧
      (∀ u, U (j u) = j (sLocalCentralThetaFourier F S u)) := by
  let W := centralWeight F S ν
  let η := sLocalClassHaar F S ν
  let w (q : C F S) := Real.exp (Real.log (sLocalClassModulus F S q)/2)
  have hw : Measurable w :=
    (Real.continuous_exp.comp ((continuous_toAdd.comp
      (continuous_sLocalThetaSobolevLogNorm F S)).div_const 2)).measurable
  have hwpos (q : C F S) : 0 < w q := Real.exp_pos _
  have hW : amplitudeMeasure η w = W := by
    unfold W centralWeight sLocalClassHardySobolevMeasure amplitudeMeasure
    congr 1
    funext q
    apply congrArg ENNReal.ofReal
    change w q ^ 2 = hardySobolevWeight (1/2) (1/2) 0 (Real.log (sLocalClassModulus F S q))
    simp only [w, ← Real.exp_nat_mul, Nat.cast_ofNat, hardySobolevWeight,
      zero_div, Real.rpow_zero, mul_one, max_self]
    congr 1
    ring
  change ∃ (j : Theta F S →L[ℂ] Lp ℂ 2 W) (U : Lp ℂ 2 W ≃ₗᵢ[ℂ] Lp ℂ 2 W),
    Injective j ∧ DenseRange j ∧ (∀ u, (j u : C F S → ℂ) =ᵐ[W] sLocalThetaFunction F S u) ∧
    (∀ u, U (j u) = j (sLocalCentralThetaFourier F S u))
  rw [← hW]
  obtain ⟨U,hU⟩ := exists_sLocalCentralFourier F S ν μ hν
  let e := amplitudeL2Iso η w hw hwpos
  let J := sLocalCentralThetaMap F S ν
  let j := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp J
  refine ⟨j,(e.trans U).trans e.symm,
    e.symm.injective.comp (sLocalThetaSobolevMap_injective F S ν (1/2) 0 0 0 (by norm_num) le_rfl le_rfl),
    e.symm.surjective.denseRange.comp (sLocalCentralThetaMap_dense F S ν) e.symm.continuous,?_,?_⟩
  · intro u
    have hθ := (amplitudeMeasure_absolutelyContinuous η w).ae_eq (centralTheta_ae F S ν u)
    filter_upwards [amplitudeL2Iso_symm_ae η w hw hwpos (J u),hθ] with q hq hθq
    change e.symm (J u) q = _
    rw [hq]
    change (w q)⁻¹ • (J u) q = _
    rw [hθq]
    change (w q)⁻¹ • ((w q : ℂ) * sLocalThetaFunction F S u q) = _
    rw [← Complex.real_smul, inv_smul_smul₀ (hwpos q).ne']
  · intro u
    change e.symm (U (e (e.symm (J u)))) = e.symm (J (sLocalCentralThetaFourier F S u))
    rw [e.apply_symm_apply,hU]

private abbrev Decay (I : Set ℝ) :=
  @ModulatedExponentialInductive (C F S) inferInstance inferInstance inferInstance
    inferInstance inferInstance (sLocalCechModulation F S) I

private def decayComponent {ω : PontryaginDual (K F S)} {I : Set ℝ}
    (u : sLocalCechDecayIsotype F S ω I) : Decay F S I := u.val

private def decayFourier_agrees {ω : PontryaginDual (K F S)} {I J : Set ℝ}
    (A : sLocalCechDecayIsotype F S ω I ≃L[ℂ] sLocalCechDecayIsotype F S ω⁻¹ J)
    (U : WeightedL2 F S ν ≃ₗᵢ[ℂ] WeightedL2 F S ν)
    (i : Decay F S I →L[ℂ] WeightedL2 F S ν) (i' : Decay F S J →L[ℂ] WeightedL2 F S ν) : Prop :=
  ∀ u : sLocalCechDecayIsotype F S ω I,
    U (i (decayComponent F S u)) = i' (decayComponent F S (A u))

set_option maxHeartbeats 3700000 in
include hν in
/-- Corrected Proposition 5.4.2.1(2). The central weighted Haar space is
the Hilbert completion of ordinary S-local theta. Selected-place Fourier
extends unitarily and restricts to the weighted decay Fourier map on each
character component, with inverse character on the target. -/
theorem exists_sLocalDecayFourier_onThetaCompletion
    (ω : PontryaginDual (K F S)) (I : Set ℝ) (hI : IsOpen I) (hIo : OrdConnected I)
    (hsub : I ⊆ Ioo (0 : ℝ) 1) (hh : (1/2 : ℝ) ∈ I) :
    let J := sLocalReflectedExponents I
    ∃ (j : Theta F S →L[ℂ] WeightedL2 F S ν)
      (U : WeightedL2 F S ν ≃ₗᵢ[ℂ] WeightedL2 F S ν)
      (i : Decay F S I →L[ℂ] WeightedL2 F S ν)
      (i' : Decay F S J →L[ℂ] WeightedL2 F S ν)
      (A : sLocalCechDecayIsotype F S ω I ≃L[ℂ] sLocalCechDecayIsotype F S ω⁻¹ J),
      Injective j ∧ DenseRange j ∧
      (∀ u, (j u : C F S → ℂ) =ᵐ[centralWeight F S ν] sLocalThetaFunction F S u) ∧
      (∀ u, U (j u) = j (sLocalCentralThetaFourier F S u)) ∧
      Injective i ∧ Injective i' ∧
      (∀ u, (i u : C F S → ℂ) =ᵐ[centralWeight F S ν] u.val) ∧
      (∀ u, (i' u : C F S → ℂ) =ᵐ[centralWeight F S ν] u.val) ∧
      (∀ f : E F S, ∃ u : sLocalCechDecayIsotype F S ω I,
        (∀ q, u.val.val q = sLocalHomogeneousTheta F S ν ω f.val q) ∧
        ∀ q, (A u).val.val q = sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val q) ∧
      decayFourier_agrees F S ν A U i i' := by
  intro J
  have hh' : (1/2 : ℝ) ∈ J := by change (1-(1/2) : ℝ) ∈ I; convert hh using 1; norm_num
  obtain ⟨j,U,hj_inj,hj_dense,hjae,hU⟩ := weightedThetaFourier F S ν μ hν
  obtain ⟨i,hi,_,hi_ae⟩ := exists_sLocalDecayHilbertInclusion_normalized F S ν I hh
  obtain ⟨i',hi',_,hi'_ae⟩ := exists_sLocalDecayHilbertInclusion_normalized F S ν J hh'
  obtain ⟨A,hA,_⟩ := existsUnique_sLocalDecayFourier F S μ ν hν ω I hI hIo ⟨_,hh⟩ hsub
  refine ⟨j,U,i,i',A,hj_inj,hj_dense,hjae,hU,hi,hi',hi_ae,hi'_ae,hA,?_⟩
  unfold decayFourier_agrees
  let D := {u : sLocalCechDecayIsotype F S ω I |
    ∃ f : E F S, ∀ q : C F S, u.val.val q = sLocalHomogeneousTheta F S ν ω f.val q}
  let B := fun u : sLocalCechDecayIsotype F S ω I ↦ U (i (decayComponent F S u))
  let B' := fun u : sLocalCechDecayIsotype F S ω I ↦ i' (decayComponent F S (A u))
  have hB : Continuous B := U.continuous.comp (i.continuous.comp continuous_subtype_val)
  have hB' : Continuous B' := i'.continuous.comp (continuous_subtype_val.comp A.continuous)
  have he : EqOn B B' D := by
    rintro p ⟨f,hf⟩
    obtain ⟨u,hu,hAu⟩ := hA f
    have heq : p = u := Subtype.ext (ModulatedExponentialInductive.algebraicEquiv.injective
      (Subtype.ext (funext fun q ↦ (hf q).trans (hu q).symm)))
    obtain ⟨L,hL,hFL⟩ := exists_fourierThetaLift F S ν ω
    let x := L (Submodule.Quotient.mk f)
    have hix : i p.val = j x := by
      apply Lp.ext
      filter_upwards [hi_ae p.val,hjae x] with q hq hq'
      exact hq.trans ((hf q).trans ((hL f q).symm.trans hq'.symm))
    have hv : ∀ q, sLocalThetaFunction F S (sLocalCentralThetaFourier F S x) q =
        sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val q := hFL f
    have hiy : i' (decayComponent F S (A p)) = j (sLocalCentralThetaFourier F S x) := by
      apply Lp.ext
      filter_upwards [hi'_ae (A p).val,hjae (sLocalCentralThetaFourier F S x)] with q hq hq'
      have hAp : (A p).val.val q = sLocalHomogeneousTheta F S ν ω⁻¹
          (sLocalSelectedFourier F S f).val q := by rw [heq]; exact hAu q
      exact hq.trans (hAp.trans ((hv q).symm.trans hq'.symm))
    change U (i p.val) = i' (decayComponent F S (A p))
    rw [hix,hiy,hU]
  exact fun p ↦ closure_minimal he (isClosed_eq hB hB') (dense_sLocalDecayTheta F S ν ω I ⟨_,hh⟩ p)

end Tate

end

end Masullo
