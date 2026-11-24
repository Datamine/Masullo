import SLocalPrincipalValue
import SLocalZetaProduct
import SLocalThetaKernels
import Mathlib.Topology.Metrizable.Urysohn

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Q := SIdeleQuotient F S
private abbrev K := SLocalThetaNormOne F S
private abbrev G := (SAdeles F S)ˣ
private abbrev E := sLocalBruhatImage F S
private abbrev H := sUnitImage F S
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Local (v : S) := locallyConstantTests (v.val.adicCompletion F)
private abbrev Rest (v : S) :=
  (w : {w : S // w ≠ v}) → w.val.val.adicCompletion F

local instance sLocalPrincipalZeta_classMeasurable : MeasurableSpace (Q F S) := borel _
local instance sLocalPrincipalZeta_classBorel : BorelSpace (Q F S) := ⟨rfl⟩
local instance sLocalPrincipalZeta_idelesMeasurable : MeasurableSpace (G F S) := borel _
local instance sLocalPrincipalZeta_idelesBorel : BorelSpace (G F S) := ⟨rfl⟩

private theorem singleFiniteIdele_mem_block (v : S) (r : (v.val.adicCompletion F)ˣ) :
    singleFiniteIdele F v.val r ∈ sIdeleBlock F S := by
  apply (sIdeleBlock_mem_iff F S _).mpr
  intro w hw
  apply (ideleOrder_eq_zero_iff F _ w).mpr
  have hne : w ≠ v.val := fun h => hw (h.symm ▸ v.property)
  change Valued.v (Function.update (fun p : HeightOneSpectrum (𝓞 F) => (1 : p.adicCompletion F))
    v.val r.val w) = 1
  rw [Function.update_of_ne hne, map_one]

private def placeIdele (v : S) (r : (v.val.adicCompletion F)ˣ) : G F S :=
  (sBlockUnitProduct F S ⟨singleFiniteIdele F v.val r, singleFiniteIdele_mem_block F S v r⟩).1

private theorem placeIdele_norm (v : S) (r : (v.val.adicCompletion F)ˣ) :
    sLocalIdeleNorm F S (placeIdele F S v r) = ‖r.val‖ := by
  rw [placeIdele, sBlock_norm_eq]
  exact singleFiniteIdele_norm F v.val r

private theorem placeIdele_arch (v : S) (r : (v.val.adicCompletion F)ˣ) :
    (placeIdele F S v r).val.1 = 1 := rfl

private theorem placeIdele_finite_self (v : S) (r : (v.val.adicCompletion F)ˣ) :
    (placeIdele F S v r).val.2 v = r.val := by
  change Function.update (fun p : HeightOneSpectrum (𝓞 F) => (1 : p.adicCompletion F))
    v.val r.val v.val = _
  rw [Function.update_self]

private theorem placeIdele_finite_other (v w : S) (h : w ≠ v) (r : (v.val.adicCompletion F)ˣ) :
    (placeIdele F S v r).val.2 w = 1 := by
  change Function.update (fun p : HeightOneSpectrum (𝓞 F) => (1 : p.adicCompletion F))
    v.val r.val w.val = _
  rw [Function.update_of_ne (fun h' => h (Subtype.ext h'))]

private def pureAt (v : S) (φ : Arch F) (k : locallyConstantTests (Rest F S v)) :
    Local F S v →ₗ[ℂ] E F S :=
  (sLocalBruhatPure F S φ).comp
    ((locallyConstantTestCongr (sLocalFiniteCoordinateSplit F S v)).symm.toLinearMap.comp
      (locallyConstantTestProduct.flip k))

private theorem pureAt_eq (v : S) (φ : Arch F) (k : locallyConstantTests (Rest F S v))
    (b : Local F S v) :
    pureAt F S v φ k b = sLocalBruhatPure F S φ (sLocalCoordinatePure F S v b k) := rfl

private theorem pureAt_idele_translate (v : S) (φ : Arch F)
    (k : locallyConstantTests (Rest F S v)) (b : Local F S v)
    (r : (v.val.adicCompletion F)ˣ) (g : G F S) :
    sLocalBruhatRestriction F S
      (pureAt F S v φ k (locallyConstantTestTranslate (v.val.adicCompletion F) r b)).val
      (placeIdele F S v r * g).val =
    sLocalBruhatRestriction F S (pureAt F S v φ k b).val g.val := by
  rw [pureAt_eq, pureAt_eq, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
  have harch : (placeIdele F S v r * g).val.1 = g.val.1 := by
    change (placeIdele F S v r).val.1 * g.val.1 = _
    rw [placeIdele_arch, one_mul]
  have hfinite (w : S) : (placeIdele F S v r * g).val.2 w =
      (placeIdele F S v r).val.2 w * g.val.2 w := rfl
  have hrest : (sLocalFiniteCoordinateSplit F S v (placeIdele F S v r * g).val.2).2 =
      (sLocalFiniteCoordinateSplit F S v g.val.2).2 := by
    funext w
    change (placeIdele F S v r * g).val.2 w.val = g.val.2 w.val
    rw [hfinite, placeIdele_finite_other F S v w.val w.property, one_mul]
  have hv : (placeIdele F S v r * g).val.2 v = r.val * g.val.2 v := by
    rw [hfinite, placeIdele_finite_self]
  rw [harch]
  congr 1
  change b.val (r⁻¹.val * (placeIdele F S v r * g).val.2 v) *
      k.val (sLocalFiniteCoordinateSplit F S v (placeIdele F S v r * g).val.2).2 =
    b.val (g.val.2 v) * k.val (sLocalFiniteCoordinateSplit F S v g.val.2).2
  rw [hv, hrest, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

variable (μ : Measure (G F S)) [μ.IsHaarMeasure]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (H F S) μ Measure.count (sLocalClassHaar F S ν))
variable (ω : PontryaginDual (K F S)) (z : ℂ)

private def placeWeight (v : S) (r : (v.val.adicCompletion F)ˣ) : ℂ :=
  sLocalZetaWeight F S ω z (QuotientGroup.mk (placeIdele F S v r))

private theorem sLocalIdelicZeta_translate_pureAt (v : S) (φ : Arch F)
    (k : locallyConstantTests (Rest F S v)) (b : Local F S v)
    (r : (v.val.adicCompletion F)ˣ) :
    sLocalIdelicZetaIntegral F S μ ω
      (pureAt F S v φ k (locallyConstantTestTranslate (v.val.adicCompletion F) r b)) z =
      placeWeight F S ω z v r * sLocalIdelicZetaIntegral F S μ ω (pureAt F S v φ k b) z := by
  unfold sLocalIdelicZetaIntegral
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_mul_left_eq_self _ (placeIdele F S v r)]
  apply integral_congr_ae
  filter_upwards with g
  unfold sLocalIdelicZetaIntegrand
  rw [pureAt_idele_translate F S, QuotientGroup.mk_mul, sLocalZetaWeight_mul]
  exact mul_assoc _ _ _

/-- The multiplier at a selected finite place, measured by the actual
S-idelic quasi-character on the inserted unit group. -/
def sLocalPrincipalZetaFactor (v : S) : ℂ :=
  if ∀ a : principalIntegralUnits F v.val, placeWeight F S ω z v a.val = 1
  then 1 - placeWeight F S ω z v (chosenFiniteUniformizer F v.val) else 1

private theorem placeIdele_eq_finiteZetaInsert (v : S) (r : (v.val.adicCompletion F)ˣ) :
    placeIdele F S v r = sLocalFiniteZetaInsert F S v r := by
  apply Units.ext
  apply Prod.ext
  · exact placeIdele_arch F S v r
  · funext w
    change (placeIdele F S v r).val.2 w = ((Pi.mulSingle v r : ∀ j : S, (j.val.adicCompletion F)ˣ) w).val
    by_cases h : w = v
    · subst w
      rw [Pi.mulSingle_eq_same, placeIdele_finite_self]
    · rw [Pi.mulSingle_eq_of_ne h, placeIdele_finite_other F S v w h, Units.val_one]

private theorem placeWeight_eq_finiteZetaWeight (v : S) (r : (v.val.adicCompletion F)ˣ) :
    placeWeight F S ω z v r =
      (sLocalFiniteZetaPhases F S ω v r : ℂ) * finiteZetaWeight F v.val z r := by
  let a : Q F S := QuotientGroup.mk (placeIdele F S v r)
  have he := sLocalClassModulus_mk F S (placeIdele F S v r)
  rw [placeIdele_norm] at he
  have hPh : (sLocalFiniteZetaPhases F S ω v r : ℂ) = sLocalZetaWeight F S ω 0 a := by
    change sLocalZetaWeight F S ω 0 (QuotientGroup.mk (sLocalFiniteZetaInsert F S v r)) =
      sLocalZetaWeight F S ω 0 (QuotientGroup.mk (placeIdele F S v r))
    rw [placeIdele_eq_finiteZetaInsert]
  change sLocalZetaWeight F S ω z a = _
  rw [hPh]
  unfold sLocalZetaWeight finiteZetaWeight
  simp only [zero_mul, Complex.exp_zero, one_mul]
  change Complex.exp (z * (Real.log (sLocalClassModulus F S a) : ℂ)) * _ = _
  rw [he, mul_comm]

/-- The actual character multiplier of a finite Weil operator is precisely
the continuation's local Euler denominator at an unramified place. -/
theorem sLocalPrincipalZetaFactor_eq_finiteZetaWeilMultiplier (v : S) :
    sLocalPrincipalZetaFactor F S ω z v =
      finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) z := by
  let χ := sLocalFiniteZetaPhases F S ω v
  have hI (r : (v.val.adicCompletion F)ˣ) :
      r ∈ finitePlaceIntegralUnits F v.val ↔ ‖r.val‖ = 1 :=
    (localIntegralUnits_value F v.val r).trans (finiteCompletion_norm_eq_one_iff F v.val r).symm
  have hmem : (∀ a : principalIntegralUnits F v.val, placeWeight F S ω z v a.val = 1) ↔
      finiteZetaUnramified F v.val χ := by
    constructor
    · intro h r hr
      let a : principalIntegralUnits F v.val := ⟨r, (hI r).mp hr⟩
      have h' : (χ r : ℂ) * finiteZetaWeight F v.val z r = 1 :=
        (placeWeight_eq_finiteZetaWeight F S ω z v r).symm.trans (h a)
      simp only [finiteZetaWeight, (hI r).mp hr, Real.log_one, Complex.ofReal_zero,
        mul_zero, Complex.exp_zero, mul_one] at h'
      exact Circle.coe_injective (h'.trans Circle.coe_one.symm)
    · intro h a
      rw [placeWeight_eq_finiteZetaWeight, show sLocalFiniteZetaPhases F S ω v a.val = 1
        from h _ ((hI a.val).mpr a.property)]
      simp [finiteZetaWeight, show ‖a.val.val‖ = 1 from a.property]
  unfold sLocalPrincipalZetaFactor finiteZetaWeilMultiplier
  rw [hmem]
  split_ifs
  · rw [placeWeight_eq_finiteZetaWeight]
    unfold finiteZetaRatio finiteZetaWeight
    rw [norm_finiteUniformizer F v.val _ (chosenFiniteUniformizer_spec F v.val), Real.log_inv,
      Complex.ofReal_neg, mul_neg, neg_mul]
  · rfl

theorem sLocalPrincipalZetaFactor_of_unramified (v : S)
    (hv : finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F S ω v)) :
    sLocalPrincipalZetaFactor F S ω z v =
      1 - sLocalZetaWeight F S ω z (QuotientGroup.mk
        (sLocalFiniteZetaInsert F S v (chosenFiniteUniformizer F v.val))) := by
  have h (a : principalIntegralUnits F v.val) : placeWeight F S ω z v a.val = 1 := by
    rw [placeWeight_eq_finiteZetaWeight]
    have ha : a.val ∈ finitePlaceIntegralUnits F v.val :=
      (localIntegralUnits_value F v.val a.val).mpr
        ((finiteCompletion_norm_eq_one_iff F v.val a.val).mp a.property)
    simp [finiteZetaWeight, hv _ ha, show ‖a.val.val‖ = 1 from a.property]
  rw [sLocalPrincipalZetaFactor, ite_eq_left h, placeWeight, placeIdele_eq_finiteZetaInsert]

theorem sLocalPrincipalZetaFactor_ne_zero (v : S) (hz : 0 < z.re) :
    sLocalPrincipalZetaFactor F S ω z v ≠ 0 := by
  unfold sLocalPrincipalZetaFactor
  split_ifs
  · have h : ‖placeWeight F S ω z v (chosenFiniteUniformizer F v.val)‖ < 1 := by
      rw [placeWeight, norm_sLocalZetaWeight_mk, placeIdele_norm,
        norm_finiteUniformizer F v.val _ (chosenFiniteUniformizer_spec F v.val)]
      have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
      rw [Real.log_inv, ← Real.exp_zero, Real.exp_lt_exp]
      exact mul_neg_of_pos_of_neg hz (neg_neg_of_pos (Real.log_pos hq))
    exact sub_ne_zero.mpr fun he => by rw [← he, norm_one] at h; exact lt_irrefl _ h
  · exact one_ne_zero

include hν in
private theorem sLocalThetaZeta_weilPrincipalValue_pureAt (v : S) (φ : Arch F)
    (k : locallyConstantTests (Rest F S v)) (b : Local F S v) (hz : 0 < z.re) :
    sLocalThetaZetaIntegral F S ν ω (sLocalWeilPrincipalValue F S v (pureAt F S v φ k b)) z =
      sLocalPrincipalZetaFactor F S ω z v * sLocalThetaZetaIntegral F S ν ω (pureAt F S v φ k b) z := by
  let Z := sLocalThetaZetaCLM F S ν ω z hz
  let L := Z.toLinearMap.comp (pureAt F S v φ k)
  have he (r : (v.val.adicCompletion F)ˣ) (b : Local F S v) :
      L (locallyConstantTestTranslate (v.val.adicCompletion F) r b) =
        placeWeight F S ω z v r * L b := by
    change sLocalThetaZetaIntegral F S ν ω (pureAt F S v φ k
      (locallyConstantTestTranslate (v.val.adicCompletion F) r b)) z =
        placeWeight F S ω z v r * sLocalThetaZetaIntegral F S ν ω (pureAt F S v φ k b) z
    rw [← (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω _ z hz).2,
      ← (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω _ z hz).2]
    exact sLocalIdelicZeta_translate_pureAt F S μ ω z v φ k b r
  have h := weilPrincipalValue_eigenfunctional F v.val L (placeWeight F S ω z v) he b
  have hp : sLocalWeilPrincipalValue F S v (pureAt F S v φ k b) =
      pureAt F S v φ k (weilPrincipalValue F v.val b) := by
    rw [pureAt_eq, pureAt_eq, sLocalWeilPrincipalValue, sLocalBruhatFiniteMap_pure,
      sLocalCoordinateMap_pure_self]
  rw [hp]
  exact h

include hν in
/-- On the positive half-plane the actual S-local zeta functional is
multiplied by the selected local Euler factor. -/
theorem sLocalThetaZeta_weilPrincipalValue (v : S) (f : E F S) (hz : 0 < z.re) :
    sLocalThetaZetaIntegral F S ν ω (sLocalWeilPrincipalValue F S v f) z =
      sLocalPrincipalZetaFactor F S ω z v * sLocalThetaZetaIntegral F S ν ω f z := by
  let Z := sLocalThetaZetaCLM F S ν ω z hz
  change Z (sLocalWeilPrincipalValue F S v f) = sLocalPrincipalZetaFactor F S ω z v * Z f
  let B := locallyConstantTests ((w : S) → w.val.adicCompletion F)
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace (Arch F ⊗[ℂ] B) := inductiveTensorTopology _ _
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]
  | tmul φ ψ =>
    change Z (sLocalWeilPrincipalValue F S v (sLocalBruhatPure F S φ ψ)) =
      sLocalPrincipalZetaFactor F S ω z v * Z (sLocalBruhatPure F S φ ψ)
    let c := locallyConstantTestCongr (sLocalFiniteCoordinateSplit F S v)
    let p := locallyConstantTestProductEquiv (X := v.val.adicCompletion F) (Y := Rest F S v)
    obtain ⟨d, rfl⟩ := (p.trans c.symm).surjective ψ
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, mul_add]
    | tmul b k =>
      have h : (p.trans c.symm) (b ⊗ₜ[ℂ] k) = sLocalCoordinatePure F S v b k :=
        congrArg c.symm (locallyConstantTestProductEquiv_tmul b k)
      rw [h, ← pureAt_eq]
      exact sLocalThetaZeta_weilPrincipalValue_pureAt F S μ ν hν ω z v φ k b hz

private theorem thetaHaar_weaklyRegular : ν.WeaklyRegular := by
  letI : T1Space (Q F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI := sLocalIdeles_secondCountable F S
  letI : SecondCountableTopology (Q F S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : SecondCountableTopology (K F S) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  letI : TopologicalSpace.PseudoMetrizableSpace (K F S) := inferInstance
  letI := sLocalThetaNormOne_compact F S
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  infer_instance

include hν in
private theorem sLocalWeilPrincipalValue_theta_zero_iff (v : S) (f : E F S) :
    sLocalThetaOperator F S (sLocalWeilPrincipalValue F S v f) = 0 ↔
      sLocalThetaOperator F S f = 0 := by
  letI : ν.WeaklyRegular := thetaHaar_weaklyRegular F S ν
  rw [sLocalTheta_zero_iff_verticalZeta F S ν _ 1 zero_lt_one,
    sLocalTheta_zero_iff_verticalZeta F S ν f 1 zero_lt_one]
  apply forall_congr'
  intro ω
  apply forall_congr'
  intro y
  let w := (1 : ℂ) + (y : ℂ) * Complex.I
  have hw : 0 < w.re := by simp [w]
  change sLocalThetaZetaIntegral F S ν ω (sLocalWeilPrincipalValue F S v f) w = 0 ↔
    sLocalThetaZetaIntegral F S ν ω f w = 0
  rw [sLocalThetaZeta_weilPrincipalValue F S μ ν hν ω w v f hw]
  exact mul_eq_zero_iff_left (sLocalPrincipalZetaFactor_ne_zero F S ω w v hw)

include hν in
/-- A finite product preserves and reflects the actual S-local theta kernel. -/
theorem sLocalWeilPrincipalValues_theta_zero_iff (s : Finset S) (f : E F S) :
    sLocalThetaOperator F S (sLocalWeilPrincipalValues F S s f) = 0 ↔
      sLocalThetaOperator F S f = 0 := by
  unfold sLocalWeilPrincipalValues
  refine Finset.noncommProd_induction s (sLocalWeilPrincipalValue F S) _
    (fun T : E F S →L[ℂ] E F S => ∀ f : E F S,
      sLocalThetaOperator F S (T f) = 0 ↔ sLocalThetaOperator F S f = 0) ?_ ?_ ?_ f
  · intro A B hA hB x
    exact (hA (B x)).trans (hB x)
  · intro x
    exact Iff.rfl
  · intro v _ x
    exact sLocalWeilPrincipalValue_theta_zero_iff F S μ ν hν v x

include hν in
/-- The actual finite-place operator on the S-local theta quotient. -/
def sLocalWeilPrincipalValuesQuotient (s : Finset S) :
    SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S := by
  let N := (sLocalThetaOperator F S).ker
  let P := sLocalWeilPrincipalValues F S s
  refine N.liftQL (N.mkQL.comp P) ?_
  intro f hf
  change N.mkQ (P f) = 0
  apply (LinearMap.mem_ker).mp
  rw [Submodule.ker_mkQ]
  exact (sLocalWeilPrincipalValues_theta_zero_iff F S μ ν hν s f).2 hf

include hν in
@[simp] theorem sLocalWeilPrincipalValuesQuotient_mk (s : Finset S) (f : E F S) :
    sLocalWeilPrincipalValuesQuotient F S μ ν hν s ((sLocalThetaOperator F S).ker.mkQ f) =
      (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S s f) := rfl

include hν in
/-- The descended operator is injective because the Euler factor is nonzero
throughout the absolute convergence half-plane. -/
theorem sLocalWeilPrincipalValuesQuotient_injective (s : Finset S) :
    Injective (sLocalWeilPrincipalValuesQuotient F S μ ν hν s) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro q hq
  let N := (sLocalThetaOperator F S).ker
  obtain ⟨f, rfl⟩ := N.mkQ_surjective q
  change sLocalWeilPrincipalValuesQuotient F S μ ν hν s (N.mkQ f) = 0 at hq
  rw [sLocalWeilPrincipalValuesQuotient_mk] at hq
  have hf : sLocalWeilPrincipalValues F S s f ∈ N := by
    rw [← Submodule.ker_mkQ N]
    exact LinearMap.mem_ker.mpr hq
  have hf' : f ∈ N := (sLocalWeilPrincipalValues_theta_zero_iff F S μ ν hν s f).1 hf
  exact LinearMap.mem_ker.mp (show f ∈ N.mkQ.ker by rwa [Submodule.ker_mkQ])


/-- The representative formula determines a unique continuous injective
operator on the theta quotient, independently of Haar normalization. -/
theorem existsUnique_sLocalWeilPrincipalValuesQuotient (s : Finset S) :
    ∃! P : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S,
      Injective P ∧ ∀ f : E F S,
        P ((sLocalThetaOperator F S).ker.mkQ f) =
          (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S s f) := by
  letI := sLocalIdeles_locallyCompact F S
  let μ : Measure (G F S) := Measure.haar
  letI : μ.IsHaarMeasure := inferInstance
  obtain ⟨ν, hνHaar, hνWeil⟩ := sLocalClassHaar_exists_weil F S μ
  letI := hνHaar
  let P := sLocalWeilPrincipalValuesQuotient F S μ ν hνWeil s
  refine ⟨P, ⟨sLocalWeilPrincipalValuesQuotient_injective F S μ ν hνWeil s, fun _ => rfl⟩, ?_⟩
  intro P' hP'
  ext q
  obtain ⟨f, rfl⟩ := (sLocalThetaOperator F S).ker.mkQ_surjective q
  exact hP'.2 f


end
end Masullo
