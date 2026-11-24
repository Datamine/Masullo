import SLocalFourierIntegral
import SLocalThetaFourier
import HeckeEulerProducts
import FinitePrincipalValue
import AdelicFourierCovariance

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F S
private abbrev A := Adeles F

private abbrev differentMultiplicity (v : Place F) :=
  multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))

private def codifferentFactor (v : Place F) : (v.adicCompletion F)ˣ :=
  chosenFiniteUniformizer F v ^ (-(differentMultiplicity F v : ℤ))

private def omittedDifferent :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset \ S

/-- The idele that scales the omitted integer lattices onto their
codifferents and is one on all selected coordinates. -/
def sLocalCodifferentTailIdele : Idele F :=
  ∏ v ∈ omittedDifferent F S, singleFiniteIdele F v (codifferentFactor F v)

private theorem sLocalCodifferentTailIdele_arch :
    (sLocalCodifferentTailIdele F S).val.1 = 1 := by
  let ev : Idele F →* InfiniteAdeleRing F :=
    (RingHom.fst _ _).toMonoidHom.comp (Units.coeHom _)
  change ev (∏ v ∈ omittedDifferent F S, singleFiniteIdele F v (codifferentFactor F v)) = 1
  rw [map_prod]
  exact Finset.prod_eq_one fun _ _ ↦ rfl

private theorem sLocalCodifferentTailIdele_finite (v : Place F) :
    (sLocalCodifferentTailIdele F S).val.2 v =
      if v ∈ S then 1 else (codifferentFactor F v).val := by
  let ev : Idele F →* v.adicCompletion F :=
    ((RestrictedProduct.evalRingHom (fun w : Place F ↦ w.adicCompletion F) v).comp
      (RingHom.snd _ _)).toMonoidHom.comp (Units.coeHom _)
  have hev (w : Place F) : ev (singleFiniteIdele F w (codifferentFactor F w)) =
      Function.update (fun w : Place F ↦ (1 : w.adicCompletion F)) w (codifferentFactor F w).val v := rfl
  change ev (∏ w ∈ omittedDifferent F S, singleFiniteIdele F w (codifferentFactor F w)) = _
  rw [map_prod]
  by_cases hv : v ∈ omittedDifferent F S
  · have hn : v ∉ S := (Finset.mem_sdiff.mp hv).2
    rw [ite_eq_right hn, Finset.prod_eq_single_of_mem v hv]
    · rw [hev, Function.update_self]
    · intro w _ hw
      rw [hev, Function.update_of_ne (Ne.symm hw)]
  · rw [Finset.prod_eq_one]
    · by_cases hS : v ∈ S
      · rw [ite_eq_left hS]
      · have hd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
          intro he
          apply hv
          apply Finset.mem_sdiff.mpr
          exact ⟨by simpa using he, hS⟩
        rw [ite_eq_right hS, codifferentFactor, show differentMultiplicity F v = 0
          from multiplicity_eq_zero.mpr hd, Nat.cast_zero, neg_zero, zpow_zero, Units.val_one]
    · intro w hw
      have hne : v ≠ w := fun h ↦ hv (h.symm ▸ hw)
      rw [hev, Function.update_of_ne hne]

theorem sLocalCodifferentTailIdele_projection :
    sAdelesProjection F S (sLocalCodifferentTailIdele F S).val = 1 := by
  apply Prod.ext
  · exact sLocalCodifferentTailIdele_arch F S
  · funext v
    change (sLocalCodifferentTailIdele F S).val.2 v.val = 1
    rw [sLocalCodifferentTailIdele_finite, ite_eq_left v.property]

private theorem codifferentFactor_norm (v : Place F) :
    ‖(codifferentFactor F v).val‖ = (v.asIdeal.absNorm : ℝ) ^ differentMultiplicity F v := by
  unfold codifferentFactor
  rw [finitePlaceUniformizer_norm_zpow, neg_neg, zpow_natCast]

private theorem sLocalCodifferentTailIdele_inv_mul_mem (v : Place F) (hv : v ∉ S) (b : A F) :
    (((sLocalCodifferentTailIdele F S)⁻¹).val * b).2 v ∈ v.adicCompletionIntegers F ↔
      b.2 v ∈ finitePlaceIntegerAnnihilator F v := by
  let γ := sLocalCodifferentTailIdele F S
  have hγ : γ.val.2 v = (codifferentFactor F v).val := by
    rw [sLocalCodifferentTailIdele_finite, ite_eq_right hv]
  have hγinv : (γ⁻¹).val.2 v = ((codifferentFactor F v)⁻¹).val := by
    have he : γ.val.2 v * (γ⁻¹).val.2 v = 1 :=
      congrArg (fun a : A F ↦ a.2 v) γ.val_inv
    rw [hγ] at he
    apply (mul_left_cancel₀ (Units.ne_zero (codifferentFactor F v)))
    exact he.trans (Units.val_inv _).symm
  change (γ⁻¹).val.2 v * b.2 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ↔ _
  rw [finitePlaceIntegerAnnihilator_eq_differentBall, ← finiteCompletion_closedBall F v]
  change dist ((γ⁻¹).val.2 v * b.2 v) 0 ≤ 1 ↔
    ‖b.2 v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentMultiplicity F v
  rw [dist_zero_right, hγinv, Units.val_inv_eq_inv_val, norm_mul, norm_inv, codifferentFactor_norm]
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [inv_mul_le_iff₀ (pow_pos hq _), mul_one]

/-- The global Fourier transform is the S-local transform extended by
the omitted codifferent indicators. The extension is the indicated
idele translate of the usual integral-tail embedding. -/
theorem sLocalFourier_eq_tailTranslate (f : E F S) :
    GlobalBruhat.fourier F f.val =
      GlobalBruhat.leftTranslate F (sLocalCodifferentTailIdele F S) (sLocalFourierCompression F S f).val := by
  let γ := sLocalCodifferentTailIdele F S
  have hγ : sAdelesProjection F S γ.val = 1 := sLocalCodifferentTailIdele_projection F S
  have hinv : sAdelesProjection F S (γ⁻¹).val = 1 := by
    have he := congrArg (sAdelesProjection F S) γ.val_inv
    change sAdelesProjection F S γ.inv = 1
    simpa only [map_mul, hγ, one_mul, map_one] using he
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext b
  change GlobalBruhat.evaluation F b (GlobalBruhat.fourier F f.val) =
    GlobalBruhat.evaluation F b (GlobalBruhat.leftTranslate F γ (sLocalFourierCompression F S f).val)
  rw [GlobalBruhat.leftTranslate_apply, sLocalFourier_codifferent_reconstruct,
    sLocalBruhatRestriction_reconstruct]
  have hproj : sAdelesProjection F S ((γ⁻¹).val * b) = sAdelesProjection F S b := by
    rw [map_mul, hinv, one_mul]
  have hmem : (∀ v ∉ S, ((γ⁻¹).val * b).2 v ∈ v.adicCompletionIntegers F) ↔
      (∀ v ∉ S, b.2 v ∈ finitePlaceIntegerAnnihilator F v) :=
    forall_congr' fun v ↦ imp_congr_right fun hv ↦ sLocalCodifferentTailIdele_inv_mul_mem F S v hv b
  rw [hproj, hmem]
  change _ = sLocalBruhatRestriction F S
    (sLocalBruhatCorestrict F S (GlobalBruhat.fourier F f.val)).val _ * _
  rw [sLocalBruhatCorestrict_restrict]

theorem globalBruhat_fourier_leftTranslate (g : Idele F) (f : GlobalBruhat F) :
    GlobalBruhat.fourier F (GlobalBruhat.leftTranslate F g f) =
      (ideleNorm F g : ℂ) • GlobalBruhat.leftTranslate F g⁻¹ (GlobalBruhat.fourier F f) := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  letI : MeasurableSpace (A F) := borel _
  letI : BorelSpace (A F) := ⟨rfl⟩
  let μ := adelicHaarUnitDomain F
  letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  let b := (GlobalBruhat.algebraicEquiv F f).val
  have hb : Measurable b := (bruhat_continuous F (GlobalBruhat.algebraicEquiv F f).property).measurable
  change GlobalBruhat.evaluation F a (GlobalBruhat.fourier F (GlobalBruhat.leftTranslate F g f)) =
    GlobalBruhat.evaluation F a
      ((ideleNorm F g : ℂ) • GlobalBruhat.leftTranslate F g⁻¹ (GlobalBruhat.fourier F f))
  rw [map_smul, GlobalBruhat.leftTranslate_apply]
  change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F (GlobalBruhat.leftTranslate F g f))).val a =
    (ideleNorm F g : ℂ) • (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val (g.val * a)
  rw [GlobalBruhat.fourier_apply, GlobalBruhat.fourier_apply]
  change adelicFourierIntegral F μ (standardAdelicCharacter F) (fun x ↦ b (g⁻¹.val * x)) a =
    (ideleNorm F g : ℂ) • adelicFourierIntegral F μ (standardAdelicCharacter F) b (g.val * a)
  have h := adelicFourier_mul_argument F μ _ (standardAdelicCharacter_continuous F) b hb g⁻¹ a
  rw [map_inv (ideleNorm F), inv_inv] at h
  exact h

private theorem globalBruhat_leftTranslate_inverse (g : Idele F) (f : GlobalBruhat F) :
    GlobalBruhat.leftTranslate F g⁻¹ (GlobalBruhat.leftTranslate F g f) = f := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  change GlobalBruhat.evaluation F a
      (GlobalBruhat.leftTranslate F g⁻¹ (GlobalBruhat.leftTranslate F g f)) =
    GlobalBruhat.evaluation F a f
  rw [GlobalBruhat.leftTranslate_apply, GlobalBruhat.leftTranslate_apply, inv_inv, ← mul_assoc]
  change GlobalBruhat.evaluation F (g.inv * g.val * a) f = _
  rw [g.inv_val, one_mul]

/-- Enlarging a stage changes the compressed transform by the ratio of
the two omitted codifferent ideles. -/
theorem sLocalFourierCompression_transition_global {T : Finset (Place F)}
    (hST : S ⊆ T) (f : E F S) :
    (sLocalFourierCompression F T (sLocalBruhatTransition F hST f)).val =
      GlobalBruhat.leftTranslate F
        ((sLocalCodifferentTailIdele F T)⁻¹ * sLocalCodifferentTailIdele F S)
        (sLocalFourierCompression F S f).val := by
  let a := sLocalCodifferentTailIdele F T
  let b := sLocalCodifferentTailIdele F S
  let g := sLocalFourierCompression F S f
  let g' := sLocalFourierCompression F T (sLocalBruhatTransition F hST f)
  have h := (sLocalFourier_eq_tailTranslate F T (sLocalBruhatTransition F hST f)).symm.trans
    (sLocalFourier_eq_tailTranslate F S f)
  change GlobalBruhat.leftTranslate F a g'.val = GlobalBruhat.leftTranslate F b g.val at h
  have e := congrArg (GlobalBruhat.leftTranslate F a⁻¹) h
  rw [globalBruhat_leftTranslate_inverse] at e
  refine e.trans ?_
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F a⁻¹
    (GlobalBruhat.leftTranslate F b g.val)) =
      GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F (a⁻¹ * b) g.val)
  simp only [GlobalBruhat.leftTranslate_apply, mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]

/-- The correction in the compressed Fourier transition is an idele of
the enlarged stage, and its archimedean and old finite coordinates are one. -/
def sLocalFourierTransitionIdele (T : Finset (Place F)) : (SAdeles F T)ˣ :=
  Units.map (sAdelesProjection F T).toMonoidHom
    ((sLocalCodifferentTailIdele F T)⁻¹ * sLocalCodifferentTailIdele F S)

theorem sLocalFourierTransitionIdele_embed {T : Finset (Place F)} (hST : S ⊆ T) :
    (sLocalEmbed F T (sLocalFourierTransitionIdele F S T)).val =
      (sLocalCodifferentTailIdele F T)⁻¹ * sLocalCodifferentTailIdele F S := by
  let a := sLocalCodifferentTailIdele F T
  let b := sLocalCodifferentTailIdele F S
  let u := sLocalFourierTransitionIdele F S T
  apply Units.ext
  apply Prod.ext
  · rw [sLocalEmbed_arch]
    rfl
  · apply RestrictedProduct.ext
    intro v
    change (sLocalEmbed F T u).val.val.2 v = (a⁻¹ * b).val.2 v
    by_cases hv : v ∈ T
    · rw [sLocalEmbed_finite F T u ⟨v, hv⟩]
      rfl
    · rw [sLocalEmbed_outside_one F T u v hv]
      have hab (g : Idele F) : (g⁻¹).val.2 v = (g.val.2 v)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        exact congrArg (fun x : A F ↦ x.2 v) g.val_inv
      change 1 = (a⁻¹).val.2 v * b.val.2 v
      rw [hab, sLocalCodifferentTailIdele_finite, sLocalCodifferentTailIdele_finite, ite_eq_right hv,
        ite_eq_right (fun h ↦ hv (hST h)), inv_mul_cancel₀ (codifferentFactor F v).ne_zero]

theorem sLocalFourierCompression_transition {T : Finset (Place F)} (hST : S ⊆ T) (f : E F S) :
    sLocalFourierCompression F T (sLocalBruhatTransition F hST f) =
      sLocalBruhatLeftTranslate F T (sLocalFourierTransitionIdele F S T)
        (sLocalBruhatTransition F hST (sLocalFourierCompression F S f)) := by
  apply Subtype.ext
  change _ = GlobalBruhat.leftTranslate F (sLocalEmbed F T (sLocalFourierTransitionIdele F S T)).val
    (sLocalFourierCompression F S f).val
  rw [sLocalFourierTransitionIdele_embed F S hST]
  exact sLocalFourierCompression_transition_global F S hST f

theorem sLocalFourierCompression_double_global (f : E F S) :
    GlobalBruhat.fourier F (GlobalBruhat.fourier F f.val) =
      (ideleNorm F (sLocalCodifferentTailIdele F S) : ℂ) •
        (sLocalFourierCompression F S (sLocalFourierCompression F S f)).val := by
  rw [sLocalFourier_eq_tailTranslate F S f, globalBruhat_fourier_leftTranslate,
    sLocalFourier_eq_tailTranslate F S (sLocalFourierCompression F S f),
    globalBruhat_leftTranslate_inverse]

/-- Compression exchanges the two evaluation moments with the scalar
from the omitted codifferent in its second coordinate. -/
theorem sLocalFourierCompression_polarEvaluation (f : E F S) :
    GlobalBruhat.polarEvaluation F (sLocalFourierCompression F S f).val =
      ((GlobalBruhat.polarEvaluation F f.val).2,
        (ideleNorm F (sLocalCodifferentTailIdele F S) : ℂ)⁻¹ *
          (GlobalBruhat.polarEvaluation F f.val).1) := by
  let C := sLocalFourierCompression F S
  let A : ℂ := ideleNorm F (sLocalCodifferentTailIdele F S)
  let ev := GlobalBruhat.evaluation F 0
  have he (g : E F S) : ev (C g).val = ev (GlobalBruhat.fourier F g.val) := by
    have h := congrArg ev (sLocalFourier_eq_tailTranslate F S g)
    change _ = GlobalBruhat.evaluation F 0
      (GlobalBruhat.leftTranslate F (sLocalCodifferentTailIdele F S) (C g).val) at h
    rw [GlobalBruhat.leftTranslate_apply, mul_zero] at h
    exact h.symm
  have hA : A ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos F _).ne'
  have h := (adelicTheta_fourier_fourier F f.val).1
  change ev (GlobalBruhat.fourier F (GlobalBruhat.fourier F f.val)) = ev f.val at h
  rw [sLocalFourierCompression_double_global, map_smul, smul_eq_mul, he (C f)] at h
  refine Prod.ext (he f) ?_
  change ev (GlobalBruhat.fourier F (C f).val) = A⁻¹ * ev f.val
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]

theorem sLocalFourierCompression_polarEvaluation_eq_zero_iff (f : E F S) :
    GlobalBruhat.polarEvaluation F (sLocalFourierCompression F S f).val = 0 ↔
      GlobalBruhat.polarEvaluation F f.val = 0 := by
  rw [sLocalFourierCompression_polarEvaluation]
  have h : (ideleNorm F (sLocalCodifferentTailIdele F S) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ideleNorm_pos F _).ne'
  change (_, _) = ((0 : ℂ), (0 : ℂ)) ↔
    GlobalBruhat.polarEvaluation F f.val = ((0 : ℂ), (0 : ℂ))
  rw [Prod.mk.injEq, mul_eq_zero, inv_eq_zero, or_iff_right h, Prod.ext_iff]
  exact and_comm

/-- The compressed S-local Fourier transform squares to the inverse
omitted codifferent modulus on ordinary theta. -/
theorem sLocalFourierCompression_double_theta (f : E F S) :
    (ideleNorm F (sLocalCodifferentTailIdele F S) : ℂ) •
      sLocalThetaOperator F S (sLocalFourierCompression F S (sLocalFourierCompression F S f)) =
      sLocalThetaOperator F S f := by
  let a : ℂ := ideleNorm F (sLocalCodifferentTailIdele F S)
  let z := sLocalFourierCompression F S (sLocalFourierCompression F S f)
  have h := (adelicTheta_fourier_fourier F f.val).2
  change globalThetaOperator F (GlobalBruhat.fourier F (GlobalBruhat.fourier F f.val)) =
    globalThetaOperator F f.val at h
  rw [sLocalFourierCompression_double_global] at h
  change globalThetaOperator F (a • z.val) = globalThetaOperator F f.val at h
  have he : globalThetaOperator F (a • z.val - f.val) = 0 := by
    rw [map_sub, h, sub_self]
  have hz : a • z - f ∈ (sLocalThetaOperator F S).ker :=
    (sLocalThetaKernel_iff_global F S _).mpr (LinearMap.mem_ker.mpr he)
  have he' := LinearMap.mem_ker.mp hz
  rw [map_sub, map_smul, sub_eq_zero] at he'
  exact he'

/-- The true S-local Fourier integral descends to the ordinary theta
quotient at every finite stage. -/
def sLocalThetaCompressedFourier : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S := by
  let M := (sLocalThetaOperator F S).ker
  let N := (globalThetaOperator F).ker
  let C := sLocalFourierCompression F S
  let γ := sLocalCodifferentTailIdele F S
  refine M.liftQL (M.mkQL.comp C) ?_
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero M).mpr
  apply (sLocalThetaKernel_iff_global F S (C f)).mpr
  have hF : (Submodule.Quotient.mk (GlobalBruhat.fourier F f.val) : GlobalThetaQuotient F) = 0 := by
    rw [← globalThetaFourier_mk,
      (Submodule.Quotient.mk_eq_zero N).mpr ((sLocalThetaKernel_iff_global F S f).mp hf), map_zero]
  have hG := LinearMap.mem_ker.mp ((Submodule.Quotient.mk_eq_zero N).mp hF)
  change globalThetaOperator F (GlobalBruhat.fourier F f.val) = 0 at hG
  rw [sLocalFourier_eq_tailTranslate] at hG
  refine LinearMap.mem_ker.mpr (funext fun q ↦ ?_)
  have he := congrFun hG (ideleClassMap F γ * q)
  rw [globalThetaOperator_leftTranslate, inv_mul_cancel_left] at he
  exact he

@[simp] theorem sLocalThetaCompressedFourier_mk (f : E F S) :
    sLocalThetaCompressedFourier F S (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalFourierCompression F S f) := rfl

theorem sLocalThetaCompressedFourier_double (q : SLocalThetaQuotient F S) :
    (ideleNorm F (sLocalCodifferentTailIdele F S) : ℂ) •
      sLocalThetaCompressedFourier F S (sLocalThetaCompressedFourier F S q) = q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [sLocalThetaCompressedFourier_mk, sLocalThetaCompressedFourier_mk]
  let M := (sLocalThetaOperator F S).ker
  let z := sLocalFourierCompression F S (sLocalFourierCompression F S f)
  let a : ℂ := ideleNorm F (sLocalCodifferentTailIdele F S)
  change M.mkQ (a • z) = M.mkQ f
  apply (Submodule.Quotient.eq M).mpr
  apply LinearMap.mem_ker.mpr
  rw [map_sub, map_smul, sLocalFourierCompression_double_theta, sub_self]

/-- Its inverse is the same S-local integral multiplied by the omitted
codifferent modulus. -/
def sLocalThetaCompressedFourierEquiv : SLocalThetaQuotient F S ≃L[ℂ] SLocalThetaQuotient F S := by
  let C := sLocalThetaCompressedFourier F S
  let a : ℂ := ideleNorm F (sLocalCodifferentTailIdele F S)
  refine ContinuousLinearEquiv.equivOfInverse C (a • C) ?_ ?_
  · exact sLocalThetaCompressedFourier_double F S
  · intro q
    change C (a • C q) = q
    rw [map_smul]
    exact sLocalThetaCompressedFourier_double F S q

end

end Masullo
