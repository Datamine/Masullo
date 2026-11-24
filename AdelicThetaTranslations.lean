import ThetaMellinQuotients
import LocallyConstantTests
import SchwartzDilationContinuity

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Arch := mixedEmbedding.mixedSpace F
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

def archDilation (g : Idele F) : Arch F ≃L[ℝ] Arch F :=
  let u := Units.map (mixedArch (F := F)).toMonoidHom g⁻¹
  let e : Arch F ≃ₗ[ℝ] Arch F :=
    { u.mulLeft with
      map_add' := mul_add _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  e.toContinuousLinearEquiv

private def finiteDilation (g : Idele F) : FinAdeles F ≃ₜ FinAdeles F :=
  (ContinuousAddEquiv.mulLeft (MulEquiv.prodUnits g⁻¹).2).toHomeomorph

private def finiteBruhatTranslate (g : Idele F) (ψ : FiniteBruhat F) : FiniteBruhat F :=
  let e := finiteDilation F g
  ⟨LocallyConstant.comap ⟨e, e.continuous⟩ ψ.toLocallyConstant,
    ψ.compactSupport.comp_homeomorph e⟩

private def adelicTranslateFun (g : Idele F) : (Adeles F → ℂ) →ₗ[ℂ] (Adeles F → ℂ) where
  toFun f a := f (g⁻¹.val * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem adelicTranslateFun_pure (g : Idele F) (ψ : FiniteBruhat F)
    (φ : 𝓢(Arch F, ℂ)) :
    adelicTranslateFun F g (bruhatTensor F φ ψ) =
      bruhatTensor F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archDilation F g) φ)
        (finiteBruhatTranslate F g ψ) := by
  funext a
  change φ (mixedArch (F := F) (g⁻¹.val * a)) * ψ.toLocallyConstant ((g⁻¹.val).2 * a.2) =
    φ (mixedArch (F := F) g⁻¹.val * mixedArch (F := F) a) * ψ.toLocallyConstant ((g⁻¹.val).2 * a.2)
  rw [map_mul]

private theorem bruhatTranslate_mem (g : Idele F) {f : Adeles F → ℂ}
    (hf : f ∈ bruhatSubmodule F) : adelicTranslateFun F g f ∈ bruhatSubmodule F := by
  let T := adelicTranslateFun F g
  apply Submodule.span_induction (p := fun h _ => T h ∈ bruhatSubmodule F) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    change adelicTranslateFun F g (bruhatTensor F φ ψ) ∈ bruhatSubmodule F
    rw [adelicTranslateFun_pure]
    exact bruhatTensor_mem F _ _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro _ _ _ _ h j
    rw [map_add]
    exact Submodule.add_mem _ h j
  · intro _ _ _ h
    rw [map_smul]
    exact Submodule.smul_mem _ _ h

private def bruhatTranslate (g : Idele F) : GlobalBruhat F →ₗ[ℂ] GlobalBruhat F :=
  let T := adelicTranslateFun F g
  let u := GlobalBruhat.algebraicEquiv F
  let A := (T.domRestrict (bruhatSubmodule F)).codRestrict (bruhatSubmodule F)
    (fun f => bruhatTranslate_mem F g f.property)
  u.symm.toLinearMap.comp (A.comp u.toLinearMap)

private theorem bruhatTranslate_pure (g : Idele F) (ψ : FiniteBruhat F)
    (φ : 𝓢(Arch F, ℂ)) :
    bruhatTranslate F g (GlobalBruhat.pure F ψ φ) =
      GlobalBruhat.pure F (finiteBruhatTranslate F g ψ)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archDilation F g) φ) := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  exact adelicTranslateFun_pure F g ψ φ

/-- Left translation by an idele on the actual adelic test space. -/
def GlobalBruhat.leftTranslate (g : Idele F) : GlobalBruhat F →L[ℂ] GlobalBruhat F where
  toLinearMap := bruhatTranslate F g
  cont := by
    apply GlobalBruhat.continuous_of_pure F (PolynormableSpace.withSeminorms ℂ (GlobalBruhat F))
    intro ψ
    let A := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (archDilation F g)
    simp_rw [bruhatTranslate_pure]
    exact (GlobalBruhat.pure_continuous F _).comp A.continuous

private theorem archDilation_continuous (φ : 𝓢(Arch F, ℂ)) :
    Continuous (fun g : Idele F ↦
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archDilation F g) φ) := by
  have h : Continuous (fun g : Idele F ↦ mixedArch g.val) :=
    ((infiniteAdele_toMixed_continuous F).comp continuous_fst).comp Units.continuous_val
  let L := ContinuousLinearMap.mul ℝ (Arch F)
  apply continuous_schwartz_linearPullback
  · exact (L.continuous.comp (h.comp continuous_inv)).congr fun g ↦ by
      exact ContinuousLinearMap.ext fun _ ↦ rfl
  · exact (L.continuous.comp h).congr fun g ↦ by
      exact ContinuousLinearMap.ext fun _ ↦ rfl

private theorem finiteBruhatTranslate_locallyConstant (ψ : FiniteBruhat F) :
    IsLocallyConstant (fun g : Idele F ↦ finiteBruhatTranslate F g ψ) := by
  letI : T2Space (FinAdeles F) :=
    T2Space.of_injective_continuous (f := fun a : FinAdeles F ↦ (a :
      (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F))
      DFunLike.coe_injective RestrictedProduct.continuous_coe
  let P (g : Idele F) : (FinAdeles F)ˣ := (MulEquiv.prodUnits g).2
  have hval : Continuous (fun g : Idele F ↦ (P g).val) :=
    continuous_snd.comp Units.continuous_val
  have hP : Continuous P := Units.continuous_iff.mpr ⟨hval, hval.comp continuous_inv⟩
  let f : LocallyConstantTestSpace (FinAdeles F) :=
    ⟨ψ.toLocallyConstant, ψ.toLocallyConstant.isLocallyConstant, ψ.compactSupport⟩
  have he := (locallyConstantTestTranslate_orbit_locallyConstant (FinAdeles F)
    (G := (FinAdeles F)ˣ) f).comp_continuous hP
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp he g] with h hh
  have htest : (finiteBruhatTranslate F h ψ).toLocallyConstant =
      (finiteBruhatTranslate F g ψ).toLocallyConstant := by
    apply LocallyConstant.ext
    intro x
    exact congrFun (congrArg Subtype.val hh) x
  have hinj : Injective (FiniteBruhat.toLocallyConstant (F := F)) := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    change v = w at h
    subst w
    rfl
  exact hinj htest

/-- Translation of a fixed adelic Schwartz–Bruhat test is continuous in the idele. -/
theorem GlobalBruhat.continuous_leftTranslate_orbit (f : GlobalBruhat F) :
    Continuous (fun g : Idele F ↦ GlobalBruhat.leftTranslate F g f) := by
  have hpure (φ : 𝓢(Arch F, ℂ)) (ψ : FiniteBruhat F) :
      Continuous (fun g : Idele F ↦ GlobalBruhat.leftTranslate F g (GlobalBruhat.pure F ψ φ)) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    let A (h : Idele F) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archDilation F h) φ
    let u := GlobalBruhat.pure F (finiteBruhatTranslate F g ψ)
    have hc : Tendsto (fun h ↦ u (A h)) (𝓝 g) (𝓝 (u (A g))) :=
      ((GlobalBruhat.pure_continuous F _).comp (archDilation_continuous F φ)).continuousAt
    change Tendsto (fun h ↦ bruhatTranslate F h (GlobalBruhat.pure F ψ φ)) (𝓝 g)
      (𝓝 (bruhatTranslate F g (GlobalBruhat.pure F ψ φ)))
    rw [bruhatTranslate_pure F g]
    refine hc.congr' ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp
      (finiteBruhatTranslate_locallyConstant F ψ) g] with h hh
    simp only [bruhatTranslate_pure, hh, A, u]
  let e := GlobalBruhat.algebraicEquiv F
  have h : ∀ (f : Adeles F → ℂ) (hf : f ∈ bruhatSubmodule F),
      Continuous (fun g : Idele F ↦ GlobalBruhat.leftTranslate F g (e.symm ⟨f, hf⟩)) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem a ha =>
      rcases ha with ⟨φ, ψ, rfl⟩
      exact hpure φ ψ
    | zero =>
      change Continuous (fun g : Idele F ↦ GlobalBruhat.leftTranslate F g (e.symm 0))
      simpa only [map_zero] using
        (continuous_const : Continuous (fun _ : Idele F ↦ (0 : GlobalBruhat F)))
    | add a b ha hb h₁ h₂ =>
      have he : (⟨a + b, _⟩ : bruhatSubmodule F) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      exact (h₁.add h₂).congr fun g ↦ by
        change GlobalBruhat.leftTranslate F g (e.symm ⟨a, ha⟩) +
          GlobalBruhat.leftTranslate F g (e.symm ⟨b, hb⟩) = _
        rw [he, map_add, map_add]
    | smul c a ha h₁ =>
      have he : (⟨c • a, _⟩ : bruhatSubmodule F) = c • ⟨a, ha⟩ := rfl
      exact (h₁.const_smul c).congr fun g ↦ by
        change c • GlobalBruhat.leftTranslate F g (e.symm ⟨a, ha⟩) = _
        rw [he, map_smul, map_smul]
  have hf := h (e f).val (e f).property
  change Continuous (fun g : Idele F ↦ GlobalBruhat.leftTranslate F g (e.symm (e f))) at hf
  simpa only [LinearEquiv.symm_apply_apply] using hf

@[simp] theorem GlobalBruhat.leftTranslate_apply (g : Idele F) (f : GlobalBruhat F)
    (a : Adeles F) : GlobalBruhat.evaluation F a (GlobalBruhat.leftTranslate F g f) =
    GlobalBruhat.evaluation F (g⁻¹.val * a) f := rfl

theorem globalThetaOperator_leftTranslate (g : Idele F) (f : GlobalBruhat F)
    (q : IdeleClass F) : globalThetaOperator F (GlobalBruhat.leftTranslate F g f) q =
      globalThetaOperator F f ((ideleClassMap F g)⁻¹ * q) := by
  obtain ⟨a, rfl⟩ := ideleClassMap_surjective F q
  rw [← map_inv, ← map_mul]
  change thetaOnIdeles F (GlobalBruhat.algebraicEquiv F (GlobalBruhat.leftTranslate F g f)).val a =
    thetaOnIdeles F (GlobalBruhat.algebraicEquiv F f).val (g⁻¹ * a)
  unfold thetaOnIdeles thetaSummand
  congr 1
  funext ξ
  change GlobalBruhat.evaluation F _ (GlobalBruhat.leftTranslate F g f) =
    GlobalBruhat.evaluation F _ f
  rw [GlobalBruhat.leftTranslate_apply]
  congr 1
  simp only [Units.val_mul]
  ac_rfl

/-- Translation on the global theta quotient factors through idele classes. -/
def globalThetaTranslateIdeles (g : Idele F) : GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F := by
  let P := (globalThetaOperator F).ker
  refine P.liftQL (P.mkQL.comp (GlobalBruhat.leftTranslate F g)) ?_
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero P).mpr
  apply LinearMap.mem_ker.mpr
  funext q
  change globalThetaOperator F (GlobalBruhat.leftTranslate F g f) q = 0
  rw [globalThetaOperator_leftTranslate]
  exact congrFun (LinearMap.mem_ker.mp hf) _

@[simp] theorem globalThetaTranslateIdeles_mk (g : Idele F) (f : GlobalBruhat F) :
    globalThetaTranslateIdeles F g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (GlobalBruhat.leftTranslate F g f) := rfl

theorem globalThetaTranslateIdeles_eq_of_class_eq {g h : Idele F}
    (he : ideleClassMap F g = ideleClassMap F h) :
    globalThetaTranslateIdeles F g = globalThetaTranslateIdeles F h := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [globalThetaTranslateIdeles_mk, globalThetaTranslateIdeles_mk, Submodule.Quotient.eq]
  apply LinearMap.mem_ker.mpr
  rw [map_sub, sub_eq_zero]
  funext r
  rw [globalThetaOperator_leftTranslate, globalThetaOperator_leftTranslate, he]

/-- Left translation on the theta quotient by an idele class. -/
def globalThetaTranslate (q : IdeleClass F) : GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F :=
  Quotient.lift (globalThetaTranslateIdeles F)
    (fun _ _ h => globalThetaTranslateIdeles_eq_of_class_eq F (Quotient.sound h)) q

@[simp] theorem globalThetaTranslate_class (g : Idele F) :
    globalThetaTranslate F (ideleClassMap F g) = globalThetaTranslateIdeles F g := rfl

theorem globalThetaTranslate_one :
    globalThetaTranslate F 1 = ContinuousLinearMap.id ℂ (GlobalThetaQuotient F) := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change globalThetaTranslateIdeles F 1 (Submodule.Quotient.mk f) = Submodule.Quotient.mk f
  rw [globalThetaTranslateIdeles_mk]
  congr 1
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  change GlobalBruhat.evaluation F a (GlobalBruhat.leftTranslate F 1 f) = _
  rw [GlobalBruhat.leftTranslate_apply]
  simp [GlobalBruhat.evaluation]

theorem globalThetaTranslate_mul (r s : IdeleClass F) :
    globalThetaTranslate F (r * s) = (globalThetaTranslate F r).comp (globalThetaTranslate F s) := by
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F r
  obtain ⟨h, rfl⟩ := ideleClassMap_surjective F s
  rw [← map_mul, globalThetaTranslate_class, globalThetaTranslate_class, globalThetaTranslate_class]
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [ContinuousLinearMap.comp_apply, globalThetaTranslateIdeles_mk, globalThetaTranslateIdeles_mk,
    globalThetaTranslateIdeles_mk]
  congr 1
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  change GlobalBruhat.evaluation F a (GlobalBruhat.leftTranslate F (g * h) f) =
    GlobalBruhat.evaluation F a (GlobalBruhat.leftTranslate F g (GlobalBruhat.leftTranslate F h f))
  simp only [GlobalBruhat.leftTranslate_apply, mul_inv_rev, Units.val_mul, mul_assoc]


private abbrev K := normOneIdeleClass F
local instance adelicThetaTranslations_idelesMeasurable : MeasurableSpace (Idele F) := borel _
local instance adelicThetaTranslations_idelesBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance adelicThetaTranslations_normOneMeasurable : MeasurableSpace (K F) := borel _
local instance adelicThetaTranslations_classMeasurable : MeasurableSpace (IdeleClass F) := borel _

/-- Haar substitution gives dilation covariance in the defining zeta integral. -/
theorem idelicZetaIntegral_leftTranslate (μ : Measure (Idele F)) [μ.IsHaarMeasure]
    (g : Idele F) (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (s : ℂ) :
    idelicZetaIntegral F μ (GlobalBruhat.algebraicEquiv F (GlobalBruhat.leftTranslate F g f)).val χ s =
      (ideleNormTwist F χ s (ideleClassMap F g) : ℂ) *
        idelicZetaIntegral F μ (GlobalBruhat.algebraicEquiv F f).val χ s := by
  let w (a : Idele F) := (ideleNormTwist F χ s (ideleClassMap F a) : ℂ)
  let u := GlobalBruhat.algebraicEquiv F
  let A (a : Idele F) := (u (GlobalBruhat.leftTranslate F g f)).val a.val * w a
  change (∫ a, A a ∂μ) = w g * ∫ a, (u f).val a.val * w a ∂μ
  rw [← integral_mul_left_eq_self A g, ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun a => ?_)
  change GlobalBruhat.evaluation F (g * a).val (GlobalBruhat.leftTranslate F g f) * w (g * a) = _
  rw [GlobalBruhat.leftTranslate_apply]
  have harg : g⁻¹.val * (g * a).val = a.val := by
    rw [Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hw : w (g * a) = w g * w a := by
    simp only [w, map_mul, Units.val_mul]
  rw [harg, hw]
  change (u f).val a.val * (w g * w a) = _
  ring

/-- Global Mellin covariance on every character component away from the
two possible poles of the trivial character in the canonical norm-twist coordinates. -/
theorem globalZetaContinued_leftTranslate (μ : Measure (Idele F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (g : Idele F) (f : GlobalBruhat F) (ω : PontryaginDual (K F))
    (s : ℂ) (hreg : ω = 1 → s ≠ 0 ∧ s ≠ 1) :
    let χ := compactIdeleClassCharacter F ω
    globalZetaContinued F ν (GlobalBruhat.leftTranslate F g f) χ 0 s =
      (ideleNormTwist F χ s (ideleClassMap F g) : ℂ) * globalZetaContinued F ν f χ 0 s := by
  let χ := compactIdeleClassCharacter F ω
  have hχ := compactIdeleClassCharacter_unitary F ω
  let q := ideleClassMap F g
  let w (z : ℂ) := (ideleNormTwist F χ z q : ℂ)
  have hw (z : ℂ) : AnalyticAt ℂ w z :=
    analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).cexp)
  let T := globalZetaContinued F ν (GlobalBruhat.leftTranslate F g f) χ 0
  let Z := globalZetaContinued F ν f χ 0
  let D := fun z => T z - w z * Z z
  have hhalf (z : ℂ) (hz : 1 < z.re) : D z = 0 := by
    have hrad (t : ℝ) : (χ (ideleClassExpSection F (Multiplicative.ofAdd t)) : ℂ) =
        Complex.exp ((0 : ℂ) * (t : ℂ)) := by
      simp [χ]
    have hId (u : GlobalBruhat F) := globalZetaContinued_eq_idelic F μ ν hν u χ hχ
      Complex.zero_re hrad z hz
    dsimp only [D, T, Z]
    rw [hId, hId, idelicZetaIntegral_leftTranslate]
    exact sub_self _
  have hT : MeromorphicOn T univ := globalZetaContinued_meromorphic F ν _ χ hχ 0
  have hZ : MeromorphicOn Z univ := globalZetaContinued_meromorphic F ν _ χ hχ 0
  have hD : MeromorphicOn D univ := fun z hz =>
    (hT z hz).sub ((hw z).meromorphicAt.mul (hZ z hz))
  have htop : meromorphicOrderAt D 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hU : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with z hz
    exact hhalf z hz
  have hs : meromorphicOrderAt D s = ⊤ := by
    by_contra h
    exact (hD.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ s) (mem_univ (2 : ℂ)) h) htop
  have hA (v : GlobalBruhat F) : AnalyticAt ℂ (globalZetaContinued F ν v χ 0) s := by
    by_cases hω : ω = 1
    · exact globalZetaContinued_analyticAt F ν v χ hχ 0 s (by simpa using (hreg hω).1)
        (by simpa using sub_ne_zero.mpr (hreg hω).2)
    · apply globalZetaContinued_entire_of_polar_zero F ν v χ hχ 0 _ s (mem_univ _)
      exact Or.inl ((compactIdeleClassCharacter_integral F ν ω).trans (ite_eq_right hω))
  have hC : ContinuousAt D s := ((hA _).sub ((hw s).mul (hA f))).continuousAt
  have hn : D =ᶠ[𝓝[≠] s] (fun _ => 0) := meromorphicOrderAt_eq_top_iff.mp hs
  exact sub_eq_zero.mp ((hC.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp hn).eq_of_nhds


end

end Masullo
