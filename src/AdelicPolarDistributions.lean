import AdelicThetaTranslations
import Mathlib.Topology.Maps.Strict.Module

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
local instance polarDistributions_normOneMeasurable : MeasurableSpace (K F) := borel _
local instance polarDistributions_normOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance polarDistributions_adeleMeasurable : MeasurableSpace (Adeles F) := borel _
local instance polarDistributions_adeleBorel : BorelSpace (Adeles F) := ⟨rfl⟩

/-- Even the trivial-character homogeneous kernel is contained in both
zero-evaluation kernels. The two punctured residue limits detect them separately. -/
theorem globalPolarEvaluation_eq_zero_of_trivialHomogeneous
    (ν : Measure (K F)) [ν.IsHaarMeasure] (f : GlobalBruhat F)
    (h : ∀ q, adelicHomogeneousTheta F ν 1 (GlobalBruhat.algebraicEquiv F f).val q = 0) :
    GlobalBruhat.polarEvaluation F f = 0 := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    exact_mod_cast (measureReal_univ_pos (μ := ν)).ne'
  have hzero := (adelicHomogeneousTheta_zero_iff_continuedZeta F ν f 1).mp h
  have hres := globalZetaContinued_trivial_residues F ν f
  have h₀ : (ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f).val 0 = 0 := by
    have ht := hres.1
    simp only [hzero, mul_zero] at ht
    exact neg_eq_zero.mp (tendsto_nhds_unique ht tendsto_const_nhds)
  have h₁ : (ν.real univ : ℂ) *
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0 := by
    have ht := hres.2
    simp only [hzero, mul_zero] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  exact Prod.ext ((mul_eq_zero.mp h₀).resolve_left hmass) ((mul_eq_zero.mp h₁).resolve_left hmass)

theorem globalThetaKernel_le_polarKernel :
    (globalThetaOperator F).ker ≤ (GlobalBruhat.polarEvaluation F).ker := by
  intro f hf
  apply LinearMap.mem_ker.mpr
  letI : T1Space (IdeleClass F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  letI : T2Space (K F) := inferInstance
  letI := normOneIdeleClass_compact F
  let ν : Measure (K F) := Measure.haar
  letI : ν.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure (K F)).IsHaarMeasure
  apply globalPolarEvaluation_eq_zero_of_trivialHomogeneous F ν f
  exact (adelicTheta_zero_iff_homogeneous_zero F ν f).mp
    (fun q => congrFun (LinearMap.mem_ker.mp hf) q) 1

/-- Both evaluation functionals descend continuously to the global theta quotient. -/
def globalThetaPolarEvaluation : GlobalThetaQuotient F →L[ℂ] ℂ × ℂ :=
  (globalThetaOperator F).ker.liftQL (GlobalBruhat.polarEvaluation F) (globalThetaKernel_le_polarKernel F)

@[simp] theorem globalThetaPolarEvaluation_mk (f : GlobalBruhat F) :
    globalThetaPolarEvaluation F (Submodule.Quotient.mk f) = GlobalBruhat.polarEvaluation F f := rfl

theorem globalThetaPolarEvaluation_unique (T : GlobalThetaQuotient F →L[ℂ] ℂ × ℂ)
    (hT : ∀ f : GlobalBruhat F, T (Submodule.Quotient.mk f) = GlobalBruhat.polarEvaluation F f) :
    T = globalThetaPolarEvaluation F := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact hT f

theorem globalThetaPolarEvaluation_surjective : Surjective (globalThetaPolarEvaluation F) := by
  intro v
  obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F v
  exact ⟨Submodule.Quotient.mk f, hf⟩

/-- The two punctured limits identify the descended evaluations with the
normalized global zeta residues in the trivial-character chart. -/
theorem globalThetaPolarEvaluation_residue_limits (ν : Measure (K F)) [ν.IsHaarMeasure]
    (q : GlobalThetaQuotient F) :
    let χ := (1 : PontryaginDual (K F))
    Tendsto (fun z => z * globalQuotientContinuedMellin F ν q (χ, z)) (𝓝[≠] (0 : ℂ))
      (𝓝 (-((ν.real univ : ℂ) * (globalThetaPolarEvaluation F q).1))) ∧
    Tendsto (fun z => (z - 1) * globalQuotientContinuedMellin F ν q (χ, z)) (𝓝[≠] (1 : ℂ))
      (𝓝 ((ν.real univ : ℂ) * (globalThetaPolarEvaluation F q).2)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let Z := fun z : ℂ => globalContinuedMellinEval F ν 1 z f
  change Tendsto (fun z => z * Z z) (𝓝[≠] 0)
        (𝓝 (-((ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f).val 0))) ∧
    Tendsto (fun z => (z - 1) * Z z) (𝓝[≠] 1)
        (𝓝 ((ν.real univ : ℂ) *
          (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0))
  simpa only [Z, globalContinuedMellinEval_apply] using
    globalZetaContinued_trivial_residues F ν f

/-- The two values are characterized by their normalized residue limits,
so this normalization is independent of the Haar measure chosen in continuation. -/
theorem globalThetaPolarEvaluation_eq_of_residue_limits (ν : Measure (K F)) [ν.IsHaarMeasure]
    (q : GlobalThetaQuotient F) (a b : ℂ)
    (ha : Tendsto (fun z => z * globalQuotientContinuedMellin F ν q (1, z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-((ν.real univ : ℂ) * a))))
    (hb : Tendsto (fun z => (z - 1) * globalQuotientContinuedMellin F ν q (1, z))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((ν.real univ : ℂ) * b))) :
    globalThetaPolarEvaluation F q = (a, b) := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  have hmass : (ν.real univ : ℂ) ≠ 0 := by
    exact_mod_cast (measureReal_univ_pos (μ := ν)).ne'
  have h := globalThetaPolarEvaluation_residue_limits F ν q
  apply Prod.ext
  · exact mul_left_cancel₀ hmass (neg_injective (tendsto_nhds_unique h.1 ha))
  · exact mul_left_cancel₀ hmass (tendsto_nhds_unique h.2 hb)

/-- On the test space evaluation has weight one, and Fourier evaluation
has weight the idele norm. -/
theorem polarEvaluation_leftTranslate (g : Idele F) (f : GlobalBruhat F) :
    GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F g f) =
      ((GlobalBruhat.polarEvaluation F f).1, ideleNorm F g • (GlobalBruhat.polarEvaluation F f).2) := by
  apply Prod.ext
  · change GlobalBruhat.evaluation F 0 (GlobalBruhat.leftTranslate F g f) = GlobalBruhat.evaluation F 0 f
    rw [GlobalBruhat.leftTranslate_apply, mul_zero]
  · change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F
        (GlobalBruhat.leftTranslate F g f))).val 0 =
      ideleNorm F g • (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0
    rw [GlobalBruhat.fourier_apply, GlobalBruhat.fourier_apply]
    let μ := adelicHaarUnitDomain F
    letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
    let u := GlobalBruhat.algebraicEquiv F f
    have h := adelicFourier_mul_argument F μ (standardAdelicCharacter F)
      (standardAdelicCharacter_continuous F) u.val (bruhat_continuous F u.property).measurable g⁻¹ 0
    rw [map_inv, inv_inv, mul_zero] at h
    exact h

/-- The adjoint eigenvalues on the theta quotient are one and the norm. -/
theorem globalThetaPolarEvaluation_translate (g : IdeleClass F) (q : GlobalThetaQuotient F) :
    globalThetaPolarEvaluation F (globalThetaTranslate F g q) =
      ((globalThetaPolarEvaluation F q).1, ideleClassNorm F g • (globalThetaPolarEvaluation F q).2) := by
  obtain ⟨a, rfl⟩ := ideleClassMap_surjective F g
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [globalThetaTranslate_class, globalThetaTranslateIdeles_mk, globalThetaPolarEvaluation_mk,
    globalThetaPolarEvaluation_mk, ideleClassNorm_mk]
  exact polarEvaluation_leftTranslate F a f

/-- Each polar functional vanishes on every nontrivial norm-one isotype
of the actual quotient under the left-translation convention. -/
theorem globalThetaPolarEvaluation_zero_of_isotype (ω : PontryaginDual (K F))
    (hω : ω ≠ 1) (q : GlobalThetaQuotient F)
    (hq : ∀ k : K F, globalThetaTranslate F k.val q = ((ω k : Circle) : ℂ) • q) :
    globalThetaPolarEvaluation F q = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : K F, ω k ≠ 1 := by
    by_contra! h
    apply hω
    ext k
    exact congrArg Subtype.val (h k)
  have hk' : ((ω k : Circle) : ℂ) ≠ 1 := fun he => hk (Circle.coe_injective (by simpa using he))
  have he := globalThetaPolarEvaluation_translate F k.val q
  have hn : ideleClassNorm F k.val = 1 := k.property
  rw [hn, one_smul, hq k, map_smul] at he
  have hz : (((ω k : Circle) : ℂ) - 1) • globalThetaPolarEvaluation F q = 0 := by
    rw [sub_smul, he, one_smul]
    exact sub_self _
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hk')


/-- The homogeneous orbit sum as a linear map on global tests. -/
def globalHomogeneousThetaOperator (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) :
    GlobalBruhat F →ₗ[ℂ] (IdeleClass F → ℂ) where
  toFun f := adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val
  map_add' f h := by
    letI : T1Space (IdeleClass F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
    letI : T2Space (K F) := inferInstance
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    funext q
    let w (u : GlobalBruhat F) (k : K F) :=
      ((ω k : Circle) : ℂ) * globalThetaOperator F u (k.val * q)
    have hI (u : GlobalBruhat F) : Integrable (w u) ν := by
      apply Continuous.integrable_of_hasCompactSupport
      · have hθ : Continuous (globalThetaOperator F u) :=
          adelicTheta_continuous F (bruhat_theta_continuous_and_invariant
            (GlobalBruhat.algebraicEquiv F u).property).1
        have hk : Continuous (fun k : K F => k.val) := continuous_subtype_val
        exact (continuous_subtype_val.comp ω.continuous).mul (hθ.comp (hk.mul continuous_const))
      · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
    change ∫ k, w (f + h) k ∂ν = (∫ k, w f k ∂ν) + ∫ k, w h k ∂ν
    rw [← integral_add (hI f) (hI h)]
    apply integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [w, map_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext q
    change (∫ k : K F, ((ω k : Circle) : ℂ) * globalThetaOperator F (c • f) (k.val * q) ∂ν) =
      c * ∫ k : K F, ((ω k : Circle) : ℂ) * globalThetaOperator F f (k.val * q) ∂ν
    rw [← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun k => ?_)
    rw [map_smul]
    change _ * (c * _) = c * (_ * _)
    ring


theorem globalHomogeneousThetaOperator_translate (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) (k : K F) (g : Idele F) (hg : ideleClassMap F g = k.val)
    (f : GlobalBruhat F) :
    globalHomogeneousThetaOperator F ν ω (GlobalBruhat.leftTranslate F g f) =
      ((ω k : Circle) : ℂ) • globalHomogeneousThetaOperator F ν ω f := by
  funext q
  let u := GlobalBruhat.algebraicEquiv F f
  change adelicHomogeneousTheta F ν ω
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.leftTranslate F g f)).val q =
    ((ω k : Circle) : ℂ) * adelicHomogeneousTheta F ν ω u.val q
  calc
    _ = adelicHomogeneousTheta F ν ω u.val (k⁻¹.val * q) := by
      unfold adelicHomogeneousTheta
      apply integral_congr_ae (Eventually.of_forall fun a => ?_)
      change _ * globalThetaOperator F (GlobalBruhat.leftTranslate F g f) (a.val * q) =
        _ * globalThetaOperator F f (a.val * (k⁻¹.val * q))
      rw [globalThetaOperator_leftTranslate, hg]
      rw [show k.val⁻¹ * (a.val * q) = a.val * (k⁻¹.val * q) by
        change k.val⁻¹ * (a.val * q) = a.val * (k.val⁻¹ * q)
        exact mul_left_comm (k.val⁻¹ : IdeleClass F) (a.val : IdeleClass F) q]
    _ = _ := by
      rw [adelicHomogeneousTheta_translate]
      simp only [map_inv, Circle.coe_inv, inv_inv]

/-- For a nontrivial character, each polar functional takes a nonzero value
on a vector in the corresponding homogeneous kernel. -/
theorem globalPolarEvaluation_nonzero_in_homogeneousKernel
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) (hω : ω ≠ 1) :
    ∃ f ∈ (globalHomogeneousThetaOperator F ν ω).ker,
      (GlobalBruhat.polarEvaluation F f).1 ≠ 0 ∧ (GlobalBruhat.polarEvaluation F f).2 ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k : K F, ω k ≠ 1 := by
    by_contra! h
    apply hω
    ext k
    exact congrArg Subtype.val (h k)
  let c : ℂ := (ω k : Circle)
  have hc : c ≠ 1 := fun he => hk (Circle.coe_injective (by simpa [c] using he))
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F k.val
  have hnorm : ideleNorm F g = 1 := by
    rw [← ideleClassNorm_mk, hg]
    exact k.property
  obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F (1, 1)
  refine ⟨GlobalBruhat.leftTranslate F g f - c • f, ?_, ?_⟩
  · apply LinearMap.mem_ker.mpr
    rw [map_sub, map_smul, globalHomogeneousThetaOperator_translate F ν ω k g hg, sub_self]
  · rw [map_sub, map_smul, polarEvaluation_leftTranslate, hnorm, hf]
    simpa using (sub_ne_zero.mpr (Ne.symm hc))

/-- The manuscript's space indexed by a character is a quotient. Each polar
functional factors through that quotient precisely at the trivial character. -/
theorem globalPolarEvaluation_factors_homogeneous_iff
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) :
    let P := (globalHomogeneousThetaOperator F ν ω).ker
    (∃ T : (GlobalBruhat F ⧸ P) →L[ℂ] ℂ × ℂ,
      ∀ f : GlobalBruhat F, T (Submodule.Quotient.mk f) = GlobalBruhat.polarEvaluation F f) ↔ ω = 1 := by
  let P := (globalHomogeneousThetaOperator F ν ω).ker
  constructor
  · rintro ⟨T, hT⟩
    by_contra hω
    obtain ⟨f, hf, h₀, _⟩ := globalPolarEvaluation_nonzero_in_homogeneousKernel F ν ω hω
    have he := hT f
    rw [(Submodule.Quotient.mk_eq_zero P).mpr hf, map_zero] at he
    exact h₀ (congrArg Prod.fst he.symm)
  · rintro rfl
    have hle : (globalHomogeneousThetaOperator F ν 1).ker ≤ (GlobalBruhat.polarEvaluation F).ker := by
      intro f hf
      apply LinearMap.mem_ker.mpr
      apply globalPolarEvaluation_eq_zero_of_trivialHomogeneous F ν f
      exact fun q => congrFun (LinearMap.mem_ker.mp hf) q
    exact ⟨Submodule.liftQL _ (GlobalBruhat.polarEvaluation F) hle, fun _ => rfl⟩

private theorem exists_globalPolarFree_lift_of_ne_one
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) (hω : ω ≠ 1) :
    let H := (globalHomogeneousThetaOperator F ν ω).ker
    let P := (GlobalBruhat.polarEvaluation F).ker
    ∃ L : GlobalBruhat F →L[ℂ] P, ∀ f, H.mkQ (L f).val = H.mkQ f := by
  intro H P
  let A := globalHomogeneousThetaOperator F ν ω
  obtain ⟨k, hk⟩ : ∃ k : K F, ω k ≠ 1 := by
    by_contra! h
    apply hω
    ext k
    exact congrArg Subtype.val (h k)
  let c : ℂ := (ω k : Circle)
  have hc : c ≠ 1 := fun e => hk (Circle.coe_injective (by simpa [c] using e))
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F k.val
  have hgN : ideleNorm F g = 1 := by
    rw [← ideleClassNorm_mk, hg]
    exact k.property
  let U := (c - 1)⁻¹ • (GlobalBruhat.leftTranslate F g - ContinuousLinearMap.id ℂ _)
  have hU (f : GlobalBruhat F) : U f ∈ P := by
    change GlobalBruhat.polarEvaluation F ((c - 1)⁻¹ • (GlobalBruhat.leftTranslate F g f - f)) = 0
    simp [map_sub, polarEvaluation_leftTranslate, hgN]
  refine ⟨U.codRestrict P hU, fun f => ?_⟩
  change H.mkQ (U f) = H.mkQ f
  have he : A (U f) = A f := by
    change A ((c - 1)⁻¹ • (GlobalBruhat.leftTranslate F g f - f)) = A f
    rw [map_smul, map_sub]
    change (c - 1)⁻¹ •
      (globalHomogeneousThetaOperator F ν ω (GlobalBruhat.leftTranslate F g f) - A f) = A f
    rw [globalHomogeneousThetaOperator_translate F ν ω k g hg]
    change (c - 1)⁻¹ • (c • A f - A f) = A f
    have hdiff : c • A f - A f = (c - 1) • A f := by rw [sub_smul, one_smul]
    rw [hdiff, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hc), one_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero H).mpr
  change A (U f - f) = 0
  rw [map_sub, he, sub_self]

/-- The polar-free tests have full image in every nontrivial homogeneous theta quotient. -/
theorem globalPolarFree_image_eq_top_of_ne_one
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) (hω : ω ≠ 1) :
    let H := (globalHomogeneousThetaOperator F ν ω).ker
    (GlobalBruhat.polarEvaluation F).ker.map H.mkQ = ⊤ := by
  intro H
  obtain ⟨L, hL⟩ := exists_globalPolarFree_lift_of_ne_one F ν ω hω
  apply top_unique
  intro q _
  obtain ⟨f, rfl⟩ := H.mkQ_surjective q
  exact Submodule.mem_map.mpr ⟨(L f).val, (L f).property, hL f⟩

/-- The quotient topology from the polar-free tests gives the whole
nontrivial homogeneous theta component. -/
theorem globalHomogeneousTheta_nontrivial_polarFree_isOpenQuotientMap
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) (hω : ω ≠ 1) :
    let H := (globalHomogeneousThetaOperator F ν ω).ker
    let P := (GlobalBruhat.polarEvaluation F).ker
    IsOpenQuotientMap (H.mkQL.comp P.subtypeL) := by
  intro H P
  let j := H.mkQL.comp P.subtypeL
  obtain ⟨L, hL⟩ := exists_globalPolarFree_lift_of_ne_one F ν ω hω
  have he : j ∘ L = H.mkQL := funext hL
  apply AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun V => ?_, ?_⟩
  · refine ⟨fun h => (H.isOpenQuotientMap_mkQL.isQuotientMap.isOpen_preimage).mp ?_,
      fun h => h.preimage j.continuous⟩
    rw [← he, preimage_comp]
    exact h.preimage L.continuous
  · intro q
    obtain ⟨f, rfl⟩ := H.mkQ_surjective q
    exact ⟨L f, hL f⟩

/-- The codimension of the polar-free image is two on the trivial homogeneous
theta component and zero on every other component. -/
theorem globalPolarFree_image_codimension
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F)) :
    let H := (globalHomogeneousThetaOperator F ν ω).ker
    Module.finrank ℂ ((GlobalBruhat F ⧸ H) ⧸ (GlobalBruhat.polarEvaluation F).ker.map H.mkQ) =
      if ω = 1 then 2 else 0 := by
  classical
  by_cases hω : ω = 1
  · subst ω
    intro H
    rw [ite_eq_left rfl]
    obtain ⟨P, hP⟩ := (globalPolarEvaluation_factors_homogeneous_iff F ν 1).2 rfl
    have hsurj : Function.Surjective P.toLinearMap := by
      intro x
      obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F x
      exact ⟨H.mkQ f, (hP f).trans hf⟩
    have hker : P.toLinearMap.ker = (GlobalBruhat.polarEvaluation F).ker.map H.mkQ := by
      ext x
      constructor
      · intro hx
        obtain ⟨f, rfl⟩ := H.mkQ_surjective x
        refine Submodule.mem_map.mpr ⟨f, ?_, rfl⟩
        change GlobalBruhat.polarEvaluation F f = 0
        exact (hP f).symm.trans (LinearMap.mem_ker.mp hx)
      · rintro ⟨f, hf, rfl⟩
        exact (hP f).trans hf
    rw [← hker, (P.toLinearMap.quotKerEquivOfSurjective hsurj).finrank_eq,
      Module.finrank_prod, Module.finrank_self]
  · intro H
    rw [ite_eq_right hω, globalPolarFree_image_eq_top_of_ne_one F ν ω hω]
    exact Module.finrank_zero_of_subsingleton

/-- The two signed residues give a split open quotient map on the trivial
homogeneous theta component. Its kernel is the image of the polar-free tests. -/
theorem globalHomogeneousTheta_trivial_residue_exact
    (ν : Measure (K F)) [ν.IsHaarMeasure] :
    let H := (globalHomogeneousThetaOperator F ν 1).ker
    let Q := GlobalBruhat F ⧸ H
    let P := (GlobalBruhat.polarEvaluation F).ker
    ∃ (R : Q →L[ℂ] ℂ × ℂ) (J : ℂ × ℂ →L[ℂ] Q),
      R.toLinearMap.ker = P.map H.mkQ ∧ IsOpenQuotientMap R ∧ RightInverse J R ∧
      ∀ f : GlobalBruhat F,
        R (H.mkQ f) =
          (-((ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).1),
            (ν.real univ : ℂ) * (GlobalBruhat.polarEvaluation F f).2) ∧
        ∀ κ : ℂ,
          let Z := globalZetaContinued F ν f (compactIdeleClassCharacter F 1) κ
          Tendsto (fun z => (z - (-κ)) * Z z) (𝓝[≠] (-κ)) (𝓝 (R (H.mkQ f)).1) ∧
          Tendsto (fun z => (z - (1 - κ)) * Z z) (𝓝[≠] (1 - κ)) (𝓝 (R (H.mkQ f)).2) := by
  intro H Q P
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let c : ℂ := ν.real univ
  have hc : c ≠ 0 := by
    change ((ν.real univ : ℝ) : ℂ) ≠ 0
    exact_mod_cast (measureReal_univ_pos (μ := ν)).ne'
  obtain ⟨T, hT⟩ := (globalPolarEvaluation_factors_homogeneous_iff F ν 1).2 rfl
  let R : Q →L[ℂ] ℂ × ℂ :=
    ((-c) • ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp T)).prod
      (c • ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp T))
  have hR (f : GlobalBruhat F) :
      R (H.mkQ f) = (-c * (GlobalBruhat.polarEvaluation F f).1,
        c * (GlobalBruhat.polarEvaluation F f).2) := by
    change (-c * (T (H.mkQ f)).1, c * (T (H.mkQ f)).2) = _
    have ht : T (H.mkQ f) = GlobalBruhat.polarEvaluation F f := hT f
    rw [ht]
  have hsurj : Surjective R := by
    intro x
    obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F
      ((-c)⁻¹ * x.1, c⁻¹ * x.2)
    refine ⟨H.mkQ f, ?_⟩
    rw [hR, hf]
    exact Prod.ext (mul_inv_cancel_left₀ (neg_ne_zero.mpr hc) _) (mul_inv_cancel_left₀ hc _)
  obtain ⟨v, hv⟩ := hsurj (1, 0)
  obtain ⟨w, hw⟩ := hsurj (0, 1)
  let J : ℂ × ℂ →L[ℂ] Q :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight v) +
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight w)
  have hJ : RightInverse J R := by
    intro x
    change R (x.1 • v + x.2 • w) = x
    rw [map_add, map_smul, map_smul, hv, hw]
    ext <;> simp
  have hopen : IsOpenMap R := .of_sections fun q => by
    refine ⟨fun x => J (x - R q) + q, (J.continuous.comp (continuous_id.sub continuous_const)).add
      continuous_const |>.continuousAt, by simp, ?_⟩
    intro x
    rw [map_add, hJ, sub_add_cancel]
  refine ⟨R, J, ?_, ⟨hsurj, R.continuous, hopen⟩, hJ, fun f => ⟨?_, ?_⟩⟩
  · ext q
    constructor
    · intro hq
      obtain ⟨f, rfl⟩ := H.mkQ_surjective q
      have hf := LinearMap.mem_ker.mp hq
      change R (H.mkQ f) = 0 at hf
      rw [hR] at hf
      refine Submodule.mem_map.mpr ⟨f, ?_, rfl⟩
      change GlobalBruhat.polarEvaluation F f = 0
      exact Prod.ext
        ((mul_eq_zero.mp (congrArg Prod.fst hf)).resolve_left (neg_ne_zero.mpr hc))
        ((mul_eq_zero.mp (congrArg Prod.snd hf)).resolve_left hc)
    · rintro ⟨f, hf, rfl⟩
      change GlobalBruhat.polarEvaluation F f = 0 at hf
      change R (H.mkQ f) = 0
      rw [hR, hf]
      simp
  · simpa only [neg_mul] using hR f
  · intro κ
    rw [hR, neg_mul]
    have h := globalZetaContinued_residue_limits F ν f (compactIdeleClassCharacter F 1)
      (compactIdeleClassCharacter_unitary F 1) κ
    have h₀ : (GlobalBruhat.polarEvaluation F f).1 = (GlobalBruhat.algebraicEquiv F f).val 0 := rfl
    have h₁ : (GlobalBruhat.polarEvaluation F f).2 =
        (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 := rfl
    simpa only [c, compactIdeleClassCharacter_integral, ite_true, h₀, h₁] using h

/-- The theta map on polar-free tests induces the subspace topology on its
image in the trivial homogeneous quotient. -/
theorem globalHomogeneousTheta_trivial_polarFree_strict
    (ν : Measure (K F)) [ν.IsHaarMeasure] :
    let H := (globalHomogeneousThetaOperator F ν 1).ker
    let P := (GlobalBruhat.polarEvaluation F).ker
    let j := H.mkQL.comp P.subtypeL
    IsStrictMap j.toLinearMap := by
  intro H P j
  obtain ⟨T, hT⟩ := (globalPolarEvaluation_factors_homogeneous_iff F ν 1).2 rfl
  let s := (j.toLinearMap.range : Set (GlobalBruhat F ⧸ H))
  have hpre : H.mkQL ⁻¹' s = (P : Set (GlobalBruhat F)) := by
    ext f
    constructor
    · rintro ⟨g, hg⟩
      have h := congrArg T hg
      change T (Submodule.Quotient.mk g.val) = T (Submodule.Quotient.mk f) at h
      rw [hT, hT] at h
      exact h.symm.trans g.property
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  let e : P ≃ₜ H.mkQL ⁻¹' s := Homeomorph.setCongr hpre.symm
  let r := s.restrictPreimage H.mkQL
  have hopen : IsOpenQuotientMap r :=
    H.isOpenQuotientMap_mkQL.restrictPreimage s
  have he : r ∘ e = j.toLinearMap.rangeRestrict := by
    funext f
    exact Subtype.ext rfl
  apply j.toLinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.2
  rw [← he]
  exact hopen.comp e.isOpenQuotientMap

end

end Masullo
