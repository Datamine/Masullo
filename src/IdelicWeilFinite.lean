import FiniteWeilDifferent
import NormTwistCharts

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
local notation "Place" => HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place) := v.adicCompletion F
private abbrev LocalIntegers (v : Place) := v.adicCompletionIntegers F

/-- The product of the integral unit groups at all finite places. -/
abbrev IntegralUnitFamily := ∀ v : Place, principalIntegralUnits F v

set_option maxHeartbeats 1500000

private def integralUnitFamilyFinite (u : IntegralUnitFamily F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion (LocalField F) (fun w ↦ (LocalIntegers F) w) le_top
    (RestrictedProduct.homeoTop (fun w ↦ ⟨(u w).val.val, by
      have h := (finiteCompletion_norm_eq_one_iff F w (u w).val).mp (u w).property
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ F w).mpr h.le⟩))

private theorem integralUnitFamilyFinite_apply (u : IntegralUnitFamily F) (v : Place) :
    integralUnitFamilyFinite F u v = (u v).val.val := rfl

private theorem integralUnitFamilyFinite_continuous : Continuous (integralUnitFamilyFinite F) := by
  apply (RestrictedProduct.continuous_inclusion le_top).comp
  apply RestrictedProduct.homeoTop.continuous.comp
  exact continuous_pi fun w ↦ ((Units.continuous_val.comp continuous_subtype_val).comp
    (continuous_apply w)).subtype_mk _

private def integralUnitFamilyIdele (u : IntegralUnitFamily F) : Idele F :=
  ⟨(1, integralUnitFamilyFinite F u), (1, integralUnitFamilyFinite F u⁻¹), by
      apply Prod.ext (mul_one _)
      apply DFunLike.ext
      intro w
      change integralUnitFamilyFinite F u w * integralUnitFamilyFinite F u⁻¹ w = 1
      rw [integralUnitFamilyFinite_apply, integralUnitFamilyFinite_apply]
      change (u w).val.val * ((u w).val⁻¹).val = 1
      exact (u w).val.val_inv
    , by
      apply Prod.ext (mul_one _)
      apply DFunLike.ext
      intro w
      change integralUnitFamilyFinite F u⁻¹ w * integralUnitFamilyFinite F u w = 1
      rw [integralUnitFamilyFinite_apply, integralUnitFamilyFinite_apply]
      change ((u w).val⁻¹).val * (u w).val.val = 1
      exact (u w).val.inv_val⟩

/-- Insert the full product of integral finite units into the idele class group. -/
def integralUnitFamilyClass (u : IntegralUnitFamily F) : IdeleClass F :=
  ideleClassMap F (integralUnitFamilyIdele F u)

theorem integralUnitFamilyClass_continuous : Continuous (integralUnitFamilyClass F) := by
  apply (ideleClassMap_continuous F).comp
  exact Units.continuous_iff.mpr ⟨continuous_const.prodMk (integralUnitFamilyFinite_continuous F),
    continuous_const.prodMk ((integralUnitFamilyFinite_continuous F).comp continuous_inv)⟩

@[simp] theorem integralUnitFamilyClass_one : integralUnitFamilyClass F 1 = 1 := by
  have h : integralUnitFamilyIdele F 1 = 1 := by
    apply Units.ext
    apply Prod.ext rfl
    apply DFunLike.ext
    intro w
    exact integralUnitFamilyFinite_apply F 1 w
  rw [integralUnitFamilyClass, h, map_one]

theorem integralUnitFamilyClass_mul (a b : IntegralUnitFamily F) :
    integralUnitFamilyClass F (a * b) =
      integralUnitFamilyClass F a * integralUnitFamilyClass F b := by
  unfold integralUnitFamilyClass
  rw [← map_mul]
  apply congrArg (ideleClassMap F)
  apply Units.ext
  apply Prod.ext
  · exact (mul_one (1 : InfiniteAdeleRing F)).symm
  apply DFunLike.ext
  intro w
  change integralUnitFamilyFinite F (a * b) w =
    integralUnitFamilyFinite F a w * integralUnitFamilyFinite F b w
  simp only [integralUnitFamilyFinite_apply, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]

/-- A finite integral unit placed in one coordinate of the product. -/
def integralUnitFamilySingle (v : Place) (u : principalIntegralUnits F v) : IntegralUnitFamily F :=
  Function.update 1 v u

theorem integralUnitFamilySingle_continuous (v : Place) :
    Continuous (integralUnitFamilySingle F v) :=
  (continuous_const (y := (1 : IntegralUnitFamily F))).update v continuous_id

theorem integralUnitFamilySingle_class (v : Place) (u : principalIntegralUnits F v) :
    integralUnitFamilyClass F (integralUnitFamilySingle F v u) =
      finitePlaceInsertion F v u.val := by
  rw [finitePlaceInsertion_apply]
  apply congrArg (ideleClassMap F)
  apply Units.ext
  apply Prod.ext
  · rfl
  apply DFunLike.ext
  intro w
  change integralUnitFamilyFinite F (integralUnitFamilySingle F v u) w =
    Function.update (fun i : Place ↦ (1 : (LocalField F) i)) v u.val.val w
  rw [integralUnitFamilyFinite_apply]
  unfold integralUnitFamilySingle
  by_cases h : w = v
  · subst w
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]
    rfl

/-- A neighborhood of one in the product contains all single-coordinate units
at all but finitely many places. -/
theorem integralUnitFamilySingle_eventually_mem {V : Set (IntegralUnitFamily F)}
    (hV : V ∈ 𝓝 (1 : IntegralUnitFamily F)) :
    ∀ᶠ v : Place in cofinite, ∀ a : principalIntegralUnits F v,
      integralUnitFamilySingle F v a ∈ V := by
  classical
  by_contra hc
  have hN : ∀ v : Place, ∃ a : principalIntegralUnits F v,
      (∃ b : principalIntegralUnits F v, integralUnitFamilySingle F v b ∉ V) →
        integralUnitFamilySingle F v a ∉ V := by
    intro v
    by_cases hv : ∃ b : principalIntegralUnits F v, integralUnitFamilySingle F v b ∉ V
    · obtain ⟨a, ha⟩ := hv
      exact ⟨a, fun _ ↦ ha⟩
    · exact ⟨1, fun he ↦ (hv he).elim⟩
  choose a ha using hN
  have ht : Tendsto (fun v ↦ integralUnitFamilySingle F v (a v)) cofinite
      (𝓝 (1 : IntegralUnitFamily F)) := by
    apply tendsto_pi_nhds.mpr
    intro w
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cofinite_ne w] with v hv
    change (1 : principalIntegralUnits F w) = (Function.update (1 : IntegralUnitFamily F) v (a v)) w
    rw [Function.update_of_ne (Ne.symm hv)]
    rfl
  apply hc
  filter_upwards [ht.eventually hV] with v hv b
  by_contra hb
  exact ha v ⟨b, hb⟩ hv

/-- Local constancy in the finite directions of an idelic test function. -/
def IdelicTestLocallyConstantAtFinite (φ : IdeleClass F → ℂ) : Prop :=
  ∀ g : IdeleClass F, IsLocallyConstant (fun a : IntegralUnitFamily F ↦ φ (g * integralUnitFamilyClass F a))

/-- Invariance under an open subgroup of the finite integral unit family
implies the finite-direction test condition. -/
theorem idelicTestLocallyConstantAtFinite_of_open_invariance (φ : IdeleClass F → ℂ)
    (H : Subgroup (IntegralUnitFamily F)) (hH : IsOpen (H : Set (IntegralUnitFamily F)))
    (hφ : ∀ g a, a ∈ H → φ (g * integralUnitFamilyClass F a) = φ g) :
    IdelicTestLocallyConstantAtFinite F φ := by
  intro g
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have hmem : a ∈ (fun b : IntegralUnitFamily F ↦ a⁻¹ * b) ⁻¹' (H : Set (IntegralUnitFamily F)) := by
    change a⁻¹ * a ∈ H
    rw [inv_mul_cancel]
    exact H.one_mem
  have ho := hH.preimage (continuous_const.mul continuous_id :
    Continuous (fun b : IntegralUnitFamily F ↦ a⁻¹ * b))
  filter_upwards [ho.mem_nhds hmem] with b hb
  have h := hφ (g * integralUnitFamilyClass F a) (a⁻¹ * b) hb
  change φ (g * integralUnitFamilyClass F b) = φ (g * integralUnitFamilyClass F a)
  rwa [mul_assoc, ← integralUnitFamilyClass_mul, mul_inv_cancel_left] at h

private theorem finitePlaceInsertion_norm (v : Place) (u : ((LocalField F) v)ˣ) :
    ideleClassNorm F (finitePlaceInsertion F v u) = ‖u.val‖ := by
  rw [finitePlaceInsertion_apply, ideleClassNorm_mk, singleFiniteIdele_norm]

private theorem finitePlaceInsertion_locallyConstant (φ : IdeleClass F → ℂ)
    (hφ : IdelicTestLocallyConstantAtFinite F φ) (v : Place) :
    IsLocallyConstant (fun u : ((LocalField F) v)ˣ ↦ φ (finitePlaceInsertion F v u)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u
  let j (a : principalIntegralUnits F v) := u * a.val
  have hU : IsOpen (principalIntegralUnits F v : Set ((LocalField F) v)ˣ) := by
    have he : (principalIntegralUnits F v : Set ((LocalField F) v)ˣ) = finitePlaceIntegralUnits F v := by
      ext a
      exact (finiteCompletion_norm_eq_one_iff F v a).trans (localIntegralUnits_value F v a).symm
    rw [he]
    exact localIntegralUnits_open F v
  have hj : IsOpenEmbedding j :=
    (Homeomorph.mulLeft u).isOpenEmbedding.comp hU.isOpenEmbedding_subtypeVal
  have hc := (hφ (finitePlaceInsertion F v u)).comp_continuous
    (integralUnitFamilySingle_continuous F v)
  have hj₁ : j 1 = u := mul_one _
  have hs (a : principalIntegralUnits F v) :
      φ (finitePlaceInsertion F v u * integralUnitFamilyClass F (integralUnitFamilySingle F v a)) =
        φ (finitePlaceInsertion F v (j a)) := by
    rw [integralUnitFamilySingle_class, ← map_mul]
  rw [← hj₁, ← hj.map_nhds_eq 1]
  change ∀ᶠ a in 𝓝 (1 : principalIntegralUnits F v),
    φ (finitePlaceInsertion F v (j a)) = φ (finitePlaceInsertion F v (j 1))
  simp only [← hs]
  exact hc.eventually_eq 1

private theorem finitePlaceInsertion_normUnits (v : Place) :
    (fun u : ((LocalField F) v)ˣ ↦ globalNormUnits F (finitePlaceInsertion F v u)) =
      (Units.map nnnormHom.toMonoidHom : ((LocalField F) v)ˣ →* ℝ≥0ˣ) := by
  funext u
  apply Units.ext
  apply NNReal.eq
  exact finitePlaceInsertion_norm F v u

/-- The local inclusion into the idele classes is proper at every finite place. -/
theorem finitePlaceInsertion_isProper (v : Place) : IsProperMap (finitePlaceInsertion F v) := by
  letI : T2Space (IdeleClass F) := ideleClasses_hausdorff
  letI := finitePlace_locallyCompact F v
  let p := chosenFiniteUniformizer F v
  have hp : 1 < ‖p.val⁻¹‖ := by
    rw [norm_inv, norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_inv]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  letI : NontriviallyNormedField ((LocalField F) v) := ⟨⟨p.val⁻¹, hp⟩⟩
  letI : ProperSpace ((LocalField F) v) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  let n : ((LocalField F) v)ˣ →* ℝ≥0ˣ := Units.map nnnormHom.toMonoidHom
  have hn : IsProperMap n := by
    have hp := isProperMap_units_nnnorm_pow (K := (LocalField F) v) 1 Nat.one_ne_zero
    change IsProperMap (n ^ (1 : ℕ) : ((LocalField F) v)ˣ →* ℝ≥0ˣ) at hp
    have he : (n ^ (1 : ℕ) : ((LocalField F) v)ˣ →* ℝ≥0ˣ) = n := pow_one n
    rwa [he] at hp
  refine isProperMap_of_comp_of_t2 (finitePlaceInsertion F v).continuous
    (globalNormUnits_proper F).continuous ?_
  rw [show globalNormUnits F ∘ finitePlaceInsertion F v = n from finitePlaceInsertion_normUnits F v]
  exact hn

private theorem finitePlaceInsertion_hasCompactSupport (φ : IdeleClass F → ℂ)
    (hφ : HasCompactSupport φ) (v : Place) :
    HasCompactSupport (fun u : ((LocalField F) v)ˣ ↦ φ (finitePlaceInsertion F v u)) :=
  HasCompactSupport.intro ((finitePlaceInsertion_isProper F v).isCompact_preimage hφ)
    fun _ hu => image_eq_zero_of_notMem_tsupport hu

/-- Restrict a compactly supported idelic test to the actual finite local group. -/
def finitePlaceIdelicTest (φ : IdeleClass F → ℂ) (hc : HasCompactSupport φ)
    (hφ : IdelicTestLocallyConstantAtFinite F φ) (v : Place) :
    locallyConstantTests ((LocalField F) v)ˣ :=
  ⟨fun u ↦ φ (finitePlaceInsertion F v u), finitePlaceInsertion_locallyConstant F φ hφ v,
    finitePlaceInsertion_hasCompactSupport F φ hc v⟩

private theorem absNorm_tendsto_cofinite : Tendsto
    (fun v : Place ↦ (v.asIdeal.absNorm : ℝ)) cofinite atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop.mpr
  intro n
  apply eventually_cofinite.mpr
  refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).preimage
    (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h)).subset ?_
  intro v hv
  exact (lt_of_not_ge hv).le

private theorem finitePlaceInsertion_eventually_avoids_compact_off_units
    (C : Set (IdeleClass F)) (hC : IsCompact C) :
    ∀ᶠ v : Place in cofinite, ∀ u : (LocalField F v)ˣ,
      u ∉ finitePlaceIntegralUnits F v → finitePlaceInsertion F v u ∉ C := by
  have hi : Continuous (fun x : IdeleClass F ↦ (ideleClassNorm F x)⁻¹) :=
    (ideleClassNorm_continuous F).inv₀ (fun x ↦ (ideleClassNorm_pos F x).ne')
  obtain ⟨A, hA⟩ := (hC.image (ideleClassNorm_continuous F)).bddAbove
  obtain ⟨B, hB⟩ := (hC.image hi).bddAbove
  filter_upwards [(absNorm_tendsto_cofinite F).eventually (eventually_gt_atTop (max A B))]
    with v hv u hu
  intro hx
  have h₁ := hA ⟨finitePlaceInsertion F v u, hx, rfl⟩
  have h₂ := hB ⟨finitePlaceInsertion F v u, hx, rfl⟩
  change ideleClassNorm F (finitePlaceInsertion F v u) ≤ A at h₁
  change (ideleClassNorm F (finitePlaceInsertion F v u))⁻¹ ≤ B at h₂
  rw [finitePlaceInsertion_norm] at h₁ h₂
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    change (1 : ℝ) < v.asIdeal.absNorm
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ‖u.val‖ = q ^ (-n) :=
    iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) u
  have hn₀ : n = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg | hpos
    · have hle : q ≤ ‖u.val‖ := by
        rw [hn]
        calc
          q = q ^ (1 : ℤ) := (zpow_one q).symm
          _ ≤ _ := zpow_le_zpow_right₀ hq.le (by omega)
      exact (not_lt_of_ge (hle.trans (h₁.trans (le_max_left _ _)))) hv
    · have hle : q ≤ ‖u.val‖⁻¹ := by
        rw [hn, ← zpow_neg, neg_neg]
        calc
          q = q ^ (1 : ℤ) := (zpow_one q).symm
          _ ≤ _ := zpow_le_zpow_right₀ hq.le (by omega)
      exact (not_lt_of_ge (hle.trans (h₂.trans (le_max_right _ _)))) hv
  apply hu
  apply (localIntegralUnits_value F v u).mpr
  apply (finiteCompletion_norm_eq_one_iff F v u).mp
  rw [hn, hn₀, neg_zero, zpow_zero]

private theorem finitePlaceIdelicTest_eventually_zero_off_units (φ : IdeleClass F → ℂ)
    (hc : HasCompactSupport φ) :
    ∀ᶠ v : Place in cofinite, ∀ u : (LocalField F v)ˣ,
      u ∉ finitePlaceIntegralUnits F v → φ (finitePlaceInsertion F v u) = 0 := by
  filter_upwards [finitePlaceInsertion_eventually_avoids_compact_off_units F (tsupport φ) hc]
    with v hv u hu
  exact image_eq_zero_of_notMem_tsupport (hv u hu)

private theorem finitePlaceIdelicTest_eventually_constant_on_units (φ : IdeleClass F → ℂ)
    (hφ : IdelicTestLocallyConstantAtFinite F φ) :
    ∀ᶠ v : Place in cofinite, ∀ u : (LocalField F v)ˣ,
      u ∈ finitePlaceIntegralUnits F v → φ (finitePlaceInsertion F v u) = φ 1 := by
  let V : Set (IntegralUnitFamily F) := {a | φ (integralUnitFamilyClass F a) = φ 1}
  have hV : V ∈ 𝓝 (1 : IntegralUnitFamily F) := by
    change ∀ᶠ a : IntegralUnitFamily F in 𝓝 1, φ (integralUnitFamilyClass F a) = φ 1
    have h := (hφ (1 : IdeleClass F)).eventually_eq (1 : IntegralUnitFamily F)
    filter_upwards [h] with a ha
    change φ (1 * integralUnitFamilyClass F a) = φ (1 * integralUnitFamilyClass F 1) at ha
    exact (congrArg φ (one_mul (integralUnitFamilyClass F a))).symm.trans
      (ha.trans (congrArg φ ((one_mul (integralUnitFamilyClass F 1)).trans
        (integralUnitFamilyClass_one F))))
  filter_upwards [integralUnitFamilySingle_eventually_mem F hV] with v hv u hu
  let a : principalIntegralUnits F v :=
    ⟨u, (finiteCompletion_norm_eq_one_iff F v u).mpr ((localIntegralUnits_value F v u).mp hu)⟩
  have ha := hv a
  change φ (integralUnitFamilyClass F (integralUnitFamilySingle F v a)) = φ 1 at ha
  rwa [integralUnitFamilySingle_class] at ha

/-- All sufficiently large finite-place restrictions are exactly the
unit-indicator test times the value of the global test at one. -/
theorem finitePlaceIdelicTest_eventually_unitTest (φ : IdeleClass F → ℂ)
    (hc : HasCompactSupport φ) (hφ : IdelicTestLocallyConstantAtFinite F φ) :
    ∀ᶠ v : Place in cofinite, finitePlaceIdelicTest F φ hc hφ v = φ 1 • finiteWeilUnitTest F v := by
  filter_upwards [finitePlaceIdelicTest_eventually_zero_off_units F φ hc,
    finitePlaceIdelicTest_eventually_constant_on_units F φ hφ] with v hz hu
  apply Subtype.ext
  funext u
  change φ (finitePlaceInsertion F v u) =
    φ 1 * (finitePlaceIntegralUnits F v).indicator (fun _ ↦ (1 : ℂ)) u
  by_cases he : u ∈ finitePlaceIntegralUnits F v
  · rw [indicator_of_mem he, mul_one, hu u he]
  · rw [indicator_of_notMem he, mul_zero, hz u he]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]

/-- The normalized finite-place summand in (B.4.4.16). -/
def finitePlaceIdelicWeilTerm (φ : IdeleClass F → ℂ) (hc : HasCompactSupport φ)
    (hφ : IdelicTestLocallyConstantAtFinite F φ) (v : Place) : ℂ :=
  (Real.log (v.asIdeal.absNorm : ℝ) / (μ v).real (finitePlaceIntegralUnits F v)) •
    finiteWeilPrincipalValue F v (μ v) 1 (finitePlaceIdelicTest F φ hc hφ v)

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
private theorem finiteWeilPrincipalValue_smul (v : Place) (a : ℂ)
    (f : locallyConstantTests (LocalField F v)ˣ) :
    finiteWeilPrincipalValue F v (μ v) 1 (a • f) =
      a • finiteWeilPrincipalValue F v (μ v) 1 f := by
  let ν := additiveHaarDifferent F v
  letI := additiveHaarDifferent_isHaar F v
  let A := finiteWeilTestLinear F v
  let J := finiteLogFourierPairing F v ν
  let m : ℂ := (μ v).real (finitePlaceIntegralUnits F v)
  unfold finiteWeilPrincipalValue finiteConnesPrincipalValue
  simp only [Units.val_one, norm_one, one_smul, one_mul]
  change -m * J (A (a • f)) = a * (-m * J (A f))
  rw [map_smul, map_smul, smul_eq_mul]
  ring

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ] in
private theorem finitePlace_eventually_not_dvd_different :
    ∀ᶠ v : Place in cofinite, ¬v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  apply eventually_cofinite.mpr
  simpa only [not_not] using Ideal.finite_factors
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
/-- Only finitely many finite places contribute to the geometric explicit-formula
sum on a compactly supported idelic test locally constant in the finite directions. -/
theorem finitePlaceIdelicWeilTerm_hasFiniteSupport (φ : IdeleClass F → ℂ)
    (hc : HasCompactSupport φ) (hφ : IdelicTestLocallyConstantAtFinite F φ) :
    (finitePlaceIdelicWeilTerm F μ φ hc hφ).HasFiniteSupport := by
  apply eventually_cofinite.mp
  filter_upwards [finitePlaceIdelicTest_eventually_unitTest F φ hc hφ,
    finitePlace_eventually_not_dvd_different F] with v hv hdv
  unfold finitePlaceIdelicWeilTerm
  rw [hv, finiteWeilPrincipalValue_smul F μ,
    finiteWeil_unitTest_principalValue_of_not_dvd_different F v (μ v) hdv, smul_zero, smul_zero]

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
/-- One finite set works for every test with support in a fixed compact set
and invariant under a fixed open level of integral units. -/
theorem finitePlaceIdelicWeilTerm_uniformly_zero (C : Set (IdeleClass F)) (hC : IsCompact C)
    (H : Subgroup (IntegralUnitFamily F)) (hH : IsOpen (H : Set (IntegralUnitFamily F))) :
    ∀ᶠ v : Place in cofinite, ∀ (φ : IdeleClass F → ℂ) (hc : HasCompactSupport φ)
      (hφ : IdelicTestLocallyConstantAtFinite F φ), tsupport φ ⊆ C →
      (∀ g a, a ∈ H → φ (g * integralUnitFamilyClass F a) = φ g) →
      finitePlaceIdelicWeilTerm F μ φ hc hφ v = 0 := by
  filter_upwards [finitePlaceInsertion_eventually_avoids_compact_off_units F C hC,
    integralUnitFamilySingle_eventually_mem F (hH.mem_nhds H.one_mem),
    finitePlace_eventually_not_dvd_different F] with v hoff hon hd φ hc hφ hs hh
  have htest : finitePlaceIdelicTest F φ hc hφ v = φ 1 • finiteWeilUnitTest F v := by
    apply Subtype.ext
    funext u
    change φ (finitePlaceInsertion F v u) =
      φ 1 * (finitePlaceIntegralUnits F v).indicator (fun _ ↦ (1 : ℂ)) u
    by_cases hu : u ∈ finitePlaceIntegralUnits F v
    · let a : principalIntegralUnits F v :=
        ⟨u, (finiteCompletion_norm_eq_one_iff F v u).mpr ((localIntegralUnits_value F v u).mp hu)⟩
      have h := hh 1 (integralUnitFamilySingle F v a) (hon a)
      have h₁ := (one_mul (integralUnitFamilyClass F (integralUnitFamilySingle F v a))).trans
        (integralUnitFamilySingle_class F v a)
      rw [indicator_of_mem hu, mul_one]
      exact (congrArg φ h₁).symm.trans h
    · rw [indicator_of_notMem hu, mul_zero]
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hoff u hu (hs h))
  unfold finitePlaceIdelicWeilTerm
  rw [htest, finiteWeilPrincipalValue_smul F μ,
    finiteWeil_unitTest_principalValue_of_not_dvd_different F v (μ v) hd, smul_zero, smul_zero]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ] in
private theorem log_finiteWeilCodifferent (v : Place) :
    Real.log ‖(finiteWeilCodifferentGenerator F v).val‖ =
      (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
  unfold finiteWeilCodifferentGenerator
  rw [finitePlaceUniformizer_norm_zpow F v, neg_neg, zpow_natCast, Real.log_pow]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ] in
/-- The sum of the finite logarithmic codifferent factors is the logarithm of
the absolute discriminant. -/
theorem finiteWeilCodifferent_log_tsum :
    (∑' v : Place, Real.log ‖(finiteWeilCodifferentGenerator F v).val‖) =
      Real.log ((discr F).natAbs : ℝ) := by
  let J := differentIdeal ℤ (𝓞 F)
  let d (v : Place) := multiplicity v.asIdeal J
  let S := (Ideal.finite_factors (show J ≠ ⊥ from differentIdeal_ne_bot)).toFinset
  have hd (v : Place) (hv : v ∉ S) : d v = 0 := by
    apply multiplicity_eq_zero.mpr
    simpa [S] using hv
  have hJ : ∏ v ∈ S, v.asIdeal ^ d v = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (f := fun v : Place ↦ v.asIdeal ^ d v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity differentIdeal_ne_bot
    · intro v hv
      by_contra hn
      exact hv (by simp [hd v hn])
  have hnorm : (∏ v ∈ S, (v.asIdeal.absNorm : ℝ) ^ d v) = ((discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hJ :
      (∏ v ∈ S, v.asIdeal.absNorm ^ d v) = (discr F).natAbs)
  rw [tsum_eq_sum (s := S)]
  · rw [← hnorm, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro v _
      rw [Real.log_pow, log_finiteWeilCodifferent]
    · intro v _
      have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
        exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
      exact pow_ne_zero _ hq.ne'
  · intro v hv
    rw [log_finiteWeilCodifferent, show multiplicity v.asIdeal J = 0 from hd v hv,
      Nat.cast_zero, zero_mul]

/-- The finite-place geometric terms in (B.4.4.16) agree with the local
Weil cutoffs and the global discriminant contribution. Both sums have finite support. -/
theorem finitePlaceIdelicWeilTerm_tsum
    (hμ : ∀ v : Place, μ v (finitePlaceIntegralUnits F v) =
      additiveHaarDifferent F v (v.adicCompletionIntegers F : Set (LocalField F v)))
    (φ : IdeleClass F → ℂ) (hc : HasCompactSupport φ)
    (hφ : IdelicTestLocallyConstantAtFinite F φ) :
    let t := finitePlaceIdelicWeilTerm F μ φ hc hφ
    let p (v : Place) := finiteWeilCanonicalPrincipalValue F v (μ v) (finitePlaceIdelicTest F φ hc hφ v)
    t.HasFiniteSupport ∧ p.HasFiniteSupport ∧
      (∑' v, t v) = (∑' v, p v) - (Real.log ((discr F).natAbs : ℝ)) • φ 1 := by
  dsimp only
  let t := finitePlaceIdelicWeilTerm F μ φ hc hφ
  let p (v : Place) := finiteWeilCanonicalPrincipalValue F v (μ v) (finitePlaceIdelicTest F φ hc hφ v)
  let b (v : Place) := Real.log ‖(finiteWeilCodifferentGenerator F v).val‖
  have ht : t.HasFiniteSupport := finitePlaceIdelicWeilTerm_hasFiniteSupport F μ φ hc hφ
  have hbEv : ∀ᶠ v in cofinite, b v = 0 := by
    filter_upwards [finitePlace_eventually_not_dvd_different F] with v hv
    change Real.log ‖(finiteWeilCodifferentGenerator F v).val‖ = 0
    rw [log_finiteWeilCodifferent, multiplicity_eq_zero.mpr hv, Nat.cast_zero, zero_mul]
  have hb : b.HasFiniteSupport := eventually_cofinite.mp hbEv
  have he (v : Place) : t v = p v - b v • φ 1 := by
    have h := finiteWeilPrincipalValue_canonical F v (μ v) (hμ v)
      (finitePlaceIdelicTest F φ hc hφ v)
    have h1 : (finitePlaceIdelicTest F φ hc hφ v).val 1 = φ 1 := by
      change φ (finitePlaceInsertion F v 1) = φ 1
      rw [map_one]
    rw [h1] at h
    exact h
  have hp : p.HasFiniteSupport := by
    apply eventually_cofinite.mp
    have htEv : ∀ᶠ v in cofinite, t v = 0 := eventually_cofinite.mpr ht
    filter_upwards [htEv, hbEv] with v htv hbv
    have h := he v
    rwa [htv, hbv, zero_smul, sub_zero, eq_comm] at h
  refine ⟨ht, hp, ?_⟩
  change (∑' v, t v) = (∑' v, p v) - Real.log ↑(discr F).natAbs • φ 1
  have hbs : Summable b := summable_of_hasFiniteSupport hb
  have hps : Summable p := summable_of_hasFiniteSupport hp
  rw [tsum_congr he, hps.tsum_sub (hbs.smul_const _), hbs.tsum_smul_const,
    finiteWeilCodifferent_log_tsum F]

end
end Masullo
