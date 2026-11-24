import GlobalSobolevWeilApproxInvariants

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField NNReal

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev U (v : HeightOneSpectrum (𝓞 F)) := ↥(principalIntegralUnits F v)
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev P := (GlobalBruhat.polarEvaluation F).ker

local instance intrinsicWeilClassMeasurable : MeasurableSpace (Q F) := borel _
local instance intrinsicWeilClassBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance intrinsicWeilClassLocallyCompact : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance intrinsicWeilClassT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance intrinsicWeilClassSecondCountable : SecondCountableTopology (Q F) :=
  ideleClass_secondCountable F
local instance intrinsicWeilUnitMeasurable (v : Place F) : MeasurableSpace (U F v) := borel _

private abbrev hs : (0 : ℝ) ≤ 2 := by norm_num
private abbrev t (q : Q F) := (ideleClassLogNorm F q).toAdd
private abbrev A (x : ℝ) := hardySobolevAmplitude 0 0 2 x
private abbrev g (v : Place F) := singleFiniteIdele F v (chosenFiniteUniformizer F v)

private theorem average_polar (v : Place F) (f : GlobalBruhat F) :
    GlobalBruhat.polarEvaluation F (globalFiniteUnitAverage F v f) = GlobalBruhat.polarEvaluation F f := by
  let E := (GlobalBruhat.polarEvaluation F).toLinearMap
  have he (u : U F v) :
      E (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f) = E f := by
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F
      (singleFiniteIdele F v u.val) f) = _
    rw [polarEvaluation_leftTranslate, singleFiniteIdele_norm, show ‖u.val.val‖ = 1 from u.property]
    simp [E]
  have hp (L : (ℂ × ℂ) →ₗ[ℂ] ℂ) : L (E (globalFiniteUnitAverage F v f)) = L (E f) := by
    let J := L.comp E
    change J (globalFiniteUnitAverage F v f) = J f
    rw [(globalFiniteUnitAverage_pairing F v f J).2]
    have h (u : U F v) : J (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f) = J f :=
      congrArg L (he u)
    simp_rw [h, integral_const, measureReal_def, principalUnitHaar_univ, ENNReal.toReal_one, one_smul]
  exact Prod.ext (hp (LinearMap.fst ℂ ℂ ℂ)) (hp (LinearMap.snd ℂ ℂ ℂ))

private theorem exists_avgFixed_polar_one (v : Place F) :
    ∃ f : GlobalBruhat F, globalFiniteUnitAverage F v f = f ∧
      GlobalBruhat.polarEvaluation F f = (1,0) := by
  obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F (1,0)
  exact ⟨_, globalFiniteUnitAverage_idempotent F v f, (average_polar F v f).trans hf⟩

private def testClass : P F →L[ℂ] GlobalPolarTheta F :=
  ((globalThetaOperator F).ker.mkQL.comp (P F).subtypeL).codRestrict _ (fun f => f.property)

private def translatedDifference (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = (1,0)) (a : Idele F) : P F :=
  ⟨GlobalBruhat.leftTranslate F a f - f, by
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F a f - f) = 0
    rw [map_sub, polarEvaluation_leftTranslate, hf]
    simp⟩

private theorem translatedDifference_average_fixed (v : Place F) (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = (1,0)) (a : Idele F)
    (hfix : globalFiniteUnitAverage F v f = f) :
    globalFiniteUnitAverage F v (translatedDifference F f hf a).val =
      (translatedDifference F f hf a).val := by
  change globalFiniteUnitAverage F v (GlobalBruhat.leftTranslate F a f - f) = _
  rw [map_sub, globalFiniteUnitAverage_leftTranslate, hfix]
  rfl

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

private abbrev J := (globalThetaSobolevMap F μ 0 0 0 2 hs).comp (testClass F)
private abbrev T (a : Q F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 2 hs a

private theorem J_translate (a : Idele F) (w : P F)
    (w' : P F) (hw' : w'.val = GlobalBruhat.leftTranslate F a w.val) :
    J F μ w' = T F μ (ideleClassMap F a) (J F μ w) := by
  have he : testClass F w' = globalPolarThetaTranslate F (ideleClassMap F a) (testClass F w) := by
    apply Subtype.ext
    change Submodule.Quotient.mk w'.val =
      globalThetaTranslate F (ideleClassMap F a) (Submodule.Quotient.mk w.val)
    rw [globalThetaTranslate_class, globalThetaTranslateIdeles_mk, hw']
  change globalThetaSobolevMap F μ 0 0 0 2 hs (testClass F w') = _
  rw [he]
  simpa only [J, ContinuousLinearMap.comp_apply, neg_zero, zero_mul, Real.exp_zero,
    Complex.ofReal_one, one_smul] using
    (globalThetaSobolevMap_translate F μ 0 0 0 2 hs (ideleClassMap F a) (testClass F w)).symm

/-- The degree-two principal value of a translated difference occupies only
the two translated edges of that difference. -/
private theorem translatedDifference_weil_formula (v : Place F) (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = (1,0)) (a : Idele F)
    (hfix : globalFiniteUnitAverage F v f = f) :
    let x := J F μ (translatedDifference F f hf a)
    let d := J F μ (translatedDifference F f hf (g F v))
    globalSobolevWeilPrincipalValue F μ 2 hs v x = d - T F μ (ideleClassMap F a) d := by
  dsimp only
  let b := g F v
  let p := translatedDifference F f hf a
  let q := translatedDifference F f hf b
  let u : P F := ⟨GlobalBruhat.leftTranslate F b p.val, by
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F b p.val) = 0
    rw [polarEvaluation_leftTranslate, show GlobalBruhat.polarEvaluation F p.val = 0 from p.property]
    simp⟩
  let w : P F := ⟨GlobalBruhat.leftTranslate F a q.val, by
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F a q.val) = 0
    rw [polarEvaluation_leftTranslate, show GlobalBruhat.polarEvaluation F q.val = 0 from q.property]
    simp⟩
  have he : p - u = q - w := by
    apply Subtype.ext
    change (GlobalBruhat.leftTranslate F a f - f) -
      GlobalBruhat.leftTranslate F b (GlobalBruhat.leftTranslate F a f - f) =
      (GlobalBruhat.leftTranslate F b f - f) -
        GlobalBruhat.leftTranslate F a (GlobalBruhat.leftTranslate F b f - f)
    rw [map_sub, map_sub, globalBruhatLeftTranslate_mul, globalBruhatLeftTranslate_mul, mul_comm b]
    abel
  change globalSobolevWeilPrincipalValue F μ 2 hs v (J F μ p) = _
  have hP : globalFiniteUnitAverage F v p.val = p.val := translatedDifference_average_fixed F v f hf a hfix
  have hcmp : globalSobolevWeilPrincipalValue F μ 2 hs v (J F μ p) =
      globalSobolevPrincipalValue F μ 2 hs v (J F μ p) :=
    globalSobolevWeilPrincipalValue_of_average_fixed F μ 2 hs v p hP
  rw [hcmp]
  change J F μ p - T F μ (ideleClassMap F b) (J F μ p) =
    J F μ q - T F μ (ideleClassMap F a) (J F μ q)
  rw [← J_translate F μ b p u rfl, ← J_translate F μ a q w rfl, ← map_sub, ← map_sub, he]

private abbrev theta (f : GlobalBruhat F) (q : Q F) := globalThetaOperator F f q

private theorem theta_log_limits (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = (1,0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Q F,
      (0 ≤ t F q → ‖theta F f q‖ ≤ C * Real.exp (-t F q)) ∧
      (t F q ≤ 0 → ‖theta F f q + 1‖ ≤ C * Real.exp (t F q)) := by
  obtain ⟨_, C, hC, h⟩ := adelicTheta_decay F f 1
  have h₁ : (GlobalBruhat.algebraicEquiv F f).val 0 = 1 := congrArg Prod.fst hf
  have h₂ : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0 :=
    congrArg Prod.snd hf
  refine ⟨C, hC, fun q => ?_⟩
  have hm : 0 < ideleClassNorm F q := ideleClassNorm_pos F q
  have ht : Real.exp (t F q) = ideleClassNorm F q := Real.exp_log hm
  constructor
  · intro hq
    have hmod : 1 ≤ ideleClassNorm F q := ht ▸ Real.one_le_exp hq
    change ‖adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q‖ ≤ _
    simpa only [pow_one, ← ht, ← Real.exp_neg] using (h q).1 hmod
  · intro hq
    have hmod : ideleClassNorm F q ≤ 1 := ht ▸ Real.exp_le_one_iff.mpr hq
    change ‖adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q + 1‖ ≤ _
    simpa only [h₁, h₂, smul_zero, sub_zero, pow_one, ← ht] using (h q).2.1 hmod

private theorem add_neg_one_triangle (x y : ℂ) :
    1 ≤ ‖x-y‖ + (‖x + 1‖ + ‖y‖) := by
  calc
    1 = ‖(-1 : ℂ)‖ := by simp
    _ = ‖(x-y) + (y-(x+1))‖ := by congr 1; ring
    _ ≤ ‖x-y‖ + ‖y-(x+1)‖ := norm_add_le _ _
    _ ≤ _ := by linarith [norm_sub_le y (x+1)]

private theorem log_class_shift (a : Idele F) (q : Q F) :
    t F ((ideleClassMap F a)⁻¹ * q) = t F q - t F (ideleClassMap F a) := by
  change (ideleClassLogNorm F ((ideleClassMap F a)⁻¹ * q)).toAdd = _
  rw [map_mul, map_inv]
  change -t F (ideleClassMap F a) + t F q = _
  ring

private theorem theta_difference_lower (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = (1,0)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (r : ℝ), R ≤ r → ∀ (a : Idele F),
      t F (ideleClassMap F a) = 4*r → ∀ (q : Q F),
      t F q ∈ Icc r (2*r) →
        (1/2 : ℝ) ≤ ‖globalPolarThetaFunction F (testClass F (translatedDifference F f hf a)) q‖ := by
  obtain ⟨C, hC, h⟩ := theta_log_limits F f hf
  refine ⟨4*C + 1, by positivity, fun r hr a ha q hq => ?_⟩
  let q' := (ideleClassMap F a)⁻¹ * q
  have hr0 : 0 ≤ r := by linarith
  have hq' : t F q' ≤ -r := by
    change t F ((ideleClassMap F a)⁻¹ * q) ≤ -r
    rw [log_class_shift, ha]
    linarith [hq.2]
  have hb : C * Real.exp (-r) ≤ 1/4 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos r)]
    linarith [Real.add_one_le_exp r]
  have hy : ‖theta F f q‖ ≤ 1/4 :=
    ((h q).1 (hr0.trans hq.1)).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hq.1)) hC.le).trans hb)
  have hx : ‖theta F f q' + 1‖ ≤ 1/4 :=
    ((h q').2 (hq'.trans (neg_nonpos.mpr hr0))).trans
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq') hC.le).trans hb)
  have hfun : globalPolarThetaFunction F (testClass F (translatedDifference F f hf a)) q =
      theta F f q' - theta F f q := by
    change globalThetaOperator F (GlobalBruhat.leftTranslate F a f - f) q = _
    rw [map_sub, Pi.sub_apply, globalThetaOperator_leftTranslate]
  rw [hfun]
  linarith [add_neg_one_triangle (theta F f q') (theta F f q), hx, hy]

omit [μ.IsHaarMeasure] in
private theorem degreeTwo_energy (u : Lp ℂ 2 μ) :
    Integrable (fun q => ‖u q‖^2) μ ∧ ‖u‖^2 = ∫ q, ‖u q‖^2 ∂μ := by
  have hu := Lp.memLp u
  exact ⟨(memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu,
    (congrArg (fun v : Lp ℂ 2 μ => ‖v‖^2) (Lp.toLp_coeFn u hu)).symm.trans (norm_sq_toLp_two hu)⟩

omit [μ.IsHaarMeasure] in
private theorem logSlab_measure {c : ℝ≥0} (hc : μ.map (t F) = c • volume)
    (r : ℝ) :
    μ (t F ⁻¹' Icc r (2*r)) = (c : ℝ≥0∞) * ENNReal.ofReal r := by
  have hct : Continuous (t F) := ideleClassLogNorm_continuous F
  rw [← Measure.map_apply hct.measurable measurableSet_Icc, hc, Measure.smul_apply,
    Real.volume_Icc, show 2*r-r = r by ring]
  rfl

private theorem theta_difference_norm_lower (f : GlobalBruhat F)
    (hf : GlobalBruhat.polarEvaluation F f = (1,0)) :
    ∃ R : ℝ, 0 < R ∧ ∃ D : ℝ, 0 < D ∧ ∀ (r : ℝ), R ≤ r → ∀ (a : Idele F),
      t F (ideleClassMap F a) = 4*r →
      D*r^3 ≤ ‖J F μ (translatedDifference F f hf a)‖^2 := by
  obtain ⟨R, hR, hdiff⟩ := theta_difference_lower F f hf
  obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
  refine ⟨R, hR, (c : ℝ)/4, by positivity, fun r hr a ha => ?_⟩
  let u := translatedDifference F f hf a
  let X := J F μ u
  let S := t F ⁻¹' Icc r (2*r)
  have hr0 : 0 < r := hR.trans_le hr
  have hct : Continuous (t F) := ideleClassLogNorm_continuous F
  have hS : MeasurableSet S := hct.measurable measurableSet_Icc
  have hm : μ S = (c : ℝ≥0∞) * ENNReal.ofReal r := logSlab_measure F μ hmap r
  have hfin : μ S ≠ ⊤ := by rw [hm]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hbnd : Integrable (S.indicator (fun _ => r^2/4)) μ :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hfin)
  have hX := globalThetaSobolevMap_ae F μ 0 0 0 2 hs (testClass F u)
  change (X : Q F → ℂ) =ᵐ[μ] fun q =>
    (A (t F q) * Real.exp (0 * t F q)) • globalPolarThetaFunction F (testClass F u) q at hX
  simp only [zero_mul, Real.exp_zero, mul_one] at hX
  have hpoint : ∀ᵐ q ∂μ, S.indicator (fun _ => r^2/4) q ≤ ‖X q‖^2 := by
    filter_upwards [hX] with q hq
    by_cases hqS : q ∈ S
    · rw [indicator_of_mem hqS, hq, norm_smul, Real.norm_eq_abs]
      have hA : A (t F q) = Real.sqrt (1 + (t F q)^2) := by
        norm_num [A, hardySobolevAmplitude, hardySobolevWeight]
      have hAr : r ≤ A (t F q) := by
        rw [hA, Real.le_sqrt hr0.le (by positivity)]
        have hqt : r ≤ t F q := hqS.1
        nlinarith [mul_nonneg (sub_nonneg.mpr hqt) (show 0 ≤ t F q + r by linarith)]
      rw [abs_of_nonneg (hr0.le.trans hAr)]
      have hhalf : (1/2 : ℝ) ≤ ‖globalPolarThetaFunction F (testClass F u) q‖ :=
        hdiff r hr a ha q hqS
      have he : r/2 ≤ A (t F q) * ‖globalPolarThetaFunction F (testClass F u) q‖ := by
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul hAr hhalf (by positivity) (hr0.le.trans hAr)
      nlinarith [sq_nonneg (r/2), mul_nonneg (sub_nonneg.mpr he)
        (show 0 ≤ A (t F q) * ‖globalPolarThetaFunction F (testClass F u) q‖ + r/2 by linarith)]
    · rw [indicator_of_notMem hqS]
      positivity
  change (c : ℝ)/4 * r^3 ≤ ‖X‖^2
  rw [(degreeTwo_energy F μ X).2]
  apply le_trans _ (integral_mono_ae hbnd (degreeTwo_energy F μ X).1 hpoint)
  rw [integral_indicator hS, setIntegral_const, measureReal_def, hm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr0.le, smul_eq_mul]
  change (c : ℝ) / 4 * r^3 ≤ ((c : ℝ) * r) * (r^2/4)
  exact le_of_eq (by ring)

private theorem translation_degreeTwo_bound (a : Q F) (d : Lp ℂ 2 μ) :
    ‖d - T F μ a d‖ ≤ (2 + |t F a|) * ‖d‖ := by
  have hT : ‖T F μ a‖ ≤ 1 + |t F a| := by
    simpa only [zero_mul, Real.exp_zero, one_mul, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
      using hardySobolevMulTranslation_singleton_opNorm_le μ (ideleClassLogNorm F)
        (ideleClassLogNorm_continuous F) 0 2 hs a
  calc
    _ ≤ ‖d‖ + ‖T F μ a d‖ := norm_sub_le _ _
    _ ≤ ‖d‖ + (1 + |t F a|) * ‖d‖ :=
      add_le_add_right (((T F μ a).le_opNorm d).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) _
    _ = _ := by ring

/-- The printed degree-two closed-range claim fails on the intrinsic
polar-free theta completion, without an ambient density premise. -/
theorem globalThetaSobolevWeilPrincipalValues_singleton_degreeTwo_nonclosed (v : Place F) :
    ¬ IsClosed (range (globalThetaSobolevWeilPrincipalValues F μ 2 hs {v})) := by
  let N := globalThetaSobolevCompletion F μ 0 0 0 2 hs
  let E := globalThetaSobolevWeilPrincipalValue F μ 2 hs v
  letI : CompleteSpace N := (globalThetaSobolevCompletion_isClosed F μ 0 0 0 2 hs).completeSpace_coe
  have hsingleton : globalThetaSobolevWeilPrincipalValues F μ 2 hs {v} = E :=
    Finset.noncommProd_singleton _ _
  rw [hsingleton]
  intro hclosed
  have hE : Injective E := by
    intro x y hxy
    apply Subtype.ext
    exact globalSobolevWeilPrincipalValue_degreeTwo_injective F μ v (congrArg Subtype.val hxy)
  obtain ⟨B, hB⟩ := E.antilipschitz_of_injective_of_isClosed_range hE hclosed
  obtain ⟨f, hfix, hf⟩ := exists_avgFixed_polar_one F v
  obtain ⟨R, hR, D, hD, hlower⟩ := theta_difference_norm_lower F μ f hf
  let d := J F μ (translatedDifference F f hf (g F v))
  let M : ℝ := 6 * (B : ℝ) * ‖d‖
  let r : ℝ := max R (max 1 (M^2/D + 1))
  have hrR : R ≤ r := le_max_left _ _
  have hr1 : 1 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hlarge : M^2 < D*r := by
    have h := (le_max_right (1 : ℝ) (M^2/D + 1)).trans (le_max_right R _)
    have hm : M^2 / D < r := (lt_add_of_pos_right _ zero_lt_one).trans_le h
    simpa only [mul_comm r D] using (div_lt_iff₀ hD).mp hm
  let a := ideleExpSection F (Multiplicative.ofAdd (4*r))
  have ha : t F (ideleClassMap F a) = 4*r :=
    congrArg Multiplicative.toAdd (ideleClassLogNorm_expSection F (Multiplicative.ofAdd (4*r)))
  let u := translatedDifference F f hf a
  let x : N := globalThetaSobolevDenseMap F μ 0 0 0 2 hs (testClass F u)
  have hsmall : ‖E x‖ ≤ (2 + 4*r) * ‖d‖ := by
    change ‖globalSobolevWeilPrincipalValue F μ 2 hs v (J F μ u)‖ ≤ _
    rw [translatedDifference_weil_formula F μ v f hf a hfix]
    simpa only [ha, abs_of_nonneg (show 0 ≤ 4*r by positivity)] using
      translation_degreeTwo_bound F μ (ideleClassMap F a) d
  have hnorm := hB.le_mul_dist x 0
  rw [map_zero, dist_zero_right, dist_zero_right] at hnorm
  have hx : ‖x‖ ≤ M*r := by
    calc
      _ ≤ (B : ℝ) * ‖E x‖ := hnorm
      _ ≤ (B : ℝ) * ((2 + 4*r) * ‖d‖) := mul_le_mul_of_nonneg_left hsmall B.coe_nonneg
      _ ≤ (B : ℝ) * ((6*r) * ‖d‖) := by
        gcongr
        linarith
      _ = _ := by dsimp [M]; ring
  have hlow : D*r^3 ≤ ‖x‖^2 := hlower r hrR a ha
  have hupper : ‖x‖^2 ≤ (M*r)^2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hstrict : (M*r)^2 < D*r^3 := by
    calc
      _ = M^2*r^2 := mul_pow .. 
      _ < (D*r)*r^2 := mul_lt_mul_of_pos_right hlarge (by positivity)
      _ = _ := by ring
  exact (not_lt_of_ge (hlow.trans hupper)) hstrict

end
end Masullo
