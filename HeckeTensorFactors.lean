import GlobalHeckeEigenfamilies
import ArchimedeanGammaProductTest
import ArchimedeanEigenfamilies
import FiniteEigenfamilies

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

/-- The real normalized family with the parity Gaussian as reference. -/
def realWeilNormalizedFamily (a : ℕ) : ℂ → StrongDual ℂ 𝓢(ℝ, ℂ) :=
  (realGammaNormalized_distribution a).choose_spec.choose

/-- The complex normalized family with the angular Gaussian as reference. -/
def complexWeilNormalizedFamily (m : ℤ) : ℂ → StrongDual ℂ 𝓢(ℂ, ℂ) :=
  (complexGammaNormalized_distribution m).choose_spec.choose

private theorem real_family_spec (a : ℕ) :
    Differentiable ℂ (realWeilNormalizedFamily a) ∧
    ∀ c, realArchimedeanZetaContinuedCLM a =ᶠ[𝓝[≠] c] fun z =>
      Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ)) • realWeilNormalizedFamily a z :=
  ⟨(realGammaNormalized_distribution a).choose_spec.choose_spec.2.1,
    (realGammaNormalized_distribution a).choose_spec.choose_spec.2.2.2⟩

private theorem complex_family_spec (m : ℤ) :
    Differentiable ℂ (complexWeilNormalizedFamily m) ∧
    ∀ c, complexArchimedeanZetaContinuedCLM complexTamagawaAngularMeasure m =ᶠ[𝓝[≠] c] fun z =>
      Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2) • complexWeilNormalizedFamily m z :=
  ⟨(complexGammaNormalized_distribution m).choose_spec.choose_spec.2.1,
    (complexGammaNormalized_distribution m).choose_spec.choose_spec.2.2.2⟩

private theorem dual_eval_diff {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [ContinuousSMul ℂ V] {A : ℂ → StrongDual ℂ V}
    (hA : Differentiable ℂ A) (f : V) : Differentiable ℂ (fun z => A z f) :=
  fun z => (vectorHolomorphic_hasDerivAt_comp hA.differentiableOn isOpen_univ
    (strongBidualEvaluation f) ⟨z, mem_univ z⟩).differentiableAt

private theorem poleClearingFactor_eventually_ne_zero {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D univ) (hD₁ : D 1 ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, D w ≠ 0 :=
  (hD z (mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun hz => hD₁ (congrFun (hD.eq_of_eventuallyEq (analyticOnNhd_const (v := 0)) hz) 1))

/-- At any regular value of the evaluated zeta integral, normalization
is multiplication by the reciprocal Gamma factor. -/
theorem realWeilNormalizedFamily_of_analyticAt (a : ℕ) (f : 𝓢(ℝ, ℂ)) (z : ℂ)
    (hZ : AnalyticAt ℂ (realArchimedeanZetaContinued a f) z) :
    realArchZetaDenominator a z * realArchimedeanZetaContinued a f z =
      realWeilNormalizedFamily a z f := by
  let D := realArchZetaDenominator a
  have hL : ContinuousAt (fun w => D w * realArchimedeanZetaContinued a f w) z :=
    ((realArchZetaDenominator_analytic a z).mul
      hZ).continuousAt
  have hR : ContinuousAt (fun w => realWeilNormalizedFamily a w f) z :=
    ((strongBidualEvaluation f).continuous.comp (real_family_spec a).1.continuous).continuousAt
  apply ((hL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hR).mp ?_).eq_of_nhds
  have hD₁ : D 1 ≠ 0 :=
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; positivity))
  have hgood := poleClearingFactor_eventually_ne_zero
    (fun w _ => realArchZetaDenominator_analytic a w) hD₁ z
  filter_upwards [(real_family_spec a).2 z, hgood] with w hw hD
  have he := DFunLike.congr_fun hw f
  simp only [realArchimedeanZetaContinuedCLM_apply, smul_apply, smul_eq_mul] at he
  change D w * realArchimedeanZetaContinued a f w = _
  rw [he, ← mul_assoc, show Complex.Gammaℝ (w + ((a % 2 : ℕ) : ℂ)) = (D w)⁻¹ by
    simp [D, realArchZetaDenominator], mul_inv_cancel₀ hD, one_mul]

private theorem real_factor_right (a : ℕ) (f : 𝓢(ℝ, ℂ)) (z : ℂ) (hz : 0 < z.re) :
    realArchZetaDenominator a z * realArchimedeanZetaContinued a f z =
      realWeilNormalizedFamily a z f := by
  have hreg (n : ℕ) : z + n ≠ 0 := fun h => by
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact realWeilNormalizedFamily_of_analyticAt a f z (realArchimedeanZetaContinued_analyticAt a f hreg)

/-- At any regular value of the evaluated zeta integral, normalization
is multiplication by the reciprocal Gamma factor. -/
theorem complexWeilNormalizedFamily_of_analyticAt (m : ℤ) (f : 𝓢(ℂ, ℂ)) (z : ℂ)
    (hZ : AnalyticAt ℂ (complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f) z) :
    complexArchZetaDenominator m z *
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f z =
      complexWeilNormalizedFamily m z f := by
  let D := complexArchZetaDenominator m
  have hL : ContinuousAt (fun w => D w *
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f w) z :=
    ((complexArchZetaDenominator_analytic m z).mul
      hZ).continuousAt
  have hR : ContinuousAt (fun w => complexWeilNormalizedFamily m w f) z :=
    ((strongBidualEvaluation f).continuous.comp (complex_family_spec m).1.continuous).continuousAt
  apply ((hL.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hR).mp ?_).eq_of_nhds
  have hD₁ : D 1 ≠ 0 := by
    let z : ℂ := 1
    have hz : 0 < z.re := by norm_num [z]
    have hreg (n : ℕ) : 2 * z + n ≠ 0 := fun h => by
      have he := congrArg Complex.re h
      simp [Complex.mul_re] at he
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hγ : Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2) ≠ 0 :=
      (complexArchZetaRegular_iff_gamma m z).mp (fun n h => (hreg n h).elim)
    exact inv_ne_zero hγ
  have hgood := poleClearingFactor_eventually_ne_zero
    (fun w _ => complexArchZetaDenominator_analytic m w) hD₁ z
  filter_upwards [(complex_family_spec m).2 z, hgood] with w hw hD
  have he := DFunLike.congr_fun hw f
  simp only [complexArchimedeanZetaContinuedCLM_apply, smul_apply, smul_eq_mul] at he
  change D w * complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f w = _
  rw [he, ← mul_assoc, show Complex.Gammaℂ (w + (m.natAbs : ℂ) / 2) = (D w)⁻¹ by
    simp [D, complexArchZetaDenominator], mul_inv_cancel₀ hD, one_mul]

private theorem complex_factor_right (m : ℤ) (f : 𝓢(ℂ, ℂ)) (z : ℂ) (hz : 0 < z.re) :
    complexArchZetaDenominator m z *
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f z =
      complexWeilNormalizedFamily m z f := by
  have hreg (n : ℕ) : 2 * z + n ≠ 0 := fun h => by
    have he := congrArg Complex.re h
    simp [Complex.mul_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact complexWeilNormalizedFamily_of_analyticAt m f z (complexArchimedeanZetaContinued_analyticAt complexTamagawaAngularMeasure m f hreg)

/-- The pullback by multiplication by the inverse of an archimedean unit. -/
def archSchwartzDilation {K : Type*} [NormedField K] [NormedAlgebra ℝ K] (u : Kˣ) :
    𝓢(K, ℂ) →L[ℂ] 𝓢(K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.unitsEquivAut K u⁻¹).restrictScalars ℝ)

@[simp] theorem archSchwartzDilation_apply {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    (u : Kˣ) (f : 𝓢(K, ℂ)) (x : K) :
    archSchwartzDilation u f x = f (x * (u⁻¹ : Kˣ).val) := rfl

theorem realArchUnitWeight_mul (a : ℕ) (s : ℂ) (u v : ℝˣ) :
    realArchUnitWeight a s (u * v) = realArchUnitWeight a s u * realArchUnitWeight a s v := by
  have hsign :
      (if (u : ℝ) * (v : ℝ) < 0 then (-1 : ℂ) ^ a else 1) =
        (if (u : ℝ) < 0 then (-1 : ℂ) ^ a else 1) *
        (if (v : ℝ) < 0 then (-1 : ℂ) ^ a else 1) := by
    rcases lt_or_gt_of_ne u.ne_zero with hu | hu <;>
      rcases lt_or_gt_of_ne v.ne_zero with hv | hv
    · rw [ite_eq_right (not_lt_of_ge (mul_pos_of_neg_of_neg hu hv).le),
        ite_eq_left hu, ite_eq_left hv, ← mul_pow]
      simp
    · simp only [ite_eq_left (mul_neg_of_neg_of_pos hu hv), ite_eq_left hu,
        ite_eq_right (not_lt_of_ge hv.le), mul_one]
    · simp only [ite_eq_left (mul_neg_of_pos_of_neg hu hv), ite_eq_right (not_lt_of_ge hu.le),
        ite_eq_left hv, one_mul]
    · simp only [ite_eq_right (not_lt_of_ge (mul_pos hu hv).le),
        ite_eq_right (not_lt_of_ge hu.le), ite_eq_right (not_lt_of_ge hv.le), one_mul]
  unfold realArchUnitWeight
  rw [Units.val_mul, abs_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _) s, hsign, mul_mul_mul_comm]

theorem complexArchUnitWeight_mul (m : ℤ) (s : ℂ) (u v : ℂˣ) :
    complexArchUnitWeight m s (u * v) =
      complexArchUnitWeight m s u * complexArchUnitWeight m s v := by
  unfold complexArchUnitWeight
  rw [Units.val_mul, norm_mul, mul_pow,
    show (((‖(u : ℂ)‖ ^ 2 * ‖(v : ℂ)‖ ^ 2 : ℝ) : ℂ)) =
        ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) * ((‖(v : ℂ)‖ ^ 2 : ℝ) : ℂ) from Complex.ofReal_mul _ _,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _) s,
    Complex.ofReal_mul, mul_div_mul_comm, mul_zpow, mul_mul_mul_comm]

private theorem integral_dilate_weight {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    [MeasurableSpace Kˣ] [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (W : Kˣ → ℂ) (hW : ∀ x y, W (x * y) = W x * W y) (u : Kˣ) (f : 𝓢(K, ℂ)) :
    (∫ x, W x * archSchwartzDilation u f x.val ∂μ) =
      W u * ∫ x, W x * f x.val ∂μ := by
  let A (x : Kˣ) := W x * archSchwartzDilation u f x.val
  change (∫ x, A x ∂μ) = _
  rw [← integral_mul_left_eq_self A u, ← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  have hx : (u * x * u⁻¹ : Kˣ) = x := by rw [mul_comm u x, mul_assoc, mul_inv_cancel, mul_one]
  have hv : (u * x).val * u⁻¹.val = x.val := congrArg Units.val hx
  simp only [A, hW, archSchwartzDilation_apply, hv, mul_assoc]

private theorem real_weight_differentiable (a : ℕ) (u : ℝˣ) :
    Differentiable ℂ (fun z => realArchUnitWeight a z u) := by
  letI : NeZero ((|(u : ℝ)| : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (abs_pos.mpr u.ne_zero).ne'⟩
  exact (differentiable_const_cpow_of_neZero _).mul_const _

private theorem complex_weight_differentiable (m : ℤ) (u : ℂˣ) :
    Differentiable ℂ (fun z => complexArchUnitWeight m z u) := by
  letI : NeZero ((‖(u : ℂ)‖ ^ 2 : ℝ) : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr u.ne_zero))⟩
  exact (differentiable_const_cpow_of_neZero _).mul_const _

local instance : MeasurableSpace ℝˣ := borel _
local instance : BorelSpace ℝˣ := ⟨rfl⟩
local instance : MeasurableSpace ℂˣ := borel _
local instance : BorelSpace ℂˣ := ⟨rfl⟩

private theorem right_positive_near_one : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)

/-- The real normalized distribution is equivariant under the full real
multiplicative group, at every spectral parameter. -/
theorem realWeilNormalizedFamily_dilate (a : ℕ) (u : ℝˣ) (f : 𝓢(ℝ, ℂ)) (z : ℂ) :
    realWeilNormalizedFamily a z (archSchwartzDilation u f) =
      realArchUnitWeight a z u * realWeilNormalizedFamily a z f := by
  let N := realWeilNormalizedFamily a
  let g := archSchwartzDilation u f
  have h₁ : AnalyticOnNhd ℂ (fun w => N w g) univ :=
    (dual_eval_diff (real_family_spec a).1 g).differentiableOn.analyticOnNhd isOpen_univ
  have h₂ : AnalyticOnNhd ℂ (fun w => realArchUnitWeight a w u * N w f) univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    exact ((real_weight_differentiable a u).mul (dual_eval_diff (real_family_spec a).1 f)).differentiableOn
  suffices he : (fun w => N w g) =ᶠ[𝓝 (1 : ℂ)] fun w => realArchUnitWeight a w u * N w f
    from congrFun (h₁.eq_of_eventuallyEq h₂ he) z
  filter_upwards [right_positive_near_one] with w hw
  have he : realArchimedeanZetaContinued a g w =
      realArchUnitWeight a w u * realArchimedeanZetaContinued a f w := by
    rw [(realArchimedeanZetaContinued_eq_unitIntegral a g hw).2,
      (realArchimedeanZetaContinued_eq_unitIntegral a f hw).2]
    exact integral_dilate_weight realArchMultiplicativeHaar (realArchUnitWeight a w)
      (realArchUnitWeight_mul a w) u f
  change realWeilNormalizedFamily a w g = _
  rw [← real_factor_right a g w hw, ← real_factor_right a f w hw, he, mul_left_comm]

/-- The complex normalized distribution is equivariant under the full
complex multiplicative group, at every spectral parameter. -/
theorem complexWeilNormalizedFamily_dilate (m : ℤ) (u : ℂˣ) (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    complexWeilNormalizedFamily m z (archSchwartzDilation u f) =
      complexArchUnitWeight m z u * complexWeilNormalizedFamily m z f := by
  let N := complexWeilNormalizedFamily m
  let g := archSchwartzDilation u f
  have h₁ : AnalyticOnNhd ℂ (fun w => N w g) univ :=
    (dual_eval_diff (complex_family_spec m).1 g).differentiableOn.analyticOnNhd isOpen_univ
  have h₂ : AnalyticOnNhd ℂ (fun w => complexArchUnitWeight m w u * N w f) univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    exact ((complex_weight_differentiable m u).mul (dual_eval_diff (complex_family_spec m).1 f)).differentiableOn
  suffices he : (fun w => N w g) =ᶠ[𝓝 (1 : ℂ)] fun w => complexArchUnitWeight m w u * N w f
    from congrFun (h₁.eq_of_eventuallyEq h₂ he) z
  filter_upwards [right_positive_near_one] with w hw
  have he : complexArchimedeanZetaContinued complexTamagawaAngularMeasure m g w =
      complexArchUnitWeight m w u * complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f w := by
    rw [(complexArchimedeanZetaContinued_eq_unitIntegral m g hw).2,
      (complexArchimedeanZetaContinued_eq_unitIntegral m f hw).2]
    exact integral_dilate_weight complexArchMultiplicativeHaar (complexArchUnitWeight m w)
      (complexArchUnitWeight_mul m w) u f
  change complexWeilNormalizedFamily m w g = _
  rw [← complex_factor_right m g w hw, ← complex_factor_right m f w hw, he, mul_left_comm]

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

variable (S : Finset (Place F)) (σ : PontryaginDual (SLocalThetaNormOne F S))
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]

private abbrev a := sLocalRealArchParameters F S σ
private abbrev j := sLocalComplexArchParameters F S σ
private abbrev χ := sLocalFiniteZetaPhases F S σ

private abbrev unitMass (v : S) : ℂ := (μ v.val).real (finitePlaceIntegralUnits F v.val)

omit [∀ v : Place F, SigmaFinite (μ v)] in
private theorem local_finite_factor_eq (v : S) (g : locallyConstantTests (v.val.adicCompletion F))
    (z : ℂ) :
    finiteProductClearedLocal F S (fun v ↦ μ v.val) (χ F S σ) v g z =
      unitMass F S μ v * finiteWeilNormalizedDistribution F v.val (μ v.val) (χ F S σ v) z g := by
  have hn : unitMass F S μ v ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ v.val)).ne'
  unfold finiteProductClearedLocal finiteWeilNormalizedDistribution
  split_ifs
  all_goals
    change _ = unitMass F S μ v * ((unitMass F S μ v)⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    rfl

private def archTensor (f : RealPlaces F → 𝓢(ℝ, ℂ))
    (g : ComplexPlaces F → 𝓢(ℂ, ℂ)) (z : ℂ) : ℂ :=
  (∏ i, realWeilNormalizedFamily (a F S σ i).2 (z + (a F S σ i).1) (f i)) *
    ∏ i, complexWeilNormalizedFamily (j F S σ i).2 (z + (j F S σ i).1) (g i)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ] in
private theorem archTensor_right (φ : Arch F) (f : RealPlaces F → 𝓢(ℝ, ℂ))
    (g : ComplexPlaces F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : mixedEmbedding.mixedSpace F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (z : ℂ) (hz : 0 < z.re) :
    archimedeanNumberFieldZetaDenominator F (a F S σ) (j F S σ) z *
      archimedeanNumberFieldZeta F complexTamagawaAngularMeasure (a F S σ) (j F S σ) z φ =
      archTensor F S σ f g z := by
  have har (i : RealPlaces F) : 0 < (z + (a F S σ i).1).re := by
    simpa only [a, Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  have hcr (i : ComplexPlaces F) : 0 < (z + (j F S σ i).1).re := by
    simpa only [j, Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz
  rw [archimedeanNumberFieldZeta_separated F _ _ φ f g hφ z har hcr]
  unfold archimedeanNumberFieldZetaDenominator archTensor
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ real_factor_right _ _ _ (har i)
  · exact Finset.prod_congr rfl fun i _ ↦ complex_factor_right _ _ _ (hcr i)

/-- At every exponent, the entire numerator on an archimedean and finite
separated test is the product of the individually normalized local values,
with the finite integral-unit masses retained. -/
theorem sLocalEulerNormalizedMellin_separated_eval
    (φ : Arch F) (f : RealPlaces F → 𝓢(ℝ, ℂ)) (g : ComplexPlaces F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : mixedEmbedding.mixedSpace F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (k : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)) (z : ℂ) :
    sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) σ
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)) z =
      archTensor F S σ f g z * ∏ v : S, unitMass F S μ v *
        finiteWeilNormalizedDistribution F v.val (μ v.val) (χ F S σ v) z (k v) := by
  let P := sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)
  let A := sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) σ P
  let B (w : ℂ) := archTensor F S σ f g w * ∏ v : S, unitMass F S μ v *
    finiteWeilNormalizedDistribution F v.val (μ v.val) (χ F S σ v) w (k v)
  have ha : AnalyticOnNhd ℂ A univ := sLocalEulerNormalizedMellin_entire F S _ σ P
  have hb : AnalyticOnNhd ℂ B univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    apply Differentiable.differentiableOn
    unfold B archTensor
    apply Differentiable.mul
    · apply Differentiable.mul <;> apply Differentiable.fun_finsetProd <;> intro i _
      · exact (dual_eval_diff (real_family_spec _).1 (f i)).comp (differentiable_id.add_const _)
      · exact (dual_eval_diff (complex_family_spec _).1 (g i)).comp (differentiable_id.add_const _)
    · apply Differentiable.fun_finsetProd
      intro i _
      exact (differentiableOn_univ.mp
        (finiteWeilNormalizedDistribution_analytic F i.val (μ i.val) (χ F S σ i) (k i)).differentiableOn).const_mul _
  suffices h : A =ᶠ[𝓝 (1 : ℂ)] B from congrFun (ha.eq_of_eventuallyEq hb h) z
  apply ((ha 1 trivial).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hb 1 trivial).continuousAt).mp
  have hpos : ∀ᶠ w : ℂ in 𝓝[≠] (1 : ℂ), 0 < w.re :=
    (show ∀ᶠ w : ℂ in 𝓝 (1 : ℂ), 0 < w.re from
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)).filter_mono
        nhdsWithin_le_nhds
  filter_upwards [sLocalEulerNormalizedMellin_pure_germ F μ S σ φ k (1 : ℂ), hpos] with w hw hp
  change A w = _ at hw
  rw [hw]
  exact congrArg₂ (· * ·) (archTensor_right F S σ φ f g hφ w hp)
    (Finset.prod_congr rfl fun i _ ↦ local_finite_factor_eq F S σ μ i (k i) w)

local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private def stageUnitMass (S : Finset (Place F)) : ℂ := ∏ v : S, unitMass F S μ v

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem stageUnitMass_ne_zero (S : Finset (Place F)) : stageUnitMass F μ S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ =>
    Complex.ofReal_ne_zero.mpr (finiteZetaUnitMass_pos F v.val (μ v.val)).ne'

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem stageUnitMass_pad {S T : Finset (Place F)} (h : S ⊆ T) :
    stageUnitMass F μ T = sLocalMellinPaddingHaarMass F μ S T * stageUnitMass F μ S := by
  unfold stageUnitMass sLocalMellinPaddingHaarMass
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : T ↦ v.val ∈ S)]
  let e : {v : T // v.val ∈ S} ≃ S :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      invFun := fun v => ⟨⟨v.val, h v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.prod_equiv e
    (fun v => unitMass F T μ v.val) (fun v => unitMass F S μ v) (fun _ => rfl)
  rw [he, mul_comm]

/-- The normalized stage numerator uses local distributions of unit
reference value, so its finite Haar masses are divided out. -/
def normalizedStageWeilMellin (ω : PontryaginDual (normOneIdeleClass F))
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (f : sLocalBruhatImage F S) (z : ℂ) : ℂ :=
  (stageUnitMass F μ S)⁻¹ * sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
    (sLocalNormOneCharacterOfGlobal F ω S hs hu) f z

/-- The unit-normalized stage numerator is unchanged when unramified
integer-ring factors are inserted at additional places. -/
theorem normalizedStageWeilMellin_pad (ω : PontryaginDual (normOneIdeleClass F))
    {S T : Finset (Place F)} (hST : S ⊆ T)
    (hs : Surjective (sIdeleClassInclusion F S)) (ht : Surjective (sIdeleClassInclusion F T))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : sLocalBruhatImage F S) (z : ℂ) :
    normalizedStageWeilMellin F μ ω T ht huT (sLocalBruhatTransition F hST f) z =
      normalizedStageWeilMellin F μ ω S hs hu f z := by
  unfold normalizedStageWeilMellin
  have he := sLocalEulerNormalizedMellin_global_pad F ω S hs hu μ hST ht huT f z
  change sLocalEulerNormalizedMellin F T _ _ _ z = _ at he
  rw [he, stageUnitMass_pad F μ hST, mul_inv]
  calc
    _ = (sLocalMellinPaddingHaarMass F μ S T)⁻¹ * sLocalMellinPaddingHaarMass F μ S T *
        ((stageUnitMass F μ S)⁻¹ * sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
          (sLocalNormOneCharacterOfGlobal F ω S hs hu) f z) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ (sLocalMellinPaddingHaarMass_ne_zero F μ (S := S) (T := T)), one_mul]

/-- Product of the unit-normalized archimedean factors for a separated tensor. -/
def sLocalNormalizedArchWeilTensor
    (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : RealPlaces F → 𝓢(ℝ, ℂ)) (g : ComplexPlaces F → 𝓢(ℂ, ℂ)) (z : ℂ) : ℂ :=
  archTensor F S ω f g z

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- On separated tests the unit-normalized stage numerator is the exact
product of the chosen local unit-normalized distributions. -/
theorem normalizedStageWeilMellin_separated_eval
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (φ : Arch F) (f : RealPlaces F → 𝓢(ℝ, ℂ)) (g : ComplexPlaces F → 𝓢(ℂ, ℂ))
    (hφ : ∀ x : mixedEmbedding.mixedSpace F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v))
    (k : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)) (z : ℂ) :
    let τ := sLocalNormOneCharacterOfGlobal F ω S hs hu
    normalizedStageWeilMellin F μ ω S hs hu (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)) z =
      sLocalNormalizedArchWeilTensor F S τ f g z *
        ∏ v : S, finiteWeilNormalizedDistribution F v.val (μ v.val) (χ F S τ v) z (k v) := by
  intro τ
  rw [normalizedStageWeilMellin,
    sLocalEulerNormalizedMellin_separated_eval F S τ μ φ f g hφ k z, Finset.prod_mul_distrib]
  change (stageUnitMass F μ S)⁻¹ * (archTensor F S τ f g z * (stageUnitMass F μ S *
    ∏ v : S, finiteWeilNormalizedDistribution F v.val (μ v.val) (χ F S τ v) z (k v))) = _
  rw [mul_left_comm (archTensor F S τ f g z), ← mul_assoc (stageUnitMass F μ S)⁻¹,
    inv_mul_cancel₀ (stageUnitMass_ne_zero F μ S), one_mul]
  rfl

/-- A single scalar relates the normalized global family to the
unit-normalized numerators on all admissible stages. -/
theorem globalNormalizedHeckeFamily_compatible_stages
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (hEq : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (Δ : ℂ → StrongDual ℂ (GlobalBruhat F)) (hΔ : Continuous Δ)
    (hfac : ∀ c, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] c] fun z => L z • Δ z) :
    ∃ B : ℂ, B ≠ 0 ∧ ∀ (T : Finset (Place F))
      (ht : Surjective (sIdeleClassInclusion F T))
      (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
      (f : sLocalBruhatImage F T) (z : ℂ),
      Δ z f.val = B * normalizedStageWeilMellin F μ ω T ht huT f z := by
  have htwo : meromorphicOrderAt L (2 : ℂ) ≠ ⊤ := by
    intro he
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hbad : ∀ᶠ z in 𝓝[≠] (2 : ℂ), False := by
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, meromorphicOrderAt_eq_top_iff.mp he]
        with z hz hz₀
      exact globalCompletedHeckeEuler_ne_zero F ω S hs hu hz ((hEq hz).symm.trans hz₀)
    exact hbad.exists.choose_spec
  have hfinite (z : ℂ) : meromorphicOrderAt L z ≠ ⊤ :=
    hL.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2 : ℂ)) (mem_univ z) htwo
  let unramified (T : Finset (Place F)) :=
    globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))
  let scale (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
      (huT : unramified T) (B : ℂ) :=
    ∀ (f : sLocalBruhatImage F T) (z : ℂ),
      Δ z f.val = B * normalizedStageWeilMellin F μ ω T ht huT f z
  have hex (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
      (huT : unramified T) : ∃ B : ℂ, B ≠ 0 ∧ scale T ht huT B := by
    have he := globalCompletedHeckeEuler_stage_eq F ω S hs hu T ht huT
    obtain ⟨r, C, hC, hr, _, _⟩ := exists_globalMellin_order_reference F η ω T ht huT μ ν hν
    obtain ⟨B, hB, hBT⟩ := globalNormalizedHeckeFamily_stage F ν ω η μ hν T ht huT L hL
      hfinite (he ▸ hEq) Δ hΔ hfac r C hC hr
    have hm := stageUnitMass_ne_zero F μ T
    refine ⟨B * stageUnitMass F μ T, mul_ne_zero hB hm, fun f z => ?_⟩
    rw [hBT f z, normalizedStageWeilMellin, mul_assoc, ← mul_assoc (stageUnitMass F μ T),
      mul_inv_cancel₀ hm, one_mul]
  have uniq {U T : Finset (Place F)} (hUT : U ⊆ T)
      {hU : Surjective (sIdeleClassInclusion F U)} {hT : Surjective (sIdeleClassInclusion F T)}
      {huU : unramified U} {huT : unramified T} {A B : ℂ}
      (hA : scale U hU huU A) (hB : scale T hT huT B) : A = B := by
    obtain ⟨r, C, hC, hr, _, _⟩ := exists_globalMellin_order_reference F η ω U hU huU μ ν hν
    have hne : normalizedStageWeilMellin F μ ω U hU huU r 0 ≠ 0 := by
      change sLocalEulerNormalizedMellin F U (fun v ↦ μ v.val)
        (sLocalNormOneCharacterOfGlobal F ω U hU huU) r = _ at hr
      unfold normalizedStageWeilMellin
      rw [congrFun hr 0]
      exact mul_ne_zero (inv_ne_zero (stageUnitMass_ne_zero F μ U)) hC
    have he := (hA r 0).symm.trans (hB (sLocalBruhatTransition F hUT r) 0)
    rw [normalizedStageWeilMellin_pad F μ ω hUT hU hT huU huT r 0] at he
    exact mul_right_cancel₀ hne he
  obtain ⟨B, hB, hS⟩ := hex S hs hu
  refine ⟨B, hB, fun T ht huT => ?_⟩
  let U := S ∪ T
  have hSU : S ⊆ U := Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_right
  have hU : Surjective (sIdeleClassInclusion F U) := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk (sIdeleTransition F hSU g), rfl⟩
  have huU : unramified U := (mem_sUnramified_iff F U _).mpr fun v hv u =>
    (mem_sUnramified_iff F S _).mp hu v (fun h => hv (hSU h)) u
  obtain ⟨D, _, hD⟩ := hex U hU huU
  obtain ⟨C, _, hC⟩ := hex T ht huT
  have hBC : B = C := (uniq hSU hS hD).trans (uniq hTU hC hD).symm
  rw [hBC]
  exact hC

/-- The normalized global family evaluates as the product of the individual
local normalized values on every admissible separated stage, with one
nonzero scalar common to the stages. -/
theorem globalNormalizedHeckeFamily_separated_eval
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (ν : Measure (normOneIdeleClass F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (hEq : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (Δ : ℂ → StrongDual ℂ (GlobalBruhat F)) (hΔ : Continuous Δ)
    (hfac : ∀ c, globalContinuedMellinEval F ν ω =ᶠ[𝓝[≠] c] fun z => L z • Δ z) :
    ∃ B : ℂ, B ≠ 0 ∧ ∀ (T : Finset (Place F))
      (ht : Surjective (sIdeleClassInclusion F T))
      (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))),
      let τ := sLocalNormOneCharacterOfGlobal F ω T ht huT
      ∀ (φ : Arch F) (f : RealPlaces F → 𝓢(ℝ, ℂ)) (g : ComplexPlaces F → 𝓢(ℂ, ℂ)),
        (∀ x : mixedEmbedding.mixedSpace F, φ x = (∏ v, f v (x.1 v)) * ∏ v, g v (x.2 v)) →
        ∀ (k : ∀ v : T, locallyConstantTests (v.val.adicCompletion F)) (z : ℂ),
          Δ z (sLocalBruhatPure F T φ (locallyConstantTestPiProduct k)).val =
            B * (archTensor F T τ f g z *
              ∏ v : T, finiteWeilNormalizedDistribution F v.val (μ v.val) (χ F T τ v) z (k v)) := by
  obtain ⟨B, hB, he⟩ := globalNormalizedHeckeFamily_compatible_stages F S μ η ν hν ω
    hs hu L hL hEq Δ hΔ hfac
  refine ⟨B, hB, ?_⟩
  intro T ht huT τ φ f g hφ k z
  rw [he T ht huT, normalizedStageWeilMellin_separated_eval F T μ ω ht huT φ f g hφ k z]
  rfl

end

end Masullo
