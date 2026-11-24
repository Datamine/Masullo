import FiniteLocalAdditiveFourier
import LocalMultiplicativeHaar
import LocallyConstantTests
import PontryaginAnnihilators
import PontryaginDuality

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

/-- Compactly supported locally constant functions have an open neighborhood
of translations that fix the entire function. -/
theorem locallyConstant_compactSupport_periods {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] {f : A → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    {u : A | ∀ x, f (x + u) = f x} ∈ 𝓝 (0 : A) := by
  let C := tsupport f
  let E : Set (A × A) := {z | f (z.1 + z.2) = f z.1}
  have hE : IsOpen E := by
    rw [show E = ⋃ c : ℂ, ((fun z : A × A ↦ z.1 + z.2) ⁻¹' {x | f x = c}) ∩
      (Prod.fst ⁻¹' {x | f x = c}) from by
      ext z
      simp only [E, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
      exact ⟨fun h ↦ ⟨f z.1, h, rfl⟩, fun ⟨c, h, hc⟩ ↦ h.trans hc.symm⟩]
    exact isOpen_iUnion fun c ↦ (hf.isOpen_fiber c |>.preimage
      (continuous_fst.add continuous_snd)).inter ((hf.isOpen_fiber c).preimage continuous_fst)
  obtain ⟨U, V, -, hV, hCU, h0V, hUV⟩ :=
    generalized_tube_lemma (show IsCompact C from hc)
      (isCompact_singleton (x := (0 : A))) hE (by
        rintro ⟨x, u⟩ ⟨_, hu⟩
        have h : u = 0 := mem_singleton_iff.mp hu
        simp [E, h])
  have hV₀ := hV.mem_nhds (h0V (mem_singleton 0))
  have hneg : {u : A | -u ∈ V} ∈ 𝓝 0 :=
    (show Tendsto (fun u : A ↦ -u) (𝓝 0) (𝓝 0) by
      simpa only [neg_zero] using (continuous_neg.continuousAt (x := (0 : A))).tendsto) hV₀
  filter_upwards [hV₀, hneg] with u hu hnu
  intro x
  by_cases hx : x ∈ C
  · exact hUV (show (x, u) ∈ U ×ˢ V from ⟨hCU hx, hu⟩)
  by_cases hxu : x + u ∈ C
  · have h : f ((x + u) + -u) = f (x + u) :=
      hUV (show (x + u, -u) ∈ U ×ˢ V from ⟨hCU hxu, hnu⟩)
    simpa only [add_neg_cancel_right] using h.symm
  exact (image_eq_zero_of_notMem_tsupport hxu).trans (image_eq_zero_of_notMem_tsupport hx).symm

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local notation "K" => v.adicCompletion F
local notation "O" => v.adicCompletionIntegers F
local notation "D" => finitePlaceIntegerAnnihilator F v
local notation "ψ" => finitePlaceTraceCharacter F v

local instance : LocallyCompactSpace K := finitePlace_locallyCompact F v
local instance : SecondCountableTopology K := finitePlace_secondCountable F v

private theorem integer_mem_iff_norm_le_one (x : K) : x ∈ O ↔ ‖x‖ ≤ 1 := by
  have hq : (1 : ℝ≥0) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def]
  exact (WithZeroMulInt.toNNReal_le_one_iff hq).symm

/-- A dilation of the integer ring is the closed ball of radius equal to the
absolute value of the dilating unit. -/
theorem finitePlaceIntegral_dilate_eq_ball (a : Kˣ) : a • (O : Set K) = {y : K | ‖y‖ ≤ ‖a.val‖} := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change (a⁻¹).val * x ∈ O ↔ ‖x‖ ≤ ‖a.val‖
  rw [integer_mem_iff_norm_le_one, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
  simpa only [mul_one] using (inv_mul_le_iff₀ (norm_pos_iff.mpr a.ne_zero) (a := (1 : ℝ)) (b := ‖x‖))

private theorem exists_conductor_dilate : ∃ d : Kˣ, D = d • (O : Set K) := by
  obtain ⟨n, hn⟩ := finitePlaceIntegerAnnihilator_eq_ball F v
  refine ⟨chosenFiniteUniformizer F v ^ n, ?_⟩
  rw [hn, finitePlaceIntegral_dilate_eq_ball, Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_zpow, zpow_neg]

theorem exists_small_integral_dilate {U : Set K} (hU : U ∈ 𝓝 (0 : K)) :
    ∃ a : Kˣ, a • (O : Set K) ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  let π := chosenFiniteUniformizer F v
  have hπ : ‖π.val‖ < 1 := by
    rw [norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π.val) hπ
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  refine ⟨π ^ n, ?_⟩
  rw [finitePlaceIntegral_dilate_eq_ball, Units.val_pow_eq_pow_val, norm_pow]
  intro x hx
  exact hsub (by simpa only [Metric.mem_ball, dist_zero_right] using hx.trans_lt hn)

section Haar

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
  (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

/-- A Fourier coefficient vanishes if a period of the test has nontrivial pairing
with the Fourier variable. -/
theorem finitePlaceTraceFourier_eq_zero_of_period {f : K → ℂ} (u y : K)
    (hu : ∀ x, f (x + u) = f x) (hy : ψ (u * y) ≠ 0) :
    finitePlaceTraceFourier F v ν f y = 0 := by
  let w (x : K) := f x * ((ψ (x * y)).toMul : ℂ)
  let c : ℂ := (ψ (u * y)).toMul
  have hc : c ≠ 1 := fun h ↦ hy (Additive.toMul.injective
    (Circle.coe_injective (h.trans Circle.coe_one.symm)))
  have hw (x : K) : w (x + u) = w x * c := by
    simp only [w, c, hu, add_mul, map_add, mul_assoc]
    rfl
  have he : (∫ x, w x ∂ν) = (∫ x, w x ∂ν) * c := by
    rw [← integral_mul_const, ← integral_add_right_eq_self (μ := ν) w u]
    exact integral_congr_ae (.of_forall hw)
  exact (mul_eq_mul_left_iff.mp ((mul_one _).trans he)).resolve_left (by simpa only [ne_comm] using hc)

private theorem traceFourier_continuous (f : locallyConstantTests K) :
    Continuous (finitePlaceTraceFourier F v ν f.val) := by
  let χ (z : K) : ℂ := (ψ z).toMul
  have hc : Continuous χ := continuous_subtype_val.comp (finitePlaceTraceCharacter_continuous F v)
  unfold finitePlaceTraceFourier
  apply continuous_of_dominated (bound := fun x : K ↦ ‖f.val x‖)
  · intro y
    exact (f.property.1.continuous.mul (hc.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  · intro y
    refine .of_forall fun x ↦ ?_
    change ‖f.val x * χ (x * y)‖ ≤ ‖f.val x‖
    rw [norm_mul, show ‖χ (x * y)‖ = 1 from Circle.norm_coe _, mul_one]
  · exact (f.property.1.continuous.integrable_of_hasCompactSupport f.property.2 (μ := ν)).norm
  · exact .of_forall fun x ↦ continuous_const.mul (hc.comp (continuous_const.mul continuous_id))

private theorem traceFourier_support (f : locallyConstantTests K) (a : Kˣ)
    (ha : a • (O : Set K) ⊆ {u | ∀ x, f.val (x + u) = f.val x}) :
    support (finitePlaceTraceFourier F v ν f.val) ⊆ a⁻¹ • D := by
  intro y hy
  rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
  change ∀ x ∈ O, ψ (x * (a.val * y)) = 0
  intro x hx
  by_contra hn
  have hxy : ψ ((a.val * x) * y) ≠ 0 := by simpa only [mul_assoc, mul_left_comm a.val x] using hn
  have hu : ∀ t, f.val (t + a.val * x) = f.val t := ha
    (mem_smul_set.mpr ⟨x, hx, rfl⟩)
  exact hy (finitePlaceTraceFourier_eq_zero_of_period F v ν _ _ hu hxy)

/-- Fourier transformation of a compact locally constant finite-place test is
continuous and supported inside a compact valuation ball. -/
theorem finitePlaceTraceFourier_compact (f : locallyConstantTests K) :
    Continuous (finitePlaceTraceFourier F v ν f.val) ∧
      HasCompactSupport (finitePlaceTraceFourier F v ν f.val) := by
  obtain ⟨a, ha⟩ := exists_small_integral_dilate F v
    (locallyConstant_compactSupport_periods f.property.1 f.property.2)
  obtain ⟨d, hd⟩ := exists_conductor_dilate F v
  refine ⟨traceFourier_continuous F v ν f, ?_⟩
  have hC : IsCompact (a⁻¹ • D) := by
    rw [hd]
    exact (finitePlaceIntegral_compact F v |>.image
      (continuous_const.mul continuous_id : Continuous fun x : K ↦ d.val * x)).image
      (continuous_const.mul continuous_id : Continuous fun x : K ↦ (a⁻¹).val * x)
  exact HasCompactSupport.intro hC
    (fun _ hx ↦ notMem_support.mp fun h ↦ hx (traceFourier_support F v ν f a ha h))

omit [BorelSpace K] [ν.IsAddHaarMeasure] in
/-- Fourier transformation preserves local constancy on finite-place tests. -/
theorem finitePlaceTraceFourier_locallyConstant (f : locallyConstantTests K) :
    IsLocallyConstant (finitePlaceTraceFourier F v ν f.val) := by
  let C := tsupport f.val
  let E : Set (K × K) := {p | ψ (p.1 * p.2) = 0}
  have hE : IsOpen E := (finitePlaceTraceCharacter_kernel_open F v).preimage
    (continuous_fst.mul continuous_snd)
  obtain ⟨U, V, -, hV, hCU, h0V, hUV⟩ := generalized_tube_lemma
    (show IsCompact C from f.property.2) (isCompact_singleton (x := (0 : K))) hE (by
      rintro ⟨x, t⟩ ⟨_, ht⟩
      have ht₀ : t = 0 := mem_singleton_iff.mp ht
      simp [E, ht₀])
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hV' : ∀ᶠ z in 𝓝 y, z - y ∈ V := by
    have ht : Tendsto (fun z : K ↦ z - y) (𝓝 y) (𝓝 0) := by
      have hc : Continuous (fun z : K ↦ z - y) := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc.continuousAt (x := y)).tendsto
    exact ht.eventually (hV.mem_nhds (h0V (mem_singleton 0)))
  filter_upwards [hV'] with z hz
  unfold finitePlaceTraceFourier
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change f.val x * ((ψ (x * z)).toMul : ℂ) = f.val x * ((ψ (x * y)).toMul : ℂ)
  by_cases hx : x ∈ C
  · have ht : ψ (x * (z - y)) = 0 := by
      change (x, z - y) ∈ E
      exact hUV ⟨hCU hx, hz⟩
    rw [mul_sub, map_sub, sub_eq_zero] at ht
    exact congrArg (fun w : Additive Circle ↦ f.val x * (w.toMul : ℂ)) ht
  · rw [image_eq_zero_of_notMem_tsupport (f := f.val) hx, zero_mul, zero_mul]

/-- The finite-place Fourier transform on the actual compact locally constant tests. -/
def finitePlaceFourierTest (f : locallyConstantTests K) : locallyConstantTests K :=
  ⟨finitePlaceTraceFourier F v ν f.val, finitePlaceTraceFourier_locallyConstant F v ν f,
    (finitePlaceTraceFourier_compact F v ν f).2⟩

omit [MeasurableSpace K] [BorelSpace K] in
private def dilatedIntegers (b : Kˣ) : AddSubgroup K :=
  (O).toAddSubgroup.map (AddMonoidHom.mulLeft b.val)

omit [MeasurableSpace K] [BorelSpace K] in
private theorem dilatedIntegers_coe (b : Kˣ) :
    (dilatedIntegers F v b : Set K) = b • (O : Set K) := rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem dilatedIntegers_compact (b : Kˣ) : IsCompact (dilatedIntegers F v b : Set K) := by
  rw [dilatedIntegers_coe]
  exact (finitePlaceIntegral_compact F v).image (continuous_const.mul continuous_id)

omit [MeasurableSpace K] [BorelSpace K] in
private theorem annihilator_dilate_integers (b : Kˣ) :
    {x | ∀ y ∈ (dilatedIntegers F v b : Set K), ψ (y * x) = 0} = b⁻¹ • D := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
  change (∀ y ∈ dilatedIntegers F v b, ψ (y * x) = 0) ↔
    ∀ y ∈ O, ψ (y * (b.val * x)) = 0
  constructor
  · intro h y hy
    exact (by
      have h' := h (b.val * y) ⟨y, hy, rfl⟩
      simpa only [mul_assoc, mul_left_comm b.val y] using h')
  · rintro h _ ⟨y, hy, rfl⟩
    change ψ ((b.val * y) * x) = 0
    simpa only [mul_assoc, mul_left_comm b.val y] using h y hy

private theorem finitePlace_measureReal_dilate (a : Kˣ) (S : Set K) :
    ν.real (a • S) = ‖a.val‖ * ν.real S := by
  rw [measureReal_def, finitePlace_addHaar_smul F v ν a, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_nnnorm, measureReal_def]

omit [BorelSpace K] [ν.IsAddHaarMeasure] in
private theorem integral_traceFourier_at_zero (f : K → ℂ) :
    finitePlaceTraceFourier F v ν f 0 = ∫ x, f x ∂ν := by
  unfold finitePlaceTraceFourier
  simp [Circle.coe_one]

/-- Fourier inversion at zero for every compact locally constant test.
The required normalization is the product of the integer ring and conductor
masses, which equals one for the standard local additive Tamagawa measure. -/
theorem integral_finitePlaceTraceFourier (f : locallyConstantTests K)
    (hν : ν.real (O : Set K) * ν.real D = 1) :
    (∫ y, finitePlaceTraceFourier F v ν f.val y ∂ν) = f.val 0 := by
  obtain ⟨a, ha⟩ := exists_small_integral_dilate F v
    (locallyConstant_compactSupport_periods f.property.1 f.property.2)
  obtain ⟨d, hd⟩ := exists_conductor_dilate F v
  let b := a⁻¹ * d
  let P := dilatedIntegers F v a
  let Q := dilatedIntegers F v b
  have hQ : (Q : Set K) = a⁻¹ • D := by
    rw [dilatedIntegers_coe, hd, smul_smul]
  have hP : (P : Set K) = a • (O : Set K) := dilatedIntegers_coe F v a
  have hQc : IsCompact (Q : Set K) := dilatedIntegers_compact F v b
  have hQm : MeasurableSet (Q : Set K) := hQc.measurableSet
  have hPm : MeasurableSet (P : Set K) := (dilatedIntegers_compact F v a).measurableSet
  have hAnn : {x | ∀ y ∈ (Q : Set K), ψ (y * x) = 0} = (P : Set K) := by
    rw [annihilator_dilate_integers, hd, hP, smul_smul]
    have he : b⁻¹ * d = a := by simp [b]
    rw [he]
  have hmass : ν.real (Q : Set K) * ν.real (P : Set K) = 1 := by
    rw [hQ, hP, finitePlace_measureReal_dilate, finitePlace_measureReal_dilate,
      Units.val_inv_eq_inv_val, norm_inv]
    have ha₀ : ‖a.val‖ ≠ 0 := norm_ne_zero_iff.mpr a.ne_zero
    calc
      _ = (‖a.val‖⁻¹ * ‖a.val‖) * (ν.real (O : Set K) * ν.real D) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ ha₀, hν, mul_one]
  let k : K → K → ℂ := fun x y ↦ f.val x * ((ψ (x * y)).toMul : ℂ)
  have hk : Continuous (uncurry k) := by
    have hc : Continuous (fun z : K ↦ ((ψ z).toMul : ℂ)) :=
      continuous_subtype_val.comp (finitePlaceTraceCharacter_continuous F v)
    exact (f.property.1.continuous.comp continuous_fst).mul
      (hc.comp (continuous_fst.mul continuous_snd))
  have hf : Integrable f.val ν := f.property.1.continuous.integrable_of_hasCompactSupport f.property.2
  letI : IsFiniteMeasure (ν.restrict (Q : Set K)) := ⟨by simpa using hQc.measure_lt_top (μ := ν)⟩
  have hki : Integrable (uncurry k) (ν.prod (ν.restrict (Q : Set K))) := by
    apply (integrable_prod_iff hk.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun x ↦ ?_, ?_⟩
    · exact (integrable_const ‖f.val x‖).mono'
        (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (.of_forall fun y ↦ by
          change ‖f.val x * ((ψ (x * y)).toMul : ℂ)‖ ≤ ‖f.val x‖
          rw [norm_mul, Circle.norm_coe, mul_one])
    · simp only [k, uncurry, norm_mul, Circle.norm_coe, mul_one, integral_const, smul_eq_mul]
      exact hf.norm.const_mul _
  have hsect (x : K) : (∫ y in (Q : Set K), ((ψ (x * y)).toMul : ℂ) ∂ν) =
      (ν.real (Q : Set K) : ℂ) * (P : Set K).indicator (fun _ ↦ 1) x := by
    have h := congrFun (finitePlaceTraceFourier_subgroup F v ν Q hQm) x
    change _ = (ν.real (Q : Set K) : ℂ) *
      {x | ∀ y ∈ (Q : Set K), ψ (y * x) = 0}.indicator (fun _ ↦ 1) x at h
    rw [hAnn] at h
    rw [← h]
    unfold finitePlaceTraceFourier
    rw [← integral_indicator hQm]
    apply integral_congr_ae
    refine .of_forall fun y ↦ ?_
    let χ (z : K) : ℂ := (ψ z).toMul
    change (Q : Set K).indicator (fun z ↦ χ (x * z)) y =
      (Q : Set K).indicator (fun _ ↦ (1 : ℂ)) y * χ (y * x)
    by_cases hy : y ∈ (Q : Set K)
    · rw [indicator_of_mem hy, indicator_of_mem hy, one_mul, mul_comm x y]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
  have hf0 : ∀ x ∈ (P : Set K), f.val x = f.val 0 := by
    intro x hx
    simpa only [zero_add] using ha (hP ▸ hx) 0
  calc
    (∫ y, finitePlaceTraceFourier F v ν f.val y ∂ν) =
        ∫ y in (Q : Set K), finitePlaceTraceFourier F v ν f.val y ∂ν := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      apply notMem_support.mp
      exact fun h ↦ hy (hQ ▸ traceFourier_support F v ν f a ha h)
    _ = ∫ x, ∫ y in (Q : Set K), k x y ∂ν ∂ν :=
      (integral_integral_swap hki).symm
    _ = (ν.real (Q : Set K) : ℂ) * (ν.real (P : Set K) : ℂ) * f.val 0 := by
      simp_rw [k, integral_const_mul, hsect]
      simp_rw [show ∀ x : K, f.val x * ((ν.real (Q : Set K) : ℂ) *
          (P : Set K).indicator (fun _ ↦ 1) x) =
          (ν.real (Q : Set K) : ℂ) * (P : Set K).indicator f.val x from fun x ↦ by
          by_cases hx : x ∈ (P : Set K) <;> simp [hx, mul_comm]]
      rw [integral_const_mul, integral_indicator hPm, setIntegral_congr_fun hPm hf0,
        setIntegral_const, Complex.real_smul, mul_assoc]
    _ = _ := by rw [← Complex.ofReal_mul, hmass, Complex.ofReal_one, one_mul]

theorem finitePlace_measure_singleton_zero : ν ({0} : Set K) = 0 := by
  let π := chosenFiniteUniformizer F v
  have hp : ‖π.val‖ < 1 := by
    rw [norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hs : π • ({0} : Set K) = ({0} : Set K) := by simp
  have h := finitePlace_measureReal_dilate F v ν π {0}
  rw [hs] at h
  have he : ν.real ({0} : Set K) = 0 := by
    by_contra hne
    have hm := mul_right_cancel₀ hne (show 1 * ν.real ({0} : Set K) =
      ‖π.val‖ * ν.real ({0} : Set K) by simpa only [one_mul] using h)
    linarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp he).resolve_right
    ((isCompact_singleton (x := (0 : K))).measure_lt_top (μ := ν)).ne

/-- The normalized logarithm in B.4.3.1, with an arbitrary value at zero
given by Lean's convention for the real logarithm. -/
def finiteNormalizedLog (x : K) : ℝ :=
  Real.log ‖x‖ / Real.log (v.asIdeal.absNorm : ℝ)

private theorem finiteNormalizedLog_measurable : Measurable (finiteNormalizedLog F v) :=
  (Real.measurable_log.comp continuous_norm.measurable).div_const _

private theorem finiteNormalizedLog_integrableOn_integers :
    IntegrableOn (finiteNormalizedLog F v) (O : Set K) ν := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let π := chosenFiniteUniformizer F v
  let U (n : ℕ) : Set K := π ^ n • (O : Set K)
  have hU (n : ℕ) : MeasurableSet (U n) := (dilatedIntegers_compact F v (π ^ n)).measurableSet
  have hnorm (n : ℕ) : ‖((π ^ n : Kˣ) : K)‖ = q⁻¹ ^ n := by
    rw [Units.val_pow_eq_pow_val, norm_pow,
      norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)]
  let w (n : ℕ) := (U n).indicator (fun _ ↦ (n : ℝ≥0∞))
  have hw (n : ℕ) : Measurable (w n) := measurable_const.indicator (hU n)
  have hbound (x : K) : ‖(O : Set K).indicator (finiteNormalizedLog F v) x‖ₑ ≤ ∑' n, w n x := by
    by_cases hx : x ∈ (O : Set K)
    · rw [indicator_of_mem hx]
      by_cases hz : x = 0
      · subst x; simp [finiteNormalizedLog]
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ‖x‖ = q ^ (-k) :=
        iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) (Units.mk0 x hz)
      have hk₀ : 0 ≤ k := by
        have ht := (integer_mem_iff_norm_le_one F v x).mp hx
        rw [hk, ← zpow_zero q] at ht
        exact neg_nonpos.mp ((zpow_le_zpow_iff_right₀ hq).mp ht)
      let n := k.toNat
      have hn : (n : ℤ) = k := Int.toNat_of_nonneg hk₀
      have hnorm' : ‖x‖ = q⁻¹ ^ n := by
        rw [hk, ← hn, zpow_neg, zpow_natCast, inv_pow]
      have hxU : x ∈ U n := by
        change x ∈ π ^ n • (O : Set K)
        rw [finitePlaceIntegral_dilate_eq_ball, hnorm]
        exact hnorm'.le
      have hlog : finiteNormalizedLog F v x = -(n : ℝ) := by
        unfold finiteNormalizedLog
        rw [hnorm', Real.log_pow, Real.log_inv, div_eq_iff (Real.log_pos hq).ne']
        ring
      rw [hlog, enorm_neg, Real.enorm_natCast, ← show w n x = (n : ℝ≥0∞) from indicator_of_mem hxU _]
      exact ENNReal.le_tsum n
    · rw [indicator_of_notMem hx, enorm_zero]
      exact zero_le
  have hsum : (∑' n : ℕ, ∫⁻ x, w n x ∂ν) < ∞ := by
    have hmass (n : ℕ) : ∫⁻ x, w n x ∂ν =
        (n : ℝ≥0∞) * ((‖π.val‖₊ : ℝ≥0∞) ^ n) * ν (O : Set K) := by
      unfold w
      rw [lintegral_indicator_const (hU n)]
      change (n : ℝ≥0∞) * ν (π ^ n • (O : Set K)) = _
      rw [finitePlace_addHaar_smul F v ν,
        Units.val_pow_eq_pow_val, nnnorm_pow, ENNReal.coe_pow, mul_assoc]
    simp_rw [hmass, ENNReal.tsum_mul_right]
    have hp : ‖(‖π.val‖ : ℝ)‖ < 1 := by
      rw [norm_norm, norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)]
      exact inv_lt_one_of_one_lt₀ hq
    apply ENNReal.mul_lt_top _ (finitePlaceIntegral_compact F v).measure_lt_top
    apply lt_top_iff_ne_top.mpr
    simp only [← ENNReal.coe_natCast, ← ENNReal.coe_pow, ← ENNReal.coe_mul]
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, coe_nnnorm, pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hp)
  rw [← integrable_indicator_iff ((finitePlaceIntegral_compact F v).measurableSet)]
  refine ⟨((finiteNormalizedLog_measurable F v).indicator
    ((finitePlaceIntegral_compact F v).measurableSet)).aestronglyMeasurable, ?_⟩
  exact ((lintegral_mono hbound).trans_eq (lintegral_tsum fun n ↦ (hw n).aemeasurable)).trans_lt hsum

theorem finiteNormalizedLog_integrableOn_compact (C : Set K) (hC : IsCompact C) :
    IntegrableOn (finiteNormalizedLog F v) C ν := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨R, hR⟩ := (hC.image continuous_norm).bddAbove
  let R₀ := max 1 R
  let B := Real.log R₀ / Real.log q
  have hB : 0 ≤ B := div_nonneg (Real.log_nonneg (le_max_left ..)) (Real.log_pos hq).le
  let O₀ : Set K := O
  have hO : MeasurableSet O₀ := (finitePlaceIntegral_compact F v).measurableSet
  letI : IsFiniteMeasure (ν.restrict C) := ⟨by simpa using hC.measure_lt_top (μ := ν)⟩
  have hI : Integrable (O₀.indicator (finiteNormalizedLog F v)) (ν.restrict C) := by
    exact ((integrable_indicator_iff hO).mpr
      (finiteNormalizedLog_integrableOn_integers F v ν)).mono_measure (Measure.restrict_le_self)
  refine (hI.norm.add (integrable_const B)).mono' (finiteNormalizedLog_measurable F v).aestronglyMeasurable ?_
  refine (ae_restrict_mem hC.measurableSet).mono fun x hx ↦ ?_
  by_cases hxo : x ∈ O₀
  · rw [Pi.add_apply, indicator_of_mem hxo]
    exact le_add_of_nonneg_right hB
  have h1 : 1 < ‖x‖ := lt_of_not_ge fun h ↦ hxo ((integer_mem_iff_norm_le_one F v x).mpr h)
  have hle : ‖x‖ ≤ R₀ := (hR ⟨x, hx, rfl⟩).trans (le_max_right ..)
  rw [Pi.add_apply, indicator_of_notMem hxo, norm_zero, zero_add]
  change ‖Real.log ‖x‖ / Real.log q‖ ≤ B
  rw [Real.norm_of_nonneg (div_nonneg (Real.log_nonneg h1.le) (Real.log_pos hq).le)]
  exact div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans h1) hle) (Real.log_pos hq).le

/-- Additive translation of a test multiplies its Fourier transform by a character. -/
theorem finitePlaceTraceFourier_addTranslate (f : K → ℂ) (x y : K) :
    finitePlaceTraceFourier F v ν (fun t ↦ f (t + -x)) y =
      finitePlaceTraceFourier F v ν f y * ((ψ (y * x)).toMul : ℂ) := by
  let w (t : K) := f (t + -x) * ((ψ (t * y)).toMul : ℂ)
  change (∫ t, w t ∂ν) = _
  rw [← integral_add_right_eq_self (μ := ν) w x]
  unfold finitePlaceTraceFourier
  rw [← integral_mul_const]
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  change f (t + x + -x) * ((ψ ((t + x) * y)).toMul : ℂ) =
    f t * ((ψ (t * y)).toMul : ℂ) * ((ψ (y * x)).toMul : ℂ)
  rw [add_neg_cancel_right]
  have he : ((ψ ((t + x) * y)).toMul : ℂ) =
      ((ψ (t * y)).toMul : ℂ) * ((ψ (y * x)).toMul : ℂ) := by
    rw [add_mul, mul_comm x y, map_add]
    rfl
  rw [he, mul_assoc]
/-- Fourier inversion on the full finite-place test space for the positive
sign convention. -/
theorem finitePlaceFourierTest_twice (hν : ν.real (O : Set K) * ν.real D = 1)
    (f : locallyConstantTests K) (x : K) :
    (finitePlaceFourierTest F v ν (finitePlaceFourierTest F v ν f)).val x = f.val (-x) := by
  let e := Homeomorph.addRight (-x)
  let g : locallyConstantTests K :=
    ⟨f.val ∘ e, f.property.1.comp_continuous e.continuous, f.property.2.comp_homeomorph e⟩
  have h (y : K) : finitePlaceTraceFourier F v ν g.val y =
      finitePlaceTraceFourier F v ν f.val y * ((ψ (y * x)).toMul : ℂ) :=
    finitePlaceTraceFourier_addTranslate F v ν f.val x y
  change (∫ y, finitePlaceTraceFourier F v ν f.val y * ((ψ (y * x)).toMul : ℂ) ∂ν) = f.val (-x)
  rw [← show g.val 0 = f.val (-x) from congrArg f.val (zero_add (-x))]
  rw [← integral_finitePlaceTraceFourier F v ν g hν]
  exact integral_congr_ae (.of_forall fun y ↦ (h y).symm)

theorem finitePlace_map_unit_mul (a : Kˣ) :
    ν.map (fun x : K ↦ a.val * x) = (‖(a⁻¹).val‖₊ : ℝ≥0) • ν := by
  ext S hS
  have ham : Measurable (fun x : K ↦ a.val * x) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply ham hS, Measure.smul_apply]
  have he : (fun x : K ↦ a.val * x) ⁻¹' S = a⁻¹ • S := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  rw [he, finitePlace_addHaar_smul F v ν]
  rfl

private theorem integral_finitePlace_unit_mul (a : Kˣ) (g : K → ℂ) :
    (∫ x : K, g (a.val * x) ∂ν) = ‖a.val‖⁻¹ • (∫ y, g y ∂ν) := by
  let e : K ≃ᵐ K := MeasurableEquiv.smul a
  have he : (e : K → K) = fun x ↦ a.val * x := rfl
  calc
    _ = ∫ y, g y ∂ν.map e := (integral_map_equiv e g).symm
    _ = _ := by
      rw [he, finitePlace_map_unit_mul F v ν, integral_smul_nnreal_measure]
      change ‖(a⁻¹).val‖ • (∫ y, g y ∂ν) = _
      rw [Units.val_inv_eq_inv_val, norm_inv]

theorem finitePlace_integrable_mul_traceCharacter (f : locallyConstantTests K) (y : K) :
    Integrable (fun x : K ↦ f.val x * ((ψ (x * y)).toMul : ℂ)) ν := by
  refine ((f.property.1.continuous.integrable_of_hasCompactSupport f.property.2
    (μ := ν)).norm).mono' ?_ ?_
  · exact (f.property.1.continuous.mul (continuous_subtype_val.comp
      ((finitePlaceTraceCharacter_continuous F v).comp
        (continuous_id.mul continuous_const)))).aestronglyMeasurable
  · exact .of_forall fun x ↦ by simp only [norm_mul, Circle.norm_coe, mul_one, le_refl]

theorem finitePlaceTraceFourier_sub (f g : locallyConstantTests K) (y : K) :
    finitePlaceTraceFourier F v ν (f - g).val y =
      finitePlaceTraceFourier F v ν f.val y - finitePlaceTraceFourier F v ν g.val y := by
  unfold finitePlaceTraceFourier
  change (∫ x, (f.val x - g.val x) * _ ∂ν) = _
  simp only [sub_mul]
  exact integral_sub (finitePlace_integrable_mul_traceCharacter F v ν f y)
    (finitePlace_integrable_mul_traceCharacter F v ν g y)

/-- Fourier transformation converts inverse dilation of the test to forward
dilation of the Fourier variable with the additive Haar Jacobian. -/
theorem finitePlaceTraceFourier_dilate (a : Kˣ) (f : K → ℂ) (y : K) :
    finitePlaceTraceFourier F v ν (fun x ↦ f (a.val⁻¹ * x)) y =
      ‖a.val‖ • finitePlaceTraceFourier F v ν f (a.val * y) := by
  let g (x : K) := f x * ((ψ (x * (a.val * y))).toMul : ℂ)
  calc
    _ = ∫ x, g ((a⁻¹).val * x) ∂ν := by
      unfold finitePlaceTraceFourier
      apply integral_congr_ae
      refine .of_forall fun x ↦ ?_
      have he : (a⁻¹).val * x * (a.val * y) = x * y := by
        rw [Units.val_inv_eq_inv_val, mul_assoc, mul_left_comm x a.val y, ← mul_assoc,
          inv_mul_cancel₀ a.ne_zero, one_mul]
      change f (a.val⁻¹ * x) * ((ψ (x * y)).toMul : ℂ) =
        f ((a⁻¹).val * x) * ((ψ ((a⁻¹).val * x * (a.val * y))).toMul : ℂ)
      exact congrArg₂ (fun t z : K ↦ f t * ((ψ z).toMul : ℂ))
        (congrArg (· * x) (Units.val_inv_eq_inv_val a).symm) he.symm
    _ = _ := by
      rw [integral_finitePlace_unit_mul F v ν, Units.val_inv_eq_inv_val, norm_inv, inv_inv]
      rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem finiteNormalizedLog_inv_mul (a : Kˣ) {x : K} (hx : x ≠ 0) :
    finiteNormalizedLog F v (a.val⁻¹ * x) = finiteNormalizedLog F v x - finiteNormalizedLog F v a.val := by
  unfold finiteNormalizedLog
  rw [norm_mul, norm_inv, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.mpr a.ne_zero))
    (norm_ne_zero_iff.mpr hx), Real.log_inv, add_div, neg_div]
  abel

private theorem traceFourier_log_integrable (f : locallyConstantTests K) :
    Integrable (fun y ↦ (finiteNormalizedLog F v y : ℂ) * finitePlaceTraceFourier F v ν f.val y) ν := by
  let g := finitePlaceTraceFourier F v ν f.val
  obtain ⟨hg, hgc⟩ := finitePlaceTraceFourier_compact F v ν f
  let C := tsupport g
  have hC : IsCompact C := hgc
  obtain ⟨B, hB⟩ := (hC.image hg.norm).bddAbove
  let B₀ := max 0 B
  have hI : IntegrableOn (fun y ↦ (finiteNormalizedLog F v y : ℂ) * g y) C ν := by
    refine ((finiteNormalizedLog_integrableOn_compact F v ν C hC).norm.const_mul B₀).mono'
      (((Complex.continuous_ofReal.measurable.comp (finiteNormalizedLog_measurable F v)).mul
        hg.measurable).aestronglyMeasurable) ?_
    refine (ae_restrict_mem hC.measurableSet).mono fun x hx ↦ ?_
    rw [norm_mul, Complex.norm_real, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hB ⟨x, hx, rfl⟩).trans (le_max_right ..)) (norm_nonneg _)
  have h := (integrable_indicator_iff hC.measurableSet).mpr hI
  refine h.congr (.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ C
  · exact indicator_of_mem hy _
  · rw [indicator_of_notMem hy]
    change 0 = (finiteNormalizedLog F v y : ℂ) * g y
    rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- Scaling the additive character in the normalized logarithmic Fourier
pairing contributes the logarithm of its multiplier times evaluation at zero. -/
theorem finitePlace_logFourier_changeCharacter (hν : ν.real (O : Set K) * ν.real D = 1)
    (a : Kˣ) (f : locallyConstantTests K) :
    ‖a.val‖ • (∫ y, (finiteNormalizedLog F v y : ℂ) *
      finitePlaceTraceFourier F v ν f.val (a.val * y) ∂ν) =
    (∫ y, (finiteNormalizedLog F v y : ℂ) * finitePlaceTraceFourier F v ν f.val y ∂ν) -
      (finiteNormalizedLog F v a.val : ℂ) * f.val 0 := by
  let h := finitePlaceTraceFourier F v ν f.val
  let g (y : K) := (finiteNormalizedLog F v (a.val⁻¹ * y) : ℂ) * h y
  let q (y : K) := (finiteNormalizedLog F v y : ℂ) * h y
  have hh : Integrable h ν := (finitePlaceTraceFourier_compact F v ν f).1.integrable_of_hasCompactSupport
    (finitePlaceTraceFourier_compact F v ν f).2
  have he : g =ᵐ[ν] fun y ↦ q y - (finiteNormalizedLog F v a.val : ℂ) * h y := by
    have hzero : ∀ᵐ y ∂ν, y ≠ (0 : K) := ae_iff.mpr (by
      simpa only [not_not, ofPred_eq_eq_singleton] using finitePlace_measure_singleton_zero F v ν)
    filter_upwards [hzero] with y hy
    dsimp only [g, q]
    rw [finiteNormalizedLog_inv_mul F v a hy, Complex.ofReal_sub, sub_mul]
  have heq (y : K) : g (a.val * y) = (finiteNormalizedLog F v y : ℂ) * h (a.val * y) := by
    dsimp only [g]
    rw [inv_mul_cancel_left₀ a.ne_zero]
  calc
    _ = ‖a.val‖ • (∫ y, g (a.val * y) ∂ν) := by
      congr 1
      apply integral_congr_ae
      exact .of_forall fun y ↦ (heq y).symm
    _ = ∫ y, g y ∂ν := by
      rw [integral_finitePlace_unit_mul F v ν, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr a.ne_zero), one_smul]
    _ = (∫ y, q y ∂ν) - (finiteNormalizedLog F v a.val : ℂ) * f.val 0 := by
      rw [integral_congr_ae he, integral_sub (traceFourier_log_integrable F v ν f)
        (hh.const_mul _), integral_const_mul, integral_finitePlaceTraceFourier F v ν f hν]

/-- Formula (B.4.3.4), evaluating the logarithmic Fourier pairing on the
left-translated test. -/
theorem finitePlace_logFourier_dilate (hν : ν.real (O : Set K) * ν.real D = 1)
    (a : Kˣ) (f : locallyConstantTests K) :
    (∫ y, (finiteNormalizedLog F v y : ℂ) *
      finitePlaceTraceFourier F v ν (fun x ↦ f.val (a.val⁻¹ * x)) y ∂ν) =
    (∫ y, (finiteNormalizedLog F v y : ℂ) * finitePlaceTraceFourier F v ν f.val y ∂ν) -
      (finiteNormalizedLog F v a.val : ℂ) * f.val 0 := by
  simp only [finitePlaceTraceFourier_dilate F v ν, mul_smul_comm, integral_smul]
  exact finitePlace_logFourier_changeCharacter F v ν hν a f

variable [MeasurableSpace (v.adicCompletion F)ˣ]

/-- The additive Connes principal value for the character `y ↦ ψ (a.val * y)`.
The two additive Haar factors of `√‖a.val‖` give the scalar `‖a.val‖`. -/
def finiteConnesPrincipalValue (μ : Measure Kˣ) (a : Kˣ) (f : locallyConstantTests K) : ℂ :=
  -(μ.real (finitePlaceIntegralUnits F v) : ℂ) *
    (‖a.val‖ • ∫ y, (finiteNormalizedLog F v y : ℂ) *
      finitePlaceTraceFourier F v ν f.val (a.val * y) ∂ν)

/-- Lemma B.4.4.4(1) for a rescaling of the standard additive character. -/
theorem finiteConnesPrincipalValue_changeCharacter
    (hν : ν.real (O : Set K) * ν.real D = 1)
    (μ : Measure Kˣ) (a : Kˣ) (f : locallyConstantTests K) :
    finiteConnesPrincipalValue F v ν μ a f = finiteConnesPrincipalValue F v ν μ 1 f +
      f.val 0 * (μ.real (finitePlaceIntegralUnits F v) : ℂ) *
        (finiteNormalizedLog F v a.val : ℂ) := by
  unfold finiteConnesPrincipalValue
  rw [finitePlace_logFourier_changeCharacter F v ν hν]
  simp only [Units.val_one, norm_one, one_smul, one_mul]
  ring

end Haar

private theorem finitePlaceTracePairing_continuous :
    Continuous (fun p : Multiplicative K × Multiplicative K ↦
      (ψ (p.1.toAdd * p.2.toAdd)).toMul) :=
  (finitePlaceTraceCharacter_continuous F v).comp
    (continuous_fst.mul continuous_snd : Continuous fun p : K × K ↦ p.1 * p.2)

private def finitePlaceTraceDualAt (x : Multiplicative K) : PontryaginDual (Multiplicative K) where
  toFun y := (ψ (x.toAdd * y.toAdd)).toMul
  map_one' := by change (ψ (x.toAdd * 0)).toMul = 1; rw [mul_zero, map_zero]; rfl
  map_mul' y z := by
    change (ψ (x.toAdd * (y.toAdd + z.toAdd))).toMul = _
    rw [mul_add, map_add]; rfl
  continuous_toFun := by
    change Continuous (fun y : K ↦ ψ (x.toAdd * y))
    exact (finitePlaceTraceCharacter_continuous F v).comp (continuous_const.mul continuous_id)

/-- The trace pairing, viewed as a map from the additive local field to its
Pontryagin dual. -/
def finitePlaceTraceDual : Multiplicative K →ₜ* PontryaginDual (Multiplicative K) := by
  refine
    { toFun := finitePlaceTraceDualAt F v
      map_one' := PontryaginDual.ext fun y ↦ by
        change (ψ (0 * y.toAdd)).toMul = 1; rw [zero_mul, map_zero]; rfl
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change (ψ ((x.toAdd + y.toAdd) * z.toAdd)).toMul = _
        rw [add_mul, map_add]; rfl
      continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry
        (finitePlaceTraceDualAt F v) (finitePlaceTracePairing_continuous F v) }

theorem finitePlaceTraceDual_apply (x y : Multiplicative K) :
    finitePlaceTraceDual F v x y = (ψ (x.toAdd * y.toAdd)).toMul := rfl

private theorem finitePlaceTraceDual_detects {x : Multiplicative K} (hx : x ≠ 1) :
    ∃ y : Multiplicative K, finitePlaceTraceDual F v x y ≠ 1 := by
  obtain ⟨z, hz⟩ := finitePlaceTraceCharacter_nontrivial F v
  have hx₀ : x.toAdd ≠ 0 := hx
  refine ⟨Multiplicative.ofAdd (z / x.toAdd), ?_⟩
  rw [finitePlaceTraceDual_apply]
  change (ψ (x.toAdd * (z / x.toAdd))).toMul ≠ 1
  rw [mul_comm, div_mul_cancel₀ z hx₀]
  exact hz

private theorem finitePlaceTraceDual_closedEmbedding :
    IsClosedEmbedding (finitePlaceTraceDual F v) := by
  let G := Multiplicative K
  let e := finitePlaceTraceDual F v
  have hInjective : Injective e := by
    intro x y h
    by_contra hxy
    obtain ⟨z, hz⟩ := finitePlaceTraceDual_detects F v (div_ne_one.mpr hxy)
    apply hz
    change (e (x / y)) z = 1
    simp only [map_div, h, div_self', PontryaginDual.one_apply]
  have hInducing : IsInducing e := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto e (𝓝 (1 : G)) (𝓝 (e 1)) := e.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨a, ha⟩ := exists_small_integral_dilate F v (show (U : Set K) ∈ 𝓝 (0 : K) from hU)
      obtain ⟨d, hd⟩ := exists_conductor_dilate F v
      let b := a⁻¹ * d
      let H : Subgroup G := (dilatedIntegers F v b).toSubgroup
      have hH : IsCompact (H : Set G) := dilatedIntegers_compact F v b
      let V := lcaAnnihilator H
      refine Filter.mem_comap.mpr ⟨(V : Set (PontryaginDual G)),
        (isOpen_lcaAnnihilator H hH).mem_nhds V.one_mem, ?_⟩
      intro x hx
      have hAnn : {x | ∀ y ∈ (dilatedIntegers F v b : Set K), ψ (y * x) = 0} =
          a • (O : Set K) := by
        rw [annihilator_dilate_integers, hd, smul_smul]
        congr 1
        simp [b]
      apply ha
      rw [← hAnn]
      intro y hy
      have he := (mem_lcaAnnihilator_iff H _).mp hx ⟨Multiplicative.ofAdd y, hy⟩
      change (ψ (x.toAdd * y)).toMul = 1 at he
      rw [mul_comm] at he
      exact he
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : UniformSpace (PontryaginDual G) := IsTopologicalGroup.rightUniformSpace _
  let : IsUniformGroup G := isUniformGroup_of_commGroup
  let : IsUniformGroup (PontryaginDual G) := isUniformGroup_of_commGroup
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  exact (MonoidHom.isUniformEmbedding_of_isEmbedding (f := e)
    ⟨hInducing, hInjective⟩).isClosedEmbedding

/-- Every nontrivial continuous additive character of the completion is the
trace character with a unique nonzero scalar multiplier. -/
theorem finitePlaceTraceDual_existsUnique_unit
    (χ : PontryaginDual (Multiplicative K)) (hχ : χ ≠ 1) :
    ∃! a : Kˣ, ∀ y : K, χ (Multiplicative.ofAdd y) = (ψ (a.val * y)).toMul := by
  let G := Multiplicative K
  let e := finitePlaceTraceDual F v
  have hEmb := finitePlaceTraceDual_closedEmbedding F v
  let R := e.toMonoidHom.range
  have hR : IsClosed (R : Set (PontryaginDual G)) := hEmb.isClosed_range
  have hsurj : Surjective e := by
    intro τ
    by_contra hτ
    have hne : τ ∉ R := hτ
    have hRA : lcaDualAnnihilator (lcaAnnihilator R) = R :=
      lcaDualAnnihilator_annihilator R hR
    rw [← hRA, mem_lcaDualAnnihilator_iff] at hne
    push Not at hne
    obtain ⟨η, hη⟩ := hne
    obtain ⟨y, hy⟩ := pontryaginBidualEval_surjective η.val
    have hy₀ : y ≠ (1 : G) := by
      intro he
      apply hη
      rw [← hy, pontryaginBidualEval_apply, he, map_one]
    obtain ⟨x, hx⟩ := finitePlaceTraceDual_detects F v hy₀
    apply hx
    have he := (mem_lcaAnnihilator_iff R η.val).mp η.property
      ⟨e x, ⟨x, rfl⟩⟩
    rw [← hy, pontryaginBidualEval_apply] at he
    change finitePlaceTraceDual F v x y = 1 at he
    rw [finitePlaceTraceDual_apply, mul_comm] at he
    simpa only [finitePlaceTraceDual_apply] using he
  obtain ⟨x, hx⟩ := hsurj χ
  have hx₀ : x.toAdd ≠ 0 := by
    intro hz
    have h : x = (1 : G) := hz
    exact hχ (by rw [← hx, h, map_one])
  let a := Units.mk0 x.toAdd hx₀
  refine ⟨a, fun y ↦ ?_, fun b hb ↦ ?_⟩
  · rw [← hx]
    rfl
  · apply Units.ext
    have he : e (Multiplicative.ofAdd b.val) = e x := by
      rw [hx]
      exact PontryaginDual.ext fun y ↦ (hb y.toAdd).symm
    exact congrArg Multiplicative.toAdd (hEmb.injective he)

theorem finiteUnitNorm_locallyConstant : IsLocallyConstant (fun u : Kˣ ↦ ‖u.val‖) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u
  have h₁ : (1 : Kˣ) ∈ finitePlaceIntegralUnits F v := by
    rw [localIntegralUnits_value]; simp
  have hU := (localIntegralUnits_open F v).preimage
    (continuous_const.mul continuous_id : Continuous fun t : Kˣ ↦ u⁻¹ * t)
  have hu : u ∈ (fun t : Kˣ ↦ u⁻¹ * t) ⁻¹' finitePlaceIntegralUnits F v := by
    change u⁻¹ * u ∈ finitePlaceIntegralUnits F v
    rwa [inv_mul_cancel]
  filter_upwards [hU.mem_nhds hu] with t ht
  have he : ‖(u⁻¹ * t).val‖ = 1 := by
    change u⁻¹ * t ∈ finitePlaceIntegralUnits F v at ht
    rw [FinitePlace.norm_def, (localIntegralUnits_value F v _).mp ht, map_one, NNReal.coe_one]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    inv_mul_eq_div, div_eq_iff (norm_ne_zero_iff.mpr u.ne_zero), one_mul] at he
  exact he

private def finiteWeilTestFun (f : locallyConstantTests Kˣ) (x : K) : ℂ := by
  classical
  exact if h : 1 + x ≠ 0 then
    (↑(‖1 + x‖ ^ (-1 / 2 : ℝ)) : ℂ) * f.val (Units.mk0 (1 + x) h)
  else 0

private theorem finiteWeilTestFun_sub_one (f : locallyConstantTests Kˣ) (u : Kˣ) :
    finiteWeilTestFun F v f (u.val - 1) =
      (↑(‖u.val‖ ^ (-1 / 2 : ℝ)) : ℂ) * f.val u := by
  have hju : 1 + (u.val - 1) = u.val := by ring
  have hz : 1 + (u.val - 1) ≠ 0 := fun h ↦ u.ne_zero (hju.symm.trans h)
  unfold finiteWeilTestFun
  rw [dite_eq_left hz]
  rw [show Units.mk0 (1 + (u.val - 1)) _ = u from Units.ext hju, hju]

/-- Translate the weighted multiplicative test to the additive line and
extend it by zero at the missing point `-1`. -/
def finiteWeilTest (f : locallyConstantTests Kˣ) : locallyConstantTests K := by
  let j : Kˣ → K := fun u ↦ u.val - 1
  have hj : IsOpenEmbedding j := by
    have he := (Homeomorph.addRight (-1 : K)).isOpenEmbedding.comp
        (IsOpenUnits.isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Kˣ → K))
    change IsOpenEmbedding (fun u : Kˣ ↦ u.val + -1) at he
    simpa only [j, sub_eq_add_neg] using he
  let C := j '' tsupport f.val
  have hC : IsCompact C := f.property.2.image hj.continuous
  have hfun (u : Kˣ) : finiteWeilTestFun F v f (j u) =
      (↑(‖u.val‖ ^ (-1 / 2 : ℝ)) : ℂ) * f.val u := finiteWeilTestFun_sub_one F v f u
  have hzero (x : K) (hx : x ∉ C) : finiteWeilTestFun F v f x = 0 := by
    by_cases h : 1 + x = 0
    · simp [finiteWeilTestFun, h]
    let u := Units.mk0 (1 + x) h
    have hju : j u = x := by change 1 + x - 1 = x; ring
    have hu : u ∉ tsupport f.val := fun hu ↦ hx ⟨u, hu, hju⟩
    rw [← hju, hfun, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨finiteWeilTestFun F v f, ?_, HasCompactSupport.intro hC hzero⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases h : 1 + x = 0
  · have hx : x ∉ C := by
      rintro ⟨u, -, rfl⟩
      exact u.ne_zero (by calc
        u.val = 1 + j u := by dsimp [j]; ring
        _ = 0 := h)
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact (hzero y hy).trans (hzero x hx).symm
  · let u := Units.mk0 (1 + x) h
    have hju : j u = x := by change 1 + x - 1 = x; ring
    rw [← hju, ← hj.map_nhds_eq u]
    change ∀ᶠ t in 𝓝 u, finiteWeilTestFun F v f (j t) = finiteWeilTestFun F v f (j u)
    simp only [hfun]
    exact (IsLocallyConstant.iff_eventually_eq _).mp
      (((finiteUnitNorm_locallyConstant F v).comp (fun r : ℝ ↦ (↑(r ^ (-1 / 2 : ℝ)) : ℂ))).mul
        f.property.1) u

@[simp] theorem finiteWeilTest_zero (f : locallyConstantTests Kˣ) :
    (finiteWeilTest F v f).val 0 = f.val 1 := by
  change finiteWeilTestFun F v f 0 = _
  simp [finiteWeilTestFun, Units.mk0_one]

theorem finiteWeilTest_sub_one (f : locallyConstantTests Kˣ) (u : Kˣ) :
    (finiteWeilTest F v f).val (u.val - 1) =
      (↑(‖u.val‖ ^ (-1 / 2 : ℝ)) : ℂ) * f.val u := finiteWeilTestFun_sub_one F v f u

@[simp] theorem finiteWeilTest_neg_one (f : locallyConstantTests Kˣ) :
    (finiteWeilTest F v f).val (-1) = 0 := by
  change finiteWeilTestFun F v f (-1) = 0
  simp [finiteWeilTestFun]

section Tamagawa

variable [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)]
  [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)]

/-- The product of the Tamagawa masses of the integer ring and its annihilator. -/
theorem finitePlace_tamagawa_fourier_normalization :
    (additiveHaarDifferent F v).real (O : Set K) * (additiveHaarDifferent F v).real D = 1 := by
  let ν := additiveHaarDifferent F v
  letI := additiveHaarDifferent_isHaar F v
  let n : ℤ := -(multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hn : D = {y : K | ‖y‖ ≤ q ^ (-n)} := by
    simpa only [n, neg_neg, zpow_natCast] using finitePlaceIntegerAnnihilator_eq_differentBall F v
  let a := chosenFiniteUniformizer F v ^ n
  have ha : ‖a.val‖ = q ^ (-n) := finitePlaceUniformizer_norm_zpow F v n
  have hD : D = a • (O : Set K) := by rw [hn, finitePlaceIntegral_dilate_eq_ball, ha]
  change ν.real (O : Set K) * ν.real D = 1
  have hm : ν.real (O : Set K) = Real.exp ((n : ℝ) / 2 * Real.log q) := by
    simpa only [n, Int.cast_neg, Int.cast_natCast] using additiveHaarDifferent_conductor_mass F v
  have hp : q ^ (-n) = Real.exp (Real.log q * -(n : ℝ)) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hq, Int.cast_neg]
  rw [hD, finitePlace_measureReal_dilate F v ν, ha, hm, hp, ← Real.exp_add, ← Real.exp_add]
  rw [← Real.exp_zero]
  congr 1
  ring

variable [MeasurableSpace (v.adicCompletion F)ˣ]

/-- The principal value for a character with its scaled additive measure,
written as the iterated integral in (B.4.4.12). -/
def finiteConnesPrincipalValueIntegral
    (μ : Measure Kˣ) (ν : Measure K) (χ : PontryaginDual (Multiplicative K))
    (f : locallyConstantTests K) : ℂ :=
  -(μ.real (finitePlaceIntegralUnits F v) : ℂ) *
    ∫ y, (finiteNormalizedLog F v y : ℂ) *
      (∫ x, f.val x * (χ (Multiplicative.ofAdd (x * y)) : ℂ) ∂ν) ∂ν

theorem finiteConnesPrincipalValue_eq_integral
    (μ : Measure Kˣ) (a : Kˣ) (f : locallyConstantTests K) :
    finiteConnesPrincipalValue F v (additiveHaarDifferent F v) μ a f =
      finiteConnesPrincipalValueIntegral F v μ
        ((Real.sqrt ‖a.val‖).toNNReal • additiveHaarDifferent F v)
        (finitePlaceTraceDual F v (Multiplicative.ofAdd a.val)) f := by
  let ν := additiveHaarDifferent F v
  let c := (Real.sqrt ‖a.val‖).toNNReal
  unfold finiteConnesPrincipalValue finiteConnesPrincipalValueIntegral
  change _ = -(μ.real (finitePlaceIntegralUnits F v) : ℂ) *
    ∫ y, (finiteNormalizedLog F v y : ℂ) *
      (∫ x, f.val x * ((ψ (a.val * (x * y))).toMul : ℂ) ∂(c • ν)) ∂(c • ν)
  simp only [integral_smul_nnreal_measure]
  congr 1
  have hinner (y : K) : (∫ x, f.val x * ((ψ (a.val * (x * y))).toMul : ℂ) ∂ν) =
      finitePlaceTraceFourier F v ν f.val (a.val * y) := by
    unfold finitePlaceTraceFourier
    apply integral_congr_ae
    refine .of_forall fun x ↦ ?_
    exact congrArg (fun z : K ↦ f.val x * ((ψ z).toMul : ℂ)) (mul_left_comm a.val x y)
  simp only [hinner, mul_smul_comm]
  change ‖a.val‖ • _ = (c : ℝ) • ∫ y, (c : ℝ) •
    ((finiteNormalizedLog F v y : ℂ) * finitePlaceTraceFourier F v ν f.val (a.val * y)) ∂ν
  rw [integral_smul, smul_smul]
  rw [show (c : ℝ) * c = ‖a.val‖ by
    simp only [c, Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.mul_self_sqrt (norm_nonneg _)]]

/-- The Weil principal value on a finite-place multiplicative test. -/
def finiteWeilPrincipalValue (μ : Measure Kˣ) (a : Kˣ) (f : locallyConstantTests Kˣ) : ℂ :=
  finiteConnesPrincipalValue F v (additiveHaarDifferent F v) μ a (finiteWeilTest F v f)

/-- Lemma B.4.4.4(2) for a rescaling of the standard additive character. -/
theorem finiteWeilPrincipalValue_changeCharacter
    (μ : Measure Kˣ) (a : Kˣ) (f : locallyConstantTests Kˣ) :
    finiteWeilPrincipalValue F v μ a f = finiteWeilPrincipalValue F v μ 1 f +
      f.val 1 * (μ.real (finitePlaceIntegralUnits F v) : ℂ) *
        (finiteNormalizedLog F v a.val : ℂ) := by
  letI := additiveHaarDifferent_isHaar F v
  simpa only [finiteWeilPrincipalValue, finiteWeilTest_zero] using
    finiteConnesPrincipalValue_changeCharacter F v (additiveHaarDifferent F v)
      (finitePlace_tamagawa_fourier_normalization F v) μ a (finiteWeilTest F v f)

/-- Lemma B.4.4.4 for every nontrivial continuous additive character, with the
character-dependent Haar factors included in the evaluation. -/
theorem finitePlace_principalValues_changeCharacter
    (μ : Measure Kˣ) (χ : PontryaginDual (Multiplicative K)) (hχ : χ ≠ 1) :
    ∃ a : Kˣ,
      (∀ y : K, χ (Multiplicative.ofAdd y) = (ψ (a.val * y)).toMul) ∧
      (∀ b : Kˣ, (∀ y : K, χ (Multiplicative.ofAdd y) = (ψ (b.val * y)).toMul) → b = a) ∧
      let ν := additiveHaarDifferent F v
      let νχ := (Real.sqrt ‖a.val‖).toNNReal • ν
      let pv := finiteConnesPrincipalValueIntegral F v μ νχ χ
      let coefficient := (μ.real (finitePlaceIntegralUnits F v) : ℂ) *
        (finiteNormalizedLog F v a.val : ℂ)
      (∀ f : locallyConstantTests K,
        pv f = finiteConnesPrincipalValue F v ν μ 1 f + f.val 0 * coefficient) ∧
      (∀ f : locallyConstantTests Kˣ,
        pv (finiteWeilTest F v f) = finiteWeilPrincipalValue F v μ 1 f + f.val 1 * coefficient) := by
  obtain ⟨a, ha, huniq⟩ := finitePlaceTraceDual_existsUnique_unit F v χ hχ
  letI := additiveHaarDifferent_isHaar F v
  have he : χ = finitePlaceTraceDual F v (Multiplicative.ofAdd a.val) :=
    PontryaginDual.ext fun y ↦ ha y.toAdd
  refine ⟨a, ha, huniq, ?_⟩
  dsimp only
  rw [he]
  constructor
  · intro f
    rw [← finiteConnesPrincipalValue_eq_integral, ← mul_assoc]
    exact finiteConnesPrincipalValue_changeCharacter F v (additiveHaarDifferent F v)
      (finitePlace_tamagawa_fourier_normalization F v) μ a f
  · intro f
    rw [← finiteConnesPrincipalValue_eq_integral, ← mul_assoc]
    exact finiteWeilPrincipalValue_changeCharacter F v μ a f

end Tamagawa

end

end Masullo
