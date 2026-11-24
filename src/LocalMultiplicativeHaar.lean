import FinitePlaceHaar
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField Pointwise WithZero

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place F) := v.adicCompletion F
private abbrev LocalUnits (v : Place F) := (LocalField F v)ˣ

variable (v : Place F)
  [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)]

/-- Restrict additive Haar to the nonzero locus and weight by the reciprocal
of the local absolute value. -/
def finitePlaceUnitDensity (μ : Measure (LocalField F v)) : Measure (LocalUnits F v) :=
  (μ.comap Units.val).withDensity (fun x : LocalUnits F v => (‖x.val‖₊ : ℝ≥0∞)⁻¹)

omit [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)] in
private theorem val_unit_preimage_mul (u : LocalUnits F v) (S : Set (LocalUnits F v)) :
    (Units.val : LocalUnits F v → LocalField F v) '' ((fun x => u * x) ⁻¹' S) =
      u⁻¹ • ((Units.val : LocalUnits F v → LocalField F v) '' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (mem_smul_set_iff_inv_smul_mem).mpr
    rw [inv_inv]
    exact ⟨u * x, hx, rfl⟩
  · intro hz
    have hz' := (mem_smul_set_iff_inv_smul_mem).mp hz
    rw [inv_inv] at hz'
    obtain ⟨x, hx, he⟩ := hz'
    refine ⟨u⁻¹ * x, ?_, ?_⟩
    · change u * (u⁻¹ * x) ∈ S
      rwa [mul_inv_cancel_left]
    · change u⁻¹ • x.val = z
      rw [he, inv_smul_smul]

private theorem finitePlaceUnitDensity_invariant (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure] :
    (finitePlaceUnitDensity F v μ).IsMulLeftInvariant := by
  let A := LocalField F v
  let U := LocalUnits F v
  let f : U → ℝ≥0∞ := fun x => (‖x.val‖₊ : ℝ≥0∞)⁻¹
  let ν : Measure U := μ.comap Units.val
  let m := finitePlaceUnitDensity F v μ
  have hval : MeasurableEmbedding (Units.val : U → A) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding
  have hf : Measurable f := (ENNReal.continuous_coe.comp
    (Units.continuous_val : Continuous (Units.val : U → A)).nnnorm).measurable.inv
  constructor
  intro u
  let e := (Homeomorph.mulLeft u).toMeasurableEquiv
  let c : ℝ≥0∞ := ‖u.val‖₊
  have hc : c ≠ 0 := by simp [c, u.ne_zero]
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hv : (‖(u⁻¹).val‖₊ : ℝ≥0∞) = c⁻¹ := by
    rw [show (u⁻¹).val = u.val⁻¹ from u.val_inv_eq_inv_val, nnnorm_inv]
    exact ENNReal.coe_inv (by simp [u.ne_zero])
  have hbase : ν.map e = c⁻¹ • ν := by
    ext S hS
    rw [Measure.map_apply e.measurable hS, Measure.smul_apply]
    change μ.comap Units.val (e ⁻¹' S) = c⁻¹ * μ.comap Units.val S
    rw [hval.comap_apply μ (e ⁻¹' S), hval.comap_apply μ S]
    change μ (Units.val '' ((fun x : U => u * x) ⁻¹' S)) = _
    rw [val_unit_preimage_mul F v]
    exact (finitePlace_addHaar_smul F v μ u⁻¹ _).trans (congrArg (· * _) hv)
  have hweight (x : U) : f (e.symm x) = c * f x := by
    change (‖(u⁻¹ * x).val‖₊ : ℝ≥0∞)⁻¹ = c * (‖x.val‖₊ : ℝ≥0∞)⁻¹
    rw [Units.val_mul, nnnorm_mul, ENNReal.coe_mul, hv, ENNReal.mul_inv, inv_inv]
    · exact Or.inr ENNReal.coe_ne_top
    · exact Or.inl (by simpa using hc)
  change m.map e = m
  ext S hS
  have hpre : MeasurableSet (e ⁻¹' S) := e.measurable hS
  rw [Measure.map_apply e.measurable hS]
  change (ν.withDensity f) (e ⁻¹' S) = (ν.withDensity f) S
  rw [withDensity_apply _ hpre, withDensity_apply _ hS]
  calc
    (∫⁻ x in e ⁻¹' S, f x ∂ν) = ∫⁻ y in S, f (e.symm y) ∂(ν.map e) := by
      have h := setLIntegral_map (μ := ν) (f := fun y : U => f (e.symm y))
        hS (hf.comp e.symm.measurable) e.measurable
      simpa only [MeasurableEquiv.symm_apply_apply] using h.symm
    _ = ∫⁻ y in S, c * f y ∂(c⁻¹ • ν) := by
      rw [hbase]
      exact lintegral_congr hweight
    _ = ∫⁻ y in S, f y ∂ν := by
      rw [setLIntegral_smul_measure, lintegral_const_mul c hf, smul_eq_mul,
        ENNReal.inv_mul_cancel_left hc hct]

/-- The finite integral units as a set of multiplicative local ideles. -/
def finitePlaceIntegralUnits : Set (LocalUnits F v) :=
  (v.adicCompletionIntegers F).toSubmonoid.units

omit [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)] in
theorem localIntegralUnits_open : IsOpen (finitePlaceIntegralUnits F v) := by
  have h := Valued.isOpen_valuationSubring (LocalField F v)
  exact (h.preimage Units.continuous_val).inter
    (h.preimage (Units.continuous_val.comp continuous_inv))

omit [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)] in
theorem localIntegralUnits_compact : IsCompact (finitePlaceIntegralUnits F v) :=
  Submonoid.units_isCompact (S := (v.adicCompletionIntegers F).toSubmonoid)
    (finitePlaceIntegral_compact F v)

omit [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)] in
theorem localIntegralUnits_value (x : LocalUnits F v) :
    x ∈ finitePlaceIntegralUnits F v ↔ (Valued.v x.val : ℤᵐ⁰) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one

omit [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)] in
private theorem localUnitDensity_one {x : LocalUnits F v} (hx : x ∈ finitePlaceIntegralUnits F v) :
    (‖x.val‖₊ : ℝ≥0∞)⁻¹ = 1 := by
  have h : ‖x.val‖₊ = 1 := by
    apply NNReal.eq
    rw [coe_nnnorm, FinitePlace.norm_def, (localIntegralUnits_value F v x).mp hx, map_one]
  rw [h, ENNReal.coe_one, inv_one]

omit [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
  [MeasurableSpace (LocalUnits F v)] [BorelSpace (LocalUnits F v)] in
private theorem localIntegralUnits_image :
    (Units.val : LocalUnits F v → LocalField F v) '' finitePlaceIntegralUnits F v =
      (v.adicCompletionIntegers F : Set (LocalField F v)) \ finitePlaceMaximalBall F v := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have he := (localIntegralUnits_value F v x).mp hx
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr he.le, by
      change ¬ (Valued.v x.val : ℤᵐ⁰) < 1
      rw [he]
      exact lt_irrefl _⟩
  · rintro ⟨hzO, hzM⟩
    have hle := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp hzO
    have he : (Valued.v z : ℤᵐ⁰) = 1 := le_antisymm hle (le_of_not_gt hzM)
    have hn : z ≠ 0 := fun h => by rw [h, map_zero] at he; exact zero_ne_one he
    exact ⟨Units.mk0 z hn, (localIntegralUnits_value F v _).mpr he, rfl⟩

private theorem localUnitDensity_integralUnits_mass (μ : Measure (LocalField F v)) :
    finitePlaceUnitDensity F v μ (finitePlaceIntegralUnits F v) =
      μ ((v.adicCompletionIntegers F : Set (LocalField F v)) \ finitePlaceMaximalBall F v) := by
  have hs := (localIntegralUnits_open F v).measurableSet
  have he : MeasurableEmbedding (Units.val : LocalUnits F v → LocalField F v) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding
  rw [finitePlaceUnitDensity, withDensity_apply _ hs, ← localIntegralUnits_image F v, ← he.comap_apply μ (finitePlaceIntegralUnits F v)]
  calc
    _ = ∫⁻ _x in finitePlaceIntegralUnits F v, 1 ∂μ.comap Units.val := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      exact localUnitDensity_one F v hx
    _ = _ := by simp [lintegral_const]

theorem finitePlaceUnitDensity_haar (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure] :
    (finitePlaceUnitDensity F v μ).IsHaarMeasure := by
  let m := finitePlaceUnitDensity F v μ
  let U := finitePlaceIntegralUnits F v
  haveI : m.IsMulLeftInvariant := finitePlaceUnitDensity_invariant F v μ
  have hU : U.Nonempty := ⟨1, (v.adicCompletionIntegers F).toSubmonoid.units.one_mem⟩
  have hmo : m U = μ ((Units.val : LocalUnits F v → LocalField F v) '' U) := by
    rw [localUnitDensity_integralUnits_mass, localIntegralUnits_image]
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior m U (localIntegralUnits_compact F v)
    (by rwa [(localIntegralUnits_open F v).interior_eq]) ?_ ?_
  · rw [hmo]
    exact (IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ (localIntegralUnits_open F v)).measure_ne_zero
      μ (hU.image Units.val)
  · rw [hmo, localIntegralUnits_image]
    exact ((measure_mono sdiff_subset).trans_lt (finitePlaceIntegral_compact F v).measure_lt_top).ne

/-- Lemma A.3.2.3. The prescribed additive and multiplicative Tamagawa
normalizations give the density (q_v/(q_v-1),d\nu_v/|x|_v).
The discriminant value cancels because the defining local volumes agree. -/
theorem finitePlaceTamagawa_density
    (ν : Measure (LocalField F v)) [ν.IsAddHaarMeasure]
    (μ : Measure (LocalUnits F v)) [μ.IsHaarMeasure]
    (hμ : μ (finitePlaceIntegralUnits F v) = ν (v.adicCompletionIntegers F : Set (LocalField F v))) :
    μ = ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / (Ideal.absNorm v.asIdeal - 1 : ℝ≥0∞)) •
      finitePlaceUnitDensity F v ν := by
  let m := finitePlaceUnitDensity F v ν
  let U := finitePlaceIntegralUnits F v
  let M := finitePlaceMaximalBall F v
  let O : Set (LocalField F v) := v.adicCompletionIntegers F
  let q : ℝ≥0∞ := Ideal.absNorm v.asIdeal
  have hq : 1 < q := by
    change 1 < (Ideal.absNorm v.asIdeal : ℝ≥0∞)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqt : q ≠ ∞ := ENNReal.natCast_ne_top _
  have hqm : q - 1 ≠ 0 := tsub_pos_of_lt hq |>.ne'
  have hqmt : q - 1 ≠ ∞ := (tsub_le_self.trans_lt hqt.lt_top).ne
  have hM₀ : ν M ≠ 0 := (finitePlaceMaximalBall_open F v).measure_ne_zero ν
    ⟨0, by change (Valued.v (0 : LocalField F v) : ℤᵐ⁰) < 1; rw [map_zero]; exact zero_lt_one⟩
  have hMsub : M ⊆ O := fun _ hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr
    (le_of_lt hx)
  have hMt : ν M ≠ ∞ := ((measure_mono hMsub).trans_lt
    (finitePlaceIntegral_compact F v).measure_lt_top).ne
  haveI : m.IsHaarMeasure := finitePlaceUnitDensity_haar F v ν
  letI : SecondCountableTopology (LocalField F v) := finitePlace_secondCountable F v
  letI : SecondCountableTopology (LocalUnits F v) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.secondCountableTopology
  letI : LocallyCompactSpace (LocalField F v) := finitePlace_locallyCompact F v
  letI : LocallyCompactSpace (LocalUnits F v) := inferInstance
  have hO : ν O = q * ν M := finitePlace_measure_integral F v ν
  have hmass : m U = (q - 1) * ν M := by
    rw [localUnitDensity_integralUnits_mass, measure_sdiff hMsub
      (finitePlaceMaximalBall_open F v).measurableSet.nullMeasurableSet hMt, hO,
      ENNReal.sub_mul (fun _ _ => hMt), one_mul]
  have hm₀ : m U ≠ 0 := mul_ne_zero hqm hM₀ |> fun h => hmass.symm ▸ h
  have hmt : m U ≠ ∞ := (localIntegralUnits_compact F v).measure_lt_top.ne
  have hr : μ U / m U = q / (q - 1) := by
    rw [hμ, hO, hmass, ENNReal.mul_div_mul_right _ _ hM₀ hMt]
  rw [measure_eq_div_smul μ m hm₀ hmt, hr]

end

end Masullo
