import AdelicBounds
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.Algebra.IsOpenUnits

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace WithZero
open scoped Classical ENNReal NNReal NumberField Pointwise WithZero

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place F) := v.adicCompletion F
private abbrev LocalIntegers (v : Place F) := v.adicCompletionIntegers F
private abbrev ValueGroup := ℤᵐ⁰

/-- The maximal ideal of the integral local ring as a subset of the
completion. -/
def finitePlaceMaximalBall (v : Place F) : Set (LocalField F v) :=
  {x | (Valued.v : Valuation (LocalField F v) ValueGroup) x < 1}

theorem finitePlaceMaximalBall_eq_ball (v : Place F) :
    finitePlaceMaximalBall F v = Metric.ball 0 1 := by
  ext x
  change Valued.v x < (1 : ValueGroup) ↔ _
  rw [Metric.mem_ball, dist_zero_right, FinitePlace.norm_def]
  exact (WithZeroMulInt.toNNReal_lt_one_iff (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)).symm

theorem finitePlaceMaximalBall_open (v : Place F) : IsOpen (finitePlaceMaximalBall F v) := by
  rw [finitePlaceMaximalBall_eq_ball]
  exact Metric.isOpen_ball

private theorem local_residue_zero (v : Place F) (x : LocalIntegers F v) :
    IsLocalRing.residue (LocalIntegers F v) x = 0 ↔ x.val ∈ finitePlaceMaximalBall F v := by
  rw [← RingHom.mem_ker, IsLocalRing.ker_residue]
  exact Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (LocalField F v) ValueGroup)

private theorem local_pair_residues (v : Place F) (x y : LocalIntegers F v) :
    IsLocalRing.residue (LocalIntegers F v) x = IsLocalRing.residue (LocalIntegers F v) y ↔
      x.val - y.val ∈ finitePlaceMaximalBall F v := by
  rw [← sub_eq_zero, ← map_sub]
  exact local_residue_zero F v (x - y)

/-- The maximal ideal has index equal to the residue cardinality,
so its additive Haar mass is the corresponding fraction of the unit ball. -/
theorem finitePlace_measure_integral (v : Place F)
    [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
    (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure] :
    μ (v.adicCompletionIntegers F : Set (LocalField F v)) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * μ (finitePlaceMaximalBall F v) := by
  let O := LocalIntegers F v
  let Q := IsLocalRing.ResidueField O
  let M := finitePlaceMaximalBall F v
  let ρ := IsLocalRing.residue O
  letI : Finite ((𝓞 F) ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Finite Q := Finite.of_equiv _ (finitePlaceResidueEquiv v).toEquiv
  letI : Fintype Q := Fintype.ofFinite Q
  choose r hr using (IsLocalRing.residue_surjective (R := O))
  let cell (q : Q) : Set (LocalField F v) := (fun x => (r q).val + x) '' M
  have hcell (q : Q) (x : LocalField F v) :
      x ∈ cell q ↔ ∃ y : O, y.val = x ∧ ρ y = q := by
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hmI : m ∈ (v.adicCompletionIntegers F : Set (LocalField F v)) :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr (le_of_lt hm)
      let y : O := r q + ⟨m, hmI⟩
      have hy : ρ (⟨m, hmI⟩ : O) = 0 := (local_residue_zero F v _).mpr hm
      exact ⟨y, rfl, by change ρ (r q + ⟨m, hmI⟩) = q; rw [map_add, hy, add_zero, hr]⟩
    · rintro ⟨y, rfl, hy⟩
      have he : ρ y = ρ (r q) := hy.trans (hr q).symm
      refine ⟨y.val - (r q).val, (local_pair_residues F v _ _).mp he, ?_⟩
      abel
  have hUnion : (v.adicCompletionIntegers F : Set (LocalField F v)) = ⋃ q, cell q := by
    ext x
    refine ⟨fun hx => mem_iUnion.mpr ⟨ρ ⟨x, hx⟩, (hcell _ _).mpr ⟨⟨x, hx⟩, rfl, rfl⟩⟩, ?_⟩
    intro hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    obtain ⟨y, rfl, _⟩ := (hcell q x).mp hq
    exact y.property
  have hdisj : Pairwise (Disjoint on cell) := by
    intro q t hqt
    apply disjoint_left.mpr
    intro x hx ht
    obtain ⟨y, hy, hq⟩ := (hcell q x).mp hx
    obtain ⟨z, hz, ht'⟩ := (hcell t x).mp ht
    have he : y = z := Subtype.ext (hy.trans hz.symm)
    exact hqt (hq.symm.trans (he ▸ ht'))
  have hopen (q : Q) : IsOpen (cell q) :=
    (Homeomorph.addLeft (r q).val).isOpenMap _ (finitePlaceMaximalBall_open F v)
  have hmass (q : Q) : μ (cell q) = μ M := by
    have h := (measurePreserving_add_left μ (r q).val).measure_preimage (hopen q).measurableSet.nullMeasurableSet
    have he : (fun x => (r q).val + x) ⁻¹' cell q = M :=
      (add_right_injective (r q).val).preimage_image M
    exact h.symm.trans (congrArg μ he)
  rw [hUnion, measure_iUnion hdisj (fun q => (hopen q).measurableSet)]
  simp only [hmass, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, finitePlaceResidue_card v]


theorem finitePlaceIntegral_compact (v : Place F) :
    IsCompact (v.adicCompletionIntegers F : Set (LocalField F v)) := by
  letI : CompactSpace (LocalIntegers F v) := compactSpace_adicIntegers v
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem finitePlace_locallyCompact (v : Place F) :
    LocallyCompactSpace (LocalField F v) :=
  (finitePlaceIntegral_compact F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring (LocalField F v)).mem_nhds (zero_mem _))

theorem finitePlace_secondCountable (v : Place F) :
    SecondCountableTopology (LocalField F v) := by
  letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  letI : SeparableSpace (LocalField F v) :=
    (HeightOneSpectrum.denseRange_algebraMap (K := F) v).separableSpace'
  infer_instance

private theorem valued_unit_norm_one (v : Place F) (u : (LocalField F v)ˣ)
    (h : Valued.v u.val = (1 : ValueGroup)) : ‖u.val‖₊ = 1 := by
  apply NNReal.eq
  rw [coe_nnnorm, FinitePlace.norm_def, h, map_one]

private theorem localValuation_unit_inv (v : Place F) (u : (LocalField F v)ˣ) :
    Valued.v u.inv = (Valued.v u.val : ValueGroup)⁻¹ := by
  rw [show u.inv = u.val⁻¹ from u.inv_eq_val_inv.trans (Units.val_inv_eq_inv_val u)]
  exact map_inv₀ (Valued.v : Valuation (LocalField F v) ValueGroup) _

private theorem integralBall_smul_unit (v : Place F) (u : (LocalField F v)ˣ)
    (h : Valued.v u.val = (1 : ValueGroup)) :
    u • (v.adicCompletionIntegers F : Set (LocalField F v)) = v.adicCompletionIntegers F := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change u.inv * x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (u.inv * x) ≤ 1 ↔ (Valued.v x : ValueGroup) ≤ 1
  rw [map_mul, localValuation_unit_inv F v, h, inv_one, one_mul]

private theorem integralBall_smul_uniformizer (v : Place F) (u : (LocalField F v)ˣ)
    (h : Valued.v u.val = exp (-1 : ℤ)) :
    u • (v.adicCompletionIntegers F : Set (LocalField F v)) = finitePlaceMaximalBall F v := by
  have hp : (exp (-1 : ℤ) : ValueGroup) ≠ 0 := WithZero.exp_ne_zero
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change u.inv * x ∈ v.adicCompletionIntegers F ↔ x ∈ finitePlaceMaximalBall F v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (u.inv * x) ≤ 1 ↔ (Valued.v x : ValueGroup) < 1
  rw [map_mul, localValuation_unit_inv F v, h, inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hp), mul_one]
  have he (a : ValueGroup) : a ≤ exp (-1 : ℤ) ↔ a < 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_lt_exp]
      omega
  exact he _

private theorem finitePlace_delta_of_uniformizer (v : Place F)
    [LocallyCompactSpace (LocalField F v)]
    [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
    (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : (LocalField F v)ˣ) (h : Valued.v u.val = exp (-1 : ℤ)) :
    distribHaarChar (LocalField F v) u = ‖u.val‖₊ := by
  let O : Set (LocalField F v) := v.adicCompletionIntegers F
  let q : ℝ≥0 := Ideal.absNorm v.asIdeal
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr ((NumberField.HeightOneSpectrum.one_lt_absNorm v).ne_zero)
  have hO₀ : μ O ≠ 0 := (Valued.isOpen_valuationSubring (LocalField F v)).measure_ne_zero μ
    ⟨0, zero_mem _⟩
  have hOtop : μ O ≠ ⊤ := (finitePlaceIntegral_compact F v).measure_lt_top.ne
  have hn : ‖u.val‖₊ = q⁻¹ := by
    apply NNReal.eq
    rw [coe_nnnorm, FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    change ((q ^ (-1 : ℤ) : ℝ≥0) : ℝ) = ((q⁻¹ : ℝ≥0) : ℝ)
    rw [zpow_neg_one]
  rw [hn]
  apply distribHaarChar_eq_of_measure_smul_eq_mul hO₀ hOtop
  rw [show O = (v.adicCompletionIntegers F : Set (LocalField F v)) from rfl,
    integralBall_smul_uniformizer F v u h, finitePlace_measure_integral F v μ]
  change μ (finitePlaceMaximalBall F v) = ((q⁻¹ : ℝ≥0) : ℝ≥0∞) *
    ((q : ℝ≥0∞) * μ (finitePlaceMaximalBall F v))
  rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hq, ENNReal.coe_one, one_mul]

private theorem finitePlace_delta_of_valueOne (v : Place F)
    [LocallyCompactSpace (LocalField F v)]
    [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
    (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : (LocalField F v)ˣ) (h : Valued.v u.val = (1 : ValueGroup)) :
    distribHaarChar (LocalField F v) u = ‖u.val‖₊ := by
  rw [valued_unit_norm_one F v u h]
  let O : Set (LocalField F v) := v.adicCompletionIntegers F
  have hO₀ : μ O ≠ 0 := (Valued.isOpen_valuationSubring (LocalField F v)).measure_ne_zero μ
    ⟨0, zero_mem _⟩
  have hOtop : μ O ≠ ⊤ := (finitePlaceIntegral_compact F v).measure_lt_top.ne
  apply distribHaarChar_eq_of_measure_smul_eq_mul hO₀ hOtop
  rw [integralBall_smul_unit F v u h, ENNReal.coe_one, one_mul]


private theorem finitePlace_delta (v : Place F)
    [LocallyCompactSpace (LocalField F v)]
    [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
    (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : (LocalField F v)ˣ) :
    distribHaarChar (LocalField F v) u = ‖u.val‖₊ := by
  let V : Valuation (LocalField F v) ValueGroup := Valued.v
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (exp (-1 : ℤ))
  have hp₀ : p ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  let π := Units.mk0 p hp₀
  have hπ : V π.val = exp (-1 : ℤ) := hp
  let k := WithZero.log (V u.val)
  have hlog : exp k = V u.val := WithZero.exp_log ((V.ne_zero_iff).mpr u.ne_zero)
  let w := u * π ^ k
  have hw : V w.val = 1 := by
    change V (u.val * (π ^ k).val) = 1
    rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← hlog, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    have hk : k + k • (-1 : ℤ) = 0 := by simp
    rw [hk, WithZero.exp_zero]
  let D : (LocalField F v)ˣ →* ℝ≥0ˣ := (distribHaarChar (LocalField F v)).toHomUnits
  let N := (nnnormHom (α := LocalField F v)).toMonoidHom.comp (Units.coeHom (LocalField F v))
  have hπN : D π = N.toHomUnits π :=
    Units.ext (finitePlace_delta_of_uniformizer F v μ π hπ)
  have hwN : D w = N.toHomUnits w :=
    Units.ext (finitePlace_delta_of_valueOne F v μ w hw)
  change D (u * π ^ k) = N.toHomUnits (u * π ^ k) at hwN
  rw [map_mul, map_mul, map_zpow, map_zpow, hπN] at hwN
  exact congrArg Units.val (mul_right_cancel hwN)

/-- Additive Haar measure on the completion scales by the normalized
absolute value at the place. -/
theorem finitePlace_addHaar_smul (v : Place F)
    [MeasurableSpace (LocalField F v)] [BorelSpace (LocalField F v)]
    (μ : Measure (LocalField F v)) [μ.IsAddHaarMeasure]
    (u : (LocalField F v)ˣ) (B : Set (LocalField F v)) :
    μ (u • B) = (‖u.val‖₊ : ℝ≥0∞) * μ B := by
  letI : LocallyCompactSpace (LocalField F v) := finitePlace_locallyCompact F v
  letI : SecondCountableTopology (LocalField F v) := finitePlace_secondCountable F v
  rw [← distribHaarChar_mul μ, finitePlace_delta F v μ]

end

end Masullo
