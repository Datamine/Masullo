import SLocalTamagawa
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Additive Tamagawa normalization on adelic rectangles

The calculation using the global different follows the appendix proof in
`RiemannMasullo/AppA_AlgebraicNT/Sec3.lean` at
cd84b23dd5e4f741037cf31aee06bc90161c6514 under Apache-2.0.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField Pointwise RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K (v : Place F) := v.adicCompletion F
private abbrev intRing (v : Place F) := (v.adicCompletionIntegers F : Set (K F v))

/-- The volume assigned to the integer ring by the exponent of a prime in the
global different. -/
def differentPrimeMass (v : Place F) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt ((v.asIdeal.absNorm : ℝ) ^
    multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹

theorem differentPrimeMass_ne_zero (v : Place F) : differentPrimeMass F v ≠ 0 :=
  ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top

theorem differentPrimeMass_ne_top (v : Place F) : differentPrimeMass F v ≠ ∞ := by
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  apply ENNReal.inv_ne_top.mpr
  exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos_of_pos (pow_pos hq _))).ne'

theorem differentPrimeMass_finite : (differentPrimeMass F).HasFiniteMulSupport := by
  have hJ : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  refine (Ideal.finite_factors hJ).subset ?_
  intro v hv
  by_contra hn
  exact hv (by
    simp [differentPrimeMass, multiplicity_eq_zero.mpr hn])

theorem differentPrimeMass_finprod :
    (∏ᶠ v : Place F, differentPrimeMass F v) = (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹ := by
  let J := differentIdeal ℤ (𝓞 F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hJ).toFinset
  let e (v : Place F) := multiplicity v.asIdeal J
  have hout (v : Place F) (hv : v ∉ T) : e v = 0 := by
    apply multiplicity_eq_zero.mpr
    simpa [T] using hv
  have hfactor : ∏ v ∈ T, v.asIdeal ^ e v = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (f := fun v : Place F => v.asIdeal ^ e v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ
    · intro v hv
      by_contra hn
      exact hv (by simp [hout v hn])
  have hnorm : (∏ v ∈ T, (v.asIdeal.absNorm : ℝ) ^ e v) = (↑(discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) => Ideal.absNorm I) hfactor :
      (∏ v ∈ T, v.asIdeal.absNorm ^ e v) = (discr F).natAbs)
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ (s := T)]
  · unfold differentPrimeMass
    change (∏ v ∈ T, (ENNReal.ofReal (Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ e v)))⁻¹) = _
    rw [← ENNReal.prod_inv_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.sqrt_nonneg _),
      ← Real.sqrt_prod T (fun _ _ => by positivity), hnorm]
    · congr 1
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs,
        Nat.cast_natAbs, Int.cast_abs]
    · exact fun _ _ _ _ _ => Or.inr ENNReal.ofReal_ne_top
  · intro v hv
    by_contra hn
    exact hv (by simp [differentPrimeMass, show multiplicity v.asIdeal J = 0 from hout v hn, J])

section FiniteMeasures

variable [∀ v : Place F, MeasurableSpace (K F v)] [∀ v : Place F, BorelSpace (K F v)]

/-- Additive Haar measure on a finite completion scaled by its global
different contribution. -/
def additiveHaarDifferent (v : Place F) : Measure (K F v) := by
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  let μ := Measure.addHaar (G := K F v)
  exact (differentPrimeMass F v / μ (intRing F v)) • μ

theorem additiveHaarDifferent_integers (v : Place F) :
    additiveHaarDifferent F v (intRing F v) = differentPrimeMass F v := by
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  let μ := Measure.addHaar (G := K F v)
  have hO₀ := (Valued.isOpen_valuationSubring (K F v)).measure_ne_zero μ
    ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hOtop := (finitePlaceIntegral_compact F v).measure_ne_top (μ := μ)
  exact ENNReal.div_mul_cancel hO₀ hOtop

theorem additiveHaarDifferent_isHaar (v : Place F) :
    (additiveHaarDifferent F v).IsAddHaarMeasure := by
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  let μ := Measure.addHaar (G := K F v)
  have hO₀ := (Valued.isOpen_valuationSubring (K F v)).measure_ne_zero μ
    ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hOtop := (finitePlaceIntegral_compact F v).measure_ne_top (μ := μ)
  exact Measure.IsAddHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨differentPrimeMass_ne_zero F v, hOtop⟩)
    (ENNReal.div_ne_top (differentPrimeMass_ne_top F v) hO₀)

end FiniteMeasures

section GlobalMeasures

variable [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]

omit [BorelSpace (Adeles F)] in
theorem signedAdelicDomain_ne_zero (μ : Measure (Adeles F)) [μ.IsAddHaarMeasure] :
    μ (signedAdelicDomain (F := F)) ≠ 0 := by
  letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let D := signedAdelicDomain (F := F)
  let A (x : F) := (algebraMap F (Adeles F) x) +ᵥ D
  have hcover : ⋃ x, A x = univ := by
    apply eq_univ_of_forall
    intro a
    obtain ⟨x, hx, -⟩ := signedAdelicDomain_existsUnique a
    exact mem_iUnion.mpr ⟨x, a - algebraMap F (Adeles F) x, hx, by
      change algebraMap F (Adeles F) x + (a - algebraMap F (Adeles F) x) = a
      abel⟩
  intro h
  have hzero : μ (⋃ x, A x) = 0 := measure_iUnion_null_iff.mpr fun x => by
    change μ ((algebraMap F (Adeles F) x) +ᵥ D) = 0
    rw [measure_vadd]
    exact h
  rw [hcover] at hzero
  exact isOpen_univ.measure_ne_zero μ univ_nonempty hzero

omit [BorelSpace (Adeles F)] in
private theorem signedAdelicDomain_ne_top (μ : Measure (Adeles F)) [μ.IsAddHaarMeasure] :
    μ (signedAdelicDomain (F := F)) ≠ ∞ :=
  ((measure_mono subset_closure).trans_lt
    signedAdelicDomain_isCompact_closure.measure_lt_top).ne

def adelicHaarUnitDomain : Measure (Adeles F) := by
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let μ := Measure.addHaar (G := Adeles F)
  exact (μ (signedAdelicDomain (F := F)))⁻¹ • μ

theorem adelicHaarUnitDomain_isHaar : (adelicHaarUnitDomain F).IsAddHaarMeasure := by
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let μ := Measure.addHaar (G := Adeles F)
  exact Measure.IsAddHaarMeasure.smul μ
    (ENNReal.inv_ne_zero.mpr (signedAdelicDomain_ne_top F μ))
    (ENNReal.inv_ne_top.mpr (signedAdelicDomain_ne_zero F μ))

theorem adelicHaarUnitDomain_apply_domain :
    adelicHaarUnitDomain F (signedAdelicDomain (F := F)) = 1 := by
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let μ := Measure.addHaar (G := Adeles F)
  exact ENNReal.inv_mul_cancel (signedAdelicDomain_ne_zero F μ) (signedAdelicDomain_ne_top F μ)

/-- The Haar normalization is independent of the initial Haar measure. -/
theorem adelicHaarUnitDomain_unique (ν : Measure (Adeles F)) [ν.IsAddHaarMeasure]
    (hν : ν (signedAdelicDomain (F := F)) = 1) : ν = adelicHaarUnitDomain F := by
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  let μ := adelicHaarUnitDomain F
  letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  let c := ν.addHaarScalarFactor μ
  have hc : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have h := congrArg (fun m : Measure (Adeles F) => m (signedAdelicDomain (F := F))) hc
  change ν (signedAdelicDomain (F := F)) = (c • μ) (signedAdelicDomain (F := F)) at h
  rw [hν, Measure.coe_nnreal_smul_apply, show μ _ = 1 from adelicHaarUnitDomain_apply_domain F,
    mul_one, ← ENNReal.coe_one, ENNReal.coe_inj] at h
  rw [hc, ← h, one_smul]

end GlobalMeasures

section IntegralBlockMeasures

variable [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]
variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
variable [∀ v : Place F, MeasurableSpace (K F v)] [∀ v : Place F, BorelSpace (K F v)]
variable (S : Finset (Place F))

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
private theorem sLocalDifferentProduct_isHaar :
    (sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val)).IsAddHaarMeasure := by
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : Place F) : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI (v : Place F) : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  let e : InfiniteAdeleRing F ≃ₜ+ mixedEmbedding.mixedSpace F :=
    { (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv, infiniteAdeleMixedHomeomorph F with }
  haveI : (archAdditiveTamagawa F).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.nnreal_smul volume (pow_ne_zero _ (by norm_num))
  haveI : ((archAdditiveTamagawa F).map e.symm).IsAddHaarMeasure :=
    e.symm.isAddHaarMeasure_map _
  let μ (v : S) := additiveHaarDifferent F v.val
  haveI (v : S) : (μ v).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v.val
  haveI : (Measure.pi μ).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  change (((archAdditiveTamagawa F).map e.symm).prod (Measure.pi μ)).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

private theorem adelicHaar_project_integralBlock (ν : Measure (Adeles F)) [ν.IsAddHaarMeasure] :
    ∃ μ : Measure (SAdeles F S), μ.IsAddHaarMeasure ∧
      ∀ T : Set (SAdeles F S), MeasurableSet T →
        μ T = ν {a | a ∈ globalIntegralBlock F S ∧ sAdelesProjection F S a ∈ T} := by
  let J := globalIntegralBlock F S
  letI : MeasurableSpace J := borel _
  letI : BorelSpace J := ⟨rfl⟩
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : Place F) : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI (v : Place F) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicIntegers v
  letI : BorelSpace (SAdeles F S) :=
    inferInstanceAs (BorelSpace (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  letI : T2Space (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.t2Space
  letI : T2Space (SAdeles F S) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  letI hAdd : MeasurableAdd (Adeles F) := ContinuousAdd.measurableAdd
  let νJ := ν.comap (J.subtype : J →+ Adeles F)
  have hJ := (globalIntegralBlock_open F S).isOpenEmbedding_subtypeVal
  haveI : νJ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := hAdd) ν hJ
  let e := globalIntegralBlockHomeomorph F S
  let p := ((sAdelesProjection F S).toAddMonoidHom).comp J.subtype
  have hp : (p : J → SAdeles F S) = Prod.fst ∘ e := rfl
  have hproper : IsProperMap (p : J → SAdeles F S) :=
    hp ▸ (isProperMap_fst_of_compactSpace.comp e.toHomeomorph.isProperMap)
  have hsurj : Surjective p := hp ▸ Prod.fst_surjective.comp e.surjective
  refine ⟨νJ.map p, Measure.isAddHaarMeasure_map νJ p hproper.continuous hsurj
    (isProperMap_iff_tendsto_cocompact.mp hproper).2, ?_⟩
  intro T hT
  rw [Measure.map_apply hproper.continuous.measurable hT]
  let i : J → Adeles F := Subtype.val
  have hi : MeasurableEmbedding i := hJ.measurableEmbedding
  change (ν.comap i) (p ⁻¹' T) = _
  rw [hi.comap_apply]
  congr 1
  ext a
  exact ⟨fun ⟨b, hb, he⟩ => ⟨he ▸ b.property, he ▸ hb⟩,
    fun ⟨h, hT⟩ => ⟨⟨a, h⟩, hT, rfl⟩⟩

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : Place F, MeasurableSpace (K F v)] [∀ v : Place F, BorelSpace (K F v)] in
/-- The selected and omitted integer-ring volumes multiply to the inverse
square root of the absolute discriminant. -/
theorem differentPrimeMass_split :
    (∏ v : S, differentPrimeMass F v.val) *
      (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) =
        (NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞)⁻¹ := by
  rw [← differentPrimeMass_finprod F]
  rw [← Finset.prod_subtype S (fun _ => Iff.rfl) (differentPrimeMass F),
    ← finprod_mem_coe_finset,
    show (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) =
      ∏ᶠ v ∈ (S : Set (Place F))ᶜ, differentPrimeMass F v from
        finprod_set_coe_eq_finprod_mem (f := differentPrimeMass F) (S : Set (Place F))ᶜ]
  have h := finprod_mem_inter_mul_sdiff' (f := differentPrimeMass F)
    (s := Set.univ) (S : Set (Place F)) ((differentPrimeMass_finite F).subset inter_subset_right)
  simpa only [univ_inter, ← compl_eq_univ_sdiff, finprod_mem_univ] using h

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
private theorem signedSAdelicDomain_measurableSet :
    MeasurableSet (signedSAdelicDomain F S) := by
  have he : signedSAdelicDomain F S =
      (infiniteAdeleMixedHomeomorph F ⁻¹' signedMixedDomain F) ×ˢ
        Set.univ.pi (fun v : S => intRing F v.val) :=
    Set.ext fun _ => and_congr_right fun _ => Set.mem_univ_pi.symm
  rw [he]
  exact ((ZSpan.fundamentalDomain_measurableSet _).preimage
    (infiniteAdeleMixedHomeomorph F).continuous.measurable).prod
    (MeasurableSet.pi (Set.to_countable _) fun v _ =>
      (Valued.isOpen_valuationSubring (K F v.val)).measurableSet)

/-- The Haar measure normalized on the adelic fundamental domain has the
restricted-product formula on every integral block. Finite factors use the
exponents computed in the global different. -/
theorem adelicHaarUnitDomain_restrictedProduct (T : Set (SAdeles F S)) (hT : MeasurableSet T) :
    adelicHaarUnitDomain F
        {a | a ∈ globalIntegralBlock F S ∧ sAdelesProjection F S a ∈ T} =
      (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) *
        sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val) T := by
  let ν := adelicHaarUnitDomain F
  letI : ν.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  obtain ⟨νS, hνS, hproj⟩ := adelicHaar_project_integralBlock F S ν
  letI : νS.IsAddHaarMeasure := hνS
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : Place F) : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI (v : Place F) : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI : LocallyCompactSpace (SAdeles F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  letI : SecondCountableTopology (SAdeles F S) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  letI : BorelSpace (SAdeles F S) :=
    inferInstanceAs (BorelSpace (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  let m (v : S) := additiveHaarDifferent F v.val
  haveI (v : S) : (m v).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v.val
  let μ := sLocalAdditiveProduct F S m
  letI : μ.IsAddHaarMeasure := sLocalDifferentProduct_isHaar F S
  let c := νS.addHaarScalarFactor μ
  have hscale : νS = c • μ := Measure.isAddLeftInvariant_eq_smul νS μ
  let D := signedSAdelicDomain F S
  have hD : MeasurableSet D := signedSAdelicDomain_measurableSet F S
  have hset : {a | a ∈ globalIntegralBlock F S ∧ sAdelesProjection F S a ∈ D} =
      signedAdelicDomain (F := F) := by
    ext a
    constructor
    · rintro ⟨hout, hin⟩
      refine ⟨hin.1, fun v => ?_⟩
      by_cases hv : v ∈ S
      · exact hin.2 ⟨v, hv⟩
      · exact hout v hv
    · intro h
      exact ⟨fun v _ => h.2 v, h.1, fun v => h.2 v.val⟩
  have hDmass := hproj D hD
  rw [hset, hscale, Measure.coe_nnreal_smul_apply] at hDmass
  have hnorm : (c : ℝ≥0∞) *
      ((NNReal.sqrt ‖discr F‖₊ : ℝ≥0∞) * ∏ v : S, differentPrimeMass F v.val) = 1 := by
    rw [← adelicHaarUnitDomain_apply_domain F]
    convert hDmass using 1
    rw [sLocalAdditiveProduct_domain F S m]
    simp only [m, additiveHaarDifferent_integers]
  let d : ℝ≥0∞ := NNReal.sqrt ‖discr F‖₊
  let tail := ∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val
  have hd : d ≠ 0 := by
    simpa [d] using discr_ne_zero F
  have hc : (c : ℝ≥0∞) = tail := calc
    (c : ℝ≥0∞) = (c : ℝ≥0∞) * (d * d⁻¹) := by rw [ENNReal.mul_inv_cancel hd ENNReal.coe_ne_top, mul_one]
    _ = ((c : ℝ≥0∞) * (d * ∏ v : S, differentPrimeMass F v.val)) * tail := by
      rw [← differentPrimeMass_split F S, ← mul_assoc d, ← mul_assoc]
    _ = tail := by rw [show (c : ℝ≥0∞) * (d * ∏ v : S, differentPrimeMass F v.val) = 1 from hnorm, one_mul]
  rw [← hproj T hT, hscale, Measure.coe_nnreal_smul_apply, hc]

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
/-- Projecting the normalized global Haar measure from an integral block gives
mass one to the signed S-local fundamental domain. The scale on the product
of the selected local measures is the contribution of the omitted places. -/
theorem sLocalDifferentProduct_normalized_by_tail :
    let tail := ∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val
    (tail • sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val))
      (signedSAdelicDomain F S) = 1 := by
  intro tail
  letI (v : Place F) : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : Place F) : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI (v : S) : (additiveHaarDifferent F v.val).IsAddHaarMeasure :=
    additiveHaarDifferent_isHaar F v.val
  rw [Measure.smul_apply, smul_eq_mul, sLocalAdditiveProduct_domain]
  simp only [additiveHaarDifferent_integers]
  let d : ℝ≥0∞ := NNReal.sqrt ‖discr F‖₊
  have hd : d ≠ 0 := by simpa [d] using discr_ne_zero F
  calc
    tail * (d * ∏ v : S, differentPrimeMass F v.val) =
        d * ((∏ v : S, differentPrimeMass F v.val) * tail) := by ac_rfl
    _ = 1 := by
      rw [show (∏ v : S, differentPrimeMass F v.val) * tail = d⁻¹ from differentPrimeMass_split F S]
      exact ENNReal.mul_inv_cancel hd ENNReal.coe_ne_top

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
/-- Every S-local Haar measure of covolume one is the product of the
selected factors rescaled by the masses at the omitted finite places. -/
theorem sLocalHaarUnitDomain_eq_product_by_tail
    (ν : Measure (SAdeles F S)) [ν.IsAddHaarMeasure]
    (hν : ν (signedSAdelicDomain F S) = 1) :
    ν = (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) •
      sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val) := by
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  letI (v : Place F) : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI : SecondCountableTopology (SAdeles F S) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  letI (v : Place F) : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI : LocallyCompactSpace (SAdeles F S) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  letI : BorelSpace (SAdeles F S) :=
    inferInstanceAs (BorelSpace (InfiniteAdeleRing F × ((v : S) → K F v.val)))
  let μ := sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val)
  letI : μ.IsAddHaarMeasure := sLocalDifferentProduct_isHaar F S
  let D := signedSAdelicDomain F S
  let tail := ∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val
  let c := ν.addHaarScalarFactor μ
  have hscale : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc : (c : ℝ≥0∞) * μ D = 1 := by
    rw [hscale, Measure.coe_nnreal_smul_apply] at hν
    exact hν
  have ht : tail * μ D = 1 := sLocalDifferentProduct_normalized_by_tail F S
  have hpos : μ D ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht
    exact zero_ne_one ht
  have hfin : μ D ≠ ∞ :=
    ((measure_mono subset_closure).trans_lt
      ((signedSAdelicDomain_compactClosure F S).measure_lt_top (μ := μ))).ne
  have he : (c : ℝ≥0∞) = tail := (ENNReal.mul_left_inj hpos hfin).mp (hc.trans ht.symm)
  change ν = tail • μ
  rw [← he]
  exact hscale

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
theorem signedSAdelicDomain_isAddFundamentalDomain (ν : Measure (SAdeles F S)) :
    IsAddFundamentalDomain (principalSAdeles F S).op (signedSAdelicDomain F S) ν := by
  let D := signedSAdelicDomain F S
  have hD : MeasurableSet D := signedSAdelicDomain_measurableSet F S
  apply IsAddFundamentalDomain.mk' hD.nullMeasurableSet
  intro x
  obtain ⟨q, hq, huniq⟩ := signedSAdelicDomain_existsUnique F S x
  let g : (principalSAdeles F S).op :=
    ⟨AddOpposite.op (-sIntegerDiagonal F S q), ⟨-q, map_neg _ _⟩⟩
  refine ⟨g, ?_, ?_⟩
  · change x + (-sIntegerDiagonal F S q) ∈ D
    simpa only [sub_eq_add_neg] using hq
  · intro b hb
    obtain ⟨r, hr⟩ : -(b.val.unop) ∈ principalSAdeles F S :=
      (principalSAdeles F S).neg_mem b.property
    change x + b.val.unop ∈ D at hb
    have hr' : x - sIntegerDiagonal F S r ∈ D := by
      rwa [hr, sub_neg_eq_add]
    have h := huniq r hr'
    apply Subtype.ext
    apply AddOpposite.unop_injective
    change b.val.unop = -sIntegerDiagonal F S q
    rw [← h, hr, neg_neg]

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]
  [∀ v : Place F, BorelSpace (K F v)] [BorelSpace (InfiniteAdeleRing F)] in
/-- Restricting to the signed fundamental domain and projecting to S-local
additive classes gives total mass equal to the volume of the domain. -/
theorem sLocalAdditiveQuotient_mass
    [MeasurableSpace (SAdelicClass F S)] [BorelSpace (SAdelicClass F S)]
    [BorelSpace (SAdeles F S)] (ν : Measure (SAdeles F S)) :
    Measure.map (QuotientAddGroup.mk : SAdeles F S → SAdelicClass F S)
      (ν.restrict (signedSAdelicDomain F S)) univ = ν (signedSAdelicDomain F S) := by
  have hm : Measurable (QuotientAddGroup.mk : SAdeles F S → SAdelicClass F S) :=
    QuotientAddGroup.continuous_mk.measurable
  rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
/-- The corrected S-local product formula for A.3.1.3, characterized by
total mass one on the additive quotient. -/
theorem sLocalAdditiveQuotient_eq_one_iff_product
    [MeasurableSpace (SAdelicClass F S)] [BorelSpace (SAdelicClass F S)]
    [BorelSpace (SAdeles F S)] (ν : Measure (SAdeles F S)) [ν.IsAddHaarMeasure] :
    Measure.map (QuotientAddGroup.mk : SAdeles F S → SAdelicClass F S)
      (ν.restrict (signedSAdelicDomain F S)) univ = 1 ↔
    ν = (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) •
      sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val) := by
  rw [sLocalAdditiveQuotient_mass]
  exact ⟨sLocalHaarUnitDomain_eq_product_by_tail F S ν,
    fun h ↦ h.symm ▸ sLocalDifferentProduct_normalized_by_tail F S⟩

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
/-- The corrected A.3.1.3 normalization for the quotient measure induced
using counting measure on the diagonal S-integers. -/
theorem sLocalCountingQuotient_eq_one_iff_product
    [BorelSpace (SAdelicClass F S)]
    [BorelSpace (SAdeles F S)] (ν : Measure (SAdeles F S)) [ν.IsAddHaarMeasure]
    (μ : Measure (SAdelicClass F S))
    [AddQuotientMeasureEqMeasurePreimage (G := (principalSAdeles F S).op) ν μ] :
    μ univ = 1 ↔
    ν = (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) •
      sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val) := by
  have hμ : Measure.map (QuotientAddGroup.mk : SAdeles F S → SAdelicClass F S)
      (ν.restrict (signedSAdelicDomain F S)) = μ :=
    ((signedSAdelicDomain_isAddFundamentalDomain F S ν).measurePreserving_add_quotient_mk μ).map_eq
  rw [← hμ]
  exact sLocalAdditiveQuotient_eq_one_iff_product F S ν

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
/-- The tail-normalized product is an additive Haar measure on the S-adeles. -/
theorem sLocalDifferentProduct_tail_isHaar :
    ((∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) •
      sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val)).IsAddHaarMeasure := by
  let μ := sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val)
  letI : μ.IsAddHaarMeasure := sLocalDifferentProduct_isHaar F S
  let tail := ∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val
  let D := signedSAdelicDomain F S
  have h : tail * μ D = 1 := sLocalDifferentProduct_normalized_by_tail F S
  have ht : tail ≠ 0 := fun e ↦ by rw [e, zero_mul] at h; exact zero_ne_one h
  have hD : μ D ≠ 0 := fun e ↦ by rw [e, mul_zero] at h; exact zero_ne_one h
  have hfin : tail ≠ ∞ := fun e ↦ by
    rw [e, ENNReal.top_mul hD] at h
    exact ENNReal.top_ne_one h
  exact Measure.IsAddHaarMeasure.smul μ ht hfin

omit [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] in
/-- The selected local factors already have covolume one when the selected
places contain all prime factors of the global different. This is the
unscaled case of the normalization proved original in commit 8b362e7. -/
theorem sLocalDifferentProduct_domain_eq_one
    (hS : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    sLocalAdditiveProduct F S (fun v => additiveHaarDifferent F v.val)
      (signedSAdelicDomain F S) = 1 := by
  have htail : (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv : ¬ v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h => v.property (hS v.val h)
    simp [differentPrimeMass, multiplicity_eq_zero.mpr hv]
  simpa only [htail, one_smul] using sLocalDifferentProduct_normalized_by_tail F S

/-- The explicit Haar mass of an adelic rectangle with an integral tail. -/
theorem adelicHaarUnitDomain_rectangle (B : Set (InfiniteAdeleRing F)) (hB : MeasurableSet B)
    (U : (v : S) → Set (K F v.val)) (hU : ∀ v, MeasurableSet (U v)) :
    adelicHaarUnitDomain F {a | a ∈ globalIntegralBlock F S ∧
      a.1 ∈ B ∧ ∀ v : S, a.2 v.val ∈ U v} =
        (∏ᶠ v : {v : Place F // v ∉ S}, differentPrimeMass F v.val) *
        ((archAdditiveTamagawa F).map (infiniteAdeleMixedHomeomorph F).symm B *
          ∏ v : S, additiveHaarDifferent F v.val (U v)) := by
  letI (v : Place F) : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI (v : Place F) : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI (v : S) : (additiveHaarDifferent F v.val).IsAddHaarMeasure :=
    additiveHaarDifferent_isHaar F v.val
  let W : Set (SAdeles F S) := B ×ˢ Set.univ.pi U
  have hW : MeasurableSet W := hB.prod (MeasurableSet.pi (Set.to_countable _) fun v _ => hU v)
  have he : {a | a ∈ globalIntegralBlock F S ∧ sAdelesProjection F S a ∈ W} =
      {a | a ∈ globalIntegralBlock F S ∧ a.1 ∈ B ∧ ∀ v : S, a.2 v.val ∈ U v} := by
    ext a
    exact and_congr_right fun _ => and_congr_right fun _ => Set.mem_univ_pi
  rw [← he, adelicHaarUnitDomain_restrictedProduct F S W hW]
  change _ * (Measure.map (infiniteAdeleMixedHomeomorph F).symm (archAdditiveTamagawa F)
    |>.prod (Measure.pi (fun v : S => additiveHaarDifferent F v.val))) W = _
  rw [Measure.prod_prod, Measure.pi_pi]

end IntegralBlockMeasures

end

end Masullo
