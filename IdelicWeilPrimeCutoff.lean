import IdelicWeilPrimeSamples
import IdelicWeilFiniteLinear

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
variable (v : Place F)
local notation "L" => (v.adicCompletion F)ˣ
local notation "U" => principalIntegralUnits F v
local notation "q" => (v.asIdeal.absNorm : ℝ)

local instance weilCutoffUnitsCompact : CompactSpace U := principalIntegralUnits_compactSpace F v
local instance weilCutoffUnitsMeasurable : MeasurableSpace U := borel _
local instance weilCutoffUnitsBorel : BorelSpace U := ⟨rfl⟩
local instance weilCutoffIdeleLocallyCompact : LocallyCompactSpace (IdeleClass F) :=
  ideleClasses_locallyCompact
local instance weilCutoffIdeleT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff

set_option maxHeartbeats 1000000

private theorem principalIntegralUnits_eq_finitePlace :
    (U : Set L) = finitePlaceIntegralUnits F v := by
  ext u
  exact (finiteCompletion_norm_eq_one_iff F v u).trans (localIntegralUnits_value F v u).symm

private theorem ordinary_weight_on_shell (n : ℤ) (hn : n ≠ 0)
    (u : L) (hu : u ∈ finiteZetaShell F v n) :
    ‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ = Real.exp (-|(n : ℝ)| * Real.log q / 2) := by
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : 0 < q := zero_lt_one.trans hq
  change ‖u.val‖ = q ^ (-n) at hu
  have hr : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hlog : Real.log ‖u.val‖ = -(n : ℝ) * Real.log q := by
    rw [hu, Real.log_zpow, Int.cast_neg]
  have hne : ‖u.val‖ ≠ 1 := by
    rw [hu, ← zpow_zero q]
    exact (zpow_right_injective₀ hq0 hq.ne').ne (neg_ne_zero.mpr hn)
  have hdist := IsUltrametricDist.dist_eq_max_of_dist_ne_dist
    (x := (1 : v.adicCompletion F)) (y := 0) (z := u.val) (by
      simpa only [dist_zero_right, dist_zero_left, norm_one] using hne.symm)
  have hnorm : ‖1 - u.val‖ = max 1 ‖u.val‖ := by
    simpa only [dist_eq_norm, sub_zero, zero_sub, norm_neg, norm_one] using hdist
  rw [hnorm, Real.rpow_def_of_pos hr]
  rcases lt_or_gt_of_ne hn with hp | hp
  · have hnr : (n : ℝ) < 0 := by exact_mod_cast hp
    have hgt : 1 < ‖u.val‖ := by
      rw [hu]
      exact one_lt_zpow₀ hq (neg_pos.mpr hp)
    rw [max_eq_right hgt.le, ← Real.exp_log hr, ← Real.exp_sub, Real.log_exp, hlog, abs_of_neg hnr]
    congr 1
    ring
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp
    have hlt : ‖u.val‖ < 1 := by
      rw [hu]
      exact zpow_lt_one_of_neg₀ hq (neg_neg_of_pos hp)
    rw [max_eq_left hlt.le, div_one, hlog, abs_of_pos hnr]
    congr 1
    ring

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]

private theorem localUnitHaar_comap :
    μ.comap (Subtype.val : U → L) =
      μ (finitePlaceIntegralUnits F v) • principalUnitHaar F v := by
  have ho : IsOpen (U : Set L) := by
    rw [principalIntegralUnits_eq_finitePlace F v]
    exact localIntegralUnits_open F v
  have e : IsOpenEmbedding (Subtype.val : U → L) := ho.isOpenEmbedding_subtypeVal
  have he : MeasurableEmbedding (Subtype.val : U → L) := e.measurableEmbedding
  letI : (μ.comap (Subtype.val : U → L)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) (f := (principalIntegralUnits F v).subtype) μ e
  obtain h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (μ.comap (Subtype.val : U → L)) (principalUnitHaar F v)
  have hs := congrArg (fun η : Measure U => η univ) h
  change μ.comap (Subtype.val : U → L) univ = _ at hs
  rw [he.comap_apply, image_univ, Subtype.range_val, principalIntegralUnits_eq_finitePlace,
    Measure.smul_apply, principalUnitHaar_univ] at hs
  have hc : μ (finitePlaceIntegralUnits F v) =
      ↑(Measure.haarScalarFactor (μ.comap (Subtype.val : U → L)) (principalUnitHaar F v)) := by
    convert hs using 1
    change _ = _ * (1 : ℝ≥0∞)
    exact (mul_one _).symm
  rw [hc]
  exact h

private theorem setIntegral_shell_as_unitAverage (g : L → ℂ) (n : ℤ) :
    (∫ u in finiteZetaShell F v n, g u ∂μ) =
      (μ.real (finitePlaceIntegralUnits F v)) •
        ∫ w : U, g (chosenFiniteUniformizer F v ^ n * w.val) ∂principalUnitHaar F v := by
  let π := chosenFiniteUniformizer F v
  let e := MeasurableEquiv.mulLeft (π ^ n)
  rw [← (measurePreserving_mul_left μ (π ^ n)).setIntegral_preimage_emb e.measurableEmbedding g,
    finiteZetaShell_preimage F v π (chosenFiniteUniformizer_spec F v),
    ← principalIntegralUnits_eq_finitePlace F v]
  have ho : IsOpen (U : Set L) := by
    rw [principalIntegralUnits_eq_finitePlace F v]
    exact localIntegralUnits_open F v
  let i : U → L := Subtype.val
  have he : IsOpenEmbedding i := ho.isOpenEmbedding_subtypeVal
  have hi : MeasurableEmbedding i := he.measurableEmbedding
  have hmap : (μ.comap i).map i = μ.restrict (U : Set L) := by
    rw [hi.map_comap, show range i = (U : Set L) from Subtype.range_val]
  rw [← hmap, hi.integral_map]
  change (∫ w : U, g (π ^ n * w.val) ∂μ.comap (Subtype.val : U → L)) = _
  rw [localUnitHaar_comap F v μ, integral_smul_measure,
    principalIntegralUnits_eq_finitePlace F v, measureReal_def]

/-- The normalized ordinary cutoff on a nonunit shell is the weighted
probability average of the pulled-back local test on that shell. -/
theorem finiteWeilOrdinary_shell_average (g : locallyConstantTests L) (n : ℤ) (hn : n ≠ 0) :
    (Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
        (∫ u in finiteZetaShell F v n, finiteWeilOrdinaryIntegrand F v g u ∂μ) =
      (Real.log q * Real.exp (-|(n : ℝ)| * Real.log q / 2)) •
        ∫ w : U, g.val (w.val * chosenFiniteUniformizer F v ^ n) ∂principalUnitHaar F v := by
  have hi : (∫ u in finiteZetaShell F v n, finiteWeilOrdinaryIntegrand F v g u ∂μ) =
      Real.exp (-|(n : ℝ)| * Real.log q / 2) • ∫ u in finiteZetaShell F v n, g.val u ∂μ := by
    rw [← integral_smul]
    apply setIntegral_congr_fun (finiteZetaShell_closed F v n).measurableSet
    intro u hu
    rw [finiteWeilOrdinaryIntegrand, ordinary_weight_on_shell F v n hn u hu]
  have hm : μ.real (finitePlaceIntegralUnits F v) ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr
      ⟨((localIntegralUnits_open F v).measure_pos μ ⟨1, one_mem _⟩).ne',
        (localIntegralUnits_compact F v).measure_lt_top.ne⟩
  rw [hi, setIntegral_shell_as_unitAverage F v μ, smul_smul, smul_smul]
  simp_rw [mul_comm (chosenFiniteUniformizer F v ^ n)]
  congr 1
  field_simp

private abbrev NormOne := normOneIdeleClass F

local instance weilCutoffNormOneMeasurable : MeasurableSpace (NormOne F) := borel _
local instance weilCutoffNormOneBorel : BorelSpace (NormOne F) := ⟨rfl⟩

/-- For each prime power, the sum of the normalized characterwise Euler
terms is precisely the pair of corresponding shells of the ordinary
finite-place cutoff on the actual idelic test. -/
theorem idelicWeil_primeSample_hasSum_cutoff
    (ν : Measure (NormOne F)) [ν.IsHaarMeasure]
    (f : BruhatCompactTest (IdeleClass F)) (n : ℕ) :
    let g := bruhatFiniteWeilPullback F v f
    let m : ℤ := ((n + 1 : ℕ) : ℤ)
    HasSum (fun ω : PontryaginDual (NormOne F) => (ν.real univ : ℂ)⁻¹ *
      heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0) (idelicWeilCenteredTest F ν ω f) (v, n))
      ((Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
        ((∫ u in finiteZetaShell F v (-m), finiteWeilOrdinaryIntegrand F v g u ∂μ) +
          (∫ u in finiteZetaShell F v m, finiteWeilOrdinaryIntegrand F v g u ∂μ))) := by
  let g := bruhatFiniteWeilPullback F v f
  let m : ℤ := ((n + 1 : ℕ) : ℤ)
  have hm : 0 < m := by dsimp only [m]; omega
  change HasSum _ ((Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
    ((∫ u in finiteZetaShell F v (-m), finiteWeilOrdinaryIntegrand F v g u ∂μ) +
      (∫ u in finiteZetaShell F v m, finiteWeilOrdinaryIntegrand F v g u ∂μ)))
  rw [smul_add, finiteWeilOrdinary_shell_average F v μ g (-m) (neg_ne_zero.mpr hm.ne'),
    finiteWeilOrdinary_shell_average F v μ g m hm.ne']
  have hcast : (m : ℝ) = ((n + 1 : ℕ) : ℝ) := Int.cast_natCast _
  simp only [Int.cast_neg, abs_neg, hcast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n + 1))]
  change HasSum _ ((Real.log q * Real.exp (-((n + 1 : ℕ) : ℝ) * Real.log q / 2)) •
    idelicWeilUnitShellAverage F f v (-m) +
    (Real.log q * Real.exp (-((n + 1 : ℕ) : ℝ) * Real.log q / 2)) •
      idelicWeilUnitShellAverage F f v m)
  rw [← smul_add, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, mul_comm (Real.log q : ℂ)]
  exact idelicWeil_primeSample_hasSum F ν f v n

/-- The paired prime-power shell contributions exhaust the entire nonunit
part of the finite cutoff. This sums shells after integrating each shell. -/
theorem finiteWeilOrdinary_hasSum_shellPairs (g : locallyConstantTests L) :
    HasSum (fun n : ℕ =>
      (Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
        ((∫ u in finiteZetaShell F v (-((n + 1 : ℕ) : ℤ)),
          finiteWeilOrdinaryIntegrand F v g u ∂μ) +
          (∫ u in finiteZetaShell F v ((n + 1 : ℕ) : ℤ),
            finiteWeilOrdinaryIntegrand F v g u ∂μ)))
      ((Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
        ∫ u in (finitePlaceIntegralUnits F v)ᶜ, finiteWeilOrdinaryIntegrand F v g u ∂μ) := by
  let S := finiteZetaShell F v
  let m (n : ℕ) : ℤ := ((n + 1 : ℕ) : ℤ)
  let A (n : ℕ) := S (-m n) ∪ S (m n)
  let I := finiteWeilOrdinaryIntegrand F v g
  have hpos (n : ℕ) : 0 < m n := by dsimp only [m]; omega
  have hdisj := finiteZetaShell_disjoint F v
  have hsub (k : ℤ) (hk : k ≠ 0) : S k ⊆ (finitePlaceIntegralUnits F v)ᶜ := by
    intro u hu
    rw [← finiteZetaShell_zero F v]
    exact fun h₀ => Set.disjoint_left.mp (hdisj hk) hu h₀
  have hA : ⋃ n, A n = (finitePlaceIntegralUnits F v)ᶜ := by
    ext u
    constructor
    · rintro hu
      obtain ⟨n, hn⟩ := mem_iUnion.mp hu
      change u ∈ S (-m n) ∪ S (m n) at hn
      rcases hn with hn | hn
      · exact hsub _ (neg_ne_zero.mpr (hpos n).ne') hn
      · exact hsub _ (hpos n).ne' hn
    · intro hu
      obtain ⟨k, hk⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) u
      have hkne : k ≠ 0 := by
        rintro rfl
        exact hu (finiteZetaShell_zero F v ▸ hk)
      refine mem_iUnion.mpr ⟨k.natAbs - 1, ?_⟩
      change u ∈ S (-m (k.natAbs - 1)) ∪ S (m (k.natAbs - 1))
      by_cases hneg : k < 0
      · left
        have hindex : -m (k.natAbs - 1) = k := by dsimp only [m]; omega
        rwa [hindex]
      · right
        have hindex : m (k.natAbs - 1) = k := by dsimp only [m]; omega
        rwa [hindex]
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    have hp := hpos i
    have hq' := hpos j
    change Disjoint (S (-m i) ∪ S (m i)) (S (-m j) ∪ S (m j))
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hdisj ?_, hdisj (by omega)⟩, ⟨hdisj (by omega), hdisj ?_⟩⟩
    · dsimp only [m]; omega
    · dsimp only [m]; omega
  have hi : IntegrableOn I (finitePlaceIntegralUnits F v)ᶜ μ :=
    (finiteWeilCanonicalPrincipalValue_integrable F v μ g).1
  have h := hasSum_integral_iUnion
    (fun n => ((finiteZetaShell_closed F v (-m n)).union
      (finiteZetaShell_closed F v (m n))).measurableSet) hd (show IntegrableOn I (⋃ n, A n) μ by
        rwa [hA])
  rw [hA] at h
  refine (h.const_smul (Real.log q / μ.real (finitePlaceIntegralUnits F v))).congr_fun fun n => ?_
  change _ • ((∫ u in S (-m n), I u ∂μ) + (∫ u in S (m n), I u ∂μ)) =
    (Real.log q / μ.real (finitePlaceIntegralUnits F v)) • ∫ u in A n, I u ∂μ
  have hp := hpos n
  dsimp only [A]
  rw [setIntegral_union (hdisj (by omega : -m n ≠ m n))
    (finiteZetaShell_closed F v (m n)).measurableSet
    (hi.mono_set (hsub _ (neg_ne_zero.mpr hp.ne'))) (hi.mono_set (hsub _ hp.ne'))]

/-- Summing over the norm-one characters first, the prime terms recover
the nonunit cutoff at each fixed finite place. -/
theorem idelicWeil_primeTerms_characterFirst
    (ν : Measure (NormOne F)) [ν.IsHaarMeasure]
    (f : BruhatCompactTest (IdeleClass F)) :
    HasSum (fun n : ℕ => ∑' ω : PontryaginDual (NormOne F), (ν.real univ : ℂ)⁻¹ *
      heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0) (idelicWeilCenteredTest F ν ω f) (v, n))
      ((Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
        ∫ u in (finitePlaceIntegralUnits F v)ᶜ,
          finiteWeilOrdinaryIntegrand F v (bruhatFiniteWeilPullback F v f) u ∂μ) := by
  refine (finiteWeilOrdinary_hasSum_shellPairs F v μ (bruhatFiniteWeilPullback F v f)).congr_fun
    fun n => ?_
  exact (idelicWeil_primeSample_hasSum_cutoff F v μ ν f n).tsum_eq

omit [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  [μ.IsHaarMeasure] in
/-- A single finite set of prime powers supports the terms of every
norm-one character of a fixed compact idelic test. -/
theorem idelicWeil_primeTerms_commonSupport
    (ν : Measure (NormOne F)) [ν.IsHaarMeasure] (f : BruhatCompactTest (IdeleClass F)) :
    ∃ T : Finset (Place F × ℕ), ∀ (ω : PontryaginDual (NormOne F)) (j : Place F × ℕ), j ∉ T →
      heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0)
        (idelicWeilCenteredTest F ν ω f) j = 0 := by
  let l (a : IdeleClass F) := (ideleClassLogNorm F a).toAdd
  have hl : Continuous l := continuous_toAdd.comp (ideleClassLogNorm_continuous F)
  obtain ⟨R, hR⟩ := ((f.property.image hl.abs).bddAbove)
  let N := ⌈Real.exp R⌉₊
  let S := {j : Place F × ℕ | (heckePrimePowerIdeal F j).absNorm ≤ N}
  have hS : S.Finite := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).preimage
    (heckePrimePowerIdeal_injective F).injOn
  refine ⟨hS.toFinset, fun ω j hj => ?_⟩
  have hzero (t : ℝ) (ht : R < |t|) : idelicWeilLogProfile F ν ω f t = 0 := by
    unfold idelicWeilLogProfile
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro k
    let a := k.val * ideleClassExpSection F (Multiplicative.ofAdd t)
    change (ω k : ℂ) * f.val.val a = 0
    have hkn : ideleClassLogNorm F k.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val)) = 1
      rw [show ideleClassNorm F k.val = 1 from k.property, Real.log_one]
      rfl
    have hla : l a = t := by
      change (ideleClassLogNorm F (k.val * ideleClassExpSection F (Multiplicative.ofAdd t))).toAdd = t
      rw [map_mul, hkn, one_mul, ideleClassLogNorm_expSection]
      rfl
    have ha : a ∉ tsupport f.val.val := by
      intro ha
      exact ht.not_ge (hla ▸ hR (mem_image_of_mem (fun b => |l b|) ha))
    rw [image_eq_zero_of_notMem_tsupport ha, mul_zero]
  have hjN : N < (heckePrimePowerIdeal F j).absNorm := by
    apply lt_of_not_ge
    intro hj'
    exact hj (hS.mem_toFinset.mpr hj')
  let x := Real.log ((heckePrimePowerIdeal F j).absNorm : ℝ)
  have hx : R < x := by
    apply (Real.lt_log_iff_exp_lt (by exact_mod_cast (Nat.zero_lt_of_lt hjN))).mpr
    exact (Nat.le_ceil (Real.exp R)).trans_lt (by exact_mod_cast hjN)
  have hxnonneg : 0 ≤ x := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hjN)))
  have h₁ := hzero x (by rwa [abs_of_nonneg hxnonneg])
  have h₂ := hzero (-x) (by rwa [abs_neg, abs_of_nonneg hxnonneg])
  unfold heckeCenteredPrimeTerm
  change _ * (_ * idelicWeilLogProfile F ν ω f x + _ * idelicWeilLogProfile F ν ω f (-x)) = 0
  rw [h₁, h₂, mul_zero, mul_zero, add_zero, mul_zero]

omit [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  [μ.IsHaarMeasure] in
/-- The sum of the characterwise prime terms equals the complete nonunit
finite-place cutoff. One finite support works for every character, so the
prime-power and character sums can be interchanged. -/
theorem idelicWeil_primeTerms_hasSum
    [∀ w : Place F, MeasurableSpace (w.adicCompletion F)ˣ]
    [∀ w : Place F, BorelSpace (w.adicCompletion F)ˣ]
    (η : ∀ w : Place F, Measure (w.adicCompletion F)ˣ) [∀ w, (η w).IsHaarMeasure]
    (ν : Measure (NormOne F)) [ν.IsHaarMeasure]
    (f : BruhatCompactTest (IdeleClass F)) :
    HasSum (fun ω : PontryaginDual (NormOne F) => (ν.real univ : ℂ)⁻¹ *
      ∑' j, heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0) (idelicWeilCenteredTest F ν ω f) j)
      (∑' w : Place F, (Real.log (w.asIdeal.absNorm : ℝ) /
          (η w).real (finitePlaceIntegralUnits F w)) •
            ∫ u in (finitePlaceIntegralUnits F w)ᶜ,
              finiteWeilOrdinaryIntegrand F w (bruhatFiniteWeilPullback F w f) u ∂η w) := by
  obtain ⟨T, hT⟩ := idelicWeil_primeTerms_commonSupport F ν f
  let P (j : Place F × ℕ) (ω : PontryaginDual (NormOne F)) :=
    (ν.real univ : ℂ)⁻¹ * heckeCenteredPrimeTerm F (heckeOrdinateCharacter F ω 0)
      (idelicWeilCenteredTest F ν ω f) j
  have hP (ω) (j) (hj : j ∉ T) : P j ω = 0 := by simp only [P, hT ω j hj, mul_zero]
  have hsum (j : Place F × ℕ) : Summable (P j) := by
    rcases j with ⟨w, n⟩
    exact (idelicWeil_primeSample_hasSum_cutoff F w (η w) ν f n).summable
  have hzero (j) (hj : j ∉ T) : (∑' ω, P j ω) = 0 := by
    simp only [hP _ j hj, tsum_zero]
  have hProd : Summable (fun j => ∑' ω, P j ω) := summable_of_ne_finset_zero hzero
  have h := hasSum_sum (s := T) (fun j _ => (hsum j).hasSum)
  have he : (∑ j ∈ T, ∑' ω, P j ω) = ∑' w : Place F, (Real.log (w.asIdeal.absNorm : ℝ) /
          (η w).real (finitePlaceIntegralUnits F w)) •
            ∫ u in (finitePlaceIntegralUnits F w)ᶜ,
              finiteWeilOrdinaryIntegrand F w (bruhatFiniteWeilPullback F w f) u ∂η w := by
    have hfinite : (∑' j, ∑' ω, P j ω) = ∑ j ∈ T, ∑' ω, P j ω := tsum_eq_sum hzero
    rw [← hfinite, hProd.tsum_prod]
    exact tsum_congr fun w => (idelicWeil_primeTerms_characterFirst F w (η w) ν f).tsum_eq
  rw [he] at h
  refine h.congr_fun fun ω => ?_
  rw [← tsum_mul_left]
  exact tsum_eq_sum (hP ω)

end
end Masullo
