import AdelicCharacters
import AdelicTamagawaProduct
import AdelicFourierCovariance
import CompactCharacterCompleteness
import FilteredQuotientIndentation
import WeilQuotientIntegral
import ThetaDifferentiation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev A := Adeles F
private abbrev M := Multiplicative (A F)
private abbrev P := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
private abbrev H := (P F).toSubgroup
private abbrev Q := M F ⧸ H F

local instance adelicPoissonMeasurableAdeles : MeasurableSpace (A F) := borel _
local instance adelicPoissonBorelAdeles : BorelSpace (A F) := ⟨rfl⟩
local instance adelicPoissonMeasurableTaggedAdeles : MeasurableSpace (M F) := borel _
local instance adelicPoissonBorelTaggedAdeles : BorelSpace (M F) := ⟨rfl⟩
local instance adelicPoissonMeasurableQuotient : MeasurableSpace (Q F) := borel _
local instance adelicPoissonBorelQuotient : BorelSpace (Q F) := ⟨rfl⟩

local instance adelicPoissonHausdorffTaggedAdeles : T2Space (M F) := by
  change T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  infer_instance

local instance adelicPoissonLocallyCompactTaggedAdeles : LocallyCompactSpace (M F) := by
  change LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_locallyCompact
  infer_instance

local instance adelicPoissonSecondCountableTaggedAdeles : SecondCountableTopology (M F) := adeles_secondCountable F

private theorem principal_closed : IsClosed (H F : Set (M F)) := principalAdeles_closed (F := F)

local instance adelicPoissonDiscretePrincipal : DiscreteTopology (H F) := principalAdeles_discrete (F := F)
local instance adelicPoissonPrincipalCountingHaar : (Measure.count : Measure (H F)).IsHaarMeasure :=
  subgroup_count_isHaarMeasure _
local instance adelicPoissonPrincipalCountingRegular : (Measure.count : Measure (H F)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

private abbrev μA : Measure (M F) := adelicHaarUnitDomain F

local instance adelicPoissonNormalizedHaar : (μA F).IsHaarMeasure := by
  let μ := adelicHaarUnitDomain F
  letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  refine {
    lt_top_of_isCompact := fun s h => by
      change μ (s : Set (A F)) < ⊤
      exact h.measure_lt_top (μ := μ)
    open_pos := fun _ h hs => (h.measure_pos μ hs).ne'
    map_mul_left_eq_self := fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) g.toAdd }

local instance adelicPoissonNormalizedRegular : (μA F).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- The signed adelic fundamental domain is Borel in the full adele ring. -/
theorem signedAdelicDomain_measurable : MeasurableSet (signedAdelicDomain (F := F)) := by
  letI : MeasurableSpace (mixedEmbedding.mixedSpace F) := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  letI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have hArch : Continuous (mixedArch (F := F)) :=
    (infiniteAdele_toMixed_continuous F).comp continuous_fst
  have h₁ := (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)).preimage
    hArch.measurable
  have h₂ : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hS : IsOpen {a : A F | ∀ v, a.2 v ∈ v.adicCompletionIntegers F} :=
    h₂.preimage (show Continuous (fun a : A F => a.2) from continuous_snd)
  exact h₁.inter hS.measurableSet


private theorem signedAdelicDomain_fiber (x : M F) :
    ∃! h : H F, (x * h.val).toAdd ∈ signedAdelicDomain (F := F) := by
  obtain ⟨r, hr, huniq⟩ := signedAdelicDomain_existsUnique x.toAdd
  let j := algebraMap F (Adeles F)
  let h : H F := ⟨Multiplicative.ofAdd (-(j r)), (P F).neg_mem ⟨r, rfl⟩⟩
  refine ⟨h, ?_, ?_⟩
  · change x.toAdd + -(j r) ∈ signedAdelicDomain
    rwa [← sub_eq_add_neg]
  intro b hb
  obtain ⟨t, ht⟩ := (show b.val.toAdd ∈ P F from b.property)
  have hh : x.toAdd - j (-t) ∈ signedAdelicDomain (F := F) := by
    rw [map_neg, sub_neg_eq_add, ht]
    exact hb
  have he : -t = r := huniq (-t) hh
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change b.val.toAdd = -j r
  rw [← he, map_neg, neg_neg]
  exact ht.symm

/-- Under the manuscript's unit-domain Haar normalization and counting on the
diagonal, the additive adelic quotient has Weil Haar measure of mass one. -/
theorem adelicAdditiveQuotient_weil_probability :
    ∃ ν : Measure (Q F), IsWeilQuotientMeasure (H F) (μA F) Measure.count ν ∧ ν univ = 1 := by
  obtain ⟨ν, hν, _⟩ := weilQuotientMeasure_existsUnique (H F) (principal_closed F)
    (μA F) Measure.count
  refine ⟨ν, hν, ?_⟩
  let D : Set (M F) := Multiplicative.toAdd ⁻¹' signedAdelicDomain
  have hD : MeasurableSet D := (signedAdelicDomain_measurable F).preimage continuous_toAdd.measurable
  let κ (y : Q F) : Measure (M F) := Measure.count.map (fun h : H F => y.out * h.val)
  obtain ⟨hκ, heq⟩ := weilMeasure_eq_bind (H F) (principal_closed F) (μA F) Measure.count ν hν
  have hκD (y : Q F) : κ y D = 1 := by
    have ht : Continuous (fun h : H F => y.out * h.val) :=
      continuous_const.mul continuous_subtype_val
    change (Measure.count.map (fun h : H F => y.out * h.val)) D = 1
    rw [Measure.map_apply ht.measurable hD]
    obtain ⟨h, hh, hu⟩ := signedAdelicDomain_fiber F y.out
    have hpre : (fun b : H F => y.out * b.val) ⁻¹' D = {h} := by
      ext b
      exact ⟨hu b, fun he => (mem_singleton_iff.mp he).symm ▸ hh⟩
    rw [hpre, Measure.count_singleton]
  have hμ : (μA F) D = 1 := adelicHaarUnitDomain_apply_domain F
  rw [← heq, Measure.bind_apply hD hκ.aemeasurable] at hμ
  change (∫⁻ y, κ y D ∂ν) = 1 at hμ
  simpa only [hκD, lintegral_const, one_mul] using hμ


/-- The full shifted orbit sum, with the zero term restored, descends to the
compact additive quotient as a continuous function. -/
def fullAdelicPeriodization {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F) (g : Idele F) :
    Q F → ℂ :=
  Quotient.lift
    (fun x : M F => (∑' ξ, shiftedThetaSummand f ξ (g, x.toAdd)) + f (g.val * x.toAdd))
    (fun x y h => by
      change (QuotientGroup.leftRel (H F)).r x y at h
      rw [QuotientGroup.leftRel_apply] at h
      obtain ⟨a, ha⟩ := (show (x⁻¹ * y).toAdd ∈ P F from h)
      change algebraMap F (Adeles F) a = -x.toAdd + y.toAdd at ha
      have hy : y.toAdd = x.toAdd + algebraMap F (Adeles F) a := by rw [ha]; abel
      rw [hy, bruhat_shiftedTheta_add_diagonal hf])

@[simp] theorem fullAdelicPeriodization_mk {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) (x : A F) :
    fullAdelicPeriodization F hf g (QuotientGroup.mk (Multiplicative.ofAdd x) : Q F) =
      (∑' ξ, shiftedThetaSummand f ξ (g, x)) + f (g.val * x) := rfl

theorem fullAdelicPeriodization_continuous {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) : Continuous (fullAdelicPeriodization F hf g) := by
  apply QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
  change Continuous (fun x : M F => (∑' ξ, shiftedThetaSummand f ξ (g, x.toAdd)) +
    f (g.val * x.toAdd))
  exact ((bruhat_shiftedTheta_continuous hf).comp
    (continuous_const.prodMk continuous_toAdd)).add
    ((bruhat_continuous F hf).comp (continuous_const.mul continuous_toAdd))

@[simp] theorem fullAdelicPeriodization_one {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) :
    fullAdelicPeriodization F hf g 1 = thetaOnIdeles F f g + f 0 := by
  change fullAdelicPeriodization F hf g
    (QuotientGroup.mk (Multiplicative.ofAdd (0 : A F)) : Q F) = _
  rw [fullAdelicPeriodization_mk]
  simp only [shiftedThetaSummand_zero, thetaOnIdeles, mul_zero]

private def principalIndex : F ≃ H F :=
  Equiv.ofBijective (fun r => ⟨Multiplicative.ofAdd (algebraMap F (A F) r), ⟨r, rfl⟩⟩)
    ⟨fun r t h => NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
      (congrArg (fun h : H F => h.val.toAdd) h),
      fun ⟨x, hx⟩ => by
        obtain ⟨r, hr⟩ := (show x.toAdd ∈ P F from hx)
        exact ⟨r, Subtype.ext (Multiplicative.toAdd.injective hr)⟩⟩

private theorem orbit_norm_summable {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) (x : M F) :
    Summable (fun h : H F => ‖f (g.val * (x * h.val).toAdd)‖) := by
  apply (principalIndex F).summable_iff.mp
  change Summable (fun r : F => ‖f (g.val * (x.toAdd + algebraMap F (A F) r))‖)
  simpa only [add_comm] using full_shiftedTheta_norm_summable hf g x.toAdd

private theorem full_shiftedTheta_norm_bound {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    {G : Set (Idele F)} (hG : IsCompact G) :
    ∃ C : ℝ, ∀ g ∈ G, ∀ x : A F,
      (∑' ξ : F, ‖f (g.val * (algebraMap F (A F) ξ + x))‖) ≤ C := by
  let D := closure (signedAdelicDomain (F := F))
  have hD : IsCompact D := signedAdelicDomain_isCompact_closure
  obtain ⟨m, hm, hmaj⟩ := bruhat_shiftedTheta_majorant hf (hG.prod hD)
  have hc : Continuous (fun x : Idele F × A F => ‖f (x.1.val * x.2)‖) :=
    ((bruhat_continuous F hf).comp
      ((Units.continuous_val.comp continuous_fst).mul continuous_snd)).norm
  obtain ⟨B, hB⟩ := (hG.prod hD).bddAbove_image hc.continuousOn
  let j := algebraMap F (A F)
  refine ⟨B + ∑' ξ, m ξ, fun g hg x => ?_⟩
  obtain ⟨r, hr, -⟩ := signedAdelicDomain_existsUnique x
  let y := x - j r
  have hy : y ∈ D := subset_closure hr
  let u (ξ : F) := ‖f (g.val * (j ξ + y))‖
  have hu : Summable u := full_shiftedTheta_norm_summable hf g y
  have htranslate : (∑' ξ : F, ‖f (g.val * (j ξ + x))‖) = ∑' ξ : F, u ξ := by
    have he (ξ : F) : u (ξ + r) = ‖f (g.val * (j ξ + x))‖ := by
      dsimp [u, y]
      rw [map_add]
      congr 3
      abel
    simpa only [Equiv.coe_addRight, he] using (Equiv.addRight r).tsum_eq u
  rw [htranslate, hu.tsum_eq_add_tsum_ite 0]
  let S : Set F := {ξ | ξ ≠ 0}
  have he : (fun ξ : F => if ξ = 0 then 0 else u ξ) = S.indicator u := by
    funext ξ
    by_cases hξ : ξ = 0 <;> simp [S, hξ]
  rw [he, ← tsum_subtype]
  change u 0 + (∑' ξ : {r : F // r ≠ 0}, u ξ.val) ≤ _
  rw [← unitsEquivNeZero.tsum_eq (fun ξ : {r : F // r ≠ 0} => u ξ.val)]
  apply add_le_add
  · simpa [u, j] using hB (mem_image_of_mem (fun z : Idele F × A F => ‖f (z.1.val * z.2)‖)
      (show (g, y) ∈ G ×ˢ D from ⟨hg, hy⟩))
  · exact (((bruhat_shiftedTheta_norm_uniform hf
      (isCompact_singleton (x := (g, y)))).hasSum (mem_singleton _)).summable).tsum_le_tsum
      (fun ξ => hmaj ξ (g, y) ⟨hg, hy⟩) hm

/-- Every idelic dilation of a global Schwartz–Bruhat test is integrable for
the normalized additive Haar measure. -/
theorem bruhat_dilate_integrable {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) : Integrable (fun x : M F => f (g.val * x.toAdd)) (μA F) := by
  obtain ⟨ν, hν, hνmass⟩ := adelicAdditiveQuotient_weil_probability F
  obtain ⟨C, hC⟩ := full_shiftedTheta_norm_bound F hf (isCompact_singleton (x := g))
  let w (x : M F) := f (g.val * x.toAdd)
  have hw : Continuous w :=
    (bruhat_continuous F hf).comp (continuous_const.mul continuous_toAdd)
  suffices (∫⁻ y : Q F, ∫⁻ h : H F, ‖w (y.out * h.val)‖₊ ∂Measure.count ∂ν) < ⊤ from
    (integrable_of_weilNormIntegral (H F) (principal_closed F) (μA F) Measure.count ν hν
      hw.measurable this).1
  have hbound (y : Q F) :
      (∫⁻ h : H F, ‖w (y.out * h.val)‖₊ ∂Measure.count) ≤ ENNReal.ofReal C := by
    rw [lintegral_count]
    simp_rw [← enorm_eq_nnnorm, ← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (orbit_norm_summable F hf g y.out),
      ← (principalIndex F).tsum_eq]
    apply ENNReal.ofReal_le_ofReal
    change (∑' r : F, ‖f (g.val * (y.out.toAdd + algebraMap F (A F) r))‖) ≤ C
    simpa only [add_comm] using hC g (mem_singleton g) y.out.toAdd
  refine (lintegral_mono hbound).trans_lt ?_
  rw [lintegral_const, hνmass, mul_one]
  exact ENNReal.ofReal_lt_top

/-- The lattice sum is pointwise the counting-measure average in the Weil formula. -/
theorem fullAdelicPeriodization_eq_cosetIntegral {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) :
    fullAdelicPeriodization F hf g =
      lcaCosetIntegral (H F) Measure.count (fun x : M F => f (g.val * x.toAdd)) := by
  letI : Countable (H F) := countable_of_Lindelof_of_discrete
  funext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [lcaCosetIntegral_mk, integral_countable (integrable_count_iff.mpr (orbit_norm_summable F hf g x))]
  simp only [count_real_singleton, one_smul]
  rw [← (principalIndex F).tsum_eq]
  rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, fullAdelicPeriodization_mk,
    ← full_shiftedTheta_eq hf]
  change (∑' r : F, f (g.val * (algebraMap F (A F) r + x.toAdd))) =
    ∑' r : F, f (g.val * (x.toAdd + algebraMap F (A F) r))
  simp only [add_comm]


/-- With the positive exponential convention, the Fourier integral on the
normalized quotient is the ambient Fourier sample at the diagonal element. -/
theorem fullAdelicPeriodization_fourier {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) (ξ : F) (ν : Measure (Q F))
    (hν : IsWeilQuotientMeasure (H F) (μA F) Measure.count ν) :
    (∫ q, fullAdelicPeriodization F hf g q * (adelicQuotientCharacter F ξ q : ℂ) ∂ν) =
      adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (fun a => f (g.val * a)) (algebraMap F (A F) ξ) := by
  let c (q : Q F) : ℂ := adelicQuotientCharacter F ξ q
  let w (x : M F) := f (g.val * x.toAdd)
  let k (x : M F) := w x * c (QuotientGroup.mk x)
  have hc : Continuous c :=
    continuous_subtype_val.comp (adelicQuotientCharacter F ξ).continuous
  have hkc : Continuous (fun x : M F => c (QuotientGroup.mk x)) :=
    hc.comp QuotientGroup.continuous_mk
  have hkw : Integrable k (μA F) := by
    apply (bruhat_dilate_integrable F hf g).mono
      (((bruhat_continuous F hf).comp (continuous_const.mul continuous_toAdd)).mul
        hkc).aestronglyMeasurable
    exact .of_forall fun x => by simp [c, Circle.norm_coe]
  have ha (x : M F) :
      c (QuotientGroup.mk x) =
        ((standardAdelicCharacter F (x.toAdd * algebraMap F (A F) ξ)).toMul : ℂ) := by
    change ((standardAdelicCharacter F (algebraMap F (A F) ξ * x.toAdd)).toMul : ℂ) = _
    rw [mul_comm]
  have hIntegral : (∫ x, k x ∂μA F) =
      adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (fun a => f (g.val * a)) (algebraMap F (A F) ξ) := by
    change (∫ x, w x * c (QuotientGroup.mk x) ∂μA F) = _
    simp only [ha]
    rfl
  rw [← hIntegral, (weilQuotientIntegral_L1_sigmaFinite (H F) (principal_closed F)
    (μA F) Measure.count ν hν hkw).2.2]
  apply integral_congr_ae
  refine .of_forall fun q => ?_
  rw [fullAdelicPeriodization_eq_cosetIntegral]
  change (∫ h : H F, w (q.out * h.val) ∂Measure.count) * c q =
    ∫ h : H F, k (q.out * h.val) ∂Measure.count
  rw [← integral_mul_const]
  apply integral_congr_ae
  refine .of_forall fun h => ?_
  have hq : (QuotientGroup.mk (q.out * h.val) : Q F) = q := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h.val).2 h.property, mul_one]
    exact Quotient.out_eq' q
  simp only [k, hq]



/-- The periodization can be differentiated along an idelic subgroup. -/
theorem fullAdelicPeriodization_log_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (q : Q F) (r : ℝ) :
    HasDerivAt (fun t : ℝ => fullAdelicPeriodization F f.property (γ (Multiplicative.ofAdd t)) q)
      (fullAdelicPeriodization F (algebraicBruhatDeriv F γ hγ f).property
        (γ (Multiplicative.ofAdd r)) q) r := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  let D := algebraicBruhatDeriv F γ hγ f
  let P (t : ℝ) : Idele F × A F := (γ (Multiplicative.ofAdd t), x.toAdd)
  let j := algebraMap F (A F)
  let C := P '' Icc (r - 1) (r + 1)
  have hC : IsCompact C := isCompact_Icc.image ((hγ.comp continuous_ofAdd).prodMk continuous_const)
  obtain ⟨m, hm, hbound⟩ := bruhat_shiftedTheta_majorant D.property hC
  have hr : r ∈ Ioo (r - 1) (r + 1) := ⟨by linarith, by linarith⟩
  have hs : Summable (fun ξ => shiftedThetaSummand f.val ξ (P r)) :=
    (((bruhat_shiftedTheta_norm_uniform f.property (isCompact_singleton (x := P r))).hasSum
      (mem_singleton _)).summable).of_norm
  have ht : HasDerivAt (fun t => ∑' ξ, shiftedThetaSummand f.val ξ (P t))
      (∑' ξ, shiftedThetaSummand D.val ξ (P r)) r := by
    apply hasDerivAt_tsum_of_isPreconnected hm isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun ξ t _ => algebraicBruhat_log_orbit_hasDerivAt F γ hγ f (j (ξ : F) + x.toAdd) t)
      ?_ hr hs hr
    intro ξ t ht
    exact hbound ξ (P t) ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  exact ht.add (algebraicBruhat_log_orbit_hasDerivAt F γ hγ f x.toAdd r)

private theorem fullAdelicPeriodization_bound {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    {C : Set (Idele F)} (hC : IsCompact C) :
    ∃ M : ℝ, ∀ g ∈ C, ∀ q : Q F, ‖fullAdelicPeriodization F hf g q‖ ≤ M := by
  let U := closure (signedAdelicDomain (F := F))
  let p (z : Idele F × A F) := (∑' ξ, shiftedThetaSummand f ξ z) + f (z.1.val * z.2)
  have hcont : Continuous p := (bruhat_shiftedTheta_continuous hf).add
    ((bruhat_continuous F hf).comp ((Units.continuous_val.comp continuous_fst).mul continuous_snd))
  obtain ⟨M, hM⟩ :=
    (hC.prod (signedAdelicDomain_isCompact_closure (F := F))).exists_bound_of_continuousOn
      hcont.continuousOn
  refine ⟨M, fun g hg q => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, hb, -⟩ := signedAdelicDomain_fiber F x
  have he : (QuotientGroup.mk (x * b.val) : Q F) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b.val).mpr b.property, mul_one]
  rw [← he]
  exact hM (g, (x * b.val).toAdd) ⟨hg, subset_closure hb⟩

/-- Differentiating the integral of an adelically dilated test gives the
integral of its directional derivative. Compact quotient periodization
supplies an integrable bound on every compact time interval. -/
theorem adelicFourier_zero_log_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (r : ℝ) :
    HasDerivAt (fun t : ℝ => adelicFourierIntegral F (adelicHaarUnitDomain F)
      (standardAdelicCharacter F) (fun a => f.val ((γ (Multiplicative.ofAdd t)).val * a)) 0)
      (adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (fun a => (algebraicBruhatDeriv F γ hγ f).val ((γ (Multiplicative.ofAdd r)).val * a)) 0) r := by
  letI : CompactSpace (Q F) := principalAdeles_quotient_compact (F := F)
  obtain ⟨ν, hν, hmass⟩ := adelicAdditiveQuotient_weil_probability F
  letI : ν.IsHaarMeasure := hν.1
  letI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  let g (t : ℝ) := γ (Multiplicative.ofAdd t)
  let D := algebraicBruhatDeriv F γ hγ f
  let p (u : bruhatSubmodule F) (t : ℝ) := fullAdelicPeriodization F u.property (g t)
  have hcont (u : bruhatSubmodule F) (t : ℝ) : Continuous (p u t) :=
    fullAdelicPeriodization_continuous F u.property (g t)
  have hint (u : bruhatSubmodule F) (t : ℝ) : Integrable (p u t) ν :=
    (hcont u t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI (u : bruhatSubmodule F) (t : ℝ) : (∫ q, p u t q ∂ν) =
      adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (fun a => u.val ((g t).val * a)) 0 := by
    have hc (q : Q F) : (adelicQuotientCharacter F 0 q : ℂ) = 1 := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change ((standardAdelicCharacter F (algebraMap F (A F) (0 : F) * x.toAdd)).toMul : ℂ) = 1
      simp only [map_zero, zero_mul]
      exact Circle.coe_one
    simpa only [p, hc, mul_one, map_zero] using
      fullAdelicPeriodization_fourier F u.property (g t) 0 ν hν
  obtain ⟨M, hM⟩ := fullAdelicPeriodization_bound F D.property
    ((isCompact_Icc (a := r - 1) (b := r + 1)).image (hγ.comp continuous_ofAdd))
  have hr : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := p f) (F' := p D) hr
    (Eventually.of_forall fun t => (hint f t).aestronglyMeasurable) (hint f r)
    (hint D r).aestronglyMeasurable
    (Eventually.of_forall fun q t ht => hM (g t) ⟨t, Ioo_subset_Icc_self ht, rfl⟩ q)
    (integrable_const M)
    (Eventually.of_forall fun q t _ => fullAdelicPeriodization_log_hasDerivAt F γ hγ f q t)).2
  simpa only [hI, g, D] using h



/-- Integrating the differentiated coset sums computes the derivative of the
Fourier integral at any fixed frequency. The phase has unit norm, so the
same compact-domain majorant works for every frequency. -/
theorem adelicFourier_log_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (ξ : A F) (r : ℝ) :
    HasDerivAt (fun t : ℝ => adelicFourierIntegral F (adelicHaarUnitDomain F)
      (standardAdelicCharacter F) (fun a => f.val ((γ (Multiplicative.ofAdd t)).val * a)) ξ)
      (adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (fun a => (algebraicBruhatDeriv F γ hγ f).val ((γ (Multiplicative.ofAdd r)).val * a)) ξ) r := by
  letI : Countable (H F) := countable_of_Lindelof_of_discrete
  letI : CompactSpace (Q F) := principalAdeles_quotient_compact (F := F)
  obtain ⟨ν, hν, hmass⟩ := adelicAdditiveQuotient_weil_probability F
  letI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  let χ (x : A F) : ℂ := (standardAdelicCharacter F (x * ξ)).toMul
  let g (t : ℝ) := γ (Multiplicative.ofAdd t)
  let D := algebraicBruhatDeriv F γ hγ f
  let w (u : bruhatSubmodule F) (t : ℝ) (x : M F) := u.val ((g t).val * x.toAdd) * χ x.toAdd
  let p (u : bruhatSubmodule F) (t : ℝ) := lcaCosetIntegral (H F) Measure.count (w u t)
  have hχ : Continuous χ := continuous_subtype_val.comp (continuous_toMul.comp
    ((standardAdelicCharacter_continuous F).comp (continuous_id.mul continuous_const)))
  have hnorm (x : A F) : ‖χ x‖ = 1 := Circle.norm_coe _
  have hInt (u : bruhatSubmodule F) (t : ℝ) : Integrable (w u t) (μA F) := by
    apply (bruhat_dilate_integrable F u.property (g t)).mono
      (((bruhat_continuous F u.property).comp (continuous_const.mul continuous_toAdd)).mul
        (hχ.comp continuous_toAdd)).aestronglyMeasurable
    exact .of_forall fun x => by simp [hnorm]
  have hWeil (u : bruhatSubmodule F) (t : ℝ) :=
    (weilQuotientIntegral_L1_sigmaFinite (H F) (principal_closed F) (μA F) Measure.count ν hν
      (hInt u t)).2
  have hI (u : bruhatSubmodule F) (t : ℝ) : (∫ q, p u t q ∂ν) =
      adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
        (fun a => u.val ((g t).val * a)) ξ := (hWeil u t).2.symm
  let j := algebraMap F (A F)
  let a (q : Q F) (s : F) := j s + q.out.toAdd
  let b (u : bruhatSubmodule F) (q : Q F) (t : ℝ) (s : F) :=
    u.val ((g t).val * a q s) * χ (a q s)
  have hsum (u : bruhatSubmodule F) (q : Q F) (t : ℝ) :
      Summable (fun s => ‖b u q t s‖) := by
    simpa only [b, a, norm_mul, hnorm, mul_one] using
      full_shiftedTheta_norm_summable u.property (g t) q.out.toAdd
  have hp (u : bruhatSubmodule F) (q : Q F) (t : ℝ) :
      p u t q = ∑' s : F, b u q t s := by
    change (∫ h : H F, w u t (q.out * h.val) ∂Measure.count) = _
    have hS : Summable (fun h : H F => ‖w u t (q.out * h.val)‖) := by
      simpa only [w, norm_mul, hnorm, mul_one] using
        orbit_norm_summable F u.property (g t) q.out
    rw [integral_countable (integrable_count_iff.mpr hS)]
    simp only [count_real_singleton, one_smul]
    rw [← (principalIndex F).tsum_eq]
    apply tsum_congr
    intro s
    change u.val ((g t).val * (q.out.toAdd + j s)) * χ (q.out.toAdd + j s) = _
    rw [add_comm]
  have hsplit (u : bruhatSubmodule F) (q : Q F) (t : ℝ) :
      p u t q = (∑' s : Fˣ, b u q t s.val) + b u q t 0 := by
    rw [hp, (hsum u q t).of_norm.tsum_eq_add_tsum_ite 0]
    let U : Set F := {s | s ≠ 0}
    have he : (fun s : F => if s = 0 then 0 else b u q t s) = U.indicator (b u q t) := by
      funext s
      by_cases hs : s = 0 <;> simp [U, hs]
    rw [he, ← tsum_subtype, add_comm]
    congr 1
    exact (unitsEquivNeZero.tsum_eq (fun s : {s : F // s ≠ 0} => b u q t s.val)).symm
  have hderiv (q : Q F) (t : ℝ) : HasDerivAt (fun s => p f s q) (p D t q) t := by
    let C := (fun s : ℝ => (g s, q.out.toAdd)) '' Icc (t - 1) (t + 1)
    have hC : IsCompact C := isCompact_Icc.image ((hγ.comp continuous_ofAdd).prodMk continuous_const)
    obtain ⟨m, hm, hb⟩ := bruhat_shiftedTheta_majorant D.property hC
    have ht : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    have hterm (s : F) (v : ℝ) : HasDerivAt (b f q · s) (b D q v s) v :=
      (algebraicBruhat_log_orbit_hasDerivAt F γ hγ f (a q s) v).mul_const (χ (a q s))
    have hunit : HasDerivAt (fun v => ∑' s : Fˣ, b f q v s.val)
        (∑' s : Fˣ, b D q t s.val) t := by
      apply hasDerivAt_tsum_of_isPreconnected hm isOpen_Ioo (convex_Ioo _ _).isPreconnected
        (fun s v _ => hterm s.val v) ?_ ht ((hsum f q t).of_norm.comp_injective Units.val_injective) ht
      intro s v hv
      simpa only [b, a, j, norm_mul, hnorm, mul_one, shiftedThetaSummand] using
        hb s (g v, q.out.toAdd) ⟨v, Ioo_subset_Icc_self hv, rfl⟩
    simp_rw [hsplit]
    exact hunit.add (hterm 0 t)
  obtain ⟨M, hM⟩ := full_shiftedTheta_norm_bound F D.property
    ((isCompact_Icc (a := r - 1) (b := r + 1)).image (hγ.comp continuous_ofAdd))
  have hbound (t : ℝ) (ht : t ∈ Ioo (r - 1) (r + 1)) (q : Q F) : ‖p D t q‖ ≤ M := by
    rw [hp]
    exact (norm_tsum_le_tsum_norm (hsum D q t)).trans (by
      simp only [b, a, norm_mul, hnorm, mul_one]
      exact hM (g t) ⟨t, Ioo_subset_Icc_self ht, rfl⟩ q.out.toAdd)
  have hr : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := p f) (F' := p D) hr
    (Eventually.of_forall fun t => (hWeil f t).1.aestronglyMeasurable) (hWeil f r).1
    (hWeil D r).1.aestronglyMeasurable
    (Eventually.of_forall fun q t ht => hbound t ht q) (integrable_const M)
    (Eventually.of_forall fun q t _ => hderiv q t)).2
  simpa only [hI, g, D] using h

/-- The directional derivative vanishes at zero. Its Fourier value at zero
is minus the logarithmic modulus exponent times the original Fourier value. -/
theorem algebraicBruhatDeriv_zero_terms
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ) (α : ℝ)
    (hα : ∀ t : ℝ, ideleNorm F (γ (Multiplicative.ofAdd t)) = Real.exp (t * α))
    (f : bruhatSubmodule F) :
    let D := algebraicBruhatDeriv F γ hγ f
    let T := adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
    D.val 0 = 0 ∧ T D.val 0 = (-α) • T f.val 0 := by
  let D := algebraicBruhatDeriv F γ hγ f
  let T := adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
  change D.val 0 = 0 ∧ T D.val 0 = (-α) • T f.val 0
  constructor
  · have hd := algebraicBruhat_log_orbit_hasDerivAt F γ hγ f 0 0
    simp only [mul_zero] at hd
    exact hd.unique (hasDerivAt_const 0 (f.val 0))
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  have he (t : ℝ) : T (fun a => f.val ((γ (Multiplicative.ofAdd t)).val * a)) 0 =
      Real.exp (t * (-α)) • T f.val 0 := by
    have h := adelicFourier_mul_argument F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
      (standardAdelicCharacter_continuous F) f.val (bruhat_continuous F f.property).measurable
      (γ (Multiplicative.ofAdd t)) 0
    simpa only [mul_zero, hα, ← Real.exp_neg, ← mul_neg] using h
  have hD := adelicFourier_zero_log_hasDerivAt F γ hγ f 0
  change HasDerivAt (fun t : ℝ => T (fun a => f.val ((γ (Multiplicative.ofAdd t)).val * a)) 0)
    (T (fun a => D.val ((γ (Multiplicative.ofAdd (0 : ℝ))).val * a)) 0) 0 at hD
  have h₀ : (fun a : A F => D.val ((γ (Multiplicative.ofAdd (0 : ℝ))).val * a)) = D.val := by
    funext a
    change D.val ((γ 1).val * a) = _
    rw [map_one, Units.val_one, one_mul]
  rw [h₀, funext he] at hD
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * (-α))) (-α) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => t * (-α)) (-α) 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const (-α)
    simpa only [Function.comp_def, zero_mul, Real.exp_zero, one_mul] using
      (Real.hasDerivAt_exp (0 * (-α))).comp 0 hlin
  exact hD.unique (hexp.smul_const (T f.val 0))

private theorem adelicQuotientCharacter_neg (ξ : F) (q : Q F) :
    adelicQuotientCharacter F (-ξ) q = (adelicQuotientCharacter F ξ q)⁻¹ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  let j := algebraMap F (A F)
  change (standardAdelicCharacter F (j (-ξ) * x.toAdd)).toMul =
    (standardAdelicCharacter F (j ξ * x.toAdd)).toMul⁻¹
  rw [map_neg, neg_mul, map_neg]
  rfl

/-- The Poisson equality on a dilated Schwartz–Bruhat test follows from
absolute summability of the diagonal Fourier samples. -/
theorem adelicPoisson_of_summable {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F)
    (hs : Summable (fun ξ : F => ‖adelicFourierIntegral F (adelicHaarUnitDomain F)
      (standardAdelicCharacter F) (fun a => f (g.val * a)) (algebraMap F (A F) ξ)‖)) :
    thetaOnIdeles F f g + f 0 =
      ∑' ξ : F, adelicFourierIntegral F (adelicHaarUnitDomain F)
        (standardAdelicCharacter F) (fun a => f (g.val * a)) (algebraMap F (A F) ξ) := by
  letI : CompactSpace (Q F) := principalAdeles_quotient_compact (F := F)
  letI : T2Space (Q F) := principalAdeles_quotient_hausdorff (F := F)
  obtain ⟨ν, hν, hmass⟩ := adelicAdditiveQuotient_weil_probability F
  letI : ν.IsHaarMeasure := hν.1
  letI : ν.Regular := hν.2.1
  let e : F ≃ PontryaginDual (Q F) :=
    (Equiv.neg F).trans (Equiv.ofBijective _ (adelicQuotientCharacter_bijective F))
  letI : Countable (H F) := countable_of_Lindelof_of_discrete
  letI : Countable F := Countable.of_equiv (H F) (principalIndex F).symm
  letI : Countable (PontryaginDual (Q F)) := Countable.of_equiv F e
  let p := fullAdelicPeriodization F hf g
  let a (ξ : F) := adelicFourierIntegral F (adelicHaarUnitDomain F)
    (standardAdelicCharacter F) (fun a => f (g.val * a)) (algebraMap F (A F) ξ)
  have hcoef (ξ : F) : (∫ q, star (e ξ q : ℂ) * p q ∂ν) = a ξ := by
    have he (q : Q F) : star (e ξ q : ℂ) = (adelicQuotientCharacter F ξ q : ℂ) := by
      change star (adelicQuotientCharacter F (-ξ) q : ℂ) = _
      have hinv := congrArg (fun z : Circle => (z⁻¹ : Circle).val)
        (adelicQuotientCharacter_neg F ξ q)
      exact (Circle.coe_inv_eq_conj (adelicQuotientCharacter F (-ξ) q)).symm.trans
        (by simpa only [inv_inv] using hinv)
    simp_rw [he, mul_comm _ (p _)]
    exact fullAdelicPeriodization_fourier F hf g ξ ν hν
  have hs' : Summable (fun χ : PontryaginDual (Q F) => ‖∫ q, star (χ q : ℂ) * p q ∂ν‖) :=
    e.summable_iff.mp (hs.congr fun ξ => congrArg norm (hcoef ξ).symm)
  have h := compact_fourier_eq_tsum ν (fullAdelicPeriodization_continuous F hf g) hmass hs' 1
  simp only [map_one, Circle.coe_one, mul_one] at h
  change p 1 = _ at h
  have hsum := (e.tsum_eq (fun χ => ∫ q, star (χ q : ℂ) * p q ∂ν))
  rw [← hsum] at h
  change p 1 = (∑' ξ : F, ∫ q, star (e ξ q : ℂ) * p q ∂ν) at h
  exact (fullAdelicPeriodization_one F hf g).symm.trans (h.trans (tsum_congr hcoef))

/-- The theta functional equation of Theorem 2.2.3.2 for tests whose
normalized adelic Fourier transform belongs to the Schwartz–Bruhat space. -/
theorem adelicTheta_riemannRoch_of_fourier_mem {f : A F → ℂ}
    (hf : f ∈ bruhatSubmodule F)
    (hFourier : adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F) f ∈
      bruhatSubmodule F) (g : Idele F) :
    let fhat := adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F) f
    thetaOnIdeles F f g =
      (ideleNorm F g)⁻¹ • thetaOnIdeles F fhat g⁻¹ +
        (ideleNorm F g)⁻¹ • fhat 0 - f 0 := by
  let fhat := adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F) f
  change thetaOnIdeles F f g =
    (ideleNorm F g)⁻¹ • thetaOnIdeles F fhat g⁻¹ + (ideleNorm F g)⁻¹ • fhat 0 - f 0
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  let j := algebraMap F (A F)
  let w := adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
    (fun a => f (g.val * a))
  have hw (r : F) : w (j r) = (ideleNorm F g)⁻¹ • fhat ((g⁻¹ : Idele F).val * j r) :=
    adelicFourier_mul_argument F _ _ (standardAdelicCharacter_continuous F) f
      (bruhat_continuous F hf).measurable g (j r)
  have hsum : Summable (fun r : F => ‖w (j r)‖) := by
    have hs := full_shiftedTheta_norm_summable hFourier g⁻¹ 0
    simp only [add_zero] at hs
    simp only [hw, norm_smul]
    exact hs.mul_left ‖(ideleNorm F g)⁻¹‖
  have he := adelicPoisson_of_summable F hf g hsum
  change thetaOnIdeles F f g + f 0 = ∑' r : F, w (j r) at he
  simp only [hw, Complex.real_smul, tsum_mul_left] at he
  have hsplit := full_shiftedTheta_eq hFourier g⁻¹ 0
  simp only [add_zero, mul_zero, shiftedThetaSummand_zero] at hsplit
  change (∑' r : F, fhat ((g⁻¹ : Idele F).val * j r)) =
    thetaOnIdeles F fhat g⁻¹ + fhat 0 at hsplit
  rw [hsplit, mul_add] at he
  simpa only [Complex.real_smul] using (eq_sub_of_add_eq he)

private abbrev FinA := FiniteAdeleRing (𝓞 F) F

/-- Compactly supported locally constant tests have a common neighborhood
of finite translations which leave the entire test unchanged. -/
theorem finiteBruhat_stabilizer_nhds (ψ : FiniteBruhat F) :
    {u : FinA F | ∀ x, ψ.toLocallyConstant (x + u) = ψ.toLocallyConstant x} ∈ 𝓝 0 := by
  let f := ψ.toLocallyConstant
  let C := tsupport f
  let E : Set (FinA F × FinA F) := {z | f (z.1 + z.2) = f z.1}
  have hE : IsOpen E := by
    rw [show E = ⋃ c : ℂ,
        ((fun z : FinA F × FinA F => z.1 + z.2) ⁻¹' {x | f x = c}) ∩
        (Prod.fst ⁻¹' {x | f x = c}) from by
      ext z
      simp only [E, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
      exact ⟨fun h => ⟨f z.1, h, rfl⟩, fun ⟨c, h, hc⟩ => h.trans hc.symm⟩]
    exact isOpen_iUnion fun c =>
      ((f.isLocallyConstant.isOpen_fiber c).preimage
        (continuous_fst.add continuous_snd)).inter
        ((f.isLocallyConstant.isOpen_fiber c).preimage continuous_fst)
  obtain ⟨U, V, -, hV, hCU, h0V, hUV⟩ :=
    generalized_tube_lemma (show IsCompact C from ψ.compactSupport)
      (isCompact_singleton (x := (0 : FinA F))) hE (by
        rintro ⟨x, u⟩ ⟨_, hu⟩
        have he : u = 0 := mem_singleton_iff.mp hu
        simp [E, he])
  have hV₀ : V ∈ 𝓝 0 := hV.mem_nhds (h0V (by simp))
  have hneg : {u : FinA F | -u ∈ V} ∈ 𝓝 0 := by
    have hc : Tendsto (fun u : FinA F => -u) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using (continuous_neg.continuousAt (x := (0 : FinA F))).tendsto
    change (fun u : FinA F => -u) ⁻¹' V ∈ 𝓝 0
    exact hc hV₀
  filter_upwards [hV₀, hneg] with u hu hnu
  intro x
  by_cases hx : x ∈ C
  · exact hUV (show (x, u) ∈ U ×ˢ V from ⟨hCU hx, hu⟩)
  by_cases hxu : x + u ∈ C
  · have h : f ((x + u) + -u) = f (x + u) := hUV (show (x + u, -u) ∈ U ×ˢ V from ⟨hCU hxu, hnu⟩)
    simpa only [add_neg_cancel_right] using h.symm
  exact (image_eq_zero_of_notMem_tsupport hxu).trans (image_eq_zero_of_notMem_tsupport hx).symm

/-- Finite translations act trivially on a neighborhood of any adelic
Schwartz–Bruhat test, uniformly in its argument. -/
theorem bruhat_finiteStabilizer_nhds {f : A F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    {u : FinA F | ∀ a : A F, f (a + finiteAdelicTranslation F u) = f a} ∈ 𝓝 0 := by
  apply Submodule.span_induction (p := fun f _ =>
    {u : FinA F | ∀ a : A F, f (a + finiteAdelicTranslation F u) = f a} ∈ 𝓝 0) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    filter_upwards [finiteBruhat_stabilizer_nhds F ψ] with u hu
    intro a
    change φ ((InfiniteAdeleRing.ringEquiv_mixedSpace F) (a.1 + 0)) *
      ψ.toLocallyConstant (a.2 + u) = φ ((InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1) *
        ψ.toLocallyConstant a.2
    rw [add_zero, hu]
  · simp
  · intro f g _ _ hf hg
    filter_upwards [hf, hg] with u hu hv
    intro a
    simp [hu a, hv a]
  · intro c f _ hf
    filter_upwards [hf] with u hu
    intro a
    simp [hu a]

/-- A nontrivial frequency on a finite translation fixing a test has zero
Fourier integral. -/
theorem adelicFourier_eq_zero_of_finite_translation {f : A F → ℂ}
    (u : FinA F) (hu : ∀ a : A F, f (a + finiteAdelicTranslation F u) = f a)
    (ξ : A F) (hξ : standardAdelicCharacter F (finiteAdelicTranslation F u * ξ) ≠ 0) :
    adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F) f ξ = 0 := by
  letI : (adelicHaarUnitDomain F).IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  let t := finiteAdelicTranslation F u
  let ψ := standardAdelicCharacter F
  let w (a : A F) := f a * ((ψ (a * ξ)).toMul : ℂ)
  let c : ℂ := (ψ (t * ξ)).toMul
  have htrans (a : A F) : w (a + t) = w a * c := by
    change f (a + t) * ((ψ ((a + t) * ξ)).toMul : ℂ) = _
    rw [show f (a + t) = f a from hu a, add_mul, map_add]
    change f a * (((ψ (a * ξ)).toMul * (ψ (t * ξ)).toMul : Circle) : ℂ) = w a * c
    rw [Circle.coe_mul, ← mul_assoc]
  have he : (∫ a, w a ∂adelicHaarUnitDomain F) =
      (∫ a, w a ∂adelicHaarUnitDomain F) * c := by
    rw [← integral_mul_const, ← integral_add_right_eq_self w t]
    exact integral_congr_ae (.of_forall htrans)
  have hc : c ≠ 1 := by
    intro h
    apply hξ
    apply Additive.toMul.injective
    change (ψ (t * ξ)).toMul = (1 : Circle)
    apply Subtype.ext
    change c = (1 : ℂ)
    exact h
  exact (mul_eq_mul_left_iff.mp ((mul_one _).trans he)).resolve_left (by simpa [ne_comm] using hc)

/-- The nonzero diagonal Fourier samples have uniformly bounded denominators
in the trace-dual coordinates of the integral basis. -/
theorem adelicFourier_diagonal_support_lattice {f : A F → ℂ}
    (hf : f ∈ bruhatSubmodule F) (g : Idele F) :
    ∃ n : ℕ, n ≠ 0 ∧
      ∀ ξ : F, adelicFourierIntegral F (adelicHaarUnitDomain F) (standardAdelicCharacter F)
          (fun a => f (g.val * a)) (algebraMap F (A F) ξ) ≠ 0 →
        ∀ i, ∃ z : ℤ,
          (z : ℚ) = (n : ℚ) * ((integralBasis F).traceDual).repr ξ i := by
  let U : Set (FinA F) := {u | ∀ a : A F, f (a + finiteAdelicTranslation F u) = f a}
  have hU : U ∈ 𝓝 0 := bruhat_finiteStabilizer_nhds F hf
  have hcont : Continuous (fun u : FinA F => g.val.2 * u) := continuous_const.mul continuous_id
  have hV : (fun u : FinA F => g.val.2 * u) ⁻¹' U ∈ 𝓝 0 :=
    hcont.continuousAt.preimage_mem_nhds (by simpa only [mul_zero] using hU)
  obtain ⟨n, hn, hsub⟩ := finiteIntegralAdeles_nat_mul_subset_nhds F hV
  let j := algebraMap F (A F)
  let d := algebraMap F (FinA F)
  refine ⟨n, hn, fun ξ hξ i => ?_⟩
  let b := integralBasis F i
  have hb : d b ∈ finiteIntegralAdeles F :=
    (finiteDiagonal_mem_integral F b).mpr
      ⟨RingOfIntegers.basis F i, (integralBasis_apply F i).symm⟩
  let u : FinA F := (n : FinA F) * d b
  have hu : g.val.2 * u ∈ U := hsub ⟨d b, hb, rfl⟩
  have hfix (a : A F) : f (g.val * (a + finiteAdelicTranslation F u)) = f (g.val * a) := by
    have he : g.val * finiteAdelicTranslation F u =
        finiteAdelicTranslation F (g.val.2 * u) := by
      apply Prod.ext
      · exact mul_zero _
      · rfl
    rw [mul_add, he]
    exact hu (g.val * a)
  have hchar : standardAdelicCharacter F (finiteAdelicTranslation F u * j ξ) = 0 := by
    by_contra hne
    exact hξ (adelicFourier_eq_zero_of_finite_translation F u hfix (j ξ) hne)
  have he : finiteAdelicTranslation F u * j ξ =
      finiteAdelicTranslation F (d ((n : F) * (ξ * b))) := by
    apply Prod.ext
    · exact zero_mul _
    · change ((n : FinA F) * d b) * d ξ = d ((n : F) * (ξ * b))
      simp only [map_mul, map_natCast]
      ac_rfl
  rw [he] at hchar
  obtain ⟨z, hz⟩ := (standardAdelicCharacter_finite_diagonal_eq_zero_iff F
    ((n : F) * (ξ * b))).mp hchar
  refine ⟨z, hz.trans ?_⟩
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Module.Basis.traceDual_repr_apply]
  rfl

end

end Masullo
