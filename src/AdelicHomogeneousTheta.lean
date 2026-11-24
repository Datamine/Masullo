import NormOneExact
import AdelicHaarScaling
import ThetaDifferentiation
import Mathlib.Analysis.Calculus.ParametricIntegral
import FilteredQuotientIndentation
import WeilQuotientIntegral
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open Filter Function MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev G := NormOneIdeles F
private abbrev H := (principalNormOne F).range
private abbrev K := normOneIdeleClass F

local instance : MeasurableSpace (G F) := borel _
local instance : BorelSpace (G F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

/-- The nonzero theta terms are absolutely summable at each idele. -/
theorem adelicThetaNorm_summable {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) : Summable (fun ξ => ‖thetaSummand F f g ξ‖) := by
  have h := bruhat_shiftedTheta_norm_uniform hf (isCompact_singleton (x := (g, 0)))
  simpa only [shiftedThetaSummand_zero] using (h.hasSum (mem_singleton _)).summable

/-- The absolute orbit sum is continuous before descent to the idele class group. -/
theorem adelicThetaNorm_continuous {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Continuous (fun g : Idele F => ∑' ξ, ‖thetaSummand F f g ξ‖) := by
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨D, hD, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨m, hm, hb⟩ := bruhat_shiftedTheta_majorant hf
    (hD.prod (isCompact_singleton (x := (0 : Adeles F))))
  have hU := HasSumUniformlyOn.of_norm_le_summable (f := fun ξ a => ‖thetaSummand F f a ξ‖)
    hm (s := D) (fun ξ a ha => by
      simpa only [Real.norm_of_nonneg (norm_nonneg _), ← shiftedThetaSummand_zero f ξ a] using
        hb ξ (a, 0) ⟨ha, mem_singleton _⟩)
  apply ContinuousOn.continuousAt _ hg
  apply (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hU).continuousOn
  exact Frequently.of_forall fun s =>
    (continuous_finsetSum s fun ξ _ =>
      ((bruhat_continuous F hf).comp (continuous_const.mul Units.continuous_val)).norm).continuousOn

/-- The compact norm-one average with the character convention of Definition 2.2.5.1. -/
def adelicHomogeneousTheta (ν : Measure (K F)) (ω : PontryaginDual (K F))
    (f : Adeles F → ℂ) (q : IdeleClass F) : ℂ :=
  ∫ k : K F, ((ω k : Circle) : ℂ) * adelicTheta F f (k.val * q) ∂ν

private theorem continuous_integral_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (v : X → Y → ℂ) (hv : Continuous (Function.uncurry v)) :
    Continuous (fun x => ∫ y, v x y ∂ν) := by
  let a (x : X) : C(Y, ℂ) := ⟨v x, hv.comp (continuous_const.prodMk continuous_id)⟩
  have ha : Continuous a := ContinuousMap.continuous_of_continuous_uncurry _ hv
  have hLip : LipschitzWith (ν univ).toNNReal (fun b : C(Y, ℂ) => ∫ y, b y ∂ν) := by
    refine LipschitzWith.of_dist_le_mul fun b c => ?_
    have hb (d : C(Y, ℂ)) : Integrable d ν :=
      d.continuous.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset
        isClosed_closure (subset_univ _))
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hb b) (hb c)]
    simpa only [measureReal_def, ENNReal.coe_toNNReal_eq_toReal, ContinuousMap.sub_apply, mul_comm] using
      (norm_integral_le_of_norm_le_const (μ := ν)
        (Eventually.of_forall fun y => ContinuousMap.norm_coe_le_norm (b - c) y))
  exact hLip.continuous.comp ha

private theorem homogeneousIntegrand_continuous
    (ω : PontryaginDual (K F)) {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Continuous (fun p : IdeleClass F × K F =>
      ((ω p.2 : Circle) : ℂ) * adelicTheta F f (p.2.val * p.1)) := by
  have hθ := adelicTheta_continuous F (bruhat_theta_continuous_and_invariant hf).1
  have hk : Continuous (fun p : IdeleClass F × K F => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_subtype_val.comp ω.continuous).comp continuous_snd).mul
    (hθ.comp (hk.mul continuous_fst))

theorem adelicHomogeneousTheta_continuous (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Continuous (adelicHomogeneousTheta F ν ω f) := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  exact continuous_integral_compact ν _ (homogeneousIntegrand_continuous F ω hf)

theorem adelicHomogeneousTheta_translate (ν : Measure (K F)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (K F)) (f : Adeles F → ℂ) (a : K F) (q : IdeleClass F) :
    adelicHomogeneousTheta F ν ω f (a.val * q) =
      ((ω a : Circle) : ℂ)⁻¹ * adelicHomogeneousTheta F ν ω f q := by
  let v (r : IdeleClass F) (k : K F) := ((ω k : Circle) : ℂ) * adelicTheta F f (k.val * r)
  change (∫ k, v (a.val * q) k ∂ν) = _ * ∫ k, v q k ∂ν
  rw [← integral_mul_left_eq_self (v (a.val * q)) a⁻¹, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have h : (a⁻¹ * k : K F).val * (a.val * q) = k.val * q := by
    change (a.val⁻¹ * k.val) * (a.val * q) = k.val * q
    rw [mul_assoc, mul_left_comm k.val, inv_mul_cancel_left]
  simp only [v, h, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_assoc]

local instance : LocallyCompactSpace (G F) := by
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  exact (ideles_normOne_isClosed (F := F)).locallyCompactSpace

local instance : T2Space (G F) := by
  letI : T2Space (Idele F) := ideles_hausdorff
  infer_instance

local instance : SecondCountableTopology (G F) := by
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact IsEmbedding.subtypeVal.secondCountableTopology

local instance : DiscreteTopology (H F) := (principalNormOne_closed_discrete F).2
local instance : Countable (H F) := countable_of_Lindelof_of_discrete
local instance : (Measure.count : Measure (H F)).IsHaarMeasure := subgroup_count_isHaarMeasure _
local instance : (Measure.count : Measure (H F)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

private noncomputable def principalEquiv : Fˣ ≃ H F :=
  Equiv.ofBijective (fun t => ⟨principalNormOne F t, t, rfl⟩) ⟨
    fun _ _ h => principalNormOne_injective F (congrArg Subtype.val h),
    fun ⟨_, t, ht⟩ => ⟨t, Subtype.ext ht⟩⟩

private abbrev Q := G F ⧸ H F

local instance : MeasurableSpace (Q F) := borel _
local instance : BorelSpace (Q F) := ⟨rfl⟩

/-- Weil normalization of the character average uses the actual norm-one class group. -/
theorem adelicNormOneWeil_existsUnique (μ : Measure (G F)) [μ.IsHaarMeasure] :
    ∃! ν : Measure (Q F), IsWeilQuotientMeasure (H F) μ Measure.count ν := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  exact weilQuotientMeasure_existsUnique _ (principalNormOne_closed_discrete F).1 _ _

/-- On norm-one ideles, prescribing the mass of the compact class quotient
fixes both Haar measures when the principal ideles carry counting measure.
The proof uses the inverse Weil construction from the original
multiplicative Tamagawa normalization. -/
theorem adelicNormOneWeil_existsUnique_of_mass (m : ℝ≥0) (hm : m ≠ 0) :
    ∃! p : Measure (G F) × Measure (Q F),
      p.1.IsHaarMeasure ∧ p.1.Regular ∧ p.2 univ = m ∧
        IsWeilQuotientMeasure (H F) p.1 Measure.count p.2 := by
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  letI : CompactSpace (Q F) := (normOneClass_quotientEquiv F).toHomeomorph.symm.compactSpace
  let U : TopologicalSpace.PositiveCompacts (Q F) := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν₀ := Measure.haarMeasure U
  have hν₀ : ν₀ univ = 1 := Measure.haarMeasure_self
  let ν := m • ν₀
  letI : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hm
  letI : ν.Regular := inferInstanceAs ((m • ν₀).Regular)
  have hmass : ν univ = m := by
    change (m : ℝ≥0∞) * ν₀ univ = m
    rw [hν₀, mul_one]
  obtain ⟨μ, ⟨hμ, hreg, hweil⟩, huniq⟩ := weilAmbientMeasure_existsUnique
    (H F) (principalNormOne_closed_discrete F).1 Measure.count ν
  refine ⟨(μ, ν), ⟨hμ, hreg, hmass, hweil⟩, ?_⟩
  rintro ⟨μ', ν'⟩ ⟨hμ', hreg', hmass', hweil'⟩
  letI : ν'.IsHaarMeasure := hweil'.1
  letI : ν'.Regular := hweil'.2.1
  have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν₀
  have hcoeff := congrArg (fun n : Measure (Q F) => n univ) hscale
  change ν' univ = (ν'.haarScalarFactor ν₀ : ℝ≥0∞) * ν₀ univ at hcoeff
  rw [hmass', hν₀, mul_one] at hcoeff
  have he : ν' = ν := by
    rw [hscale, ← ENNReal.coe_inj.mp hcoeff]
  subst ν'
  exact Prod.ext (huniq μ' ⟨hμ', hreg', hweil'⟩) rfl

/-- Lemma 2.2.5.2. The lift of the character average to the ideles is the
absolutely convergent unfolded integral over norm-one ideles. We use the
quotient Haar corresponding to counting measure on the principal ideles. -/
theorem adelicHomogeneousTheta_weil (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (Q F)) (hν : IsWeilQuotientMeasure (H F) μ Measure.count ν)
    (ω : PontryaginDual (K F)) {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) (g : Idele F) :
    let w := fun h : G F => ((ω (normOneIdelesToClasses F h) : Circle) : ℂ) * f (h.val * g).val
    Integrable w μ ∧
    adelicHomogeneousTheta F (ν.map (normOneClass_quotientEquiv F)) ω f (ideleClassMap F g) =
      ∫ h, w h ∂μ := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  letI : ν.IsHaarMeasure := hν.1
  let e := normOneClass_quotientEquiv F
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  letI : CompactSpace (Q F) := e.toHomeomorph.symm.compactSpace
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let w (h : G F) := ((ω (normOneIdelesToClasses F h) : Circle) : ℂ) * f (h.val * g).val
  have hw : Continuous w := by
    have hk := (normOneIdelesToClasses_openQuotient F).continuous
    exact ((continuous_subtype_val.comp ω.continuous).comp hk).mul
      ((bruhat_continuous F hf).comp (Units.continuous_val.comp
        (continuous_subtype_val.mul continuous_const)))
  let p := principalEquiv F
  have he (x : G F) : e (QuotientGroup.mk x) = normOneIdelesToClasses F x := rfl
  have hp (x : G F) (t : Fˣ) :
      w (x * (p t).val) = ((ω (normOneIdelesToClasses F x) : Circle) : ℂ) *
        thetaSummand F f (x.val * g) t := by
    have h1 : normOneIdelesToClasses F (p t).val = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [normOneIdelesToClasses_ker]
      exact (p t).property
    unfold w thetaSummand
    rw [map_mul, h1, mul_one]
    change _ * f ((x.val * principalIdele F t) * g).val = _
    rw [mul_comm x.val, mul_assoc]
  have hs (x : G F) : Summable (fun h : H F => ‖w (x * h.val)‖) :=
    p.summable_iff.mp ((adelicThetaNorm_summable F hf (x.val * g)).congr fun t => by
      change _ = ‖w (x * (p t).val)‖
      rw [hp, norm_mul, Circle.norm_coe, one_mul])
  have hr (x : G F) :
      (∑' h : H F, ‖w (x * h.val)‖) = ∑' t, ‖thetaSummand F f (x.val * g) t‖ := by
    rw [← p.tsum_eq]
    simp only [hp, norm_mul, Circle.norm_coe, one_mul]
  let A (x : G F) := ∑' t, ‖thetaSummand F f (x.val * g) t‖
  have hA : Continuous A := (adelicThetaNorm_continuous F hf).comp
    (continuous_subtype_val.mul continuous_const)
  have hA_inv (x y : G F) (h : (QuotientGroup.mk x : Q F) = QuotientGroup.mk y) :
      A x = A y := by
    let b : H F := ⟨x⁻¹ * y, QuotientGroup.eq.mp h⟩
    obtain ⟨t, ht⟩ := b.property
    have hy : y.val = principalIdele F t * x.val := by
      change principalNormOne F t = x⁻¹ * y at ht
      have ht' := congrArg Subtype.val ht
      change principalIdele F t = x.val⁻¹ * y.val at ht'
      rw [ht', mul_comm, mul_inv_cancel_left]
    unfold A
    rw [hy, mul_assoc]
    simpa only [thetaSummand, Equiv.coe_mulRight, map_mul, mul_assoc] using
      ((Equiv.mulRight t).tsum_eq (fun a => ‖thetaSummand F f (x.val * g) a‖)).symm
  let Abar : Q F → ℝ := Quotient.lift A (fun x y h => hA_inv x y (Quotient.sound h))
  have hAbar : Continuous Abar := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp hA
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hAbar.continuousOn
  have hfin : (∫⁻ q : Q F, ∫⁻ h : H F, ‖w (q.out * h.val)‖₊ ∂Measure.count ∂ν) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal M) ?_)
    · simp [ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)]
    intro q
    change (∫⁻ h : H F, ‖w (q.out * h.val)‖₊ ∂Measure.count) ≤ ENNReal.ofReal M
    rw [lintegral_count]
    simp_rw [← enorm_eq_nnnorm, ← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hs q.out), hr]
    apply ENNReal.ofReal_le_ofReal
    have heq : Abar q = A q.out := congrArg Abar (Quotient.out_eq' q).symm
    change A q.out ≤ M
    rw [← heq]
    exact (le_abs_self (Abar q)).trans (by simpa only [Real.norm_eq_abs] using hM q (mem_univ q))
  obtain ⟨hInt, hEq⟩ := integrable_of_weilNormIntegral _ (principalNormOne_closed_discrete F).1
    μ Measure.count ν hν hw.measurable hfin
  refine ⟨hInt, ?_⟩
  rw [hEq]
  let v (k : K F) := ((ω k : Circle) : ℂ) * adelicTheta F f (k.val * ideleClassMap F g)
  change (∫ k, v k ∂ν.map e.toHomeomorph.toMeasurableEquiv) = _
  rw [e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (μ := ν) v]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [lcaCosetIntegral_mk, integral_countable (integrable_count_iff.mpr (hs x))]
  simp only [count_real_singleton, one_smul]
  rw [← p.tsum_eq]
  simp_rw [hp, tsum_mul_left]
  change v (e (QuotientGroup.mk x)) = _
  rw [he]
  rfl


/-- The class measure in Lemma 2.2.5.2 is Haar and realizes the unfolding
for every homogeneous theta average. -/
theorem adelicNormOneHaar_with_unfolding (μ : Measure (G F)) [μ.IsHaarMeasure] :
    ∃ ν : Measure (K F), ν.IsHaarMeasure ∧
      (∃ η : Measure (Q F), IsWeilQuotientMeasure (H F) μ Measure.count η ∧
        ν = η.map (normOneClass_quotientEquiv F)) ∧
      ∀ (ω : PontryaginDual (K F)) (f : Adeles F → ℂ) (_ : f ∈ bruhatSubmodule F)
        (g : Idele F),
        let w := fun h : G F => ((ω (normOneIdelesToClasses F h) : Circle) : ℂ) * f (h.val * g).val
        Integrable w μ ∧
          adelicHomogeneousTheta F ν ω f (ideleClassMap F g) = ∫ h, w h ∂μ := by
  obtain ⟨η, hη, _⟩ := adelicNormOneWeil_existsUnique F μ
  letI : η.IsHaarMeasure := hη.1
  let e := normOneClass_quotientEquiv F
  have hh : (η.map e).IsHaarMeasure :=
    e.toMulEquiv.isHaarMeasure_map η e.continuous e.symm.continuous
  exact ⟨η.map e, hh, ⟨η, hη, rfl⟩, fun ω _ hf g =>
    adelicHomogeneousTheta_weil F μ η hη ω hf g⟩

/-- The derivative passes through the global norm-one character integral
in Theorem 2.2.5.4(3), in the logarithmic parameter of the subgroup. -/
theorem adelicHomogeneousTheta_log_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (ν : Measure (K F)) [ν.IsHaarMeasure] (ω : PontryaginDual (K F))
    (f : bruhatSubmodule F) (q : IdeleClass F) (r : ℝ) :
    HasDerivAt (fun t : ℝ => adelicHomogeneousTheta F ν ω f.val
      (ideleClassMap F (γ (Multiplicative.ofAdd t)) * q))
      (adelicHomogeneousTheta F ν ω (algebraicBruhatDeriv F γ hγ f).val
        (ideleClassMap F (γ (Multiplicative.ofAdd r)) * q)) r := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let D := algebraicBruhatDeriv F γ hγ f
  let a (t : ℝ) : IdeleClass F := ideleClassMap F (γ (Multiplicative.ofAdd t)) * q
  have ha : Continuous a := ((ideleClassMap_continuous F).comp
    (hγ.comp continuous_ofAdd)).mul continuous_const
  let v (u : Adeles F → ℂ) (t : ℝ) (k : K F) : ℂ :=
    ((ω k : Circle) : ℂ) * adelicTheta F u (k.val * a t)
  have hc {u : Adeles F → ℂ} (hu : u ∈ bruhatSubmodule F) (t : ℝ) :
      Continuous (v u t) :=
    (homogeneousIntegrand_continuous F ω hu).comp (continuous_const.prodMk continuous_id)
  have hInt {u : Adeles F → ℂ} (hu : u ∈ bruhatSubmodule F) (t : ℝ) : Integrable (v u t) ν :=
    (hc hu t).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  obtain ⟨M, hb⟩ := ((isCompact_Icc.image ha).prod isCompact_univ).exists_bound_of_continuousOn
    (homogeneousIntegrand_continuous F ω D.property).continuousOn
  have hdiff (t : ℝ) (k : K F) : HasDerivAt (fun b => v f.val b k) (v D.val t k) t := by
    obtain ⟨g, hg⟩ := ideleClassMap_surjective F (k.val * q)
    have harg (b : ℝ) : k.val * a b = ideleClassMap F (γ (Multiplicative.ofAdd b) * g) := by
      rw [map_mul, hg]
      exact mul_left_comm k.val (ideleClassMap F (γ (Multiplicative.ofAdd b))) q
    simpa only [v, harg, D, adelicTheta_mk] using
      (thetaOnIdeles_log_orbit_hasDerivAt F γ hγ f g t).const_mul ((ω k : Circle) : ℂ)
  have hs : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := v f.val) (F' := v D.val)
    hs (Eventually.of_forall fun t => (hInt f.property t).aestronglyMeasurable)
    (hInt f.property r) (hInt D.property r).aestronglyMeasurable
    (Eventually.of_forall fun k t ht => hb (a t, k)
      ⟨⟨t, Ioo_subset_Icc_self ht, rfl⟩, mem_univ k⟩) (integrable_const M)
    (Eventually.of_forall fun k t _ => hdiff t k)).2
  exact h

end

end Masullo
