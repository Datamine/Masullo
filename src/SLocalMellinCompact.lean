import SLocalThetaFourier
import SLocalMeromorphicKernels
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.ContinuousMap.Compact

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev ArchTests := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FiniteTests :=
  locallyConstantTests (∀ v : S, v.val.adicCompletion F)
private abbrev Characters := PontryaginDual (SLocalThetaNormOne F S)

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]

/-- The complement of the union of the actual local pole lattices on a
character component. The finite factors exclude only unramified poles. -/
def sLocalMellinRegularSet (ω : Characters F S) : Set ℂ :=
  {z |
    (∀ i, RealArchZetaRegular (sLocalRealArchParameters F S ω i).2
      (z + (sLocalRealArchParameters F S ω i).1)) ∧
    (∀ i, ComplexArchZetaRegular (sLocalComplexArchParameters F S ω i).2
      (z + (sLocalComplexArchParameters F S ω i).1)) ∧
    sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω) z ≠ 0}

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
/-- The regular domain is the nonvanishing domain of the real and complex
Gamma factors (with Lean's values at their poles) and the finite Euler denominators. -/
theorem sLocalMellinRegularSet_iff_euler (ω : Characters F S) (z : ℂ) :
    z ∈ sLocalMellinRegularSet F S ω ↔
      (∀ i, Complex.Gammaℝ (z + (sLocalRealArchParameters F S ω i).1 +
        (((sLocalRealArchParameters F S ω i).2 % 2 : ℕ) : ℂ)) ≠ 0) ∧
      (∀ i, Complex.Gammaℂ (z + (sLocalComplexArchParameters F S ω i).1 +
        ((sLocalComplexArchParameters F S ω i).2.natAbs : ℂ) / 2) ≠ 0) ∧
      sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω) z ≠ 0 := by
  simp only [sLocalMellinRegularSet, mem_setOf_eq,
    realArchZetaRegular_iff_gamma, complexArchZetaRegular_iff_gamma]

private theorem isOpen_mellinRegular (P : ℕ → Prop) :
    IsOpen {z : ℂ | ∀ k : ℕ, z + k = 0 → P k} := by
  let A : Set ℤ := {m | ∃ k : ℕ, m = (k : ℤ) ∧ ¬ P k}
  have hcl : IsClosed (((↑) : ℤ → ℂ) '' A) :=
    Complex.isClosedEmbedding_intCast.isClosedMap _ (isClosed_discrete A)
  have he : {z : ℂ | ∀ k : ℕ, z + k = 0 → P k} =
      ((fun z : ℂ => -z) ⁻¹' (((↑) : ℤ → ℂ) '' A))ᶜ := by
    ext z
    constructor
    · intro hz hn
      obtain ⟨m, ⟨k, rfl, hk⟩, h⟩ := hn
      have h' : (k : ℂ) = -z := by exact_mod_cast h
      exact hk (hz k (by rw [h', add_neg_cancel]))
    · intro hz k hk
      by_contra hp
      apply hz
      refine ⟨(k : ℤ), ⟨k, rfl, hp⟩, ?_⟩
      push_cast
      linear_combination hk
  rw [he]
  exact (hcl.preimage continuous_neg).isOpen_compl

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
theorem sLocalMellinRegularSet_isOpen (ω : Characters F S) :
    IsOpen (sLocalMellinRegularSet F S ω) := by
  have hR : IsOpen {z : ℂ | ∀ i, RealArchZetaRegular (sLocalRealArchParameters F S ω i).2
      (z + (sLocalRealArchParameters F S ω i).1)} := by
    rw [show {z : ℂ | ∀ i, RealArchZetaRegular (sLocalRealArchParameters F S ω i).2
      (z + (sLocalRealArchParameters F S ω i).1)} = ⋂ i, {z : ℂ |
        RealArchZetaRegular (sLocalRealArchParameters F S ω i).2
          (z + (sLocalRealArchParameters F S ω i).1)} by ext z; simp]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_mellinRegular (fun k => Odd ((sLocalRealArchParameters F S ω i).2 + k))).preimage
        (continuous_id.add continuous_const)
  have hC : IsOpen {z : ℂ | ∀ i, ComplexArchZetaRegular (sLocalComplexArchParameters F S ω i).2
      (z + (sLocalComplexArchParameters F S ω i).1)} := by
    rw [show {z : ℂ | ∀ i, ComplexArchZetaRegular (sLocalComplexArchParameters F S ω i).2
      (z + (sLocalComplexArchParameters F S ω i).1)} = ⋂ i, {z : ℂ |
        ComplexArchZetaRegular (sLocalComplexArchParameters F S ω i).2
          (z + (sLocalComplexArchParameters F S ω i).1)} by ext z; simp]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_mellinRegular (fun k => ¬ ∃ n : ℕ,
        k = (sLocalComplexArchParameters F S ω i).2.natAbs + 2 * n)).preimage
          (continuous_const.mul (continuous_id.add continuous_const))
  have hfin : Continuous (sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω)) :=
    continuous_iff_continuousAt.mpr fun z =>
      (sLocalFiniteZetaDenominator_analytic F S (sLocalFiniteZetaPhases F S ω) z trivial).continuousAt
  exact hR.inter (hC.inter (isOpen_ne_fun hfin continuous_const))

variable (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev archZeta (ω : Characters F S) :=
  archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω)

private abbrev finiteZeta (ω : Characters F S) :=
  sLocalFiniteZetaContinued F S μ (sLocalFiniteZetaPhases F S ω)

private abbrev Z (ω : Characters F S) (z : ℂ) : E F S →L[ℂ] ℂ :=
  (archZeta F S ω z).comp
    (sLocalFiniteZetaSchwartzTest F S μ (sLocalFiniteZetaPhases F S ω) z)

private theorem Z_pure (ω : Characters F S) (z : ℂ) (φ : ArchTests F) (ψ : FiniteTests F S) :
    Z F S μ ω z (sLocalBruhatPure F S φ ψ) = finiteZeta F S μ ω z ψ * archZeta F S ω z φ := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  change archZeta F S ω z (sLocalFiniteZetaSchwartzTest F S μ (sLocalFiniteZetaPhases F S ω)
    z (sLocalBruhatPure F S φ ψ)) = _
  rw [sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure, map_smul]
  rfl

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
private theorem archZeta_estimate (ω : Characters F S) {z : ℂ}
    (hz : z ∈ sLocalMellinRegularSet F S ω) :
    ∃ D, HasOperatorTaylorEstimate (archZeta F S ω) z D :=
  archimedeanNumberFieldZeta_hasOperatorTaylorEstimate F _ _ z hz.1 hz.2.1

private theorem finiteZeta_continuousOn (ω : Characters F S) (ψ : FiniteTests F S) :
    ContinuousOn (fun z => finiteZeta F S μ ω z ψ) (sLocalMellinRegularSet F S ω) := by
  intro z hz
  exact (sLocalFiniteZetaContinued_analyticAt F S μ (sLocalFiniteZetaPhases F S ω)
    ψ z hz.2.2).continuousAt.continuousWithinAt

theorem sLocalProductZetaContinued_continuousOn_regular (ω : Characters F S) (f : E F S) :
    ContinuousOn (fun z => Z F S μ ω z f) (sLocalMellinRegularSet F S ω) := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  have hf : f ∈ Submodule.span ℂ {g : E F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, ψ, rfl⟩ := hg
    simp_rw [Z_pure]
    apply (finiteZeta_continuousOn F S μ ω ψ).mul
    intro z hz
    obtain ⟨D, hD⟩ := archZeta_estimate F S ω hz
    exact (hD.hasDerivAt φ).continuousAt.continuousWithinAt
  | zero => simpa only [map_zero] using continuousOn_const
  | add f g _ _ hf hg =>
    rw [show (fun z => Z F S μ ω z (f + g)) =
      (fun z => Z F S μ ω z f) + (fun z => Z F S μ ω z g) from funext fun z => map_add _ _ _]
    exact hf.add hg
  | smul c f _ hf =>
    rw [show (fun z => Z F S μ ω z (c • f)) =
      c • (fun z => Z F S μ ω z f) from funext fun z => map_smul _ _ _]
    exact hf.const_smul c

include μ in
set_option maxHeartbeats 800000 in
/-- The actual S-local continued Mellin transform as a continuous linear
map into the uniform norm on a compact set of regular parameters. -/
def sLocalMellinCompact (ω : Characters F S) (K : Set ℂ) (hK : IsCompact K)
    (hreg : K ⊆ sLocalMellinRegularSet F S ω) : E F S →L[ℂ] C(K, ℂ) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T : E F S →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨fun z => Z F S μ ω z f,
        continuousOn_iff_continuous_domRestrict.mp ((sLocalProductZetaContinued_continuousOn_regular F S μ ω f).mono hreg)⟩
      map_add' := fun f g => ContinuousMap.ext fun z => map_add (Z F S μ ω z) f g
      map_smul' := fun c f => ContinuousMap.ext fun z => map_smul (Z F S μ ω z) c f }
  refine ⟨T, continuous_sLocal_of_pure F S (norm_withSeminorms ℂ C(K, ℂ)) T ?_⟩
  intro ψ
  let A : ArchTests F →ₗ[ℂ] C(K, ℂ) := T.comp ((sLocalBruhatPure F S).flip ψ)
  change Continuous A
  obtain ⟨p, hp, hA⟩ := HasOperatorTaylorEstimate.compact_bound hK
    (fun z hz => archZeta_estimate F S ω (hreg hz)) (normSeminorm ℂ ℂ) continuous_norm
  obtain ⟨M, hM⟩ := hK.bddAbove_image ((finiteZeta_continuousOn F S μ ω ψ).mono hreg).norm
  let b : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ _) A
  intro i
  apply Seminorm.continuous_of_le (q := b • p) (hp.const_smul b)
  intro φ
  apply (ContinuousMap.norm_le _ (apply_nonneg (b • p) φ)).mpr
  intro z
  change ‖Z F S μ ω z (sLocalBruhatPure F S φ ψ)‖ ≤ (b : ℝ) * p φ
  rw [Z_pure, norm_mul]
  exact mul_le_mul ((hM (mem_image_of_mem _ z.property)).trans (le_max_left _ _))
    (hA z z.property φ) (norm_nonneg _) b.coe_nonneg

@[simp] theorem sLocalMellinCompact_apply (ω : Characters F S) (K : Set ℂ)
    (hK : IsCompact K) (hreg : K ⊆ sLocalMellinRegularSet F S ω)
    (f : E F S) (z : K) :
    sLocalMellinCompact F S μ ω K hK hreg f z =
      sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
        (sLocalComplexArchParameters F S ω) f z := rfl

include μ in
set_option maxHeartbeats 800000 in
/-- The continued transform in the uniform norm on a compact set that can
meet several unitary character components. -/
def sLocalMellinOnCompact (K : Set (Characters F S × ℂ)) (hK : IsCompact K)
    (hreg : ∀ x ∈ K, x.2 ∈ sLocalMellinRegularSet F S x.1) :
    E F S →L[ℂ] C(K, ℂ) := by
  letI : T1Space (SIdeleQuotient F S) :=
    QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI : T2Space (SLocalThetaNormOne F S) := inferInstance
  letI := sLocalThetaNormOne_compact F S
  letI : DiscreteTopology (Characters F S) := inferInstance
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T (ω : Characters F S) := (fun z : ℂ => (ω, z)) ⁻¹' K
  have hT (ω) : IsCompact (T ω) := by
    have hh := (hK.inter_right ((isClosed_singleton (x := ω)).preimage continuous_fst)).image continuous_snd
    convert hh using 1
    ext z
    change (ω, z) ∈ K ↔ _
    constructor
    · intro hz
      exact ⟨(ω, z), ⟨hz, mem_singleton _⟩, rfl⟩
    · rintro ⟨⟨ω', z'⟩, ⟨hz, hω'⟩, rfl⟩
      change ω' = ω at hω'
      exact hω' ▸ hz
  have hr (ω) : T ω ⊆ sLocalMellinRegularSet F S ω := fun z hz => hreg (ω, z) hz
  let L : E F S →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨fun x => Z F S μ x.val.1 x.val.2 f, by
        apply continuous_iff_continuousAt.mpr
        intro x
        let B : Set K := {y | y.val.1 = x.val.1}
        have hB : B ∈ 𝓝 x :=
          (continuous_fst.comp continuous_subtype_val).continuousAt.eventually
            ((isOpen_discrete {x.val.1}).mem_nhds (mem_singleton _))
        have hmap : MapsTo (fun y : K => y.val.2) B (T x.val.1) := by
          intro y hy
          change y.val.1 = x.val.1 at hy
          simpa only [← hy, T, mem_preimage, Prod.mk.eta] using y.property
        have hC := ((sLocalProductZetaContinued_continuousOn_regular F S μ x.val.1 f).mono (hr x.val.1)).comp
          (continuous_snd.comp continuous_subtype_val).continuousOn hmap
        apply ((hC x rfl).continuousAt hB).congr_of_eventuallyEq
        filter_upwards [hB] with y hy
        change y.val.1 = x.val.1 at hy
        simp only [Function.comp_apply, hy]⟩
      map_add' := fun f g => ContinuousMap.ext fun x => map_add (Z F S μ x.val.1 x.val.2) f g
      map_smul' := fun c f => ContinuousMap.ext fun x => map_smul (Z F S μ x.val.1 x.val.2) c f }
  have hfib (ω) : ∃ p : Seminorm ℂ (E F S), Continuous p ∧
      ∀ z ∈ T ω, ∀ f, ‖Z F S μ ω z f‖ ≤ p f := by
    letI : CompactSpace (T ω) := isCompact_iff_compactSpace.mp (hT ω)
    let A := sLocalMellinCompact F S μ ω (T ω) (hT ω) (hr ω)
    refine ⟨(normSeminorm ℂ (C(T ω, ℂ))).comp A.toLinearMap, continuous_norm.comp A.continuous,
      fun z hz f => ?_⟩
    exact (ContinuousMap.norm_coe_le_norm (A f) ⟨z, hz⟩)
  choose p hp hP using hfib
  let I := ((hK.image continuous_fst).finite_of_discrete).toFinset
  let P := I.sup p
  refine ⟨L, ?_⟩
  apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ _) L
  intro i
  apply Seminorm.continuous_of_le (Seminorm.continuous_finsetSup (s := I) (fun ω _ => hp ω))
  intro f
  apply (ContinuousMap.norm_le _ (apply_nonneg P f)).mpr
  intro x
  have hi : x.val.1 ∈ I := Set.Finite.mem_toFinset _ |>.mpr ⟨x, x.property, rfl⟩
  exact (hP x.val.1 x.val.2 x.property f).trans ((Finset.le_sup hi : p x.val.1 ≤ P) f)


@[simp] theorem sLocalMellinOnCompact_apply (K : Set (Characters F S × ℂ)) (hK : IsCompact K)
    (hreg : ∀ x ∈ K, x.2 ∈ sLocalMellinRegularSet F S x.1) (f : E F S) (x : K) :
    sLocalMellinOnCompact F S μ K hK hreg f x =
      sLocalProductZetaContinued F S μ x.val.1 (sLocalRealArchParameters F S x.val.1)
        (sLocalComplexArchParameters F S x.val.1) f x.val.2 := rfl

private abbrev SIdeles := (SAdeles F S)ˣ

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

local instance : MeasurableMul (SIdeles F S) :=
  ⟨fun g => ((continuous_const (y := g)).mul continuous_id).measurable,
    fun g => (continuous_id.mul (continuous_const (y := g))).measurable⟩

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
/-- Left Haar substitution gives the covariance formula on the initial
integral. -/
theorem sLocalIdelicZetaIntegral_leftTranslate (η : Measure (SIdeles F S)) [η.IsHaarMeasure]
    (ω : Characters F S) (g : SIdeles F S) (f : E F S) (z : ℂ) :
    sLocalIdelicZetaIntegral F S η ω (sLocalBruhatLeftTranslate F S g f) z =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) * sLocalIdelicZetaIntegral F S η ω f z := by
  unfold sLocalIdelicZetaIntegral
  rw [← integral_mul_left_eq_self _ g, ← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun x => ?_
  have hg : g⁻¹.val * (g * x).val = x.val := by
    rw [Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
  simp only [sLocalIdelicZetaIntegrand, sLocalBruhatLeftTranslate_restrict,
    QuotientGroup.mk_mul, sLocalZetaWeight_mul]
  rw [show g.inv * (g * x).val = x.val from hg]
  ring

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

set_option maxHeartbeats 750000 in
/-- The dilation covariance of the continued transform as an equality of
meromorphic functions. -/
theorem sLocalContinuedZeta_leftTranslate (ω : Characters F S)
    (g : SIdeles F S) (f : E F S) :
    sLocalMeromorphicZetaComponent F S μ ω (sLocalBruhatLeftTranslate F S g f) =
      zeroMeromorphicGerms.mkQ (⟨fun z => sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
        Z F S μ ω z f, by
        apply Meromorphic.mul _ (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f)
        intro z
        unfold sLocalZetaWeight
        exact (((analyticAt_id.mul analyticAt_const).cexp).mul analyticAt_const).meromorphicAt⟩ :
        meromorphicRepresentatives) := by
  apply sLocalMeromorphicZetaComponent_eq_of_agrees
  intro z hz
  change sLocalZetaWeight F S ω z (QuotientGroup.mk g) * Z F S μ ω z f = _
  let η := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : η.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  change _ = sLocalIdelicZetaIntegral F S η ω (sLocalBruhatLeftTranslate F S g f) z
  rw [sLocalIdelicZetaIntegral_leftTranslate F S η]
  exact congrArg (_ * ·) ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz)

/-- On the positive half-plane, the continued transform satisfies
dilation covariance directly by substitution in the defining integral. -/
theorem sLocalProductZetaContinued_leftTranslate_right (ω : Characters F S)
    (g : SIdeles F S) (f : E F S) {z : ℂ} (hz : 0 < z.re) :
    Z F S μ ω z (sLocalBruhatLeftTranslate F S g f) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) * Z F S μ ω z f := by
  let η := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : η.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  calc
    _ = sLocalIdelicZetaIntegral F S η ω (sLocalBruhatLeftTranslate F S g f) z :=
      (sLocalIdelicZeta_meromorphic_continuation F S μ ω _).2 hz
    _ = sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
        sLocalIdelicZetaIntegral F S η ω f z :=
      sLocalIdelicZetaIntegral_leftTranslate F S η ω g f z
    _ = _ := congrArg (_ * ·) ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f).2 hz).symm

set_option maxHeartbeats 750000 in
/-- Dilation covariance holds pointwise at every regular parameter of the
continued S-local Mellin transform. -/
theorem sLocalProductZetaContinued_leftTranslate (ω : Characters F S)
    (g : SIdeles F S) (f : E F S) {z : ℂ} (hz : z ∈ sLocalMellinRegularSet F S ω) :
    sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
        (sLocalComplexArchParameters F S ω) (sLocalBruhatLeftTranslate F S g f) z =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) *
        sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
          (sLocalComplexArchParameters F S ω) f z := by
  let A (w : ℂ) := Z F S μ ω w (sLocalBruhatLeftTranslate F S g f)
  let B (w : ℂ) := sLocalZetaWeight F S ω w (QuotientGroup.mk g) * Z F S μ ω w f
  have h := sLocalContinuedZeta_leftTranslate F S μ ω g f
  simp only [sLocalMeromorphicZetaComponent, LinearMap.comp_apply] at h
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  change ∀ w : ℂ, (A - B) =ᶠ[𝓝[≠] w] 0 at h
  have ha : ContinuousAt A z :=
    (sLocalProductZetaContinued_continuousOn_regular F S μ ω _ z hz).continuousAt ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds hz)
  have hc : ContinuousAt (fun w => sLocalZetaWeight F S ω w (QuotientGroup.mk g)) z := by
    unfold sLocalZetaWeight
    fun_prop
  have hB : ContinuousAt B z :=
    hc.mul ((sLocalProductZetaContinued_continuousOn_regular F S μ ω f z hz).continuousAt
      ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds hz))
  change A z = B z
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique ((ha.sub hB).tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (h z).symm)


end

end Masullo
