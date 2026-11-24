import SchwartzReflexivity
import ThetaTranslationContinuity
import QuotientDuals
import SLocalBruhatStructure
import SLocalZetaProduct

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1000000

/-- Strong closure of a family is the annihilator of its simultaneous kernel. -/
theorem strongDual_closure_span_eq_annihilator {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (e : E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E)) (he : ∀ x T, e x T = T x)
    (l : ι → StrongDual ℂ E) (N : Submodule ℂ E) (hN : ∀ x, x ∈ N ↔ ∀ i, l i x = 0) :
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ E)) =
      {T : StrongDual ℂ E | ∀ x ∈ N, T x = 0} := by
  let D := StrongDual ℂ E
  letI : Module ℝ D := Module.restrictScalars ℝ ℂ D
  letI : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  letI : LocallyConvexSpace ℝ D := strongDual_withBoundedSeminorms.toLocallyConvexSpace
  let M := Submodule.span ℂ (range l)
  ext T
  constructor
  · intro hT x hx
    let ev : D →L[ℂ] ℂ := e x
    have hh : M ≤ ev.ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr ((he x (l i)).trans ((hN x).mp hx i))
    have he' : T ∈ ev.ker := closure_minimal hh ev.isClosed_ker hT
    exact (he x T).symm.trans (LinearMap.mem_ker.mp he')
  · intro hT
    by_contra hOut
    obtain ⟨L, hL, hz⟩ := exists_dual_eq_zero_on_submodule_of_notMem (𝕜 := ℂ)
      M.topologicalClosure M.isClosed_topologicalClosure hOut
    obtain ⟨x, rfl⟩ := e.surjective L
    have hx : x ∈ N := (hN x).mpr fun i ↦ (he x (l i)).symm.trans
      (hz _ (M.le_topologicalClosure (Submodule.subset_span (mem_range_self i))))
    exact hL ((he x T).trans (hT x hx))

/-- Enlarging a strongly generating family inside the same range preserves its closed span. -/
theorem closure_span_eq_of_generating_subfamily {D : Type*} [AddCommGroup D] [Module ℂ D]
    [TopologicalSpace D] (A : Submodule ℂ D) {U V : Set D}
    (hU : closure (Submodule.span ℂ U : Set D) = closure (A : Set D))
    (hUV : U ⊆ V) (hV : V ⊆ A) :
    closure (Submodule.span ℂ V : Set D) = closure (A : Set D) := by
  apply le_antisymm (closure_mono (Submodule.span_le.mpr hV))
  rw [← hU]
  exact closure_mono (Submodule.span_mono hUV)

/-- A spectral interval containing two frequencies has vectors that are not eigenvectors. -/
theorem spectralInterval_range_not_eigenvectors :
    let A := Icc (0 : ℝ) 1
    let P (x : ℂ × ℂ) := (if 0 ∈ A then x.1 else 0, if 1 ∈ A then x.2 else 0)
    let U (t : ℝ) (x : ℂ × ℂ) := (x.1, Complex.exp ((t : ℂ) * Complex.I) * x.2)
    ∃ x ∈ range P, ¬ ∃ c : ℂ, U Real.pi x = c • x := by
  refine ⟨(1, 1), ⟨(1, 1), by simp⟩, ?_⟩
  rintro ⟨c, hc⟩
  have h₁ : (1 : ℂ) = c := by
    have h := congrArg Prod.fst hc
    simpa only [Prod.smul_fst, smul_eq_mul, mul_one] using h
  have h₂ : (-1 : ℂ) = c := by
    have h := congrArg Prod.snd hc
    simpa only [Prod.smul_snd, smul_eq_mul, mul_one, Complex.exp_pi_mul_I] using h
  exact (by norm_num : (1 : ℂ) ≠ -1) (h₁.trans h₂.symm)

universe u

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S
private abbrev Θ := SLocalThetaQuotient F S
private abbrev N := (sLocalThetaOperator F S).ker

/-- The transpose of the actual S-local theta quotient map. -/
def sLocalThetaTranspose : StrongDual ℂ (Θ F S) →L[ℂ] StrongDual ℂ (E F S) :=
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ (N F S).mkQL

theorem sLocalThetaTranspose_injective : Injective (sLocalThetaTranspose F S) := by
  intro U V h
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N F S) q
  exact DFunLike.congr_fun h f

theorem sLocalThetaTranspose_invariant (T : StrongDual ℂ (Θ F S))
    (g : (SAdeles F S)ˣ) (hg : (QuotientGroup.mk g : SIdeleQuotient F S) = 1) (f : E F S) :
    sLocalThetaTranspose F S T (sLocalBruhatLeftTranslate F S g f) = sLocalThetaTranspose F S T f := by
  change T (Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S g f)) = T (Submodule.Quotient.mk f)
  rw [← sLocalThetaTranslateIdeles_mk, ← show sLocalThetaTranslate F S (QuotientGroup.mk g) =
    sLocalThetaTranslateIdeles F S g from rfl, hg, sLocalThetaTranslate_one]

theorem sLocalThetaInvariantDistributions_isClosed :
    IsClosed {T : StrongDual ℂ (E F S) | ∀ g : (SAdeles F S)ˣ,
      (QuotientGroup.mk g : SIdeleQuotient F S) = 1 →
        ∀ f, T (sLocalBruhatLeftTranslate F S g f) = T f} := by
  let G := {g : (SAdeles F S)ˣ | (QuotientGroup.mk g : SIdeleQuotient F S) = 1}
  have h : {T : StrongDual ℂ (E F S) | ∀ g : (SAdeles F S)ˣ,
      (QuotientGroup.mk g : SIdeleQuotient F S) = 1 →
        ∀ f, T (sLocalBruhatLeftTranslate F S g f) = T f} =
      ⋂ (g : G) (f : E F S), {T : StrongDual ℂ (E F S) |
        T (sLocalBruhatLeftTranslate F S g.val f) = T f} := by
    ext T
    simp [G]
  rw [h]
  exact isClosed_iInter fun g ↦ isClosed_iInter fun f ↦
    isClosed_eq (continuous_eval_const _) (continuous_eval_const _)

local instance : MeasurableSpace (SIdeleQuotient F S) := borel _
local instance : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

private theorem thetaHaar_weaklyRegular : ν.WeaklyRegular := by
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  letI := sLocalIdeles_secondCountable F S
  letI : SecondCountableTopology (SIdeleQuotient F S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : SecondCountableTopology (K F S) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : TopologicalSpace.PseudoMetrizableSpace (K F S) := inferInstance
  letI := sLocalThetaNormOne_compact F S
  letI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  infer_instance

local instance : ContinuousSMul ℂ (E F S) :=
  (PolynormableSpace.withSeminorms ℂ (E F S)).continuousSMul

private theorem sLocalThetaTest_span_eq {ι : Type*}
    (l : ι → StrongDual ℂ (E F S)) (M : Submodule ℂ (E F S))
    (hM : ∀ f, f ∈ M ↔ ∀ i, l i f = 0) :
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ (E F S))) =
      {T : StrongDual ℂ (E F S) | ∀ f ∈ M, T f = 0} := by
  letI : UniformSpace (E F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (E F S) := sLocalBruhat_complete F S
  letI : BarrelledSpace ℂ (E F S) := sLocalBruhat_barrelled F S
  letI : PolynormableSpace ℂ (E F S) := (sLocalBruhat_nuclear F S).2.1
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (sLocalBruhat_nuclear F S)
  exact strongDual_closure_span_eq_annihilator e he l M hM

private theorem isClosed_annihilator (M : Submodule ℂ (E F S)) :
    IsClosed {T : StrongDual ℂ (E F S) | ∀ x ∈ M, T x = 0} := by
  have h : {T : StrongDual ℂ (E F S) | ∀ x ∈ M, T x = 0} =
      ⋂ x : M, {T : StrongDual ℂ (E F S) | T x.val = 0} := by
    ext T
    simp
  rw [h]
  exact isClosed_iInter fun x ↦ isClosed_eq (continuous_eval_const x.val) continuous_const

/-- The ordinary theta transpose is strongly generated by one vertical line
in each character component. Nonzero normalizing factors preserve the span. -/
theorem sLocalThetaTranspose_closure_range_vertical (σ : ℝ) (hσ : 0 < σ)
    (d : PontryaginDual (K F S) × ℝ → ℂ) (hd : ∀ i, d i ≠ 0) :
    closure (range (sLocalThetaTranspose F S)) =
      closure (Submodule.span ℂ (range fun i : PontryaginDual (K F S) × ℝ ↦ d i •
        sLocalThetaZetaCLM F S ν i.1 ((σ : ℂ) + (i.2 : ℂ) * Complex.I)
          (by simpa using hσ)) : Set (StrongDual ℂ (E F S))) := by
  let M := N F S
  let l (i : PontryaginDual (K F S) × ℝ) := d i • sLocalThetaZetaCLM F S ν i.1
    ((σ : ℂ) + (i.2 : ℂ) * Complex.I) (by simpa using hσ)
  letI := thetaHaar_weaklyRegular F S ν
  have hM (f : E F S) : f ∈ M ↔ ∀ i, l i f = 0 := by
    change sLocalThetaOperator F S f = 0 ↔ _
    rw [sLocalTheta_zero_iff_verticalZeta F S ν f σ hσ]
    constructor
    · intro h i
      change d i * sLocalThetaZetaIntegral F S ν i.1 f ((σ : ℂ) + (i.2 : ℂ) * Complex.I) = 0
      rw [h i.1 i.2, mul_zero]
    · intro h ω y
      exact (mul_eq_zero.mp (h (ω,y))).resolve_left (hd (ω,y))
  change closure (range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) =
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ (E F S)))
  rw [quotientDual_strongRange, sLocalThetaTest_span_eq F S l M hM]
  exact (isClosed_annihilator F S M).closure_eq

/-- The homogeneous theta kernel, exhibited as the joint kernel of the Mellin evaluations. -/
def sLocalHomogeneousThetaKernel (ω : PontryaginDual (K F S)) : Submodule ℂ (E F S) :=
  ⨅ y : ℝ, (sLocalThetaZetaCLM F S ν ω ((1 : ℂ) + (y : ℂ) * Complex.I) (by simp)).ker

theorem mem_sLocalHomogeneousThetaKernel_iff (ω : PontryaginDual (K F S)) (f : E F S) :
    f ∈ sLocalHomogeneousThetaKernel F S ν ω ↔
      ∀ q, sLocalHomogeneousTheta F S ν ω f.val q = 0 := by
  rw [sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω f 1 zero_lt_one]
  simp only [sLocalHomogeneousThetaKernel, Submodule.mem_iInf, LinearMap.mem_ker, Complex.ofReal_one]
  rfl

abbrev SLocalHomogeneousThetaQuotient (ω : PontryaginDual (K F S)) :=
  E F S ⧸ sLocalHomogeneousThetaKernel F S ν ω

/-- Transpose of the S-local homogeneous quotient map in the strong topology. -/
def sLocalHomogeneousThetaTranspose (ω : PontryaginDual (K F S)) :
    StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω) →L[ℂ] StrongDual ℂ (E F S) :=
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ (sLocalHomogeneousThetaKernel F S ν ω).mkQL

theorem sLocalHomogeneousThetaTranspose_injective (ω : PontryaginDual (K F S)) :
    Injective (sLocalHomogeneousThetaTranspose F S ν ω) := by
  intro U V h
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (sLocalHomogeneousThetaKernel F S ν ω) q
  exact DFunLike.congr_fun h f

theorem sLocalHomogeneousTheta_leftTranslate_normOne (ω : PontryaginDual (K F S))
    (k : K F S) (g : (SAdeles F S)ˣ) (hg : (QuotientGroup.mk g : SIdeleQuotient F S) = k.val)
    (f : E F S) (q : SIdeleQuotient F S) :
    sLocalHomogeneousTheta F S ν ω (sLocalBruhatLeftTranslate F S g f).val q =
      (ω k : ℂ) * sLocalHomogeneousTheta F S ν ω f.val q := by
  have he : sLocalHomogeneousTheta F S ν ω (sLocalBruhatLeftTranslate F S g f).val q =
      sLocalHomogeneousTheta F S ν ω f.val (k.val⁻¹ * q) := by
    unfold sLocalHomogeneousTheta
    refine integral_congr_ae (.of_forall fun a ↦ ?_)
    change (ω a : ℂ) * sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S g f) (a.val * q) =
      (ω a : ℂ) * sLocalThetaOperator F S f (a.val * (k.val⁻¹ * q))
    rw [sLocalThetaOperator_leftTranslate, hg, mul_left_comm k.val⁻¹ a.val q]
  rw [he, show k.val⁻¹ = (k⁻¹).val from rfl, sLocalHomogeneousTheta_translate,
    map_inv, Circle.coe_inv, inv_inv]

theorem sLocalHomogeneousThetaTranspose_homogeneous (ω : PontryaginDual (K F S))
    (T : StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω))
    (k : K F S) (g : (SAdeles F S)ˣ) (hg : (QuotientGroup.mk g : SIdeleQuotient F S) = k.val)
    (f : E F S) :
    sLocalHomogeneousThetaTranspose F S ν ω T (sLocalBruhatLeftTranslate F S g f) =
      (ω k : ℂ) * sLocalHomogeneousThetaTranspose F S ν ω T f := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  change T (M.mkQL (sLocalBruhatLeftTranslate F S g f)) = (ω k : ℂ) * T (M.mkQL f)
  rw [← smul_eq_mul, ← map_smul, ← map_smul]
  apply congrArg T
  change (Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S g f) : E F S ⧸ M) =
    Submodule.Quotient.mk ((ω k : ℂ) • f)
  rw [Submodule.Quotient.eq]
  change _ ∈ sLocalHomogeneousThetaKernel F S ν ω
  rw [sLocalHomogeneousThetaKernel, Submodule.mem_iInf]
  intro y
  let z : ℂ := 1 + (y : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  let L := sLocalThetaZetaCLM F S ν ω z hz
  change L (sLocalBruhatLeftTranslate F S g f - (ω k : ℂ) • f) = 0
  rw [map_sub, map_smul, sub_eq_zero]
  change sLocalThetaZetaIntegral F S ν ω (sLocalBruhatLeftTranslate F S g f) z =
    (ω k : ℂ) * sLocalThetaZetaIntegral F S ν ω f z
  rw [(sLocalThetaZeta_integrable_eq_radial F S ν ω _ z hz).2,
    (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2, sLocalRadialMellin, sLocalRadialMellin,
    ← integral_const_mul]
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  let q : SIdeleQuotient F S := QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))
  change Complex.exp (z * (t : ℂ)) *
    sLocalHomogeneousTheta F S ν ω (sLocalBruhatLeftTranslate F S g f).val q =
      (ω k : ℂ) * (Complex.exp (z * (t : ℂ)) * sLocalHomogeneousTheta F S ν ω f.val q)
  rw [sLocalHomogeneousTheta_leftTranslate_normOne F S ν ω k g hg f,
    mul_left_comm (Complex.exp (z * (t : ℂ)))]

theorem sLocalThetaHomogeneousDistributions_isClosed (ω : PontryaginDual (K F S)) :
    IsClosed {T : StrongDual ℂ (E F S) | ∀ (k : K F S) (g : (SAdeles F S)ˣ),
      (QuotientGroup.mk g : SIdeleQuotient F S) = k.val →
        ∀ f, T (sLocalBruhatLeftTranslate F S g f) = (ω k : ℂ) * T f} := by
  let G (k : K F S) := {g : (SAdeles F S)ˣ | (QuotientGroup.mk g : SIdeleQuotient F S) = k.val}
  have h : {T : StrongDual ℂ (E F S) | ∀ (k : K F S) (g : (SAdeles F S)ˣ),
      (QuotientGroup.mk g : SIdeleQuotient F S) = k.val →
        ∀ f, T (sLocalBruhatLeftTranslate F S g f) = (ω k : ℂ) * T f} =
      ⋂ (k : K F S) (g : G k) (f : E F S), {T : StrongDual ℂ (E F S) |
        T (sLocalBruhatLeftTranslate F S g.val f) = (ω k : ℂ) * T f} := by
    ext T
    simp [G]
  rw [h]
  exact isClosed_iInter fun k ↦ isClosed_iInter fun g ↦ isClosed_iInter fun f ↦
    isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const _))

/-- The homogeneous transpose range is strongly generated by the evaluations on any
line of absolute convergence in its character component. -/
theorem sLocalHomogeneousThetaTranspose_closure_range_vertical (ω : PontryaginDual (K F S))
    (σ : ℝ) (hσ : 0 < σ) (d : ℝ → ℂ) (hd : ∀ y, d y ≠ 0) :
    closure (range (sLocalHomogeneousThetaTranspose F S ν ω)) =
      closure (Submodule.span ℂ (range fun y : ℝ ↦ d y •
        sLocalThetaZetaCLM F S ν ω ((σ : ℂ) + (y : ℂ) * Complex.I) (by simpa using hσ)) :
        Set (StrongDual ℂ (E F S))) := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let l (y : ℝ) := d y • sLocalThetaZetaCLM F S ν ω
    ((σ : ℂ) + (y : ℂ) * Complex.I) (by simpa using hσ)
  have hM (f : E F S) : f ∈ M ↔ ∀ y, l y f = 0 := by
    rw [mem_sLocalHomogeneousThetaKernel_iff, sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω f σ hσ]
    apply forall_congr'
    intro y
    change sLocalThetaZetaIntegral F S ν ω f ((σ : ℂ) + (y : ℂ) * Complex.I) = 0 ↔
      d y * sLocalThetaZetaIntegral F S ν ω f ((σ : ℂ) + (y : ℂ) * Complex.I) = 0
    exact ⟨fun h ↦ by rw [h, mul_zero], fun h ↦ (mul_eq_zero.mp h).resolve_left (hd y)⟩
  change closure (range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) =
    closure (Submodule.span ℂ (range l) : Set (StrongDual ℂ (E F S)))
  rw [quotientDual_strongRange, sLocalThetaTest_span_eq F S l M hM]
  exact (isClosed_annihilator F S M).closure_eq

private abbrev reciprocalEuler (ω : PontryaginDual (K F S)) (z : ℂ) : ℂ :=
  archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z *
    sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω) z

private theorem reciprocalEuler_ne_zero (ω : PontryaginDual (K F S)) {z : ℂ} (hz : 0 < z.re) :
    reciprocalEuler F S ω z ≠ 0 := by
  apply mul_ne_zero _ (sLocalFiniteZetaDenominator_ne_zero_of_pos F S _ z hz)
  apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
  · exact fun i => by simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  · exact fun i => by simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz

/-- The Gaussian-normalization factor on a positive line is the reciprocal Euler product. -/
def sLocalThetaNormalizedLineTestEval (σ : ℝ) (hσ : 0 < σ)
    (ω : PontryaginDual (K F S)) (y : ℝ) : StrongDual ℂ (E F S) :=
  let z := (σ : ℂ) + (y : ℂ) * Complex.I
  reciprocalEuler F S ω z • sLocalThetaZetaCLM F S ν ω z (by simpa [z] using hσ)

/-- The normalized Mellin evaluations are eigendistributions for the actual S-idelic action. -/
theorem sLocalThetaNormalizedLineTestEval_translate (σ : ℝ) (hσ : 0 < σ)
    (ω : PontryaginDual (K F S)) (y : ℝ) (g : (SAdeles F S)ˣ) (f : E F S) :
    sLocalThetaNormalizedLineTestEval F S ν σ hσ ω y (sLocalBruhatLeftTranslate F S g f) =
      sLocalZetaWeight F S ω ((σ : ℂ) + (y : ℂ) * Complex.I) (QuotientGroup.mk g) *
        sLocalThetaNormalizedLineTestEval F S ν σ hσ ω y f := by
  let z := (σ : ℂ) + (y : ℂ) * Complex.I
  let a : SIdeleQuotient F S := QuotientGroup.mk g
  let μ := sLocalClassHaar F S ν
  letI : μ.IsHaarMeasure := sLocalClassHaar_isHaar F S ν
  let χ := sLocalZetaWeight F S ω z
  let G (q : SIdeleQuotient F S) := χ q * sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S g f) q
  change reciprocalEuler F S ω z * (∫ q, G q ∂μ) =
    χ a * (reciprocalEuler F S ω z * (∫ q, χ q * sLocalThetaOperator F S f q ∂μ))
  have he : (∫ q, G q ∂μ) = χ a * (∫ q, χ q * sLocalThetaOperator F S f q ∂μ) := by
    rw [← integral_const_mul, ← integral_mul_left_eq_self G a]
    refine integral_congr_ae (.of_forall fun q ↦ ?_)
    change χ (a * q) * sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S g f) (a * q) =
      χ a * (χ q * sLocalThetaOperator F S f q)
    rw [sLocalThetaOperator_leftTranslate, show (QuotientGroup.mk g : SIdeleQuotient F S) = a from rfl,
      inv_mul_cancel_left]
    exact (congrArg (fun c : ℂ ↦ c * sLocalThetaOperator F S f q)
      (sLocalZetaWeight_mul F S ω z a q)).trans (mul_assoc _ _ _)
  rw [he, mul_left_comm]

/-- The corrected strong generating statements in Theorem 5.5.3.2 hold with
the normalized eigendistributions on any one positive line in each component. -/
theorem sLocalThetaTranspose_normalized_strongGeneration (σ : ℝ) (hσ : 0 < σ) :
    (∀ ω : PontryaginDual (K F S),
      closure (range (sLocalHomogeneousThetaTranspose F S ν ω)) =
        closure (Submodule.span ℂ (range (sLocalThetaNormalizedLineTestEval F S ν σ hσ ω)) :
          Set (StrongDual ℂ (E F S)))) ∧
    closure (range (sLocalThetaTranspose F S)) =
      closure (Submodule.span ℂ (range fun i : PontryaginDual (K F S) × ℝ ↦
        sLocalThetaNormalizedLineTestEval F S ν σ hσ i.1 i.2) : Set (StrongDual ℂ (E F S))) := by
  have hz (y : ℝ) : 0 < ((σ : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hσ
  constructor
  · intro ω
    exact sLocalHomogeneousThetaTranspose_closure_range_vertical F S ν ω σ hσ
      (fun y ↦ reciprocalEuler F S ω ((σ : ℂ) + (y : ℂ) * Complex.I))
      (fun y ↦ reciprocalEuler_ne_zero F S ω (hz y))
  · have h := sLocalThetaTranspose_closure_range_vertical F S ν σ hσ
      (fun i ↦ reciprocalEuler F S i.1 ((σ : ℂ) + (i.2 : ℂ) * Complex.I))
      (fun i ↦ reciprocalEuler_ne_zero F S i.1 (hz i.2))
    exact h

end
end Masullo
