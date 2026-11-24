import NormTwistCharts
import ArchimedeanWeilCutoffs
import IdelicMellinSummation
import ElementaryVelocity
import BruhatWholeQuotientStages
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ContDiff NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private theorem hasCompactSupport_pullback_proper {X : Type*} [TopologicalSpace X]
    (φ : IdeleClass F → ℂ) (hf : HasCompactSupport φ) (g : X → IdeleClass F)
    (hg : IsProperMap g) : HasCompactSupport (φ ∘ g) := by
  have hPre : IsCompact (g ⁻¹' tsupport φ) := hg.isCompact_preimage hf
  apply hPre.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.preimage hg.continuous)
  exact fun x hx ↦ subset_closure hx

/-- The restriction of a compactly supported idelic test to an actual
infinite-place insertion has compact support. -/
theorem infinitePlaceIdelicTest_hasCompactSupport (φ : IdeleClass F → ℂ)
    (hf : HasCompactSupport φ) (v : InfinitePlace F) :
    HasCompactSupport (φ ∘ infinitePlaceInsertion F v) :=
  hasCompactSupport_pullback_proper F φ hf _ (infinitePlaceInsertion_isProper F v)

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

private theorem elementarySchwartz_contDiff_translatedCover {m n r : ℕ} {D : Type*}
    [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (w : ElementarySchwartz m n r D) (a : ElementaryLCAModel m n r D) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦
      w.val (a + elementaryCoverHom x)) := by
  obtain ⟨t, ht⟩ := elementaryCover_surjective a.2.2.1 a.2.2.2 a.1 a.2.1
  have ha : elementaryCover (a.1, t) a.2.2.1 a.2.2.2 = a := ht
  have he : (fun x ↦ w.val (a + elementaryCoverHom x)) =
      (fun x ↦ w.val (elementaryCover ((a.1, t) + x) a.2.2.1 a.2.2.2)) := by
    funext x
    rw [elementaryCover_add, ha]
  rw [he]
  exact (w.property.1 _ _).comp (contDiff_const.add contDiff_id)

private theorem exists_elementaryCoverLinear {m n r : ℕ} {D V : Type*}
    [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : Multiplicative V →ₜ* Multiplicative (ElementaryLCAModel m n r D)) :
    ∃ L : V →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      ∀ x, q (Multiplicative.ofAdd x) = Multiplicative.ofAdd (elementaryCoverHom (L x)) := by
  obtain ⟨L, hL⟩ := exists_linear_elementaryVelocity (r := r) (F := D) q
  refine ⟨L, fun x ↦ ?_⟩
  have hx : q (Multiplicative.ofAdd ((1 : ℝ) • x)) =
      Multiplicative.ofAdd (elementaryCoverHom ((1 : ℝ) • L x)) := hL x 1
  simpa only [one_smul] using hx

set_option maxHeartbeats 900000 in
/-- Smoothness of a Bruhat test pulled back along an additive vector group,
including translations in any component of the idele class group. -/
theorem bruhatCompactTest_contDiff_vectorOrbit {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (φ : BruhatCompactTest (IdeleClass F)) (g : IdeleClass F)
    (h : Multiplicative V →ₜ* IdeleClass F) :
    ContDiff ℝ ∞ (fun x : V ↦ φ.val.val (g * h (Multiplicative.ofAdd x))) := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let m := mellinClassModulus F
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m :=
    fun t ↦ ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  obtain ⟨P, u, hu⟩ := φ.val.property
  obtain ⟨Q, hPQ⟩ := exists_wholeBruhatStage_refinement m hm hms P
  let w := P.transition Q.val hPQ u
  have hw : Q.val.realize w = φ.val.val :=
    (congrArg Subtype.val (P.inclusion_transition Q.val hPQ u)).trans hu
  let A := ElementaryLCAModel Q.val.2.realDim Q.val.2.torusDim Q.val.2.latticeRank Q.val.2.finiteFactor
  let q : Multiplicative V →ₜ* Multiplicative A := Q.coordinates.comp h
  obtain ⟨L, hL⟩ := exists_elementaryCoverLinear (m := Q.val.2.realDim)
    (n := Q.val.2.torusDim) (r := Q.val.2.latticeRank) (D := Q.val.2.finiteFactor) q
  let a : A := (Q.coordinates g).toAdd
  have hEq : (fun x : V ↦ φ.val.val (g * h (Multiplicative.ofAdd x))) =
      fun x ↦ w.val (a + elementaryCoverHom (L x)) := by
    funext x
    have hEval (y : IdeleClass F) : φ.val.val y = w.val (Q.coordinates y).toAdd :=
      (congrFun hw y).symm.trans (Q.realize_eq_coordinates w y)
    have hx : Q.coordinates (h (Multiplicative.ofAdd x)) =
        Multiplicative.ofAdd (elementaryCoverHom (L x)) := hL x
    calc
      _ = w.val ((Q.coordinates (g * h (Multiplicative.ofAdd x))).toAdd) := hEval _
      _ = w.val (((Q.coordinates g) * Q.coordinates (h (Multiplicative.ofAdd x))).toAdd) :=
        congrArg (fun y : Multiplicative A ↦ w.val y.toAdd) (map_mul Q.coordinates g _)
      _ = _ := congrArg (fun y : Multiplicative A ↦ w.val ((Q.coordinates g * y).toAdd)) hx
  rw [hEq]
  let Lc : V →L[ℝ] _ := ⟨L, L.continuous_of_finiteDimensional⟩
  exact (elementarySchwartz_contDiff_translatedCover w a).comp Lc.contDiff

private def weilExpUnits {K : Type*} [RCLike K] (E : K → K)
    (h₀ : E 0 = 1) (hadd : ∀ x y, E (x + y) = E x * E y)
    (hne : ∀ x, E x ≠ 0) (hc : Continuous E) : Multiplicative K →ₜ* Kˣ where
  toFun t := Units.mk0 (E t.toAdd) (hne _)
  map_one' := Units.ext h₀
  map_mul' a b := Units.ext (hadd a.toAdd b.toAdd)
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    exact ⟨hc.comp continuous_toAdd, (hc.comp continuous_toAdd).inv₀ fun _ ↦ hne _⟩

set_option maxHeartbeats 900000 in
private theorem bruhatCompactTest_localLog_contDiffOn {K : Type*} [RCLike K]
    [FiniteDimensional ℝ K]
    (φ : BruhatCompactTest (IdeleClass F)) (i : Kˣ →ₜ* IdeleClass F)
    (e : Multiplicative K →ₜ* Kˣ) (l : K → K) (hL : ContDiffAt ℝ ∞ l 1)
    (hInv : ∀ᶠ w in 𝓝 (1 : K), (e (Multiplicative.ofAdd (l w))).val = w) :
    ContDiffOn ℝ ∞ (archWeilZeroExtension (φ.val.val ∘ i)) ({0} : Set K)ᶜ := by
  intro x hx
  let u := Units.mk0 x hx
  let p : K → K := fun y ↦ x⁻¹ * y
  have hp : p x = 1 := inv_mul_cancel₀ hx
  have hpD : ContDiff ℝ ∞ p := contDiff_const.mul contDiff_id
  have hpC : Tendsto p (𝓝 x) (𝓝 1) := hp ▸ hpD.continuous.continuousAt.tendsto
  let j := i.comp e
  let g (t : K) := φ.val.val (i u * j (Multiplicative.ofAdd t))
  have hg : ContDiff ℝ ∞ g := bruhatCompactTest_contDiff_vectorOrbit F φ (i u) j
  have hSmooth : ContDiffAt ℝ ∞ (fun y ↦ g (l (p y))) x :=
    hg.contDiffAt.comp x ((hp.symm ▸ hL).comp x hpD.contDiffAt)
  apply (hSmooth.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hn : ∀ᶠ y : K in 𝓝 x, y ≠ 0 := isOpen_compl_singleton.mem_nhds hx
  filter_upwards [hpC.eventually hInv, hn] with y hy hy₀
  have hU : u * e (Multiplicative.ofAdd (l (p y))) = Units.mk0 y hy₀ := by
    apply Units.ext
    change x * (e (Multiplicative.ofAdd (l (p y)))).val = y
    rw [hy]
    exact mul_inv_cancel_left₀ hx y
  have heval : archWeilZeroExtension (φ.val.val ∘ i) y = φ.val.val (i (Units.mk0 y hy₀)) :=
    archWeilZeroExtension_unit _ (Units.mk0 y hy₀)
  rw [heval, ← hU, map_mul]
  rfl

private def infinitePlaceWeilUnitEquiv {K : Type*} [RCLike K] {v : InfinitePlace F}
    (e : K ≃+* v.Completion) (he : Continuous e) (he' : Continuous e.symm) :
    Kˣ ≃ₜ* v.Completionˣ :=
  Units.mapContinuousMulEquiv ⟨e.toMulEquiv, he, he'⟩

/-- Real multiplicative coordinates for the pullback of an idelic test. -/
def realPlaceWeilInsertion (v : InfinitePlace F) (hv : v.IsReal) :
    ℝˣ →ₜ* IdeleClass F :=
  (infinitePlaceInsertion F v).comp (ContinuousMonoidHom.toContinuousMonoidHom (infinitePlaceWeilUnitEquiv F
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous))

/-- Complex multiplicative coordinates for the pullback of an idelic test. -/
def complexPlaceWeilInsertion (v : InfinitePlace F) (hv : v.IsComplex) :
    ℂˣ →ₜ* IdeleClass F :=
  (infinitePlaceInsertion F v).comp (ContinuousMonoidHom.toContinuousMonoidHom (infinitePlaceWeilUnitEquiv F
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous))

theorem realPlaceWeilTest_smooth (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsReal) :
    ContDiffOn ℝ ∞ (archWeilZeroExtension (φ.val.val ∘ realPlaceWeilInsertion F v hv))
      ({0} : Set ℝ)ᶜ := by
  let e := weilExpUnits Real.exp Real.exp_zero Real.exp_add Real.exp_ne_zero Real.continuous_exp
  apply bruhatCompactTest_localLog_contDiffOn F φ _ e Real.log (Real.contDiffAt_log.mpr one_ne_zero)
  filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds (show (1 : ℝ) ∈ Ioi (0 : ℝ) from Set.mem_Ioi.mpr (by norm_num))] with w hw
  exact Real.exp_log hw

theorem complexPlaceWeilTest_smooth (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsComplex) :
    ContDiffOn ℝ ∞ (archWeilZeroExtension (φ.val.val ∘ complexPlaceWeilInsertion F v hv))
      ({0} : Set ℂ)ᶜ := by
  let e := weilExpUnits Complex.exp Complex.exp_zero Complex.exp_add Complex.exp_ne_zero Complex.continuous_exp
  apply bruhatCompactTest_localLog_contDiffOn F φ _ e Complex.log
    ((Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ)
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with w hw
  exact Complex.exp_log (Complex.slitPlane_ne_zero hw)

theorem realPlaceWeilTest_hasCompactSupport (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsReal) :
    HasCompactSupport (φ.val.val ∘ realPlaceWeilInsertion F v hv) := by
  apply hasCompactSupport_pullback_proper F _ φ.property
  exact (infinitePlaceInsertion_isProper F v).comp
    (infinitePlaceWeilUnitEquiv F
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous).toHomeomorph.isProperMap

theorem complexPlaceWeilTest_hasCompactSupport (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsComplex) :
    HasCompactSupport (φ.val.val ∘ complexPlaceWeilInsertion F v hv) := by
  apply hasCompactSupport_pullback_proper F _ φ.property
  exact (infinitePlaceInsertion_isProper F v).comp
    (infinitePlaceWeilUnitEquiv F
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous).toHomeomorph.isProperMap

local instance : MeasurableSpace ℝˣ := borel _
local instance : BorelSpace ℝˣ := ⟨rfl⟩
local instance : MeasurableSpace ℂˣ := borel _
local instance : BorelSpace ℂˣ := ⟨rfl⟩

/-- The normalized real term for an actual idelic Bruhat test. -/
def realPlaceIdelicWeilTerm (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsReal) : ℂ :=
  -realLogFourierDistribution
    (archWeilShiftedTest 1 (φ.val.val ∘ realPlaceWeilInsertion F v hv)
      (realPlaceWeilTest_hasCompactSupport F φ v hv) (realPlaceWeilTest_smooth F φ v hv))

/-- The normalized complex term for an actual idelic Bruhat test. -/
def complexPlaceIdelicWeilTerm (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsComplex) : ℂ :=
  -complexTraceLogFourierDistribution
    (archWeilShiftedTest 2 (φ.val.val ∘ complexPlaceWeilInsertion F v hv)
      (complexPlaceWeilTest_hasCompactSupport F φ v hv) (complexPlaceWeilTest_smooth F φ v hv))

/-- The real-place cutoff in (B.4.4.20) after restriction and normalization. -/
theorem realPlaceIdelicWeilTruncated_tendsto (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsReal) :
    Tendsto (fun ε ↦ (2 : ℝ)⁻¹ •
      (archWeilTruncated 1 realArchMultiplicativeHaar (φ.val.val ∘ realPlaceWeilInsertion F v hv) ε +
        (2 * Real.log ε : ℝ) • φ.val.val 1) +
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) • φ.val.val 1)
      (𝓝[>] 0) (𝓝 (realPlaceIdelicWeilTerm F φ v hv)) := by
  simpa only [Function.comp_apply, map_one, realPlaceIdelicWeilTerm] using
    realWeilTruncated_tendsto (φ.val.val ∘ realPlaceWeilInsertion F v hv)
      (realPlaceWeilTest_hasCompactSupport F φ v hv) (realPlaceWeilTest_smooth F φ v hv)

/-- The complex-place cutoff in (B.4.4.20) after restriction and normalization. -/
theorem complexPlaceIdelicWeilTruncated_tendsto (φ : BruhatCompactTest (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsComplex) :
    Tendsto (fun ε ↦ (2 * Real.pi)⁻¹ •
      (archWeilTruncated 2 complexArchMultiplicativeHaar (φ.val.val ∘ complexPlaceWeilInsertion F v hv) ε +
        (2 * Real.pi * Real.log ε : ℝ) • φ.val.val 1) +
      (2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))) • φ.val.val 1)
      (𝓝[>] 0) (𝓝 (complexPlaceIdelicWeilTerm F φ v hv)) := by
  simpa only [Function.comp_apply, map_one, complexPlaceIdelicWeilTerm] using
    complexWeilTruncated_tendsto (φ.val.val ∘ complexPlaceWeilInsertion F v hv)
      (complexPlaceWeilTest_hasCompactSupport F φ v hv) (complexPlaceWeilTest_smooth F φ v hv)

end
end Masullo
