import WeilSigmaCompactLocalization
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Analysis.Real.Cardinality

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

private abbrev RealGroup := Multiplicative ℝ
private abbrev DiscreteRealGroup := WithDiscreteTopology RealGroup

private def discreteRealGroupEquiv : DiscreteRealGroup ≃ RealGroup :=
  { toFun := WithTopology.ofTopology
    invFun := WithTopology.toTopology (⊥ : TopologicalSpace RealGroup)
    left_inv := by intro x; cases x; rfl
    right_inv := fun _ => rfl }

private instance : CommGroup DiscreteRealGroup := discreteRealGroupEquiv.commGroup

private abbrev RealProduct := DiscreteRealGroup × RealGroup

local instance : MeasurableSpace RealGroup := inferInstanceAs (MeasurableSpace ℝ)
local instance : BorelSpace RealGroup := inferInstanceAs (BorelSpace ℝ)
local instance : MeasurableSpace RealProduct := borel _
local instance : BorelSpace RealProduct := ⟨rfl⟩

private def realFiber : Subgroup RealProduct := (MonoidHom.fst DiscreteRealGroup RealGroup).ker

local instance : MeasurableSpace (RealProduct ⧸ realFiber) := borel _

private theorem realFiber_closed : IsClosed (realFiber : Set RealProduct) :=
  isClosed_eq continuous_fst continuous_const

private def realToFiber : RealGroup ≃ₜ* realFiber where
  toFun t := ⟨(1, t), rfl⟩
  invFun x := x.val.2
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext x.property.symm rfl)
  map_mul' _ _ := Subtype.ext (Prod.ext (one_mul _).symm rfl)
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _
  continuous_invFun := continuous_snd.comp continuous_subtype_val

private def realGroupVolume : Measure RealGroup := (volume : Measure ℝ)

private theorem realGroupVolume_haar : realGroupVolume.IsHaarMeasure where
  map_mul_left_eq_self x := Measure.IsAddLeftInvariant.map_add_left_eq_self
    (μ := (volume : Measure ℝ)) (Multiplicative.toAdd x)
  lt_top_of_isCompact K hK := IsCompact.measure_lt_top (μ := (volume : Measure ℝ)) hK
  open_pos U hU hne := (hU.measure_pos (volume : Measure ℝ) hne).ne'

private def realFiberMeasure : Measure realFiber :=
  realGroupVolume.map realToFiber

private theorem realFiberMeasure_haar : realFiberMeasure.IsHaarMeasure := by
  letI := realGroupVolume_haar
  exact realToFiber.toMulEquiv.isHaarMeasure_map _ realToFiber.continuous realToFiber.symm.continuous

private theorem realFiberMeasure_regular : realFiberMeasure.Regular := by
  letI : realGroupVolume.Regular := inferInstanceAs ((volume : Measure ℝ).Regular)
  exact Measure.Regular.map realToFiber.toHomeomorph

private theorem realFiberMeasure_nullSingleton : NullSingletonClass realFiberMeasure := by
  constructor
  intro x
  have hm : Measurable (realToFiber : RealGroup → realFiber) := realToFiber.continuous.measurable
  rw [realFiberMeasure, Measure.map_apply hm (measurableSet_singleton x),
    show realToFiber ⁻¹' {x} = {realToFiber.symm x} from by
      ext y
      exact realToFiber.toEquiv.apply_eq_iff_eq_symm_apply]
  exact measure_singleton (μ := (volume : Measure ℝ)) _

private def realSlice : Set RealProduct := {x | x.2 = 1}

private def realSliceIndicator : RealProduct → ℂ := realSlice.indicator (fun _ => 1)

private theorem realSliceIndicator_measurable : Measurable realSliceIndicator :=
  measurable_const.indicator (isClosed_eq continuous_snd continuous_const).measurableSet

private theorem realSliceIndicator_not_integrable (μ : Measure RealProduct)
    [μ.IsHaarMeasure] [μ.Regular] : ¬ Integrable realSliceIndicator μ := by
  intro h
  obtain ⟨H, _, hσ, hH⟩ := exists_open_sigmaCompact_subgroup_of_integrable μ h
  have hp : IsSigmaCompact (Prod.fst '' (H : Set RealProduct)) :=
    hσ.image continuous_fst
  have hu : Prod.fst '' (H : Set RealProduct) = (univ : Set DiscreteRealGroup) := by
    refine eq_univ_of_forall fun x => ⟨(x, 1), hH ?_, rfl⟩
    change realSliceIndicator (x, 1) ≠ 0
    rw [realSliceIndicator, Set.indicator_of_mem (show (x, (1 : RealGroup)) ∈ realSlice from rfl)]
    exact one_ne_zero
  obtain ⟨K, hc, hcover⟩ := hu ▸ hp
  have hcount : (univ : Set DiscreteRealGroup).Countable := by
    rw [← hcover]
    exact Set.countable_iUnion fun i => (hc i).finite_of_discrete.countable
  let e : DiscreteRealGroup ≃ ℝ := discreteRealGroupEquiv.trans Multiplicative.toAdd
  have hcountReal : (univ : Set ℝ).Countable := by
    simpa only [image_univ, e.surjective.range_eq] using hcount.image e
  exact Cardinal.not_countable_real hcountReal

private theorem realSliceIndicator_fiber_zero (x : RealProduct) :
    (∫⁻ h : realFiber, ‖realSliceIndicator (x * (h : RealProduct))‖₊ ∂realFiberMeasure) = 0 := by
  letI := realFiberMeasure_nullSingleton
  rw [← lintegral_zero]
  apply lintegral_congr_ae
  filter_upwards [realFiberMeasure.ae_ne (realToFiber x.2⁻¹)] with h hh
  have hmiss : x * (h : RealProduct) ∉ realSlice := by
    intro he
    change x.2 * h.val.2 = 1 at he
    have hinv : h.val.2 = x.2⁻¹ := eq_inv_of_mul_eq_one_right he
    exact hh (Subtype.ext (Prod.ext h.property hinv))
  rw [realSliceIndicator, Set.indicator_of_notMem hmiss, nnnorm_zero, ENNReal.coe_zero]

/-- The unrestricted converse in C.4.4.4 fails for regular Haar measure.
Every fibre norm integral vanishes, but the Borel test is not Haar-integrable. -/
theorem weil_converse_arbitraryGroup_counterexample :
    ∃ (μ : Measure RealProduct) (ν : Measure (RealProduct ⧸ realFiber)),
      IsWeilQuotientMeasure realFiber μ realFiberMeasure ν ∧
      Measurable realSliceIndicator ∧
      (∫⁻ q : RealProduct ⧸ realFiber, ∫⁻ h : realFiber, ‖realSliceIndicator (q.out * (h : RealProduct))‖₊
        ∂realFiberMeasure ∂ν) = 0 ∧
      ¬ Integrable realSliceIndicator μ := by
  letI : BorelSpace (RealProduct ⧸ realFiber) := ⟨rfl⟩
  letI := realFiberMeasure_haar
  letI := realFiberMeasure_regular
  let μ : Measure RealProduct := Measure.haar
  obtain ⟨ν, hν, _⟩ :=
    weilQuotientMeasure_existsUnique realFiber realFiber_closed μ realFiberMeasure
  refine ⟨μ, ν, hν, realSliceIndicator_measurable, ?_, realSliceIndicator_not_integrable μ⟩
  simp only [realSliceIndicator_fiber_zero, lintegral_zero]

end
end Masullo
