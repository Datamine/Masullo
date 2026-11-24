import CompactGroupAveraging
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

section RelativelyCompact

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

/-- The first clause of Lemma 4.3.3.7 holds for every measurable subset
with compact closure. No invariance condition on this subset is needed
for existence, uniqueness, or continuity of the restricted average. -/
theorem relativelyCompactSubset_pettis (S : Set X)
    (hc : IsCompact (closure S)) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (ρ : X → E →L[ℂ] E) (hρ : Continuous (fun z : X × E => ρ z.1 z.2)) :
    ∃! Φ : E →L[ℂ] E, ∀ u, HasPositivePettisIntegral (ν.restrict S) (fun x => ρ x u) (Φ u) := by
  let K := closure S
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let μ := (ν.restrict S).comap (Subtype.val : K → X)
  have hKm : MeasurableSet K := isClosed_closure.measurableSet
  have hEmb : MeasurableEmbedding (Subtype.val : K → X) := MeasurableEmbedding.subtype_coe hKm
  have hμ : μ.map Subtype.val = ν.restrict S := by
    rw [show μ = (ν.restrict S).comap (Subtype.val : K → X) from rfl,
      map_comap_subtype_coe hKm, Measure.restrict_restrict hKm, inter_eq_right.mpr (subset_closure : S ⊆ K)]
  haveI : IsFiniteMeasure μ := ⟨by
    have he := congrArg (fun η : Measure X => η univ) hμ
    rw [Measure.map_apply hEmb.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ] at he
    rw [he]
    exact (measure_mono subset_closure).trans_lt (hc.measure_lt_top (μ := ν))⟩
  have hρK : Continuous (fun z : K × E => ρ z.1.val z.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨Φ, hΦ⟩ := compactPettis_clm_exists μ (fun x => ρ x.val) hρK
  refine ⟨Φ, ?_, ?_⟩
  · intro u l
    rw [← hμ, hEmb.integrable_map_iff, hEmb.integral_map]
    exact hΦ u l
  · intro Ψ hΨ
    apply ContinuousLinearMap.ext
    intro u
    apply positivePettis_integral_unique (hΨ u)
    intro l
    rw [← hμ, hEmb.integrable_map_iff, hEmb.integral_map]
    exact hΦ u l

end RelativelyCompact

section OpenSubgroup
variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

omit [T2Space G] in
/-- A corrected form of Lemma 4.3.3.7 and Corollary 4.3.3.8. With a compact
open subgroup, the actual restricted Haar integral has the stated range,
projection property and weak kernel closure. The trivial character gives
the untwisted statement. -/
theorem compactOpenSubset_average (H : OpenSubgroup G) (hH : IsCompact (H : Set G))
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun z : G × E => ρ z.1 z.2))
    (ω : G →* Circle) (hω : Continuous ω) (ν : Measure G) [ν.IsHaarMeasure] :
    let A := (twistedCircleAction ω ρ).comp H.toSubgroup.subtype
    ∃ Φ : E →L[ℂ] E,
      (∀ (u : E) (l : StrongDual ℂ E),
        IntegrableOn (fun g => l (twistedCircleAction ω ρ g u)) H ν ∧
        l (Φ u) = ∫ g in H, l (twistedCircleAction ω ρ g u) ∂ν) ∧
      range Φ = {u | ∀ g ∈ H, ρ g u = (ω g : ℂ) • u} ∧
      IsClosed {u | ∀ g ∈ H, ρ g u = (ω g : ℂ) • u} ∧
      (∀ u, let P := (ν.real H : ℂ)⁻¹ • Φ; P (P u) = P u) ∧
      closure ((toWeakSpace ℂ E) '' (Φ.ker : Set E)) =
        closure ((toWeakSpace ℂ E) '' (actionDifferenceSpan A : Set E)) := by
  let μ := ν.comap (Subtype.val : H → G)
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hEmb : IsOpenEmbedding (H.toSubgroup.subtype : H →* G) :=
    H.isOpen.isOpenEmbedding_subtypeVal
  have he := hEmb.measurableEmbedding
  haveI : μ.IsHaarMeasure := {
    map_mul_left_eq_self a := by
      ext S hS
      have hm : Measurable (fun x : H => a * x) :=
        (continuous_const.mul continuous_id).measurable
      change (Measure.map (fun x => a * x) (ν.comap (H.toSubgroup.subtype : H →* G))) S =
        (ν.comap (H.toSubgroup.subtype : H →* G)) S
      rw [Measure.map_apply hm hS, he.comap_apply, he.comap_apply]
      have hset : (Subtype.val : H → G) '' (a * ·) ⁻¹' S =
          ((a : G) * ·) ⁻¹' (Subtype.val '' S) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨a * y, hy, rfl⟩
        · rintro ⟨y, hy, heq⟩
          refine ⟨a⁻¹ * y, by simpa, ?_⟩
          change (a : G)⁻¹ * (y : G) = x
          rw [heq, inv_mul_cancel_left]
      change ν ((Subtype.val : H → G) '' (a * ·) ⁻¹' S) = ν (Subtype.val '' S)
      rw [hset]
      exact (show ν (((a : G) * ·) ⁻¹' (Subtype.val '' S)) =
        ν (Subtype.val '' S) by
        have hmG : Measurable (fun x : G => (a : G) * x) :=
          (continuous_const.mul continuous_id).measurable
        have hsG : MeasurableSet ((Subtype.val : H → G) '' S) := he.measurableSet_image.mpr hS
        rw [← Measure.map_apply hmG hsG, Measure.IsMulLeftInvariant.map_mul_left_eq_self])
    lt_top_of_isCompact := (IsFiniteMeasureOnCompacts.comap' ν hEmb.continuous he).lt_top_of_isCompact
    open_pos := (Measure.IsOpenPosMeasure.comap ν hEmb).open_pos }
  let A := (twistedCircleAction ω ρ).comp H.toSubgroup.subtype
  have hA : Continuous (fun z : H × E => A z.1 z.2) := by
    have hPart : Continuous (fun z : H × E => ρ z.1.val z.2) :=
      hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hc : Continuous (fun z : H × E => (((ω z.1.val)⁻¹ : Circle) : ℂ)) :=
      continuous_subtype_val.comp (hω.comp (continuous_subtype_val.comp continuous_fst)).inv
    exact hc.smul hPart
  obtain ⟨Φ, hPettis, hRange, hClosed, hIdem, _, hKer⟩ := compactGroupAverage A hA μ
  have hMass : μ.real univ = ν.real H := by
    change ((ν.comap (H.toSubgroup.subtype : H →* G)) univ).toReal = (ν H).toReal
    rw [he.comap_apply, image_univ]
    change (ν (range (Subtype.val : H → G))).toReal = (ν H).toReal
    rw [Subtype.range_val]
  have hFixed : (fixedSubmodule A : Set E) = {u | ∀ g ∈ H, ρ g u = (ω g : ℂ) • u} := by
    ext u
    change (∀ g : H, (((ω g.val)⁻¹ : Circle) : ℂ) • ρ g.val u = u) ↔ _
    constructor
    · intro hu g hg
      have h := congrArg ((ω g : ℂ) • ·) (hu ⟨g, hg⟩)
      rwa [smul_smul, Circle.coe_inv, mul_inv_cancel₀ (ω g).coe_ne_zero, one_smul] at h
    · intro hu g
      rw [hu g.val g.property, smul_smul, Circle.coe_inv,
        inv_mul_cancel₀ (ω g.val).coe_ne_zero, one_smul]
  refine ⟨Φ, ?_, hRange.trans hFixed, hFixed ▸ hClosed, ?_, ?_⟩
  · intro u l
    have h := hPettis u l
    constructor
    · rw [IntegrableOn, ← map_comap_subtype_coe H.isOpen.measurableSet,
        (MeasurableEmbedding.subtype_coe H.isOpen.measurableSet).integrable_map_iff]
      exact h.1
    · rw [← integral_subtype_comap H.isOpen.measurableSet]
      exact h.2
  · simpa only [hMass] using hIdem
  · change closure ((toWeakSpace ℂ E) '' (Φ.ker : Set E)) =
      closure ((toWeakSpace ℂ E) '' (actionDifferenceSpan A : Set E))
    have hK : Convex ℝ (Φ.ker : Set E) := (Φ.ker.restrictScalars ℝ).convex
    have hD : Convex ℝ (actionDifferenceSpan A : Set E) :=
      ((actionDifferenceSpan A).restrictScalars ℝ).convex
    rw [← hK.toWeakSpace_closure ℂ, ← hD.toWeakSpace_closure ℂ, Φ.isClosed_ker.closure_eq]
    exact congrArg (fun M : Submodule ℂ E => (toWeakSpace ℂ E) '' (M : Set E)) hKer

end OpenSubgroup

section Obstruction

abbrev TwoElementGroup := Multiplicative (ZMod 2)

local instance : TopologicalSpace TwoElementGroup := ⊥
local instance : DiscreteTopology TwoElementGroup := ⟨rfl⟩
local instance : MeasurableSpace TwoElementGroup := ⊤
local instance : BorelSpace TwoElementGroup := ⟨borel_eq_top_of_discrete.symm⟩

private def flip : TwoElementGroup := Multiplicative.ofAdd (1 : ZMod 2)

private def signAction : TwoElementGroup →* (ℂ →L[ℂ] ℂ) where
  toFun g := if g = 1 then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    by_cases hg : g = 1
    · simp [hg]
    by_cases hh : h = 1
    · simp [hh]
    have hgh : g * h = 1 := by
      change ZMod 2 at g h
      fin_cases g <;> fin_cases h
      · exact (hg rfl).elim
      · exact (hg rfl).elim
      · exact (hh rfl).elim
      · rfl
    simp only [hg, hh, hgh, ite_true, ite_false]
    apply ContinuousLinearMap.ext
    intro u
    change u = -(-u)
    simp

/-- Averaging the sign action on the nonidentity singleton gives minus the
identity. This compact open subset has nonempty interior and the average
is invertible, although its fixed space is zero. -/
theorem relativelyCompactSubset_average_counterexample :
    ∃ (G : Type) (_ : CommGroup G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (_ : T2Space G) (_ : LocallyCompactSpace G)
      (_ : MeasurableSpace G) (_ : BorelSpace G)
      (ν : Measure G) (_ : ν.IsHaarMeasure) (X : Set G) (ρ : G →* (ℂ →L[ℂ] ℂ)),
      IsCompact X ∧ IsOpen X ∧ (interior X).Nonempty ∧
      Continuous (fun z : G × ℂ => ρ z.1 z.2) ∧ ν X = 1 ∧
      (∀ u, (∫ g in X, ρ g u ∂ν) = -u) ∧
      {u : ℂ | ∀ g ∈ X, ρ g u = u} = {0} ∧
      (∫ g in X, ρ g (∫ h in X, ρ h (1 : ℂ) ∂ν) ∂ν) ≠
        ∫ g in X, ρ g (1 : ℂ) ∂ν := by
  let X : Set TwoElementGroup := {flip}
  let ν : Measure TwoElementGroup := Measure.count
  have hX : IsOpen X := isOpen_discrete X
  have hInt : (interior X).Nonempty := by simpa only [hX.interior_eq] using singleton_nonempty flip
  have hMass : ν X = 1 := Measure.count_singleton _
  have hHaar : ν.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior ν X isCompact_singleton
      hInt (by simp [hMass]) (by simp [hMass])
  have hflip : flip ≠ (1 : TwoElementGroup) := by decide
  have hEval (u : ℂ) : signAction flip u = -u := by simp [signAction, hflip]
  have hI (u : ℂ) : (∫ g in X, signAction g u ∂ν) = -u := by
    rw [Measure.restrict_singleton, show ν {flip} = 1 from hMass, one_smul,
      integral_dirac, hEval]
  refine ⟨TwoElementGroup, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ν, hHaar, X, signAction, isCompact_singleton,
    hX, hInt, ?_, hMass, hI, ?_, ?_⟩
  · apply continuous_prod_of_discrete_left.mpr
    exact fun g => (signAction g).continuous
  · ext u
    change (∀ g ∈ X, signAction g u = u) ↔ u = 0
    simp only [X, mem_singleton_iff, forall_eq, hEval]
    constructor
    · intro h
      linear_combination -(1 / 2 : ℂ) * h
    · rintro rfl
      simp
  · rw [hI, hI, neg_neg]
    norm_num

end Obstruction

end

end Masullo
