import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Topology.Algebra.IsOpenUnits

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Masullo

noncomputable section

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [LocallyCompactSpace Aˣ] [SecondCountableTopology Aˣ]

/-- An additive measure that gives full measure to the units and scales
by a positive modulus is, up to a positive scalar, the multiplicative
Haar measure weighted by that modulus. -/
theorem additiveMeasure_eq_weighted_unitHaar
    (η : Measure A) [IsFiniteMeasureOnCompacts η] (hη : η ≠ 0)
    (μ : Measure Aˣ) [μ.IsHaarMeasure]
    (hj : IsOpenEmbedding (Units.val : Aˣ → A))
    (hfull : ∀ᵐ x ∂η, x ∈ range (Units.val : Aˣ → A))
    (d : Aˣ →* ℝ) (hd : Continuous d) (hpos : ∀ u, 0 < d u)
    (hscale : ∀ u : Aˣ, η.map (fun x ↦ u.val * x) = (ENNReal.ofReal (d u))⁻¹ • η) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      (μ.withDensity (fun u ↦ ENNReal.ofReal (d u))).map (Units.val : Aˣ → A) =
        c • η := by
  let j : Aˣ → A := Units.val
  have hJ : MeasurableEmbedding j := hj.measurableEmbedding
  let ρ : Measure Aˣ := η.comap j
  have hρ : ρ.map j = η := (hJ.map_comap η).trans (Measure.restrict_eq_self_of_ae_mem hfull)
  let w (u : Aˣ) : ℝ≥0∞ := ENNReal.ofReal (d u)
  let W (u : Aˣ) : ℝ≥0∞ := ENNReal.ofReal ((d u)⁻¹)
  have hw0 (u : Aˣ) : w u ≠ 0 := (ENNReal.ofReal_pos.mpr (hpos u)).ne'
  have hwt (u : Aˣ) : w u ≠ ∞ := ENNReal.ofReal_ne_top
  have hW (u : Aˣ) : W u = (w u)⁻¹ := ENNReal.ofReal_inv_of_pos (hpos u)
  have hwmeas : Measurable w := hd.measurable.ennreal_ofReal
  have hWcont : Continuous W :=
    ENNReal.continuous_ofReal.comp (hd.inv₀ (fun u ↦ (hpos u).ne'))
  have hWmeas : Measurable W := hWcont.measurable
  let unitMeasure : Measure Aˣ := ρ.withDensity W
  have hFin : IsFiniteMeasureOnCompacts unitMeasure := by
    constructor
    intro C hC
    by_cases he : C.Nonempty
    · obtain ⟨u, _, hu⟩ := hC.exists_isMaxOn he hWcont.continuousOn
      have hmax : ∀ x ∈ C, W x ≤ W u := fun x hx ↦ hu hx
      rw [show unitMeasure C = ∫⁻ x in C, W x ∂ρ from withDensity_apply _ hC.isClosed.measurableSet]
      calc
        _ ≤ ∫⁻ _ in C, W u ∂ρ :=
          lintegral_mono_ae (ae_restrict_of_forall_mem hC.isClosed.measurableSet hmax)
        _ = W u * ρ C := setLIntegral_const C (W u)
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
          rw [hJ.comap_apply]
          exact (hC.image hj.continuous).measure_lt_top)
    · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
      exact ENNReal.zero_lt_top
  have hInv : unitMeasure.IsMulLeftInvariant := by
    constructor
    intro u
    let e := (Homeomorph.mulLeft u).toMeasurableEquiv
    have hBase : ρ.map e = (w u)⁻¹ • ρ := by
      have hmap : (ρ.map e).map j = ((w u)⁻¹ • ρ).map j := by
        rw [Measure.map_map hJ.measurable e.measurable, Measure.map_smul, hρ, ← hscale]
        have hcomp : j ∘ e = (fun x : A ↦ u.val * x) ∘ j := rfl
        have hm : Measurable (fun x : A ↦ u.val * x) :=
          (continuous_const.mul continuous_id).measurable
        rw [hcomp, ← Measure.map_map hm hJ.measurable, hρ]
      exact (hJ.comap_map (ρ.map e)).symm.trans
        ((congrArg (Measure.comap j) hmap).trans (hJ.comap_map _))
    have hweight (x : Aˣ) : W (e.symm x) = w u * W x := by
      have he : w (e.symm x) = (w u)⁻¹ * w x := by
        change ENNReal.ofReal (d (u⁻¹ * x)) = _
        rw [map_mul, map_inv, ENNReal.ofReal_mul (inv_nonneg.mpr (hpos u).le),
          ENNReal.ofReal_inv_of_pos (hpos u)]
      rw [hW, he, ENNReal.mul_inv, inv_inv, ← hW]
      · exact Or.inr (hwt x)
      · exact Or.inr (hw0 x)
    change unitMeasure.map e = unitMeasure
    ext C hC
    have hpre : MeasurableSet (e ⁻¹' C) := e.measurable hC
    rw [Measure.map_apply e.measurable hC]
    change (ρ.withDensity W) (e ⁻¹' C) = (ρ.withDensity W) C
    rw [withDensity_apply _ hpre, withDensity_apply _ hC]
    calc
      _ = ∫⁻ y in C, W (e.symm y) ∂(ρ.map e) := by
        have ht := setLIntegral_map (μ := ρ) (f := fun y ↦ W (e.symm y))
          hC (hWmeas.comp e.symm.measurable) e.measurable
        simpa only [MeasurableEquiv.symm_apply_apply] using ht.symm
      _ = ∫⁻ y in C, w u * W y ∂((w u)⁻¹ • ρ) := by
        rw [hBase]
        exact lintegral_congr hweight
      _ = _ := by
        rw [setLIntegral_smul_measure, lintegral_const_mul _ hWmeas, smul_eq_mul,
          ENNReal.inv_mul_cancel_left (hw0 u) (hwt u)]
  let c := Measure.haarScalarFactor unitMeasure μ
  have he : unitMeasure = c • μ := Measure.isMulLeftInvariant_eq_smul unitMeasure μ
  have hBack : unitMeasure.withDensity w = ρ := by
    have hi : (fun x ↦ (W x)⁻¹) = w := funext fun x ↦ by rw [hW, inv_inv]
    rw [← hi]
    exact withDensity_inv_same₀ hWmeas.aemeasurable (.of_forall fun x ↦ by rw [hW]; exact ENNReal.inv_ne_zero.mpr (hwt x))
      (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)
  have hmap : η = c • (μ.withDensity w).map j := by
    rw [← hρ, ← hBack, he]
    change Measure.map j (((c : ℝ≥0∞) • μ).withDensity w) =
      (c : ℝ≥0∞) • Measure.map j (μ.withDensity w)
    rw [withDensity_smul_measure, Measure.map_smul]
  have hcn : c ≠ 0 := fun hc ↦ hη (by simpa [hc] using hmap)
  refine ⟨c⁻¹, inv_ne_zero hcn, ?_⟩
  change (μ.withDensity w).map j = c⁻¹ • η
  rw [hmap, smul_smul, inv_mul_cancel₀ hcn, one_smul]

end

end Masullo
