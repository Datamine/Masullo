import QuotientLiftedMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

open Filter Function MeasureTheory Set Topology ProbabilityTheory
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable (μ : Measure H) [μ.IsHaarMeasure] [μ.Regular]

local instance : MeasurableSpace (G ⧸ H) := borel _
local instance : BorelSpace (G ⧸ H) := ⟨rfl⟩

variable (ν : Measure (G ⧸ H))

local notation "ρ" => quotientLiftedMeasure H μ ν
local notation "fiber" => quotientCosetMeasure H μ

private def cosetKernel : Kernel (G ⧸ H) G :=
  ⟨fiber, quotientCosetMeasure_measurable H hH μ⟩

include hH in
private theorem integral_coset_average {f : G → ℂ}
    (hf : Integrable f ρ) : Integrable (fun q => ∫ x, f x ∂fiber q) ν := by
  let k := cosetKernel H hH μ
  have hi : Integrable f ((k.comp (Kernel.const Unit ν)) ()) := by
    rw [← Measure.comp_eq_comp_const_apply]
    exact hf
  simpa only [Kernel.const_apply, k, cosetKernel, Kernel.coe_mk] using hi.integral_comp

/-- Coset integration descends to a contraction on the (L^1) spaces of the
lifted and quotient measures. -/
def quotientL1Average : (G →₁[ρ] ℂ) →L[ℂ] ((G ⧸ H) →₁[ν] ℂ) := by
  let k := cosetKernel H hH μ
  let a (f : G →₁[ρ] ℂ) (q : G ⧸ H) := ∫ x, f x ∂fiber q
  have ha (f : G →₁[ρ] ℂ) : Integrable (a f) ν :=
    integral_coset_average H hH μ ν (L1.integrable_coeFn f)
  have hf (f : G →₁[ρ] ℂ) : ∀ᵐ q ∂ν, Integrable f (fiber q) :=
    ((Measure.integrable_comp_iff (κ := k) (μ := ν)
      (L1.integrable_coeFn f).aestronglyMeasurable).mp (L1.integrable_coeFn f)).1
  let A : (G →₁[ρ] ℂ) →ₗ[ℂ] ((G ⧸ H) →₁[ν] ℂ) :=
    { toFun := fun f => (ha f).toL1 (a f)
      map_add' := by
        intro f g
        rw [← Integrable.toL1_add]
        apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
        have he := Measure.ae_ae_of_ae_comp (κ := k) (Lp.coeFn_add f g)
        filter_upwards [hf f, hf g, he] with q hfq hgq heq
        exact (integral_congr_ae heq).trans (integral_add hfq hgq)
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← Integrable.toL1_smul]
        apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
        have he := Measure.ae_ae_of_ae_comp (κ := k) (Lp.coeFn_smul c f)
        filter_upwards [he] with q heq
        exact (integral_congr_ae heq).trans (integral_smul c _) }
  exact A.mkContinuous 1 (fun f => by
    change ‖(ha f).toL1 (a f)‖ ≤ 1 * ‖f‖
    rw [one_mul, Integrable.norm_toL1_eq_lintegral_enorm, L1.norm_def]
    have hmeas : Measurable (fun x => ‖f x‖ₑ) := (Lp.stronglyMeasurable f).enorm
    have hbound : (∫⁻ q, ‖a f q‖ₑ ∂ν) ≤ ∫⁻ x, ‖f x‖ₑ ∂ρ := by
      calc
        _ ≤ ∫⁻ q, ∫⁻ x, ‖f x‖ₑ ∂fiber q ∂ν :=
          lintegral_mono fun q => enorm_integral_le_lintegral_enorm _
        _ = _ := (Measure.lintegral_bind k.aemeasurable hmeas.aemeasurable).symm
    exact ENNReal.toReal_mono
      ((hasFiniteIntegral_iff_enorm.mp (L1.integrable_coeFn f).hasFiniteIntegral).ne) hbound)

theorem quotientL1Average_coe (f : G →₁[ρ] ℂ) :
    quotientL1Average H hH μ ν f =ᵐ[ν] fun q => ∫ x, f x ∂fiber q :=
  (integral_coset_average H hH μ ν (L1.integrable_coeFn f)).coeFn_toL1


private abbrev qmap := (QuotientGroup.mk : G → G ⧸ H)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem qmapMeasurable : Measurable (qmap H) :=
  QuotientGroup.continuous_mk.measurable

include hH in
omit [T2Space G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular] in
private theorem quotientCosetMeasure_ae_qmap (q : G ⧸ H) :
    ∀ᵐ x ∂fiber q, qmap H x = q := by
  letI : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
  have ht : Measurable (fun h : H => q.out * (h : G)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  change ∀ᵐ x ∂μ.map (fun h : H => q.out * (h : G)), qmap H x = q
  apply (ae_map_iff ht.aemeasurable ((qmapMeasurable H) (measurableSet_singleton q))).mpr
  exact .of_forall fun h => by
    change QuotientGroup.mk (q.out * (h : G)) = q
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr h.property, mul_one]
    exact Quotient.out_eq' q

include hH in
private theorem ae_qmap_pullback {s : Set (G ⧸ H)} (hs : MeasurableSet s)
    (h : ∀ᵐ q ∂ν, q ∈ s) : ∀ᵐ x ∂ρ, qmap H x ∈ s := by
  apply Measure.ae_comp_of_ae_ae (κ := cosetKernel H hH μ) ((qmapMeasurable H) hs)
  filter_upwards [h] with q hq
  filter_upwards [quotientCosetMeasure_ae_qmap H hH μ q] with x hx
  exact hx.symm ▸ hq

include hH in
/-- Null sets for the quotient measure pull back to null sets for the lift. -/
theorem quotientLiftedMeasure_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (qmap H) ρ ν := by
  have hq := qmapMeasurable H
  refine ⟨hq, Measure.AbsolutelyContinuous.mk fun s hs hnull => ?_⟩
  have ha : ∀ᵐ c ∂ν, c ∈ sᶜ := ae_iff.mpr (by simpa using hnull)
  have hb := ae_qmap_pullback H hH μ ν hs.compl ha
  have hc := (ae_map_iff hq.aemeasurable hs.compl).mpr hb
  simpa using ae_iff.mp hc

include hH in
omit [T2Space G] [SecondCountableTopology G] in
/-- A continuous quotient indentation has mass one for each translated fibre
measure, with the inverse-translation convention of Lemma 12.2.1.1. -/
theorem quotientIndentation_fiber_mass (u : C(G, ℝ))
    (hu : ∀ x : G, Integrable (fun h : H => u ((h : G)⁻¹ * x)) μ ∧
      (∫ h : H, u ((h : G)⁻¹ * x) ∂μ) = 1) (q : G ⧸ H) :
    Integrable u (fiber q) ∧ (∫ x, u x ∂fiber q) = 1 := by
  letI : LocallyCompactSpace H := hH.locallyCompactSpace
  have ht : Measurable (fun h : H => q.out * (h : G)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  have he (h : H) : u ((h : G)⁻¹ * q.out) =
      (fun k : H => u (q.out * (k : G))) h⁻¹ := by rw [mul_comm]; rfl
  have hi (x : G) := hu x
  have hi' := (hi q.out).1
  simp_rw [he] at hi'
  have hi'' : Integrable (fun h : H => u (q.out * (h : G))) μ := by
    simpa only [Function.comp_def, inv_inv] using (Measure.measurePreserving_inv μ).integrable_comp_of_integrable hi'
  change Integrable u (μ.map (fun h : H => q.out * (h : G))) ∧
    (∫ x, u x ∂μ.map (fun h : H => q.out * (h : G))) = 1
  refine ⟨(integrable_map_measure u.continuous.aestronglyMeasurable ht.aemeasurable).mpr hi'', ?_⟩
  rw [integral_map ht.aemeasurable u.continuous.aestronglyMeasurable,
    ← integral_inv_eq_self (fun h : H => u (q.out * (h : G))) μ]
  simpa only [he] using (hu q.out).2

section SectionMap

variable (u : C(G, ℝ)) (hu₀ : ∀ x, 0 ≤ u x)
  (hu : ∀ q : G ⧸ H, Integrable u (quotientCosetMeasure H μ q) ∧
    (∫ x, u x ∂quotientCosetMeasure H μ q) = 1)

private def sectionFun (w : G ⧸ H → ℂ) (x : G) : ℂ :=
  (u x : ℂ) * w (qmap H x)

include hH hu₀ hu in
private theorem sectionFun_norm (w : G ⧸ H → ℂ) (hw : Measurable w) :
    (∫⁻ x, ‖sectionFun H u w x‖ₑ ∂ρ) = ∫⁻ q, ‖w q‖ₑ ∂ν := by
  have hmeas : Measurable (sectionFun H u w) :=
    (Complex.continuous_ofReal.comp u.continuous).measurable.mul (hw.comp (qmapMeasurable H))
  rw [quotientLiftedMeasure, Measure.lintegral_bind
    (quotientCosetMeasure_measurable H hH μ).aemeasurable hmeas.enorm.aemeasurable]
  apply lintegral_congr
  intro q
  have hpoint (x : G) (hx : qmap H x = q) :
      ‖sectionFun H u w x‖ₑ = ENNReal.ofReal (u x) * ‖w q‖ₑ := by
    rw [sectionFun, hx, enorm_mul]
    congr 1
    rw [enorm_eq_nnnorm, Complex.nnnorm_real, Real.nnnorm_of_nonneg (hu₀ x),
      ENNReal.ofReal_eq_coe_nnreal (hu₀ x)]
  calc
    (∫⁻ x, ‖sectionFun H u w x‖ₑ ∂fiber q) =
        ∫⁻ x, ENNReal.ofReal (u x) * ‖w q‖ₑ ∂fiber q := by
      apply lintegral_congr_ae
      filter_upwards [quotientCosetMeasure_ae_qmap H hH μ q] with x hx using hpoint x hx
    _ = ‖w q‖ₑ := by
      have hm : Measurable (fun x => ENNReal.ofReal (u x)) :=
        (ENNReal.continuous_ofReal.comp u.continuous).measurable
      rw [lintegral_mul_const _ hm,
        ← ofReal_integral_eq_lintegral_ofReal (hu q).1 (.of_forall hu₀),
        (hu q).2, ENNReal.ofReal_one, one_mul]

include hH hu₀ hu in
private theorem sectionFun_integrable (w : (G ⧸ H) →₁[ν] ℂ) :
    Integrable (sectionFun H u w) ρ := by
  have hw := Lp.stronglyMeasurable w
  refine ⟨((Complex.continuous_ofReal.comp u.continuous).stronglyMeasurable.mul
    (hw.measurable.comp (qmapMeasurable H)).stronglyMeasurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, sectionFun_norm H hH μ ν u hu₀ hu _ hw.measurable]
  exact hasFiniteIntegral_iff_enorm.mp (L1.integrable_coeFn w).hasFiniteIntegral

/-- Multiply the pullback of an (L^1) class by a normalized nonnegative
coset cutoff. This is a complex-linear isometry. -/
def quotientL1Section : ((G ⧸ H) →₁[ν] ℂ) →ₗᵢ[ℂ] (G →₁[ρ] ℂ) := by
  let i (w : (G ⧸ H) →₁[ν] ℂ) := sectionFun_integrable H hH μ ν u hu₀ hu w
  refine { toFun := fun w => (i w).toL1 (sectionFun H u w)
           map_add' := ?_
           map_smul' := ?_
           norm_map' := ?_ }
  · intro v w
    rw [← Integrable.toL1_add]
    apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
    have hm : MeasurableSet {q | (v + w) q = v q + w q} :=
      measurableSet_eq_fun (Lp.stronglyMeasurable (v + w)).measurable
        ((Lp.stronglyMeasurable v).measurable.add (Lp.stronglyMeasurable w).measurable)
    filter_upwards [ae_qmap_pullback H hH μ ν hm (Lp.coeFn_add v w)] with x hx
    change (v + w) (qmap H x) = v (qmap H x) + w (qmap H x) at hx
    simp only [sectionFun, Pi.add_apply, hx, mul_add]
  · intro c w
    rw [RingHom.id_apply, ← Integrable.toL1_smul]
    apply (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr
    have hm : MeasurableSet {q | (c • w) q = c • w q} :=
      measurableSet_eq_fun (Lp.stronglyMeasurable (c • w)).measurable
        ((Lp.stronglyMeasurable w).measurable.const_smul c)
    filter_upwards [ae_qmap_pullback H hH μ ν hm (Lp.coeFn_smul c w)] with x hx
    change (c • w) (qmap H x) = c • w (qmap H x) at hx
    simp only [sectionFun, hx, smul_eq_mul, mul_left_comm]
  · intro w
    change ‖(i w).toL1 (sectionFun H u w)‖ = ‖w‖
    rw [Integrable.norm_toL1_eq_lintegral_enorm, L1.norm_def,
      sectionFun_norm H hH μ ν u hu₀ hu _ (Lp.stronglyMeasurable w).measurable]

theorem quotientL1Section_coe (w : (G ⧸ H) →₁[ν] ℂ) :
    quotientL1Section H hH μ ν u hu₀ hu w =ᵐ[ρ] sectionFun H u w :=
  (sectionFun_integrable H hH μ ν u hu₀ hu w).coeFn_toL1

/-- The weighted pullback is a right inverse to the (L^1) coset average. -/
theorem quotientL1Average_section (w : (G ⧸ H) →₁[ν] ℂ) :
    quotientL1Average H hH μ ν (quotientL1Section H hH μ ν u hu₀ hu w) = w := by
  apply Lp.ext
  have he := Measure.ae_ae_of_ae_comp (κ := cosetKernel H hH μ)
    (quotientL1Section_coe H hH μ ν u hu₀ hu w)
  filter_upwards [quotientL1Average_coe H hH μ ν
    (quotientL1Section H hH μ ν u hu₀ hu w), he] with q ha hq
  rw [ha]
  have heq : (fun x => quotientL1Section H hH μ ν u hu₀ hu w x) =ᵐ[fiber q]
      sectionFun H u w := hq
  rw [integral_congr_ae heq]
  calc
    (∫ x, sectionFun H u w x ∂fiber q) =
        ∫ x, (u x : ℂ) * w q ∂fiber q := by
      apply integral_congr_ae
      filter_upwards [quotientCosetMeasure_ae_qmap H hH μ q] with x hx
      simp only [sectionFun, hx]
    _ = w q := by
      rw [integral_mul_const, integral_complex_ofReal, (hu q).2, Complex.ofReal_one, one_mul]

end SectionMap


/-- The (L^1) average agrees with the continuous compact-support average on
the canonical image of compactly supported continuous functions. -/
theorem quotientL1Average_on_compact [IsFiniteMeasureOnCompacts ν]
    (g : CompactlySupportedContinuousMap G ℂ) :
    let S := TopologicalGroup.IsSES.ofClosedSubgroup H hH
    let hg := (quotientLiftedMeasure_integral_compact H hH μ ν g).1
    quotientL1Average H hH μ ν (hg.toL1 g) =
      (S.pushforward μ g).integrable.toL1 (S.pushforward μ g) := by
  intro S hg
  apply Lp.ext
  have he := Measure.ae_ae_of_ae_comp (κ := cosetKernel H hH μ) hg.coeFn_toL1
  filter_upwards [quotientL1Average_coe H hH μ ν (hg.toL1 g), he,
    (S.pushforward μ g).integrable.coeFn_toL1] with q hq hfg hp
  rw [hq, hp]
  have heq : (fun x => hg.toL1 g x) =ᵐ[fiber q] g := hfg
  rw [integral_congr_ae heq]
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change (∫ y, g y ∂fiber (QuotientGroup.mk x)) = S.pushforward μ g (QuotientGroup.mk' H x)
  rw [quotientCosetMeasure_mk, S.pushforward_apply_apply]
  have hf : Measurable (fun h : H => x * (h : G)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  exact integral_map hf.aemeasurable g.continuous.aestronglyMeasurable

/-- Corollary 12.2.1.2(2). Every indentation determines the isometric section
with the stated pointwise formula on (L^1) classes. -/
theorem quotientL1_split_of_indentation (u : C(G, ℝ)) (hu₀ : ∀ x, 0 ≤ u x)
    (hu : ∀ x : G, Integrable (fun h : H => u ((h : G)⁻¹ * x)) μ ∧
      (∫ h : H, u ((h : G)⁻¹ * x) ∂μ) = 1) :
    ∃ J : ((G ⧸ H) →₁[ν] ℂ) →ₗᵢ[ℂ] (G →₁[ρ] ℂ),
      Function.RightInverse J (quotientL1Average H hH μ ν) ∧
        ∀ w, J w =ᵐ[ρ] fun x => (u x : ℂ) * w (QuotientGroup.mk x) := by
  let h := quotientIndentation_fiber_mass H hH μ u hu
  exact ⟨quotientL1Section H hH μ ν u hu₀ h, quotientL1Average_section H hH μ ν u hu₀ h,
    quotientL1Section_coe H hH μ ν u hu₀ h⟩

/-- The (L^1) coset average is onto. -/
theorem quotientL1Average_surjective : Surjective (quotientL1Average H hH μ ν) := by
  obtain ⟨u, hu₀, _, hu⟩ := exists_quotientIndentation H hH μ
  obtain ⟨J, hJ, _⟩ := quotientL1_split_of_indentation H hH μ ν u hu₀ hu
  exact hJ.surjective

end
end Masullo
