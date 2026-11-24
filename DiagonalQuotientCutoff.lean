import FilteredQuotientIndentation
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function MeasureTheory Set Topology
open scoped NNReal ENNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
variable (u : C(G, ℝ))

private abbrev q := (QuotientGroup.mk : G → G ⧸ H)

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [DiscreteTopology H] in
private theorem coset_q (x : G) (h : H) : q H ((h : G)⁻¹ * x) = q H x := by
  unfold q
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    (QuotientGroup.eq_one_iff _).mpr h.property, inv_one, one_mul]

include hH in
omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem finite_cutoff_translates
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    {K : Set G} (hK : IsCompact K) :
    ∃ F : Finset H, ∀ x ∈ K, ∀ h ∉ F, u ((h : G)⁻¹ * x) = 0 := by
  classical
  let P := tsupport u ∩ q H ⁻¹' (q H '' K)
  have hq : Continuous (q H) := QuotientGroup.continuous_mk
  have hP : IsCompact P := hp _ (hK.image hq)
  let C : Set H := Subtype.val ⁻¹' (K * P⁻¹)
  have hc : IsCompact C := hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.mul hP.inv)
  refine ⟨hc.finite_of_discrete.toFinset, fun x hx h hh => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hh
  have hs : (h : G)⁻¹ * x ∈ P :=
    ⟨hmem, by rw [mem_preimage, coset_q H]; exact mem_image_of_mem _ hx⟩
  have hmul : x * ((h : G)⁻¹ * x)⁻¹ = (h : G) := by
    simp [mul_inv_rev, ← mul_assoc]
  have hC : h ∈ C :=
    ⟨x, hx, ((h : G)⁻¹ * x)⁻¹, Set.inv_mem_inv.mpr hs, hmul⟩
  exact hc.finite_of_discrete.mem_toFinset.mpr hC

omit [T2Space G] [LocallyCompactSpace G] in
private theorem integrable_count_of_finset_support {f : H → ℝ} (hc : Continuous f)
    (F : Finset H) (hf : ∀ h ∉ F, f h = 0) : Integrable f Measure.count := by
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  exact hc.integrable_of_hasCompactSupport
    (exists_compact_iff_hasCompactSupport.mp ⟨F, F.finite_toSet.isCompact, hf⟩)

include hH in
/-- Proposition 12.2.2.2(1). Proper fibre support makes the diagonal average
locally a finite sum of continuous functions. -/
theorem diagonalIndentation_continuous
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hpos : ∀ x, 0 ≤ u x) :
    (∀ x y : G, Integrable (fun h : H => u ((h : G)⁻¹ * x) * u ((h : G)⁻¹ * y)) Measure.count) ∧
      Continuous (fun p : G × G => diagonalIndentation H u p.1 p.2) ∧
      (∀ x y : G, 0 ≤ diagonalIndentation H u x y) ∧
      ∀ (h : H) (x y : G), diagonalIndentation H u ((h : G) * x) ((h : G) * y) =
        diagonalIndentation H u x y := by
  have hI (x y : G) :
      Integrable (fun h : H => u ((h : G)⁻¹ * x) * u ((h : G)⁻¹ * y)) Measure.count := by
    obtain ⟨F, hF⟩ := finite_cutoff_translates H hH u hp (K := {x}) isCompact_singleton
    apply integrable_count_of_finset_support H (by fun_prop) F
    intro h hh
    rw [hF x (mem_singleton x) h hh, zero_mul]
  refine ⟨hI, ?_, fun x y => integral_nonneg (fun h => mul_nonneg (hpos _) (hpos _)), ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds p.1
    obtain ⟨F, hF⟩ := finite_cutoff_translates H hH u hp hK
    let f (z : G × G) := ∑ h ∈ F, u ((h : G)⁻¹ * z.1) * u ((h : G)⁻¹ * z.2)
    have hf : Continuous f := continuous_finsetSum _ (fun _ _ => by fun_prop)
    have he (z : G × G) (hz : z.1 ∈ K) : diagonalIndentation H u z.1 z.2 = f z := by
      unfold diagonalIndentation
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (F : Set H)) (fun h hh => by
        rw [hF z.1 hz h hh, zero_mul])]
      rw [setIntegral_finset F (hI z.1 z.2).integrableOn]
      simp [f, Measure.real]
    have hNear : ∀ᶠ z : G × G in 𝓝 p, z.1 ∈ K := continuous_fst.continuousAt hKn
    have hev : (fun z : G × G => diagonalIndentation H u z.1 z.2) =ᶠ[𝓝 p] f :=
      hNear.mono fun z hz => he z hz
    exact hf.continuousAt.congr_of_eventuallyEq hev
  · intro h x y
    unfold diagonalIndentation
    rw [← integral_mul_left_eq_self (μ := (Measure.count : Measure H))
      (fun a : H => u ((a : G)⁻¹ * ((h : G) * x)) * u ((a : G)⁻¹ * ((h : G) * y))) h]
    simp [Subgroup.coe_mul, mul_inv_rev, mul_assoc]


include hH in
omit [T2Space G] [LocallyCompactSpace G] in
/-- A second coset integration removes the diagonal indentation. Each product
test in the double integral has finite support on the discrete subgroup. -/
theorem diagonalIndentation_integral [SecondCountableTopology G]
    (hp : ∀ L : Set (G ⧸ H), IsCompact L → IsCompact (tsupport u ∩ q H ⁻¹' L))
    (hn : ∀ x : G, (∫ h : H, u ((h : G)⁻¹ * x) ∂Measure.count) = 1)
    (x y : G) :
    Integrable (fun h : H => diagonalIndentation H u x ((h : G)⁻¹ * y)) Measure.count ∧
      (∫ h : H, diagonalIndentation H u x ((h : G)⁻¹ * y) ∂Measure.count) = 1 := by
  classical
  letI : (Measure.count : Measure H).IsHaarMeasure := subgroup_count_isHaarMeasure H
  letI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  letI : Countable H := countable_of_Lindelof_of_discrete
  obtain ⟨F, hF⟩ := finite_cutoff_translates H hH u hp (K := {x}) isCompact_singleton
  obtain ⟨E, hE⟩ := finite_cutoff_translates H hH u hp (K := {y}) isCompact_singleton
  let g (a h : H) := u ((a : G)⁻¹ * x) * u ((a : G)⁻¹ * ((h : G)⁻¹ * y))
  let B : Set (H × H) := (F : Set H) ×ˢ (↑(E * F⁻¹) : Set H)
  have hB : IsCompact B := F.finite_toSet.isCompact.prod (E * F⁻¹).finite_toSet.isCompact
  have hg₀ (p : H × H) (hpB : p ∉ B) : g p.1 p.2 = 0 := by
    by_cases ha : p.1 ∈ F
    · have hha : p.2 * p.1 ∉ E := by
        intro hin
        apply hpB
        refine ⟨ha, ?_⟩
        change p.2 ∈ (E * F⁻¹ : Finset H)
        simpa using (Finset.mul_mem_mul hin (Finset.inv_mem_inv ha) :
          p.2 * p.1 * p.1⁻¹ ∈ E * F⁻¹)
      unfold g
      have he : (p.1 : G)⁻¹ * ((p.2 : G)⁻¹ * y) = ((p.2 * p.1 : H) : G)⁻¹ * y := by
        rw [Subgroup.coe_mul, mul_inv_rev, mul_assoc]
      rw [he, hE y (mem_singleton y) _ hha, mul_zero]
    · unfold g
      rw [hF x (mem_singleton x) _ ha, zero_mul]
  have hgc : Continuous (fun p : H × H => g p.1 p.2) := by
    dsimp only [g]
    fun_prop
  have hG : Integrable (uncurry g)
      ((Measure.count : Measure H).prod Measure.count) :=
    hgc.integrable_of_hasCompactSupport (exists_compact_iff_hasCompactSupport.mp ⟨B, hB, hg₀⟩)
  refine ⟨hG.swap.integral_prod_left, ?_⟩
  change (∫ h, ∫ a, g a h ∂Measure.count ∂Measure.count) = 1
  rw [← integral_integral_swap hG]
  have hi (a : H) : (∫ h, g a h ∂Measure.count) = u ((a : G)⁻¹ * x) := by
    unfold g
    rw [integral_const_mul]
    have he (h : H) : u ((a : G)⁻¹ * ((h : G)⁻¹ * y)) =
        (fun b : H => u ((b : G)⁻¹ * y)) (h * a) := by
      simp [Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    simp_rw [he]
    have hs := integral_mul_right_eq_self (μ := (Measure.count : Measure H))
      (fun b : H => u ((b : G)⁻¹ * y)) a
    rw [hs, hn, mul_one]
  simpa only [hi] using hn x

end
end Masullo
