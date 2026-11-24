import BruhatCompactTestTopology
import CompactGroupAveraging
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.LocallyConvex.StrongTopology

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal ComplexOrder

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

section Estimates

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]

/-- A jointly continuous linear family is uniformly small on a common
zero neighborhood when its parameter ranges over a compact set. -/
private theorem compact_orbits_small (ρ : G → E →ₗ[ℂ] E)
    (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2)
    {K : Set G} (hK : IsCompact K) (p : Seminorm ℂ E) (hp : Continuous p) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 (0 : E), ∀ g ∈ K, ∀ u ∈ V, p (ρ g u) < δ := by
  let N := {z : G × E | p (ρ z.1 z.2) < δ}
  have hN : IsOpen N := isOpen_lt (hp.comp hρ) continuous_const
  have hsub : K ×ˢ ({0} : Set E) ⊆ N := by
    rintro ⟨g, u⟩ ⟨_, rfl : u = 0⟩
    simpa [N] using hδ
  obtain ⟨U, V, _, hV, hKU, h0V, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hN hsub
  exact ⟨V, hV.mem_nhds (h0V rfl), fun g hg u hu ↦ hUV (show (g, u) ∈ U ×ˢ V from ⟨hKU hg, hu⟩)⟩

private theorem compact_orbits_bounded (ρ : G → E →ₗ[ℂ] E)
    (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2)
    {K : Set G} (hK : IsCompact K) {B : Set E} (hB : Bornology.IsVonNBounded ℂ B)
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ K, ∀ u ∈ B, p (ρ g u) ≤ C := by
  obtain ⟨V, hV, hsmall⟩ := compact_orbits_small ρ hρ hK p hp zero_lt_one
  obtain ⟨r, hr, h⟩ := (hB hV).exists_pos
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  refine ⟨r, hr, fun g hg u hu ↦ ?_⟩
  obtain ⟨v, hv, rfl⟩ := h (r : ℂ) hn.ge hu
  rw [map_smul, map_smul_eq_mul, hn]
  exact mul_le_of_le_one_right hr.le (hsmall g hg v hv).le

private theorem pettis_kernel_seminorm_le (ρ : G → E →ₗ[ℂ] E)
    {φ : G → ℂ} {u v : E}
    (hv : HasPositivePettisIntegral μ (fun g ↦ φ g • ρ g u) v)
    {K : Set G} (hK : IsCompact K) (hφ : ∀ g ∉ K, φ g = 0)
    (p : Seminorm ℂ E) (hp : Continuous p) {C M : ℝ}
    (hC : ∀ g ∈ K, p (ρ g u) ≤ C) (hM : ∀ g ∈ K, ‖φ g‖ ≤ M) (hM₀ : 0 ≤ M) :
    p v ≤ (M * C) * μ.real K := by
  obtain ⟨ℓ, hℓ, hbound⟩ := seminorm_support p hp v
  rw [← hℓ, (hv ℓ).2,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) (s := K)
      (fun g hg ↦ by change ℓ (φ g • ρ g u) = 0; rw [hφ g hg, zero_smul, map_zero])]
  apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
  intro g hg
  rw [map_smul, norm_smul]
  exact mul_le_mul (hM g hg) ((hbound _).trans (hC g hg)) (norm_nonneg _) hM₀

private theorem hasPositivePettisIntegral_add {f g : G → E} {u v : E}
    (hf : HasPositivePettisIntegral μ f u) (hg : HasPositivePettisIntegral μ g v) :
    HasPositivePettisIntegral μ (f + g) (u + v) := by
  intro ℓ
  have he : ℓ ∘ (f + g) = (ℓ ∘ f) + (ℓ ∘ g) := by ext x; exact map_add ℓ _ _
  refine ⟨he ▸ (hf ℓ).1.add (hg ℓ).1, ?_⟩
  change ℓ (u + v) = ∫ x, (ℓ ∘ (f + g)) x ∂μ
  rw [he, map_add, (hf ℓ).2, (hg ℓ).2]
  exact (integral_add (hf ℓ).1 (hg ℓ).1).symm

private theorem hasPositivePettisIntegral_smul (c : ℂ) {f : G → E} {u : E}
    (hf : HasPositivePettisIntegral μ f u) :
    HasPositivePettisIntegral μ (c • f) (c • u) := by
  intro ℓ
  have he : ℓ ∘ (c • f) = c • (ℓ ∘ f) := by ext x; exact map_smul ℓ _ _
  refine ⟨he ▸ (hf ℓ).1.smul c, ?_⟩
  change ℓ (c • u) = ∫ x, (ℓ ∘ (c • f)) x ∂μ
  rw [he, map_smul, (hf ℓ).2]
  exact (integral_smul c (ℓ ∘ f)).symm

private theorem exists_continuousPettisKernel [T2Space E] (ρ : G → E →ₗ[ℂ] E)
    (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2) {φ : G → ℂ}
    (hφ : Continuous φ) (hK : HasCompactSupport φ)
    (hInt : ∀ u, ∃ v, HasPositivePettisIntegral μ (fun g ↦ φ g • ρ g u) v) :
    ∃ T : E →L[ℂ] E, ∀ u, HasPositivePettisIntegral μ (fun g ↦ φ g • ρ g u) (T u) := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  choose T hT using hInt
  let L : E →ₗ[ℂ] E :=
    { toFun := T
      map_add' := fun u v ↦ by
        apply positivePettis_integral_unique (hT (u + v))
        simpa only [map_add, smul_add, Pi.add_def] using
          hasPositivePettisIntegral_add μ (hT u) (hT v)
      map_smul' := fun c u ↦ by
        apply positivePettis_integral_unique (hT (c • u))
        have he (g : G) : φ g • ρ g (c • u) = c • (φ g • ρ g u) := by
          rw [map_smul, smul_comm]
        change HasPositivePettisIntegral μ (fun g ↦ φ g • ρ g (c • u)) (c • T u)
        exact (funext he).symm ▸ hasPositivePettisIntegral_smul μ c (hT u) }
  refine ⟨⟨L, ?_⟩, hT⟩
  let W := PolynormableSpace.withSeminorms ℂ E
  apply W.continuous_of_continuous_comp L
  intro p
  apply Seminorm.continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  let M := max 0 B
  have hM : 0 ≤ M := le_max_left _ _
  let D := M * μ.real (tsupport φ)
  have hD : 0 ≤ D := mul_nonneg hM ENNReal.toReal_nonneg
  let δ := ε / (D + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨V, hV, hv⟩ := compact_orbits_small ρ hρ hK p.val p.property hδ
  filter_upwards [hV] with u hu
  have hle := pettis_kernel_seminorm_le μ ρ (hT u) hK
    (fun g hg ↦ image_eq_zero_of_notMem_tsupport hg) p.val p.property
    (fun g hg ↦ (hv g hg u hu).le) (fun g hg ↦ (hB g hg).trans (le_max_right _ _)) hM
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
  change p.val (T u) < ε
  calc
    _ ≤ δ * D := hle.trans_eq (by dsimp [D]; ring)
    _ < δ * (D + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ _ (by positivity)

set_option maxHeartbeats 700000 in
private theorem stage_value_le (p : BruhatSchwartzStage G) (f : p.Space) (g : G) :
    ‖p.realize f g‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f := by
  by_cases hg : g ∈ p.1.upper.val
  · let x : p.1.upper.val := ⟨g, hg⟩
    let y := (p.1.stageCoordinates p.2 x).toAdd
    rw [p.1.realizeSchwartz_apply_of_mem p.2 f x]
    change ‖f y‖ ≤ _
    have h : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ENNReal)) y
    exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne h
  · have hf : p.realize f g = 0 := p.1.realizeSchwartz_apply_of_not_mem p.2 f g hg
    exact (norm_eq_zero.mpr hf).le.trans (apply_nonneg _ _)

set_option maxHeartbeats 2000000 in
private theorem continuous_operators_on_bruhatStage (ρ : G → E →ₗ[ℂ] E)
    (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2)
    (L : BruhatCompactTest G →ₗ[ℂ] (E →L[ℂ] E))
    (hL : ∀ φ u, HasPositivePettisIntegral μ (fun g ↦ φ.val.val g • ρ g u) (L φ u))
    (i : BruhatCompactTestIndex G) :
    Continuous (L.comp i.inclusion) := by
  apply continuous_of_tendsto_nhds_zero
  let W := PolynormableSpace.withSeminorms ℂ E
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis W.hasBasis_zero_ball).tendsto_right_iff.mpr
  rintro ⟨B, J, ε⟩ ⟨hB, hε⟩
  let p := J.sup (fun q : {q : Seminorm ℂ E // Continuous q} ↦ q.val)
  have hp : Continuous p := Seminorm.continuous_finsetSup fun q _ ↦ q.property
  obtain ⟨C, hC, hc⟩ := compact_orbits_bounded ρ hρ i.2.property hB p hp
  let q : Seminorm ℂ i.1.Space := elementarySchwartzSeminorm (0, 0, 0, 0)
  have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
  let q' : Seminorm ℂ i.Space := q.comp (i.1.compactTests i.2.val).subtype
  have hcq : Continuous q' := hq.comp continuous_subtype_val
  let M := C * μ.real i.2.val
  let δ := ε / (M + 1)
  have hM : 0 ≤ M := mul_nonneg hC.le ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [(hcq.isOpen_preimage _ isOpen_Iio).mem_nhds
    (show q' 0 < δ by simpa only [map_zero] using hδ)] with f hf
  intro u hu
  let φ := i.inclusion f
  have hoff (g : G) (hg : g ∉ i.2.val) : φ.val.val g = 0 :=
    f.property g hg
  have hs (g : G) : ‖φ.val.val g‖ ≤ q' f := stage_value_le i.1 f.val g
  change q' f < δ at hf
  have hle := pettis_kernel_seminorm_le μ ρ (hL φ u) i.2.property hoff p hp
    (fun g hg ↦ hc g hg u hu) (fun g _ ↦ hs g) (apply_nonneg _ _)
  change p (L φ u - 0) < ε
  rw [sub_zero]
  calc
    _ ≤ q' f * M := hle.trans_eq (by dsimp [M]; ring)
    _ ≤ δ * M := mul_le_mul_of_nonneg_right hf.le hM
    _ < δ * (M + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ _ (by positivity)

set_option maxHeartbeats 2800000 in
/-- Compactly supported test functions act continuously in the topology of
uniform convergence on bounded sets whenever the orbits have Pettis integrals.
The proof uses the zero-order test seminorm on each fixed-support stage. -/
theorem exists_bruhatPettisConvolution [T2Space E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (ρ : G → E →ₗ[ℂ] E)
    (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2)
    (hInt : ∀ (φ : BruhatCompactTest G) u,
      ∃ v, HasPositivePettisIntegral μ (fun g ↦ φ.val.val g • ρ g u) v) :
    ∃ A : BruhatCompactTest G →L[ℂ] (E →L[ℂ] E),
      ∀ φ u, HasPositivePettisIntegral μ (fun g ↦ φ.val.val g • ρ g u) (A φ u) := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hExists (φ : BruhatCompactTest G) :=
    exists_continuousPettisKernel μ ρ hρ (bruhatSchwartz_continuous φ.val) φ.property (hInt φ)
  choose A hA using hExists
  let L : BruhatCompactTest G →ₗ[ℂ] (E →L[ℂ] E) :=
    { toFun := A
      map_add' := fun φ ψ ↦ by
        ext u
        apply positivePettis_integral_unique (hA (φ + ψ) u)
        change HasPositivePettisIntegral μ
          (fun g ↦ (φ.val.val g + ψ.val.val g) • ρ g u) (A φ u + A ψ u)
        simp only [add_smul]
        exact hasPositivePettisIntegral_add μ (hA φ u) (hA ψ u)
      map_smul' := fun c φ ↦ by
        ext u
        apply positivePettis_integral_unique (hA (c • φ) u)
        change HasPositivePettisIntegral μ (fun g ↦ (c • φ.val.val g) • ρ g u) (c • A φ u)
        simp only [smul_assoc]
        exact hasPositivePettisIntegral_smul μ c (hA φ u) }
  refine ⟨⟨L, ?_⟩, hA⟩
  letI : LocallyConvexSpace ℂ E := by
    apply LocallyConvexSpace.ofBasisZero ℂ E _ _
      (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball
    intro i _
    exact convex_RCLike_iff_convex_real.mpr (Seminorm.convex_ball _ _ _)
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  letI : LocallyConvexSpace ℂ (E →L[ℂ] E) := ContinuousLinearMap.instLocallyConvexSpace
  letI : ContinuousSMul ℝ (E →L[ℂ] E) := IsScalarTower.continuousSMul ℂ
  letI : PolynormableSpace ℂ (E →L[ℂ] E) := LocallyConvexSpace.toPolynormableSpace
  apply (locallyConvexFinal_continuous_iff
    (fun i : BruhatCompactTestIndex G ↦ i.inclusion) L).mpr
  exact continuous_operators_on_bruhatStage μ ρ hρ L hA

end Estimates

end
end Masullo
