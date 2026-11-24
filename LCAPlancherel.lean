/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
db376192baf52253727c46e2b211619d4e6a3941, AppD_SchwartzBruhat/Sec1a.lean.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import LCAFourierIntegral
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal
open InnerProductSpace

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- The prescribed Plancherel isometry agrees with the Fourier integral
on the common domain of the two transforms. -/
def IsFourierPlancherel (μ : Measure G) (ν : Measure (PontryaginDual G))
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν) : Prop :=
  ∀ (f : G → ℂ) (_ : Integrable f μ) (h₂ : MemLp f 2 μ),
    (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Paper: Lemma D.1.1.2(4), p. 747. A Plancherel measure is a regular Haar measure
on the dual for which the Fourier transform preserves the finite L² norm on L¹ ∩ L². -/
def IsLCAPlancherelMeasure (μ : Measure G) (ν : Measure (PontryaginDual G)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ (f : G → ℂ), Integrable f μ → MemLp f 2 μ →
      MemLp (lcaFourier μ f) 2 ν ∧ eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ

omit [T2Space G] [μ.Regular] in
/-- The Fourier norm of a single nonzero compactly supported test function fixes the
scalar between two regular Haar measures satisfying Plancherel. -/
theorem isLCAPlancherelMeasure_unique
    {ν₁ ν₂ : Measure (PontryaginDual G)}
    (h₁ : IsLCAPlancherelMeasure μ ν₁) (h₂ : IsLCAPlancherelMeasure μ ν₂) : ν₁ = ν₂ := by
  let := h₁.1
  let := h₁.2.1
  let := h₂.1
  let := h₂.2.1
  let c := ν₁.haarScalarFactor ν₂
  have hc : ν₁ = c • ν₂ := Measure.isMulLeftInvariant_eq_smul_of_regular _ _
  obtain ⟨g, hgK, -, hg₁⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : G → ℂ := fun x ↦ g x
  have hfC : Continuous f := Complex.continuous_ofReal.comp g.continuous
  have hfK : HasCompactSupport f := hgK.comp_left Complex.ofReal_zero
  have hf₁ := hfC.integrable_of_hasCompactSupport (μ := μ) hfK
  have hf₂ := hfC.memLp_of_hasCompactSupport (μ := μ) (p := 2) hfK
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff hf₂.aestronglyMeasurable (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
    have hEq : f = 0 := Measure.eq_of_ae_eq hae hfC continuous_const
    exact hg₁ (Complex.ofReal_eq_zero.mp (congrFun hEq 1))
  have hScale := (h₁.2.2 f hf₁ hf₂).2
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp : (2 : ℝ≥0∞) ≠ ⊤),
    (h₂.2.2 f hf₁ hf₂).2] at hScale
  change (↑(c ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * eLpNorm f 2 μ = eLpNorm f 2 μ at hScale
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)] at hScale
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 :=
    (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp (hScale.trans (one_mul _).symm)
  have hc₁ : c = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot
  rw [hc, hc₁, one_smul]

/-- The range of an L² Fourier isometry has trivial orthogonal complement.
Orthogonality to translates of each integrable test function forces the product of its
conjugated transform with the orthogonal vector to vanish almost everywhere. -/
private theorem lcaFourier_isometry_surjective
    {ν : Measure (PontryaginDual G)} [ν.Regular]
    (U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (f : G → ℂ), Integrable f μ → ∀ (h₂ : MemLp f 2 μ),
      (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f) :
    Function.Surjective U := by
  classical
  let R := U.toLinearMap.range
  have hClosed : IsClosed (R : Set (Lp ℂ 2 ν)) := U.isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace R := hClosed.isComplete.completeSpace_coe
  suffices R = ⊤ from LinearMap.range_eq_top.mp this
  refine Submodule.orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr ?_)
  intro g hg
  have hInner (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      ∫ χ, g χ * star (lcaFourier μ f χ) ∂ν = 0 := by
    have hZero := (R.mem_orthogonal g).mp hg _ (U.toLinearMap.mem_range_self (h₂.toLp f))
    change inner ℂ (U (h₂.toLp f)) g = 0 at hZero
    rw [L2.inner_def] at hZero
    refine (integral_congr_ae ((hU f hf h₂).mono fun χ hχ ↦ ?_)).trans hZero
    rw [RCLike.inner_apply, starRingEnd_apply, hχ]
  have hProduct (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      (fun χ ↦ g χ * star (lcaFourier μ f χ)) =ᵐ[ν] 0 := by
    have hInt : Integrable (fun χ ↦ g χ * star (lcaFourier μ f χ)) ν :=
      (L2.integrable_inner (𝕜 := ℂ) (U (h₂.toLp f)) g).congr
        ((hU f hf h₂).mono fun χ hχ ↦ by
          change inner ℂ (U (h₂.toLp f) χ) (g χ) = _
          rw [RCLike.inner_apply, starRingEnd_apply, hχ])
    refine ae_eq_zero_of_integral_mul_circle_eq_zero (X := PontryaginDual G) (D := G)
      (fun χ : PontryaginDual G ↦ χ.toMonoidHom)
      (fun a ↦ (continuous_eval_const (F := C(G, Circle)) a).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous)
      (fun _ _ h ↦ PontryaginDual.ext (fun a ↦ congrArg (fun k : G →* Circle ↦ k a) h))
      hInt ?_
    intro a
    let m := measurePreserving_mul_left μ a⁻¹
    have hZero := hInner (fun x ↦ f (a⁻¹ * x)) (m.integrable_comp_of_integrable hf)
      (h₂.comp_measurePreserving m)
    refine (integral_congr_ae (.of_forall fun χ ↦ ?_)).trans hZero
    change g χ * star (lcaFourier μ f χ) * (χ a : ℂ) = _
    rw [lcaFourier_translate μ f a⁻¹ χ, star_mul, map_inv, Circle.coe_inv_eq_conj,
      ← Complex.star_def, star_star]
    ring
  -- A modulated indicator of a compact neighborhood gives a transform nonzero at each point.
  obtain ⟨K, hK, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hKm := hK.isClosed.measurableSet
  have hKfin := (hK.measure_lt_top (μ := μ)).ne
  have hKpos : 0 < μ K := (isOpen_interior.measure_pos μ
    ⟨1, mem_interior_iff_mem_nhds.mpr hK₁⟩).trans_le (measure_mono interior_subset)
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hKfin
  let f (ψ : PontryaginDual G) : G → ℂ := K.indicator fun x ↦ (ψ x : ℂ)
  have hfLp (ψ : PontryaginDual G) (p : ℝ≥0∞) : MemLp (f ψ) p μ :=
    (memLp_indicator_iff_restrict hKm).mpr <|
      MemLp.of_bound (continuous_subtype_val.comp ψ.continuous).aestronglyMeasurable
        1 (.of_forall fun x ↦ (Circle.norm_coe (ψ x)).le)
  have hf (ψ : PontryaginDual G) : Integrable (f ψ) μ :=
    memLp_one_iff_integrable.mp (hfLp ψ 1)
  have hNonzero (ψ : PontryaginDual G) : lcaFourier μ (f ψ) ψ ≠ 0 := by
    unfold lcaFourier
    rw [show (fun x ↦ f ψ x * star (ψ x : ℂ)) = K.indicator (fun _ ↦ (1 : ℂ)) by
      funext x
      by_cases hx : x ∈ K
      · simp only [f, indicator_of_mem hx, Complex.star_def, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow, Complex.ofReal_one]
      · simp [f, hx]]
    rw [integral_indicator hKm, integral_const, Measure.real, Measure.restrict_apply_univ,
      Complex.real_smul, mul_one]
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hKpos.ne' hKfin).ne'
  let O (ψ : PontryaginDual G) := {χ | lcaFourier μ (f ψ) χ ≠ 0}
  have hOpen (ψ : PontryaginDual G) : IsOpen (O ψ) :=
    isOpen_ne_fun (continuous_lcaFourier μ (hf ψ)) continuous_const
  have hLocal (ψ : PontryaginDual G) : ∀ᵐ χ ∂ν.restrict (O ψ), g χ = 0 := by
    filter_upwards [ae_restrict_of_ae (hProduct (f ψ) (hf ψ) (hfLp ψ 2)),
      ae_restrict_mem (hOpen ψ).measurableSet] with χ hχ hmem
    exact (mul_eq_zero.mp hχ).resolve_right (star_ne_zero.mpr hmem)
  have hCompact (L : Set (PontryaginDual G)) (hL : IsCompact L) :
      ∀ᵐ χ ∂ν.restrict L, g χ = 0 := by
    obtain ⟨t, -, ht⟩ := hL.elim_nhds_subcover O (fun ψ _ ↦ (hOpen ψ).mem_nhds (hNonzero ψ))
    exact ae_mono (Measure.restrict_mono ht le_rfl)
      ((ae_restrict_biUnion_finset_iff O t _).mpr (fun ψ _ ↦ hLocal ψ))
  -- Compact approximation of the integrable squared norm avoids a countability assumption.
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [L2.inner_def]
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  let q (χ : PontryaginDual G) := inner ℂ (g χ) (g χ)
  have hq : Integrable q ν := L2.integrable_inner g g
  obtain ⟨L, -, hL, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hq MeasurableSet.univ hε
  have hZero : ∫ χ in L, q χ ∂ν = 0 := by
    have hqZero : q =ᵐ[ν.restrict L] (0 : PontryaginDual G → ℂ) :=
      (hCompact L hL).mono fun χ hχ ↦ by simp [q, hχ]
    rw [integral_congr_ae hqZero, Pi.zero_def, integral_zero]
  have hEq : (∫ χ, q χ ∂ν) = ∫ χ in Lᶜ, q χ ∂ν := by
    rw [← integral_add_compl hL.isClosed.measurableSet hq, hZero, zero_add]
  change ‖∫ χ, q χ ∂ν‖ < 0 + ε
  rw [hEq, zero_add]
  exact (norm_integral_le_integral_norm q).trans_lt (by rwa [← compl_eq_univ_sdiff] at hTail)

/-- Paper: Lemma D.1.1.2(4), p. 747. The Fourier transform on L¹ ∩ L²
extends uniquely to a unitary isomorphism on L². -/
theorem lcaFourier_unitary (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) :
    ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
      IsFourierPlancherel μ ν U := by
  let : ν.Regular := hν.2.1
  let D : Submodule ℂ (Lp ℂ 2 μ) :=
    { carrier := {f | Integrable (f : G → ℂ) μ}
      zero_mem' := (integrable_zero G ℂ μ).congr (Lp.coeFn_zero ℂ 2 μ).symm
      add_mem' := fun {_ _} hf hg ↦ (hf.add hg).congr (Lp.coeFn_add _ _).symm
      smul_mem' := fun c _ hf ↦ (hf.smul c).congr (Lp.coeFn_smul c _).symm }
  have hDense : DenseRange D.subtype := by
    apply (Lp.simpleFunc.denseRange (E := ℂ) (p := 2) (μ := μ) ENNReal.ofNat_ne_top).mono
    rintro f ⟨g, rfl⟩
    have hInt : Integrable (Lp.simpleFunc.toSimpleFunc g) μ :=
      (SimpleFunc.memLp_iff_integrable two_ne_zero ENNReal.ofNat_ne_top).mp (Lp.simpleFunc.memLp g)
    exact ⟨⟨g, hInt.congr (Lp.simpleFunc.toSimpleFunc_eq_toFun g)⟩, rfl⟩
  have hPlancherel (f : D) := hν.2.2 f f.2 (Lp.memLp (f : Lp ℂ 2 μ))
  let transform (f : D) : Lp ℂ 2 ν := (hPlancherel f).1.toLp (lcaFourier μ f)
  have hTransform (f : D) : (transform f : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f :=
    MemLp.coeFn_toLp _
  let F : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := transform
      map_add' f g := by
        apply Lp.ext
        filter_upwards [hTransform (f + g), hTransform f, hTransform g,
          Lp.coeFn_add (transform f) (transform g)] with χ hfg hf hg hAdd
        change transform (f + g) χ = (transform f + transform g) χ
        rw [hfg, hAdd, Pi.add_apply, hf, hg]
        unfold lcaFourier
        calc
          _ = ∫ x, ((f : Lp ℂ 2 μ) x + (g : Lp ℂ 2 μ) x) * star (χ x : ℂ) ∂μ :=
            integral_congr_ae ((Lp.coeFn_add (f : Lp ℂ 2 μ) g).mono fun x hx ↦ by
              change ((f : Lp ℂ 2 μ) + (g : Lp ℂ 2 μ)) x * _ = _
              rw [hx]
              rfl)
          _ = _ := by
            simp_rw [add_mul]
            exact integral_add (integrable_fourierIntegrand μ f.2 χ)
              (integrable_fourierIntegrand μ g.2 χ)
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [hTransform (c • f), hTransform f, Lp.coeFn_smul c (transform f)]
          with χ hcf hf hSmul
        change transform (c • f) χ = (c • transform f) χ
        rw [hcf, hSmul, Pi.smul_apply, hf]
        unfold lcaFourier
        calc
          _ = ∫ x, c • ((f : Lp ℂ 2 μ) x * star (χ x : ℂ)) ∂μ :=
            integral_congr_ae ((Lp.coeFn_smul c (f : Lp ℂ 2 μ)).mono fun x hx ↦ by
              change ((c • (f : Lp ℂ 2 μ)) : Lp ℂ 2 μ) x * _ = _
              rw [hx, Pi.smul_apply]
              exact smul_mul_assoc _ _ _)
          _ = _ := integral_smul c _ }
  have hNorm (f : D) : ‖F f‖ = ‖D.subtype f‖ := by
    change ‖(hPlancherel f).1.toLp (lcaFourier μ f)‖ = ‖(f : Lp ℂ 2 μ)‖
    rw [Lp.norm_toLp, Lp.norm_def, (hPlancherel f).2]
  let V := F.extendOfNorm D.subtype
  have hEqOn (x : D) : V (D.subtype x) = F x :=
    F.extendOfNorm_eq hDense ⟨1, fun x ↦ by rw [hNorm, one_mul]⟩ x
  have hVNorm (x : Lp ℂ 2 μ) : ‖V x‖ = ‖x‖ :=
    hDense.induction_on x (isClosed_eq V.continuous.norm continuous_norm)
      (fun y ↦ (congrArg norm (hEqOn y)).trans (hNorm y))
  let U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 ν := ⟨V.toLinearMap, hVNorm⟩
  have hU (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
    let x : D := ⟨h₂.toLp f, hf.congr h₂.coeFn_toLp.symm⟩
    have hEq : U (D.subtype x) = F x := hEqOn x
    change (U (D.subtype x) : PontryaginDual G → ℂ) =ᵐ[ν] _
    rw [hEq]
    refine (hTransform x).trans (.of_forall fun χ ↦ integral_congr_ae ?_)
    exact h₂.coeFn_toLp.mono fun y hy ↦ by change _ * _ = _ * _; rw [hy]
  let e := LinearIsometryEquiv.ofSurjective U (lcaFourier_isometry_surjective μ U hU)
  refine ⟨e, hU, fun V hV ↦ ?_⟩
  apply LinearIsometryEquiv.ext
  intro f
  refine hDense.induction_on (p := fun w ↦ V w = e w) f
    (isClosed_eq V.continuous e.continuous) fun x ↦ ?_
  have hx := Lp.memLp (x : Lp ℂ 2 μ)
  have hEq : hx.toLp (x : G → ℂ) = D.subtype x := Lp.toLp_coeFn _ hx
  rw [← hEq]
  exact Lp.ext ((hV x x.2 hx).trans (hU x x.2 hx).symm)


end
end Masullo
