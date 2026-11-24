import ModulatedSobolevMellin
import ModulatedJumpPoisson

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* Multiplicative ℝ)
variable (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure m.toMonoidHom.ker) [SFinite μ]

local notation "Kernel" => m.toMonoidHom.ker

/-- The logarithmically weighted group measure, in the manuscript's split Haar coordinates. -/
def modulatedSobolevMeasure (b s : ℝ) : Measure G :=
  Measure.map (modulatedLogSplit m τ hτ) ((stripMeasure b b s).prod μ)

/-- The pushed product measure is Haar weighted by the source Sobolev density. -/
theorem modulatedSobolevMeasure_eq_weighted (b s : ℝ) :
    modulatedSobolevMeasure m τ hτ μ b s =
      hardySobolevMeasure (modulatedLogMeasure m τ hτ μ) (modulatedLog m) b b s := by
  let e := modulatedLogSplit m τ hτ
  let w (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (stripSobolevAmplitude b b s x ^ 2)
  have hw : Measurable w :=
    ((stripSobolevAmplitude_continuous b b s).pow 2).measurable.ennreal_ofReal
  have hm : Measurable (modulatedLog m) := (continuous_toAdd.comp m.continuous).measurable
  have he (p : ℝ × Kernel) : modulatedLog m (e p) = p.1 := by
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.1) * p.2.val)) = p.1
    rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one]
    rfl
  apply Measure.ext_of_lintegral
  intro f hf
  have heM := e.continuous.measurable
  change (∫⁻ g, f g ∂Measure.map e ((volume.withDensity w).prod μ)) =
    ∫⁻ g, f g ∂(Measure.map e (volume.prod μ)).withDensity
      (fun g => ENNReal.ofReal (hardySobolevWeight b b s (modulatedLog m g)))
  simp only [← stripSobolevAmplitude_sq (a := b) (b := b) (s := s) le_rfl]
  change (∫⁻ g, f g ∂Measure.map e ((volume.withDensity w).prod μ)) =
    ∫⁻ g, f g ∂(Measure.map e (volume.prod μ)).withDensity (w ∘ modulatedLog m)
  rw [prod_withDensity_left hw, lintegral_map hf heM,
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun p : ℝ × Kernel => w p.1) from hw.comp measurable_fst)
      (show Measurable (fun p : ℝ × Kernel => f (e p)) from hf.comp heM),
    lintegral_withDensity_eq_lintegral_mul _ (hw.comp hm) hf,
    lintegral_map ((hw.comp hm).mul hf) heM]
  exact lintegral_congr (fun p => by simp only [Pi.mul_apply, Function.comp_apply, he])

include hτ in
omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
private theorem sectionChange_ker (σ : Multiplicative ℝ →ₜ* G) (hσ : RightInverse σ m) (x : ℝ) :
    σ (Multiplicative.ofAdd x) / τ (Multiplicative.ofAdd x) ∈ Kernel := by
  change m (σ (Multiplicative.ofAdd x) / τ (Multiplicative.ofAdd x)) = 1
  rw [map_div, hσ, hτ, div_self']

include hτ in
/-- Changing the section is a Haar-preserving translation in each radial fiber. -/
theorem modulatedSectionChange_measurePreserving [μ.IsMulLeftInvariant]
    (σ : Multiplicative ℝ →ₜ* G) (hσ : RightInverse σ m) (ν : Measure ℝ) [SFinite ν] :
    MeasurePreserving (fun p : ℝ × Kernel =>
      (p.1, (⟨σ (Multiplicative.ofAdd p.1) / τ (Multiplicative.ofAdd p.1),
        sectionChange_ker m τ hτ σ hσ p.1⟩ : Kernel) * p.2)) (ν.prod μ) (ν.prod μ) := by
  let κ (x : ℝ) : Kernel := ⟨σ (Multiplicative.ofAdd x) / τ (Multiplicative.ofAdd x),
    sectionChange_ker m τ hτ σ hσ x⟩
  have hκ : Continuous κ :=
    ((σ.continuous.comp continuous_ofAdd).div' (τ.continuous.comp continuous_ofAdd)).subtype_mk _
  exact (MeasurePreserving.id ν).skew_product
    ((hκ.comp continuous_fst).mul continuous_snd).measurable
    (Eventually.of_forall fun x => map_mul_left_eq_self μ (κ x))

/-- The weighted Haar measure is independent of the splitting section. -/
theorem modulatedSobolevMeasure_section_independent [μ.IsMulLeftInvariant]
    (σ : Multiplicative ℝ →ₜ* G) (hσ : RightInverse σ m) (b s : ℝ) :
    modulatedSobolevMeasure m τ hτ μ b s = modulatedSobolevMeasure m σ hσ μ b s := by
  let ν := stripMeasure b b s
  let κ (x : ℝ) : Kernel := ⟨σ (Multiplicative.ofAdd x) / τ (Multiplicative.ofAdd x),
    sectionChange_ker m τ hτ σ hσ x⟩
  let A (p : ℝ × Kernel) := (p.1, κ p.1 * p.2)
  have hA : MeasurePreserving A (ν.prod μ) (ν.prod μ) :=
    modulatedSectionChange_measurePreserving m τ hτ μ σ hσ ν
  have hcomp : modulatedLogSplit m σ hσ = (modulatedLogSplit m τ hτ) ∘ A := by
    funext p
    change σ (Multiplicative.ofAdd p.1) * p.2.val =
      τ (Multiplicative.ofAdd p.1) * ((σ (Multiplicative.ofAdd p.1) /
        τ (Multiplicative.ofAdd p.1)) * p.2.val)
    rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left]
  change Measure.map (modulatedLogSplit m τ hτ) (ν.prod μ) =
    Measure.map (modulatedLogSplit m σ hσ) (ν.prod μ)
  rw [hcomp, ← Measure.map_map (modulatedLogSplit m τ hτ).continuous.measurable hA.measurable,
    hA.map_eq]

private def sobolevGroupCoordinates :
    (Kernel × ℝ) ≃ᵐ G :=
  ((Homeomorph.prodComm Kernel ℝ).trans (modulatedLogSplit m τ hτ)).toMeasurableEquiv

private theorem sobolevGroupCoordinates_apply (p : Kernel × ℝ) :
    sobolevGroupCoordinates m τ hτ p = τ (Multiplicative.ofAdd p.2) * p.1.val := rfl

private theorem sobolevGroupCoordinates_measurePreserving (b s : ℝ) :
    MeasurePreserving (sobolevGroupCoordinates m τ hτ)
      (μ.prod (stripMeasure b b s)) (modulatedSobolevMeasure m τ hτ μ b s) := by
  let ν := stripMeasure b b s
  let e := modulatedLogSplit m τ hτ
  exact (show MeasurePreserving e (ν.prod μ) (Measure.map e (ν.prod μ)) from
    ⟨e.continuous.measurable, rfl⟩).comp Measure.measurePreserving_swap

/-- Pullback along the group section is an isometry between the actual weighted
group (L^2) space and the product (L^2) space. -/
def modulatedSobolevGroupEquiv (b s : ℝ) :
    Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b s) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (μ.prod (stripMeasure b b s)) := by
  let e := sobolevGroupCoordinates m τ hτ
  let h := sobolevGroupCoordinates_measurePreserving m τ hτ μ b s
  let J : Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b s) →ₗᵢ[ℂ]
      Lp ℂ 2 (μ.prod (stripMeasure b b s)) := Lp.compMeasurePreservingₗᵢ ℂ e h
  refine LinearIsometryEquiv.ofSurjective J (fun u => ?_)
  let I : Lp ℂ 2 (μ.prod (stripMeasure b b s)) →ₗᵢ[ℂ]
      Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b s) :=
    Lp.compMeasurePreservingₗᵢ ℂ e.symm (h.symm e)
  refine ⟨I u, ?_⟩
  apply Lp.ext
  have he := Lp.coeFn_compMeasurePreserving (I u) h
  have he' := Lp.coeFn_compMeasurePreserving u (h.symm e)
  filter_upwards [he, h.quasiMeasurePreserving.ae he'] with p hp h'p
  exact hp.trans (h'p.trans (congrArg (fun q => u q) (e.symm_apply_apply p)))

theorem modulatedSobolevGroupEquiv_ae (b s : ℝ)
    (u : Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b s)) :
    (modulatedSobolevGroupEquiv m τ hτ μ b s u : Kernel × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure b b s)]
      fun p => u (τ (Multiplicative.ofAdd p.2) * p.1.val) :=
  Lp.coeFn_compMeasurePreserving u (sobolevGroupCoordinates_measurePreserving m τ hτ μ b s)

private theorem sobolevGroupCoordinates_log (p : Kernel × ℝ) :
    modulatedLog m (sobolevGroupCoordinates m τ hτ p) = p.2 := by
  rw [sobolevGroupCoordinates_apply]
  change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.2) * p.1.val)) = p.2
  rw [map_mul, hτ, show m p.1.val = 1 from p.1.property, mul_one]
  rfl

/-- The supported group space in the actual group weighted measure. -/
def modulatedGroupCutoff (b s : ℝ) (U : Set ℝ) :
    Submodule ℂ (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b s)) :=
  (lpTwoRadialSupport μ (stripMeasure b b s) U).comap
    (modulatedSobolevGroupEquiv m τ hτ μ b s).toLinearMap

theorem modulatedGroupCutoff_mem_iff (b s : ℝ) (U : Set ℝ)
    (u : Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b s)) :
    u ∈ modulatedGroupCutoff m τ hτ μ b s U ↔
      ∀ᵐ g ∂modulatedSobolevMeasure m τ hτ μ b s, modulatedLog m g ∉ U → u g = 0 := by
  let ν := stripMeasure b b s
  let e := sobolevGroupCoordinates m τ hτ
  let J := modulatedSobolevGroupEquiv m τ hτ μ b s
  let h := sobolevGroupCoordinates_measurePreserving m τ hτ μ b s
  have hJ : (J u : Kernel × ℝ → ℂ) =ᵐ[μ.prod ν] u ∘ e :=
    modulatedSobolevGroupEquiv_ae m τ hτ μ b s u
  change (∀ᵐ p ∂μ.prod ν, p.2 ∉ U → J u p = 0) ↔ _
  constructor
  · intro hu
    have hp : ∀ᵐ p ∂μ.prod ν, modulatedLog m (e p) ∉ U → u (e p) = 0 := by
      filter_upwards [hu, hJ] with p hp hEq hn
      change J u p = u (e p) at hEq
      rw [← hEq]
      exact hp (sobolevGroupCoordinates_log m τ hτ p ▸ hn)
    have hv := (h.symm e).quasiMeasurePreserving.ae hp
    filter_upwards [hv] with g hg hn
    simpa only [e.apply_symm_apply] using hg (by simpa only [e.apply_symm_apply] using hn)
  · intro hu
    have hp := h.quasiMeasurePreserving.ae hu
    filter_upwards [hp, hJ] with p hp hEq hn
    change J u p = u (e p) at hEq
    exact hEq.trans (hp (by simpa only [sobolevGroupCoordinates_log m τ hτ p] using hn))

def modulatedGroupCutoffEquiv (b s : ℝ) (U : Set ℝ) :
    modulatedGroupCutoff m τ hτ μ b s U ≃ₗᵢ[ℂ]
      lpTwoRadialSupport μ (stripMeasure b b s) U := by
  let J := modulatedSobolevGroupEquiv m τ hτ μ b s
  let S := lpTwoRadialSupport μ (stripMeasure b b s) U
  let R := modulatedGroupCutoff m τ hτ μ b s U
  let A : R →ₗᵢ[ℂ] S :=
    ⟨(J.toLinearMap.comp R.subtype).codRestrict S (fun u => u.property), fun u => J.norm_map u.val⟩
  refine LinearIsometryEquiv.ofSurjective A fun v => ?_
  exact ⟨⟨J.symm v.val, show J (J.symm v.val) ∈ S by rw [J.apply_symm_apply]; exact v.property⟩,
    Subtype.ext (J.apply_symm_apply v.val)⟩

/-- The physical group version of the supported Mellin isometry. -/
def modulatedGroupMellinEquiv (b : ℝ) (N : ℕ) {U : Set ℝ} (hU : IsOpen U) :
    modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) U ≃ₗᵢ[ℂ]
      Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N U) :=
  (modulatedGroupCutoffEquiv m τ hτ μ b (2 * (N : ℝ)) U).trans
    (modulatedSupportedMellinEquiv μ b N hU)

private theorem modulatedGroupMellin_fiber_ae [IsFiniteMeasure μ] (b s c : ℝ)
    (χ : PontryaginDual Kernel) (z : ℂ) (k : ℕ)
    (u : modulatedGroupCutoff m τ hτ μ b s (Ioi c)) :
    let J := modulatedGroupCutoffEquiv m τ hτ μ b s (Ioi c)
    (fun x => (∫ j : Kernel, (χ j : ℂ) * (J u).val (j, x) ∂μ) *
      mellinEvaluationKernel k z x) =ᵐ[volume]
    (fun x => (∫ j : Kernel, (χ j : ℂ) *
      u.val (τ (Multiplicative.ofAdd x) * j.val) ∂μ) * mellinEvaluationKernel k z x) := by
  intro J
  let ν := stripMeasure b b s
  have he :
      (fun p : Kernel × ℝ => (J u).val p) =ᵐ[μ.prod ν]
        fun p => u.val (τ (Multiplicative.ofAdd p.2) * p.1.val) :=
    modulatedSobolevGroupEquiv_ae m τ hτ μ b s u.val
  have hswap : ∀ᵐ p ∂ν.prod μ, (J u).val (p.2, p.1) =
      u.val (τ (Multiplicative.ofAdd p.1) * p.2.val) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae he
  have ha := absolutelyContinuous_amplitudeMeasure volume _
    (stripSobolevAmplitude_continuous b b s).measurable
    (stripSobolevAmplitude_pos b b s)
  filter_upwards [ha.ae_le (Measure.ae_ae_of_ae_prod hswap)] with x hx
  apply congrArg (· * mellinEvaluationKernel k z x)
  exact integral_congr_ae (hx.mono fun j hj => congrArg ((χ j : ℂ) * ·) hj)

set_option maxHeartbeats 800000 in
/-- Mellin evaluation on the Hilbert tensor agrees with the iterated integral
of the actual physical representative in any chosen splitting. -/
theorem modulatedGroupMellin_evaluation [IsFiniteMeasure μ] (b : ℝ) (N : ℕ) {c : ℝ} (hc : c ≤ 0)
    {z : ℂ} (hz : z.re < b) (k : ℕ) (χ : PontryaginDual Kernel) :
    let E := modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) (Ioi c)
    let H := Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))
    let M := modulatedGroupMellinEquiv m τ hτ μ b N (U := Ioi c) isOpen_Ioi
    ∃! L : StrongDual ℂ H, ∀ u : E,
      let F x := (∫ j : Kernel, (χ j : ℂ) *
        u.val (τ (Multiplicative.ofAdd x) * j.val) ∂μ) * mellinEvaluationKernel k z x
      Integrable F ∧ L (M u) = ∫ x, F x := by
  intro E H M
  let s : ℝ := 2 * (N : ℝ)
  let J := modulatedGroupCutoffEquiv m τ hτ μ b s (Ioi c)
  obtain ⟨L, hL, huniq⟩ := modulatedSupportedMellin_evaluation μ b N hc hz k χ
  have hEq := modulatedGroupMellin_fiber_ae m τ hτ μ b s c χ z k
  refine ⟨L, fun u => ?_, fun L' hL' => ?_⟩
  · have h := hL (J u)
    exact ⟨h.1.congr (hEq u), h.2.trans (integral_congr_ae (hEq u))⟩
  · apply huniq L'
    intro v
    obtain ⟨u, rfl⟩ := J.surjective v
    have h := hL' u
    exact ⟨h.1.congr (hEq u).symm, h.2.trans (integral_congr_ae (hEq u).symm)⟩

/-- The bounded group moment is the holomorphic derivative of the chosen
character coordinate of the Mellin transform. -/
theorem modulatedGroupMellinCharacter_iteratedDeriv [IsFiniteMeasure μ] (b : ℝ) (N : ℕ)
    {c : ℝ} (hc : c ≤ 0) {z : ℂ} (hz : z.re < b) (k : ℕ) (χ : PontryaginDual Kernel)
    (u : modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) (Ioi c)) :
    let M := modulatedGroupMellinEquiv m τ hτ μ b N (U := Ioi c) isOpen_Ioi
    iteratedDeriv k (modulatedMellinCharacter μ b N c χ (M u)) z =
      ∫ x : ℝ, (∫ j : Kernel, (χ j : ℂ) *
        u.val (τ (Multiplicative.ofAdd x) * j.val) ∂μ) * mellinEvaluationKernel k z x := by
  intro M
  let J := modulatedGroupCutoffEquiv m τ hτ μ b (2 * (N : ℝ)) (Ioi c)
  exact (modulatedMellinCharacter_iteratedDeriv μ b N hc hz k χ (J u)).trans
    (integral_congr_ae (modulatedGroupMellin_fiber_ae m τ hτ μ b (2 * (N : ℝ)) c χ z k u))

/-- Corrected Corollary 9.2.1.6 for the actual lower-cutoff group space. -/
theorem modulatedGroupMellin_hardy_decomposition [IsFiniteMeasure μ] (b : ℝ) (N : ℕ)
    {c : ℝ} (hc : c < 0) (χ : PontryaginDual Kernel)
    (u : modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) (Ioi c)) :
    let M := modulatedGroupMellinEquiv m τ hτ μ b N (U := Ioi c) isOpen_Ioi
    let F := modulatedMellinCharacter μ b N c χ (M u)
    DifferentiableOn ℂ F (Complex.re ⁻¹' Iio b) ∧
    (∀ r < b, ∀ k ≤ N, MemLp (fun y : ℝ => iteratedDeriv k F (⟨r, y⟩ : ℂ)) 2 volume) ∧
    (∀ z : ℂ, z.re < b →
      F z = ∫ x : ℝ, (∫ j : Kernel, (χ j : ℂ) *
        u.val (τ (Multiplicative.ofAdd x) * j.val) ∂μ) * Complex.exp (z * (x : ℂ))) ∧
    ∃ F₁ F₂ : ℂ → ℂ,
      DifferentiableOn ℂ F₁ (Complex.re ⁻¹' Iio b) ∧ UniformMellinLineBound (Iio b) N F₁ ∧
      Differentiable ℂ F₂ ∧ UniformMellinLineBound (Ioi b) N F₂ ∧
      (∃ C : ℝ, ∀ z : ℂ,
        ‖F₂ z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x))) ∧
      (∀ z : ℂ, z.re < b → F z = F₁ z + F₂ z) := by
  intro M F
  obtain ⟨hd, hLp, hparts⟩ := modulatedMellinCharacter_decomposition μ b N hc χ (M u)
  refine ⟨hd, hLp, fun z hz => ?_, hparts⟩
  simpa only [iteratedDeriv_zero, mellinEvaluationKernel, pow_zero, mul_one] using
    modulatedGroupMellinCharacter_iteratedDeriv m τ hτ μ b N hc.le hz 0 χ u

/-- The evaluations in Corollary 9.2.1.7 are the actual point and derivative
evaluations on the supported analytic Mellin tensor. -/
theorem modulatedGroupMellin_evaluation_derivative [IsFiniteMeasure μ] (b : ℝ) (N : ℕ)
    {c : ℝ} (hc : c ≤ 0) {z : ℂ} (hz : z.re < b) (k : ℕ) (χ : PontryaginDual Kernel) :
    let E := modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) (Ioi c)
    let H := Completion (Lp ℂ 2 μ ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))
    let M := modulatedGroupMellinEquiv m τ hτ μ b N (U := Ioi c) isOpen_Ioi
    ∃! L : StrongDual ℂ H,
      (∀ v, L v = iteratedDeriv k (modulatedMellinCharacter μ b N c χ v) z) ∧
      ∀ u : E,
        let F x := (∫ j : Kernel, (χ j : ℂ) *
          u.val (τ (Multiplicative.ofAdd x) * j.val) ∂μ) * mellinEvaluationKernel k z x
        Integrable F ∧ L (M u) = ∫ x, F x := by
  intro E H M
  obtain ⟨L, hL, huniq⟩ := modulatedGroupMellin_evaluation m τ hτ μ b N hc hz k χ
  refine ⟨L, ⟨?_, hL⟩, fun L' hL' => huniq L' hL'.2⟩
  intro v
  obtain ⟨u, rfl⟩ := M.surjective v
  exact (hL u).2.trans
    (modulatedGroupMellinCharacter_iteratedDeriv m τ hτ μ b N hc hz k χ u).symm

include hτ in
omit [SFinite μ] in
/-- The integral of any physical test over each Haar fiber is independent of the section. -/
theorem modulatedSection_fiberIntegral_eq [μ.IsMulLeftInvariant]
    (σ : Multiplicative ℝ →ₜ* G) (hσ : RightInverse σ m) (f : G → ℂ) (x : ℝ) :
    (∫ k : Kernel, f (τ (Multiplicative.ofAdd x) * k.val) ∂μ) =
      ∫ k : Kernel, f (σ (Multiplicative.ofAdd x) * k.val) ∂μ := by
  let κ : Kernel := ⟨σ (Multiplicative.ofAdd x) / τ (Multiplicative.ofAdd x),
    sectionChange_ker m τ hτ σ hσ x⟩
  calc
    _ = ∫ k : Kernel, f (τ (Multiplicative.ofAdd x) * (κ * k).val) ∂μ :=
      (integral_mul_left_eq_self (fun k : Kernel => f (τ (Multiplicative.ofAdd x) * k.val)) κ).symm
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun k => congrArg f ?_
      change τ (Multiplicative.ofAdd x) * ((σ (Multiplicative.ofAdd x) /
        τ (Multiplicative.ofAdd x)) * k.val) = σ (Multiplicative.ofAdd x) * k.val
      rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left]

include hτ in
omit [SFinite μ] in
/-- At a fixed group quasi-character, changing the section preserves the
Mellin moment after expressing the same quasi-character in the new coordinates. -/
theorem modulatedGroupMellin_moment_section_independent [μ.IsMulLeftInvariant]
    (σ : Multiplicative ℝ →ₜ* G) (hσ : RightInverse σ m)
    (f q : G → ℂ) (χ ψ : PontryaginDual Kernel) (z w : ℂ) (k : ℕ)
    (hχ : ∀ (x : ℝ) (j : Kernel),
      q (τ (Multiplicative.ofAdd x) * j.val) = (χ j : ℂ) * Complex.exp (z * (x : ℂ)))
    (hψ : ∀ (x : ℝ) (j : Kernel),
      q (σ (Multiplicative.ofAdd x) * j.val) = (ψ j : ℂ) * Complex.exp (w * (x : ℂ))) :
    (∫ x : ℝ, (∫ j : Kernel, (χ j : ℂ) * f (τ (Multiplicative.ofAdd x) * j.val) ∂μ) *
      mellinEvaluationKernel k z x) =
      ∫ x : ℝ, (∫ j : Kernel, (ψ j : ℂ) * f (σ (Multiplicative.ofAdd x) * j.val) ∂μ) *
        mellinEvaluationKernel k w x := by
  have hfactor (a : Multiplicative ℝ →ₜ* G) (ω : PontryaginDual Kernel) (u : ℂ) (x : ℝ)
      (ha : ∀ j : Kernel,
        q (a (Multiplicative.ofAdd x) * j.val) = (ω j : ℂ) * Complex.exp (u * (x : ℂ))) :
      (∫ j : Kernel, (ω j : ℂ) * f (a (Multiplicative.ofAdd x) * j.val) ∂μ) *
        mellinEvaluationKernel k u x =
      (∫ j : Kernel, q (a (Multiplicative.ofAdd x) * j.val) *
        f (a (Multiplicative.ofAdd x) * j.val) ∂μ) * (x : ℂ) ^ k := by
    unfold mellinEvaluationKernel
    rw [← mul_assoc, ← integral_mul_const]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun j => by
      change (ω j : ℂ) * f (a (Multiplicative.ofAdd x) * j.val) * Complex.exp (u * (x : ℂ)) =
        q (a (Multiplicative.ofAdd x) * j.val) * f (a (Multiplicative.ofAdd x) * j.val)
      rw [ha]
      ac_rfl
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    (hfactor τ χ z x (hχ x)).trans
      ((congrArg (· * (x : ℂ) ^ k)
        (modulatedSection_fiberIntegral_eq m τ hτ μ σ hσ (fun g => q g * f g) x)).trans
        (hfactor σ ψ w x (hψ x)).symm)

end

end Masullo
