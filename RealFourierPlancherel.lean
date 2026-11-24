import CompactCharacterCompleteness
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Normed.Operator.Extend

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal FourierTransform SchwartzMap InnerProductSpace ComplexConjugate

namespace Masullo

noncomputable section

local notation "H" => (Lp ℂ 2 (volume : Measure ℝ))
local notation "S" => (𝓢(ℝ, ℂ))

private instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

private def realSchwartzToL2 : S →L[ℂ] H := SchwartzMap.toLpCLM ℂ ℂ 2 volume

private def realSchwartzFourierToL2 : S →ₗ[ℂ] H :=
  realSchwartzToL2.toLinearMap.comp (SchwartzMap.fourierTransformCLM ℂ).toLinearMap

private theorem realSchwartzToL2_dense : DenseRange realSchwartzToL2 :=
  SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (μ := volume) ENNReal.ofNat_ne_top

private theorem realSchwartzFourierToL2_norm (f : S) :
    ‖realSchwartzFourierToL2 f‖ = ‖realSchwartzToL2 f‖ := by
  have h (g : S) : ‖realSchwartzToL2 g‖ ^ 2 = ∫ x : ℝ, ‖g x‖ ^ 2 :=
    norm_sq_toLp_two (g.memLp 2 volume)
  have hsq : ‖realSchwartzFourierToL2 f‖ ^ 2 = ‖realSchwartzToL2 f‖ ^ 2 := by
    change ‖realSchwartzToL2 (𝓕 f)‖ ^ 2 = ‖realSchwartzToL2 f‖ ^ 2
    rw [h, h, SchwartzMap.integral_norm_sq_fourier]
  nlinarith [norm_nonneg (realSchwartzFourierToL2 f), norm_nonneg (realSchwartzToL2 f)]

private theorem realSchwartzFourierToL2_bound :
    ∃ C : ℝ, ∀ f, ‖realSchwartzFourierToL2 f‖ ≤ C * ‖realSchwartzToL2 f‖ :=
  ⟨1, fun f => by rw [one_mul, realSchwartzFourierToL2_norm]⟩

private def realFourierL2Isometry : H →ₗᵢ[ℂ] H := by
  let F := realSchwartzFourierToL2.extendOfNorm realSchwartzToL2.toLinearMap
  refine { F.toLinearMap with norm_map' := fun v => ?_ }
  refine realSchwartzToL2_dense.induction (fun _ ⟨f, hf⟩ => ?_)
    (isClosed_eq F.continuous.norm continuous_norm) v
  change ‖F _‖ = ‖_‖
  rw [← hf, show F (realSchwartzToL2 f) = realSchwartzFourierToL2 f from
    LinearMap.extendOfNorm_eq realSchwartzToL2_dense realSchwartzFourierToL2_bound f]
  exact realSchwartzFourierToL2_norm f

private theorem realFourierL2Isometry_onSchwartz (f : S) :
    realFourierL2Isometry (realSchwartzToL2 f) = realSchwartzToL2 (𝓕 f) :=
  LinearMap.extendOfNorm_eq realSchwartzToL2_dense realSchwartzFourierToL2_bound f

private theorem realFourierL2Isometry_surjective : Surjective realFourierL2Isometry := by
  have hc := realFourierL2Isometry.isometry.isClosedEmbedding.isClosed_range
  intro v
  apply closure_minimal (s := range realSchwartzToL2) (t := range realFourierL2Isometry) _ hc
    (realSchwartzToL2_dense v)
  rintro _ ⟨f, rfl⟩
  refine ⟨realSchwartzToL2 (𝓕⁻ f), ?_⟩
  rw [realFourierL2Isometry_onSchwartz, FourierTransform.fourier_fourierInv_eq]

/-- The Fourier transform on the real line extends to a unitary operator
on Lebesgue L², with Mathlib's Fourier sign and its (2pi) convention. -/
def realFourierL2 : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective realFourierL2Isometry realFourierL2Isometry_surjective

theorem realFourierL2_onSchwartz (f : S) :
    realFourierL2 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
  realFourierL2Isometry_onSchwartz f

theorem realFourierL2_symm_onSchwartz (f : S) :
    realFourierL2.symm (f.toLp 2 volume) = (𝓕⁻ f).toLp 2 volume := by
  apply realFourierL2.injective
  rw [LinearIsometryEquiv.apply_symm_apply, realFourierL2_onSchwartz, FourierTransform.fourier_fourierInv_eq]

/-- On integrable L² profiles, the real Plancherel transform agrees almost
everywhere with the Fourier integral. -/
theorem realFourierL2_ae_eq_fourier (f : H) (hf : Integrable (f : ℝ → ℂ)) :
    (realFourierL2 f : ℝ → ℂ) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
  have hFc : Continuous (𝓕 (f : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (realFourierL2 f)).locallyIntegrable (by norm_num)) hFc.locallyIntegrable
  intro φ hφ hφc
  let g : S := (hφc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)
  let t := g.toLp 2 volume
  have hg (x : ℝ) : g x = (φ x : ℂ) := rfl
  have hs : (∫ y : ℝ, inner ℂ ((𝓕 (f : ℝ → ℂ)) y) (g y)) =
      ∫ x : ℝ, inner ℂ (f x) ((𝓕⁻ g) x) := by
    have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change inner ℝ y x = inner ℝ x y
      exact real_inner_comm _ _
    have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
      (L := innerₗ ℝ) (μ := volume) (ν := volume) Real.continuous_fourierChar
      continuous_inner hf (g.integrable (μ := volume))
    rw [hflip] at h
    rw [SchwartzMap.fourierInv_coe]
    exact h
  have htest : inner ℂ (realFourierL2 f) t = inner ℂ f ((𝓕⁻ g).toLp 2 volume) := by
    rw [← realFourierL2_symm_onSchwartz, ← realFourierL2.inner_map_map f (realFourierL2.symm t),
      LinearIsometryEquiv.apply_symm_apply]
  have hI : (∫ y : ℝ, inner ℂ (realFourierL2 f y) (g y)) =
      ∫ x : ℝ, inner ℂ (f x) ((𝓕⁻ g) x) := by
    rw [L2.inner_def, L2.inner_def] at htest
    calc
      _ = ∫ y : ℝ, inner ℂ (realFourierL2 f y) (t y) :=
        integral_congr_ae ((g.coeFn_toLp 2 volume).mono fun y hy =>
          congrArg (fun a : ℂ => inner ℂ (realFourierL2 f y) a) hy.symm)
      _ = ∫ x : ℝ, inner ℂ (f x) (((𝓕⁻ g).toLp 2 volume) x) := htest
      _ = _ := integral_congr_ae (((𝓕⁻ g).coeFn_toLp 2 volume).mono fun x hx =>
        congrArg (fun a : ℂ => inner ℂ (f x) a) hx)
  have heq (v : ℝ → ℂ) (x : ℝ) : conj (inner ℂ (v x) (g x)) = φ x • v x := by
    rw [inner_conj_symm, hg, RCLike.inner_apply, Complex.real_smul]
    simp [mul_comm]
  have h := congrArg (conj : ℂ → ℂ) (hI.trans hs.symm)
  rw [← integral_conj, ← integral_conj] at h
  simpa only [heq] using h

/-- The inverse extension agrees with the inverse Fourier integral on
integrable L² profiles. -/
theorem realFourierL2_symm_ae_eq_fourierInv (f : H) (hf : Integrable (f : ℝ → ℂ)) :
    (realFourierL2.symm f : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ (f : ℝ → ℂ) := by
  let h := Measure.measurePreserving_neg (volume : Measure ℝ)
  let R := Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) h (p := 2) (E := ℂ)
  have hR (u : H) : (R u : ℝ → ℂ) =ᵐ[volume] (fun x => u (-x)) :=
    Lp.coeFn_compMeasurePreserving u h
  have he : realFourierL2.symm f = R (realFourierL2 f) := by
    refine realSchwartzToL2_dense.induction_on f
      (isClosed_eq realFourierL2.symm.continuous (R.continuous.comp realFourierL2.continuous)) ?_
    intro g
    change realFourierL2.symm (g.toLp 2 volume) = R (realFourierL2 (g.toLp 2 volume))
    rw [realFourierL2_symm_onSchwartz, realFourierL2_onSchwartz]
    apply Lp.ext
    filter_upwards [(𝓕⁻ g).coeFn_toLp 2 volume, hR ((𝓕 g).toLp 2 volume),
      h.quasiMeasurePreserving.ae_eq_comp ((𝓕 g).coeFn_toLp 2 volume)] with x hx hy hz
    rw [hx, hy]
    have hfneg : (𝓕⁻ g) x = (𝓕 g) (-x) := by
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]
    exact hfneg.trans hz.symm
  rw [he]
  exact (hR (realFourierL2 f)).trans
    ((h.quasiMeasurePreserving.ae_eq_comp (realFourierL2_ae_eq_fourier f hf)).trans
      (.of_forall fun x => (Real.fourierInv_eq_fourier_neg (f : ℝ → ℂ) x).symm))

/-- Exact real Plancherel energy for every integrable square-integrable profile. -/
theorem real_fourier_integral_plancherel {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume ∧ (∫ y : ℝ, ‖𝓕 f y‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let u := h₂.toLp f
  have hU : (u : ℝ → ℂ) =ᵐ[volume] f := h₂.coeFn_toLp
  have hf : Integrable (u : ℝ → ℂ) := h₁.congr hU.symm
  have hF := (realFourierL2_ae_eq_fourier u hf).trans
    (.of_forall fun y => Real.fourier_congr_ae hU y)
  have hmem := (Lp.memLp (realFourierL2 u)).ae_eq hF
  have he : hmem.toLp (𝓕 f) = realFourierL2 u := Lp.ext (hmem.coeFn_toLp.trans hF.symm)
  refine ⟨hmem, ?_⟩
  rw [← norm_sq_toLp_two hmem, ← norm_sq_toLp_two h₂, he]
  rw [realFourierL2.norm_map]

end
end Masullo
