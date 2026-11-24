import CutoffConvolutionKernel
import NormOneClassCompact
import AdelicHaarScaling

open Filter MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The preimage of a compact interval in the logarithmic norm coordinate is
compact because the norm-one idele class group is compact. -/
theorem ideleClass_logNormBand_compact (a b : ℝ) :
    IsCompact {g : IdeleClass F | (ideleClassLogNorm F g).toAdd ∈ Icc a b} := by
  letI : CompactSpace (normOneIdeleClass F) := normOneIdeleClass_compact F
  let e := ideleClassSplitHomeomorph F
  let S : Set (normOneIdeleClass F × Multiplicative ℝ) :=
    (univ : Set (normOneIdeleClass F)) ×ˢ (Icc a b : Set ℝ)
  have hS : IsCompact S := isCompact_univ.prod isCompact_Icc
  have h := hS.image e.symm.continuous
  have he : e.symm '' S = {g : IdeleClass F | (ideleClassLogNorm F g).toAdd ∈ Icc a b} := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e (e.symm x)).2.toAdd ∈ Icc a b
      rw [e.apply_symm_apply]
      exact hx.2
    · intro hg
      exact ⟨e g, ⟨mem_univ _, hg⟩, e.symm_apply_apply g⟩
  rwa [he] at h

/-- Second countability passes from the adeles to their units and then through
the open quotient by the principal ideles. -/
theorem ideleClass_secondCountable : SecondCountableTopology (IdeleClass F) := by
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))

/-- The source-variable Sobolev density used in (10.4.3.30). -/
def ideleClassSobolevDensity (s : ℝ) (g : IdeleClass F) : ℝ :=
  (1 + (ideleClassLogNorm F g).toAdd ^ 2) ^ (s / 2)

private theorem ideleClassSobolevDensity_continuous (s : ℝ) :
    Continuous (ideleClassSobolevDensity F s) := by
  have h : Continuous (fun g : IdeleClass F => (ideleClassLogNorm F g).toAdd) :=
    ideleClassLogNorm_continuous F
  unfold ideleClassSobolevDensity
  exact (continuous_const.add (h.pow 2)).rpow_const fun g =>
    Or.inl ((add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)).ne')

section Kernel

variable [MeasurableSpace (IdeleClass F)] [BorelSpace (IdeleClass F)]
  (μ : Measure (IdeleClass F)) [μ.IsHaarMeasure]

local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact (F := F)

/-- The cutoff convolution on the idele class group has a square-integrable
kernel and its Hilbert–Schmidt norm equals the kernel norm. -/
theorem ideleClass_cutoffConvolutionKernel_hilbertSchmidt
    (s a b : ℝ) {ρ φ : IdeleClass F → ℂ} (hρ : Continuous ρ) (hφ : AEMeasurable φ μ)
    (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hρsupp : ∀ g, (ideleClassLogNorm F g).toAdd ∉ Icc a b → ρ g = 0)
    (hφsupp : HasCompactSupport φ) :
    let w := ideleClassSobolevDensity F s
    let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure ν :=
      IsLocallyFiniteMeasure.withDensity_ofReal (ideleClassSobolevDensity_continuous F s)
    let k := cutoffConvolutionKernel w ρ φ
    ∃ (hk : MemLp k 2 (ν.prod ν)),
      (∀ f : IdeleClass F →₂[ν] ℂ, ∀ᵐ x ∂μ,
        kernelIntegralOperator (hk.toLp k) f x = ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ) ∧
      IsCompactOperator (kernelIntegralOperator (hk.toLp k)) ∧
      ∃ (J : Set (IdeleClass F →₂[ν] ℂ)) (_ : J.Countable)
        (basis : HilbertBasis J ℂ (IdeleClass F →₂[ν] ℂ)),
        Summable (fun i => ‖kernelIntegralOperator (hk.toLp k) (basis i)‖ ^ 2) ∧
          (∑' i, ‖kernelIntegralOperator (hk.toLp k) (basis i)‖ ^ 2) = ‖hk.toLp k‖ ^ 2 := by
  letI := ideleClasses_hausdorff (F := F)
  have hρc : HasCompactSupport ρ := by
    let K := {g : IdeleClass F | (ideleClassLogNorm F g).toAdd ∈ Icc a b}
    have hK : IsCompact K := ideleClass_logNormBand_compact F a b
    have hs : Function.support ρ ⊆ K := by
      intro x hx
      exact not_not.mp fun hn => hx (hρsupp x hn)
    exact hK.of_isClosed_subset isClosed_closure (closure_minimal hs hK.isClosed)
  have hpos (g : IdeleClass F) : 0 < ideleClassSobolevDensity F s g :=
    Real.rpow_pos_of_pos (by positivity) _
  have hw := ideleClassSobolevDensity_continuous F s
  exact cutoffConvolutionKernel_hilbertSchmidt μ hw hpos hρ hφ hφb hρc hφsupp

/-- The full cutoff convolution term in (10.4.3.37) gives an actual L²
kernel whose action is truncated Haar convolution. -/
theorem ideleClass_cutoffConvolutionKernel
    (s a b : ℝ) {ρ φ : IdeleClass F → ℂ} (hρ : Continuous ρ) (hφ : Continuous φ)
    (hρsupp : ∀ g, (ideleClassLogNorm F g).toAdd ∉ Icc a b → ρ g = 0)
    (hφsupp : HasCompactSupport φ) :
    let w := ideleClassSobolevDensity F s
    let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure ν :=
      IsLocallyFiniteMeasure.withDensity_ofReal (ideleClassSobolevDensity_continuous F s)
    let k := cutoffConvolutionKernel w ρ φ
    ∃ hk : MemLp k 2 (ν.prod ν),
      ∀ f : IdeleClass F →₂[ν] ℂ, ∀ᵐ x ∂μ,
        kernelIntegralOperator (hk.toLp k) f x = ρ x * ∫ y, φ y * f (y⁻¹ * x) ∂μ := by
  obtain ⟨hk, haction, _⟩ := ideleClass_cutoffConvolutionKernel_hilbertSchmidt F μ s a b
    hρ hφ.measurable.aemeasurable (hφsupp.exists_bound_of_continuous hφ) hρsupp hφsupp
  exact ⟨hk, haction⟩

end Kernel

end

end Masullo
