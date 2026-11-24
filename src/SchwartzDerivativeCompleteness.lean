import SchwartzComplete
import PeriodicDerivativeTopology
import TopologicalLinearLimits

open Function Set Topology TopologicalSpace UniformSpace
open scoped ContDiff SchwartzMap Uniformity

namespace Masullo

noncomputable section

/-- The weighted derivative topology of Schwartz maps into a complex Banach
space is Fréchet, for every real normed domain. -/
theorem isFrechetTVS_schwartzMap_banach (X E : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
    IsFrechetTVS 𝓢(X, E) := by
  letI : CompleteSpace 𝓢(X, E) := completeSpace_schwartzMap
  letI : (uniformity 𝓢(X, E)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  refine ⟨inferInstance, (schwartz_withSeminorms ℂ X E).toPolynormableSpace,
    UniformSpace.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

private theorem isClosed_fixedSupportSchwartz {K : Set ℝ} :
    IsClosed (fixedSupportSchwartz K : Set 𝓢(ℝ, ℂ)) := by
  have he : (fixedSupportSchwartz K : Set 𝓢(ℝ, ℂ)) =
      ⋂ x : ↥(Kᶜ), {f : 𝓢(ℝ, ℂ) | f x = 0} := by
    ext f
    constructor
    · intro hf
      apply mem_iInter.mpr
      intro x
      exact notMem_support.mp fun hx => x.property (hf hx)
    · intro hf x hx
      by_contra hK
      exact (mem_support.mp hx) (mem_iInter.mp hf ⟨x, hK⟩)
  rw [he]
  apply isClosed_iInter
  intro x
  exact isClosed_eq (((BoundedContinuousFunction.evalCLM ℂ (x : ℝ)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).continuous) continuous_const

private theorem periodicChart_isClosedEmbedding (d : ℝ) [Fact (0 < d)] :
    IsClosedEmbedding (periodicChart d Fact.out) := by
  let K := Icc (-d) d
  let hspec := periodicCutoff_spec d (Fact.out : 0 < d)
  let C : SmoothPeriodic d →L[ℂ] LogFixedTest K :=
    compactPeriodicSection d isCompact_Icc hspec.1 hspec.2.1
  let P : LogFixedTest K →L[ℂ] SmoothPeriodic d := periodizationCLM d isCompact_Icc
  have hPC : LeftInverse P C := by
    intro f
    apply Subtype.ext
    exact hspec.2.2 _ f.property.2
  have hC : IsEmbedding C := IsEmbedding.of_comp C.continuous continuous_subtype_val
    (show IsEmbedding (periodicChart d Fact.out) from ⟨⟨rfl⟩, periodicChart_injective d Fact.out⟩)
  have hclosed : IsClosed (range C) := by
    have he : range C = {z | C (P z) = z} := by
      ext z
      constructor
      · rintro ⟨f, rfl⟩
        exact congrArg C (hPC f)
      · intro hz
        exact ⟨P z, hz⟩
    rw [he]
    exact isClosed_eq (C.continuous.comp P.continuous) continuous_id
  exact (isClosed_fixedSupportSchwartz (K := K)).isClosedEmbedding_subtypeVal.comp
    ⟨hC, hclosed⟩

/-- Smooth scalar functions on the circle with the uniform derivative
topology form a Fréchet space. -/
theorem smoothPeriodic_isFrechet_derivatives (d : ℝ) [Fact (0 < d)] :
    @IsFrechetTVS (SmoothPeriodic d) _ _ (periodicDerivativeTopology d) := by
  let U := SmoothPeriodic d
  have htop := smoothPeriodic_topology_eq_derivative d
  suffices hh : IsFrechetTVS U by
    exact (congrArg (fun t : TopologicalSpace U => @IsFrechetTVS U _ _ t) htop).mp hh
  have hW : WithSeminorms (periodicDerivativeSeminorms d) := htop.symm ▸ periodicDerivative_withSeminorms d
  letI : IsTopologicalAddGroup U := hW.topologicalAddGroup
  letI : PolynormableSpace ℂ U := hW.toPolynormableSpace
  letI : UniformSpace U := IsTopologicalAddGroup.rightUniformSpace U
  letI : IsUniformAddGroup U := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have hE := periodicChart_isClosedEmbedding d
  let j := periodicChart d (Fact.out : 0 < d)
  have hj : IsUniformEmbedding j := AddMonoidHom.isUniformEmbedding_of_isEmbedding hE.isEmbedding
  letI : T0Space U := hE.isEmbedding.t0Space
  letI : FirstCountableTopology U := hE.isEmbedding.firstCountableTopology
  letI : (𝓤 U).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact ⟨inferInstance, inferInstance, UniformSpace.metrizableSpace,
    hj.isUniformInducing.completeSpace hE.isClosed_range.isComplete⟩

end
end Masullo
