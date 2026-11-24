import IdelicWeilFiniteLinear
import IdelicHeckeZeroStrongDual
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology UniformSpace
open scoped Classical NumberField UniformConvergence UniformConvergenceCLM

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
local notation "Place" => HeightOneSpectrum (𝓞 F)
private abbrev LocalField (v : Place) := v.adicCompletion F

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

private theorem continuous_of_finite_evaluations {X I : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [Fintype I]
    (L : X →ₗ[ℂ] ℂ) (T : X →ₗ[ℂ] (I → ℂ)) (hT : Continuous T)
    (hker : LinearMap.ker T ≤ LinearMap.ker L) : Continuous L := by
  let Q : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ L hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hE : (L : X → ℂ) = Q ∘ T.rangeRestrict := by
    funext u
    change L u = (LinearMap.ker T).liftQ L hker (T.quotKerEquivRange.symm ⟨T u, _⟩)
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  rw [hE]
  exact Q.continuous_of_finiteDimensional.comp (hT.subtype_mk _)

set_option maxHeartbeats 1100000 in
private theorem finitePlace_exists_coset_cover (v : Place)
    (C : Set (LocalField F v)ˣ) (hC : IsCompact C)
    (H : Subgroup (IntegralUnitFamily F)) (hH : IsOpen (H : Set (IntegralUnitFamily F))) :
    ∃ S : Finset (LocalField F v)ˣ, ∀ x ∈ C, ∃ y ∈ S, ∃ b : principalIntegralUnits F v,
      integralUnitFamilySingle F v b ∈ H ∧ y * b.val = x := by
  let U := principalIntegralUnits F v
  let O : Set (LocalField F v)ˣ :=
    Subtype.val '' (integralUnitFamilySingle F v ⁻¹' (H : Set (IntegralUnitFamily F)))
  have hU : IsOpen (U : Set (LocalField F v)ˣ) := by
    have he : (U : Set (LocalField F v)ˣ) = finitePlaceIntegralUnits F v := by
      ext u
      exact (finiteCompletion_norm_eq_one_iff F v u).trans (localIntegralUnits_value F v u).symm
    rw [he]
    exact localIntegralUnits_open F v
  have hO : IsOpen O := hU.isOpenMap_subtype_val _ (hH.preimage (integralUnitFamilySingle_continuous F v))
  have h1 : (1 : (LocalField F v)ˣ) ∈ O := by
    refine ⟨1, ?_, rfl⟩
    have he : integralUnitFamilySingle F v (1 : U) = 1 := by
      exact Function.update_eq_self v (1 : IntegralUnitFamily F)
    change integralUnitFamilySingle F v (1 : U) ∈ H
    rw [he]
    exact H.one_mem
  let V (x : (LocalField F v)ˣ) : Set (LocalField F v)ˣ := (fun a => x * a) '' O
  have hV (x) : IsOpen (V x) := (Homeomorph.mulLeft x).isOpenMap _ hO
  have hcover : C ⊆ ⋃ x, V x := fun x _ => mem_iUnion.mpr ⟨x, 1, h1, mul_one x⟩
  obtain ⟨S, hS⟩ := hC.elim_finite_subcover V hV hcover
  refine ⟨S, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hS hx)
  obtain ⟨hyS, ⟨a, ⟨b, hb, rfl⟩, he⟩⟩ := mem_iUnion.mp hy
  exact ⟨y, hyS, b, hb, he⟩

private theorem continuous_of_finite_test_values {X A : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [TopologicalSpace A]
    (R : X →ₗ[ℂ] locallyConstantTests A) (J : locallyConstantTests A →ₗ[ℂ] ℂ)
    (S : Finset A) (heval : ∀ a, Continuous (fun u => (R u).val a))
    (hsep : ∀ u, (∀ a ∈ S, (R u).val a = 0) → (R u).val = 0) :
    Continuous (J.comp R) := by
  let T : X →ₗ[ℂ] (S → ℂ) := LinearMap.pi (fun a : S =>
    (LinearMap.proj a.val).comp ((locallyConstantTests A).subtype.comp R))
  apply continuous_of_finite_evaluations (J.comp R) T
  · exact continuous_pi fun a => heval a.val
  · intro u hu
    have he : ∀ a ∈ S, (R u).val a = 0 := fun a ha =>
      congrFun (LinearMap.mem_ker.mp hu) (⟨a, ha⟩ : S)
    have hz : R u = 0 := Subtype.ext (hsep u he)
    exact LinearMap.mem_ker.mpr (by rw [LinearMap.comp_apply, hz, map_zero])

private theorem stage_inclusion_eval (i : BruhatCompactTestIndex (IdeleClass F))
    (u : i.Space) (g : IdeleClass F) :
    (i.inclusion u).val.val g = i.1.realize u.val g :=
  rfl

private theorem finite_pullback_stage_eval (v : Place) (i : BruhatCompactTestIndex (IdeleClass F))
    (u : i.Space) (x : (LocalField F v)ˣ) :
    (bruhatFiniteWeilPullback F v (i.inclusion u)).val x =
      i.1.realize u.val (finitePlaceInsertion F v x) :=
  rfl

private theorem finiteLocal_evaluations_separate (v : Place)
    (C : Set (LocalField F v)ˣ) (H : Subgroup (IntegralUnitFamily F))
    (S : Finset (LocalField F v)ˣ)
    (hS : ∀ x ∈ C, ∃ y ∈ S, ∃ b : principalIntegralUnits F v,
      integralUnitFamilySingle F v b ∈ H ∧ y * b.val = x)
    (f : IdeleClass F → ℂ)
    (hf : ∀ g a, a ∈ H → f (g * integralUnitFamilyClass F a) = f g)
    (hz : ∀ x ∉ C, f (finitePlaceInsertion F v x) = 0)
    (hzero : ∀ x ∈ S, f (finitePlaceInsertion F v x) = 0) (x : (LocalField F v)ˣ) :
    f (finitePlaceInsertion F v x) = 0 := by
  by_cases hx : x ∈ C
  · obtain ⟨y, hy, b, hb, he⟩ := hS x hx
    let j := finitePlaceInsertion F v
    let a := integralUnitFamilySingle F v b
    have hj : j x = j y * integralUnitFamilyClass F a :=
      (congrArg j he.symm).trans
        ((map_mul j y b.val).trans (congrArg (j y * ·) (integralUnitFamilySingle_class F v b).symm))
    exact (congrArg f hj).trans ((hf (j y) a hb).trans (hzero y hy))
  · exact hz x hx

set_option maxHeartbeats 500000 in
private theorem stage_local_evaluations_separate (v : Place)
    (i : BruhatCompactTestIndex (IdeleClass F)) :
    ∃ S : Finset (LocalField F v)ˣ, ∀ u : i.Space,
      (∀ x ∈ S, i.1.realize u.val (finitePlaceInsertion F v x) = 0) →
      ∀ x, i.1.realize u.val (finitePlaceInsertion F v x) = 0 := by
  let hLevel := bruhatCompactTest_stage_finite_invariance F i
  let H := hLevel.choose
  have hInv := hLevel.choose_spec.2
  let j := finitePlaceInsertion F v
  let C := j ⁻¹' i.2.val
  have hC : IsCompact C := (finitePlaceInsertion_isProper F v).isCompact_preimage i.2.property
  let hCover := finitePlace_exists_coset_cover F v C hC H hLevel.choose_spec.1
  let S := hCover.choose
  refine ⟨S, fun u hu => finiteLocal_evaluations_separate F v C H S hCover.choose_spec
    (i.1.realize u.val) ?_ (fun x hx => u.property (j x) hx) hu⟩
  intro g a ha
  simpa only [stage_inclusion_eval] using hInv u g a ha

set_option maxHeartbeats 500000 in
private theorem finitePullbackLinear_stage_continuous
    (v : Place) (i : BruhatCompactTestIndex (IdeleClass F))
    (J : locallyConstantTests (LocalField F v)ˣ →ₗ[ℂ] ℂ) :
    Continuous (J.comp ((bruhatFiniteWeilPullback F v).comp i.inclusion)) := by
  let hValues := stage_local_evaluations_separate F v i
  let S := hValues.choose
  have hS := hValues.choose_spec
  apply continuous_of_finite_test_values _ J S
  · intro x
    change Continuous (fun u : i.Space => (bruhatFiniteWeilPullback F v (i.inclusion u)).val x)
    simp only [finite_pullback_stage_eval]
    exact (i.1.continuous_realize_eval (finitePlaceInsertion F v x)).comp continuous_subtype_val
  · intro u hu
    funext x
    change (bruhatFiniteWeilPullback F v (i.inclusion u)).val x = 0
    simp only [finite_pullback_stage_eval] at hu ⊢
    exact hS u hu x

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]

/-- Each normalized finite-place Weil term is a continuous linear functional
on compact idelic Bruhat tests. -/
def bruhatFiniteWeilTerm (v : Place) : StrongDual ℂ (BruhatCompactTest (IdeleClass F)) :=
  ⟨bruhatFiniteWeilLinear F μ v,
    (locallyConvexFinal_continuous_iff (fun i : BruhatCompactTestIndex (IdeleClass F) => i.inclusion)
      (bruhatFiniteWeilLinear F μ v)).mpr (fun i => finitePullbackLinear_stage_continuous F v i (finiteWeilLocalLinear F μ v))⟩

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
theorem bruhatFiniteWeilTerm_apply (v : Place) (f : BruhatCompactTest (IdeleClass F)) :
    bruhatFiniteWeilTerm F μ v f =
      finitePlaceIdelicWeilTerm F μ f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f) v :=
  bruhatFiniteWeilLinear_apply F μ v f

set_option maxHeartbeats 950000 in
omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
/-- The finite-place series converges unconditionally in the strong dual.
Its partial sums stabilize on each bounded family of compact tests. -/
theorem bruhatFiniteWeilTerm_hasSum :
    ∃ L : StrongDual ℂ (BruhatCompactTest (IdeleClass F)),
      HasSum (bruhatFiniteWeilTerm F μ) L ∧
      ∀ f, L f = ∑' v : Place, bruhatFiniteWeilTerm F μ v f := by
  let X := BruhatCompactTest (IdeleClass F)
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : CompleteSpace (StrongDual ℂ X) := bruhatCompactTest_strongDual_complete
  let B := {V : Set X | IsVonNBounded ℂ V}
  letI : T2Space (X →ᵤ[B] ℂ) := UniformOnFun.t2Space_of_covering sUnion_isVonNBounded_eq_univ
  let j : StrongDual ℂ X → (X →ᵤ[B] ℂ) := UniformOnFun.ofFun B ∘ DFunLike.coe
  have hj : IsUniformInducing j := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id ℂ) ℂ B
  let v := bruhatFiniteWeilTerm F μ
  let g (f : X) := ∑' w : Place, v w f
  have ht : Tendsto (fun s : Finset Place => j (∑ w ∈ s, v w)) atTop (𝓝 (UniformOnFun.ofFun B g)) := by
    apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
    intro V hV E hE
    filter_upwards [bruhatCompactTest_finiteWeil_partialSums_eventually_eq F μ V hV] with s hs f hf
    have he : (∑ w ∈ s, v w) f = g f := by
      rw [sum_apply]
      simpa only [v, g, bruhatFiniteWeilTerm_apply] using hs f hf
    change (g f, (∑ w ∈ s, v w) f) ∈ E
    rw [he]
    exact refl_mem_uniformity hE
  obtain ⟨L, hL⟩ := hj.isComplete_range.isClosed.mem_of_tendsto ht
    (Eventually.of_forall fun s => mem_range_self _)
  rw [← hL] at ht
  refine ⟨L, hj.isInducing.tendsto_nhds_iff.mpr ht, fun f => ?_⟩
  exact congrArg (fun J : X →ᵤ[B] ℂ => UniformOnFun.toFun B J f) hL

/-- At the prescribed local Haar normalizations the strong-dual limit
evaluates to the sum of canonical finite cutoffs minus the discriminant term. -/
theorem bruhatFiniteWeilTerm_tsum_apply_canonical
    (hμ : ∀ v : Place, μ v (finitePlaceIntegralUnits F v) =
      additiveHaarDifferent F v (v.adicCompletionIntegers F : Set (LocalField F v)))
    (f : BruhatCompactTest (IdeleClass F)) :
    (∑' v : Place, bruhatFiniteWeilTerm F μ v f) =
      (∑' v : Place, finiteWeilCanonicalPrincipalValue F v (μ v) (bruhatFiniteWeilPullback F v f)) -
        (Real.log ((discr F).natAbs : ℝ)) • f.val.val 1 := by
  simp only [bruhatFiniteWeilTerm_apply]
  exact (finitePlaceIdelicWeilTerm_tsum F μ hμ f.val.val f.property
    (bruhatCompactTest_locallyConstantAtFinite F f)).2.2

end
end Masullo
