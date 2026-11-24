import ModulatedDecaySplitTensor
import ModulatedDecayAngularSummability
import PointwiseLinearSeries
import InjectiveTensorMaps
import CompletedProjectiveTensorMaps

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

/-- Absolute summability of all products of continuous factor seminorms
gives convergence of the corresponding series of elementary tensors. -/
theorem completedProjectiveTensor_summable_of_factorSeminorms
    {A R ι : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] (a : ι → A) (r : ι → R)
    (h : ∀ (p : Seminorm ℂ A) (q : Seminorm ℂ R), Continuous p → Continuous q →
      Summable (fun i => p (a i) * q (r i))) :
    Summable (fun i => (projectiveTensorModuleStructure A R).incl (a i ⊗ₜ[ℂ] r i)) := by
  classical
  let X := A ⊗[ℂ] R
  let D := projectiveTensorModuleStructure A R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : CompleteSpace (Completion X) := Completion.completeSpace X
  let t (i : ι) : X := a i ⊗ₜ[ℂ] r i
  change Summable (fun i => (Completion.toCompl (t i) : Completion X))
  apply summable_iff_cauchySeq_finset.mpr
  suffices ht : CauchySeq (fun u : Finset ι => ∑ i ∈ u, t i) by
    have hc := (Completion.uniformContinuous_coe X).comp_cauchySeq ht
    simpa only [Function.comp_def, map_sum] using
      (show CauchySeq (fun u : Finset ι => Completion.toCompl (∑ i ∈ u, t i)) from hc)
  refine cauchySeq_finset_iff_sum_vanishing.mpr fun U hU => ?_
  let W := projectiveTensor_withSeminorms (E := A) (F := R)
  obtain ⟨⟨J, ε⟩, hε, hJU⟩ := W.hasBasis_zero_ball.mem_iff.mp hU
  let p := ProjectiveTensorTest.tensor (E := A) (F := R)
  let b (j : ProjectiveTensorTest A R) (i : ι) := j.first (a i) * j.second (r i)
  have hb (j : ProjectiveTensorTest A R) (i : ι) : 0 ≤ b j i :=
    mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  let B (i : ι) := ∑ j ∈ J, b j i
  have hB : Summable B := by
    have hs (L : Finset (ProjectiveTensorTest A R)) :
        Summable (fun i => ∑ j ∈ L, b j i) := by
      induction L using Finset.induction_on with
      | empty => simp
      | @insert j L hj hL =>
        simp only [Finset.sum_insert hj]
        exact (h j.first j.second j.first_continuous j.second_continuous).add hL
    exact hs J
  obtain ⟨s, hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp (summable_iff_cauchySeq_finset.mp hB)
    (Iio ε) (Iio_mem_nhds hε)
  refine ⟨s, fun u hu => hJU ((J.sup p).mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hb j i)
  intro j hj
  calc
    p j (∑ i ∈ u, t i) ≤ ∑ i ∈ u, p j (t i) :=
      Finset.le_sum_of_subadditive (p j) (map_zero _).le (map_add_le_add _) _ _
    _ ≤ ∑ i ∈ u, B i :=
      Finset.sum_le_sum fun i _ =>
        (j.bound (a i) (r i)).trans (Finset.single_le_sum (fun k _ => hb k i) hj)

private def tensorCompletionIncl
    {X : Type*} [AddCommGroup X] [Module ℂ X] (D : TopologicalModuleStructure X) :
    letI : UniformSpace X := D.uniformSpace
    X →L[ℂ] D.Completed := by
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  exact ⟨{ toFun := D.incl
           map_add' := fun x y => Completion.coe_add x y
           map_smul' := fun c x => Completion.coe_smul c x }, Completion.continuous_coe X⟩

section Insertion

variable {A R : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
  [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup R]

/-- Inserting a fixed first factor is continuous in the completed projective tensor space. -/
def completedProjectiveTensor_insertLeft (a : A) :
    R →L[ℂ] (projectiveTensorModuleStructure A R).Completed := by
  letI : TopologicalSpace (A ⊗[ℂ] R) := projectiveTensorTopology A R
  exact (tensorCompletionIncl (projectiveTensorModuleStructure A R)).comp
    ⟨TensorProduct.mk ℂ A R a,
      (continuous_projectiveTensor_tmul (E := A) (F := R)).comp (continuous_const.prodMk continuous_id)⟩

/-- Inserting a fixed second factor is continuous in the completed projective tensor space. -/
def completedProjectiveTensor_insertRight (r : R) :
    A →L[ℂ] (projectiveTensorModuleStructure A R).Completed := by
  letI : TopologicalSpace (A ⊗[ℂ] R) := projectiveTensorTopology A R
  exact (tensorCompletionIncl (projectiveTensorModuleStructure A R)).comp
    ⟨(TensorProduct.mk ℂ A R).flip r,
      (continuous_projectiveTensor_tmul (E := A) (F := R)).comp (continuous_id.prodMk continuous_const)⟩

@[simp]
theorem completedProjectiveTensor_insertLeft_apply (a : A) (r : R) :
    completedProjectiveTensor_insertLeft a r =
      (projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r) := rfl

@[simp]
theorem completedProjectiveTensor_insertRight_apply (a : A) (r : R) :
    completedProjectiveTensor_insertRight r a =
      (projectiveTensorModuleStructure A R).incl (a ⊗ₜ[ℂ] r) := rfl

end Insertion

/-- A synthesis map is a left inverse on the completed tensors if on each
elementary tensor it sums the angular reconstruction with the radial factor fixed. -/
theorem completedProjectiveTensor_leftInverse_of_angularSeries
    {A R Y Ω : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup R]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (F : (projectiveTensorModuleStructure A R).Completed →L[ℂ] Y)
    (S : Y →L[ℂ] (projectiveTensorModuleStructure A R).Completed)
    (a : Ω → A) (c : A → Ω → ℂ)
    (hA : ∀ x, HasSum (fun θ => c x θ • a θ) x)
    (hSF : ∀ x y, HasSum (fun θ =>
        (projectiveTensorModuleStructure A R).incl (a θ ⊗ₜ[ℂ] (c x θ • y)))
      (S (F ((projectiveTensorModuleStructure A R).incl (x ⊗ₜ[ℂ] y))))) :
    S.comp F = ContinuousLinearMap.id ℂ _ := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : T0Space D.Completed := Completion.t0Space X
  apply completedProjectiveTensor_ext
  intro x y
  change S (F (D.incl (x ⊗ₜ[ℂ] y))) = D.incl (x ⊗ₜ[ℂ] y)
  have hs : HasSum (fun θ => D.incl (a θ ⊗ₜ[ℂ] (c x θ • y))) (D.incl (x ⊗ₜ[ℂ] y)) := by
    refine ((hA x).mapL (completedProjectiveTensor_insertRight y)).congr_fun fun θ => ?_
    rw [completedProjectiveTensor_insertRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact (hSF x y).unique hs

/-- A summable series of rank-one maps from a barrelled space has continuous
linear synthesis in the completed projective tensor product. -/
theorem exists_completedProjectiveTensor_synthesis
    {A R Y Ω : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddCommGroup R] [Module ℂ R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y]
    [IsUniformAddGroup Y] [ContinuousSMul ℂ Y] [BarrelledSpace ℂ Y]
    (a : Ω → A) (L : Ω → Y →L[ℂ] R)
    (hs : ∀ y, Summable (fun θ =>
      (projectiveTensorModuleStructure A R).incl (a θ ⊗ₜ[ℂ] L θ y))) :
    ∃ S : Y →L[ℂ] (projectiveTensorModuleStructure A R).Completed,
      ∀ y, HasSum (fun θ =>
        (projectiveTensorModuleStructure A R).incl (a θ ⊗ₜ[ℂ] L θ y)) (S y) := by
  let D := projectiveTensorModuleStructure A R
  let X := A ⊗[ℂ] R
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := projectiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : T0Space D.Completed := Completion.t0Space X
  letI : PolynormableSpace ℂ D.Completed := polynormableSpace_completion
  letI : ContinuousSMul ℂ D.Completed := (PolynormableSpace.withSeminorms ℂ D.Completed).continuousSMul
  exact exists_continuousLinearMap_hasSum_pointwise
    (fun θ => (completedProjectiveTensor_insertLeft (a θ)).comp (L θ)) hs


variable {d n r : ℕ} {T : Type*} [AddCommGroup T] [TopologicalSpace T] [DiscreteTopology T] [Finite T]
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure]

local notation "K" => m.toMonoidHom.ker
local notation "A" => ElementaryLCAModel d n r T
local notation "E" => ElementarySchwartz d n r T

/-- One angular Fourier term in the completed projective tensor product. -/
def completed_splitAngularFourierTerm [CompactSpace A]
    (φ : K →ₜ* Multiplicative A) (hm : IsProperMap m)
    (I : Set ℝ) (hI : I.Nonempty) (f : ModulatedExponentialInductive m I)
    (θ : PontryaginDual (Multiplicative A)) :
    (projectiveTensorModuleStructure E (PositiveRealExponentialDecay I)).Completed :=
  (projectiveTensorModuleStructure E (PositiveRealExponentialDecay I)).incl
    (compactElementaryInverseCharacterTest θ ⊗ₜ[ℂ]
      modulatedDecayAngularCoefficient m τ hτ ν (θ.comp φ) I hI hm f)

/-- The angular Fourier tensors converge in the completed projective tensor product
of an elementary angular stage and the radial decay space. -/
theorem summable_completed_splitAngularFourier [LocallyCompactSpace K] [CompactSpace A]
    (φ : K →ₜ* Multiplicative A) (hφ : Surjective φ) (hm : IsProperMap m)
    (I : Set ℝ) (hI : I.Nonempty) (f : ModulatedExponentialInductive m I) :
    Summable (completed_splitAngularFourierTerm m τ hτ ν φ hm I hI f) := by
  obtain ⟨hd, hr⟩ := elementaryLCAModel_compact_dimensions (m := d) (n := n) (r := r) (F := T)
  subst d
  subst r
  exact completedProjectiveTensor_summable_of_factorSeminorms compactElementaryInverseCharacterTest _
    (summable_splitAngularCoefficient_factorSeminorms m τ hτ ν φ hφ hm I hI f)

include hτ in
set_option maxHeartbeats 2500000 in
/-- The Fourier tensor series defines a continuous linear synthesis map on
any barrelled space of decay tests. -/
theorem exists_completed_splitAngularFourierSynthesis
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [ContinuousSMul ℂ Y] [BarrelledSpace ℂ Y]
    [LocallyCompactSpace K] [CompactSpace A] (φ : K →ₜ* Multiplicative A) (hφ : Surjective φ)
    (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty)
    (s : Y →L[ℂ] ModulatedExponentialInductive m I) :
    ∃ L : Y →L[ℂ] (projectiveTensorModuleStructure E (PositiveRealExponentialDecay I)).Completed,
      ∀ f, HasSum (completed_splitAngularFourierTerm m τ hτ ν φ hm I hI (s f)) (L f) := by
  exact exists_completedProjectiveTensor_synthesis
    (fun θ => compactElementaryInverseCharacterTest θ)
    (fun θ => (modulatedDecayAngularCoefficient m τ hτ ν (θ.comp φ) I hI hm).comp s)
    (fun f => summable_completed_splitAngularFourier m τ hτ ν φ hφ hm I hI (s f))

end

end Masullo
