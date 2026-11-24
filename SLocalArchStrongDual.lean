import SLocalArchSimultaneousInterpolation
import FinestReflexivity
import AbsoluteBasisDuality

open Filter Function IsDedekindDomain MeasureTheory Module NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev FiniteArrays (I : Type*) := I →₀ ℂ

set_option backward.isDefEq.respectTransparency false in
private def finsuppProductStrongDual (I : Type*) :
    letI : TopologicalSpace (FiniteArrays I) := finestLocallyConvexTopology _
    FiniteArrays I ≃L[ℂ] StrongDual ℂ (I → ℂ) := by
  letI : TopologicalSpace (FiniteArrays I) := finestLocallyConvexTopology _
  let W := finest_withSeminorms (FiniteArrays I)
  letI : IsTopologicalAddGroup (FiniteArrays I) := W.topologicalAddGroup
  letI : ContinuousSMul ℂ (FiniteArrays I) := W.continuousSMul
  let D := StrongDual ℂ (FiniteArrays I)
  letI : TopologicalSpace D :=
    ContinuousLinearMap.topologicalSpace (E := FiniteArrays I) (F := ℂ) (σ := RingHom.id ℂ)
  letI : IsTopologicalAddGroup D :=
    ContinuousLinearMap.topologicalAddGroup (E := FiniteArrays I) (F := ℂ) (σ := RingHom.id ℂ)
  letI : TopologicalSpace (StrongDual ℂ D) :=
    ContinuousLinearMap.topologicalSpace (E := D) (F := ℂ) (σ := RingHom.id ℂ)
  let b : Basis I ℂ (FiniteArrays I) := Finsupp.basisSingleOne
  let e : (I → ℂ) ≃L[ℂ] D := finest_strongDual_product b
  let d : FiniteArrays I ≃L[ℂ] StrongDual ℂ D := finest_strongBidual b
  let a : StrongDual ℂ D →L[ℂ] StrongDual ℂ (I → ℂ) :=
    ContinuousLinearMap.precomp (σ := RingHom.id ℂ) (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ)
      (E := I → ℂ) (F := D) ℂ e.toContinuousLinearMap
  let a' : StrongDual ℂ (I → ℂ) →L[ℂ] StrongDual ℂ D :=
    ContinuousLinearMap.precomp (σ := RingHom.id ℂ) (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ)
      (E := D) (F := I → ℂ) ℂ e.symm.toContinuousLinearMap
  let r : StrongDual ℂ D ≃L[ℂ] StrongDual ℂ (I → ℂ) :=
    { a.toLinearMap with
      invFun := a'
      left_inv := fun f ↦ ContinuousLinearMap.ext fun x ↦ congrArg f (e.apply_symm_apply x)
      right_inv := fun f ↦ ContinuousLinearMap.ext fun x ↦ congrArg f (e.symm_apply_apply x)
      continuous_toFun := a.continuous
      continuous_invFun := a'.continuous }
  exact d.trans r

set_option backward.isDefEq.respectTransparency false in
private theorem finsuppProductStrongDual_single (I : Type*) (i : I) (x : I → ℂ) :
    finsuppProductStrongDual I (Finsupp.single i 1) x = x i := by
  letI : TopologicalSpace (FiniteArrays I) := finestLocallyConvexTopology _
  let W := finest_withSeminorms (FiniteArrays I)
  letI : IsTopologicalAddGroup (FiniteArrays I) := W.topologicalAddGroup
  letI : ContinuousSMul ℂ (FiniteArrays I) := W.continuousSMul
  let b : Basis I ℂ (FiniteArrays I) := Finsupp.basisSingleOne
  change finest_strongBidual b (Finsupp.single i 1) (finest_strongDual_product b x) = _
  rw [finest_strongBidual_apply]
  change (b.constr ℂ x) (b i) = _
  exact b.constr_basis ℂ x i

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev L (v : S) := v.val.adicCompletion F
private abbrev K := SLocalThetaNormOne F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))
variable (ω : PontryaginDual (K F S))

private abbrev I := SLocalArchPoleIndex F S ω
private abbrev V := sLocalArchPolarImage F S ν ω
private abbrev Q := V F S ν ω ⧸ sLocalArchPolarKernel F S μ ν hν ω

/-- The strong dual is the algebraic sum of its Laurent coordinate lines,
with the finest locally convex topology on that sum. -/
def sLocalArchStrongDualEquivFinsupp :
    letI : TopologicalSpace (FiniteArrays (I F S ω)) := finestLocallyConvexTopology _
    FiniteArrays (I F S ω) ≃L[ℂ] StrongDual ℂ (Q F S μ ν hν ω) := by
  letI : TopologicalSpace (FiniteArrays (I F S ω)) := finestLocallyConvexTopology _
  exact (finsuppProductStrongDual (I F S ω)).trans
    ((sLocalArchPolarQuotient_equiv_coefficients F S μ ν hν ω).symm.arrowCongr
      (ContinuousLinearEquiv.refl ℂ ℂ))

/-- A unit vector in the direct sum acts by the corresponding Laurent
coefficient on a homogeneous principal-value class. -/
theorem sLocalArchStrongDualEquivFinsupp_single_mk
    (i : I F S ω) (v : V F S ν ω) :
    sLocalArchStrongDualEquivFinsupp F S μ ν hν ω (Finsupp.single i 1) (Submodule.Quotient.mk v) =
      sLocalArchLaurentCoeff F S μ ν hν ω i.val.1 i.val.2 v := by
  change finsuppProductStrongDual _ (Finsupp.single i 1)
    (sLocalArchPolarQuotient_equiv_coefficients F S μ ν hν ω (Submodule.Quotient.mk v)) = _
  rw [finsuppProductStrongDual_single]
  rfl

private theorem finsupp_hasSum_enumerated_single {J : Type*} (σ : ℕ ≃ J) (a : FiniteArrays J) :
    letI : TopologicalSpace (FiniteArrays J) := finestLocallyConvexTopology _
    HasSum (fun n ↦ a (σ n) • Finsupp.single (σ n) (1 : ℂ)) a := by
  letI : TopologicalSpace (FiniteArrays J) := finestLocallyConvexTopology _
  let T := a.support.image σ.symm
  have ht (n : ℕ) : n ∈ T ↔ σ n ∈ a.support := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨j, hj, he⟩ ↦ by rwa [← he, σ.apply_symm_apply],
      fun h ↦ ⟨σ n, h, σ.symm_apply_apply n⟩⟩
  have hz (n : ℕ) (hn : n ∉ T) : a (σ n) • Finsupp.single (σ n) (1 : ℂ) = 0 := by
    rw [Finsupp.notMem_support_iff.mp (fun h ↦ hn ((ht n).mpr h)), zero_smul]
  have he : ∑ n ∈ T, a (σ n) • Finsupp.single (σ n) (1 : ℂ) = a := by
    ext j
    have hs (n : ℕ) : (a (σ n) • Finsupp.single (σ n) (1 : ℂ)) j =
        if σ n = j then a (σ n) else 0 := by
      by_cases h : σ n = j <;> simp [h]
    rw [Finsupp.finsetSum_apply]
    by_cases h : j ∈ a.support
    · rw [Finset.sum_eq_single_of_mem (σ.symm j) ((ht _).mpr (by simpa using h))]
      · simp
      · intro n _ hn
        rw [hs, ite_eq_right (fun he ↦ hn (σ.injective (he.trans (σ.apply_symm_apply j).symm)))]
    · simp only [hs, Finsupp.notMem_support_iff.mp h]
      apply Finset.sum_eq_zero
      intro n _
      by_cases he : σ n = j <;> simp [he, Finsupp.notMem_support_iff.mp h]
  have hh : HasSum (fun n ↦ a (σ n) • Finsupp.single (σ n) (1 : ℂ))
      (∑ n ∈ T, a (σ n) • Finsupp.single (σ n) (1 : ℂ)) := hasSum_sum_of_ne_finset_zero hz
  rw [he] at hh
  exact hh

/-- Every enumeration of the admissible Laurent coordinates is a
Schauder basis of the strong dual of the archimedean quotient. -/
theorem sLocalArchStrongDual_hasSchauderBasis (σ : ℕ ≃ I F S ω) :
    ∃ (a : ℕ → StrongDual ℂ (Q F S μ ν hν ω))
      (d : ℕ → StrongDual ℂ (StrongDual ℂ (Q F S μ ν hν ω))),
      (∀ n (v : V F S ν ω), a n (Submodule.Quotient.mk v) =
        sLocalArchLaurentCoeff F S μ ν hν ω (σ n).val.1 (σ n).val.2 v) ∧
      IsSchauderBasis a d := by
  let E := FiniteArrays (I F S ω)
  letI : TopologicalSpace E := finestLocallyConvexTopology _
  let e := sLocalArchStrongDualEquivFinsupp F S μ ν hν ω
  let A (n : ℕ) := e (Finsupp.single (σ n) 1)
  let d (n : ℕ) : StrongDual ℂ (StrongDual ℂ (Q F S μ ν hν ω)) :=
    (⟨Finsupp.lapply (σ n), finest_linear_continuous (Finsupp.lapply (σ n))⟩ :
      E →L[ℂ] ℂ).comp e.symm.toContinuousLinearMap
  refine ⟨A, d, fun n v ↦ sLocalArchStrongDualEquivFinsupp_single_mk F S μ ν hν ω (σ n) v,
    ⟨?_, ?_⟩⟩
  · intro m n
    change (e.symm (e (Finsupp.single (σ n) 1))) (σ m) = _
    rw [e.symm_apply_apply]
    by_cases h : m = n <;> simp [σ.injective.eq_iff, h]
  · intro l
    have hs := (finsupp_hasSum_enumerated_single σ (e.symm l)).map
      e.toLinearEquiv.toAddMonoidHom e.continuous
    change HasSum (fun n ↦ e ((e.symm l) (σ n) • Finsupp.single (σ n) 1)) (e (e.symm l)) at hs
    have ht : HasSum (fun n ↦ d n l • A n) l := by
      change HasSum (fun n ↦ (e.symm l) (σ n) • e (Finsupp.single (σ n) 1)) l
      simpa only [map_smul, e.apply_symm_apply] using hs
    exact Tendsto.mono_left ht (SummationFilter.conditional ℕ).le_atTop

end

end Masullo
