/-
The example is motivated by original erratum F226. It uses coordinatewise
convergence and the constant sequence in place of the original normed example.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Topology.UniformSpace.Completion
import CompletedInductiveTensorPermanence

open Filter Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo.CompletionTail

noncomputable section

abbrev FiniteSequences := ℕ →₀ ℂ
abbrev ComplexSequences := ℕ → ℂ

/-- Transition maps discard initial coordinates of a finite sequence. -/
def finiteSequenceTail (m n : ℕ) (_ : m ≤ n) : FiniteSequences →ₗ[ℂ] FiniteSequences :=
  Finsupp.lcomapDomain (fun k : ℕ => k + (n - m)) (fun _ _ h => Nat.add_right_cancel h)

/-- The same transitions act on arbitrary sequences by shifting the indices. -/
def complexSequenceTail (m n : ℕ) (_ : m ≤ n) : ComplexSequences →ₗ[ℂ] ComplexSequences where
  toFun f k := f (k + (n - m))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : DirectedSystem (fun _ : ℕ => FiniteSequences)
    (finiteSequenceTail · · ·) where
  map_self {i} x := by
    ext k
    change x (k + (i - i)) = x k
    simp
  map_map {k j i} hij hjk x := by
    ext l
    change x (l + (k - j) + (j - i)) = x (l + (k - i))
    rw [show l + (k - j) + (j - i) = l + (k - i) by omega]

instance : DirectedSystem (fun _ : ℕ => ComplexSequences)
    (complexSequenceTail · · ·) where
  map_self {i} x := by
    funext k
    change x (k + (i - i)) = x k
    simp
  map_map {k j i} hij hjk x := by
    funext l
    change x (l + (k - j) + (j - i)) = x (l + (k - i))
    rw [show l + (k - j) + (j - i) = l + (k - i) by omega]

/-- Every finite sequence is eventually killed by a transition. -/
theorem finiteSequenceTail_limit_subsingleton :
    Subsingleton (Module.DirectLimit (fun _ : ℕ => FiniteSequences) finiteSequenceTail) := by
  let D := Module.DirectLimit (fun _ : ℕ => FiniteSequences) finiteSequenceTail
  have hz (x : D) : x = 0 := by
    obtain ⟨m, f, rfl⟩ := Module.DirectLimit.exists_of x
    let t := f.support.sup id + 1
    have hn : m ≤ m + t := Nat.le_add_right m t
    have he : finiteSequenceTail m (m + t) hn f = 0 := by
      ext k
      change f (k + (m + t - m)) = 0
      rw [Nat.add_sub_cancel_left]
      by_contra h
      have hs : k + t ∈ f.support := Finsupp.mem_support_iff.mpr h
      have hb : k + t ≤ f.support.sup id := Finset.le_sup (f := id) hs
      omega
    rw [← Module.DirectLimit.of_f (hij := hn), he, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The constant sequence survives all transitions, so its limit class is nonzero. -/
theorem complexSequenceTail_limit_class_ne_zero :
    Module.DirectLimit.of ℂ ℕ (fun _ => ComplexSequences) complexSequenceTail 0 (fun _ => 1) ≠ 0 := by
  intro h
  obtain ⟨n, hn, he⟩ := Module.DirectLimit.of.zero_exact h
  have hc := congrFun he 0
  exact one_ne_zero hc


/-- Finite sequences carry the topology of coordinatewise convergence. -/
abbrev finiteSequenceUniformSpace : UniformSpace FiniteSequences :=
  (inferInstance : UniformSpace ComplexSequences).comap
    (fun f : FiniteSequences => (f : ComplexSequences))

private theorem finiteSequence_denseRange :
    DenseRange (fun f : FiniteSequences => (f : ComplexSequences)) := by
  intro w
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨s, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
  let f : FiniteSequences :=
    Finsupp.onFinset s (fun k => if k ∈ s then w k else 0) (by
      intro k hk
      by_contra h
      exact hk (ite_eq_right h))
  refine ⟨f, hsub (fun k hk => ?_), f, rfl⟩
  change f k ∈ W k
  have hks : k ∈ s := hk
  have he : f k = w k := (Finsupp.onFinset_apply).trans (ite_eq_left hks)
  exact he.symm ▸ mem_of_mem_nhds (hW k)

/-- The separated completion of the finite sequences for this topology is
the full sequence product, with its natural inclusion on finite sequences. -/
def finiteSequenceCompletionEquiv :
    @Completion FiniteSequences finiteSequenceUniformSpace ≃ᵤ ComplexSequences := by
  letI := finiteSequenceUniformSpace
  let pkg : AbstractCompletion FiniteSequences :=
    { space := ComplexSequences
      coe := fun f => (f : ComplexSequences)
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := IsUniformInducing.mk (by rfl)
      dense := finiteSequence_denseRange }
  exact Completion.cPkg.compareEquiv pkg


theorem finiteSequenceCompletionEquiv_coe (f : FiniteSequences) :
    finiteSequenceCompletionEquiv (@Completion.coe' _ finiteSequenceUniformSpace f) =
      (f : ComplexSequences) := by
  letI := finiteSequenceUniformSpace
  unfold finiteSequenceCompletionEquiv
  apply AbstractCompletion.compare_coe

theorem finiteSequenceTail_uniformContinuous (m n : ℕ) (h : m ≤ n) :
    letI := finiteSequenceUniformSpace
    UniformContinuous (finiteSequenceTail m n h) := by
  letI := finiteSequenceUniformSpace
  let u : FiniteSequences → ComplexSequences := fun f => (f : ComplexSequences)
  have hu : IsUniformInducing u := IsUniformInducing.mk (by rfl)
  apply hu.uniformContinuous_iff.mpr
  have hc : UniformContinuous (complexSequenceTail m n h) :=
    Pi.uniformContinuous_precomp (fun k : ℕ => k + (n - m))
  exact hc.comp hu.uniformContinuous

/-- Completing the finite-sequence transition gives the same shift on the
whole product, including sequences of infinite support. -/
theorem finiteSequenceCompletionEquiv_tail (m n : ℕ) (h : m ≤ n)
    (x : @Completion FiniteSequences finiteSequenceUniformSpace) :
    letI := finiteSequenceUniformSpace
    finiteSequenceCompletionEquiv (Completion.map (finiteSequenceTail m n h) x) =
    complexSequenceTail m n h (finiteSequenceCompletionEquiv x) := by
  letI := finiteSequenceUniformSpace
  have hc : UniformContinuous (complexSequenceTail m n h) :=
    Pi.uniformContinuous_precomp (fun k : ℕ => k + (n - m))
  apply Completion.ext'
    (finiteSequenceCompletionEquiv.uniformContinuous_toFun.comp
      Completion.uniformContinuous_map).continuous
    (hc.comp finiteSequenceCompletionEquiv.uniformContinuous_toFun).continuous _ x
  intro f
  change finiteSequenceCompletionEquiv (Completion.map (finiteSequenceTail m n h) f) =
    complexSequenceTail m n h (finiteSequenceCompletionEquiv f)
  rw [Completion.map_coe (finiteSequenceTail_uniformContinuous m n h),
    finiteSequenceCompletionEquiv_coe, finiteSequenceCompletionEquiv_coe]
  rfl


/-- The constant sequence gives a nonzero completion point fixed by every
extended tail transition, despite the vanishing of the finite-sequence limit. -/
theorem finiteSequenceCompletionTail_survives :
    letI := finiteSequenceUniformSpace
    ∃ x : Completion FiniteSequences, x ≠ (Completion.coe' (0 : FiniteSequences)) ∧
      ∀ m n (h : m ≤ n), Completion.map (finiteSequenceTail m n h) x = x := by
  letI := finiteSequenceUniformSpace
  let e := finiteSequenceCompletionEquiv
  let x := e.symm (fun _ : ℕ => (1 : ℂ))
  have hx : e x = fun _ : ℕ => (1 : ℂ) := e.apply_symm_apply _
  refine ⟨x, ?_, ?_⟩
  · intro h
    have he : e x = (fun _ : ℕ => (0 : ℂ)) := by
      rw [h]
      exact finiteSequenceCompletionEquiv_coe _
    exact one_ne_zero (congrFun (hx.symm.trans he) 0)
  · intro m n h
    apply e.injective
    change finiteSequenceCompletionEquiv (Completion.map (finiteSequenceTail m n h) x) = e x
    rw [finiteSequenceCompletionEquiv_tail]
    change complexSequenceTail m n h (e x) = e x
    rw [hx]
    rfl


section ScalarTensor

local instance : UniformSpace FiniteSequences := finiteSequenceUniformSpace

private def finiteSequenceCoe : FiniteSequences →ₗ[ℂ] ComplexSequences where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem finiteSequenceCoe_uniformInducing : IsUniformInducing finiteSequenceCoe := ⟨rfl⟩

local instance : IsUniformAddGroup FiniteSequences :=
  finiteSequenceCoe_uniformInducing.isUniformAddGroup finiteSequenceCoe

local instance : T2Space FiniteSequences :=
  (show IsEmbedding finiteSequenceCoe from
    ⟨finiteSequenceCoe_uniformInducing.isInducing, fun _ _ h => Finsupp.ext (congrFun h)⟩).t2Space

local instance : PolynormableSpace ℂ FiniteSequences :=
  finiteSequenceCoe_uniformInducing.isInducing.polynormableSpace (f := finiteSequenceCoe)

local instance : ContinuousSMul ℂ FiniteSequences :=
  (PolynormableSpace.withSeminorms ℂ FiniteSequences).continuousSMul

/-- Each finite-sequence shift is continuous for coordinatewise convergence. -/
def finiteSequenceTailCLM (m n : ℕ) (h : m ≤ n) : FiniteSequences →L[ℂ] FiniteSequences :=
  ⟨finiteSequenceTail m n h, (finiteSequenceTail_uniformContinuous m n h).continuous⟩


private abbrev tailTensorStructure := inductiveTensorModuleStructure FiniteSequences ℂ

/-- The completed tensor transition, with the scalar factor unchanged. -/
def tailScalarTensorMap (m n : ℕ) (h : m ≤ n) : tailTensorStructure.Completed →L[ℂ] tailTensorStructure.Completed :=
  completedInductiveTensor_map (finiteSequenceTailCLM m n h) (ContinuousLinearMap.id ℂ ℂ)

theorem tailScalarTensorMap_comparison (m n : ℕ) (h : m ≤ n) (z : tailTensorStructure.Completed) :
    completedInductiveTensorScalarRightUnit FiniteSequences (tailScalarTensorMap m n h z) =
      Completion.map (finiteSequenceTail m n h)
        (completedInductiveTensorScalarRightUnit FiniteSequences z) := by
  let X := FiniteSequences ⊗[ℂ] ℂ
  letI : UniformSpace X := tailTensorStructure.uniformSpace
  let e := completedInductiveTensorScalarRightUnit FiniteSequences
  apply Completion.ext'
    (e.uniformContinuous_toFun.continuous.comp (tailScalarTensorMap m n h).continuous)
    (Completion.continuous_map.comp e.uniformContinuous_toFun.continuous) _ z
  intro t
  change e (tailScalarTensorMap m n h (tailTensorStructure.incl t)) =
    Completion.map (finiteSequenceTail m n h) (e (tailTensorStructure.incl t))
  let u := TensorProduct.rid ℂ FiniteSequences
  have ht : t = u t ⊗ₜ[ℂ] (1 : ℂ) := (u.symm_apply_apply t).symm
  set x := u t with hx
  rw [ht]
  change e ((completedInductiveTensor_map (finiteSequenceTailCLM m n h)
    (ContinuousLinearMap.id ℂ ℂ)) (tailTensorStructure.incl (x ⊗ₜ[ℂ] (1 : ℂ)))) =
    Completion.map (finiteSequenceTail m n h) (e (tailTensorStructure.incl (x ⊗ₜ[ℂ] (1 : ℂ))))
  rw [completedInductiveTensor_map_tmul]
  change completedInductiveTensorScalarRightUnit FiniteSequences
      (tailTensorStructure.incl (finiteSequenceTail m n h x ⊗ₜ[ℂ] (1 : ℂ))) =
    Completion.map (finiteSequenceTail m n h)
      (completedInductiveTensorScalarRightUnit FiniteSequences (tailTensorStructure.incl (x ⊗ₜ[ℂ] (1 : ℂ))))
  rw [completedInductiveTensorScalarRightUnit_incl, completedInductiveTensorScalarRightUnit_incl,
    TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, one_smul,
    Completion.map_coe (finiteSequenceTail_uniformContinuous m n h)]


abbrev tailScalarTensorTransition (m n : ℕ) (h : m ≤ n) :=
  (tailScalarTensorMap m n h).toLinearMap

private instance : DirectedSystem (fun _ : ℕ => tailTensorStructure.Completed)
    (tailScalarTensorTransition · · ·) where
  map_self {i} z := by
    change tailScalarTensorMap i i le_rfl z = z
    apply (completedInductiveTensorScalarRightUnit FiniteSequences).injective
    rw [tailScalarTensorMap_comparison]
    have h : (finiteSequenceTail i i le_rfl : FiniteSequences → FiniteSequences) = id :=
      funext (fun x => DirectedSystem.map_self' finiteSequenceTail (i := i) x)
    rw [h, Completion.map_id, id_eq]
  map_map {k j i} hij hjk z := by
    change tailScalarTensorMap j k hjk (tailScalarTensorMap i j hij z) =
      tailScalarTensorMap i k (hij.trans hjk) z
    apply (completedInductiveTensorScalarRightUnit FiniteSequences).injective
    rw [tailScalarTensorMap_comparison, tailScalarTensorMap_comparison, tailScalarTensorMap_comparison]
    have h : (finiteSequenceTail j k hjk : FiniteSequences → FiniteSequences) ∘ finiteSequenceTail i j hij =
        finiteSequenceTail i k (hij.trans hjk) :=
      funext (DirectedSystem.map_map' finiteSequenceTail hij hjk)
    let w := completedInductiveTensorScalarRightUnit FiniteSequences z
    change (Completion.map (finiteSequenceTail j k hjk) ∘ Completion.map (finiteSequenceTail i j hij)) w =
      Completion.map (finiteSequenceTail i k (hij.trans hjk)) w
    rw [Completion.map_comp (finiteSequenceTail_uniformContinuous j k hjk)
      (finiteSequenceTail_uniformContinuous i j hij), h]

/-- A nonzero vector in the first completed stage survives in the direct limit. -/
theorem tailScalarTensor_directLimit_nontrivial :
    ¬ Subsingleton (Module.DirectLimit (fun _ => tailTensorStructure.Completed) tailScalarTensorTransition) := by
  let X := FiniteSequences ⊗[ℂ] ℂ
  letI : UniformSpace X := tailTensorStructure.uniformSpace
  letI : IsUniformAddGroup X := tailTensorStructure.uniformGroup
  let e := completedInductiveTensorScalarRightUnit FiniteSequences
  obtain ⟨x, hx0, hx⟩ := finiteSequenceCompletionTail_survives
  let z := e.symm x
  have he : e z = x := e.apply_symm_apply _
  have hz0 : z ≠ 0 := by
    intro h
    apply hx0
    calc
      x = e z := he.symm
      _ = e (tailTensorStructure.incl 0) :=
        congrArg e (h.trans (show tailTensorStructure.incl 0 = 0 from
          Completion.coe_zero).symm)
      _ = Completion.coe' (0 : FiniteSequences) := by
        rw [completedInductiveTensorScalarRightUnit_incl, map_zero]
  have hz (n : ℕ) (hn : 0 ≤ n) : tailScalarTensorMap 0 n hn z = z := by
    apply e.injective
    rw [tailScalarTensorMap_comparison]
    change Completion.map (finiteSequenceTail 0 n hn) (e z) = e z
    rw [he]
    exact hx 0 n hn
  intro hs
  have h := hs.elim (Module.DirectLimit.of ℂ ℕ _ tailScalarTensorTransition 0 z) 0
  obtain ⟨n, hn, heq⟩ := Module.DirectLimit.of.zero_exact h
  exact hz0 ((hz n hn).symm.trans heq)


private abbrev TailLimit := Module.DirectLimit (fun _ : ℕ => FiniteSequences) finiteSequenceTail

local instance : AddCommGroup (TailLimit ⊗[ℂ] ℂ) :=
  TensorProduct.addCommGroup (R := ℂ) (M := TailLimit) (N := ℂ)

/-- With a singleton scalar second system, (C.2.3.27) has a nontrivial
source and a zero target in the tail-shift example. -/
theorem tailScalarTensor_directLimit_not_injective
    [TopologicalSpace TailLimit]
    (T : Module.DirectLimit (fun _ => tailTensorStructure.Completed) tailScalarTensorTransition →
      (inductiveTensorModuleStructure TailLimit ℂ).Completed) :
    ¬ Function.Injective T := by
  letI : Subsingleton TailLimit := finiteSequenceTail_limit_subsingleton
  let X := TailLimit ⊗[ℂ] ℂ
  let V := inductiveTensorModuleStructure TailLimit ℂ
  letI : UniformSpace X := V.uniformSpace
  have hzero (z : V.Completed) : z = V.incl 0 := by
    exact Completion.induction_on (p := fun w : V.Completed => w = V.incl 0) z
      (isClosed_eq continuous_id continuous_const)
      (fun w => congrArg V.incl (Subsingleton.elim w 0))
  intro hinj
  apply tailScalarTensor_directLimit_nontrivial
  exact ⟨fun x y => hinj ((hzero (T x)).trans (hzero (T y)).symm)⟩

end ScalarTensor

end
end Masullo.CompletionTail
