import StrictLimitQuotients

open Function Set Topology UniformSpace

namespace Masullo

noncomputable section

/-- A closed subspace of a Fréchet space is Fréchet in its intrinsic topology. -/
theorem isFrechetTVS_closedSubmodule {A : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] (hA : IsFrechetTVS A) (S : Submodule ℂ A)
    (hS : IsClosed (S : Set A)) : IsFrechetTVS S := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hA
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := hcomplete
  letI : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace S := hS.isComplete.completeSpace_coe
  refine ⟨inferInstance, inferInstance, IsEmbedding.subtypeVal.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- A Fréchet space embedded by a linear map into a Hausdorff topological
additive group has closed image. -/
theorem IsFrechetTVS.isClosedEmbedding {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B]
    (hA : IsFrechetTVS A) (f : A →L[ℂ] B) (hf : IsEmbedding f) :
    IsClosedEmbedding f := by
  obtain ⟨hadd, _, _, hcomplete⟩ := hA
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := hcomplete
  exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := f) hf).isClosedEmbedding

namespace LinearInductivePresentation

universe u v w
variable {E : Type u} {X : ℕ → Type v} {Y : ℕ → Type w}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
variable [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]
variable (D : LinearInductivePresentation E X) (F : Submodule ℂ E)
variable (Dq : LinearInductivePresentation (E ⧸ F) Y)

abbrev adaptedQuotientStage (a : ℕ → ℕ) (n : ℕ) : Submodule ℂ (X (a (2*n+1))) :=
  (Dq.incl (a (2*n))).toLinearMap.range.comap (F.mkQ.comp (D.incl (a (2*n+1))).toLinearMap)

/-- Realization of a synchronized stage in the original ambient space. -/
def adaptedQuotientInclusion (a : ℕ → ℕ) (n : ℕ) :
    D.adaptedQuotientStage F Dq a n →L[ℂ] E :=
  (D.incl (a (2*n+1))).comp (D.adaptedQuotientStage F Dq a n).subtypeL

omit [ContinuousSMul ℂ E] in
/-- Cofinal verification of the stage topologies of a strict quotient. The new
ambient stages are closed subspaces of original stages and map onto the
selected quotient stages. Each original stage maps into a new stage. -/
theorem quotient_adaptedStages
    (hF : IsClosed (F : Set E))
    (hX : ∀ n, IsFrechetTVS (X n)) (hY : ∀ n, IsFrechetTVS (Y n))
    (hEmbQ : ∀ n, IsEmbedding (Dq.incl n)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      (∀ n, IsClosed (D.adaptedQuotientStage F Dq a n : Set (X (a (2*n+1))))) ∧
      (∀ n, F.mkQ '' range (D.adaptedQuotientInclusion F Dq a n) =
        range (Dq.incl (a (2*n)))) ∧
      (∀ n, range (D.incl n) ⊆ range (D.adaptedQuotientInclusion F Dq a (n+1))) := by
  obtain ⟨a, ha, hUpper, hLower⟩ := D.quotient_interleaving F hF Dq hX hY
  let K := D.adaptedQuotientStage F Dq a
  letI : IsClosed (F : Set E) := hF
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · intro n
    exact ((hY _).isClosedEmbedding _ (hEmbQ _)).isClosed_range.preimage
      (F.mkQL.comp (D.incl _)).continuous
  · intro n
    apply subset_antisymm
    · rintro y ⟨z, ⟨x, rfl⟩, rfl⟩
      exact x.property
    · intro y hy
      obtain ⟨z, ⟨x, rfl⟩, hx⟩ := hLower (2*n) hy
      have hxK : x ∈ K n := by
        change F.mkQ (D.incl (a (2*n+1)) x) ∈ range (Dq.incl (a (2*n)))
        rwa [hx]
      exact ⟨D.incl _ x, ⟨⟨x, hxK⟩, rfl⟩, hx⟩
  · intro n x hx
    have hn₀ : n ≤ a (2*n+1) := (by omega : n ≤ 2*n+1).trans ha.le_apply
    have hn : n ≤ a (2*(n+1)+1) := hn₀.trans (ha.monotone (by omega))
    obtain ⟨z, hz⟩ := hx
    have hzImage : F.mkQ x ∈ range (Dq.incl (a (2*(n+1)))) := by
      have hstep : 2*n+1+1 = 2*(n+1) := by omega
      rw [← hstep]
      exact hUpper (2*n+1) ⟨x, D.range_incl_mono hn₀ ⟨z, hz⟩, rfl⟩
    refine ⟨⟨D.transition hn z, ?_⟩, (D.incl_transition hn z).trans hz⟩
    change F.mkQ (D.incl (a (2*(n+1)+1)) (D.transition hn z)) ∈ range (Dq.incl (a (2*(n+1))))
    rw [D.incl_transition hn z, hz]
    exact hzImage

/-- The adapted stages form an increasing chain inside the ambient space. -/
def adaptedQuotientTransition (a : ℕ → ℕ) (ha : Monotone a) {m n : ℕ} (h : m ≤ n) :
    D.adaptedQuotientStage F Dq a m →L[ℂ] D.adaptedQuotientStage F Dq a n := by
  let hmn := ha (show 2*m+1 ≤ 2*n+1 by omega)
  refine ((D.transition hmn).comp (D.adaptedQuotientStage F Dq a m).subtypeL).codRestrict _ ?_
  intro x
  change F.mkQ (D.incl (a (2*n+1)) (D.transition hmn (x : X (a (2*m+1))))) ∈
    range (Dq.incl (a (2*n)))
  rw [D.incl_transition]
  exact Dq.range_incl_mono (ha (by omega)) x.property

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
@[simp] theorem adaptedQuotientInclusion_transition
    (a : ℕ → ℕ) (ha : Monotone a) {m n : ℕ} (h : m ≤ n)
    (x : D.adaptedQuotientStage F Dq a m) :
    D.adaptedQuotientInclusion F Dq a n (D.adaptedQuotientTransition F Dq a ha h x) =
      D.adaptedQuotientInclusion F Dq a m x :=
  D.incl_transition (ha (by omega)) x.val

end LinearInductivePresentation

end

end Masullo
