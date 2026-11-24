import AdelicSchwartzNuclear
import StrongDualBarrelled

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct SchwartzMap

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

/-- The finite adelic tests use the finest locally convex topology. -/
abbrev FiniteAdelicTest : Type u := locallyConstantTests (FinAdeles F)

local instance : T2Space (FinAdeles F) := T2Space.of_injective_continuous
  (f := fun a : FinAdeles F => (a : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F))
  DFunLike.coe_injective RestrictedProduct.continuous_coe

local instance : SecondCountableTopology (FinAdeles F) := finiteAdeles_secondCountable F

local instance : TopologicalSpace (FiniteAdelicTest F) := finestLocallyConvexTopology _
local instance : IsTopologicalAddGroup (FiniteAdelicTest F) :=
  (finest_withSeminorms _).topologicalAddGroup
local instance : ContinuousSMul ℂ (FiniteAdelicTest F) :=
  (finest_withSeminorms (FiniteAdelicTest F)).continuousSMul
local instance : T2Space (FiniteAdelicTest F) := finest_t2 _
local instance : PolynormableSpace ℂ (FiniteAdelicTest F) :=
  (finest_withSeminorms _).toPolynormableSpace

theorem finiteAdelicTest_nuclear : NuclearLocallyConvex.{u, u} (FiniteAdelicTest F) :=
  ⟨inferInstance, inferInstance, fun X => locallyConstantTests_nuclear (FinAdeles F) X⟩

theorem finiteAdelicTest_complete : @CompleteSpace (FiniteAdelicTest F) (finestUniformSpace _) :=
  finest_complete _

theorem finiteAdelicTest_barrelled : BarrelledSpace ℂ (FiniteAdelicTest F) :=
  finest_barrelled

theorem finiteAdelicTest_montel : MontelSpace ℂ (FiniteAdelicTest F) :=
  ⟨fun _ => finest_closed_bounded_isCompact⟩

theorem finiteAdelicTest_strongDual_nuclear :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (FiniteAdelicTest F)) := by
  refine ⟨inferInstance, strongDual_withBoundedSeminorms.toPolynormableSpace, ?_⟩
  intro X _ _ _ _ _
  exact locallyConstantTests_strongDual_nuclear (FinAdeles F) X

theorem finiteAdelicTest_strongDual_complete :
    CompleteSpace (StrongDual ℂ (FiniteAdelicTest F)) :=
  (locallyConstantTests_strongDual_frechet (FinAdeles F)).1

theorem finiteAdelicTest_strongDual_frechet :
    IsFrechetTVS (StrongDual ℂ (FiniteAdelicTest F)) := by
  let E := StrongDual ℂ (FiniteAdelicTest F)
  refine ⟨inferInstance, (finiteAdelicTest_strongDual_nuclear F).2.1,
    (locallyConstantTests_strongDual_frechet (FinAdeles F)).2, ?_⟩
  change @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)
  exact Eq.mpr (congrArg (@CompleteSpace E) (IsUniformAddGroup.rightUniformSpace_eq (G := E)))
    (finiteAdelicTest_strongDual_complete F)

theorem finiteAdelicTest_strongDual_montel :
    MontelSpace ℂ (StrongDual ℂ (FiniteAdelicTest F)) := by
  letI := finiteAdelicTest_strongDual_complete F
  exact ⟨fun _ hs hb => (nuclearLocallyConvex_totallyBounded
    (E := StrongDual ℂ (FiniteAdelicTest F)) (finiteAdelicTest_strongDual_nuclear F) hb).isCompact_of_isClosed hs⟩

theorem finiteAdelicTest_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (FiniteAdelicTest F)) :=
  isFrechetTVS_barrelled (finiteAdelicTest_strongDual_frechet F)

private theorem finiteDimensional_isFrechet {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [T2Space E] [PolynormableSpace ℂ E] : IsFrechetTVS E := by
  let e := (Module.finBasis ℂ E).equivFun.toContinuousLinearEquiv
  refine ⟨inferInstance, inferInstance, e.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have h : IsUniformInducing e.toLinearEquiv.toLinearMap.toAddMonoidHom :=
    AddMonoidHom.isUniformInducing_of_isInducing e.toHomeomorph.isInducing
  exact (h.completeSpace_congr e.surjective).mpr inferInstance

/-- The finite adelic tests have a strict nuclear Fréchet presentation by
finite-dimensional subspaces with the induced topology. -/
theorem finiteAdelicTest_exists_nuclearFrechetPresentation :
    ∃ P : ℕ → Submodule ℂ (FiniteAdelicTest F),
      Monotone P ∧ (∀ x : FiniteAdelicTest F, ∃ n, x ∈ P n) ∧
      (∀ n, IsFrechetTVS (P n) ∧ NuclearLocallyConvex.{u, u} (P n)) ∧
      (∀ n, IsClosedEmbedding ((P n).subtype : P n → FiniteAdelicTest F)) ∧
      (∀ (m n : ℕ) (_h : m ≤ n) (h' : P m ≤ P n),
        IsClosedEmbedding (Submodule.inclusion h' : P m → P n)) ∧
      locallyConvexFinalTopology (A := fun n : ℕ => ↥(P n)) (fun n => (P n).subtype) =
        finestLocallyConvexTopology (FiniteAdelicTest F) := by
  obtain ⟨P, hm, hex, hfd, hclosed, htrans, hfinal⟩ := locallyConstantTests_strictLF (FinAdeles F)
  refine ⟨P, hm, hex, fun n => ?_, fun n => ?_, htrans, hfinal⟩
  · letI := hfd n
    let hN := nuclearLocallyConvex_submodule (finiteAdelicTest_nuclear F) (P n)
    letI := hN.2.1
    exact ⟨finiteDimensional_isFrechet, hN⟩
  · refine ⟨(hclosed n).2, ?_⟩
    have he : range ((P n).subtype : P n → FiniteAdelicTest F) = (P n : Set _) := by
      ext x
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [he]
    exact (hclosed n).1

/-- The global adelic tests are a strict locally convex inductive limit of
nuclear Fréchet spaces. -/
theorem globalBruhat_exists_nuclearFrechetPresentation :
    ∃ (I : Type u) (P : ℕ → Finset I)
      (D : LinearInductivePresentation (GlobalBruhat F) (fun n => P n → Arch F)),
      (∀ n, IsFrechetTVS (P n → Arch F) ∧ NuclearLocallyConvex.{u, u} (P n → Arch F)) ∧
      (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (GlobalBruhat F),
        (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p) := by
  obtain ⟨I, P, D, hFr, hEmb, hTrans, hFinal⟩ := globalBruhat_exists_frechetPresentation F
  exact ⟨I, P, D, fun n => ⟨hFr n, nuclearLocallyConvex_pi
    (fun _ : P n => archimedeanSchwartz_nuclear F)⟩, hEmb, hTrans, hFinal⟩

theorem globalBruhat_nuclear : NuclearLocallyConvex.{u, u} (GlobalBruhat F) := by
  obtain ⟨_, _, D, hN, _, _, hFinal⟩ := globalBruhat_exists_nuclearFrechetPresentation F
  exact D.nuclear_of_stages (fun n => (hN n).2) hFinal

theorem globalBruhat_barrelled : BarrelledSpace ℂ (GlobalBruhat F) := by
  obtain ⟨_, _, D, hFr, _, _, hFinal⟩ := globalBruhat_exists_frechetPresentation F
  exact barrelled_of_frechet_final D.incl hFr hFinal

theorem globalBruhat_montel : MontelSpace ℂ (GlobalBruhat F) := by
  letI : UniformSpace (GlobalBruhat F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (GlobalBruhat F) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (GlobalBruhat F) := globalBruhat_complete F
  exact ⟨fun _ hs hb => (nuclearLocallyConvex_totallyBounded
    (globalBruhat_nuclear F) hb).isCompact_of_isClosed hs⟩

theorem globalBruhat_strongDual_complete : CompleteSpace (StrongDual ℂ (GlobalBruhat F)) := by
  let j (ψ : FiniteBruhat F) : Arch F →L[ℂ] GlobalBruhat F :=
    ⟨GlobalBruhat.pure F ψ, GlobalBruhat.pure_continuous F ψ⟩
  exact strongDual_complete_of_sequentialSlices j fun l =>
    GlobalBruhat.continuous_of_pure F (norm_withSeminorms ℂ ℂ) l

theorem globalBruhat_strongDual_nuclear :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (GlobalBruhat F)) := by
  obtain ⟨I, P, D, hFr, hEmb, hTrans, hFinal⟩ := globalBruhat_exists_frechetPresentation F
  apply strongDual_nuclear_of_strictFrechet D hFr hEmb hTrans hFinal
  intro n
  change NuclearLocallyConvex.{u, u} (StrongDual ℂ (P n → Arch F))
  exact strongDual_nuclear_pi_finite (fun _ => archimedeanSchwartz_strongDual_nuclear F)

theorem globalBruhat_strongDual_montel :
    MontelSpace ℂ (StrongDual ℂ (GlobalBruhat F)) := by
  letI := globalBruhat_strongDual_complete F
  exact ⟨fun _ hs hb => (nuclearLocallyConvex_totallyBounded
    (E := StrongDual ℂ (GlobalBruhat F)) (globalBruhat_strongDual_nuclear F) hb).isCompact_of_isClosed hs⟩

set_option maxSynthPendingDepth 8 in
theorem globalBruhat_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (GlobalBruhat F)) := by
  let E := GlobalBruhat F
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace E := globalBruhat_complete F
  letI : BarrelledSpace ℂ E := globalBruhat_barrelled F
  letI : TopologicalSpace (StrongDual ℂ E) := ContinuousLinearMap.topologicalSpace
  letI : IsTopologicalAddGroup (StrongDual ℂ E) := ContinuousLinearMap.topologicalAddGroup
  apply strongDual_barrelled_of_bidually_surjective
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (E := E) (globalBruhat_nuclear F)
  intro f
  obtain ⟨x, hx⟩ := e.surjective f
  exact ⟨x, ContinuousLinearMap.ext fun l => (he x l).symm.trans (DFunLike.congr_fun hx l)⟩

end
end Masullo
