import AdelicSchwartzNuclear
import StrongDualBarrelled
import SLocalBruhatFiniteTensor

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

variable (S : Finset (Place F))

/-- Proposition 2.1.4.1(2). The S-local stages are nuclear Fréchet spaces,
with closed embeddings and the locally convex inductive limit topology. -/
theorem sLocalBruhat_exists_nuclearFrechetPresentation :
    ∃ (I : Type u) (P : ℕ → Finset I)
      (D : LinearInductivePresentation (Test F S) (fun n ↦ P n → Arch F)),
      (∀ n, IsFrechetTVS (P n → Arch F)) ∧
      (∀ n, NuclearLocallyConvex.{u, u} (P n → Arch F)) ∧
      (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (Test F S), (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) := by
  obtain ⟨I, P, D, hFr, hEmb, hTrans, hFinal⟩ := sLocalBruhat_exists_frechetPresentation F S
  exact ⟨I, P, D, hFr,
    (fun n ↦ nuclearLocallyConvex_pi (fun _ : P n ↦ archimedeanSchwartz_nuclear F)),
    hEmb, hTrans, hFinal⟩

theorem sLocalBruhat_barrelled : BarrelledSpace ℂ (Test F S) := by
  obtain ⟨_, _, D, hFr, _, _, hFinal⟩ := sLocalBruhat_exists_frechetPresentation F S
  exact barrelled_of_frechet_final D.incl hFr hFinal

set_option maxSynthPendingDepth 8 in
/-- Barrelledness of the strong dual completes the classical Montel property. -/
theorem sLocalBruhat_strongDual_barrelled : BarrelledSpace ℂ (StrongDual ℂ (Test F S)) := by
  let W := PolynormableSpace.withSeminorms ℂ (Test F S)
  letI : ContinuousSMul ℂ (Test F S) := W.continuousSMul
  letI : UniformSpace (Test F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Test F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Test F S) := sLocalBruhat_complete F S
  letI : T2Space (Test F S) := (sLocalBruhat_nuclear F S).1
  letI : BarrelledSpace ℂ (Test F S) := sLocalBruhat_barrelled F S
  letI : TopologicalSpace (StrongDual ℂ (Test F S)) := ContinuousLinearMap.topologicalSpace
  letI : IsTopologicalAddGroup (StrongDual ℂ (Test F S)) := ContinuousLinearMap.topologicalAddGroup
  apply strongDual_barrelled_of_bidually_surjective
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (E := Test F S) (sLocalBruhat_nuclear F S)
  intro f
  obtain ⟨x, hx⟩ := e.surjective f
  exact ⟨x, ContinuousLinearMap.ext fun l ↦ (he x l).symm.trans (DFunLike.congr_fun hx l)⟩

/-- Proposition 2.1.4.1(5). The global space has the universal mapping
property of the locally convex inductive limit of the S-local spaces. -/
theorem globalBruhat_existsUnique_lift
    {R : Type*} [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]
    (L : ∀ S : Finset (Place F), Test F S →L[ℂ] R)
    (hL : ∀ (S T : Finset (Place F)) (h : S ⊆ T) (x : Test F S),
      L T (sLocalBruhatTransition F h x) = L S x) :
    ∃! A : GlobalBruhat F →L[ℂ] R, ∀ (S : Finset (Place F)) (x : Test F S),
      A (sLocalBruhatInclusion F S x) = L S x := by
  let j := sLocalBruhatInclusion F
  choose stage repr hrepr using globalBruhat_exhausted F
  let a (x : GlobalBruhat F) := L (stage x) (repr x)
  have ha (S : Finset (Place F)) (x : Test F S) : a (j S x) = L S x := by
    let T := stage (j S x)
    let U := T ∪ S
    have hTU : T ⊆ U := Finset.subset_union_left
    have hSU : S ⊆ U := Finset.subset_union_right
    have he : sLocalBruhatTransition F hTU (repr (j S x)) = sLocalBruhatTransition F hSU x :=
      Subtype.ext (hrepr (j S x))
    exact (hL T U hTU _).symm.trans ((congrArg (L U) he).trans (hL S U hSU _))
  let A : GlobalBruhat F →ₗ[ℂ] R :=
    { toFun := a
      map_add' := fun x y ↦ by
        let U := stage x ∪ stage y
        let x' := sLocalBruhatTransition F (T := U) Finset.subset_union_left (repr x)
        let y' := sLocalBruhatTransition F (T := U) Finset.subset_union_right (repr y)
        have hx : j U x' = x := hrepr x
        have hy : j U y' = y := hrepr y
        rw [← hx, ← hy, ← map_add, ha, ha, ha, map_add]
      map_smul' := fun c x ↦ by
        rw [← hrepr x, ← map_smul, ha, ha, RingHom.id_apply, map_smul] }
  have hc : Continuous[locallyConvexFinalTopology (fun S ↦ (j S).toLinearMap), inferInstance] A := by
    apply (locallyConvexFinal_continuous_iff _ A).mpr
    intro S
    change Continuous (fun x : Test F S ↦ a (j S x))
    simp only [ha]
    exact (L S).continuous
  have hc' : Continuous A := by
    rw [globalBruhat_finalTopology F] at hc
    exact hc
  refine ⟨⟨A, hc'⟩, ha, ?_⟩
  intro B hB
  apply ContinuousLinearMap.ext
  intro x
  rw [← hrepr x, hB]
  exact (ha _ _).symm

end
end Masullo
