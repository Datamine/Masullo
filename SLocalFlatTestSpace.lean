import ArchimedeanFlatMellin
import SLocalPrincipalValueImage
import SLocalThetaShellReduction
import InductiveTensorBasis
import InductiveTensorAssociativity
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Function IsDedekindDomain Module NumberField Set TensorProduct Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FiniteTests := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
private abbrev Test := sLocalBruhatImage F S
private abbrev Flat := archimedeanFlatTestSubspace F

private def flatArchSpan : Submodule ℂ (Test F S) :=
  Submodule.span ℂ {f | ∃ (a : Arch F) (ψ : FiniteTests F S),
    a ∈ Flat F ∧ sLocalBruhatPure F S a ψ = f}

private theorem mem_flatArchSpan (f : Test F S) :
    f ∈ flatArchSpan F S ↔ ∀ l : FiniteTests F S →ₗ[ℂ] ℂ,
      sLocalBruhatContractFinite F S l f ∈ Flat F := by
  constructor
  · intro hf l
    induction hf using Submodule.span_induction with
    | mem q g =>
      obtain ⟨a, ψ, ha, rfl⟩ := g
      rw [sLocalBruhatContractFinite_pure]
      exact (Flat F).smul_mem _ ha
    | zero => rw [map_zero]; exact (Flat F).zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact (Flat F).add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact (Flat F).smul_mem c ha
  · intro hf
    let b := Module.Free.chooseBasis ℂ (FiniteTests F S)
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    letI : TopologicalSpace (Arch F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
    let e := (sLocalBruhatTensorEquiv F S).toLinearEquiv
    let u : Arch F ⊗[ℂ] FiniteTests F S ≃ₗ[ℂ] _ := TensorProduct.equivFinsuppOfBasisRight b
    have he (a : Arch F) (ψ : FiniteTests F S) :
        e (a ⊗ₜ[ℂ] ψ) = sLocalBruhatPure F S a ψ :=
      TensorProduct.lift.tmul _ _
    have hcol (t : Arch F ⊗[ℂ] FiniteTests F S) (i : Module.Free.ChooseBasisIndex ℂ (FiniteTests F S)) :
        u t i = sLocalBruhatContractFinite F S (b.coord i) (e t) := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add t w ht hw => simp only [map_add, Finsupp.add_apply, ht, hw]
      | tmul a ψ =>
        rw [he, sLocalBruhatContractFinite_pure]
        exact TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b a ψ i
    let t := e.symm f
    let g := u t
    have hG (i : Module.Free.ChooseBasisIndex ℂ (FiniteTests F S)) : g i ∈ Flat F := by
      change u t i ∈ Flat F
      rw [hcol, show e t = f by exact e.apply_symm_apply f]
      exact hf (b.coord i)
    have hsum : f = ∑ i ∈ g.support, sLocalBruhatPure F S (g i) (b i) := by
      have h := congrArg e (TensorProduct.equivFinsuppOfBasisRight_symm_apply b g)
      change e (u.symm g) = e (∑ i ∈ g.support, g i ⊗ₜ[ℂ] b i) at h
      rw [map_sum] at h
      simp only [he] at h
      rw [← h]
      change f = e (u.symm (u (e.symm f)))
      simp
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ⟨g i, b i, hG i, rfl⟩

private theorem flatArchSpan_isClosed : IsClosed (flatArchSpan F S : Set (Test F S)) := by
  have he : (flatArchSpan F S : Set (Test F S)) =
      ⋂ l : FiniteTests F S →ₗ[ℂ] ℂ,
        (sLocalBruhatContractFinite F S l) ⁻¹' (Flat F : Set (Arch F)) := by
    ext f
    rw [Set.mem_iInter]
    exact mem_flatArchSpan F S f
  rw [he]
  exact isClosed_iInter fun l ↦
    (archimedeanFlatTestSubspace_isClosed F).preimage (sLocalBruhatContractFinite F S l).continuous

private def flatArchTensorEquiv :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    letI : TopologicalSpace (Flat F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
    (Flat F ⊗[ℂ] FiniteTests F S) ≃L[ℂ] flatArchSpan F S := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Flat F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
  letI : TopologicalSpace (Arch F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
  letI : PolynormableSpace ℂ (Arch F) :=
    (schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).toPolynormableSpace
  let e := sLocalBruhatTensorEquiv F S
  let T := TensorProduct.map (Flat F).subtype (LinearMap.id : FiniteTests F S →ₗ[ℂ] _)
  let L := e.toLinearEquiv.toLinearMap.comp T
  let b := Module.Free.chooseBasis ℂ (FiniteTests F S)
  have hT : IsEmbedding T := inductiveTensor_submodule_isEmbedding b (Flat F)
  have hL : IsEmbedding L := e.toHomeomorph.isEmbedding.comp hT
  have hPure (a : Flat F) (g : FiniteTests F S) : L (a ⊗ₜ[ℂ] g) = sLocalBruhatPure F S a.val g := by
    change e (T (a ⊗ₜ[ℂ] g)) = _
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    exact TensorProduct.lift.tmul _ _
  have hR : LinearMap.range L = flatArchSpan F S := by
    apply le_antisymm
    · rintro f ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul a g => rw [hPure]; exact Submodule.subset_span ⟨a.val, g, a.property, rfl⟩
      | add t w ht hw => rw [map_add]; exact Submodule.add_mem _ ht hw
    · apply Submodule.span_le.mpr
      rintro f ⟨a, g, ha, rfl⟩
      exact ⟨(⟨a, ha⟩ : Flat F) ⊗ₜ[ℂ] g, hPure ⟨a, ha⟩ g⟩
  let E := (LinearEquiv.ofInjective L hL.injective).trans (LinearEquiv.ofEq _ _ hR)
  have hE (t : Flat F ⊗[ℂ] FiniteTests F S) : (E t).val = L t := rfl
  refine ⟨E, hL.continuous.subtype_mk _, ?_⟩
  apply hL.isInducing.continuous_iff.mpr
  have hEq : (L : (Flat F ⊗[ℂ] FiniteTests F S) → Test F S) ∘ E.symm = Subtype.val := by
    funext f
    change L (E.symm f) = f.val
    rw [← hE, E.apply_symm_apply]
  change Continuous ((L : (Flat F ⊗[ℂ] FiniteTests F S) → Test F S) ∘ E.symm)
  rw [hEq]
  exact continuous_subtype_val

private theorem flatArchTensorEquiv_tmul (a : Flat F) (g : FiniteTests F S) :
    letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
    letI : TopologicalSpace (Flat F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
    (flatArchTensorEquiv F S (a ⊗ₜ[ℂ] g)).val = sLocalBruhatPure F S a.val g := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
  change sLocalBruhatTensorEquiv F S
      (TensorProduct.map (Flat F).subtype (LinearMap.id : FiniteTests F S →ₗ[ℂ] _)
        (a ⊗ₜ[ℂ] g)) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  exact TensorProduct.lift.tmul _ _

private def finiteNonzeroSpan : Submodule ℂ (FiniteTests F S) :=
  Submodule.span ℂ {ψ | ∃ g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F),
    (∀ v : S, (g v).val 0 = 0) ∧ locallyConstantTestPiProduct g = ψ}

/-- The polar-free Schwartz–Bruhat test space of (5.3.4.1) on the actual
S-local additive space. -/
def sLocalPolarFreeTestSubspace : Submodule ℂ (Test F S) :=
  Submodule.span ℂ {f | ∃ (a : Arch F) (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)),
    a ∈ Flat F ∧ (∀ v : S, (g v).val 0 = 0) ∧
    sLocalBruhatPure F S a (locallyConstantTestPiProduct g) = f}

private theorem pure_mem_polarFree (a : Arch F) (ha : a ∈ Flat F)
    (ψ : FiniteTests F S) (hψ : ψ ∈ finiteNonzeroSpan F S) :
    sLocalBruhatPure F S a ψ ∈ sLocalPolarFreeTestSubspace F S := by
  induction hψ using Submodule.span_induction with
  | mem ψ h =>
    obtain ⟨g, hg, rfl⟩ := h
    exact Submodule.subset_span ⟨a, g, ha, hg, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add ψ τ _ _ hp ht => rw [map_add]; exact Submodule.add_mem _ hp ht
  | smul z ψ _ hp => rw [map_smul]; exact Submodule.smul_mem _ z hp

theorem sLocalPolarFreeTestSubspace_eq_inf :
    sLocalPolarFreeTestSubspace F S =
      flatArchSpan F S ⊓ sLocalFiniteNonzeroTestSubspace F S Finset.univ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a, g, ha, hg, rfl⟩
    exact ⟨Submodule.subset_span ⟨a, _, ha, rfl⟩,
      Submodule.subset_span ⟨a, g, fun v _ ↦ hg v, rfl⟩⟩
  rintro f ⟨ha, hf⟩
  let B := finiteNonzeroSpan F S
  obtain ⟨B', hB'⟩ := B.exists_isCompl
  let π := B.projection B' hB'
  let P := sLocalBruhatFiniteMap F S π
  have hfix (x : Test F S) (hx : x ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ) : P x = x := by
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, g, hg, rfl⟩ := h
      change P (sLocalBruhatPure F S a (locallyConstantTestPiProduct g)) = _
      rw [show P = sLocalBruhatFiniteMap F S π from rfl, sLocalBruhatFiniteMap_pure]
      congr 1
      exact B.projection_apply_of_mem_left hB'
        (Submodule.subset_span ⟨g, fun v ↦ hg v (Finset.mem_univ v), rfl⟩)
    | zero => exact P.map_zero
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul z a _ ha => rw [map_smul, ha]
  have hmap (x : Test F S) (hx : x ∈ flatArchSpan F S) :
      P x ∈ sLocalPolarFreeTestSubspace F S := by
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ψ, hA, rfl⟩ := h
      rw [show P = sLocalBruhatFiniteMap F S π from rfl, sLocalBruhatFiniteMap_pure]
      exact pure_mem_polarFree F S a hA (π ψ) (B.projection_apply_mem hB' ψ)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul z a _ ha => rw [map_smul]; exact Submodule.smul_mem _ z ha
  rw [← hfix f hf]
  exact hmap f ha

/-- Requiring flatness in the Archimedean factor and zero extensions
in the finite factors gives a closed S-local test subspace. -/
theorem sLocalPolarFreeTestSubspace_isClosed :
    IsClosed (sLocalPolarFreeTestSubspace F S : Set (Test F S)) := by
  rw [sLocalPolarFreeTestSubspace_eq_inf, Submodule.coe_inf]
  exact (flatArchSpan_isClosed F S).inter (sLocalFiniteNonzeroTestSubspace_isClosed F S Finset.univ)

/-- Form a polar-free S-local test from one flat archimedean test and flat finite factors. -/
def sLocalPolarFreePure (a : Flat F)
    (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F)) (hg : ∀ v : S, (g v).val 0 = 0) :
    sLocalPolarFreeTestSubspace F S :=
  ⟨sLocalBruhatPure F S a.val (locallyConstantTestPiProduct g),
    Submodule.subset_span ⟨a.val, g, a.property, hg, rfl⟩⟩

/-- Induction over the pure generators of the bundled polar-free space. -/
theorem sLocalPolarFree_induction (p : sLocalPolarFreeTestSubspace F S → Prop)
    (hp : ∀ a g hg, p (sLocalPolarFreePure F S a g hg)) (hz : p 0)
    (ha : ∀ x y, p x → p y → p (x + y)) (hs : ∀ (c : ℂ) x, p x → p (c • x))
    (f : sLocalPolarFreeTestSubspace F S) : p f := by
  let P := sLocalPolarFreeTestSubspace F S
  suffices h : ∀ (x : Test F S) (hx : x ∈ P), p ⟨x, hx⟩ by exact h f.val f.property
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, g, ha₀, hg, rfl⟩ := h
    exact hp ⟨a, ha₀⟩ g hg
  | zero => exact hz
  | add x y hx hy hpx hpy => exact ha ⟨x, hx⟩ ⟨y, hy⟩ hpx hpy
  | smul c x hx hpx => exact hs c ⟨x, hx⟩ hpx

set_option maxHeartbeats 1000000 in
/-- A continuous linear automorphism of the jointly flat archimedean
factor lifts continuously to the S-local polar-free test space. The
finite factors stay fixed on every pure test. -/
theorem exists_sLocalPolarFree_archMulCLM (M : Flat F ≃L[ℂ] Flat F) :
    ∃ N : sLocalPolarFreeTestSubspace F S →L[ℂ] sLocalPolarFreeTestSubspace F S,
      ∀ (a : Flat F) (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F))
        (hg : ∀ v : S, (g v).val 0 = 0),
        N (sLocalPolarFreePure F S a g hg) = sLocalPolarFreePure F S (M a) g hg := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  letI : IsTopologicalAddGroup (FiniteTests F S) := (finest_withSeminorms _).topologicalAddGroup
  letI : TopologicalSpace (Flat F ⊗[ℂ] FiniteTests F S) := inductiveTensorTopology _ _
  let P := sLocalPolarFreeTestSubspace F S
  let X := flatArchSpan F S
  let e := flatArchTensorEquiv F S
  let T := inductiveTensor_rTensorEquiv (C := FiniteTests F S) M
  let L : X ≃L[ℂ] X := (e.symm.trans T).trans e
  have hle : P ≤ X := by
    change sLocalPolarFreeTestSubspace F S ≤ flatArchSpan F S
    rw [sLocalPolarFreeTestSubspace_eq_inf]
    exact inf_le_left
  let q : P →L[ℂ] X := ⟨Submodule.inclusion hle, continuous_subtype_val.subtype_mk _⟩
  let K := X.subtypeL.comp (L.toContinuousLinearMap.comp q)
  have hPure (a : Flat F) (g : ∀ v : S, locallyConstantTests (v.val.adicCompletion F))
      (hg : ∀ v : S, (g v).val 0 = 0) :
      K (sLocalPolarFreePure F S a g hg) = (sLocalPolarFreePure F S (M a) g hg).val := by
    have he : q (sLocalPolarFreePure F S a g hg) = e (a ⊗ₜ[ℂ] locallyConstantTestPiProduct g) := by
      apply Subtype.ext
      exact (flatArchTensorEquiv_tmul F S a _).symm
    change (L (q (sLocalPolarFreePure F S a g hg))).val = _
    rw [he]
    change (e (T (e.symm (e (a ⊗ₜ[ℂ] locallyConstantTestPiProduct g))))).val = _
    rw [e.symm_apply_apply]
    change (e ((M a) ⊗ₜ[ℂ] locallyConstantTestPiProduct g)).val = _
    exact flatArchTensorEquiv_tmul F S (M a) _
  have hK (f : P) : K f ∈ P := by
    induction f using sLocalPolarFree_induction F S with
    | hp a g hg =>
      rw [hPure]
      exact (sLocalPolarFreePure F S (M a) g hg).property
    | hz =>
      rw [map_zero]
      exact P.zero_mem
    | ha x y hx hy =>
      rw [map_add]
      exact P.add_mem hx hy
    | hs c x hx =>
      rw [map_smul]
      exact P.smul_mem c hx
  exact ⟨K.codRestrict P hK, fun a g hg ↦ Subtype.ext (hPure a g hg)⟩

private theorem sLocalArchPullback_mem_flat (u : (SAdeles F S)ˣ) {a : Arch F} (ha : a ∈ Flat F) :
    sLocalArchPullback F S u a ∈ Flat F := by
  unfold sLocalArchPullback
  dsimp only
  apply schwartzFlatSubspace_compCLM _ _ ha
  intro x hx
  rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨v, by change _ * x.1 v = 0; rw [hv, mul_zero]⟩
  · exact Or.inr ⟨v, by change _ * x.2 v = 0; rw [hv, mul_zero]⟩

/-- Multiplicative translation preserves archimedean flatness and the
zero-extension condition at every selected finite coordinate. -/
theorem sLocalBruhatLeftTranslate_mem_polarFree (u : (SAdeles F S)ˣ)
    {f : Test F S} (hf : f ∈ sLocalPolarFreeTestSubspace F S) :
    sLocalBruhatLeftTranslate F S u f ∈ sLocalPolarFreeTestSubspace F S := by
  induction hf using Submodule.span_induction with
  | mem q h =>
    obtain ⟨a, g, ha, hg, rfl⟩ := h
    rw [sLocalBruhatLeftTranslate_pure_piProduct]
    apply Submodule.subset_span
    refine ⟨sLocalArchPullback F S u a, sLocalFinitePiTranslate F S u g,
      sLocalArchPullback_mem_flat F S u ha, ?_, rfl⟩
    intro v
    change (g v).val (_ • (0 : v.val.adicCompletion F)) = 0
    rw [smul_zero, hg v]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul z a _ ha => rw [map_smul]; exact Submodule.smul_mem _ z ha

end

end Masullo
