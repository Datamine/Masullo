import AdelicBruhatTensor
import SchwartzComplete
import StrictLimitCompleteness
import StrictLimitQuotients

open Function IsDedekindDomain NumberField Set Topology UniformSpace
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev FinTest (S : Finset (Place F)) :=
  locallyConstantTests ((w : S) → w.val.adicCompletion F)

local instance bruhatFrechetFiniteTestTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (locallyConstantTests X) := finestLocallyConvexTopology _

local instance bruhatFrechetTensorTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (Arch F ⊗[ℂ] locallyConstantTests X) := inductiveTensorTopology _ _

local instance : PolynormableSpace ℂ (Arch F) :=
  (schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).toPolynormableSpace

private def basisPrefix {I : Type*} (j : I ↪ ℕ) (n : ℕ) : Finset I :=
  ((finite_lt_nat n).preimage j.injective.injOn).toFinset

@[simp] private theorem mem_prefix {I : Type*} (j : I ↪ ℕ) (n : ℕ) (i : I) :
    i ∈ basisPrefix j n ↔ j i < n := Set.Finite.mem_toFinset _

private theorem prefix_mono {I : Type*} (j : I ↪ ℕ) : Monotone (basisPrefix j) :=
  fun _m _n h _ hi ↦ (mem_prefix j _ _).mpr (((mem_prefix j _ _).mp hi).trans_le h)

section BasisPresentation

variable {X W : Type u} [TopologicalSpace X] [TopologicalSpace W]
  [AddCommGroup W] [Module ℂ W] [IsTopologicalAddGroup W] [T2Space W]
  (e : (Arch F ⊗[ℂ] locallyConstantTests X) ≃L[ℂ] W)
  {I : Type*} (b : Module.Basis I ℂ (locallyConstantTests X))

private def coeffs : W ≃ₗ[ℂ] (I →₀ Arch F) :=
  e.symm.toLinearEquiv.trans (TensorProduct.equivFinsuppOfBasisRight b)

omit [IsTopologicalAddGroup W] [T2Space W] in
private theorem coeffs_pure (i : I) (φ : Arch F) (ψ : locallyConstantTests X) :
    coeffs F e b (e (φ ⊗ₜ[ℂ] ψ)) i = b.repr ψ i • φ := by
  change TensorProduct.equivFinsuppOfBasisRight b (e.symm (e (φ ⊗ₜ[ℂ] ψ))) i = _
  rw [ContinuousLinearEquiv.symm_apply_apply, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]

private def coeff (i : I) : W →L[ℂ] Arch F := by
  let L := (Finsupp.lapply i).comp (coeffs F e b).toLinearMap
  let M := L.comp e.toLinearEquiv.toLinearMap
  let B : Type u := locallyConstantTests X
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  have h : Continuous M := (continuous_inductiveTensor_iff M).mpr
    ⟨fun ψ => by
      change Continuous (fun φ ↦ coeffs F e b (e (φ ⊗ₜ[ℂ] ψ)) i)
      simp_rw [coeffs_pure]
      exact continuous_const_smul _,
    fun φ => finest_linear_continuous (TensorProduct.curry M φ)⟩
  refine ⟨L, (h.comp e.symm.continuous).congr fun x => ?_⟩
  change L (e (e.symm x)) = L x
  rw [e.apply_symm_apply]

private def pureSlice (ψ : locallyConstantTests X) : Arch F →L[ℂ] W :=
  ⟨e.toLinearEquiv.toLinearMap.comp ((TensorProduct.mk ℂ (Arch F) _).flip ψ),
    e.continuous.comp (continuous_inductiveTensor_tmul_left ψ)⟩

omit [IsTopologicalAddGroup W] [T2Space W] in
@[simp] private theorem pureSlice_apply (ψ : locallyConstantTests X) (φ : Arch F) :
    pureSlice F e ψ φ = e (φ ⊗ₜ[ℂ] ψ) := rfl

private abbrev Stage (s : Finset I) := s → Arch F

private def stageInclusion (s : Finset I) : Stage F s →L[ℂ] W :=
  ∑ i : s, (pureSlice F e (b i.val)).comp (ContinuousLinearMap.proj i)

omit [T2Space W] in
private theorem stageInclusion_coeff (s : Finset I) (x : Stage F s) (i : I) :
    coeffs F e b (stageInclusion F e b s x) i = if h : i ∈ s then x ⟨i, h⟩ else 0 := by
  classical
  simp only [stageInclusion, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, pureSlice_apply,
    map_sum, Finsupp.finsetSum_apply, coeffs_pure, b.repr_self, Finsupp.single_apply]
  by_cases h : i ∈ s
  · rw [dite_eq_left h, Finset.sum_eq_single (⟨i, h⟩ : s)]
    · simp
    · intro a _ ha
      have hn : a.val ≠ i := fun e ↦ ha (Subtype.ext e)
      simp [hn]
    · simp
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    have hn : a.val ≠ i := fun e ↦ h (e ▸ a.property)
    simp [hn]

private def stageProjection (s : Finset I) : W →L[ℂ] Stage F s :=
  ContinuousLinearMap.pi fun i ↦ coeff F e b i.val

omit [T2Space W] in
private theorem stageProjection_leftInverse (s : Finset I) :
    LeftInverse (stageProjection F e b s) (stageInclusion F e b s) := by
  intro x
  funext i
  change coeffs F e b (stageInclusion F e b s x) i.val = x i
  rw [stageInclusion_coeff, dite_eq_left i.property]

private theorem stageInclusion_closed (s : Finset I) :
    IsClosedEmbedding (stageInclusion F e b s) := by
  let incl := stageInclusion F e b s
  let proj := stageProjection F e b s
  have h := stageProjection_leftInverse F e b s
  refine ⟨h.isEmbedding proj.continuous incl.continuous, ?_⟩
  have he : range incl = {f | incl (proj f) = f} := by
    ext f
    refine ⟨?_, fun hf ↦ ⟨proj f, hf⟩⟩
    rintro ⟨x, rfl⟩
    exact congrArg incl (h x)
  rw [he]
  exact isClosed_eq (incl.continuous.comp proj.continuous) continuous_id

omit [T2Space W] in
private theorem stageInclusion_covers {s : Finset I} {f : W}
    (h : (coeffs F e b f).support ⊆ s) :
    stageInclusion F e b s (stageProjection F e b s f) = f := by
  apply (coeffs F e b).injective
  apply Finsupp.ext
  intro i
  rw [stageInclusion_coeff]
  by_cases hi : i ∈ s
  · rw [dite_eq_left hi]
    rfl
  · rw [dite_eq_right hi, Finsupp.notMem_support_iff.mp fun hc ↦ hi (h hc)]

private def stageTransition {s t : Finset I} (_h : s ⊆ t) : Stage F s →L[ℂ] Stage F t :=
  ContinuousLinearMap.pi fun i ↦ if hi : i.val ∈ s then ContinuousLinearMap.proj (⟨i.val, hi⟩ : s) else 0

omit [T2Space W] in
private theorem stageTransition_compatible {s t : Finset I} (h : s ⊆ t) (x : Stage F s) :
    stageInclusion F e b t (stageTransition F h x) = stageInclusion F e b s x := by
  apply (coeffs F e b).injective
  apply Finsupp.ext
  intro i
  simp only [stageInclusion_coeff]
  by_cases ht : i ∈ t
  · rw [dite_eq_left ht]
    change ((if hi : i ∈ s then ContinuousLinearMap.proj (⟨i, hi⟩ : s) else 0 :
      Stage F s →L[ℂ] Arch F) x) = _
    split_ifs <;> rfl
  · rw [dite_eq_right ht, dite_eq_right (fun hs ↦ ht (h hs))]

private theorem prefix_exhaust (j : I ↪ ℕ) (t : Finset I) :
    ∃ n, t ⊆ basisPrefix j n :=
  ⟨t.sup j + 1, fun i hi ↦ (mem_prefix j _ i).mpr ((Finset.le_sup hi).trans_lt (Nat.lt_succ_self _))⟩

omit [T2Space W] in
private theorem continuous_of_basis_stages {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] [PolynormableSpace ℂ Y] (j : I ↪ ℕ)
    (L : W →ₗ[ℂ] Y)
    (hL : ∀ n, Continuous (L.comp (stageInclusion F e b (basisPrefix j n)).toLinearMap)) :
    Continuous L := by
  let M := L.comp e.toLinearEquiv.toLinearMap
  let B : Type u := locallyConstantTests X
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  suffices hM : Continuous M by
    refine (hM.comp e.symm.continuous).congr fun x => ?_
    change L (e (e.symm x)) = L x
    rw [e.apply_symm_apply]
  refine (continuous_inductiveTensor_iff M).mpr
    ⟨fun ψ => ?_, fun φ => finest_linear_continuous (TensorProduct.curry M φ)⟩
  obtain ⟨n, hn⟩ := prefix_exhaust j (b.repr ψ).support
  have he (φ : Arch F) :
      stageInclusion F e b (basisPrefix j n) (stageProjection F e b (basisPrefix j n) (pureSlice F e ψ φ)) =
        pureSlice F e ψ φ := by
    apply stageInclusion_covers F e b
    intro i hi
    apply hn
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi) (by
      change coeffs F e b (e (φ ⊗ₜ[ℂ] ψ)) i = 0
      rw [coeffs_pure, Finsupp.notMem_support_iff.mp h, zero_smul])
  change Continuous (fun φ ↦ L (pureSlice F e ψ φ))
  rw [show (fun φ ↦ L (pureSlice F e ψ φ)) = fun φ ↦
    L (stageInclusion F e b (basisPrefix j n) (stageProjection F e b (basisPrefix j n) (pureSlice F e ψ φ)))
    from funext fun φ ↦ congrArg L (he φ).symm]
  exact (hL n).comp ((stageProjection F e b (basisPrefix j n)).continuous.comp
    (pureSlice F e ψ).continuous)

private def basisPresentation (j : I ↪ ℕ) :
    LinearInductivePresentation W (fun n ↦ Stage F (basisPrefix j n)) where
  incl n := stageInclusion F e b (basisPrefix j n)
  transition h := stageTransition F (prefix_mono j h)
  injective_incl n := (stageProjection_leftInverse F e b (basisPrefix j n)).injective
  incl_transition h x := stageTransition_compatible F e b (prefix_mono j h) x
  exhaust f := by
    obtain ⟨n, hn⟩ := prefix_exhaust j (coeffs F e b f).support
    exact ⟨n, stageProjection F e b (basisPrefix j n) f, stageInclusion_covers F e b hn⟩
  continuous_limit L :=
    ⟨fun h n ↦ h.comp (stageInclusion F e b (basisPrefix j n)).continuous,
      continuous_of_basis_stages F e b j L⟩

private theorem stage_isFrechet (s : Finset I) : IsFrechetTVS (Stage F s) := by
  letI : CompleteSpace (Arch F) := completeSpace_schwartzMap
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · letI : TopologicalSpace.MetrizableSpace (Arch F) := by
      have : (uniformity (Arch F)).IsCountablyGenerated := by
        rw [uniformity_eq_comap_nhds_zero (Arch F)]
        infer_instance
      exact UniformSpace.metrizableSpace
    infer_instance
  · rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance

omit [T2Space W] in
private theorem seminorm_continuous_of_basis_stages (j : I ↪ ℕ) (p : Seminorm ℂ W)
    (hp : ∀ n, Continuous (p.comp (stageInclusion F e b (basisPrefix j n)).toLinearMap)) :
    Continuous p := by
  let L := localBanachDenseMap p
  have hL : Continuous L := by
    apply continuous_of_basis_stages F e b j
    intro n
    apply (norm_withSeminorms ℂ (LocalBanach p)).continuous_of_continuous_comp
    intro _
    convert hp n using 1
    exact funext fun x ↦ norm_localBanachDenseMap p (stageInclusion F e b (basisPrefix j n) x)
  simpa only [L, norm_localBanachDenseMap] using hL.norm

include e in
/-- An archimedean Schwartz factor tensored with locally constant tests
on a second-countable space has a strict presentation by finite Schwartz products. -/
private theorem tensor_exists_frechetPresentation [T2Space X] [SecondCountableTopology X] :
    ∃ (I : Type u) (P : ℕ → Finset I)
      (D : LinearInductivePresentation W (fun n ↦ Stage F (P n))),
      (∀ n, IsFrechetTVS (Stage F (P n))) ∧ (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ W, (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) := by
  obtain ⟨J, hJ, ⟨a⟩⟩ := locallyConstantTests_countable_basis X
  letI : Countable J := hJ.to_subtype
  obtain ⟨j, hj⟩ := exists_injective_nat J
  let count : J ↪ ℕ := ⟨j, hj⟩
  let D := basisPresentation F e a count
  have h (n : ℕ) : IsClosedEmbedding (D.incl n) := stageInclusion_closed F e a (basisPrefix count n)
  refine ⟨J, basisPrefix count, D, (fun n ↦ stage_isFrechet F (basisPrefix count n)), h,
    (fun n ↦ ?_), seminorm_continuous_of_basis_stages F e a count⟩
  apply (h (n+1)).of_comp_iff.mp
  have he : (D.incl (n+1)) ∘ (D.transition (Nat.le_succ n)) = D.incl n :=
    funext (D.incl_transition (Nat.le_succ n))
  rw [he]
  exact h n


end BasisPresentation

variable (S : Finset (Place F))

/-- Each S-local Schwartz–Bruhat test space is a strict locally convex limit
of finite products of the archimedean Schwartz space. -/
theorem sLocalBruhat_exists_frechetPresentation :
    ∃ (I : Type u) (P : ℕ → Finset I)
      (D : LinearInductivePresentation (Test F S) (fun n ↦ Stage F (P n))),
      (∀ n, IsFrechetTVS (Stage F (P n))) ∧ (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (Test F S), (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) := by
  letI := (finiteProducts_locallyConstantTests_context F S).1.1
  letI := (finiteProducts_locallyConstantTests_context F S).1.2
  exact tensor_exists_frechetPresentation F (sLocalBruhatTensorEquiv F S)

/-- The global test space is a strict locally convex limit of finite products
of the archimedean Schwartz space. -/
theorem globalBruhat_exists_frechetPresentation :
    ∃ (I : Type u) (P : ℕ → Finset I)
      (D : LinearInductivePresentation (GlobalBruhat F) (fun n ↦ Stage F (P n))),
      (∀ n, IsFrechetTVS (Stage F (P n))) ∧ (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (GlobalBruhat F), (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) := by
  letI : T2Space (FiniteAdeleRing (𝓞 F) F) := T2Space.of_injective_continuous
    (f := fun a : FiniteAdeleRing (𝓞 F) F => (a : (v : Place F) → v.adicCompletion F))
    DFunLike.coe_injective RestrictedProduct.continuous_coe
  letI := finiteAdeles_secondCountable F
  exact tensor_exists_frechetPresentation F (globalBruhatTensorEquiv F)

/-- The actual S-local test space is complete in the additive uniformity
of its Schwartz–Bruhat topology. -/
theorem sLocalBruhat_complete :
    @CompleteSpace (Test F S) (IsTopologicalAddGroup.rightUniformSpace (Test F S)) := by
  obtain ⟨_, _, D, hFr, hEmb, _, hFinal⟩ := sLocalBruhat_exists_frechetPresentation F S
  exact D.complete_of_strict (fun n ↦ (hFr n).choose_spec.2.2)
    (fun n ↦ (hEmb n).isEmbedding) hFinal

/-- The global Schwartz–Bruhat test space is complete for its additive uniformity. -/
theorem globalBruhat_complete :
    @CompleteSpace (GlobalBruhat F) (IsTopologicalAddGroup.rightUniformSpace (GlobalBruhat F)) := by
  obtain ⟨S, D, hEmb, hFinal⟩ := globalBruhat_exists_cofinalPresentation F
  exact D.complete_of_strict (fun n ↦ sLocalBruhat_complete F (S n)) hEmb hFinal


/-- The stage with no finite places is itself Fréchet, since its finite
coordinate space is a single point. -/
theorem archStageBruhat_isFrechet : IsFrechetTVS (Test F ∅) := by
  let X := (w : (∅ : Finset (Place F))) → w.val.adicCompletion F
  let x₀ : X := 0
  have hx (x : X) : x = x₀ := by
    funext w
    exact (Finset.notMem_empty _ w.property).elim
  letI : CompactSpace X := by
    refine ⟨?_⟩
    have hu : (univ : Set X) = {x₀} := by ext x; simp [hx x]
    rw [hu]
    exact isCompact_singleton
  let ev : FinTest F ∅ →ₗ[ℂ] ℂ := (LinearMap.proj x₀).comp (FinTest F ∅).subtype
  let e : FinTest F ∅ ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective ev (by
    refine ⟨?_, ?_⟩
    · intro f g h
      apply Subtype.ext
      funext x
      rw [hx x]
      exact h
    · intro c
      exact ⟨⟨fun _ ↦ c, IsLocallyConstant.const c, HasCompactSupport.of_compactSpace _⟩, rfl⟩)
  let b : Module.Basis Unit ℂ (FinTest F ∅) := (Module.Basis.singleton Unit ℂ).map e.symm
  let s : Finset Unit := Finset.univ
  let E := sLocalBruhatTensorEquiv F ∅
  let j := stageInclusion F E b s
  let P := stageProjection F E b s
  have hL := stageProjection_leftInverse F E b s
  have hR : RightInverse P j :=
    fun f ↦ stageInclusion_covers F E b (Finset.subset_univ (coeffs F E b f).support)
  let Q : Stage F s ≃L[ℂ] Test F ∅ :=
    { toLinearEquiv := LinearEquiv.ofLinear j.toLinearMap P.toLinearMap
        (LinearMap.ext hR) (LinearMap.ext hL)
      continuous_toFun := j.continuous
      continuous_invFun := P.continuous }
  obtain ⟨hadd, hpoly, hmet, hcomplete⟩ := stage_isFrechet F s
  letI := hmet
  letI : UniformSpace (Stage F s) := IsTopologicalAddGroup.rightUniformSpace _
  letI : UniformSpace (Test F ∅) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Stage F s) := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup (Test F ∅) := isUniformAddGroup_of_addCommGroup
  have hU : IsUniformInducing Q.toLinearEquiv.toLinearMap.toAddMonoidHom :=
    AddMonoidHom.isUniformInducing_of_isInducing Q.toHomeomorph.isInducing
  exact ⟨inferInstance, inferInstance, Q.symm.toHomeomorph.isEmbedding.metrizableSpace,
    (hU.completeSpace_congr Q.surjective).mp hcomplete⟩

end

end Masullo
