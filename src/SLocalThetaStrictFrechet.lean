import SLocalThetaAngularProjection
import StrictLimitCompleteness
import Mathlib.Data.Nat.Pairing
import StrictInductiveTelescope
import NuclearApproximation
import ThetaStrongDualCompleteness
import Mathlib.Analysis.LocallyConvex.Montel

open Bornology Function IsDedekindDomain NumberField Set Topology UniformSpace
open scoped Classical ENNReal NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Theta (S : Finset (Place F)) := SLocalThetaQuotient F S

variable (S : Finset (Place F))
private abbrev B := locallyConstantTests ((w : S) → w.val.adicCompletion F)

private structure IntegralUnitLevel where
  groups (w : S) : Subgroup (w.val.adicCompletion F)ˣ
  isOpen (w : S) : IsOpen (groups w : Set (w.val.adicCompletion F)ˣ)
  norm_eq_one (w : S) (a : groups w) : ‖a.val.val‖ = 1

private def IntegralUnitLevel.inter (a b : IntegralUnitLevel F S) : IntegralUnitLevel F S :=
  ⟨fun w ↦ a.groups w ⊓ b.groups w, fun w ↦ (a.isOpen w).inter (b.isOpen w),
    fun w u ↦ a.norm_eq_one w ⟨u.val, u.property.1⟩⟩

private def IntegralUnitLevel.fixed (a : IntegralUnitLevel F S) : Submodule ℂ (B F S) where
  carrier := {ψ | ∀ w, thetaFiniteInvariantAt F S w (a.groups w) ψ}
  zero_mem' := fun _ _ _ _ ↦ rfl
  add_mem' {f g} hf hg := fun w u x z ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, hf w u x z, hg w u x z]
  smul_mem' c ψ hψ := fun w u x z ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, hψ w u x z]

private theorem level_fixed_anti {a b : IntegralUnitLevel F S}
    (h : a.groups ≤ b.groups) : b.fixed ≤ a.fixed :=
  fun _ hψ w u x z ↦ hψ w ⟨u.val, h w u.property⟩ x z

private theorem level_exhausts (ψ : B F S) :
    ∃ a : IntegralUnitLevel F S, ψ ∈ a.fixed := by
  obtain ⟨H, hH, hn, hψ⟩ := sLocalThetaFiniteTests_have_invariant_levels F S ψ
  exact ⟨⟨H, hH, hn⟩, hψ⟩

/-- There is a decreasing sequence of open integral-unit levels at which
every fixed finite test becomes invariant. -/
private theorem exists_countable_levels :
    ∃ a : ℕ → IntegralUnitLevel F S,
      Antitone (fun n ↦ (a n).groups) ∧ ∀ ψ : B F S, ∃ n, ψ ∈ (a n).fixed := by
  letI := (finiteProducts_locallyConstantTests_context F S).1.2
  obtain ⟨I, hI, ⟨b⟩⟩ := locallyConstantTests_countable_basis ((w : S) → w.val.adicCompletion F)
  letI : Countable I := hI.to_subtype
  obtain ⟨j, hj⟩ := exists_injective_nat I
  choose selected hselected using fun i : I ↦ level_exhausts F S (b i)
  obtain ⟨base, _⟩ := level_exhausts F S 0
  let next (n : ℕ) := if h : ∃ i, j i = n then selected h.choose else base
  have hnext (i : I) : next (j i) = selected i := by
    have hi : ∃ k, j k = j i := ⟨i, rfl⟩
    rw [show next (j i) = selected hi.choose by unfold next; rw [dite_eq_left hi],
      hj hi.choose_spec]
  let a (n : ℕ) : IntegralUnitLevel F S := Nat.rec base (fun n prev ↦ IntegralUnitLevel.inter F S prev (next n)) n
  have hAnti : Antitone (fun n ↦ (a n).groups) := by
    apply antitone_nat_of_succ_le
    intro n w
    exact inf_le_left
  refine ⟨a, hAnti, fun ψ ↦ ?_⟩
  let t := (b.repr ψ).support
  let N := t.sup j + 1
  have hN (i : I) (hi : i ∈ t) : (a N).groups ≤ (selected i).groups := by
    have hle : j i + 1 ≤ N := Nat.succ_le_succ (Finset.le_sup hi)
    have hm : (a (j i+1)).groups ≤ (next (j i)).groups := fun w ↦ inf_le_right
    rw [hnext i] at hm
    exact (hAnti hle).trans hm
  refine ⟨N, ?_⟩
  have hb : (∑ i ∈ t, b.repr ψ i • b i) = ψ := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, t] using b.linearCombination_repr ψ
  rw [← hb]
  exact (a N).fixed.sum_mem fun i hi ↦ (a N).fixed.smul_mem _
    (level_fixed_anti F S (hN i hi) (hselected i))

local instance strictThetaFiniteTopology : TopologicalSpace (B F S) := finestLocallyConvexTopology _
local instance strictThetaTensorTopology : TopologicalSpace (Arch F ⊗[ℂ] B F S) :=
  inductiveTensorTopology _ _

private def invariantStage (a : IntegralUnitLevel F S) : Submodule ℂ (Theta F S) :=
  sLocalThetaInvariantTestSpan F S a.groups

private theorem invariantStage_anti {a b : IntegralUnitLevel F S} (h : a.groups ≤ b.groups) :
    invariantStage F S b ≤ invariantStage F S a := sLocalThetaInvariantTestSpan_antitone F S h

private def thetaSliceBase (ψ : B F S) : Arch F →L[ℂ] Theta F S :=
  (sLocalThetaOperator F S).ker.mkQL.comp
    ⟨(sLocalBruhatPure F S).flip ψ, (GlobalBruhat.pure_continuous F _).subtype_mk _⟩

private theorem thetaSlice_mem {a : IntegralUnitLevel F S} {ψ : B F S}
    (hψ : ψ ∈ a.fixed) (φ : Arch F) : thetaSliceBase F S ψ φ ∈ invariantStage F S a :=
  Submodule.subset_span ⟨φ, ψ, hψ, rfl⟩

private theorem levels_exhaust_theta (a : ℕ → IntegralUnitLevel F S)
    (ha : Antitone (fun n ↦ (a n).groups)) (ht : ∀ ψ : B F S, ∃ n, ψ ∈ (a n).fixed)
    (q : Theta F S) : ∃ n, q ∈ invariantStage F S (a n) := by
  let e := sLocalBruhatTensorEquiv F S
  let K := (sLocalThetaOperator F S).ker
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective K q
  obtain ⟨t, rfl⟩ := e.surjective f
  let L := K.mkQ.comp e.toLinearEquiv.toLinearMap
  change ∃ n, L t ∈ invariantStage F S (a n)
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨max n m, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _
      (invariantStage_anti F S (ha (le_max_left n m)) hn)
      (invariantStage_anti F S (ha (le_max_right n m)) hm)
  | tmul φ ψ =>
    obtain ⟨n, hn⟩ := ht ψ
    exact ⟨n, thetaSlice_mem F S hn φ⟩

private theorem levels_final (a : ℕ → IntegralUnitLevel F S)
    (ht : ∀ ψ : B F S, ∃ n, ψ ∈ (a n).fixed)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (L : Theta F S →ₗ[ℂ] Y)
    (hL : ∀ n, Continuous (L.comp (invariantStage F S (a n)).subtype)) :
    Continuous L := by
  let K := (sLocalThetaOperator F S).ker
  apply K.isQuotientMap_mkQ.continuous_iff.mpr
  change Continuous (L.comp K.mkQ)
  apply continuous_sLocal_of_pure F S (PolynormableSpace.withSeminorms ℂ Y)
  intro ψ
  obtain ⟨n, hn⟩ := ht ψ
  let g := (thetaSliceBase F S ψ).codRestrict (invariantStage F S (a n)) (thetaSlice_mem F S hn)
  exact (hL n).comp g.continuous

private theorem levels_seminorm_final (a : ℕ → IntegralUnitLevel F S)
    (ht : ∀ ψ : B F S, ∃ n, ψ ∈ (a n).fixed) (p : Seminorm ℂ (Theta F S))
    (hp : ∀ n, Continuous (p.comp (invariantStage F S (a n)).subtype)) : Continuous p := by
  let L := localBanachDenseMap p
  have hL : Continuous L := by
    apply levels_final F S a ht
    intro n
    apply (norm_withSeminorms ℂ (LocalBanach p)).continuous_of_continuous_comp
    intro _
    convert hp n using 1
    exact funext (fun x ↦ norm_localBanachDenseMap p x.val)
  simpa only [L, norm_localBanachDenseMap] using hL.norm

/-- The countable system of angular fixed spaces has a cofinal union and
detects continuity of seminorms on the ordinary theta quotient. -/
theorem sLocalTheta_exists_angularStages :
    ∃ (H : ℕ → ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ),
      (∀ n w, IsOpen (H n w : Set (w.val.adicCompletion F)ˣ)) ∧
      (∀ n w (a : H n w), ‖a.val.val‖ = 1) ∧ Antitone H ∧
      (∀ q : Theta F S, ∃ n, q ∈ sLocalThetaInvariantTestSpan F S (H n)) ∧
      ∀ p : Seminorm ℂ (Theta F S),
        (∀ n, Continuous (p.comp (sLocalThetaInvariantTestSpan F S (H n)).subtype)) →
          Continuous p := by
  obtain ⟨a,ha,ht⟩ := exists_countable_levels F S
  exact ⟨fun n ↦ (a n).groups, fun n ↦ (a n).isOpen, fun n ↦ (a n).norm_eq_one, ha,
    levels_exhaust_theta F S a ha ht, levels_seminorm_final F S a ht⟩

/-- The actual S-local theta quotient is a countable strict locally convex
inductive limit of Fréchet spaces. -/
theorem sLocalTheta_exists_strictFrechet_with_lifts :
    ∃ (W : ℕ → Submodule ℂ (Theta F S))
      (D : LinearInductivePresentation (Theta F S) (fun n ↦ W n)),
      (∀ n, IsFrechetTVS (W n)) ∧ (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (Theta F S), (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) → ∀ n, NuclearLocallyConvex.{u, u} (W n)) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) →
        NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F)) →
        ∀ n, NuclearLocallyConvex.{u, u} (StrongDual ℂ (W n))) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) → ∀ n (B : Set (W n)), IsVonNBounded ℂ B →
        ∃ A : Set (Test F S), IsCompact A ∧ D.incl n '' B ⊆ (sLocalThetaOperator F S).ker.mkQL '' A) := by
  obtain ⟨a, ha, ht⟩ := exists_countable_levels F S
  let W (n : ℕ) := invariantStage F S (a n)
  have hm : Monotone W := fun _ _ h ↦ invariantStage_anti F S (ha h)
  letI : T2Space (Theta F S) := sLocalThetaQuotient_t2Space F S
  have hF (n : ℕ) : IsFrechetTVS (W n) :=
    sLocalThetaInvariantTestSpan_isFrechet F S (a n).groups (a n).isOpen (a n).norm_eq_one
  let D : LinearInductivePresentation (Theta F S) (fun n ↦ W n) :=
    { incl := fun n ↦ (W n).subtypeL
      transition := fun h ↦ ⟨Submodule.inclusion (hm h), continuous_subtype_val.subtype_mk _⟩
      injective_incl := fun _ ↦ Subtype.val_injective
      incl_transition := fun _ _ ↦ rfl
      exhaust := fun q ↦ by
        obtain ⟨n, hn⟩ := levels_exhaust_theta F S a ha ht q
        exact ⟨n, ⟨q, hn⟩, rfl⟩
      continuous_limit := fun L ↦ ⟨fun h n ↦ h.comp (W n).subtypeL.continuous, levels_final F S a ht L⟩ }
  have hClosed (n : ℕ) : IsClosedEmbedding (D.incl n) :=
    (hF n).isClosedEmbedding _ IsEmbedding.subtypeVal
  refine ⟨W, D, hF, hClosed, fun n ↦ ?_, levels_seminorm_final F S a ht,
    fun hN n ↦ sLocalThetaInvariantTestSpan_nuclear_of_arch F S (a n).groups
      (a n).isOpen (a n).norm_eq_one hN,
    fun hN hD n ↦ sLocalThetaInvariantTestSpan_strongDual_nuclear_of_arch F S (a n).groups
      (a n).isOpen (a n).norm_eq_one hN hD,
    fun hN n B hB ↦ sLocalThetaInvariantTestSpan_bounded_lift F S (a n).groups
      (a n).isOpen (a n).norm_eq_one hN B hB⟩
  apply (hClosed (n+1)).of_comp_iff.mp
  have he : D.incl (n+1) ∘ D.transition (Nat.le_succ n) = D.incl n :=
    funext (D.incl_transition (Nat.le_succ n))
  rw [he]
  exact hClosed n

theorem sLocalTheta_exists_strictFrechet :
    ∃ (W : ℕ → Submodule ℂ (Theta F S))
      (D : LinearInductivePresentation (Theta F S) (fun n ↦ W n)),
      (∀ n, IsFrechetTVS (W n)) ∧ (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (Theta F S), (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) → ∀ n, NuclearLocallyConvex.{u, u} (W n)) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) →
        NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F)) →
        ∀ n, NuclearLocallyConvex.{u, u} (StrongDual ℂ (W n))) := by
  obtain ⟨W, D, hF, hE, hT, hP, hN, hD, _⟩ := sLocalTheta_exists_strictFrechet_with_lifts F S
  exact ⟨W, D, hF, hE, hT, hP, hN, hD⟩

/-- The S-local theta quotient is complete for its additive uniformity. -/
theorem sLocalThetaQuotient_complete :
    @CompleteSpace (Theta F S) (IsTopologicalAddGroup.rightUniformSpace (Theta F S)) := by
  letI : PolynormableSpace ℂ (Theta F S) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  obtain ⟨W, D, hFr, hE, _, hFinal, _, _⟩ := sLocalTheta_exists_strictFrechet F S
  letI : ∀ n, IsTopologicalAddGroup (W n) := fun n ↦ (hFr n).choose
  exact D.complete_of_strict (fun n ↦ (hFr n).choose_spec.2.2)
    (fun n ↦ (hE n).isEmbedding) hFinal

private theorem exists_cofinal_place_sequence :
    ∃ S : ℕ → Finset (Place F), Monotone S ∧ ∀ A, ∃ n, A ⊆ S n := by
  letI := finitePlaces_countable F
  obtain ⟨e, he⟩ := exists_injective_nat (Place F)
  let finite (n : ℕ) : {v : Place F | e v < n}.Finite :=
    (finite_lt_nat n).preimage he.injOn
  let S (n : ℕ) := (finite n).toFinset
  refine ⟨S, ?_, ?_⟩
  · intro m n h v hv
    exact (finite n).mem_toFinset.mpr (((finite m).mem_toFinset.mp hv).trans_le h)
  · intro A
    refine ⟨A.sup e + 1, fun v hv ↦ (finite _).mem_toFinset.mpr ?_⟩
    exact (Finset.le_sup hv).trans_lt (Nat.lt_succ_self _)

/-- Seminorm continuity on a cofinal tower implies continuity on the global theta quotient. -/
theorem globalTheta_cofinal_seminorm_final {S : ℕ → Finset (Place F)}
    (hS : ∀ A, ∃ n, A ⊆ S n) (p : Seminorm ℂ (GlobalThetaQuotient F))
    (hp : ∀ n, Continuous (p.comp (sLocalThetaToGlobal F (S n)).toLinearMap)) :
    Continuous p := by
  let L := localBanachDenseMap p
  have hL : Continuous L := by
    apply globalThetaQuotient_continuous_of_cofinal F hS
    intro n
    apply (norm_withSeminorms ℂ (LocalBanach p)).continuous_of_continuous_comp
    intro _
    convert hp n using 1
    exact funext (fun x ↦ norm_localBanachDenseMap p (sLocalThetaToGlobal F (S n) x))
  simpa only [L, norm_localBanachDenseMap] using hL.norm

/-- The actual global ordinary theta quotient is complete for its additive uniformity. -/
theorem globalThetaQuotient_complete :
    @CompleteSpace (GlobalThetaQuotient F)
      (IsTopologicalAddGroup.rightUniformSpace (GlobalThetaQuotient F)) := by
  letI : PolynormableSpace ℂ (GlobalThetaQuotient F) :=
    polynormableSpace_complex_quotient (globalThetaOperator F).ker
  obtain ⟨S, hS, hcof⟩ := exists_cofinal_place_sequence F
  let D := globalThetaQuotient_tower F S hS hcof
  exact D.complete_of_strict (fun n ↦ sLocalThetaQuotient_complete F (S n))
    (fun n ↦ (sLocalThetaToGlobal_isClosedEmbedding F (S n)).isEmbedding)
    (globalTheta_cofinal_seminorm_final F hcof)


private theorem frechet_range_of_embedding {X E : Type u}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [PolynormableSpace ℂ E]
    (hX : IsFrechetTVS X) (j : X →L[ℂ] E) (hj : IsEmbedding j) :
    IsFrechetTVS j.toLinearMap.range ∧
      (NuclearLocallyConvex.{u, u} X → NuclearLocallyConvex.{u, u} j.toLinearMap.range) ∧
      (NuclearLocallyConvex.{u, u} (StrongDual ℂ X) →
        NuclearLocallyConvex.{u, u} (StrongDual ℂ j.toLinearMap.range)) := by
  let R := j.toLinearMap.range
  let e := LinearEquiv.ofInjective j.toLinearMap hj.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hj.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  obtain ⟨hadd, _, hmetric, hcomplete⟩ := hX
  letI : TopologicalSpace.MetrizableSpace X := hmetric
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  have hu : IsUniformInducing e.toLinearMap.toAddMonoidHom :=
    AddMonoidHom.isUniformInducing_of_isInducing he
  let eL : X ≃L[ℂ] R := ⟨e, h.continuous, h.symm.continuous⟩
  exact ⟨⟨inferInstance, inferInstance, h.symm.isEmbedding.metrizableSpace,
    (hu.completeSpace_congr e.surjective).mp hcomplete⟩,
    nuclearLocallyConvex_of_equiv eL, strongDual_nuclear_of_equiv eL⟩

/-- The global ordinary theta quotient also has a strict countable Fréchet
presentation. The two indices are synchronized by Fréchet factorization. -/
theorem globalTheta_exists_strictFrechet :
    ∃ (W : ℕ → Submodule ℂ (GlobalThetaQuotient F))
      (D : LinearInductivePresentation (GlobalThetaQuotient F) (fun n ↦ W n)),
      (∀ n, IsFrechetTVS (W n)) ∧ (∀ n, IsClosedEmbedding (D.incl n)) ∧
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ p : Seminorm ℂ (GlobalThetaQuotient F),
        (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) → ∀ n, NuclearLocallyConvex.{u, u} (W n)) ∧
      (NuclearLocallyConvex.{u, u} (Arch F) →
        NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F)) →
        ∀ n, NuclearLocallyConvex.{u, u} (StrongDual ℂ (W n))) := by
  let G := GlobalThetaQuotient F
  letI : T2Space G := globalThetaQuotient_t2Space F
  letI : PolynormableSpace ℂ G := polynormableSpace_complex_quotient (globalThetaOperator F).ker
  obtain ⟨S, hS, hcof⟩ := exists_cofinal_place_sequence F
  let D := globalThetaQuotient_tower F S hS hcof
  choose W d hF hEmb _ hlocal hnuclear hdual using fun n ↦ sLocalTheta_exists_strictFrechet F (S n)
  let j (a : ℕ × ℕ) : W a.1 a.2 →L[ℂ] G := (D.incl a.1).comp ((d a.1).incl a.2)
  let R (a : ℕ × ℕ) := (j a).toLinearMap.range
  have hj (a : ℕ × ℕ) : IsEmbedding (j a) :=
    (sLocalThetaToGlobal_isClosedEmbedding F (S a.1)).isEmbedding.comp (hEmb a.1 a.2).isEmbedding
  have hR (a : ℕ × ℕ) : IsFrechetTVS (R a) :=
    (frechet_range_of_embedding (hF a.1 a.2) (j a) (hj a)).1
  have hTransfer (a : ℕ × ℕ) (n : ℕ) (ha : a.1 ≤ n) : ∃ m, R a ≤ R (n, m) := by
    letI : T2Space (Theta F (S n)) := sLocalThetaQuotient_t2Space F (S n)
    let f := (D.transition ha).comp ((d a.1).incl a.2)
    obtain ⟨m, v, hv⟩ := frechet_factorization_of_isFrechetTVS (hF a.1 a.2) (hF n)
      f (d n).incl (d n).injective_incl (d n).exhaust
    refine ⟨m, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine ⟨v x, ?_⟩
    have he : (d n).incl m (v x) = D.transition ha ((d a.1).incl a.2 x) := DFunLike.congr_fun hv x
    change D.incl n ((d n).incl m (v x)) = D.incl a.1 ((d a.1).incl a.2 x)
    rw [he, D.incl_transition]
  have hJoin (a b : ℕ × ℕ) : ∃ c, R a ≤ R c ∧ R b ≤ R c := by
    let n := max a.1 b.1
    obtain ⟨ka, ha⟩ := hTransfer a n (le_max_left _ _)
    obtain ⟨kb, hb⟩ := hTransfer b n (le_max_right _ _)
    let m := max ka kb
    have hn (k : ℕ) (hk : k ≤ m) : R (n, k) ≤ R (n, m) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨(d n).transition hk x, congrArg (D.incl n) ((d n).incl_transition hk x)⟩
    exact ⟨(n, m), ha.trans (hn ka (le_max_left _ _)), hb.trans (hn kb (le_max_right _ _))⟩
  let p := Nat.pairEquiv.symm
  let a (n : ℕ) : ℕ × ℕ := Nat.rec (p 0) (fun n prev ↦ (hJoin prev (p (n+1))).choose) n
  let U (n : ℕ) := R (a n)
  have hU : Monotone U :=
    monotone_nat_of_le_succ (fun n ↦ (hJoin (a n) (p (n+1))).choose_spec.1)
  have hCover (b : ℕ × ℕ) : ∃ n, R b ≤ U n := by
    obtain ⟨n, rfl⟩ := p.surjective b
    cases n with
    | zero => exact ⟨0, le_rfl⟩
    | succ n => exact ⟨n+1, (hJoin (a n) (p (n+1))).choose_spec.2⟩
  have hEx (y : G) : ∃ n, y ∈ U n := by
    obtain ⟨n, x, rfl⟩ := D.exhaust y
    obtain ⟨m, z, rfl⟩ := (d n).exhaust x
    obtain ⟨k, hk⟩ := hCover (n, m)
    exact ⟨k, hk ⟨z, rfl⟩⟩
  have hP (q : Seminorm ℂ G) (hq : ∀ n, Continuous (q.comp (U n).subtype)) : Continuous q := by
    apply globalTheta_cofinal_seminorm_final F hcof
    intro n
    apply hlocal n
    intro m
    obtain ⟨k, hk⟩ := hCover (n, m)
    let L := (j (n, m)).codRestrict (U k) (fun x ↦ hk ⟨x, rfl⟩)
    exact (hq k).comp L.continuous
  let D' : LinearInductivePresentation G (fun n ↦ U n) :=
    { incl := fun n ↦ (U n).subtypeL
      transition := fun h ↦ ⟨Submodule.inclusion (hU h), continuous_subtype_val.subtype_mk _⟩
      injective_incl := fun _ ↦ Subtype.val_injective
      incl_transition := fun _ _ ↦ rfl
      exhaust := fun y ↦ by
        obtain ⟨n, hn⟩ := hEx y
        exact ⟨n, ⟨y, hn⟩, rfl⟩
      continuous_limit := fun L ↦ ⟨fun h n ↦ h.comp (U n).subtypeL.continuous, fun h ↦ by
        apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L
        intro i
        apply hP
        intro n
        exact ((norm_withSeminorms ℂ ℂ).continuous_seminorm i).comp (h n)⟩ }
  have hUFr (n : ℕ) := hR (a n)
  have hc (n : ℕ) : IsClosedEmbedding (D'.incl n) :=
    (hUFr n).isClosedEmbedding _ IsEmbedding.subtypeVal
  have hStage (hN : NuclearLocallyConvex.{u, u} (Arch F)) (n : ℕ) :
      NuclearLocallyConvex.{u, u} (U n) := by
    let c := a n
    exact (frechet_range_of_embedding (hF c.1 c.2) (j c) (hj c)).2.1 (hnuclear c.1 hN c.2)
  have hDualStage (hN : NuclearLocallyConvex.{u, u} (Arch F))
      (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F))) (n : ℕ) :
      NuclearLocallyConvex.{u, u} (StrongDual ℂ (U n)) := by
    let c := a n
    exact (frechet_range_of_embedding (hF c.1 c.2) (j c) (hj c)).2.2 (hdual c.1 hN hD c.2)
  refine ⟨U, D', hUFr, hc, fun n ↦ ?_, hP, hStage, hDualStage⟩
  apply (hc (n+1)).of_comp_iff.mp
  have he : D'.incl (n+1) ∘ D'.transition (Nat.le_succ n) = D'.incl n :=
    funext (D'.incl_transition (Nat.le_succ n))
  rw [he]
  exact hc n


/-- A locally convex inductive limit of Fréchet spaces is barrelled. -/
theorem barrelled_of_frechet_final {E : Type*} {X : ℕ → Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (j : ∀ n, X n →L[ℂ] E) (hX : ∀ n, IsFrechetTVS (X n))
    (hfinal : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (j n).toLinearMap)) → Continuous p) :
    BarrelledSpace ℂ E := by
  constructor
  intro p hp
  apply hfinal
  intro n
  letI := isFrechetTVS_barrelled (hX n)
  exact (p.comp (j n).toLinearMap).continuous_of_lowerSemicontinuous (hp.comp (j n).continuous)

/-- The actual S-local theta quotient is barrelled. -/
theorem sLocalThetaQuotient_barrelled : BarrelledSpace ℂ (Theta F S) := by
  obtain ⟨_, D, hF, _, _, hFinal, _, _⟩ := sLocalTheta_exists_strictFrechet F S
  exact barrelled_of_frechet_final D.incl hF hFinal

/-- The actual global theta quotient is barrelled. -/
theorem globalThetaQuotient_barrelled : BarrelledSpace ℂ (GlobalThetaQuotient F) := by
  obtain ⟨_, D, hF, _, _, hFinal, _, _⟩ := globalTheta_exists_strictFrechet F
  exact barrelled_of_frechet_final D.incl hF hFinal


/-- Nuclearity of the archimedean Schwartz factor implies nuclearity of the
actual S-local ordinary theta quotient. -/
theorem sLocalThetaQuotient_nuclear_of_arch (hN : NuclearLocallyConvex.{u, u} (Arch F)) :
    NuclearLocallyConvex.{u, u} (Theta F S) := by
  letI : T2Space (Theta F S) := sLocalThetaQuotient_t2Space F S
  letI : PolynormableSpace ℂ (Theta F S) := polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  obtain ⟨_, D, _, _, _, hFinal, hn, _⟩ := sLocalTheta_exists_strictFrechet F S
  exact D.nuclear_of_stages (hn hN) hFinal

/-- Nuclearity of the archimedean Schwartz factor implies nuclearity of the
actual global ordinary theta quotient. -/
theorem globalThetaQuotient_nuclear_of_arch (hN : NuclearLocallyConvex.{u, u} (Arch F)) :
    NuclearLocallyConvex.{u, u} (GlobalThetaQuotient F) := by
  letI : T2Space (GlobalThetaQuotient F) := globalThetaQuotient_t2Space F
  letI : PolynormableSpace ℂ (GlobalThetaQuotient F) :=
    polynormableSpace_complex_quotient (globalThetaOperator F).ker
  obtain ⟨_, D, _, _, _, hFinal, hn, _⟩ := globalTheta_exists_strictFrechet F
  exact D.nuclear_of_stages (hn hN) hFinal

theorem sLocalThetaQuotient_montel_of_arch (hN : NuclearLocallyConvex.{u, u} (Arch F)) :
    MontelSpace ℂ (Theta F S) := by
  letI : UniformSpace (Theta F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (Theta F S) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (Theta F S) := sLocalThetaQuotient_complete F S
  exact ⟨fun _ hs hb ↦
    (nuclearLocallyConvex_totallyBounded (sLocalThetaQuotient_nuclear_of_arch F S hN) hb).isCompact_of_isClosed hs⟩

theorem globalThetaQuotient_montel_of_arch (hN : NuclearLocallyConvex.{u, u} (Arch F)) :
    MontelSpace ℂ (GlobalThetaQuotient F) := by
  letI : UniformSpace (GlobalThetaQuotient F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (GlobalThetaQuotient F) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (GlobalThetaQuotient F) := globalThetaQuotient_complete F
  exact ⟨fun _ hs hb ↦
    (nuclearLocallyConvex_totallyBounded (globalThetaQuotient_nuclear_of_arch F hN) hb).isCompact_of_isClosed hs⟩

/-- The strong dual of a strict Fréchet limit is nuclear when all stage strong duals are nuclear. -/
theorem strongDual_nuclear_of_strictFrechet
    {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {W : ℕ → Type u} [∀ n, AddCommGroup (W n)] [∀ n, Module ℂ (W n)]
    [∀ n, TopologicalSpace (W n)]
    (D : LinearInductivePresentation E W) (hFr : ∀ n, IsFrechetTVS (W n))
    (hEmb : ∀ n, IsClosedEmbedding (D.incl n))
    (hTrans : ∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n)))
    (hFinal : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p)
    (hN : ∀ n, NuclearLocallyConvex.{u, u} (StrongDual ℂ (W n))) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ E) := by
  letI : ∀ n, IsTopologicalAddGroup (W n) := fun n ↦ (hFr n).choose
  letI : ∀ n, PolynormableSpace ℂ (W n) := fun n ↦ (hFr n).choose_spec.1
  letI : ∀ n, ContinuousSMul ℂ (W n) :=
    fun n ↦ (PolynormableSpace.withSeminorms ℂ (W n)).continuousSMul
  have hLimit (L : E →ₗ[ℂ] lp (fun _ : ℕ ↦ ℂ) ∞)
      (hL : ∀ n, Continuous (L.comp (D.incl n).toLinearMap)) : Continuous L := by
    apply (norm_withSeminorms ℂ _).continuous_of_continuous_comp
    intro i
    apply hFinal
    intro n
    exact ((norm_withSeminorms ℂ _).continuous_seminorm i).comp (hL n)
  let e := D.strongDualRestrictionOfStrict hTrans (fun n ↦ (hEmb n).isEmbedding) hLimit
  exact nuclearLocallyConvex_of_equiv e.symm
    (nuclearLocallyConvex_submodule (nuclearLocallyConvex_pi hN) D.CompatibleDual)

/-- The strong dual of the S-local theta quotient inherits nuclearity from the
archimedean Schwartz factor and its strong dual. -/
theorem sLocalThetaQuotient_strongDual_nuclear_of_arch
    (hN : NuclearLocallyConvex.{u, u} (Arch F))
    (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F))) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (Theta F S)) := by
  obtain ⟨_, D, hFr, hEmb, hTrans, hFinal, _, hn⟩ := sLocalTheta_exists_strictFrechet F S
  exact strongDual_nuclear_of_strictFrechet D hFr hEmb hTrans hFinal (hn hN hD)

/-- The strong dual of the global theta quotient inherits nuclearity from the
archimedean Schwartz factor and its strong dual. -/
theorem globalThetaQuotient_strongDual_nuclear_of_arch
    (hN : NuclearLocallyConvex.{u, u} (Arch F))
    (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F))) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ (GlobalThetaQuotient F)) := by
  obtain ⟨_, D, hFr, hEmb, hTrans, hFinal, _, hn⟩ := globalTheta_exists_strictFrechet F
  exact strongDual_nuclear_of_strictFrechet D hFr hEmb hTrans hFinal (hn hN hD)

theorem sLocalThetaQuotient_strongDual_montel_of_arch
    (hN : NuclearLocallyConvex.{u, u} (Arch F))
    (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F))) :
    MontelSpace ℂ (StrongDual ℂ (Theta F S)) := by
  letI := sLocalThetaQuotient_strongDual_complete F S
  exact ⟨fun _ hs hb ↦ (nuclearLocallyConvex_totallyBounded
    (sLocalThetaQuotient_strongDual_nuclear_of_arch F S hN hD) hb).isCompact_of_isClosed hs⟩

theorem globalThetaQuotient_strongDual_montel_of_arch
    (hN : NuclearLocallyConvex.{u, u} (Arch F))
    (hD : NuclearLocallyConvex.{u, u} (StrongDual ℂ (Arch F))) :
    MontelSpace ℂ (StrongDual ℂ (GlobalThetaQuotient F)) := by
  letI := globalThetaQuotient_strongDual_complete F
  exact ⟨fun _ hs hb ↦ (nuclearLocallyConvex_totallyBounded
    (globalThetaQuotient_strongDual_nuclear_of_arch F hN hD) hb).isCompact_of_isClosed hs⟩

end

end Masullo
