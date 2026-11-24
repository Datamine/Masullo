import FinestNuclear
import FinestStrongDual
import FinestStrictLF
import TopologicalLinearLimits
import AdelicHaarScaling
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Algebra.Support
import Mathlib.LinearAlgebra.Basis.VectorSpace

open Bornology Filter Function IsDedekindDomain NumberField Set Topology TopologicalSpace
open scoped NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (X : Type*) [TopologicalSpace X]

/-- The locally constant complex-valued tests with compact support. -/
def locallyConstantTests : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' a _ hf := ⟨hf.1.comp (a • ·), hf.2.smul_left⟩

/-- Compact opens in a second-countable space form a countable collection. -/
theorem countable_compactOpens [SecondCountableTopology X] :
    ({U : Set X | IsCompact U ∧ IsOpen U}).Countable := by
  classical
  let B := countableBasis X
  letI : Countable B := (countable_countableBasis X).to_subtype
  let f (s : Finset B) : Set X := ⋃₀ (Set.image Subtype.val (s : Set B))
  refine (countable_range f).mono ?_
  intro U hU
  obtain ⟨s, hs⟩ := eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open
    B (isBasis_countableBasis X) U hU.1 hU.2
  exact ⟨s, hs.symm⟩

variable [T2Space X]

/-- An indicator of a compact open set is a locally constant test. -/
def compactOpenIndicator (U : {U : Set X // IsCompact U ∧ IsOpen U}) :
    locallyConstantTests X := by
  classical
  let f : X → ℂ := U.val.indicator (fun _ => 1)
  have hUc : IsClopen U.val := ⟨U.property.1.isClosed, U.property.2⟩
  have hl : IsLocallyConstant f := by
    intro V
    by_cases h1 : (1 : ℂ) ∈ V <;> by_cases h0 : (0 : ℂ) ∈ V
    · have he : f ⁻¹' V = univ := by
        ext x
        by_cases hx : x ∈ U.val <;> simp [f, hx, h1, h0]
      rw [he]
      exact isOpen_univ
    · have he : f ⁻¹' V = U.val := by
        ext x
        by_cases hx : x ∈ U.val <;> simp [f, hx, h1, h0]
      exact he ▸ hUc.2
    · have he : f ⁻¹' V = U.valᶜ := by
        ext x
        by_cases hx : x ∈ U.val <;> simp [f, hx, h1, h0]
      exact he ▸ hUc.1.isOpen_compl
    · have he : f ⁻¹' V = ∅ := by
        ext x
        by_cases hx : x ∈ U.val <;> simp [f, hx, h1, h0]
      exact he ▸ isOpen_empty
  refine ⟨f, hl, ?_⟩
  have hs : Function.support f = U.val := by
    ext x
    by_cases hx : x ∈ U.val <;> simp [f, hx, Function.mem_support]
  rw [HasCompactSupport, tsupport, hs, hUc.1.closure_eq]
  exact U.property.1

/-- Compact-open indicators span the locally constant compactly supported tests. -/
theorem span_compactOpenIndicators :
    Submodule.span ℂ (range (compactOpenIndicator X)) = ⊤ := by
  classical
  apply top_unique
  intro f _
  have hf : IsLocallyConstant f.val ∧ HasCompactSupport f.val := f.property
  let K := tsupport f.val
  have hK : IsCompact K := hf.2
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A := (range (fun x : K => f.val x)) \ {0}
  have hA : A.Finite :=
    (hf.1.comp_continuous continuous_subtype_val).range_finite.sdiff
  let fiber (a : ℂ) := {x | f.val x = a}
  have hc (a : A) : IsCompact (fiber a.val) ∧ IsOpen (fiber a.val) := by
    have hc := hf.1.isClopen_fiber a.val
    have hsubset : fiber a.val ⊆ K := by
      intro x hx
      apply subset_tsupport f.val
      exact fun h => a.property.2 (hx.symm.trans h)
    exact ⟨hK.of_isClosed_subset hc.1 hsubset, hc.2⟩
  letI : Fintype A := hA.fintype
  let term (a : A) := a.val • compactOpenIndicator X ⟨fiber a.val, hc a⟩
  have ht : ∀ a : A, term a ∈ Submodule.span ℂ (range (compactOpenIndicator X)) :=
    fun a => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨fiber a.val, hc a⟩, rfl⟩)
  have he : f = ∑ a : A, term a := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    have hterm (a : A) : (term a).val x = if f.val x = a.val then a.val else 0 := by
      change a.val * (fiber a.val).indicator (fun _ => (1 : ℂ)) x = _
      by_cases h : f.val x = a.val <;> simp [fiber, h]
    change f.val x = ∑ a : A, (term a).val x
    simp_rw [hterm]
    by_cases hx : f.val x = 0
    · rw [hx]
      symm
      exact Finset.sum_eq_zero fun a _ => ite_eq_right (fun h => a.property.2 h.symm)
    · have hmem : f.val x ∈ A := ⟨⟨⟨x, subset_tsupport f.val hx⟩, rfl⟩, hx⟩
      rw [Finset.sum_eq_single (⟨f.val x, hmem⟩ : A)]
      · simp
      · intro a _ ha
        exact ite_eq_right (fun h => ha (Subtype.ext h.symm))
      · simp
  rw [he]
  exact Submodule.sum_mem _ fun a _ => ht a

/-- The defining tests have a countable algebraic basis on second-countable spaces. -/
theorem locallyConstantTests_countable_basis [SecondCountableTopology X] :
    ∃ I : Set (locallyConstantTests X), I.Countable ∧ Nonempty (Module.Basis I ℂ (locallyConstantTests X)) := by
  let S := range (compactOpenIndicator X)
  letI : Countable {U : Set X // IsCompact U ∧ IsOpen U} :=
    (countable_compactOpens X).to_subtype
  have hS : S.Countable := countable_range _
  have hspan : ⊤ ≤ Submodule.span ℂ S := (span_compactOpenIndicators X).ge
  let b := Module.Basis.ofSpan hspan
  refine ⟨range b, hS.mono (Module.Basis.ofSpan_subset hspan), ⟨?_⟩⟩
  rw [show range b = _ from Module.Basis.range_ofSpan hspan]
  exact b

abbrev LocallyConstantTestSpace := locallyConstantTests X

local notation "S₀" => LocallyConstantTestSpace X

/-- The countable algebraic basis gives the strict LF presentation by finite-dimensional spaces. -/
theorem locallyConstantTests_strictLF [SecondCountableTopology X] :
    letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
    ∃ P : ℕ → Submodule ℂ S₀, Monotone P ∧ (∀ x : S₀, ∃ n, x ∈ P n) ∧
      (∀ n, FiniteDimensional ℂ (P n)) ∧
      (∀ n, IsClosed (P n : Set S₀) ∧ IsEmbedding ((P n).subtype : P n → S₀)) ∧
      (∀ (m n : ℕ) (_h : m ≤ n) (h' : P m ≤ P n),
        IsClosedEmbedding (Submodule.inclusion h' : P m → P n)) ∧
      locallyConvexFinalTopology (A := fun n : ℕ => ↥(P n)) (fun n => (P n).subtype) =
        finestLocallyConvexTopology S₀ := by
  obtain ⟨I, hI, ⟨b⟩⟩ := locallyConstantTests_countable_basis X
  letI : Countable I := hI.to_subtype
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat I
  exact finest_strictLF b ⟨j, hj⟩

/-- The locally constant test topology is nuclear in the tensor-product characterization. -/
theorem locallyConstantTests_nuclear [SecondCountableTopology X] (Y : Type*)
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] :
    letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
    projectiveTensorTopology S₀ Y = injectiveTensorTopology S₀ Y := by
  obtain ⟨I, hI, ⟨b⟩⟩ := locallyConstantTests_countable_basis X
  letI : Countable I := hI.to_subtype
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat I
  exact finest_tensorTopologies_equal b ⟨j, hj⟩

/-- The strong dual is complete and metrizable in its locally convex topology. -/
theorem locallyConstantTests_strongDual_frechet [SecondCountableTopology X] :
    letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
    CompleteSpace (StrongDual ℂ S₀) ∧ MetrizableSpace (StrongDual ℂ S₀) := by
  obtain ⟨I, hI, ⟨b⟩⟩ := locallyConstantTests_countable_basis X
  letI : Countable I := hI.to_subtype
  exact finest_strongDual_frechet b

/-- The strong dual is nuclear in the tensor-product characterization. -/
theorem locallyConstantTests_strongDual_nuclear [SecondCountableTopology X] (Y : Type*)
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] :
    letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
    projectiveTensorTopology (StrongDual ℂ S₀) Y =
      injectiveTensorTopology (StrongDual ℂ S₀) Y := by
  obtain ⟨_, _, ⟨b⟩⟩ := locallyConstantTests_countable_basis X
  exact finest_strongDual_nuclear b

/-- The finest topology is Hausdorff, locally convex, complete and Montel,
and every linear subspace is topologically complemented. -/
theorem locallyConstantTests_finest_properties :
    letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
    letI : UniformSpace S₀ := finestUniformSpace _
    T2Space S₀ ∧ PolynormableSpace ℂ S₀ ∧ CompleteSpace S₀ ∧ BarrelledSpace ℂ S₀ ∧
      (∀ B : Set S₀, IsClosed B → IsVonNBounded ℂ B → IsCompact B) ∧
      (∀ P : Submodule ℂ S₀, ∃ Q : Submodule ℂ S₀, P.IsTopCompl Q) := by
  letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
  letI : UniformSpace S₀ := finestUniformSpace _
  exact ⟨finest_t2 _, (finest_withSeminorms _).toPolynormableSpace, finest_complete _,
    finest_barrelled, fun _ => finest_closed_bounded_isCompact,
    fun P => (finest_submodule_quotient P).1⟩

/-- Every linear map from the test space to a locally convex space is continuous.
In particular, every bounded linear map is continuous, which gives bornologicality. -/
theorem locallyConstantTests_linear_continuous (Y : Type*)
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (L : S₀ →ₗ[ℂ] Y) :
    Continuous[finestLocallyConvexTopology S₀, inferInstance] L :=
  finest_linear_continuous L

section Translation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X]

/-- The left action takes a test at (x) to its value at (g^{-1}x). -/
def locallyConstantTestTranslate (g : G) : S₀ →ₗ[ℂ] S₀ where
  toFun f := ⟨f.val ∘ (g⁻¹ • ·), f.property.1.comp_continuous (continuous_const_smul _),
    f.property.2.comp_homeomorph (Homeomorph.smul g⁻¹)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem locallyConstantTestTranslate_orbit_locallyConstant (f : S₀) :
    IsLocallyConstant (fun g : G => locallyConstantTestTranslate X g f) := by
  have hlocal (x : X) : ∀ᶠ p : G × X in 𝓝 (1, x), f.val (p.1 • p.2) = f.val p.2 := by
    have h₁ := (f.property.1.comp_continuous (continuous_fst.smul continuous_snd)).eventually_eq ((1 : G), x)
    have h₂ := (f.property.1.comp_continuous continuous_snd).eventually_eq ((1 : G), x)
    filter_upwards [h₁, h₂] with p hp hq
    change f.val (p.1 • p.2) = f.val ((1 : G) • x) at hp
    rw [one_smul] at hp
    exact hp.trans hq.symm
  have hc : ∀ᶠ g : G in 𝓝 1, ∀ x ∈ tsupport f.val, f.val (g • x) = f.val x :=
    f.property.2.eventually_forall_of_forall_eventually (fun x _ => hlocal x)
  have hci : ∀ᶠ g : G in 𝓝 1, ∀ x ∈ tsupport f.val, f.val (g⁻¹ • x) = f.val x :=
    (continuous_inv.tendsto' (1 : G) 1 inv_one).eventually hc
  have hstab : ∀ᶠ g : G in 𝓝 1, ∀ x : X, f.val (g⁻¹ • x) = f.val x := by
    filter_upwards [hc, hci] with g hg hgi x
    by_cases hx : x ∈ tsupport f.val
    · exact hgi x hx
    · by_cases hix : g⁻¹ • x ∈ tsupport f.val
      · exact (by simpa only [smul_inv_smul] using (hg _ hix).symm)
      · exact (image_eq_zero_of_notMem_tsupport hix).trans
          (image_eq_zero_of_notMem_tsupport hx).symm
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro g
  have hnear : Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' g 1 (inv_mul_cancel g)
  filter_upwards [hnear.eventually hstab] with h hh
  apply Subtype.ext
  funext x
  change f.val (h⁻¹ • x) = f.val (g⁻¹ • x)
  simpa only [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul] using hh (g⁻¹ • x)

/-- Compact sets of translating group elements act uniformly on every convergent
net of tests. The conclusion controls each continuous seminorm simultaneously
over the compact set of translates. -/
theorem locallyConstantTestTranslate_uniform {ι : Type*} {l : Filter ι}
    {u : ι → S₀} {f : S₀} (hu : Tendsto u l (@nhds _ (finestLocallyConvexTopology S₀) f))
    {K : Set G} (hK : IsCompact K) (p : Seminorm ℂ S₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ g ∈ K, p (locallyConstantTestTranslate X g (u i - f)) < ε := by
  letI : TopologicalSpace S₀ := finestLocallyConvexTopology _
  have hp := finest_withSeminorms S₀
  letI : IsTopologicalAddGroup S₀ := hp.topologicalAddGroup
  let r (g : K) := p.comp (locallyConstantTestTranslate X g.val)
  have hb : BddAbove (range r) := (Seminorm.bddAbove_range_iff).mpr fun x => by
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hf : IsLocallyConstant (fun g : K => locallyConstantTestTranslate X g.val x) :=
      (locallyConstantTestTranslate_orbit_locallyConstant X x).comp_continuous continuous_subtype_val
    exact (hf.comp p).range_finite.bddAbove
  let q := ⨆ g : K, r g
  have hq : Continuous q := hp.continuous_seminorm q
  have hzero : Tendsto (fun i => u i - f) l (𝓝 (0 : S₀)) := by
    have hf : Tendsto (fun _ : ι => f) l (𝓝 f) := tendsto_const_nhds
    simpa only [sub_self] using hu.sub hf
  have he := (hq.tendsto' (0 : S₀) 0 (map_zero q)).comp hzero
  filter_upwards [he (Iio_mem_nhds hε)] with i hi g hg
  exact ((le_ciSup hb ⟨g, hg⟩) (u i - f)).trans_lt hi

end Translation

section IntegralUnits

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R] [IsTopologicalRing R]

/-- Compact integral units give uniform convergence of the translated tests. -/
theorem locallyConstantTestTranslate_integral_units {ι : Type*} {l : Filter ι}
    {u : ι → LocallyConstantTestSpace R} {f : LocallyConstantTestSpace R}
    (hu : Tendsto u l (@nhds _ (finestLocallyConvexTopology (LocallyConstantTestSpace R)) f))
    (O : Submonoid R) (hO : IsCompact (O : Set R))
    (p : Seminorm ℂ (LocallyConstantTestSpace R)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ g ∈ O.units,
      p (locallyConstantTestTranslate R g (u i - f)) < ε :=
  locallyConstantTestTranslate_uniform R hu (Submonoid.units_isCompact hO) p hε

end IntegralUnits

section Places

variable (F : Type*) [Field F] [NumberField F]

/-- A finite local completion is Hausdorff and second countable. These instances apply
the locally constant test space construction to the space in Proposition 2.1.2.4. -/
theorem finitePlace_locallyConstantTests_context (v : HeightOneSpectrum (𝓞 F)) :
    T2Space (v.adicCompletion F) ∧ SecondCountableTopology (v.adicCompletion F) :=
  ⟨inferInstance, finitePlace_secondCountable F v⟩

/-- Finite coordinate products and restricted tails are Hausdorff and second countable,
including the empty finite product and the full finite adele ring. -/
theorem finiteProducts_locallyConstantTests_context (S : Finset (HeightOneSpectrum (𝓞 F))) :
    let P := ((v : S) → v.val.adicCompletion F)
    let T := Πʳ (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}),
      [v.val.adicCompletion F, v.val.adicCompletionIntegers F]
    (T2Space P ∧ SecondCountableTopology P) ∧ (T2Space T ∧ SecondCountableTopology T) := by
  letI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := finiteAdeles_secondCountable F
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion F) :=
    finitePlace_secondCountable F v.val
  let e := finiteCoordinateSplit F S
  let j : (Πʳ (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}),
      [v.val.adicCompletion F, v.val.adicCompletionIntegers F]) → FiniteAdeleRing (𝓞 F) F :=
    fun t => e (0, t)
  letI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous (f := fun a : FiniteAdeleRing (𝓞 F) F => (a :
      (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F))
      DFunLike.coe_injective RestrictedProduct.continuous_coe
  let T := Πʳ (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}),
    [v.val.adicCompletion F, v.val.adicCompletionIntegers F]
  have hid : IsInducing (Prod.snd ∘ Prod.mk (0 : (v : S) → v.val.adicCompletion F) : T → T) :=
    IsEmbedding.id.isInducing
  have hj : IsEmbedding j := e.toHomeomorph.isEmbedding.comp
    ⟨IsInducing.of_comp (continuous_const.prodMk continuous_id) continuous_snd hid,
      fun _ _ h => congrArg Prod.snd h⟩
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨hj.t2Space, hj.secondCountableTopology⟩⟩

/-- The integral submonoid in the finite product of completions. -/
def finiteProductIntegers (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Submonoid ((v : S) → v.val.adicCompletion F) where
  carrier := {a | ∀ v, a v ∈ v.val.adicCompletionIntegers F}
  one_mem' _ := one_mem _
  mul_mem' ha hb v := mul_mem (ha v) (hb v)

theorem finiteProductIntegers_compact (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (finiteProductIntegers F S : Set ((v : S) → v.val.adicCompletion F)) := by
  have he : (finiteProductIntegers F S : Set ((v : S) → v.val.adicCompletion F)) =
      Set.univ.pi (fun v : S => (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))) := by
    ext a
    exact ⟨fun h v _ => h v, fun h v => h v (mem_univ v)⟩
  rw [he]
  exact isCompact_univ_pi fun v => finitePlaceIntegral_compact F v.val

abbrev FiniteAdeleTail (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  Πʳ (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}),
    [v.val.adicCompletion F, v.val.adicCompletionIntegers F]

/-- The product of integer rings inside the restricted tail outside a finite set. -/
def tailIntegralSubmonoid (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Submonoid (FiniteAdeleTail F S) where
  carrier := {a | ∀ v, a v ∈ v.val.adicCompletionIntegers F}
  one_mem' _ := one_mem _
  mul_mem' ha hb v := mul_mem (ha v) (hb v)

theorem tailIntegralSubmonoid_compact (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (tailIntegralSubmonoid F S : Set (FiniteAdeleTail F S)) := by
  let J := {v : HeightOneSpectrum (𝓞 F) // v ∉ S}
  let R (v : J) := v.val.adicCompletion F
  let O (v : J) := v.val.adicCompletionIntegers F
  letI (v : J) : CompactSpace (O v) :=
    isCompact_iff_compactSpace.mp (finitePlaceIntegral_compact F v.val)
  let j : (∀ v, O v) → FiniteAdeleTail F S :=
    RestrictedProduct.inclusion _ _ le_top ∘ (RestrictedProduct.homeoTop :
      (∀ v, O v) ≃ₜ (Πʳ v, [R v, O v]_[⊤]))
  have hj : Continuous j :=
    (RestrictedProduct.continuous_inclusion le_top).comp RestrictedProduct.homeoTop.continuous
  have hr : range j = (tailIntegralSubmonoid F S : Set (FiniteAdeleTail F S)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩ v
      exact (a v).property
    · intro hx
      refine ⟨fun v => ⟨x v, hx v⟩, ?_⟩
      exact DFunLike.ext _ _ fun _ => rfl
  exact hr ▸ isCompact_range hj

/-- Lemma 2.1.2.10(1). Uniform convergence over the integral units at one finite place. -/
theorem finitePlace_testTranslate_uniform (v : HeightOneSpectrum (𝓞 F))
    {u : ℕ → LocallyConstantTestSpace (v.adicCompletion F)}
    {f : LocallyConstantTestSpace (v.adicCompletion F)}
    (hu : Tendsto u atTop (@nhds _ (finestLocallyConvexTopology _) f))
    (p : Seminorm ℂ (LocallyConstantTestSpace (v.adicCompletion F))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units,
      p (locallyConstantTestTranslate (v.adicCompletion F) g (u n - f)) < ε :=
  locallyConstantTestTranslate_integral_units hu _ (finitePlaceIntegral_compact F v) p hε

/-- Lemma 2.1.2.10(2). Uniform convergence over the finite product of integer-ring units. -/
theorem finiteProduct_testTranslate_uniform (S : Finset (HeightOneSpectrum (𝓞 F)))
    {u : ℕ → LocallyConstantTestSpace ((v : S) → v.val.adicCompletion F)}
    {f : LocallyConstantTestSpace ((v : S) → v.val.adicCompletion F)}
    (hu : Tendsto u atTop (@nhds _ (finestLocallyConvexTopology _) f))
    (p : Seminorm ℂ (LocallyConstantTestSpace ((v : S) → v.val.adicCompletion F)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g ∈ (finiteProductIntegers F S).units,
      p (locallyConstantTestTranslate ((v : S) → v.val.adicCompletion F) g (u n - f)) < ε :=
  locallyConstantTestTranslate_integral_units hu _ (finiteProductIntegers_compact F S) p hε

/-- Lemma 2.1.2.10(3). Uniform convergence over the integer-ring units in a restricted tail. -/
theorem finiteTail_testTranslate_uniform (S : Finset (HeightOneSpectrum (𝓞 F)))
    {u : ℕ → LocallyConstantTestSpace (FiniteAdeleTail F S)}
    {f : LocallyConstantTestSpace (FiniteAdeleTail F S)}
    (hu : Tendsto u atTop (@nhds _ (finestLocallyConvexTopology _) f))
    (p : Seminorm ℂ (LocallyConstantTestSpace (FiniteAdeleTail F S))) {ε : ℝ} (hε : 0 < ε) :
    letI : Fact (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      IsOpen (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))) :=
      ⟨fun v => Valued.isOpen_valuationSubring (v.val.adicCompletion F)⟩
    ∀ᶠ n in atTop, ∀ g ∈ (tailIntegralSubmonoid F S).units,
      p (locallyConstantTestTranslate (FiniteAdeleTail F S) g (u n - f)) < ε := by
  letI : Fact (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      IsOpen (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))) :=
    ⟨fun v => Valued.isOpen_valuationSubring (v.val.adicCompletion F)⟩
  letI : T2Space (FiniteAdeleTail F S) := (finiteProducts_locallyConstantTests_context F S).2.1
  exact locallyConstantTestTranslate_integral_units hu _ (tailIntegralSubmonoid_compact F S) p hε

end Places

end
end Masullo
