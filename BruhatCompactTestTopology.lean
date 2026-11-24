import BruhatCompactSupport
import BruhatSchwartzStrict
import ElementarySchwartzComplete

open Filter Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Compactly supported smooth Bruhat functions, realized in Schwartz–Bruhat space. -/
def bruhatCompactTestSubmodule : Submodule ℂ (BruhatSchwartz G) where
  carrier := {f | HasCompactSupport f.val}
  zero_mem' := HasCompactSupport.zero
  add_mem' hf hg := hf.add hg
  smul_mem' _ _ hf := hf.smul_left

def BruhatCompactTest (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] :=
  ↥(bruhatCompactTestSubmodule (G := G))

namespace BruhatCompactTest

instance : AddCommGroup (BruhatCompactTest G) :=
  inferInstanceAs (AddCommGroup (bruhatCompactTestSubmodule (G := G)))

instance : Module ℂ (BruhatCompactTest G) :=
  inferInstanceAs (Module ℂ (bruhatCompactTestSubmodule (G := G)))

def algebraicEquiv : BruhatCompactTest G ≃ₗ[ℂ] bruhatCompactTestSubmodule (G := G) :=
  LinearEquiv.refl ℂ _

def val (u : BruhatCompactTest G) : BruhatSchwartz G := (algebraicEquiv u).val

theorem property (u : BruhatCompactTest G) : HasCompactSupport u.val.val :=
  (algebraicEquiv u).property

theorem val_injective : Injective (val : BruhatCompactTest G → BruhatSchwartz G) :=
  fun _ _ h => algebraicEquiv.injective (Subtype.ext h)

end BruhatCompactTest

theorem exists_bruhatCompactTest_iff (f : G → ℂ) :
    (∃ u : BruhatCompactTest G, u.val.val = f) ↔
      f ∈ bruhatSmoothSubmodule (G := G) ∧ HasCompactSupport f := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨bruhatSchwartz_le_smooth u.val.property, u.property⟩
  · rintro ⟨hf, hc⟩
    exact ⟨BruhatCompactTest.algebraicEquiv.symm
      ⟨⟨f, bruhatSchwartz_mem_of_smooth_compactSupport hf hc⟩, hc⟩, rfl⟩

namespace BruhatSchwartzStage

/-- The closed subspace of an elementary Schwartz stage with ambient support in K. -/
def compactTests (p : BruhatSchwartzStage G) (K : Set G) : Submodule ℂ p.Space where
  carrier := {u | ∀ g ∉ K, p.realize u g = 0}
  zero_mem' g _ := by rw [map_zero]; rfl
  add_mem' hu hv g hg := by rw [map_add, Pi.add_apply, hu g hg, hv g hg, add_zero]
  smul_mem' c _ hu g hg := by rw [map_smul, Pi.smul_apply, hu g hg, smul_zero]

theorem continuous_realize_eval (p : BruhatSchwartzStage G) (g : G) :
    Continuous (fun u : p.Space => p.realize u g) :=
  (bruhatSchwartz_continuous_eval g).comp p.inclusionCLM.continuous

theorem isClosed_compactTests (p : BruhatSchwartzStage G) (K : Set G) :
    IsClosed (p.compactTests K : Set p.Space) := by
  have he : (p.compactTests K : Set p.Space) = ⋂ g : (Kᶜ : Set G), {u | p.realize u g.val = 0} := by
    ext u
    exact ⟨fun hu => mem_iInter.mpr fun g => hu g g.property,
      fun hu g hg => mem_iInter.mp hu ⟨g, hg⟩⟩
  rw [he]
  exact isClosed_iInter fun g => isClosed_eq (p.continuous_realize_eval g.val) continuous_const

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem compactTests_hasCompactSupport (p : BruhatSchwartzStage G) {K : Set G}
    (hK : IsCompact K) (u : p.compactTests K) : HasCompactSupport (p.realize u.val) :=
  HasCompactSupport.intro' hK hK.isClosed u.property

end BruhatSchwartzStage

abbrev BruhatCompactTestIndex (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  BruhatSchwartzStage G × {K : Set G // IsCompact K}

abbrev BruhatCompactTestIndex.Space (i : BruhatCompactTestIndex G) :=
  i.1.compactTests i.2.val

def BruhatCompactTestIndex.inclusion (i : BruhatCompactTestIndex G) :
    i.Space →ₗ[ℂ] BruhatCompactTest G :=
  BruhatCompactTest.algebraicEquiv.symm.toLinearMap.comp
    ((i.1.inclusion.comp (i.1.compactTests i.2.val).subtype).codRestrict _
      (fun u => i.1.compactTests_hasCompactSupport i.2.property u))

/-- The locally convex topology of Bruhat tests is final over their elementary
stages at fixed compact support. -/
instance : TopologicalSpace (BruhatCompactTest G) :=
  locallyConvexFinalTopology (fun i : BruhatCompactTestIndex G => i.inclusion)

instance : PolynormableSpace ℂ (BruhatCompactTest G) :=
  (locallyConvexFinal_withSeminorms
    (fun i : BruhatCompactTestIndex G => i.inclusion)).toPolynormableSpace

instance : IsTopologicalAddGroup (BruhatCompactTest G) :=
  (locallyConvexFinal_withSeminorms
    (fun i : BruhatCompactTestIndex G => i.inclusion)).topologicalAddGroup

def BruhatCompactTestIndex.inclusionCLM (i : BruhatCompactTestIndex G) :
    i.Space →L[ℂ] BruhatCompactTest G := by
  refine ⟨i.inclusion, ?_⟩
  exact locallyConvexFinal_stage_continuous (fun j : BruhatCompactTestIndex G => j.inclusion) i

def bruhatCompactTest_toSchwartz : BruhatCompactTest G →L[ℂ] BruhatSchwartz G := by
  let L : BruhatCompactTest G →ₗ[ℂ] BruhatSchwartz G :=
    bruhatCompactTestSubmodule.subtype.comp BruhatCompactTest.algebraicEquiv.toLinearMap
  refine ⟨L, (locallyConvexFinal_continuous_iff
    (fun i : BruhatCompactTestIndex G => i.inclusion) L).mpr fun i => ?_⟩
  change Continuous ((i.1.inclusionCLM : i.1.Space → BruhatSchwartz G) ∘
    (Subtype.val : i.Space → i.1.Space))
  exact i.1.inclusionCLM.continuous.comp continuous_subtype_val

theorem bruhatCompactTest_t2 : T2Space (BruhatCompactTest G) := by
  letI : T2Space (BruhatSchwartz G) := bruhatSchwartz_t2
  exact T2Space.of_injective_continuous
    (f := bruhatCompactTest_toSchwartz) BruhatCompactTest.val_injective bruhatCompactTest_toSchwartz.continuous

theorem BruhatCompactTestIndex.inclusion_injective (i : BruhatCompactTestIndex G) :
    Injective i.inclusionCLM := by
  intro u v h
  apply Subtype.ext
  apply i.1.inclusion_injective
  exact congrArg (fun f : BruhatCompactTest G => f.val) h

namespace BruhatCompactTestIndex

theorem transition_realize (i j : BruhatCompactTestIndex G) (h : i.1.1 ≤ j.1.1) (u : i.1.Space) :
    j.1.realize (i.1.transition j.1 h u) = i.1.realize u :=
  congrArg Subtype.val (i.1.inclusion_transition j.1 h u)

def transition (i j : BruhatCompactTestIndex G) (h : i.1.1 ≤ j.1.1) (hK : i.2.val ⊆ j.2.val) :
    i.Space →L[ℂ] j.Space :=
  ((i.1.transition j.1 h).comp (i.1.compactTests i.2.val).subtypeL).codRestrict _
    (fun u g hg => (congrFun (i.transition_realize j h u.val) g).trans (u.property g (fun h => hg (hK h))))

theorem inclusion_transition (i j : BruhatCompactTestIndex G) (h : i.1.1 ≤ j.1.1)
    (hK : i.2.val ⊆ j.2.val) (u : i.Space) :
    j.inclusionCLM (i.transition j h hK u) = i.inclusionCLM u := by
  apply BruhatCompactTest.val_injective
  change j.1.inclusionCLM (i.1.transition j.1 h u.val) = i.1.inclusionCLM u.val
  exact i.1.inclusion_transition j.1 h u.val

theorem transition_isClosedEmbedding (i j : BruhatCompactTestIndex G) (h : i.1.1 ≤ j.1.1)
    (hK : i.2.val ⊆ j.2.val) : IsClosedEmbedding (i.transition j h hK) := by
  apply IsClosedEmbedding.of_comp (g := (Subtype.val : j.Space → j.1.Space)) IsEmbedding.subtypeVal
  exact (i.1.transition_isClosedEmbedding j.1 h).comp
    (i.1.isClosed_compactTests i.2.val).isClosedEmbedding_subtypeVal

end BruhatCompactTestIndex

private theorem compactTestIndex_cofinalSequence [SecondCountableTopology G] (K : CompactExhaustion G) :
    ∃ b : ℕ → BruhatCompactTestIndex G,
      Monotone (fun n => (b n).1.1) ∧ Monotone (fun n => (b n).2.val) ∧
      ∀ i : BruhatCompactTestIndex G, ∃ n, i.1.1 ≤ (b n).1.1 ∧ i.2.val ⊆ (b n).2.val := by
  obtain ⟨P, hP, hCov⟩ := lcaStructuralPairs_cofinalSequence (G := G)
  refine ⟨fun n => (⟨P n, Classical.choice (P n).quotient_elementary⟩, ⟨K n, K.isCompact n⟩),
    hP, K.subset, fun i => ?_⟩
  obtain ⟨n, hn⟩ := hCov i.1.1
  obtain ⟨k, hk⟩ := K.exists_superset_of_isCompact i.2.property
  exact ⟨max n k, hn.trans (hP (le_max_left n k)), hk.trans (K.subset (le_max_right n k))⟩

private theorem compactTest_continuous_of_cofinal (b : ℕ → BruhatCompactTestIndex G)
    (hCov : ∀ i : BruhatCompactTestIndex G, ∃ n, i.1.1 ≤ (b n).1.1 ∧ i.2.val ⊆ (b n).2.val)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y]
    (L : BruhatCompactTest G →ₗ[ℂ] Y) :
    Continuous L ↔ ∀ n, Continuous (L.comp (b n).inclusion) := by
  refine ⟨fun h n => h.comp (b n).inclusionCLM.continuous, fun h => ?_⟩
  refine (locallyConvexFinal_continuous_iff (fun i : BruhatCompactTestIndex G => i.inclusion) L).mpr fun i => ?_
  obtain ⟨n, hn, hk⟩ := hCov i
  have he : (L.comp i.inclusion : i.Space → Y) =
      (L.comp (b n).inclusion) ∘ i.transition (b n) hn hk :=
    funext fun u => congrArg L (i.inclusion_transition (b n) hn hk u).symm
  exact (congrArg (fun f : i.Space → Y => Continuous f) he).mpr
    ((h n).comp (i.transition (b n) hn hk).continuous)

set_option maxHeartbeats 3000000 in
private def compactTestPresentation (b : ℕ → BruhatCompactTestIndex G)
    (hb : Monotone (fun n => (b n).1.1)) (hK : Monotone (fun n => (b n).2.val))
    (hCov : ∀ i : BruhatCompactTestIndex G, ∃ n, i.1.1 ≤ (b n).1.1 ∧ i.2.val ⊆ (b n).2.val) :
    LinearInductivePresentation (BruhatCompactTest G) (fun n => (b n).Space) := by
  refine {
    incl := fun n => (b n).inclusionCLM
    transition := fun {n k} h => (b n).transition (b k) (hb h) (hK h)
    injective_incl := fun n => (b n).inclusion_injective
    incl_transition := fun {n k} h u => (b n).inclusion_transition (b k) (hb h) (hK h) u
    exhaust := ?_
    continuous_limit := ?_ }
  · intro x
    obtain ⟨p, u, hu⟩ := x.val.property
    let i : BruhatCompactTestIndex G := (p, ⟨tsupport x.val.val, x.property⟩)
    let v : i.Space := ⟨u, fun g hg => (congrFun hu g).trans (image_eq_zero_of_notMem_tsupport hg)⟩
    obtain ⟨n, hn, hk⟩ := hCov i
    exact ⟨n, i.transition (b n) hn hk v,
      (i.inclusion_transition (b n) hn hk v).trans
        (BruhatCompactTest.val_injective (Subtype.ext hu))⟩
  · intro L
    exact compactTest_continuous_of_cofinal b hCov L

theorem BruhatCompactTestIndex.inclusion_isEmbedding [SecondCountableTopology G]
    (i : BruhatCompactTestIndex G) : IsEmbedding i.inclusionCLM := by
  refine IsEmbedding.of_comp i.inclusionCLM.continuous bruhatCompactTest_toSchwartz.continuous ?_
  change IsEmbedding ((i.1.inclusionCLM : i.1.Space → BruhatSchwartz G) ∘
    (Subtype.val : i.Space → i.1.Space))
  exact ((bruhatSchwartz_strict (G := G)).2.1 i.1).comp IsEmbedding.subtypeVal

private theorem compactTestStage_isFrechet (i : BruhatCompactTestIndex G) :
    IsFrechetTVS i.Space := by
  obtain ⟨hT, _, hmetric, hcomplete⟩ := @elementarySchwartz_isFrechet
    i.1.2.realDim i.1.2.torusDim i.1.2.latticeRank i.1.2.finiteFactor
    i.1.2.finiteGroup i.1.2.finiteTopology i.1.2.finiteDiscrete (Finite.of_fintype _)
  letI : TopologicalSpace.MetrizableSpace i.1.Space := hmetric
  letI : CompleteSpace i.1.Space := hcomplete
  letI : IsClosed (i.Space : Set i.1.Space) := i.1.isClosed_compactTests i.2.val
  letI : IsUniformAddGroup i.Space := (i.1.compactTests i.2.val).toAddSubgroup.isUniformAddGroup
  refine ⟨inferInstance, inferInstance, IsEmbedding.subtypeVal.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

set_option maxHeartbeats 2500000 in
/-- Compact Bruhat tests form a countable strict locally convex inductive
limit of Fréchet spaces that bound both the support and the structural quotient. -/
theorem bruhatCompactTest_strict [SecondCountableTopology G] (K : CompactExhaustion G) :
    ∃ (b : ℕ → BruhatCompactTestIndex G)
      (D : LinearInductivePresentation (BruhatCompactTest G) (fun n => (b n).Space)),
      (∀ n, IsClosedEmbedding (D.transition (Nat.le_succ n))) ∧
      (∀ n, IsEmbedding (D.incl n)) ∧
      ∀ n, IsFrechetTVS (b n).Space := by
  let seq := compactTestIndex_cofinalSequence (G := G) K
  let b := seq.choose
  have hb := seq.choose_spec.1
  have hK := seq.choose_spec.2.1
  have hCov := seq.choose_spec.2.2
  let D := compactTestPresentation b hb hK hCov
  have hclosed (n : ℕ) : IsClosedEmbedding (D.transition (Nat.le_succ n)) :=
    (b n).transition_isClosedEmbedding (b (n + 1)) (hb (Nat.le_succ n)) (hK (Nat.le_succ n))
  exact ⟨b, D, hclosed, fun n => (b n).inclusion_isEmbedding,
    fun n => compactTestStage_isFrechet (b n)⟩

set_option maxHeartbeats 2500000 in
/-- Every bounded family is bounded in one compact-test stage, so the family
has both a fixed structural quotient and a common compact support. -/
theorem bruhatCompactTest_bounded_stage [SecondCountableTopology G] (K : CompactExhaustion G)
    (B : Set (BruhatCompactTest G)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ (i : BruhatCompactTestIndex G) (A : Set i.Space),
      Bornology.IsVonNBounded ℂ A ∧ i.inclusionCLM '' A = B := by
  let seq := compactTestIndex_cofinalSequence (G := G) K
  let b := seq.choose
  have hb := seq.choose_spec.1
  have hK := seq.choose_spec.2.1
  have hCov := seq.choose_spec.2.2
  let D := compactTestPresentation b hb hK hCov
  letI (n : ℕ) : ContinuousSMul ℂ (b n).Space :=
    (PolynormableSpace.withSeminorms ℂ (b n).Space).continuousSMul
  have hclosed (n : ℕ) : IsClosedEmbedding (D.transition (Nat.le_succ n)) :=
    (b n).transition_isClosedEmbedding (b (n + 1)) (hb (Nat.le_succ n)) (hK (Nat.le_succ n))
  obtain ⟨n, A, hA, he⟩ := (D.strict_bounded_iff hclosed (fun n => (b n).inclusion_isEmbedding)
    (fun L => (compactTest_continuous_of_cofinal b hCov L).mpr) B).mp hB
  exact ⟨b n, A, hA, he⟩

end

end Masullo
