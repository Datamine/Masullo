import StrictInductiveTensorStages
import StrictLimitCompleteness
import StrictStageTopology

open Filter Function Set Topology UniformSpace
open scoped TensorProduct

namespace Masullo

noncomputable section

private theorem exists_monotone_cofinal_nat {K : Type*} [Preorder K]
    [Nonempty K] [Countable K] [IsDirectedOrder K] :
    ∃ s : ℕ → K, Monotone s ∧ ∀ k, ∃ n, k ≤ s n := by
  obtain ⟨a, ha⟩ := exists_surjective_nat K
  let up (x y : K) := (exists_ge_ge x y).choose
  have hup (x y : K) : x ≤ up x y ∧ y ≤ up x y := (exists_ge_ge x y).choose_spec
  let s : ℕ → K := Nat.rec (a 0) (fun n x => up x (a (n+1)))
  refine ⟨s, monotone_nat_of_le_succ (fun n => (hup (s n) (a (n+1))).1), ?_⟩
  intro k
  obtain ⟨n, rfl⟩ := ha k
  cases n with
  | zero => exact ⟨0, le_rfl⟩
  | succ n => exact ⟨n+1, (hup (s n) (a (n+1))).2⟩

private theorem complete_of_countable_final_embeddings
    {K W : Type*} [Preorder K] [Nonempty K] [Countable K] [IsDirectedOrder K]
    {V : K → Type*} [AddCommGroup W] [Module ℂ W] [UniformSpace W]
    [IsUniformAddGroup W] [PolynormableSpace ℂ W]
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, UniformSpace (V i)]
    [∀ i, IsUniformAddGroup (V i)] [∀ i, CompleteSpace (V i)]
    (k : ∀ i, V i →L[ℂ] W) (emb : ∀ i, IsEmbedding (k i))
    (t : ∀ i j, i ≤ j → V i →L[ℂ] V j)
    (ht : ∀ i j hij (x : V i), k j (t i j hij x) = k i x)
    (hs : ∀ x : W, ∃ i, x ∈ range (k i))
    (hfinal : (inferInstance : TopologicalSpace W) =
      locallyConvexFinalTopology (fun i => (k i).toLinearMap)) : CompleteSpace W := by
  obtain ⟨a, ha, hcof⟩ := exists_monotone_cofinal_nat (K := K)
  let D : LinearInductivePresentation W (fun n => V (a n)) :=
    { incl := fun n => k (a n)
      transition := fun {m n} h => t (a m) (a n) (ha h)
      injective_incl := fun n => (emb (a n)).injective
      incl_transition := fun {m n} h x => ht (a m) (a n) (ha h) x
      exhaust := fun x => by
        obtain ⟨i, z, rfl⟩ := hs x
        obtain ⟨n, hi⟩ := hcof i
        exact ⟨n, t i (a n) hi z, ht i (a n) hi z⟩
      continuous_limit := fun l => by
        constructor
        · intro hl n
          exact hl.comp (k (a n)).continuous
        · intro hl
          have hc i : Continuous (l.comp (k i).toLinearMap) := by
            obtain ⟨n, hi⟩ := hcof i
            exact ((hl n).comp (t i (a n) hi).continuous).congr (fun x => congrArg l (ht i (a n) hi x))
          exact (congrArg (fun T : TopologicalSpace W => Continuous[T, inferInstance] l) hfinal).mpr
            ((locallyConvexFinal_continuous_iff (fun i => (k i).toLinearMap) l).mpr hc) }
  have hc (n : ℕ) : @CompleteSpace (V (a n)) (IsTopologicalAddGroup.rightUniformSpace (V (a n))) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hlim (p : Seminorm ℂ W) (hp : ∀ n, Continuous (p.comp (D.incl n).toLinearMap)) :
      Continuous p := by
    have hcont i : Continuous (p.comp (k i).toLinearMap) := by
      obtain ⟨n, hi⟩ := hcof i
      exact ((hp n).comp (t i (a n) hi).continuous).congr (fun x => congrArg p (ht i (a n) hi x))
    exact (congrArg (fun T : TopologicalSpace W => Continuous[T, inferInstance] p) hfinal).mpr
      (locallyConvexFinal_seminorm_continuous (fun i => (k i).toLinearMap) p hcont)
  have H := D.complete_of_strict hc (fun n => emb (a n)) hlim
  rwa [IsUniformAddGroup.rightUniformSpace_eq] at H

section TensorLimits

variable {I J E F : Type*} [Preorder I] [Preorder J]
  [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J]
  {A : I → Type*} {B : J → Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalAddGroup (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, TopologicalSpace (B j)]
  [∀ j, IsTopologicalAddGroup (B j)]

variable (u : ∀ i, A i →L[ℂ] E) (v : ∀ j, B j →L[ℂ] F)

variable (f : ∀ i i', i ≤ i' → A i →L[ℂ] A i')
  (g : ∀ j j', j ≤ j' → B j →L[ℂ] B j')
  (hf : ∀ i i' h, (u i').comp (f i i' h) = u i)
  (hg : ∀ j j' h, (v j').comp (g j j' h) = v j)

abbrev CompletedInductiveTensorStage (p : I × J) :=
  (inductiveTensorModuleStructure (A p.1) (B p.2)).Completed

def completedTensorStageTransition (p q : I × J) (h : p ≤ q) :
    CompletedInductiveTensorStage (A := A) (B := B) p →L[ℂ]
      CompletedInductiveTensorStage (A := A) (B := B) q :=
  completedInductiveTensor_map (f p.1 q.1 h.1) (g p.2 q.2 h.2)

omit [Nonempty I] [Nonempty J] [IsDirectedOrder I] [IsDirectedOrder J] in
include hf hg in
private theorem completedTensorStage_compatible (p q : I × J) (h : p ≤ q)
    (x : CompletedInductiveTensorStage (A := A) (B := B) p) :
    completedInductiveTensor_map (u q.1) (v q.2) (completedTensorStageTransition f g p q h x) =
      completedInductiveTensor_map (u p.1) (v p.2) x := by
  have he := completedInductiveTensor_map_comp (f p.1 q.1 h.1) (g p.2 q.2 h.2) (u q.1) (v q.2)
  rw [hf p.1 q.1 h.1, hg p.2 q.2 h.2] at he
  exact DFunLike.congr_fun he x

local instance : IsDirectedOrder (I × J) := ⟨fun p q => by
  obtain ⟨i, hp, hq⟩ := exists_ge_ge p.1 q.1
  obtain ⟨j, hp', hq'⟩ := exists_ge_ge p.2 q.2
  exact ⟨(i, j), ⟨hp, hp'⟩, ⟨hq, hq'⟩⟩⟩

include hf hg in
theorem completedTensorStageSpan_exhaust
    (x : completedTensorStageSpan u v) :
    ∃ p : I × J, x ∈ range (completedTensorStageIntoSpan u v p.1 p.2) := by
  let V (p : I × J) := (completedInductiveTensor_map (u p.1) (v p.2)).toLinearMap.range
  have hm : Monotone V := fun p q h _ ⟨z, hz⟩ =>
    ⟨completedTensorStageTransition f g p q h z,
      (completedTensorStage_compatible u v f g hf hg p q h z).trans hz⟩
  have hsub : completedTensorStageSpan u v ≤ ⨆ p, V p := by
    refine Submodule.span_le.mpr ?_
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    exact le_iSup V (i, j) hj
  have hx : x.val ∈ (↑(⨆ p, V p) : Set _) := hsub x.property
  have hdir : Directed (· ≤ ·) V := fun p q => by
    obtain ⟨r, hp, hq⟩ := exists_ge_ge p q
    exact ⟨r, hm hp, hm hq⟩
  rw [Submodule.coe_iSup_of_directed V hdir] at hx
  obtain ⟨p, z, hz⟩ := mem_iUnion.mp hx
  exact ⟨p, z, Subtype.ext hz⟩

include hf hg in
/-- Under the strict stage hypotheses, the completed stage images exhaust
the full inductive tensor completion. -/
theorem completedTensorStageSpan_eq_top_of_strict [Countable I] [Countable J]
    [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap))
    (hue : ∀ i, IsEmbedding (u i)) (hve : ∀ j, IsEmbedding (v j))
    (ht : ∀ i j, inductiveTensorTopology (A i) (B j) = injectiveTensorTopology (A i) (B j)) :
    completedTensorStageSpan u v = ⊤ := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : T0Space D.Completed := Completion.t0Space X
  letI : PolynormableSpace ℂ D.Completed := polynormableSpace_completion
  let S := completedTensorStageSpan u v
  letI : IsUniformAddGroup S :=
    IsUniformInducing.isUniformAddGroup S.subtype isUniformEmbedding_subtype_val.isUniformInducing
  let W (p : I × J) := CompletedInductiveTensorStage (A := A) (B := B) p
  let k (p : I × J) : W p →L[ℂ] S := completedTensorStageIntoSpan u v p.1 p.2
  letI : ∀ p : I × J, IsUniformAddGroup (W p) := fun p => by
    let P := inductiveTensorModuleStructure (A p.1) (B p.2)
    letI : UniformSpace (A p.1 ⊗[ℂ] B p.2) := P.uniformSpace
    letI : IsUniformAddGroup (A p.1 ⊗[ℂ] B p.2) := P.uniformGroup
    exact Completion.isUniformAddGroup
  letI : ∀ p : I × J, CompleteSpace (W p) := fun p =>
    @Completion.completeSpace (A p.1 ⊗[ℂ] B p.2)
      (inductiveTensorModuleStructure (A p.1) (B p.2)).uniformSpace
  have hk (p : I × J) : IsEmbedding (k p) := by
    apply IsEmbedding.of_comp (k p).continuous continuous_subtype_val
    exact completedInductiveTensor_map_isEmbedding_of_equal (u p.1) (v p.2)
      (hue p.1) (hve p.2) (ht p.1 p.2)
  have hn (p q : I × J) (h : p ≤ q) (z : W p) :
      k q (completedTensorStageTransition f g p q h z) = k p z :=
    Subtype.ext (completedTensorStage_compatible u v f g hf hg p q h z)
  letI : CompleteSpace S := complete_of_countable_final_embeddings k hk
    (completedTensorStageTransition f g) hn (completedTensorStageSpan_exhaust u v f g hf hg)
    (completedTensorStageSpan_topology u v hu hv hE hF)
  have hc : IsComplete (S : Set D.Completed) := by
    have hh : IsComplete (range (fun x : S => (x : D.Completed))) :=
      isUniformEmbedding_subtype_val.isUniformInducing.isComplete_range
    rw [show range (fun x : S => (x : D.Completed)) = (S : Set D.Completed) from Subtype.range_coe] at hh
    exact hh
  have hd : Dense (S : Set D.Completed) := completedInductiveTensor_stageSpan_dense u v hu hv
  exact SetLike.coe_injective (hc.isClosed.closure_eq.symm.trans hd.closure_eq)

section DirectLimit

variable [DecidableEq (I × J)]

abbrev CompletedInductiveTensorDirectLimit :=
  Module.DirectLimit (CompletedInductiveTensorStage (A := A) (B := B))
    (fun p q h => (completedTensorStageTransition f g p q h).toLinearMap)

abbrev completedInductiveTensorDirectLimitTopology :
    TopologicalSpace (CompletedInductiveTensorDirectLimit f g) :=
  locallyConvexFinalTopology (Module.DirectLimit.of ℂ (I × J)
    (CompletedInductiveTensorStage (A := A) (B := B))
    (fun p q h => (completedTensorStageTransition f g p q h).toLinearMap))

include hf hg in
/-- The strict countable stage system gives the canonical completed
inductive tensor isomorphism in the final clause of (C.2.3.27). -/
theorem exists_completedInductiveTensor_strictLimitEquiv [Countable I] [Countable J]
    [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (hu : ∀ x : E, ∃ i, x ∈ range (u i)) (hv : ∀ y : F, ∃ j, y ∈ range (v j))
    (hE : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun i => (u i).toLinearMap))
    (hF : ‹TopologicalSpace F› = locallyConvexFinalTopology (fun j => (v j).toLinearMap))
    (hue : ∀ i, IsEmbedding (u i)) (hve : ∀ j, IsEmbedding (v j))
    (ht : ∀ i j, inductiveTensorTopology (A i) (B j) = injectiveTensorTopology (A i) (B j)) :
    letI : TopologicalSpace (CompletedInductiveTensorDirectLimit f g) :=
      completedInductiveTensorDirectLimitTopology f g
    ∃ L : CompletedInductiveTensorDirectLimit f g ≃L[ℂ]
        (inductiveTensorModuleStructure E F).Completed,
      ∀ (p : I × J) (z : CompletedInductiveTensorStage (A := A) (B := B) p),
        L (Module.DirectLimit.of ℂ (I × J) _ (fun p q h =>
          (completedTensorStageTransition f g p q h).toLinearMap) p z) =
        completedInductiveTensor_map (u p.1) (v p.2) z := by
  let X := E ⊗[ℂ] F
  let D := inductiveTensorModuleStructure E F
  letI : UniformSpace X := D.uniformSpace
  letI : IsUniformAddGroup X := D.uniformGroup
  letI : UniformContinuousConstSMul ℂ X := D.uniformConstSmul
  letI : PolynormableSpace ℂ X := inductiveTensor_withSeminorms.toPolynormableSpace
  letI : IsUniformAddGroup D.Completed := Completion.isUniformAddGroup
  letI : PolynormableSpace ℂ D.Completed := polynormableSpace_completion
  let W (p : I × J) := CompletedInductiveTensorStage (A := A) (B := B) p
  letI : ∀ p : I × J, IsTopologicalAddGroup (W p) := fun p => by
    let P := inductiveTensorModuleStructure (A p.1) (B p.2)
    letI : UniformSpace (A p.1 ⊗[ℂ] B p.2) := P.uniformSpace
    letI : IsUniformAddGroup (A p.1 ⊗[ℂ] B p.2) := P.uniformGroup
    letI : IsUniformAddGroup P.Completed := Completion.isUniformAddGroup
    infer_instance
  let t (p q : I × J) (h : p ≤ q) := (completedTensorStageTransition f g p q h).toLinearMap
  let L := CompletedInductiveTensorDirectLimit f g
  letI : TopologicalSpace L := completedInductiveTensorDirectLimitTopology f g
  let i := Module.DirectLimit.of ℂ (I × J) W t
  let J₀ (p : I × J) := completedInductiveTensor_map (u p.1) (v p.2)
  let Q : L →ₗ[ℂ] D.Completed := Module.DirectLimit.lift ℂ _ W t
    (fun p => (J₀ p).toLinearMap) (completedTensorStage_compatible u v f g hf hg)
  have hQ (p : I × J) (z : W p) : Q (i p z) = J₀ p z :=
    Module.DirectLimit.lift_of _ _ z
  let S := completedTensorStageSpan u v
  have htop : S = ⊤ := completedTensorStageSpan_eq_top_of_strict u v f g hf hg
    hu hv hE hF hue hve ht
  have hQs : Surjective Q := by
    intro z
    let w : S := ⟨z, htop.symm ▸ Submodule.mem_top⟩
    obtain ⟨p, x, hx⟩ := completedTensorStageSpan_exhaust u v f g hf hg w
    exact ⟨i p x, (hQ p x).trans (congrArg Subtype.val hx)⟩
  have hQi : Injective Q := by
    apply (injective_iff_map_eq_zero Q).mpr
    intro z hz
    obtain ⟨p, x, rfl⟩ := Module.DirectLimit.exists_of z
    have he : J₀ p x = J₀ p 0 := (hQ p x).symm.trans (hz.trans (map_zero (J₀ p)).symm)
    have hx := (completedInductiveTensor_map_isEmbedding_of_equal (u p.1) (v p.2)
      (hue p.1) (hve p.2) (ht p.1 p.2)).injective he
    exact hx.symm ▸ map_zero (i p)
  let e := LinearEquiv.ofBijective Q ⟨hQi, hQs⟩
  have hQc : Continuous Q :=
    (locallyConvexFinal_continuous_iff i Q).mpr fun p =>
      (J₀ p).continuous.congr fun z => (hQ p z).symm
  let k (p : I × J) := (completedTensorStageIntoSpan u v p.1 p.2).toLinearMap
  let R : S →ₗ[ℂ] L := e.symm.toLinearMap.comp S.subtype
  letI : PolynormableSpace ℂ L := (locallyConvexFinal_withSeminorms i).toPolynormableSpace
  have hR : Continuous R := by
    have hfinal : (inferInstance : TopologicalSpace S) = locallyConvexFinalTopology k :=
      completedTensorStageSpan_topology u v hu hv hE hF
    apply (congrArg (fun T : TopologicalSpace S => Continuous[T, inferInstance] R) hfinal).mpr
    apply (locallyConvexFinal_continuous_iff k R).mpr
    intro p
    apply (locallyConvexFinal_stage_continuous i p).congr
    intro z
    change i p z = e.symm (J₀ p z)
    rw [← hQ p]
    exact (e.symm_apply_apply (i p z)).symm
  let w (x : D.Completed) : S := ⟨x, htop.symm ▸ Submodule.mem_top⟩
  have hes : Continuous e.symm := hR.comp (continuous_id.subtype_mk _ : Continuous w)
  exact ⟨⟨e, hQc, hes⟩, hQ⟩

end DirectLimit
end TensorLimits

section StageEmbeddings

variable {I : Type*} [Preorder I] [DecidableEq I] [Nonempty I] [IsDirectedOrder I]
  {A : I → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalAddGroup (A i)] [∀ i, PolynormableSpace ℂ (A i)]
  (f : ∀ i j, i ≤ j → A i →L[ℂ] A j) [DirectedSystem A (f · · ·)]

/-- A cofinal sequence of transitions identifies each original strict stage
with its image in the locally convex limit. -/
private theorem strictFinalDirectLimit_stage_isEmbedding
    (a : ℕ → I) (ha : Monotone a) (hcof : ∀ i, ∃ n, i ≤ a n)
    (hf : ∀ i j h, IsEmbedding (f i j h)) :
    let f₀ := fun i j h => (f i j h).toLinearMap
    let k := Module.DirectLimit.of ℂ I A f₀
    letI : TopologicalSpace (Module.DirectLimit A f₀) := locallyConvexFinalTopology k
    ∀ i, IsEmbedding (k i) := by
  dsimp only
  let f₀ := fun i j h => (f i j h).toLinearMap
  letI : DirectedSystem A (f₀ · · ·) := ‹DirectedSystem A (f · · ·)›
  let k := Module.DirectLimit.of ℂ I A f₀
  let E := Module.DirectLimit A f₀
  letI : TopologicalSpace E := locallyConvexFinalTopology k
  letI : IsTopologicalAddGroup E := (locallyConvexFinal_withSeminorms k).topologicalAddGroup
  let u (i : I) : A i →L[ℂ] E := ⟨k i, locallyConvexFinal_stage_continuous k i⟩
  have hu (i : I) : Injective (u i) := by
    intro x y h
    have h₀ : k i x = k i y := h
    obtain ⟨j, h, he⟩ := Module.DirectLimit.exists_eq_of_of_eq h₀
    exact (hf i j h).injective he
  have ht (i j : I) (h : i ≤ j) (x : A i) : u j (f i j h x) = u i x :=
    Module.DirectLimit.of_f (f := f₀) (hij := h) (x := x)
  let D : LinearInductivePresentation E (fun n => A (a n)) :=
    { incl := fun n => u (a n)
      transition := fun {m n} h => f (a m) (a n) (ha h)
      injective_incl := fun n => hu (a n)
      incl_transition := fun {m n} h x => ht (a m) (a n) (ha h) x
      exhaust := fun x => by
        obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of (f := f₀) x
        obtain ⟨n, hn⟩ := hcof i
        exact ⟨n, f i (a n) hn y, ht i (a n) hn y⟩
      continuous_limit := fun l => by
        constructor
        · intro hc n
          exact hc.comp (u (a n)).continuous
        · intro hc
          apply (locallyConvexFinal_continuous_iff k l).mpr
          intro i
          obtain ⟨n, hn⟩ := hcof i
          exact ((hc n).comp (f i (a n) hn).continuous).congr (fun x => congrArg l (ht i (a n) hn x)) }
  have hlim (p : Seminorm ℂ E) (hp : ∀ n, Continuous (p.comp (D.incl n).toLinearMap)) :
      Continuous p := by
    apply locallyConvexFinal_seminorm_continuous k p
    intro i
    obtain ⟨n, hn⟩ := hcof i
    exact ((hp n).comp (f i (a n) hn).continuous).congr (fun x => congrArg p (ht i (a n) hn x))
  intro i
  obtain ⟨n, hn⟩ := hcof i
  have hD := D.strict_incl_isEmbedding hlim (fun n => hf (a n) (a (n+1)) (ha (Nat.le_succ n))) n
  have hEq : (u (a n) : A (a n) → E) ∘ f i (a n) hn = u i :=
    funext (ht i (a n) hn)
  have he := hD.comp (hf i (a n) hn)
  rw [hEq] at he
  exact he

end StageEmbeddings

section NuclearLimits

universe u v

variable {I J : Type*} [Preorder I] [Preorder J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] [Countable I] [Countable J] [IsDirectedOrder I] [IsDirectedOrder J]
  {A : I → Type u} {B : J → Type v}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalAddGroup (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, TopologicalSpace (B j)]
  [∀ j, IsTopologicalAddGroup (B j)] [∀ j, T2Space (B j)]

variable (f : ∀ i i', i ≤ i' → A i →L[ℂ] A i')
  (g : ∀ j j', j ≤ j' → B j →L[ℂ] B j')
  [DirectedSystem A (f · · ·)] [DirectedSystem B (g · · ·)]

/-- The strict nuclear Fréchet case of Proposition C.2.3.13(2).
The map extends the pairwise completed tensor maps of the original stages. -/
theorem strictNuclearFrechet_completedInductiveTensor_directLimit
    (hA : ∀ i, IsFrechetTVS (A i)) (hB : ∀ j, IsFrechetTVS (B j))
    (hN : ∀ i, NuclearLocallyConvex.{v} (A i))
    (hfe : ∀ i i' h, IsEmbedding (f i i' h))
    (hge : ∀ j j' h, IsEmbedding (g j j' h)) :
    let f₀ := fun i i' h => (f i i' h).toLinearMap
    let g₀ := fun j j' h => (g j j' h).toLinearMap
    let a := Module.DirectLimit.of ℂ I A f₀
    let b := Module.DirectLimit.of ℂ J B g₀
    let E := Module.DirectLimit A f₀
    let F := Module.DirectLimit B g₀
    letI : TopologicalSpace E := locallyConvexFinalTopology a
    letI : TopologicalSpace F := locallyConvexFinalTopology b
    letI : TopologicalSpace (CompletedInductiveTensorDirectLimit f g) :=
      completedInductiveTensorDirectLimitTopology f g
    letI : IsTopologicalAddGroup E := (locallyConvexFinal_withSeminorms a).topologicalAddGroup
    letI : IsTopologicalAddGroup F := (locallyConvexFinal_withSeminorms b).topologicalAddGroup
    ∃ L : CompletedInductiveTensorDirectLimit f g ≃L[ℂ]
        (inductiveTensorModuleStructure E F).Completed,
      ∀ (p : I × J) (z : CompletedInductiveTensorStage (A := A) (B := B) p),
        L (Module.DirectLimit.of ℂ (I × J) _ (fun p q h =>
          (completedTensorStageTransition f g p q h).toLinearMap) p z) =
        completedInductiveTensor_map ⟨a p.1, locallyConvexFinal_stage_continuous a p.1⟩
          ⟨b p.2, locallyConvexFinal_stage_continuous b p.2⟩ z := by
  dsimp only
  let f₀ := fun i i' h => (f i i' h).toLinearMap
  let g₀ := fun j j' h => (g j j' h).toLinearMap
  let a := Module.DirectLimit.of ℂ I A f₀
  let b := Module.DirectLimit.of ℂ J B g₀
  let E := Module.DirectLimit A f₀
  let F := Module.DirectLimit B g₀
  letI : TopologicalSpace E := locallyConvexFinalTopology a
  letI : TopologicalSpace F := locallyConvexFinalTopology b
  letI : IsTopologicalAddGroup E := (locallyConvexFinal_withSeminorms a).topologicalAddGroup
  letI : IsTopologicalAddGroup F := (locallyConvexFinal_withSeminorms b).topologicalAddGroup
  letI : PolynormableSpace ℂ E := (locallyConvexFinal_withSeminorms a).toPolynormableSpace
  letI : PolynormableSpace ℂ F := (locallyConvexFinal_withSeminorms b).toPolynormableSpace
  let u (i : I) : A i →L[ℂ] E := ⟨a i, locallyConvexFinal_stage_continuous a i⟩
  let v (j : J) : B j →L[ℂ] F := ⟨b j, locallyConvexFinal_stage_continuous b j⟩
  have hf (i i' : I) (h : i ≤ i') : (u i').comp (f i i' h) = u i :=
    ContinuousLinearMap.ext (fun x => Module.DirectLimit.of_f (f := f₀) (hij := h) (x := x))
  have hg (j j' : J) (h : j ≤ j') : (v j').comp (g j j' h) = v j :=
    ContinuousLinearMap.ext (fun x => Module.DirectLimit.of_f (f := g₀) (hij := h) (x := x))
  letI : ∀ i, PolynormableSpace ℂ (A i) := fun i => (hA i).choose_spec.1
  letI : ∀ j, PolynormableSpace ℂ (B j) := fun j => (hB j).choose_spec.1
  obtain ⟨α, hα, hαc⟩ := exists_monotone_cofinal_nat (K := I)
  obtain ⟨β, hβ, hβc⟩ := exists_monotone_cofinal_nat (K := J)
  have hue : ∀ i, IsEmbedding (u i) := strictFinalDirectLimit_stage_isEmbedding f α hα hαc hfe
  have hve : ∀ j, IsEmbedding (v j) := strictFinalDirectLimit_stage_isEmbedding g β hβ hβc hge
  exact exists_completedInductiveTensor_strictLimitEquiv u v f g hf hg
    Module.DirectLimit.exists_of Module.DirectLimit.exists_of rfl rfl hue hve
    (fun i j => nuclearFrechet_inductiveTensorTopology_eq_injective (hA i) (hB j) (hN i))

end NuclearLimits

end
end Masullo
