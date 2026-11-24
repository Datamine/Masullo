import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Function Set Topology
open scoped Pointwise

namespace Masullo

noncomputable section

/-- A countable family of closed sets of empty interior can have dense union.
Density alone therefore cannot supply the Baire step for a graph projection. -/
theorem dense_countable_union_with_empty_interiors :
    ∃ S : ℚ → Set ℝ, (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧ Dense (⋃ n, S n) := by
  refine ⟨fun n => {(n : ℝ)}, fun n => ⟨isClosed_singleton, interior_singleton _⟩, ?_⟩
  have he : (⋃ n : ℚ, ({(n : ℝ)} : Set ℝ)) = range ((↑) : ℚ → ℝ) := by
    ext x
    simp only [mem_iUnion, mem_singleton_iff, mem_range, eq_comm]
  rw [he]
  exact Rat.denseRange_cast

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y]
variable [ContinuousSMul ℂ X] [ContinuousSMul ℂ Y]

private theorem image_closure_mem_nhds_of_nonmeagre_range (p : X →L[ℂ] Y)
    (h : ¬ IsMeagre (range p)) {U : Set X} (hU : U ∈ 𝓝 0) :
    closure (p '' U) ∈ 𝓝 0 := by
  obtain ⟨V, hV, -, hsymm, hVU⟩ := exists_closed_nhds_zero_neg_eq_add_subset hU
  let c : ℂ := 1 / 2
  have hc : c ≠ 0 := by norm_num [c]
  have hsmall : ‖c‖ < 1 := by norm_num [c, norm_div, Complex.norm_ofNat]
  have hcover : range p ⊆ ⋃ n : ℕ, (c ^ n)⁻¹ • (p '' V) := by
    rintro _ ⟨x, rfl⟩
    have ht : Tendsto (fun n : ℕ => c ^ n • x) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).zero_smul_const x
    obtain ⟨n, hn⟩ := (ht.eventually_mem hV).exists
    refine mem_iUnion.mpr ⟨n, ⟨p (c ^ n • x), ⟨_, hn, rfl⟩, ?_⟩⟩
    change (c ^ n)⁻¹ • p (c ^ n • x) = p x
    rw [map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]
  have hVmeagre : ¬ IsMeagre (p '' V) := by
    intro hm
    apply h
    refine (isMeagre_iUnion fun n => ?_).mono hcover
    let e : Y ≃ₜ Y := Homeomorph.smulOfNeZero (c ^ n) (pow_ne_zero _ hc)
    have hEq : (c ^ n)⁻¹ • (p '' V) = e ⁻¹' (p '' V) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change c ^ n • ((c ^ n)⁻¹ • z) ∈ p '' V
        rwa [smul_inv_smul₀ (pow_ne_zero _ hc)]
      · intro hy
        change c ^ n • y ∈ p '' V at hy
        exact ⟨c ^ n • y, hy, inv_smul_smul₀ (pow_ne_zero _ hc) _⟩
    rw [hEq]
    exact hm.preimage_of_isOpenMap e.continuous e.isOpenMap
  have hn : (interior (closure (p '' V))).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    exact fun he => hVmeagre ((show IsNowhereDense (p '' V) from he).isMeagre)
  obtain ⟨y, hy⟩ := hn
  have hb : (fun z : Y => z + y) ⁻¹' interior (closure (p '' V)) ∈ 𝓝 0 := by
    apply (isOpen_interior.preimage (continuous_id.add continuous_const)).mem_nhds
    simpa using hy
  refine mem_of_superset hb fun z hz => ?_
  have hz' : z + y ∈ closure (p '' V) := interior_subset hz
  have hcsub : Continuous (fun a : Y × Y => a.1 - a.2) := continuous_fst.sub continuous_snd
  have hk : (z + y, y) ∈ closure ((p '' V) ×ˢ (p '' V)) := by
    rw [closure_prod_eq]
    exact ⟨hz', interior_subset hy⟩
  have hz'' := image_closure_subset_closure_image hcsub
    (mem_image_of_mem (fun a : Y × Y => a.1 - a.2) hk)
  have hincl : (fun a : Y × Y => a.1 - a.2) '' ((p '' V) ×ˢ (p '' V)) ⊆ p '' U := by
    rintro _ ⟨⟨_, _⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
    refine ⟨a - b, hVU ⟨a, ha, -b, ?_, (sub_eq_add_neg a b).symm⟩, map_sub p a b⟩
    rw [← hsymm]
    exact neg_mem_neg.mpr hb
  exact closure_mono hincl (by simpa using hz'')

variable [FirstCountableTopology X]

/-- A continuous linear map from a complete metrizable topological vector
space onto a nonmeagre range is an open surjection. -/
private theorem open_surjective_of_nonmeagre_range
    [@CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X)] [T2Space Y]
    (p : X →L[ℂ] Y) (h : ¬ IsMeagre (range p)) : IsOpenMap p ∧ Surjective p := by
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hnear (U : Set X) (hU : U ∈ 𝓝 0) : closure (p '' U) ∈ 𝓝 0 :=
    image_closure_mem_nhds_of_nonmeagre_range p h hU
  have himage (U : Set X) (hU : U ∈ 𝓝 0) : p '' U ∈ 𝓝 0 := by
    obtain ⟨S, hS, hclosed, hSU⟩ := exists_mem_nhds_isClosed_subset hU
    obtain ⟨u, hu, hadd⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero X
    obtain ⟨k, -, hk⟩ := hu.toHasBasis.mem_iff.mp hS
    let v : ℕ → Set X := fun n => u (k + n)
    have hv (n : ℕ) : v n ∈ 𝓝 (0 : X) := hu.mem _
    have hvadd (n : ℕ) : v (n + 1) + v (n + 1) ⊆ v n := hadd (k + n)
    refine mem_of_superset (hnear (v 1) (hv 1)) fun y hy => ?_
    have step (n : ℕ) (s : X) (hs : y - p s ∈ closure (p '' v (n + 1))) :
        ∃ a ∈ v (n + 1), y - p (s + a) ∈ closure (p '' v (n + 2)) := by
      let W := interior (closure (p '' v (n + 2)))
      have hW : 0 ∈ W := mem_interior_iff_mem_nhds.mpr (hnear _ (hv (n + 2)))
      have hopen : IsOpen ((fun t : Y => (y - p s) - t) ⁻¹' W) :=
        isOpen_interior.preimage (continuous_const.sub continuous_id)
      have hw : y - p s ∈ (fun t : Y => (y - p s) - t) ⁻¹' W := by simpa using hW
      obtain ⟨_, ht, a, ha, rfl⟩ := mem_closure_iff.mp hs _ hopen hw
      refine ⟨a, ha, ?_⟩
      have he : y - p (s + a) = (y - p s) - p a := by rw [map_add, sub_add_eq_sub_sub]
      rw [he]
      exact interior_subset ht
    choose next hnext hres using step
    let q : ∀ n : ℕ, {s : X // y - p s ∈ closure (p '' v (n + 1))} :=
      Nat.rec ⟨0, by simpa using hy⟩
        (fun n s => ⟨s.val + next n s.val s.property, hres n s.val s.property⟩)
    let s : ℕ → X := fun n => (q n).val
    have hs0 : s 0 = 0 := rfl
    have hstep (n : ℕ) : s (n + 1) - s n ∈ v (n + 1) := by
      change s n + next n (s n) (q n).property - s n ∈ _
      simpa only [add_sub_cancel_left] using hnext n (s n) (q n).property
    have hdiff {m n : ℕ} (hmn : m ≤ n) : s n - s m ∈ v m := by
      exact Nat.decreasingInduction'
        (P := fun j => s n - s j ∈ v j)
        (fun m _ _ ih => hvadd m ⟨_, ih, _, hstep m, sub_add_sub_cancel _ _ _⟩)
        hmn (by simpa using mem_of_mem_nhds (hv n))
    have huX : (uniformity X).HasBasis (fun _ : ℕ => True)
        (fun i => {a : X × X | a.1 - a.2 ∈ u i}) := by
      rw [uniformity_eq_comap_nhds_zero_swapped X]
      exact hu.toHasBasis.comap _
    have hCauchy : CauchySeq s := by
      rw [huX.cauchySeq_iff']
      simp only [mem_ofPred_eq, forall_true_left]
      exact fun i => ⟨i, fun n hn => hu.antitone (Nat.le_add_left i k) (hdiff hn)⟩
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hxS : x ∈ S := hclosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => hk (by simpa [hs0, v] using hdiff (Nat.zero_le n)))
    have ht : Tendsto (fun n => y - p (s n)) atTop (𝓝 0) := by
      apply tendsto_def.mpr
      intro W hW
      obtain ⟨W', hW', hWclosed, hWW⟩ := exists_mem_nhds_isClosed_subset hW
      have hpre : p ⁻¹' W' ∈ 𝓝 0 := by
        apply p.continuous.continuousAt.preimage_mem_nhds
        simpa only [map_zero] using hW'
      obtain ⟨i, -, hi⟩ := hu.toHasBasis.mem_iff.mp hpre
      filter_upwards [eventually_ge_atTop i] with n hn
      exact hWW (hWclosed.closure_subset_iff.mpr
        (by
          rintro _ ⟨a, ha, rfl⟩
          apply hi
          exact hu.antitone (by dsimp [v] at ha; omega) ha) (q n).property)
    have ht' : Tendsto (fun n => y - p (s n)) atTop (𝓝 (y - p x)) :=
      tendsto_const_nhds.sub ((p.continuous.tendsto x).comp hx)
    exact ⟨x, hSU hxS, (sub_eq_zero.mp (tendsto_nhds_unique ht' ht)).symm⟩
  have hopen : IsOpenMap p := by
    apply (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := p)).mpr
    exact Filter.le_map_iff.mpr himage
  refine ⟨hopen, fun y => ?_⟩
  have hy : Tendsto (fun n : ℕ => (1 / 2 : ℂ) ^ n • y) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num [norm_div, Complex.norm_ofNat])).zero_smul_const y
  obtain ⟨n, x, -, he⟩ := (hy.eventually_mem (himage univ univ_mem)).exists
  refine ⟨(((1 / 2 : ℂ) ^ n)⁻¹) • x, ?_⟩
  rw [map_smul, he, inv_smul_smul₀ (pow_ne_zero _ (by norm_num))]

/-- A surjective continuous linear map from a complete metrizable complex TVS
to a Hausdorff Baire complex TVS is open. -/
theorem isOpenMap_of_surjective_complete_baire
    [@CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X)] [T2Space Y] [BaireSpace Y]
    (p : X →L[ℂ] Y) (hp : Surjective p) : IsOpenMap p :=
  (open_surjective_of_nonmeagre_range p (by
    rw [hp.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ ⟨0, mem_univ _⟩)).1

section Factorization

variable {A E H : Type*}
variable [AddCommGroup A] [AddCommGroup E] [AddCommGroup H]
variable [Module ℂ A] [Module ℂ E] [Module ℂ H]
variable [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace H]
variable [IsTopologicalAddGroup E]

private def coincidenceGraph (u : A →L[ℂ] E) (j : H →L[ℂ] E) :
    Submodule ℂ (A × H) :=
  (u.comp (ContinuousLinearMap.fst ℂ A H) - j.comp (ContinuousLinearMap.snd ℂ A H)).toLinearMap.ker

private def coincidenceProjection (u : A →L[ℂ] E) (j : H →L[ℂ] E) :
    coincidenceGraph u j →L[ℂ] A :=
  (ContinuousLinearMap.fst ℂ A H).comp (coincidenceGraph u j).subtypeL

private theorem coincidence_eq (u : A →L[ℂ] E) (j : H →L[ℂ] E)
    (z : coincidenceGraph u j) : u z.val.1 = j z.val.2 :=
  sub_eq_zero.mp z.property

end Factorization

section ClosedGraph

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [UniformSpace A] [UniformSpace B] [IsUniformAddGroup A] [IsUniformAddGroup B]
  [ContinuousSMul ℂ A] [ContinuousSMul ℂ B] [CompleteSpace A] [CompleteSpace B]
  [T2Space A] [FirstCountableTopology A] [FirstCountableTopology B]

/-- A linear map with closed graph between complex Fréchet spaces is continuous. -/
theorem frechet_continuous_of_closed_graph (L : A →ₗ[ℂ] B)
    (hL : IsClosed (L.graph : Set (A × B))) : Continuous L := by
  let P := L.graph
  letI : IsClosed (P : Set (A × B)) := hL
  letI : IsUniformAddGroup P := P.toAddSubgroup.isUniformAddGroup
  letI : FirstCountableTopology P := IsInducing.subtypeVal.firstCountableTopology
  letI : @CompleteSpace P (IsTopologicalAddGroup.rightUniformSpace P) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  letI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace A := BaireSpace.of_completelyPseudoMetrizable
  let p : P →L[ℂ] A := (ContinuousLinearMap.fst ℂ A B).comp P.subtypeL
  have hp : Bijective p := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact Prod.ext h (((L.mem_graph_iff x.val).mp x.property).trans
        ((congrArg L h).trans ((L.mem_graph_iff y.val).mp y.property).symm))
    · intro x
      exact ⟨⟨(x, L x), (L.mem_graph_iff _).mpr rfl⟩, rfl⟩
  let e := LinearEquiv.ofBijective p.toLinearMap hp
  have he : Continuous e.symm := e.toEquiv.continuous_symm_iff.mpr
    (isOpenMap_of_surjective_complete_baire p hp.2)
  have hEq : (L : A → B) = fun x => (e.symm x).val.2 := by
    funext x
    have h := (L.mem_graph_iff _).mp (e.symm x).property
    exact (congrArg L (e.apply_symm_apply x)).symm.trans h.symm
  rw [hEq]
  exact (continuous_snd.comp continuous_subtype_val).comp he

end ClosedGraph

section FrechetStages

variable {A E : Type*} {F : ℕ → Type*}
variable [UniformSpace A] [AddCommGroup A] [Module ℂ A] [IsUniformAddGroup A]
variable [ContinuousSMul ℂ A] [CompleteSpace A] [T2Space A] [FirstCountableTopology A]
variable [TopologicalSpace E] [AddCommGroup E] [Module ℂ E] [IsTopologicalAddGroup E] [T2Space E]
variable [∀ n, UniformSpace (F n)] [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)]
variable [∀ n, IsUniformAddGroup (F n)] [∀ n, ContinuousSMul ℂ (F n)]
variable [∀ n, CompleteSpace (F n)] [∀ n, FirstCountableTopology (F n)]

private theorem frechet_graph_projection (u : A →L[ℂ] E) (j : ∀ n, F n →L[ℂ] E)
    (hexhaust : ∀ y : E, ∃ n, y ∈ range (j n)) :
    ∃ n, IsOpenMap (coincidenceProjection u (j n)) ∧
      Surjective (coincidenceProjection u (j n)) := by
  have hcover : (⋃ n, range (coincidenceProjection u (j n))) = univ := by
    apply eq_univ_of_forall
    intro a
    obtain ⟨n, b, hb⟩ := hexhaust (u a)
    exact mem_iUnion.mpr ⟨n, ⟨⟨(a, b), sub_eq_zero.mpr hb.symm⟩, rfl⟩⟩
  letI : (uniformity A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BaireSpace A := by infer_instance
  have hn : ∃ n, ¬ IsMeagre (range (coincidenceProjection u (j n))) := by
    by_contra! hm
    have h := isMeagre_iUnion hm
    rw [hcover] at h
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty h
  obtain ⟨n, hn⟩ := hn
  let P := coincidenceGraph u (j n)
  letI : IsClosed (P : Set (A × F n)) :=
    (u.comp (ContinuousLinearMap.fst ℂ A (F n)) -
      (j n).comp (ContinuousLinearMap.snd ℂ A (F n))).isClosed_ker
  letI : IsUniformAddGroup P := P.toAddSubgroup.isUniformAddGroup
  letI : FirstCountableTopology P := IsInducing.subtypeVal.firstCountableTopology
  haveI : @CompleteSpace P (IsTopologicalAddGroup.rightUniformSpace P) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  exact ⟨n, open_surjective_of_nonmeagre_range (coincidenceProjection u (j n)) hn⟩

/-- Grothendieck factorization through a countable exhaustion by continuous
linear injections from Fréchet spaces. The proof uses a graph projection with
nonmeagre range, as supplied by the countable cover. -/
theorem frechet_factorization (u : A →L[ℂ] E) (j : ∀ n, F n →L[ℂ] E)
    (hinj : ∀ n, Injective (j n))
    (hexhaust : ∀ y : E, ∃ n, y ∈ range (j n)) :
    ∃ (n : ℕ) (v : A →L[ℂ] F n), (j n).comp v = u := by
  obtain ⟨n, hopen, hsurj⟩ := frechet_graph_projection u j hexhaust
  let P := coincidenceGraph u (j n)
  let p : P →L[ℂ] A := coincidenceProjection u (j n)
  have hp : Injective p := by
    intro a b he
    apply Subtype.ext
    apply Prod.ext
    · exact he
    · apply hinj n
      rw [← coincidence_eq u (j n) a, ← coincidence_eq u (j n) b]
      exact congrArg u he
  let e := LinearEquiv.ofBijective p.toLinearMap ⟨hp, hsurj⟩
  let g : A →L[ℂ] P := ⟨e.symm.toLinearMap, e.toEquiv.continuous_symm_iff.mpr hopen⟩
  refine ⟨n, ((ContinuousLinearMap.snd ℂ A (F n)).comp P.subtypeL).comp g, ?_⟩
  ext a
  change (j n) (e.symm a).val.2 = u a
  have h := coincidence_eq u (j n) (e.symm a)
  have he : (e.symm a).val.1 = a := e.apply_symm_apply a
  exact h.symm.trans (congrArg u he)

/-- Continuity descends along the graph projection even when the stage maps
of the exhaustion have kernels. -/
theorem continuous_restriction_of_frechet_exhaustion
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (u : A →L[ℂ] E) (j : ∀ n, F n →L[ℂ] E)
    (hexhaust : ∀ y : E, ∃ n, y ∈ range (j n))
    (v : E →ₗ[ℂ] Z) (hv : ∀ n, Continuous (v.comp (j n).toLinearMap)) :
    Continuous (v.comp u.toLinearMap) := by
  obtain ⟨n, hopen, hsurj⟩ := frechet_graph_projection u j hexhaust
  let P := coincidenceGraph u (j n)
  let p : P →L[ℂ] A := coincidenceProjection u (j n)
  have hq : IsQuotientMap p := hopen.isQuotientMap p.continuous hsurj
  refine hq.continuous_iff.mpr ?_
  have he : ((v.comp u.toLinearMap : A → Z) ∘ p) =
      fun z : P => (v.comp (j n).toLinearMap) z.val.2 := by
    funext z
    exact congrArg v (coincidence_eq u (j n) z)
  rw [he]
  exact (hv n).comp (continuous_snd.comp continuous_subtype_val)

end FrechetStages

end

end Masullo
