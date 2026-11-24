import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Function Set Topology
open scoped RestrictedProduct

namespace Masullo

variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

/-- Changing the preferred subsets on a finite set of indices leaves the
cofinite restricted-product topology unchanged. -/
def restrictedProductChange (A B : ∀ i, Set (G i)) (h : ∀ᶠ i in cofinite, A i = B i) :
    (Πʳ i, [G i, A i]) ≃ₜ (Πʳ i, [G i, B i]) := by
  let m₁ : ∀ᶠ i in cofinite, MapsTo (id : G i → G i) (A i) (B i) :=
    h.mono fun _ hi => hi ▸ mapsTo_id _
  let m₂ : ∀ᶠ i in cofinite, MapsTo (id : G i → G i) (B i) (A i) :=
    h.mono fun _ hi => hi.symm ▸ mapsTo_id _
  let f := RestrictedProduct.mapAlong G G id tendsto_id (fun _ => id) m₁
  let g := RestrictedProduct.mapAlong G G id tendsto_id (fun _ => id) m₂
  exact
    { toFun := f
      invFun := g
      left_inv := fun _ => RestrictedProduct.ext _ _ (fun _ => rfl)
      right_inv := fun _ => RestrictedProduct.ext _ _ (fun _ => rfl)
      continuous_toFun := RestrictedProduct.mapAlong_continuous G G id tendsto_id _ m₁
        (fun _ => continuous_id)
      continuous_invFun := RestrictedProduct.mapAlong_continuous G G id tendsto_id _ m₂
        (fun _ => continuous_id) }

@[simp] theorem restrictedProductChange_apply (A B : ∀ i, Set (G i))
    (h : ∀ᶠ i in cofinite, A i = B i) (x : Πʳ i, [G i, A i]) (i : ι) :
    restrictedProductChange A B h x i = x i := rfl

@[simp] theorem restrictedProductChange_symm_apply (A B : ∀ i, Set (G i))
    (h : ∀ᶠ i in cofinite, A i = B i) (x : Πʳ i, [G i, B i]) (i : ι) :
    (restrictedProductChange A B h).symm x i = x i := rfl

private def joinRestrictedProduct (A : ∀ i, Set (G i)) (J : Finset ι) [DecidablePred (· ∈ J)]
    (p : (∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, A i])) : Πʳ i, [G i, A i] :=
  ⟨fun i => if hi : i ∈ J then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩, by
    rw [eventually_cofinite]
    let M : Set {i // i ∉ J} := {i | p.2 i ∉ A i}
    have hM : M.Finite := eventually_cofinite.mp p.2.2
    apply (J.finite_toSet.union (hM.image Subtype.val)).subset
    intro i hi
    by_cases hJ : i ∈ J
    · exact Or.inl hJ
    · have hmem : p.2 ⟨i, hJ⟩ ∉ A i := by simpa [hJ] using hi
      exact Or.inr ⟨⟨i, hJ⟩, hmem, rfl⟩⟩

/-- A finite set of coordinates can be split off, with the remaining
coordinates retaining their restricted-product topology. -/
noncomputable def restrictedProductSplitOpenTail (A : ∀ i, Set (G i)) (J : Finset ι)
    (hopen : ∀ i ∉ J, IsOpen (A i)) :
    ((∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, A i])) ≃ₜ (Πʳ i, [G i, A i]) := by
  classical
  let tail (x : Πʳ i, [G i, A i]) :=
    RestrictedProduct.mapAlong G (fun i : {i // i ∉ J} => G i) Subtype.val
      Subtype.val_injective.tendsto_cofinite (fun _ => id)
      (.of_forall fun _ => mapsTo_id _) x
  refine
    { toFun := joinRestrictedProduct A J
      invFun := fun x => (fun i => x i, tail x)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro p
    apply Prod.ext
    · funext i
      simp [joinRestrictedProduct, i.property]
    · apply RestrictedProduct.ext
      intro i
      change (if hi : i.val ∈ J then p.1 ⟨i.val, hi⟩ else p.2 ⟨i.val, hi⟩) = p.2 i
      rw [dite_eq_right i.property]
  · intro x
    apply RestrictedProduct.ext
    intro i
    change (if hi : i ∈ J then x i else tail x ⟨i, hi⟩) = x i
    by_cases hi : i ∈ J
    · rw [dite_eq_left hi]
    · rw [dite_eq_right hi]; rfl
  · apply (RestrictedProduct.continuous_dom_prod_left
      (R := fun i : {i // i ∉ J} => G i)
      (A := fun i : {i // i ∉ J} => A i)
      (fun i => hopen i i.property)).mpr
    intro S hS
    let S' := Subtype.val '' S
    have hS' : cofinite ≤ 𝓟 S' := by
      rw [le_principal_iff, mem_cofinite]
      rw [le_principal_iff, mem_cofinite] at hS
      refine (J.finite_toSet.union (hS.image Subtype.val)).subset fun i hi => ?_
      by_cases hJ : i ∈ J
      · exact Or.inl hJ
      · exact Or.inr ⟨⟨i, hJ⟩, fun h => hi ⟨⟨i, hJ⟩, h, rfl⟩, rfl⟩
    let P := (∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, A i]_[𝓟 S])
    let j (p : P) : Πʳ i, [G i, A i]_[𝓟 S'] :=
      ⟨joinRestrictedProduct A J (p.1, RestrictedProduct.inclusion _ _ hS p.2), by
        rw [eventually_principal]
        rintro i ⟨k, hk, rfl⟩
        have hp := p.2.2 hk
        change p.2 k ∈ A k.val at hp
        simpa [joinRestrictedProduct, k.property] using hp⟩
    have hj : Continuous j := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro i
      change Continuous (fun p : P =>
        (if hi : i ∈ J then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩ : G i))
      by_cases hi : i ∈ J
      · simp only [dite_eq_left hi]
        exact (continuous_apply (⟨i, hi⟩ : J)).comp continuous_fst
      · simp only [dite_eq_right hi]
        exact (RestrictedProduct.continuous_eval (⟨i, hi⟩ : {i // i ∉ J})).comp continuous_snd
    exact (RestrictedProduct.continuous_inclusion hS').comp hj
  · refine (continuous_pi fun i => RestrictedProduct.continuous_eval i.val).prodMk ?_
    exact RestrictedProduct.mapAlong_continuous G _ Subtype.val
      Subtype.val_injective.tendsto_cofinite (fun _ => id)
      (.of_forall fun _ => mapsTo_id _) (fun _ => continuous_id)

theorem restrictedProductSplitOpenTail_apply (A : ∀ i, Set (G i)) (J : Finset ι)
    (hopen : ∀ i ∉ J, IsOpen (A i))
    (p : (∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, A i])) (i : ι) :
    letI := Classical.decEq ι
    restrictedProductSplitOpenTail A J hopen p i =
      if hi : i ∈ J then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩ := rfl

/- Cofinite openness suffices. Replace the finitely many nonopen subsets
by unrestricted coordinates before applying the open-tail construction. -/
noncomputable def restrictedProductFiniteSplit (A : ∀ i, Set (G i)) (J : Finset ι)
    (hopen : ∀ᶠ i in cofinite, IsOpen (A i)) :
    ((∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, A i])) ≃ₜ (Πʳ i, [G i, A i]) := by
  classical
  let B (i : ι) := if IsOpen (A i) then A i else univ
  have hB (i : ι) : IsOpen (B i) := by by_cases hi : IsOpen (A i) <;> simp [B, hi]
  have hAB : ∀ᶠ i in cofinite, A i = B i :=
    hopen.mono fun i hi => by simp [B, hi]
  have htail : ∀ᶠ i : {i // i ∉ J} in cofinite, A i = B i :=
    Subtype.val_injective.tendsto_cofinite.eventually hAB
  let e := restrictedProductChange (fun i : {i // i ∉ J} => A i)
    (fun i : {i // i ∉ J} => B i) htail
  exact ((Homeomorph.refl (∀ i : J, G i)).prodCongr e).trans
    ((restrictedProductSplitOpenTail B J (fun i _ => hB i)).trans
      (restrictedProductChange A B hAB).symm)

theorem restrictedProductFiniteSplit_apply (A : ∀ i, Set (G i)) (J : Finset ι)
    (hopen : ∀ᶠ i in cofinite, IsOpen (A i))
    (p : (∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, A i])) (i : ι) :
    letI := Classical.decEq ι
    restrictedProductFiniteSplit A J hopen p i =
      if hi : i ∈ J then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩ := rfl

/-- A box is open when the preferred subsets outside its finite exceptional
set are open. This is the condition required in A.1.1.2(5). -/
theorem restrictedProductBoxOpen (A U : ∀ i, Set (G i)) (J : Finset ι)
    (hA : ∀ i ∉ J, IsOpen (A i)) (hU : ∀ i ∈ J, IsOpen (U i)) :
    IsOpen {x : Πʳ i, [G i, A i] |
      (∀ i ∉ J, x i ∈ A i) ∧ (∀ i ∈ J, x i ∈ U i)} := by
  let e := restrictedProductSplitOpenTail A J hA
  have h₁ : IsOpen ((univ : Set J).pi fun i : J => U i.val) :=
    isOpen_set_pi finite_univ (fun i _ => hU i i.property)
  have h₂ : IsOpen {p : Πʳ i : {i // i ∉ J}, [G i, A i] |
      ∀ i : {i // i ∉ J}, p i ∈ A i.val} :=
    RestrictedProduct.isOpen_forall_mem
      (R := fun i : {i // i ∉ J} => G i.val)
      (A := fun i : {i // i ∉ J} => A i.val)
      (fun i => hA i i.property)
  have he := (h₁.prod h₂).preimage e.symm.continuous
  convert he using 1
  ext p
  simp only [mem_preimage, mem_ofPred_eq, Set.mem_prod, mem_univ_pi]
  change ((∀ i ∉ J, p i ∈ A i) ∧ (∀ i ∈ J, p i ∈ U i)) ↔
    ((∀ i : J, p i.val ∈ U i.val) ∧ (∀ i : {i // i ∉ J}, p i.val ∈ A i.val))
  exact and_comm.trans ⟨fun ⟨h, k⟩ => ⟨fun i => h i i.property, fun i => k i i.property⟩,
    fun ⟨h, k⟩ => ⟨fun i hi => h ⟨i, hi⟩, fun i hi => k ⟨i, hi⟩⟩⟩

/-- A compact set in a restricted product with open preferred subsets
has a common finite set of exceptional coordinates. -/
theorem compact_restrictedProduct_one_stage (A : ∀ i, Set (G i))
    (hopen : ∀ i, IsOpen (A i)) {K : Set (Πʳ i, [G i, A i])} (hK : IsCompact K) :
    ∃ J : Finset ι, ∀ x ∈ K, ∀ i ∉ J, x i ∈ A i := by
  classical
  let U (J : Finset ι) : Set (Πʳ i, [G i, A i]) := {x | ∀ i ∉ J, x i ∈ A i}
  have hU (J : Finset ι) : IsOpen (U J) :=
    RestrictedProduct.isOpen_forall_imp_mem hopen
  have hcover : K ⊆ ⋃ J, U J := by
    intro x _
    have hx : {i | x i ∉ A i}.Finite := eventually_cofinite.mp x.2
    refine mem_iUnion.mpr ⟨hx.toFinset, ?_⟩
    change ∀ i ∉ hx.toFinset, x i ∈ A i
    intro i hi
    by_contra ha
    exact hi (hx.mem_toFinset.mpr ha)
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨T.biUnion id, fun x hx i hi => ?_⟩
  obtain ⟨J, hJ, hmem⟩ := mem_iUnion₂.mp (hT hx)
  exact hmem i (fun h => hi (Finset.mem_biUnion.mpr ⟨J, hJ, h⟩))

/-- The compact-closure criterion in A.1.1.2(3). -/
theorem restrictedProduct_compact_closure_iff [∀ i, T2Space (G i)]
    (A : ∀ i, Set (G i)) (hA : ∀ᶠ i in cofinite, IsOpen (A i) ∧ IsCompact (A i))
    (H : Set (Πʳ i, [G i, A i])) :
    IsCompact (closure H) ↔
      ∃ B : ∀ i, Set (G i), (∀ i, IsCompact (B i)) ∧ (∀ᶠ i in cofinite, B i = A i) ∧
        ∀ x ∈ H, ∀ i, x i ∈ B i := by
  classical
  constructor
  · intro hK
    let C (i : ι) := if IsOpen (A i) then A i else univ
    have hopen : ∀ i, IsOpen (C i) := fun i => by by_cases hi : IsOpen (A i) <;> simp [C, hi]
    have hAC : ∀ᶠ i in cofinite, A i = C i :=
      hA.mono fun i hi => by simp [C, hi.1]
    let e := restrictedProductChange A C hAC
    obtain ⟨J, hJ⟩ := compact_restrictedProduct_one_stage C hopen (hK.image e.continuous)
    let E := {i | i ∉ J ∧ IsOpen (A i) ∧ IsCompact (A i)}
    have hJev : ∀ᶠ i in cofinite, i ∉ J := J.finite_toSet.compl_mem_cofinite
    have hE : ∀ᶠ i in cofinite, i ∈ E := hJev.and hA
    let B (i : ι) := if i ∈ E then A i else (fun x : Πʳ j, [G j, A j] => x i) '' closure H
    refine ⟨B, ?_, hE.mono (fun i hi => by simp [B, hi]), ?_⟩
    · intro i
      by_cases hi : i ∈ E
      · simpa [B, hi] using hi.2.2
      · simpa [B, hi] using hK.image (RestrictedProduct.continuous_eval i)
    · intro x hx i
      by_cases hi : i ∈ E
      · have h := hJ (e x) ⟨x, subset_closure hx, rfl⟩ i hi.1
        change x i ∈ C i at h
        simpa [B, C, hi, hi.2.1] using h
      · simpa [B, hi] using (show x i ∈ (fun x : Πʳ j, [G j, A j] => x i) '' closure H from
          ⟨x, subset_closure hx, rfl⟩)
  · rintro ⟨B, hB, hBA, hH⟩
    let S := {i | B i = A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hBA
    let j (x : ∀ i, B i) : Πʳ i, [G i, A i]_[𝓟 S] :=
      ⟨fun i => (x i).val, by
        rw [eventually_principal]
        intro i hi
        change (x i).val ∈ A i
        rw [← show B i = A i from hi]
        exact (x i).property⟩
    have hj : Continuous j := RestrictedProduct.continuous_rng_of_principal.mpr
      (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))
    letI (i : ι) : CompactSpace (B i) := isCompact_iff_compactSpace.mp (hB i)
    let p := RestrictedProduct.inclusion G A hS ∘ j
    have hp : IsCompact (range p) := isCompact_range ((RestrictedProduct.continuous_inclusion hS).comp hj)
    refine hp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hp.isClosed)
    intro x hx
    exact ⟨fun i => ⟨x i, hH x hx i⟩, rfl⟩

section Groups

variable [∀ i, CommGroup (G i)]

/-- A.1.1.2(1). A cofinite family of compact open subgroups gives a
locally compact topological group. Each finite exceptional coordinate may
use an arbitrary subgroup. -/
theorem restrictedProductGroup_locallyCompact
    [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)]
    (K : ∀ i, Subgroup (G i))
    (hK : ∀ᶠ i in cofinite, IsOpen (K i : Set (G i)) ∧ IsCompact (K i : Set (G i))) :
    LocallyCompactSpace (Πʳ i, [G i, K i]) ∧
      T2Space (Πʳ i, [G i, K i]) ∧ IsTopologicalGroup (Πʳ i, [G i, K i]) := by
  classical
  let B (i : ι) := if IsOpen (K i : Set (G i)) then K i else ⊤
  letI : Fact (∀ i, IsOpen (B i : Set (G i))) :=
    ⟨fun i => by by_cases hi : IsOpen (K i : Set (G i)) <;> simp [B, hi]⟩
  have hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)) :=
    hK.mono fun i hi => by simpa [B, hi.1] using hi.2
  letI : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  letI : IsTopologicalGroup (Πʳ i, [G i, B i]) := inferInstance
  have hEq : ∀ᶠ i in cofinite, (K i : Set (G i)) = B i :=
    hK.mono fun i hi => by simp [B, hi.1]
  let e : (Πʳ i, [G i, K i]) ≃ₜ (Πʳ i, [G i, B i]) :=
    restrictedProductChange _ _ hEq
  refine ⟨e.isOpenEmbedding.locallyCompactSpace, inferInstance, ?_⟩
  have hm : Continuous (fun p : (Πʳ i, [G i, K i]) × (Πʳ i, [G i, K i]) =>
      e.symm (e p.1 * e p.2)) :=
    e.symm.continuous.comp ((e.continuous.comp continuous_fst).mul
      (e.continuous.comp continuous_snd))
  have hi : Continuous (fun x : Πʳ i, [G i, K i] => e.symm (e x)⁻¹) :=
    e.symm.continuous.comp (continuous_inv.comp e.continuous)
  exact
    { continuous_mul := hm
      continuous_inv := hi }

/-- The canonical cofinite change respects multiplication. -/
theorem restrictedProductChange_mul (K B : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, (K i : Set (G i)) = B i) (x y : Πʳ i, [G i, K i]) :
    let e : (Πʳ i, [G i, K i]) ≃ₜ (Πʳ i, [G i, B i]) := restrictedProductChange _ _ h
    e (x * y) = e x * e y :=
  RestrictedProduct.ext _ _ fun _ => rfl

/-- Splitting off a finite block is compatible with the pointwise group law. -/
theorem restrictedProductFiniteSplit_mul (K : ∀ i, Subgroup (G i)) (J : Finset ι)
    (h : ∀ᶠ i in cofinite, IsOpen (K i : Set (G i)))
    (p q : (∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, K i])) :
    let e : ((∀ i : J, G i) × (Πʳ i : {i // i ∉ J}, [G i, K i])) ≃ₜ (Πʳ i, [G i, K i]) :=
      restrictedProductFiniteSplit _ J h
    e (p * q) = e p * e q := by
  classical
  apply RestrictedProduct.ext
  intro i
  change (if hi : i ∈ J then p.1 ⟨i, hi⟩ * q.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩ * q.2 ⟨i, hi⟩ : G i) =
    (if hi : i ∈ J then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩ : G i) *
      (if hi : i ∈ J then q.1 ⟨i, hi⟩ else q.2 ⟨i, hi⟩ : G i)
  by_cases hi : i ∈ J <;> simp [hi]

end Groups

/-- A single real coordinate with preferred subgroup zero shows why
the nonopen distinguished coordinates must be included in the finite block
in A.1.1.2(5). -/
theorem restrictedProduct_box_nonopen_at_real_coordinate :
    ¬ IsOpen {x : Πʳ _i : Unit, [ℝ, ({0} : Set ℝ)] | x () = 0} := by
  let A (_ : Unit) : Set ℝ := {0}
  let j (y : ℝ) : Πʳ i : Unit, [ℝ, A i]_[⊥] :=
    ⟨fun _ => y, eventually_bot⟩
  have hj : Continuous j := RestrictedProduct.continuous_rng_of_bot.mpr
    (continuous_pi fun _ => continuous_id)
  let p := RestrictedProduct.inclusion (fun _ : Unit => ℝ) A (Filter.cofinite_eq_bot.le) ∘ j
  have hp : Continuous p := (RestrictedProduct.continuous_inclusion _).comp hj
  intro h
  apply not_isOpen_singleton (0 : ℝ)
  exact h.preimage hp

end Masullo
