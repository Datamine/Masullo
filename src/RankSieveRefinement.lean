import RankCanonicalSite
import Mathlib.Topology.Compactification.StoneCech

/-! Bounded refinements of canonical covering sieves. -/

open Cardinal CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace
open scoped Cardinal Ordinal

noncomputable section

namespace Masullo

universe u

private theorem stoneCech_card_le (D : Type u) [TopologicalSpace D] :
    #(StoneCech D) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ #D) := by
  have h₁ : #(StoneCech D) ≤ #(PreStoneCech D) := Cardinal.mk_quot_le
  have h₂ : #(PreStoneCech D) ≤ #(Ultrafilter D) := Cardinal.mk_quot_le
  have h₃ : #(Ultrafilter D) ≤ #(Set (Set D)) := by
    apply mk_le_of_injective (f := fun F : Ultrafilter D ↦ F.toFilter.sets)
    intro F G h
    apply Ultrafilter.ext
    intro s
    change F.toFilter.sets = G.toFilter.sets at h
    change s ∈ F.toFilter.sets ↔ s ∈ G.toFilter.sets
    rw [h]
  simpa only [mk_set] using h₁.trans (h₂.trans h₃)

private theorem compactProbe_small {Z X : CGWH.{u}} (f : C(Z.obj, X.obj))
    {U : Set X.obj} (h : ¬ IsOpen (f ⁻¹' U)) :
    ∃ (L : CompHaus.{u}) (l : C(L, Z.obj)),
      #(L : Type u) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ #(X.obj : Type u)) ∧ ¬ IsOpen ((f ∘ l) ⁻¹' U) := by
  obtain ⟨K, k, hk⟩ : ∃ (K : CompHaus.{u}) (k : C(K, Z.obj)), ¬ IsOpen ((f ∘ k) ⁻¹' U) := by
    by_contra hn
    push Not at hn
    apply h
    apply UCompactlyGeneratedSpace.isOpen
    exact hn
  let q := f.comp k
  let M := range q
  let j : C(K, M) := ⟨fun y ↦ ⟨q y,mem_range_self y⟩, q.continuous.subtype_mk _⟩
  have hj : Surjective j := fun ⟨y,t,ht⟩ ↦ ⟨t,Subtype.ext ht⟩
  letI : T2Space M := weaklyHausdorff_compact_surjection (weaklyHausdorff_subspace X.property _) K j hj
  let D := ULift.{u} M
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  let c : D → K := fun x ↦ (hj x.down).choose
  let e := stoneCechExtend (show Continuous c from continuous_of_discreteTopology)
  have he : Continuous e := continuous_stoneCechExtend _
  have hes : Surjective (j ∘ e) := by
    intro y
    refine ⟨stoneCechUnit (ULift.up y), ?_⟩
    change j (e (stoneCechUnit (ULift.up y))) = y
    dsimp only [e]
    rw [stoneCechExtend_stoneCechUnit]
    exact (hj y).choose_spec
  have hq : IsQuotientMap (j ∘ e) :=
    IsQuotientMap.of_surjective_continuous hes (j.continuous.comp he)
  let L := CompHaus.of (StoneCech D)
  let l := k.comp (show C(L,K) from ⟨e,he⟩)
  have hD : #D ≤ #(X.obj : Type u) :=
    mk_le_of_injective (f := fun x : D ↦ x.down.val) (fun _ _ h ↦ ULift.ext _ _ (Subtype.ext h))
  refine ⟨L,l,(stoneCech_card_le D).trans
    (power_le_power_left two_ne_zero (power_le_power_left two_ne_zero hD)),?_⟩
  intro ho
  apply hk
  let U₀ : Set M := Subtype.val ⁻¹' U
  have hU₀ : IsOpen U₀ := (hq.isOpen_preimage).mp ho
  exact hU₀.preimage j.continuous

variable {α : Ordinal.{u}} {X : RankSpace α}

private structure SieveProbe (S : Sieve X) where
  domain : CompHaus.{u}
  source : RankSieveArrows S
  factor : C(domain, source.1.space.obj)
  bound : #(domain : Type u) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ #(X.space.obj : Type u))

private def SieveProbe.map {S : Sieve X} (A : SieveProbe S) : C(A.domain, X.space.obj) :=
  ((rankSpaceInclusion α).map A.source.2.val).hom.hom.hom.comp A.factor

private theorem sieveProbe_hits {S : Sieve X} (hS : IsQuotientMap (rankSieveMap S)) (x : X.space.obj) :
    ∃ (A : SieveProbe S) (a : A.domain), A.map a = x := by
  obtain ⟨⟨i,y⟩,hy⟩ := hS.surjective x
  let K := CompHaus.of (ULift.{u} Unit)
  refine ⟨⟨K,i,ContinuousMap.const _ y,?_⟩,⟨()⟩,hy⟩
  change #(ULift.{u} Unit) ≤ _
  simp only [mk_uLift, lift_one, mk_unit]
  exact Cardinal.one_le_iff_ne_zero.mpr (power_ne_zero _ two_ne_zero)

private theorem sieveProbe_detects {S : Sieve X} (hS : IsQuotientMap (rankSieveMap S))
    (U : Set X.space.obj) (hU : ¬ IsOpen U) :
    ∃ A : SieveProbe S, ¬ IsOpen (A.map ⁻¹' U) := by
  have h : ∃ i : RankSieveArrows S, ¬ IsOpen (((rankSpaceInclusion α).map i.2.val).hom ⁻¹' U) := by
    by_contra hn
    push Not at hn
    exact hU ((hS.isOpen_preimage).mp (isOpen_sigma_iff.mpr hn))
  obtain ⟨i,hi⟩ := h
  obtain ⟨L,l,hcard,hn⟩ := compactProbe_small ((rankSpaceInclusion α).map i.2.val).hom.hom.hom hi
  exact ⟨⟨L,i,l,hcard⟩,hn⟩

/-- A canonical covering sieve contains a jointly quotient family with a
rank-bounded disjoint union of sources. Each member factors through the sieve
by a compact Hausdorff source of uniformly bounded cardinality. -/
theorem rankCanonicalSieve_boundedFamily (S : Sieve X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hκ : (preBeth α).IsStrongLimit)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X) :
    ∃ (I : Type u) (Y : I → RankSpace α) (f : ∀ i, Y i ⟶ X),
      (∀ i, S (f i)) ∧ #(Σ i, (Y i).space.obj : Type u) < preBeth α ∧
        IsQuotientMap (fun p : Σ i, (Y i).space.obj ↦ ((rankSpaceInclusion α).map (f p.1)).hom p.2) := by
  classical
  let U := rankSpaceInclusion α
  let κ := preBeth α
  let I := X.space.obj ⊕ {s : Set X.space.obj // ¬ IsOpen s}
  let C := (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ #(X.space.obj : Type u))
  have hq := (rankCanonicalTopology_iff S hα hω).mp hS
  let hits (x : X.space.obj) := sieveProbe_hits hq x
  let detects (s : {s : Set X.space.obj // ¬ IsOpen s}) :=
    sieveProbe_detects hq s.val s.property
  let A : I → SieveProbe S := Sum.elim (fun x ↦ (hits x).choose) (fun s ↦ (detects s).choose)
  have hA : ∀ i, #((A i).domain : Type u) ≤ C := fun i ↦ (A i).bound
  have hC : C < κ := hκ.isStrongPrelimit (hκ.isStrongPrelimit X.carrier_lt)
  have hI : #I < κ := by
    dsimp [I]
    rw [mk_sum, lift_id, lift_id]
    refine add_lt_of_lt hω.le X.carrier_lt ?_
    exact (mk_set_le _).trans_lt (by rw [mk_set]; exact hκ.isStrongPrelimit X.carrier_lt)
  let W (i : I) : CGWH.{u} := CGWH.of (X := ((A i).domain : Type u))
    (fun K k ↦ (isCompact_range k.continuous).isClosed)
  have hW (i : I) := rankSpace_representative hα (W i) ((hA i).trans_lt hC)
  let Y (i : I) := (hW i).choose
  let e (i : I) := (hW i).choose_spec.some
  let j (i : I) : (Y i).space ⟶ (A i).source.1.space :=
    CGWH.map ((A i).factor.comp ⟨e i,(e i).continuous⟩)
  let g (i : I) : Y i ⟶ (A i).source.1 := U.preimage (j i)
  let f (i : I) : Y i ⟶ X := g i ≫ (A i).source.2.val
  have hf (i : I) (x : (Y i).space.obj) : (U.map (f i)).hom x = (A i).map (e i x) := by
    change (U.map (g i ≫ (A i).source.2.val)).hom x = _
    rw [U.map_comp]
    rw [show U.map (g i) = j i from U.map_preimage _]
    rfl
  refine ⟨I,Y,f,fun i ↦ S.downward_closed (A i).source.2.property (g i), ?_, ?_⟩
  · have hY (i : I) : #((Y i).space.obj : Type u) ≤ C :=
      (Cardinal.mk_congr (e i).toEquiv).le.trans (hA i)
    rw [Cardinal.mk_sigma]
    exact (Cardinal.sum_le_sum _ _ hY).trans_lt (by
      rw [Cardinal.sum_const']
      exact mul_lt_of_lt hω.le hI hC)
  · let q' (p : Σ i, (Y i).space.obj) := (U.map (f p.1)).hom p.2
    have hc : Continuous q' := continuous_sigma fun i ↦ (U.map (f i)).hom.hom.hom.continuous
    refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨?_, fun h ↦ h.preimage hc⟩, ?_⟩
    · intro hs
      by_contra hn
      let i : I := Sum.inr ⟨s,hn⟩
      have hi : IsOpen (q' ∘ Sigma.mk i ⁻¹' s) := isOpen_sigma_iff.mp hs i
      have he : IsOpen ((A i).map ⁻¹' s) := by
        have h := hi.preimage (e i).symm.continuous
        convert h using 1
        ext x
        simp only [mem_preimage, Function.comp_apply, q', hf, Homeomorph.apply_symm_apply]
      exact (detects ⟨s,hn⟩).choose_spec he
    · intro x
      let i : I := Sum.inl x
      obtain ⟨a,ha⟩ := (hits x).choose_spec
      let a₀ : (W i).obj := a
      refine ⟨⟨i,(e i).symm a₀⟩,?_⟩
      exact (hf i ((e i).symm a₀)).trans ((congrArg ((A i).map) ((e i).apply_symm_apply a₀)).trans ha)


/-- A jointly quotient family inside a canonical sieve can be assembled
into a quotient projection from an actual rank-site coproduct. The
individual summand maps lie over the original sieve. -/
theorem rankCanonicalSieve_quotientCoproduct (S : Sieve X)
    (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hκ : (preBeth α).IsStrongLimit)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X) :
    ∃ (I : Type u) (Y : I → RankSpace α) (W : RankSpace α) (q : W ⟶ X)
      (e : W.space.obj ≃ₜ (Σ i, (Y i).space.obj)) (j : ∀ i, Y i ⟶ W),
        IsQuotientMap ((rankSpaceInclusion α).map q).hom ∧
        (∀ i, S (j i ≫ q)) ∧
        ∀ i x, e (((rankSpaceInclusion α).map (j i)).hom x) = ⟨i,x⟩ := by
  obtain ⟨I,Y,f,hf,hsize,hq⟩ := rankCanonicalSieve_boundedFamily S hα hω hκ hS
  let U := rankSpaceInclusion α
  let Z := (CGWH.coproductCofan (fun i ↦ (Y i).space)).pt
  obtain ⟨W,⟨e⟩⟩ := rankSpace_representative hα Z hsize
  let v : C(Z.obj, X.space.obj) :=
    ⟨fun p : Σ i, (Y i).space.obj ↦ (U.map (f p.1)).hom p.2, hq.continuous⟩
  let m : W.space ⟶ X.space := CGWH.map (v.comp ⟨e,e.continuous⟩)
  let q := U.preimage m
  let k (i : I) : (Y i).space ⟶ W.space :=
    CGWH.map ((show C(Z.obj,W.space.obj) from ⟨e.symm,e.symm.continuous⟩).comp
      ((CGWH.coproductCofan (fun i ↦ (Y i).space)).inj i).hom.hom.hom)
  let j (i : I) := U.preimage (k i)
  have hqm : U.map q = m := U.map_preimage _
  have hjk (i : I) : U.map (j i) = k i := U.map_preimage _
  have he (i : I) (x : (Y i).space.obj) : e ((U.map (j i)).hom x) = ⟨i,x⟩ := by
    rw [hjk]
    exact e.apply_symm_apply _
  refine ⟨I,Y,W,q,e,j,?_,?_,he⟩
  · rw [hqm]
    change IsQuotientMap (v ∘ e)
    exact hq.comp e.isQuotientMap
  · intro i
    suffices hh : j i ≫ q = f i by rw [hh]; exact hf i
    apply U.map_injective
    rw [U.map_comp, hqm]
    apply CGWH.ext_hom
    intro x
    change v (e ((U.map (j i)).hom x)) = (U.map (f i)).hom x
    rw [he]
    rfl


private def liftingSieve {Z : CGWH.{u}} (f : C(Z.obj, X.space.obj)) : Sieve X where
  arrows Y q := ∃ l : C(Y.space.obj, Z.obj), ∀ y, f (l y) = ((rankSpaceInclusion α).map q).hom y
  downward_closed := by
    intro Y W q ⟨l,hl⟩ g
    refine ⟨l.comp ((rankSpaceInclusion α).map g).hom.hom.hom, fun w ↦ ?_⟩
    rw [(rankSpaceInclusion α).map_comp]
    exact hl _

private theorem liftingSieve_isCanonical {Z : CGWH.{u}} (f : C(Z.obj, X.space.obj))
    (hf : IsQuotientMap f) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hκ : (preBeth α).IsStrongLimit) :
    liftingSieve f ∈ Sheaf.canonicalTopology (RankSpace α) X := by
  apply (rankCanonicalTopology_iff _ hα hω).mpr
  let U := rankSpaceInclusion α
  let S := liftingSieve f
  have hcard (L : CompHaus.{u}) (hL : #(L : Type u) < preBeth α) (l : C(L,Z.obj)) :
      ∃ (Y : RankSpace α) (q : Y ⟶ X) (e : Y.space.obj ≃ₜ (L : Type u)),
        S q ∧ ∀ y, (U.map q).hom y = f (l (e y)) := by
    let W : CGWH.{u} := CGWH.of (X := (L : Type u))
      (fun K k ↦ (isCompact_range k.continuous).isClosed)
    obtain ⟨Y,⟨e⟩⟩ := rankSpace_representative hα W hL
    let l' := l.comp ⟨e,e.continuous⟩
    let m : Y.space ⟶ X.space := CGWH.map (f.comp l')
    let q := U.preimage m
    have hm : U.map q = m := U.map_preimage m
    have he (y : Y.space.obj) : (U.map q).hom y = f (l (e y)) := by
      rw [hm]
      rfl
    exact ⟨Y,q,e,⟨l',fun y ↦ (he y).symm⟩,he⟩
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨?_,?_⟩, ?_⟩
  · intro hs
    by_contra hn
    have hnf : ¬ IsOpen (f ⁻¹' s) := fun ho ↦ hn ((hf.isOpen_preimage).mp ho)
    obtain ⟨L,l,hL,hl⟩ := compactProbe_small f hnf
    have hLt : #(L : Type u) < preBeth α :=
      hL.trans_lt (hκ.isStrongPrelimit (hκ.isStrongPrelimit X.carrier_lt))
    obtain ⟨Y,q,e,hq,he⟩ := hcard L hLt l
    let i : RankSieveArrows S := ⟨Y,q,hq⟩
    have hi : IsOpen ((fun y : Y.space.obj ↦ (U.map q).hom y) ⁻¹' s) :=
      isOpen_sigma_iff.mp hs i
    apply hl
    have h := hi.preimage e.symm.continuous
    convert h using 1
    ext x
    simp only [mem_preimage, Function.comp_apply, he, Homeomorph.apply_symm_apply]
  · exact fun hs ↦ hs.preimage (rankSieveMap_continuous S)
  · intro x
    obtain ⟨z,hz⟩ := hf.surjective x
    let L := CompHaus.of (ULift.{u} Unit)
    have hL : #(L : Type u) < preBeth α := by
      change #(ULift.{u} Unit) < preBeth α
      simpa only [mk_uLift, lift_one, mk_unit] using (one_lt_aleph0.trans hω)
    obtain ⟨Y,q,e,hq,he⟩ := hcard L hL (ContinuousMap.const _ z)
    exact ⟨⟨⟨Y,q,hq⟩,e.symm ⟨()⟩⟩,(he _).trans hz⟩

/-- Any CGWH quotient map to an object of the rank site has a rank-site
quotient refinement. The original domain can have arbitrary size within the
carrier universe. -/
theorem rankQuotientMap_refinement {Z : CGWH.{u}} (f : Z ⟶ X.space)
    (hf : IsQuotientMap f.hom) (hα : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hκ : (preBeth α).IsStrongLimit) :
    ∃ (W : RankSpace α) (g : W.space ⟶ Z), IsQuotientMap (g ≫ f).hom := by
  let U := rankSpaceInclusion α
  let fc := f.hom.hom.hom
  let S := liftingSieve fc
  obtain ⟨I,Y,W,q,e,j,hq,hS,he⟩ := rankCanonicalSieve_quotientCoproduct S hα hω hκ
    (liftingSieve_isCanonical fc hf hα hω hκ)
  let d (i : I) : C((Y i).space.obj,Z.obj) := (hS i).choose
  have hd (i : I) (y : (Y i).space.obj) : fc (d i y) = (U.map (j i ≫ q)).hom y :=
    (hS i).choose_spec y
  let l : C((Σ i, (Y i).space.obj),Z.obj) :=
    ⟨fun p ↦ d p.1 p.2,continuous_sigma fun i ↦ (d i).continuous⟩
  let g : W.space ⟶ Z := CGWH.map (l.comp ⟨e,e.continuous⟩)
  have hl : (g ≫ f).hom = (U.map q).hom := by
    apply ConcreteCategory.hom_ext
    intro w
    let i := (e w).1
    let y := (e w).2
    have he' : (U.map (j i)).hom y = w := e.injective (he i y)
    change fc (d i y) = (U.map q).hom w
    rw [hd, U.map_comp]
    exact congrArg (U.map q).hom he'
  exact ⟨W,g,hl.symm ▸ hq⟩

end Masullo
