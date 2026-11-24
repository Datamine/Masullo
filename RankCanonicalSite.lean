import RankRegularity
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

open Cardinal CategoryTheory CategoryTheory.Limits Function Order Set Topology TopologicalSpace
open scoped Cardinal Ordinal

namespace Masullo

universe u

noncomputable section

variable {α : Ordinal.{u}}

local notation "U" => rankSpaceInclusion α

private theorem rankHom_ext {X Y : RankSpace α} {f g : X ⟶ Y}
    (h : ∀ x : X.space.obj, ((U).map f).hom x = ((U).map g).hom x) : f = g :=
  (U).map_injective (cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ h))

private theorem rankHom_eval {X Y : RankSpace α} {f g : X ⟶ Y}
    (h : f = g) (x : X.space.obj) : ((U).map f).hom x = ((U).map g).hom x :=
  congrArg (fun a : X ⟶ Y => ((U).map a).hom x) h

private structure RankProbe (α : Ordinal.{u}) where
  obj : RankSpace α
  base : obj.space.obj
  unique : ∀ x : obj.space.obj, x = base

private def rankProbe (hcard : preBeth α = α.card) (hω : ℵ₀ < preBeth α) : RankProbe α := by
  let h := rankSpace_representative hcard CGWH.basepointObject
    (show #(ULift.{u} Unit) < preBeth α from mk_le_aleph0.trans_lt hω)
  let e := h.choose_spec.some
  exact ⟨h.choose, e.symm ⟨()⟩, fun x => e.injective (Subsingleton.elim _ _)⟩

private def RankProbe.point (P : RankProbe α) (X : RankSpace α) (x : X.space.obj) : P.obj ⟶ X :=
  (U).preimage (CGWH.map (ContinuousMap.const _ x))

private theorem RankProbe.point_apply (P : RankProbe α) (X : RankSpace α) (x : X.space.obj)
    (z : P.obj.space.obj) : ((U).map (P.point X x)).hom z = x := by
  change (((U).map ((U).preimage (CGWH.map (ContinuousMap.const _ x)))).hom) z = x
  rw [Functor.map_preimage]
  rfl

/-- The set of arrows in a sieve, including the source objects. -/
abbrev RankSieveArrows {X : RankSpace α} (S : Sieve X) := Σ Y : RankSpace α, {f : Y ⟶ X // S f}

/-- The canonical map of the ordinary topological disjoint union over a sieve. -/
def rankSieveMap {X : RankSpace α} (S : Sieve X) :
    (Σ i : RankSieveArrows S, i.1.space.obj) → X.space.obj :=
  fun x => ((U).map x.1.2.val).hom x.2

theorem rankSieveMap_continuous {X : RankSpace α} (S : Sieve X) : Continuous (rankSieveMap S) :=
  continuous_sigma fun i => ((U).map i.2.val).hom.hom.hom.continuous

private theorem rankSieveMap_isSheafFor {X Z : RankSpace α} {S : Sieve X}
    (P : RankProbe α) (hS : IsQuotientMap (rankSieveMap S)) :
    Presieve.IsSheafFor (yoneda.obj Z) S.arrows := by
  classical
  intro a ha
  let q := rankSieveMap S
  let b : (Σ i : RankSieveArrows S, i.1.space.obj) → Z.space.obj :=
    fun x => ((U).map (a x.1.2.val x.1.2.property)).hom x.2
  let f : X.space.obj → Z.space.obj := b ∘ hS.surjective.hasRightInverse.choose
  have hf : ∀ y, f (q y) = b y := by
    intro y
    let y' := hS.surjective.hasRightInverse.choose (q y)
    have eq : q y' = q y := hS.surjective.hasRightInverse.choose_spec (q y)
    have e : P.point y'.1.1 y'.2 ≫ y'.1.2.val = P.point y.1.1 y.2 ≫ y.1.2.val := by
      apply rankHom_ext
      intro t
      change ((U).map y'.1.2.val).hom (((U).map (P.point y'.1.1 y'.2)).hom t) =
        ((U).map y.1.2.val).hom (((U).map (P.point y.1.1 y.2)).hom t)
      rw [P.point_apply, P.point_apply]
      exact eq
    have h := rankHom_eval
      (ha (P.point y'.1.1 y'.2) (P.point y.1.1 y.2) y'.1.2.property y.1.2.property e) P.base
    change ((U).map (a y'.1.2.val y'.1.2.property)).hom
        (((U).map (P.point y'.1.1 y'.2)).hom P.base) =
      ((U).map (a y.1.2.val y.1.2.property)).hom (((U).map (P.point y.1.1 y.2)).hom P.base) at h
    rw [P.point_apply, P.point_apply] at h
    exact h
  have hfc : Continuous f := hS.continuous_iff.mpr (by
    show Continuous (f ∘ q)
    rw [show f ∘ q = b from funext hf]
    exact continuous_sigma fun i => ((U).map (a i.2.val i.2.property)).hom.hom.hom.continuous)
  let d : X ⟶ Z := (U).preimage (CGWH.map ⟨f, hfc⟩)
  have hd : ∀ x : X.space.obj, ((U).map d).hom x = f x := by
    intro x
    simp only [d, Functor.map_preimage]
    rfl
  refine ⟨d, ?_, ?_⟩
  · intro Y p hp
    apply rankHom_ext
    intro y
    change ((U).map d).hom (((U).map p).hom y) = ((U).map (a p hp)).hom y
    rw [hd]
    exact hf ⟨⟨Y, p, hp⟩, y⟩
  · intro m hm
    apply rankHom_ext
    intro x
    obtain ⟨⟨⟨Y, p, hp⟩, y⟩, rfl⟩ := hS.surjective x
    rw [hd]
    exact (rankHom_eval (hm p hp) y).trans (hf ⟨⟨Y, p, hp⟩, y⟩).symm


private def twoPointCGWH : CGWH.{u} :=
  CGWH.of (X := ULift.{u} Bool) (fun _ f => (isCompact_range f.continuous).isClosed)

private theorem rankSieveMap_surj_of_canonical {X : RankSpace α} {S : Sieve X}
    (hcard : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X) : Surjective (rankSieveMap S) := by
  let P := rankProbe hcard hω
  obtain ⟨Z, ⟨e⟩⟩ := rankSpace_representative hcard twoPointCGWH
    (show #(ULift.{u} Bool) < preBeth α from mk_le_aleph0.trans_lt hω)
  intro x
  by_contra hx
  let k := P.point X x
  let V := S.pullback k
  have hV : V ∈ Sheaf.canonicalTopology (RankSpace α) P.obj :=
    (Sheaf.canonicalTopology _).pullback_stable k hS
  have hempty {Y : RankSpace α} {g : Y ⟶ P.obj} (hg : V g) (y : Y.space.obj) : False := by
    apply hx
    refine ⟨⟨⟨Y, g ≫ k, hg⟩, y⟩, ?_⟩
    change ((U).map k).hom (((U).map g).hom y) = x
    exact P.point_apply _ _ _
  let a := P.point Z (e.symm ⟨false⟩)
  let b := P.point Z (e.symm ⟨true⟩)
  let family : V.arrows.FamilyOfElements (yoneda.obj Z) := fun {_} g _ => g ≫ a
  have ha : family.IsAmalgamation a := fun {_} _ _ => rfl
  have hb : family.IsAmalgamation b := by
    intro Y g hg
    apply rankHom_ext
    intro y
    exact (hempty hg y).elim
  have eq : a = b := (Sheaf.isSheaf_yoneda_obj Z _ hV).isSeparatedFor family a b ha hb
  have he := rankHom_eval eq P.base
  change ((U).map (P.point Z _)).hom P.base = ((U).map (P.point Z _)).hom P.base at he
  rw [P.point_apply, P.point_apply] at he
  exact Bool.false_ne_true (congrArg ULift.down (e.symm.injective he))

private def RankFinalCarrier (X : RankSpace α) := (X.space.obj : Type u)

private def rankFinalSpace {X : RankSpace α} (S : Sieve X) : CGWH.{u} := by
  let t₀ : TopologicalSpace (X.space.obj : Type u) := inferInstance
  let t : TopologicalSpace (RankFinalCarrier X) := TopologicalSpace.coinduced (show (Σ i : RankSieveArrows S, i.1.space.obj) → RankFinalCarrier X from rankSieveMap S) inferInstance
  letI := t
  have hcg : CompactlyGeneratedSpace (RankFinalCarrier X) :=
    compactlyGeneratedSpace_of_coinduced
      (continuous_coinduced_rng : Continuous (show (Σ i : RankSieveArrows S, i.1.space.obj) → RankFinalCarrier X from rankSieveMap S)) rfl
  have hi : Continuous[t, t₀] (id : RankFinalCarrier X → X.space.obj) :=
    continuous_coinduced_dom.mpr (rankSieveMap_continuous S)
  have hwh : WeaklyHausdorff (RankFinalCarrier X) := by
    intro K f
    let g : C(K, X.space.obj) := ⟨fun x => f x, hi.comp f.continuous⟩
    exact (X.space.property K g).preimage hi
  exact @CGWH.of _ t hcg hwh

private def rankFinalInclusion {X : RankSpace α} (S : Sieve X) :
    rankFinalSpace S ⟶ X.space :=
  CGWH.map ⟨(id : RankFinalCarrier X → X.space.obj),
    continuous_coinduced_dom.mpr (rankSieveMap_continuous S)⟩

private def rankFinalLift {X Y : RankSpace α} {S : Sieve X} {g : Y ⟶ X} (hg : S g) :
    Y.space ⟶ rankFinalSpace S := by
  let i : RankSieveArrows S := ⟨Y, g, hg⟩
  let j : Y.space.obj → Σ i : RankSieveArrows S, i.1.space.obj :=
    @Sigma.mk (RankSieveArrows S) (fun i => (i.1.space.obj : Type u)) i
  have hj : Continuous j := continuous_sigmaMk
  let q : (Σ i : RankSieveArrows S, i.1.space.obj) → RankFinalCarrier X := rankSieveMap S
  have hq : Continuous (show (Σ i : RankSieveArrows S, i.1.space.obj) → (rankFinalSpace S).obj from q) :=
    continuous_coinduced_rng
  exact CGWH.map ⟨q ∘ j, hq.comp hj⟩

private theorem rankFinalLift_fac {X Y : RankSpace α} {S : Sieve X} {g : Y ⟶ X} (hg : S g) :
    rankFinalLift hg ≫ rankFinalInclusion S = (U).map g :=
  cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ (fun _ => rfl))

private theorem rankSieveMap_quotient_of_canonical {X : RankSpace α} {S : Sieve X}
    (hcard : preBeth α = α.card) (hω : ℵ₀ < preBeth α)
    (hS : S ∈ Sheaf.canonicalTopology (RankSpace α) X) : IsQuotientMap (rankSieveMap S) := by
  have hsurj := rankSieveMap_surj_of_canonical hcard hω hS
  obtain ⟨Z, ⟨homeo⟩⟩ := rankSpace_representative hcard (rankFinalSpace S) X.carrier_lt
  let e := cgwhIsoOfHomeo homeo
  let π : Z ⟶ X := (U).preimage (e.hom ≫ rankFinalInclusion S)
  have hπ : (U).map π = e.hom ≫ rankFinalInclusion S := Functor.map_preimage U _
  have hp : Mono π := by
    have hmono : Mono ((U).map π) := (CGWH.mono_iff_injective _).mpr (hπ ▸ homeo.injective)
    exact Functor.mono_of_mono_map U hmono
  let a : S.arrows.FamilyOfElements (yoneda.obj Z) :=
    fun {_} g hg => (U).preimage (rankFinalLift hg ≫ e.inv)
  have ha {Y : RankSpace α} (g : Y ⟶ X) (hg : S g) : a g hg ≫ π = g := by
    apply (U).map_injective
    simp only [a, Functor.map_comp, Functor.map_preimage, hπ, Category.assoc, Iso.inv_hom_id_assoc,
      rankFinalLift_fac]
  have hac : a.Compatible := by
    intro Y₁ Y₂ A f₁ f₂ g₁ g₂ r₁ r₂ h
    letI := hp
    apply (cancel_mono π).mp
    change (f₁ ≫ a g₁ r₁) ≫ π = (f₂ ≫ a g₂ r₂) ≫ π
    rw [Category.assoc, Category.assoc, ha, ha]
    exact h
  obtain ⟨d, hd, _⟩ := Sheaf.isSheaf_yoneda_obj Z _ hS a hac
  have hr : d ≫ π = 𝟙 X := by
    apply rankHom_ext
    intro x
    obtain ⟨⟨⟨Y, g, hg⟩, y⟩, h⟩ := hsurj x
    change ((U).map g).hom y = x at h
    rw [← h]
    have eq : g ≫ (d ≫ π) = g ≫ 𝟙 X := by
      rw [← Category.assoc, show g ≫ d = a g hg from hd g hg, ha, Category.comp_id]
    exact rankHom_eval eq y
  have hid : Continuous (show X.space.obj → (rankFinalSpace S).obj from id) := by
    have h : Continuous (fun x : X.space.obj => homeo (((U).map d).hom x)) :=
      homeo.continuous.comp ((U).map d).hom.hom.hom.continuous
    convert h using 1
    funext x
    have heq := rankHom_eval hr x
    change ((U).map π).hom (((U).map d).hom x) = x at heq
    rw [hπ] at heq
    exact heq.symm
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun T => ⟨?_, fun h =>
    h.preimage (rankSieveMap_continuous S)⟩, hsurj⟩
  intro h
  have hT : IsOpen (show Set (rankFinalSpace S).obj from T) := isOpen_coinduced.mpr h
  exact hT.preimage hid


private theorem rankSieveMap_pullback_quotient {X Y : RankSpace α} {S : Sieve X}
    (hω : ℵ₀ < preBeth α) (hcard : preBeth α = α.card)
    (g : Y ⟶ X) (hS : IsQuotientMap (rankSieveMap S)) :
    IsQuotientMap (rankSieveMap (S.pullback g)) := by
  let I := RankSieveArrows S
  let F (i : I) := i.1.space
  let C := (CGWH.coproductCofan F).pt
  let f : C ⟶ X.space := CGWH.map ⟨rankSieveMap S, rankSieveMap_continuous S⟩
  let L := (CGWH.fibreSubspaceLimit f ((U).map g)).cone.pt
  let a : L.obj → Σ i : I, (F i).obj := fun z => z.val.1
  let b : L.obj → Y.space.obj := fun z => z.val.2
  have ha : Continuous a := (CGWH.fibreSubspaceLimit f ((U).map g)).cone.π.app WalkingCospan.left
    |>.hom.hom.hom.continuous
  have hb : Continuous b := (CGWH.fibreSubspaceLimit f ((U).map g)).cone.π.app WalkingCospan.right
    |>.hom.hom.hom.continuous
  have hq : IsQuotientMap b := CGWH.quotient_baseChange f ((U).map g) hS
  let j (i : I) : (F i).obj → (Σ i : I, (F i).obj) := @Sigma.mk I (fun i => ((F i).obj : Type u)) i
  let A (i : I) : Set L.obj := a ⁻¹' range (j i)
  have hA (i : I) : IsOpen (A i) := isOpen_range_sigmaMk.preimage ha
  have hcover : (⋃ i, A i) = Set.univ := by
    ext z
    exact ⟨fun _ => mem_univ _, fun _ => mem_iUnion.mpr ⟨(a z).1, (a z).2, rfl⟩⟩
  have hT (i : I) : ∃ (W : RankSpace α) (p : W ⟶ i.1) (q : W ⟶ Y) (e : W.space.obj ≃ₜ A i),
      p ≫ i.2.val = q ≫ g ∧ ∀ w, ((U).map q).hom w = b (e w).val := by
    letI : CompactlyGeneratedSpace (A i) := open_compactlyGenerated (hA i)
    let B := CGWH.of (weaklyHausdorff_subspace L.property (A i))
    let e := (IsEmbedding.sigmaMk (i := i) (σ := fun i => ((F i).obj : Type u))).toHomeomorph
    let k : A i → range (j i) := fun x => ⟨a x.val, x.property⟩
    have hk : Continuous k := (ha.comp continuous_subtype_val).subtype_mk _
    let d : A i → (F i).obj := fun x => e.symm (k x)
    have hd : Continuous d := e.symm.continuous.comp hk
    have he (x : A i) : j i (d x) = a x.val :=
      congrArg Subtype.val (e.apply_symm_apply (k x))
    have hinj : Injective (fun x : A i => (d x, b x.val)) := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · change a x.val = a y.val
        rw [← he x, ← he y]
        exact congrArg (j i) (congrArg Prod.fst h)
      · change b x.val = b y.val
        exact congrArg (fun p : (F i).obj × Y.space.obj => p.2) h
    have hc : #(B.obj : Type u) < preBeth α := by
      apply (mk_le_of_injective hinj).trans_lt
      rw [mk_prod, lift_id, lift_id]
      exact mul_lt_of_lt hω.le i.1.carrier_lt Y.carrier_lt
    obtain ⟨W, ⟨ew⟩⟩ := rankSpace_representative hcard B hc
    let p : W ⟶ i.1 := (U).preimage (CGWH.map ⟨d ∘ ew, hd.comp ew.continuous⟩)
    let q : W ⟶ Y := (U).preimage
      (CGWH.map ⟨fun w => b (ew w).val, hb.comp (continuous_subtype_val.comp ew.continuous)⟩)
    have hp (w : W.space.obj) : ((U).map p).hom w = d (ew w) := by
      simp only [p, Functor.map_preimage]
      rfl
    have hq' (w : W.space.obj) : ((U).map q).hom w = b (ew w).val := by
      simp only [q, Functor.map_preimage]
      rfl
    refine ⟨W, p, q, ew, ?_, hq'⟩
    apply rankHom_ext
    intro w
    change ((U).map i.2.val).hom (((U).map p).hom w) =
      ((U).map g).hom (((U).map q).hom w)
    rw [hp, hq']
    have h := (ew w).val.property
    change rankSieveMap S (a (ew w).val) = ((U).map g).hom (b (ew w).val) at h
    rw [← he] at h
    exact h
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun D => ⟨?_, fun h =>
    h.preimage (rankSieveMap_continuous (S.pullback g))⟩, ?_⟩
  · intro hD
    apply hq.isOpen_preimage.mp
    apply (isOpen_iff_of_cover hA hcover).mpr
    intro i
    obtain ⟨W, p, q, e, w, h⟩ := hT i
    have hs : S (q ≫ g) := w ▸ S.downward_closed i.2.property p
    let v : RankSieveArrows (S.pullback g) := ⟨W, q, hs⟩
    let k : W.space.obj → Σ i : RankSieveArrows (S.pullback g), i.1.space.obj :=
      @Sigma.mk _ (fun i => (i.1.space.obj : Type u)) v
    have hk : Continuous k := continuous_sigmaMk
    have hkD : IsOpen (e ⁻¹' (Subtype.val ⁻¹' (b ⁻¹' D))) := by
      have eq : e ⁻¹' (Subtype.val ⁻¹' (b ⁻¹' D)) = k ⁻¹' (rankSieveMap (S.pullback g) ⁻¹' D) :=
        Set.ext fun x => by
          change b (e x).val ∈ D ↔ ((U).map q).hom x ∈ D
          rw [h]
      rw [eq]
      exact hD.preimage hk
    have heD := e.isQuotientMap.isOpen_preimage.mp hkD
    have hE := (hA i).isOpenEmbedding_subtypeVal.isOpenMap _ heD
    have eq : (Subtype.val : A i → L.obj) '' (Subtype.val ⁻¹' (b ⁻¹' D)) = A i ∩ b ⁻¹' D := by
      ext z
      constructor
      · rintro ⟨⟨z, hz⟩, hD, rfl⟩
        exact ⟨hz, hD⟩
      · rintro ⟨hz, hD⟩
        exact ⟨⟨z, hz⟩, hD, rfl⟩
    exact eq ▸ hE
  · intro y
    obtain ⟨z, rfl⟩ := hq.surjective y
    let i := (a z).1
    let z' : A i := ⟨z, (a z).2, rfl⟩
    obtain ⟨W, p, q, e, eq, h⟩ := hT i
    have hs : S (q ≫ g) := eq ▸ S.downward_closed i.2.property p
    refine ⟨⟨⟨W, q, hs⟩, e.symm z'⟩, ?_⟩
    change ((U).map q).hom (e.symm z') = b z
    rw [h, e.apply_symm_apply]


/-- For the actual small rank stage a sieve is canonical precisely when its
family of arrows is jointly submersive. -/
theorem rankCanonicalTopology_iff {X : RankSpace α} (S : Sieve X)
    (hcard : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    S ∈ Sheaf.canonicalTopology (RankSpace α) X ↔ IsQuotientMap (rankSieveMap S) := by
  refine ⟨rankSieveMap_quotient_of_canonical hcard hω, ?_⟩
  intro hS
  apply Sheaf.mem_finestTopology_of_forall_isSheafFor
  rintro _ ⟨Z, rfl⟩ Y g
  exact rankSieveMap_isSheafFor (rankProbe hcard hω) (rankSieveMap_pullback_quotient hω hcard g hS)

private def rankSubmersiveFamily {X : RankSpace α} (R : Presieve X) : Prop :=
  ∃ (I : Type u) (Y : I → RankSpace α) (f : ∀ i, Y i ⟶ X),
    R = Presieve.ofArrows Y f ∧ IsQuotientMap
      (fun y : Σ i, (Y i).space.obj => ((U).map (f y.1)).hom y.2)

/-- Submersive families, with all index repetitions removed by the presieve. -/
def rankSubmersivePrecoverage (α : Ordinal.{u}) : Precoverage (RankSpace α) where
  coverings _ := {R | rankSubmersiveFamily R}

private theorem rankSieve_quotient_of_family {X : RankSpace α} {I : Type u}
    {Y : I → RankSpace α} (f : ∀ i, Y i ⟶ X) (S : Sieve X)
    (hf : ∀ i, S (f i))
    (h : IsQuotientMap (fun y : Σ i, (Y i).space.obj => ((U).map (f y.1)).hom y.2)) :
    IsQuotientMap (rankSieveMap S) := by
  let k : (Σ i, (Y i).space.obj) → Σ j : RankSieveArrows S, j.1.space.obj :=
    fun y => ⟨⟨Y y.1, f y.1, hf y.1⟩, y.2⟩
  have hk : Continuous k := by
    apply continuous_sigma
    intro i
    let j : RankSieveArrows S := ⟨Y i, f i, hf i⟩
    exact (continuous_sigmaMk (σ := fun j : RankSieveArrows S => (j.1.space.obj : Type u)) (i := j))
  exact IsQuotientMap.of_comp hk (rankSieveMap_continuous S) h

/-- Lemma E.3.5.7. The topology generated by the families in Cov1 is the
canonical Grothendieck topology. -/
theorem rankSubmersiveTopology_eq_canonical
    (hcard : preBeth α = α.card) (hω : ℵ₀ < preBeth α) :
    (rankSubmersivePrecoverage α).toGrothendieck = Sheaf.canonicalTopology (RankSpace α) := by
  apply le_antisymm
  · apply (Precoverage.toGrothendieck_le_iff_le_toPrecoverage).mpr
    intro X R hR
    change rankSubmersiveFamily R at hR
    obtain ⟨I, Y, f, rfl, h⟩ := hR
    apply (rankCanonicalTopology_iff _ hcard hω).mpr
    exact rankSieve_quotient_of_family f _ (fun i => Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i)) h
  · intro X S hS
    let I := RankSieveArrows S
    let R := Presieve.ofArrows (fun i : I => i.1) (fun i => i.2.val)
    have hR : R ∈ rankSubmersivePrecoverage α X :=
      show rankSubmersiveFamily R from ⟨I, _, _, rfl, (rankCanonicalTopology_iff S hcard hω).mp hS⟩
    have hgen := (rankSubmersivePrecoverage α).generate_mem_toGrothendieck hR
    apply (rankSubmersivePrecoverage α).toGrothendieck.superset_covering ?_ hgen
    apply (Sieve.generate_le_iff _ _).mpr
    exact Presieve.ofArrows_le_iff.mpr (fun i => i.2.property)

end

end Masullo
