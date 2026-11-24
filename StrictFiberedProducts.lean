import StrictBasedPullbacks

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.VerticalIsoComma

universe u

variable {D : Type u} [SmallCategory D]

section FullSubcategory

variable {W : BasedCategory.{u, u} D} (P : ObjectProperty W.obj)

private def fullBased : BasedCategory.{u, u} D :=
  BasedCategory.ofFunctor (P.ι ⋙ W.p)

private def fullInclusion : fullBased P ⥤ᵇ W where
  toFunctor := P.ι
  w := rfl

private theorem fullStrong {R Q : D} {a b : P.FullSubcategory}
    (f : R ⟶ Q) (m : a ⟶ b) (hm : W.p.IsStronglyCartesian f m.hom) :
    (fullBased P).p.IsStronglyCartesian f m := by
  let I := fullInclusion P
  haveI : W.p.IsHomLift f (I.map m) := hm.toIsHomLift
  refine { toIsHomLift := I.isHomLift_map f m, universal_property' := ?_ }
  intro c g n hn
  letI : (fullBased P).p.IsHomLift (g ≫ f) n := hn
  haveI : W.p.IsHomLift (g ≫ f) (I.map n) := I.preserves_isHomLift (g ≫ f) n
  haveI : W.p.IsStronglyCartesian f (I.map m) := hm
  obtain ⟨k, ⟨hk, he⟩, hu⟩ := IsStronglyCartesian.universal_property W.p f (I.map m)
    (a' := I.obj c) g (g ≫ f) rfl (I.map n)
  let j : c ⟶ a := ⟨k⟩
  haveI : W.p.IsHomLift g (I.map j) := hk
  refine ⟨j, ⟨I.isHomLift_map g j, ObjectProperty.hom_ext _ he⟩, ?_⟩
  rintro r ⟨hr, heq⟩
  letI : (fullBased P).p.IsHomLift g r := hr
  apply ObjectProperty.hom_ext
  exact hu (I.map r) ⟨I.preserves_isHomLift g r, congrArg InducedCategory.Hom.hom heq⟩

theorem preserves_of_lifts {T : BasedCategory.{u, u} D} (I : T ⥤ᵇ W)
    (h : ∀ (b : T.obj) (R : D) (f : R ⟶ T.p.obj b),
      ∃ (a : T.obj) (m : a ⟶ b), T.p.IsStronglyCartesian f m ∧
        W.p.IsStronglyCartesian f (I.map m)) :
    PreservesCartesian I := by
  intro R Q a b f m hm
  let p := T.p
  haveI : p.IsHomLift f m := hm.toIsHomLift
  have hQ : p.obj b = Q := codomain_eq p f m
  subst Q
  obtain ⟨c, n, hn, hw⟩ := h b R f
  haveI : p.IsStronglyCartesian f n := hn
  haveI : p.IsStronglyCartesian f m := hm
  haveI : p.IsCartesian f n := IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f n
  haveI : p.IsCartesian f m := IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f m
  let e := IsCartesian.domainUniqueUpToIso p f n m
  have he : e.hom ≫ n = m := IsCartesian.fac p f n m
  haveI : p.IsHomLift (𝟙 R) e.hom := IsCartesian.domainUniqueUpToIso_inv_isHomLift p f n m
  haveI : W.p.IsHomLift (𝟙 R) (I.map e.hom) := I.preserves_isHomLift (𝟙 R) e.hom
  haveI : IsIso (I.map e.hom) := inferInstanceAs (IsIso ((I.toFunctor.mapIso e).hom))
  haveI : W.p.IsStronglyCartesian (𝟙 R) (I.map e.hom) := IsStronglyCartesian.of_isIso _ _ _
  haveI : W.p.IsStronglyCartesian f (I.map n) := hw
  have hh : W.p.IsStronglyCartesian (𝟙 R ≫ f) (I.map e.hom ≫ I.map n) :=
    IsStronglyCartesian.comp W.p
  have hmap : I.map e.hom ≫ I.map n = I.map m :=
    (I.toFunctor.map_comp e.hom n).symm.trans (congrArg (fun j : a ⟶ b => I.map j) he)
  rw [hmap, Category.id_comp] at hh
  exact hh

private def fullFactor {T : BasedCategory.{u, u} D} (A : T ⥤ᵇ W)
    (hA : ∀ a, P (A.obj a)) : T ⥤ᵇ fullBased P where
  toFunctor := {
    obj a := ⟨A.obj a, hA a⟩
    map m := ⟨A.map m⟩
    map_id a := ObjectProperty.hom_ext _ (A.toFunctor.map_id a)
    map_comp m n := ObjectProperty.hom_ext _ (A.toFunctor.map_comp m n) }
  w := A.w

set_option backward.isDefEq.respectTransparency false in
private theorem fullFactor_cancel {T : BasedCategory.{u, u} D} {A B : T ⥤ᵇ fullBased P}
    (he : A ⋙ fullInclusion P = B ⋙ fullInclusion P) : A = B := by
  cases A with
  | mk A ha =>
    cases B with
    | mk B hb =>
      have hAB : A ⋙ P.ι = B ⋙ P.ι := congrArg BasedFunctor.toFunctor he
      have hh (a : T.obj) : A.obj a = B.obj a := by
        apply ObjectProperty.FullSubcategory.ext
        exact Functor.congr_obj hAB a
      have h : A = B := by
        refine CategoryTheory.Functor.ext hh ?_
        intro a b m
        apply ObjectProperty.hom_ext
        change P.ι.map (A.map m) = P.ι.map (eqToHom (hh a) ≫ B.map m ≫ eqToHom (hh b).symm)
        rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
        exact Functor.congr_hom hAB m
      cases h
      rfl

end FullSubcategory

section Product

variable {X Y S : BasedCategory.{u, u} D} (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- A collection of matched objects is stable if a compatible lift of
every base arrow can be chosen with source in the same collection. -/
def StrictObjectStable (P : ObjectProperty (StrictObj F G)) : Prop :=
  ∀ (a : StrictObj F G), P a → ∀ (R : D) (f : R ⟶ X.p.obj a.obj.left),
    ∃ (b : StrictObj F G) (_ : P b) (m : b ⟶ a),
      X.p.IsStronglyCartesian f m.hom.left ∧ Y.p.IsStronglyCartesian f m.hom.right

private def stableStrictObject : ObjectProperty (StrictObj F G) :=
  fun a => ∃ P, StrictObjectStable F G P ∧ P a

private theorem stableStrictObject_stable : StrictObjectStable F G (stableStrictObject F G) := by
  rintro a ⟨P, hP, ha⟩ R f
  obtain ⟨b, hb, m, hL, hR⟩ := hP a ha R f
  exact ⟨b, ⟨P, hP, hb⟩, m, hL, hR⟩

/-- The full subcategory of the strict product on matched objects that
belong to a stable collection. -/
def supportedStrictBased : BasedCategory.{u, u} D :=
  fullBased (W := strictBased F G) (stableStrictObject F G)

def supportedStrictInclusion : supportedStrictBased F G ⥤ᵇ strictBased F G :=
  fullInclusion (W := strictBased F G) (stableStrictObject F G)

def supportedFst : supportedStrictBased F G ⥤ᵇ X := supportedStrictInclusion F G ⋙ strictFst F G

def supportedSnd : supportedStrictBased F G ⥤ᵇ Y := supportedStrictInclusion F G ⋙ strictSnd F G

theorem supportedStrictCone : supportedFst F G ⋙ F = supportedSnd F G ⋙ G :=
  congrArg (supportedStrictInclusion F G ⋙ ·) (strictCone F G)

private theorem supportedStrong (hG : PreservesCartesian G)
    (a : (stableStrictObject F G).FullSubcategory) (R : D)
    (f : R ⟶ (strictBased F G).p.obj a.obj) :
    ∃ (b : (stableStrictObject F G).FullSubcategory) (m : b ⟶ a),
      (strictBased F G).p.IsStronglyCartesian f m.hom ∧
      (based F G).p.IsStronglyCartesian f m.hom.hom := by
  obtain ⟨b, hb, m, hL, hR⟩ := stableStrictObject_stable F G a.obj a.property R f
  let m' : (⟨b, hb⟩ : (stableStrictObject F G).FullSubcategory) ⟶ a := ⟨m⟩
  have hh := strong_of_components hG f m.hom hL hR
  exact ⟨⟨b, hb⟩, m', fullStrong (W := based F G) (isStrictComparison F G) f m hh, hh⟩

theorem supportedStrictFibered (hG : PreservesCartesian G) :
    (supportedStrictBased F G).p.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain ⟨b, m, hm, _⟩ := supportedStrong F G hG a R f
  exact ⟨b, m, fullStrong (W := strictBased F G) (stableStrictObject F G) f m hm⟩

private theorem supportedToIso_preserves (hG : PreservesCartesian G) :
    PreservesCartesian (supportedStrictInclusion F G ⋙ strictToIso F G) := by
  apply preserves_of_lifts
  intro a R f
  obtain ⟨b, m, hs, hi⟩ := supportedStrong F G hG a R f
  exact ⟨b, m, fullStrong (W := strictBased F G) (stableStrictObject F G) f m hs, hi⟩

theorem supportedStrict_projections [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G) :
    PreservesCartesian (supportedFst F G) ∧ PreservesCartesian (supportedSnd F G) := by
  obtain ⟨hL, hR⟩ := preserves_projections hF hG
  exact ⟨fun f m hm => hL f _ (supportedToIso_preserves F G hG f m hm),
    fun f m hm => hR f _ (supportedToIso_preserves F G hG f m hm)⟩

/-- The universal property ranges over all fibered categories as test
objects, even if the given fibers are groupoids. -/
theorem supportedStrict_universal (hG : PreservesCartesian G) {T : BasedCategory.{u, u} D}
    [T.p.IsFibered] (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (h : A ⋙ F = B ⋙ G)
    (hA : PreservesCartesian A) (hB : PreservesCartesian B) :
    ∃! L : T ⥤ᵇ supportedStrictBased F G,
      L ⋙ supportedFst F G = A ∧ L ⋙ supportedSnd F G = B ∧ PreservesCartesian L := by
  let L := strictLift F G A B h
  let P : ObjectProperty (StrictObj F G) := fun b => ∃ x, L.obj x = b
  have hP : StrictObjectStable F G P := by
    rintro _ ⟨x, rfl⟩ R f
    have hx : X.p.obj (L.obj x).obj.left = T.p.obj x := A.w_obj x
    obtain ⟨y, m, hm'⟩ := IsPreFibered.exists_isCartesian T.p (a := x) hx.symm f
    haveI := hm'
    have hm : T.p.IsStronglyCartesian f m := inferInstance
    exact ⟨L.obj y, ⟨y, rfl⟩, L.map m, hA f m hm, hB f m hm⟩
  let L' := fullFactor (stableStrictObject F G) L (fun x => ⟨P, hP, x, rfl⟩)
  have he : L' ⋙ supportedStrictInclusion F G = L := rfl
  have hh : PreservesCartesian L' := by
    intro R Q a b f m hm
    exact fullStrong (W := strictBased F G) (stableStrictObject F G) f (L'.map m)
      (strictLift_preserves F G hG A B h hA hB f m hm)
  refine ⟨L', ⟨(strictLift_projections F G A B h).1,
    (strictLift_projections F G A B h).2, hh⟩, ?_⟩
  intro N hN
  apply fullFactor_cancel (W := strictBased F G) (stableStrictObject F G)
  have hN' : (N ⋙ supportedStrictInclusion F G) ⋙ strictFst F G = A ∧
      (N ⋙ supportedStrictInclusion F G) ⋙ strictSnd F G = B := ⟨hN.1, hN.2.1⟩
  have hu := (strictLift_unique F G A B h).unique hN' (strictLift_projections F G A B h)
  exact hu.trans he.symm

theorem supportedStrict_groupoidal
    (hX : ∀ (U : D) {a b : X.obj} (m : a ⟶ b), X.p.IsHomLift (𝟙 U) m → IsIso m)
    (hY : ∀ (U : D) {a b : Y.obj} (m : a ⟶ b), Y.p.IsHomLift (𝟙 U) m → IsIso m)
    (U : D) {a b : (supportedStrictBased F G).obj} (m : a ⟶ b)
    (hm : (supportedStrictBased F G).p.IsHomLift (𝟙 U) m) : IsIso m := by
  let I := supportedStrictInclusion F G ⋙ strictToIso F G
  haveI := hm
  have hi : (based F G).p.IsHomLift (𝟙 U) (I.map m) := I.preserves_isHomLift (𝟙 U) m
  haveI : IsIso (I.map m) := vertical_arrow_isIso hX hY _ hi
  have hff : I.toFunctor.FullyFaithful :=
    ((stableStrictObject F G).fullyFaithfulι).comp (strictToIso_fullyFaithful F G)
  exact hff.isIso_of_isIso_map m

end Product

end Masullo.VerticalIsoComma
