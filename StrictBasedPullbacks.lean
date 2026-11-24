import VerticalIsoCommaFibered
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.VerticalIsoComma

universe u

variable {D : Type u} [SmallCategory D]
  {X Y S : BasedCategory.{u, u} D} (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- The strict fiber product consists of the canonical equality
isomorphisms in the based iso-comma category. -/
def isStrictComparison : ObjectProperty (Obj F G) :=
  fun a => ∃ h : F.obj a.left = G.obj a.right, a.iso.hom = eqToHom h

abbrev StrictObj := (isStrictComparison F G).FullSubcategory

def strictBased : BasedCategory.{u, u} D :=
  BasedCategory.ofFunctor ((isStrictComparison F G).ι ⋙ (based F G).p)

/-- The comparison of the strict pullback with the two-fiber product. -/
def strictToIso : strictBased F G ⥤ᵇ based F G where
  toFunctor := (isStrictComparison F G).ι
  w := rfl

def strictToIso_fullyFaithful : (strictToIso F G).toFunctor.FullyFaithful :=
  (isStrictComparison F G).fullyFaithfulι

def strictFst : strictBased F G ⥤ᵇ X := strictToIso F G ⋙ fst F G

def strictSnd : strictBased F G ⥤ᵇ Y := strictToIso F G ⋙ snd F G

private theorem based_ext {U V : BasedCategory.{u, u} D} {L M : U ⥤ᵇ V}
    (h : L.toFunctor = M.toFunctor) : L = M := by
  cases L
  cases M
  cases h
  rfl

theorem strictObj_ext {a b : StrictObj F G}
    (hl : a.obj.left = b.obj.left) (hr : a.obj.right = b.obj.right) : a = b := by
  rcases a with ⟨⟨ax, ay, ai, ha⟩, ha'⟩
  rcases b with ⟨⟨bx, byy, bi, hb⟩, hb'⟩
  change ax = bx at hl
  change ay = byy at hr
  subst bx byy
  obtain ⟨e, he⟩ := ha'
  obtain ⟨_, he'⟩ := hb'
  have hi : ai = bi := Iso.ext (he.trans he'.symm)
  subst bi
  rfl

theorem strictCone : strictFst F G ⋙ F = strictSnd F G ⋙ G := by
  have h (a : StrictObj F G) : F.obj a.obj.left = G.obj a.obj.right := a.property.choose
  have hm (a : StrictObj F G) : a.obj.iso.hom = eqToHom (h a) := a.property.choose_spec
  apply based_ext
  refine CategoryTheory.Functor.ext h ?_
  intro a b f
  change StrictObj F G at a b
  have hs := f.hom.square
  change F.map f.hom.left = eqToHom (h a) ≫ G.map f.hom.right ≫ eqToHom (h b).symm
  rw [hm a, hm b] at hs
  calc
    _ = (F.map f.hom.left ≫ eqToHom (h b)) ≫ eqToHom (h b).symm := by simp
    _ = _ := by rw [hs, Category.assoc]

variable {T : BasedCategory.{u, u} D}

private theorem eqToBasedIso_app {L M : T ⥤ᵇ S} (h : L = M) (a : T.obj) :
    (eqToIso h).hom.toNatTrans.app a = eqToHom (congrArg (fun J : T ⥤ᵇ S => J.obj a) h) := by
  cases h
  rfl

/-- The strict lift of a strictly commuting cone. -/
def strictLift (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (h : A ⋙ F = B ⋙ G) :
    T ⥤ᵇ strictBased F G where
  toFunctor := {
    obj a := ⟨(lift F G A B (eqToIso h)).obj a, by
      refine ⟨congrArg (fun L : T ⥤ᵇ S => L.obj a) h, ?_⟩
      rw [lift_comparison]
      exact eqToBasedIso_app h a⟩
    map m := ⟨(lift F G A B (eqToIso h)).map m⟩
    map_id a := ObjectProperty.hom_ext _ ((lift F G A B (eqToIso h)).map_id a)
    map_comp m n := ObjectProperty.hom_ext _ ((lift F G A B (eqToIso h)).map_comp m n) }
  w := A.w

theorem strictLift_projections (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (h : A ⋙ F = B ⋙ G) :
    strictLift F G A B h ⋙ strictFst F G = A ∧ strictLift F G A B h ⋙ strictSnd F G = B := by
  exact ⟨lift_fst F G A B (eqToIso h), lift_snd F G A B (eqToIso h)⟩

/-- A strict cone has a unique based lift through the strict pullback. -/
theorem strictLift_unique (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (h : A ⋙ F = B ⋙ G) :
    ∃! L : T ⥤ᵇ strictBased F G,
      L ⋙ strictFst F G = A ∧ L ⋙ strictSnd F G = B := by
  let M := strictLift F G A B h
  refine ⟨M, strictLift_projections F G A B h, ?_⟩
  intro L hL
  have eqL : L ⋙ strictFst F G = M ⋙ strictFst F G :=
    hL.1.trans (strictLift_projections F G A B h).1.symm
  have eqR : L ⋙ strictSnd F G = M ⋙ strictSnd F G :=
    hL.2.trans (strictLift_projections F G A B h).2.symm
  have hObj (x : T.obj) : L.obj x = M.obj x := by
    have hl := congrArg (fun J : T ⥤ᵇ X => J.obj x) eqL
    have hr := congrArg (fun J : T ⥤ᵇ Y => J.obj x) eqR
    exact strictObj_ext F G hl hr
  have hFunctor : L.toFunctor = M.toFunctor := by
    refine CategoryTheory.Functor.ext hObj ?_
    intro x y f
    apply ObjectProperty.hom_ext
    apply Arrow.ext
    · change (strictFst F G).map (L.map f) =
        (strictFst F G).map (eqToHom (hObj x) ≫ M.map f ≫ eqToHom (hObj y).symm)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_map]
      exact CategoryTheory.Functor.congr_hom (congrArg BasedFunctor.toFunctor eqL) f
    · change (strictSnd F G).map (L.map f) =
        (strictSnd F G).map (eqToHom (hObj x) ≫ M.map f ≫ eqToHom (hObj y).symm)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_map]
      exact CategoryTheory.Functor.congr_hom (congrArg BasedFunctor.toFunctor eqR) f
  exact based_ext hFunctor

/-- Having enough componentwise lifts means the matched objects and arrows
can be chosen together in the strict product. -/
def HasComponentLifts : Prop :=
  ∀ (a : StrictObj F G) (R : D) (f : R ⟶ X.p.obj a.obj.left),
    ∃ (b : StrictObj F G) (m : b ⟶ a),
      X.p.IsStronglyCartesian f m.hom.left ∧ Y.p.IsStronglyCartesian f m.hom.right

private theorem strong_of_ambient {R Q : D} {a b : StrictObj F G}
    (f : R ⟶ Q) (m : a ⟶ b)
    (hm : (based F G).p.IsStronglyCartesian f m.hom) :
    (strictBased F G).p.IsStronglyCartesian f m := by
  let I := strictToIso F G
  haveI : (based F G).p.IsHomLift f (I.map m) := hm.toIsHomLift
  refine { toIsHomLift := I.isHomLift_map f m, universal_property' := ?_ }
  intro c g n hn
  letI : (strictBased F G).p.IsHomLift (g ≫ f) n := hn
  haveI : (based F G).p.IsHomLift (g ≫ f) (I.map n) := I.preserves_isHomLift (g ≫ f) n
  haveI : (based F G).p.IsStronglyCartesian f (I.map m) := hm
  have h := IsStronglyCartesian.universal_property (based F G).p f (I.map m)
    (a' := I.obj c) g (g ≫ f) rfl (I.map n)
  obtain ⟨k, ⟨hk, hkm⟩, huniq⟩ := h
  let j : c ⟶ a := ⟨k⟩
  haveI : (based F G).p.IsHomLift g (I.map j) := hk
  refine ⟨j, ⟨I.isHomLift_map g j, ObjectProperty.hom_ext _ hkm⟩, ?_⟩
  rintro r ⟨hr, he⟩
  letI : (strictBased F G).p.IsHomLift g r := hr
  apply ObjectProperty.hom_ext
  exact huniq (I.map r) ⟨I.preserves_isHomLift g r, congrArg InducedCategory.Hom.hom he⟩

/-- The strict product is fibered under the componentwise hypothesis. -/
theorem strictFibered (hG : PreservesCartesian G) (hc : HasComponentLifts F G) :
    (strictBased F G).p.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain ⟨b, m, hL, hR⟩ := hc a R f
  exact ⟨b, m, strong_of_ambient F G f m (strong_of_components hG f m.hom hL hR)⟩

/-- The comparison functor preserves Cartesian arrows when the strict
pullback has sufficient componentwise lifts. -/
theorem strictToIso_preserves (hG : PreservesCartesian G) (hc : HasComponentLifts F G) :
    PreservesCartesian (strictToIso F G) := by
  intro R Q a b f m hm
  let I := strictToIso F G
  let p := (strictBased F G).p
  let q := (based F G).p
  haveI : p.IsHomLift f m := hm.toIsHomLift
  have hQ : X.p.obj b.obj.left = Q := codomain_eq p f m
  subst Q
  obtain ⟨c, n, hnL, hnR⟩ := hc b R f
  have hnStrong : q.IsStronglyCartesian f (I.map n) := strong_of_components hG f n.hom hnL hnR
  haveI : p.IsStronglyCartesian f n := strong_of_ambient F G f n hnStrong
  haveI : p.IsStronglyCartesian f m := hm
  haveI : p.IsCartesian f n := IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f n
  haveI : p.IsCartesian f m := IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f m
  let e := IsCartesian.domainUniqueUpToIso p f n m
  have he : e.hom ≫ n = m := IsCartesian.fac p f n m
  haveI : p.IsHomLift (𝟙 R) e.hom := IsCartesian.domainUniqueUpToIso_inv_isHomLift p f n m
  haveI : q.IsHomLift (𝟙 R) (I.map e.hom) := I.preserves_isHomLift (𝟙 R) e.hom
  haveI : IsIso (I.map e.hom) :=
    inferInstanceAs (IsIso ((I.toFunctor.mapIso e).hom))
  haveI : q.IsStronglyCartesian (𝟙 R) (I.map e.hom) := IsStronglyCartesian.of_isIso _ _ _
  haveI : q.IsStronglyCartesian f (I.map n) := hnStrong
  have h : q.IsStronglyCartesian (𝟙 R ≫ f) (I.map e.hom ≫ I.map n) :=
    IsStronglyCartesian.comp q
  have hmap : I.map e.hom ≫ I.map n = I.map m :=
    (I.toFunctor.map_comp e.hom n).symm.trans
      (congrArg (fun a : a ⟶ b => I.map a) he)
  rw [hmap, Category.id_comp] at h
  exact h

/-- A strict commuting cone of Cartesian functors has a Cartesian
universal functor to the strict product. -/
theorem strictLift_preserves (hG : PreservesCartesian G) (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y)
    (h : A ⋙ F = B ⋙ G) (hA : PreservesCartesian A) (hB : PreservesCartesian B) :
    PreservesCartesian (strictLift F G A B h) := by
  intro R Q a b f m hm
  exact strong_of_ambient F G f _ (preserves_lift hG A B (eqToIso h) hA hB f m hm)

/-- Lemmas E.5.7.18 and E.5.7.20. The existing strict pullback in based
categories computes the strict pullback of fibered categories when it has
componentwise lifts. The comparison with the two-fiber product is fully
faithful and preserves the Cartesian arrows under the same hypothesis. -/
theorem strictFibered_projections [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G)
    (hc : HasComponentLifts F G) :
    (strictBased F G).p.IsFibered ∧
      PreservesCartesian (strictToIso F G) ∧
      PreservesCartesian (strictFst F G) ∧ PreservesCartesian (strictSnd F G) := by
  have hi : PreservesCartesian (strictToIso F G) := strictToIso_preserves F G hG hc
  obtain ⟨hL, hR⟩ := preserves_projections hF hG
  exact ⟨strictFibered F G hG hc, hi,
    fun f m hm => hL f _ (hi f m hm), fun f m hm => hR f _ (hi f m hm)⟩

/-- When each fiber of the middle category is discrete, every vertical
comparison isomorphism is induced by equality of the two objects. -/
theorem all_strict_of_discreteFibers
    (hS : ∀ (U : D) (a b : Fiber S.p U) (m : a ⟶ b), ∃ e : a = b, m = eqToHom e) :
    ∀ a : Obj F G, isStrictComparison F G a := by
  intro a
  let U := X.p.obj a.left
  let x : Fiber S.p U := ⟨F.obj a.left, F.w_obj a.left⟩
  let y : Fiber S.p U := ⟨G.obj a.right, (G.w_obj a.right).trans (base_eq a)⟩
  let m : x ⟶ y := ⟨a.iso.hom, a.vertical⟩
  obtain ⟨e, he⟩ := hS U x y m
  refine ⟨congrArg Fiber.fiberInclusion.obj e, ?_⟩
  have h := congrArg Fiber.fiberInclusion.map he
  rw [eqToHom_map] at h
  exact h

/-- The strict and iso-comma products are strictly isomorphic as based
categories when all comparison isomorphisms come from equalities. -/
def isoToStrict (h : ∀ a : Obj F G, isStrictComparison F G a) :
    based F G ⥤ᵇ strictBased F G where
  toFunctor := {
    obj a := ⟨a, h a⟩
    map m := ⟨m⟩
    map_id _ := rfl
    map_comp _ _ := rfl }
  w := rfl

theorem strictComparison_isomorphism
    (h : ∀ a : Obj F G, isStrictComparison F G a) :
    strictToIso F G ⋙ isoToStrict F G h = BasedFunctor.id (strictBased F G) ∧
    isoToStrict F G h ⋙ strictToIso F G = BasedFunctor.id (based F G) := by
  exact ⟨rfl, rfl⟩

/-- Lemma E.5.7.26. For a discrete middle fiber, the strict product
has componentwise lifts and its comparison with the two-fiber product
has a strict inverse over the base. -/
theorem strictProduct_of_discreteFibers [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G)
    (hS : ∀ (U : D) (a b : Fiber S.p U) (m : a ⟶ b), ∃ e : a = b, m = eqToHom e) :
    let h := all_strict_of_discreteFibers F G hS
    (strictBased F G).p.IsFibered ∧
      strictToIso F G ⋙ isoToStrict F G h = BasedFunctor.id (strictBased F G) ∧
      isoToStrict F G h ⋙ strictToIso F G = BasedFunctor.id (based F G) := by
  let h := all_strict_of_discreteFibers F G hS
  have hc : HasComponentLifts F G := by
    intro a R f
    obtain ⟨b, m, hL, hR⟩ := exists_componentLift hF hG a.obj R f
    exact ⟨⟨b, h b⟩, ⟨m⟩, hL, hR⟩
  exact ⟨strictFibered F G hG hc, strictComparison_isomorphism F G h⟩

/-- Every fiber of the strict product is a groupoid when the two
outer categories are fibered in groupoids. -/
theorem strictFiber_isGroupoid
    (hX : ∀ (U : D) {a b : X.obj} (m : a ⟶ b), X.p.IsHomLift (𝟙 U) m → IsIso m)
    (hY : ∀ (U : D) {a b : Y.obj} (m : a ⟶ b), Y.p.IsHomLift (𝟙 U) m → IsIso m)
    (U : D) {a b : Fiber (strictBased F G).p U} (m : a ⟶ b) : IsIso m := by
  let I := strictToIso F G
  let a' := Fiber.fiberInclusion.map m
  haveI : (strictBased F G).p.IsHomLift (𝟙 U) a' := m.property
  have hj : (based F G).p.IsHomLift (𝟙 U) (I.map a') := I.preserves_isHomLift (𝟙 U) a'
  have hIso : IsIso (I.map a') := vertical_arrow_isIso hX hY _ hj
  let e : a.val ≅ b.val := ObjectProperty.isoMk (isStrictComparison F G)
    (@asIso _ _ _ _ (I.map a') hIso)
  have he : e.hom = a' := rfl
  haveI : (strictBased F G).p.IsHomLift (𝟙 U) e.hom := he.symm ▸ m.property
  let n : b ⟶ a := ⟨e.inv, IsHomLift.lift_id_inv (strictBased F G).p U e⟩
  refine ⟨⟨n, Fiber.hom_ext ?_, Fiber.hom_ext ?_⟩⟩
  · change a' ≫ e.inv = 𝟙 a.val
    rw [← he]
    exact e.hom_inv_id
  · change e.inv ≫ a' = 𝟙 b.val
    rw [← he]
    exact e.inv_hom_id

end Masullo.VerticalIsoComma
