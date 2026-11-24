import StrictFiberedProducts

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.BasedInertia

open VerticalIsoComma

universe u v w
variable {D : Type u} [SmallCategory D] (X : BasedCategory.{u, u} D)

private abbrev base : BasedCategory.{u, u} D := BasedCategory.ofFunctor (Functor.id D)

private def toBase : X ⥤ᵇ base where
  toFunctor := X.p
  w := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem toBase_preserves : PreservesCartesian (toBase X) := by
  intro R Q a b f m hm
  haveI := hm.toIsHomLift
  refine { toIsHomLift := (toBase X).preserves_isHomLift f m, universal_property' := ?_ }
  intro c g n hn
  letI := hn
  have hRa := domain_eq X.p f m
  let k : c ⟶ X.p.obj a := g ≫ eqToHom hRa.symm
  have hk : (base (D := D)).p.IsHomLift g k := by
    apply IsHomLift.of_fac' (base (D := D)).p g k rfl hRa
    exact (Category.id_comp _).symm
  refine ⟨k, ⟨hk, ?_⟩, ?_⟩
  · let hQb := codomain_eq X.p f m
    have h₁ : X.p.map m = eqToHom hRa ≫ f ≫ eqToHom hQb.symm := fac' X.p f m
    have h₂ : n = (g ≫ f) ≫ eqToHom hQb.symm := by
      have h := fac' (base (D := D)).p (g ≫ f) n
      change n = eqToHom (show c = c from rfl) ≫ (g ≫ f) ≫ eqToHom hQb.symm at h
      simpa only [eqToHom_refl, Category.id_comp] using h
    change k ≫ X.p.map m = n
    rw [h₁, h₂]
    change (g ≫ eqToHom hRa.symm) ≫ (eqToHom hRa ≫ f ≫ eqToHom hQb.symm) = _
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · rintro r ⟨hr, _⟩
    letI := hr
    have h := fac' (base (D := D)).p g r
    change r = eqToHom (show c = c from rfl) ≫ g ≫ eqToHom hRa.symm at h
    simpa only [k, eqToHom_refl, Category.id_comp] using h

/-- Product over the base, using the vertical iso-comma for the two maps
to the identity category over the base. -/
abbrev product := VerticalIsoComma.based (toBase X) (toBase X)

set_option backward.isDefEq.respectTransparency false in
private theorem productStrict (a : VerticalIsoComma.Obj (toBase X) (toBase X)) :
    isStrictComparison (toBase X) (toBase X) a := by
  haveI := a.vertical
  have h : (toBase X).obj a.left = (toBase X).obj a.right := (base_eq a).symm
  refine ⟨h, ?_⟩
  have he := fac' (base (D := D)).p (𝟙 (X.p.obj a.left)) a.iso.hom
  change a.iso.hom = eqToHom (show X.p.obj a.left = X.p.obj a.left from rfl) ≫
    𝟙 (X.p.obj a.left) ≫ eqToHom h at he
  simpa only [eqToHom_refl, Category.id_comp] using he

/-- The product used in the diagonal is canonically isomorphic to the
strict product over the base category. -/
theorem product_comparison_strict :
    let F := toBase X
    strictToIso F F ⋙ isoToStrict F F (productStrict X) =
        BasedFunctor.id (strictBased F F) ∧
      isoToStrict F F (productStrict X) ⋙ strictToIso F F = BasedFunctor.id (product X) :=
  strictComparison_isomorphism _ _ (productStrict X)

/-- The diagonal into the product over the base. -/
def diagonal : X ⥤ᵇ product X :=
  lift (toBase X) (toBase X) (BasedFunctor.id X) (BasedFunctor.id X) (Iso.refl _)

theorem diagonal_preserves : PreservesCartesian (diagonal X) :=
  preserves_lift (toBase_preserves X) _ _ _ (fun _ _ h => h) (fun _ _ h => h)

abbrev diagonalPullback := VerticalIsoComma.based (diagonal X) (diagonal X)

theorem diagonalPullback_fibered [X.p.IsFibered] : (diagonalPullback X).p.IsFibered :=
  VerticalIsoComma.isFibered (diagonal_preserves X) (diagonal_preserves X)

section
variable {D' : Type u} [SmallCategory D'] (Y : BasedCategory.{v,w} D')

/-- Inertia objects are objects equipped with a vertical automorphism. -/
structure Obj where
  point : Y.obj
  loop : point ≅ point
  vertical : Y.p.IsHomLift (𝟙 (Y.p.obj point)) loop.hom

variable {Y}

@[ext]
structure Arrow (a b : Obj Y) where
  hom : a.point ⟶ b.point
  square : hom ≫ b.loop.hom = a.loop.hom ≫ hom

instance : Category.{v} (Obj Y) where
  Hom := Arrow
  id a := ⟨𝟙 a.point, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.square, ← Category.assoc, f.square, Category.assoc]⟩
  id_comp f := Arrow.ext (Category.id_comp _)
  comp_id f := Arrow.ext (Category.comp_id _)
  assoc f g h := Arrow.ext (Category.assoc _ _ _)

variable (Y)

/-- Projection from inertia to the original category. -/
def forget : Obj Y ⥤ Y.obj where
  obj a := a.point
  map f := f.hom

abbrev based : BasedCategory.{v,max v w} D' := BasedCategory.ofFunctor (forget Y ⋙ Y.p)



/-- The projection from inertia as a functor over the original base. -/
def forgetBased : based Y ⥤ᵇ Y where
  toFunctor := forget Y
  w := rfl

end

private abbrev PullbackObj := VerticalIsoComma.Obj (diagonal X) (diagonal X)

private def first (a : PullbackObj X) : a.left ≅ a.right :=
  (fst (toBase X) (toBase X)).toFunctor.mapIso a.iso

private def second (a : PullbackObj X) : a.left ≅ a.right :=
  (snd (toBase X) (toBase X)).toFunctor.mapIso a.iso

private theorem first_vertical (a : PullbackObj X) :
    X.p.IsHomLift (𝟙 (X.p.obj a.left)) (first X a).hom :=
  (fst (toBase X) (toBase X)).preserves_isHomLift _ _

private theorem second_vertical (a : PullbackObj X) :
    X.p.IsHomLift (𝟙 (X.p.obj a.left)) (second X a).hom :=
  (snd (toBase X) (toBase X)).preserves_isHomLift _ _

set_option backward.isDefEq.respectTransparency false in
private def comparisonObj (a : Obj X) : PullbackObj X where
  left := a.point
  right := a.point
  iso := objectIso (Iso.refl a.point) a.loop
    (IsHomLift.id rfl) a.vertical (by
      change (toBase X).map (𝟙 a.point) ≫ 𝟙 _ = 𝟙 _ ≫ (toBase X).map a.loop.hom
      haveI := a.vertical
      change X.p.map (𝟙 a.point) ≫ 𝟙 _ = 𝟙 _ ≫ X.p.map a.loop.hom
      have hh := eq_of_isHomLift X.p (𝟙 (X.p.obj a.point)) a.loop.hom
      have hi := X.p.map_id a.point
      exact congrArg (· ≫ 𝟙 (X.p.obj a.point)) hi |>.trans
        (congrArg (𝟙 (X.p.obj a.point) ≫ ·) hh))
  vertical := by
    apply IsHomLift.of_fac' _ _ _ rfl rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact X.p.map_id a.point

set_option backward.isDefEq.respectTransparency false in
/-- The inertia loop supplies the second component of the comparison
isomorphism between the two diagonals. -/
def comparison : based X ⥤ᵇ diagonalPullback X where
  toFunctor := {
    obj := comparisonObj X
    map := fun m => {
      left := m.hom
      right := m.hom
      over := by
        apply IsHomLift.of_fac' _ _ _ rfl rfl
        simp
      square := by
        apply VerticalIsoComma.Arrow.ext
        · exact (Category.comp_id _).trans (Category.id_comp _).symm
        · exact m.square }
    map_id a := VerticalIsoComma.Arrow.ext rfl rfl
    map_comp f g := VerticalIsoComma.Arrow.ext rfl rfl }
  w := rfl

set_option backward.isDefEq.respectTransparency false in
private def inverseObj (a : PullbackObj X) : Obj X where
  point := a.left
  loop := second X a ≪≫ (first X a).symm
  vertical := by
    haveI := first_vertical X a
    haveI := second_vertical X a
    haveI := lift_id_inv X.p (X.p.obj a.left) (first X a)
    change X.p.IsHomLift (𝟙 (X.p.obj a.left)) ((second X a).hom ≫ (first X a).inv)
    exact comp_lift_id_right' X.p (𝟙 (X.p.obj a.left)) (second X a).hom
      (X.p.obj a.left) (first X a).inv

set_option backward.isDefEq.respectTransparency false in
/-- The inverse sends a pair of vertical isomorphisms to their ratio
at the first object. -/
def inverseComparison : diagonalPullback X ⥤ᵇ based X where
  toFunctor := {
    obj := inverseObj X
    map {a b} f := ⟨f.left, by
      have h₁ : f.left ≫ (first X b).hom = (first X a).hom ≫ f.right :=
        congrArg (fun m => m.left) f.square
      have h₂ : f.left ≫ (second X b).hom = (second X a).hom ≫ f.right :=
        congrArg (fun m => m.right) f.square
      change f.left ≫ (second X b).hom ≫ (first X b).inv =
        ((second X a).hom ≫ (first X a).inv) ≫ f.left
      apply (cancel_mono (first X b).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h₁, Iso.inv_hom_id_assoc, h₂]⟩
    map_id a := Arrow.ext rfl
    map_comp f g := Arrow.ext rfl }
  w := rfl


set_option backward.isDefEq.respectTransparency false in
private def unitComponent (a : Obj X) : a ≅ inverseObj X (comparisonObj X a) where
  hom := ⟨𝟙 a.point, by
    change 𝟙 a.point ≫ (a.loop.hom ≫ 𝟙 a.point) = a.loop.hom ≫ 𝟙 a.point
    exact Category.id_comp _⟩
  inv := ⟨𝟙 a.point, by
    change 𝟙 a.point ≫ a.loop.hom = (a.loop.hom ≫ 𝟙 a.point) ≫ 𝟙 a.point
    simp⟩
  hom_inv_id := Arrow.ext (Category.id_comp _)
  inv_hom_id := Arrow.ext (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison has a left inverse over the base. -/
def unitIso : BasedFunctor.id (based X) ≅ comparison X ⋙ inverseComparison X :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (unitComponent X) (fun m => by
      apply Arrow.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (fun a => by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact X.p.map_id a.point)

set_option backward.isDefEq.respectTransparency false in
private def counitComponent (a : PullbackObj X) :
    comparisonObj X (inverseObj X a) ≅ a :=
  objectIso (Iso.refl a.left) (first X a) (IsHomLift.id rfl) (first_vertical X a) (by
    apply VerticalIsoComma.Arrow.ext
    · change 𝟙 a.left ≫ (first X a).hom = 𝟙 a.left ≫ (first X a).hom
      rfl
    · change 𝟙 a.left ≫ (second X a).hom =
        ((second X a).hom ≫ (first X a).inv) ≫ (first X a).hom
      simp [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison with the double diagonal pullback is an
equivalence over the base. -/
def counitIso : inverseComparison X ⋙ comparison X ≅ BasedFunctor.id (diagonalPullback X) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (counitComponent X) (fun m => by
      apply VerticalIsoComma.Arrow.ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact congrArg (fun p => p.left) m.square))
    (fun a => by
      apply IsHomLift.of_fac' _ _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact X.p.map_id a.left)


/-- Forgetting the base recovers an ordinary categorical equivalence. -/
def comparisonEquivalence : Obj X ≌ (diagonalPullback X).obj :=
  CategoryTheory.Equivalence.mk (comparison X).toFunctor (inverseComparison X).toFunctor
    ((BasedNatTrans.forgetful (based X) (based X)).mapIso (unitIso X))
    ((BasedNatTrans.forgetful (diagonalPullback X) (diagonalPullback X)).mapIso (counitIso X))

set_option backward.isDefEq.respectTransparency false in
private theorem reflectsCartesian {R Q : D} {a b : Obj X} (f : R ⟶ Q) (m : a ⟶ b)
    (hm : (diagonalPullback X).p.IsStronglyCartesian f ((comparison X).map m)) :
    (based X).p.IsStronglyCartesian f m := by
  let J := comparison X
  let p := (based X).p
  let q := (diagonalPullback X).p
  haveI : J.toFunctor.IsEquivalence := (comparisonEquivalence X).isEquivalence_functor
  letI : q.IsStronglyCartesian f (J.map m) := hm
  refine { toIsHomLift := J.isHomLift_map f m, universal_property' := ?_ }
  intro c g n hn
  letI : p.IsHomLift (g ≫ f) n := hn
  haveI : q.IsHomLift (g ≫ f) (J.map n) := J.preserves_isHomLift _ _
  obtain ⟨k, ⟨hk, hkn⟩, hu⟩ := IsStronglyCartesian.universal_property q f (J.map m)
    (a' := J.obj c) g (g ≫ f) rfl (J.map n)
  obtain ⟨l, rfl⟩ := J.toFunctor.map_surjective k
  letI : q.IsHomLift g (J.map l) := hk
  refine ⟨l, ⟨J.isHomLift_map g l, J.toFunctor.map_injective (by
    change J.toFunctor.map (l ≫ m) = J.toFunctor.map n
    rw [J.toFunctor.map_comp]
    exact hkn)⟩, ?_⟩
  rintro j ⟨hj, hjn⟩
  letI : p.IsHomLift g j := hj
  apply J.toFunctor.map_injective
  refine hu (J.map j) ⟨J.preserves_isHomLift g j, ?_⟩
  exact (J.toFunctor.map_comp j m).symm.trans (congrArg J.toFunctor.map hjn)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_lift [X.p.IsFibered] (a : Obj X) (R : D) (f : R ⟶ X.p.obj a.point) :
    ∃ (b : Obj X) (m : b ⟶ a), (based X).p.IsStronglyCartesian f m ∧
      X.p.IsStronglyCartesian f ((forgetBased X).map m) := by
  let J := comparison X
  let K := inverseComparison X
  let q := (diagonalPullback X).p
  letI : q.IsFibered := diagonalPullback_fibered X
  obtain ⟨b, m, hm⟩ := IsPreFibered.exists_isCartesian q (a := J.obj a) rfl f
  letI := hm
  haveI : q.IsStronglyCartesian f m := inferInstance
  let k := K.map m ≫ (unitIso X).inv.toNatTrans.app a
  have triangle : J.map ((unitIso X).inv.toNatTrans.app a) =
      (counitIso X).hom.toNatTrans.app (J.obj a) := VerticalIsoComma.Arrow.ext rfl rfl
  have hmap : J.map k = (counitIso X).hom.toNatTrans.app b ≫ m := by
    change J.toFunctor.map (K.map m ≫ (unitIso X).inv.toNatTrans.app a) = _
    rw [J.toFunctor.map_comp]
    rw [show J.toFunctor.map ((unitIso X).inv.toNatTrans.app a) =
      (counitIso X).hom.toNatTrans.app (J.obj a) from triangle]
    exact (counitIso X).hom.toNatTrans.naturality m
  have hb : q.obj b = R := domain_eq q f m
  haveI : q.IsHomLift (𝟙 R) ((counitIso X).hom.toNatTrans.app b) :=
    (counitIso X).hom.isHomLift hb
  haveI : IsIso ((counitIso X).hom.toNatTrans.app b) := by
    change IsIso (((BasedNatTrans.forgetful _ _).mapIso (counitIso X)).hom.app b)
    infer_instance
  haveI : q.IsStronglyCartesian (𝟙 R) ((counitIso X).hom.toNatTrans.app b) :=
    IsStronglyCartesian.of_isIso _ _ _
  have h : q.IsStronglyCartesian (𝟙 R ≫ f)
      ((counitIso X).hom.toNatTrans.app b ≫ m) := IsStronglyCartesian.comp q
  rw [Category.id_comp] at h
  have hJ : q.IsStronglyCartesian f (J.map k) := hmap.symm ▸ h
  have hfst : PreservesCartesian (fst (diagonal X) (diagonal X)) := (preserves_projections (diagonal_preserves X) (diagonal_preserves X)).1
  exact ⟨K.obj b, k, reflectsCartesian X f k hJ, hfst f (J.map k) hJ⟩

/-- The inertia category is fibered over the base. -/
theorem isFibered [X.p.IsFibered] : (based X).p.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain ⟨b, m, hm, _⟩ := exists_lift X a R f
  exact ⟨b, m, hm⟩

/-- Forgetting the automorphism preserves Cartesian arrows. -/
theorem forget_preserves [X.p.IsFibered] : PreservesCartesian (forgetBased X) :=
  preserves_of_lifts _ (exists_lift X)


section ChangePresentation

variable {X Y : BasedCategory.{u,u} D} (F : X ⥤ᵇ Y)

set_option backward.isDefEq.respectTransparency false in
/-- A based functor takes a vertical automorphism to a vertical
automorphism of the image object. -/
def map : based X ⥤ᵇ based Y where
  toFunctor := {
    obj a := {
      point := F.obj a.point
      loop := F.toFunctor.mapIso a.loop
      vertical := by
        letI := a.vertical
        have h := F.preserves_isHomLift (𝟙 (X.p.obj a.point)) a.loop.hom
        exact F.w_obj a.point ▸ h }
    map {a b} m := ⟨F.map m.hom, by
      change F.toFunctor.map m.hom ≫ F.toFunctor.map b.loop.hom =
        F.toFunctor.map a.loop.hom ≫ F.toFunctor.map m.hom
      rw [← F.toFunctor.map_comp, ← F.toFunctor.map_comp, m.square]⟩
    map_id a := Arrow.ext (F.map_id a.point)
    map_comp m n := Arrow.ext (F.map_comp m.hom n.hom) }
  w := by
    change forget X ⋙ (F.toFunctor ⋙ Y.p) = forget X ⋙ X.p
    rw [F.w]

set_option backward.isDefEq.respectTransparency false in
/-- Full faithfulness is preserved by inertia. -/
def map_fullyFaithful (hF : F.toFunctor.FullyFaithful) : (map F).toFunctor.FullyFaithful where
  preimage {a b} m := ⟨hF.preimage m.hom, by
    apply hF.map_injective
    simp only [F.toFunctor.map_comp, hF.map_preimage]
    exact m.square⟩
  map_preimage m := Arrow.ext (hF.map_preimage m.hom)
  preimage_map m := Arrow.ext (hF.preimage_map m.hom)

set_option backward.isDefEq.respectTransparency false in
/-- If the image of an object is vertically isomorphic to the point of an
inertia object, full faithfulness lifts the loop along that isomorphism. -/
theorem lift_vertical_object (hF : F.toFunctor.FullyFaithful)
    (a : X.obj) (b : Obj Y) (e : F.obj a ≅ b.point)
    (he : Y.p.IsHomLift (𝟙 (X.p.obj a)) e.hom) :
    ∃ (l : Obj X) (j : (map F).obj l ≅ b),
      l.point = a ∧ (based Y).p.IsHomLift (𝟙 (X.p.obj a)) j.hom := by
  letI := he
  haveI : Y.p.IsHomLift (𝟙 (X.p.obj a)) b.loop.hom :=
    (codomain_eq Y.p (𝟙 (X.p.obj a)) e.hom) ▸ b.vertical
  haveI := lift_id_inv Y.p (X.p.obj a) e
  haveI : Y.p.IsHomLift (𝟙 (X.p.obj a)) (b.loop.hom ≫ e.inv) :=
    comp_lift_id_right' Y.p (𝟙 (X.p.obj a)) b.loop.hom (X.p.obj a) e.inv
  let k := e ≪≫ b.loop ≪≫ e.symm
  haveI : Y.p.IsHomLift (𝟙 (X.p.obj a)) k.hom :=
    comp_lift_id_right' Y.p (𝟙 (X.p.obj a)) e.hom (X.p.obj a) (b.loop.hom ≫ e.inv)
  let v := hF.preimageIso k
  have hv : F.map v.hom = k.hom := hF.map_preimage _
  haveI : Y.p.IsHomLift (𝟙 (X.p.obj a)) (F.map v.hom) := hv.symm ▸ ‹_›
  let l : Obj X := ⟨a, v, F.isHomLift_map _ _⟩
  let j : (map F).obj l ≅ b :=
    { hom := ⟨e.hom, by
        change e.hom ≫ b.loop.hom = F.map v.hom ≫ e.hom
        rw [hv]
        simp [k, Category.assoc]⟩
      inv := ⟨e.inv, by
        change e.inv ≫ F.map v.hom = b.loop.hom ≫ e.inv
        rw [hv]
        simp [k]⟩
      hom_inv_id := Arrow.ext e.hom_inv_id
      inv_hom_id := Arrow.ext e.inv_hom_id }
  haveI : Y.p.IsHomLift (𝟙 (X.p.obj a)) ((forgetBased Y).map j.hom) := he
  exact ⟨l, j, rfl, (forgetBased Y).isHomLift_map _ _⟩

end ChangePresentation

end Masullo.BasedInertia
