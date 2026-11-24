import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

open CategoryTheory CategoryTheory.Functor Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

namespace Masullo

universe u v w

namespace FiberedGrothendieck

open CategoryTheory.Pseudofunctor.CoGrothendieck

variable {D : Type u} [SmallCategory D]
variable (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v, w})

/-- The composition in (E.6.1.3) uses the pullback functor on the second
fiber arrow, indexed by the first base arrow. The Grothendieck construction
makes the more general pseudofunctor version with its coherence explicit. -/
theorem fibered : IsFibered (forget F) := inferInstance

abbrev fiberInclusionModel (U : D) : F.obj ⟨op U⟩ ⥤ Fiber (forget F) U :=
  Fiber.inducedFunctor (comp_const F U)

theorem fiberInclusionModel_bijective (U : D) :
    Function.Bijective (fiberInclusionModel F U).obj := by
  constructor
  · intro a b hab
    let component (x : Fiber (forget F) U) : F.obj ⟨op U⟩ :=
      cast (congrArg (fun V : D => ↥(F.obj ⟨op V⟩)) x.2) x.1.fiber
    exact congrArg component hab
  · intro Y
    have hYS : (Fiber.fiberInclusion.obj Y).base = U := by simpa using! Y.2
    refine ⟨hYS ▸ (Fiber.fiberInclusion.obj Y).fiber, ?_⟩
    apply Fiber.fiberInclusion_obj_inj
    ext
    · exact hYS.symm
    · change HEq (hYS ▸ (Fiber.fiberInclusion.obj Y).fiber) (Fiber.fiberInclusion.obj Y).fiber
      exact rec_heq_of_heq (C := fun V : D => ↥(F.obj ⟨op V⟩)) hYS HEq.rfl

noncomputable def fiberModelEquivalence (U : D) : (F.obj ⟨op U⟩) ≌ Fiber (forget F) U :=
  (fiberInclusionModel F U).asEquivalence

/-- The groupoid clause of E.6.1.2, expressed as invertibility of every
arrow in each actual fiber. -/
theorem fiber_all_isIso_of_groupoid
    (hF : ∀ (U : D) (a b : F.obj ⟨op U⟩) (t : a ⟶ b), IsIso t)
    (U : D) {x y : Fiber (forget F) U} (f : x ⟶ y) : IsIso f := by
  obtain ⟨a, rfl⟩ := (fiberInclusionModel_bijective F U).2 x
  obtain ⟨b, rfl⟩ := (fiberInclusionModel_bijective F U).2 y
  let I := fiberInclusionModel F U
  obtain ⟨t, rfl⟩ := I.map_surjective f
  letI := hF U a b t
  infer_instance

/-- The set-valued clause of E.6.1.2. Each fiber is discrete when the
diagram has discrete categories as its values. -/
theorem fiber_discrete_of_discrete
    (hF : ∀ (U : D) (a b : F.obj ⟨op U⟩), Subsingleton (a ⟶ b) ∧ (Nonempty (a ⟶ b) → a = b))
    (U : D) (x y : Fiber (forget F) U) :
    Subsingleton (x ⟶ y) ∧ (Nonempty (x ⟶ y) → x = y) := by
  obtain ⟨a, rfl⟩ := (fiberInclusionModel_bijective F U).2 x
  obtain ⟨b, rfl⟩ := (fiberInclusionModel_bijective F U).2 y
  let I := fiberInclusionModel F U
  have h := hF U a b
  constructor
  · constructor
    intro f g
    obtain ⟨s, rfl⟩ := I.map_surjective f
    obtain ⟨t, rfl⟩ := I.map_surjective g
    exact congrArg I.map (@Subsingleton.elim _ h.1 s t)
  · rintro ⟨f⟩
    obtain ⟨t, -⟩ := I.map_surjective f
    exact congrArg I.obj (h.2 ⟨t⟩)

section StrongComparison

variable {F K : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v,w}} (τ : F ⟶ K)

private abbrev appAt (X : D) := (τ.app ⟨op X⟩).toFunctor

private abbrev naturalityAt {X Y : D} (f : X ⟶ Y) (b : F.obj ⟨op Y⟩) :=
  (Cat.Hom.toNatIso (τ.naturality f.op.toLoc)).app b

set_option backward.isDefEq.respectTransparency false in
/-- The total functor is fully faithful if all its components are fully faithful. -/
noncomputable def mapFullyFaithful (h : ∀ X : D, (appAt τ X).FullyFaithful) :
    (Pseudofunctor.CoGrothendieck.map τ).FullyFaithful where
  preimage {a b} r :=
    ⟨r.base,(h a.base).preimage (r.fiber ≫ (naturalityAt τ r.base b.fiber).inv)⟩
  map_preimage {a b} r := by
    apply Hom.ext <;> try rfl
    let e := naturalityAt τ r.base b.fiber
    change (appAt τ a.base).map ((h a.base).preimage (r.fiber ≫ e.inv)) ≫ e.hom = r.fiber ≫ eqToHom rfl
    rw [(h a.base).map_preimage]
    simp [Category.assoc]
  preimage_map {a b} r := by
    apply Hom.ext <;> try rfl
    let e := naturalityAt τ r.base b.fiber
    change (h a.base).preimage (((appAt τ a.base).map r.fiber ≫ e.hom) ≫ e.inv) = r.fiber ≫ eqToHom rfl
    simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem mapAtLift_bijective (h : (Pseudofunctor.CoGrothendieck.map τ).FullyFaithful)
    (a b : F.CoGrothendieck) (q : a.base ⟶ b.base) :
    Function.Bijective ((appAt τ a.base).map :
      (a.fiber ⟶ (F.map q.op.toLoc).toFunctor.obj b.fiber) → _) := by
  constructor
  · intro r s hr
    let r' : a ⟶ b := ⟨q,r⟩
    let s' : a ⟶ b := ⟨q,s⟩
    have he : (Pseudofunctor.CoGrothendieck.map τ).map r' =
        (Pseudofunctor.CoGrothendieck.map τ).map s' := by
      apply Hom.ext <;> try rfl
      let e := naturalityAt τ q b.fiber
      change (appAt τ a.base).map r ≫ e.hom = ((appAt τ a.base).map s ≫ e.hom) ≫ eqToHom rfl
      exact (congrArg (fun v ↦ v ≫ e.hom) hr).trans (Category.comp_id _).symm
    exact (Hom.congr (h.map_injective he)).trans (Category.comp_id _)
  · intro r
    let t : (Pseudofunctor.CoGrothendieck.map τ).obj a ⟶
        (Pseudofunctor.CoGrothendieck.map τ).obj b := ⟨q,r ≫ (naturalityAt τ q b.fiber).hom⟩
    obtain ⟨⟨q',s⟩,hs⟩ := h.map_surjective t
    have hq : q' = q := congrArg Hom.base hs
    subst q'
    refine ⟨s,?_⟩
    have he := (Hom.congr hs).trans (Category.comp_id _)
    apply (cancel_mono (naturalityAt τ q b.fiber).hom).mp
    exact he

/-- Full faithfulness of the total functor is detected on its components. -/
theorem map_fullyFaithful_iff :
    Nonempty (Pseudofunctor.CoGrothendieck.map τ).FullyFaithful ↔
      ∀ X : D, Nonempty (appAt τ X).FullyFaithful := by
  refine ⟨?_,fun h ↦ ⟨mapFullyFaithful τ fun X ↦ (h X).some⟩⟩
  rintro ⟨h⟩ X
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro a b
  let L := appAt τ X
  let b' := (F.map (𝟙 X).op.toLoc).toFunctor.obj b
  let e : b' ≅ b := (Cat.Hom.toNatIso (F.mapId ⟨op X⟩)).app b
  have hl := mapAtLift_bijective τ h ⟨X,a⟩ ⟨X,b⟩ (𝟙 X)
  change Function.Bijective (L.map : (a ⟶ b') → _) at hl
  constructor
  · intro r s hrs
    change L.map r = L.map s at hrs
    have he : r ≫ e.inv = s ≫ e.inv := hl.1 (by simp only [Functor.map_comp, hrs])
    exact (cancel_mono e.inv).mp he
  · intro r
    obtain ⟨t,ht⟩ := hl.2 (r ≫ L.map e.inv)
    refine ⟨t ≫ e.hom,?_⟩
    change L.map (t ≫ e.hom) = r
    rw [Functor.map_comp, ht, Category.assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id, Category.comp_id]

/-- Essential surjectivity on every component gives essential surjectivity
over the same base object in the total category. -/
theorem map_essSurj_of_components (h : ∀ X : D, (appAt τ X).EssSurj) :
    (Pseudofunctor.CoGrothendieck.map τ).EssSurj where
  mem_essImage b := by
    obtain ⟨a,⟨e⟩⟩ := (h b.base).mem_essImage b.fiber
    exact ⟨⟨b.base,a⟩,⟨(ι K b.base).mapIso e⟩⟩

/-- If the target fibres are groupoids, essential surjectivity of the total
functor gives essential surjectivity on every component by base change. -/
theorem component_essSurj_of_map (h : (Pseudofunctor.CoGrothendieck.map τ).EssSurj)
    (hK : ∀ X : D, ∀ a b : K.obj ⟨op X⟩, ∀ r : a ⟶ b, IsIso r)
    (X : D) : (appAt τ X).EssSurj where
  mem_essImage b := by
    obtain ⟨a,⟨e⟩⟩ := h.mem_essImage (⟨X,b⟩ : K.CoGrothendieck)
    let q := e.inv.base
    let e' := naturalityAt τ q a.fiber
    letI := hK X _ _ e.inv.fiber
    exact ⟨(F.map q.op.toLoc).toFunctor.obj a.fiber,⟨e' ≪≫ (asIso e.inv.fiber).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Component equivalences yield an equivalence of total categories with
inverse over the same base and vertical unit and counit. -/
theorem equivalence_over_of_components (hff : ∀ X : D, (appAt τ X).FullyFaithful)
    (he : ∀ X : D, (appAt τ X).EssSurj) :
    ∃ e : F.CoGrothendieck ≌ K.CoGrothendieck,
      e.functor = Pseudofunctor.CoGrothendieck.map τ ∧
      e.inverse ⋙ forget F = forget K ∧
      (∀ a, (forget F).IsHomLift (𝟙 a.base) (e.unitIso.hom.app a)) ∧
      ∀ b, (forget K).IsHomLift (𝟙 b.base) (e.counitIso.hom.app b) := by
  let L := Pseudofunctor.CoGrothendieck.map τ
  let ff := mapFullyFaithful τ hff
  let pick (b : K.CoGrothendieck) := (he b.base).mem_essImage b.fiber
  let obj (b : K.CoGrothendieck) : F.CoGrothendieck := ⟨b.base,(pick b).choose⟩
  let v (b : K.CoGrothendieck) : L.obj (obj b) ≅ b := (ι K b.base).mapIso (pick b).choose_spec.some
  let I : K.CoGrothendieck ⥤ F.CoGrothendieck := {
    obj := obj
    map {a b} r := ff.preimage ((v a).hom ≫ r ≫ (v b).inv)
    map_id a := ff.map_injective (by simp)
    map_comp r s := ff.map_injective (by simp [ff.map_preimage,Category.assoc]) }
  have hpre {a b : F.CoGrothendieck} (r : L.obj a ⟶ L.obj b) : L.map (ff.preimage r) = r :=
    ff.map_preimage r
  have hmap {a b} (r : a ⟶ b) : L.map (I.map r) = (v a).hom ≫ r ≫ (v b).inv := ff.map_preimage _
  let η : 𝟭 F.CoGrothendieck ≅ L ⋙ I := NatIso.ofComponents
    (fun a ↦ (ff.preimageIso (v (L.obj a))).symm) (fun r ↦ ff.map_injective (by
      change L.map (r ≫ ff.preimage (v (L.obj _)).inv) = L.map (ff.preimage (v (L.obj _)).inv ≫ I.map (L.map r))
      rw [L.map_comp,L.map_comp,hpre,hpre,hmap]
      simp))
  let ε : I ⋙ L ≅ 𝟭 K.CoGrothendieck := NatIso.ofComponents v (by
    intro a b r
    change L.map (I.map r) ≫ (v b).hom = (v a).hom ≫ r
    rw [hmap]
    simp [Category.assoc])
  let e : F.CoGrothendieck ≌ K.CoGrothendieck := {
    functor := L
    inverse := I
    unitIso := η
    counitIso := ε
    functor_unitIso_comp a := by
      change L.map (ff.preimage (v (L.obj a)).inv) ≫ (v (L.obj a)).hom = 𝟙 _
      rw [ff.map_preimage, Iso.inv_hom_id] }
  refine ⟨e,rfl,?_,?_,?_⟩
  · refine Functor.ext (fun _ ↦ rfl) ?_
    intro a b r
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    change (I.map r).base = r.base
    exact (congrArg Hom.base (hmap r)).trans (by
      change 𝟙 a.base ≫ r.base ≫ 𝟙 b.base = r.base
      simp)
  · intro a
    apply IsHomLift.of_fac' (forget F) (𝟙 a.base) (e.unitIso.hom.app a) rfl rfl
    change (ff.preimage (v (L.obj a)).inv).base = _
    refine (congrArg Hom.base (hpre (v (L.obj a)).inv)).trans ?_
    simp only [eqToHom_refl,Category.comp_id]
    rfl
  · intro b
    exact IsHomLift.map (forget K) (e.counitIso.hom.app b)

end StrongComparison

section VerticalArrows

variable {F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v,w}}

set_option backward.isDefEq.respectTransparency false in
/-- A vertical endomorphism is the inclusion of a fibre endomorphism. -/
theorem exists_verticalHom {a : F.CoGrothendieck} (r : a ⟶ a)
    (hr : (forget F).IsHomLift (𝟙 a.base) r) :
    ∃ t : a.fiber ⟶ a.fiber, (ι F a.base).map t = r := by
  have hb : r.base = 𝟙 a.base := by
    letI := hr
    simpa using (IsHomLift.fac (forget F) (𝟙 a.base) r).symm
  obtain ⟨d,s⟩ := r
  change d = 𝟙 a.base at hb
  subst d
  let e := (Cat.Hom.toNatIso (F.mapId ⟨op a.base⟩)).app a.fiber
  refine ⟨s ≫ e.hom,?_⟩
  apply Hom.ext <;> try rfl
  change (s ≫ e.hom) ≫ e.inv = s ≫ eqToHom rfl
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Composition with a vertical arrow on the left keeps the base arrow
and composes the original fibre arrow on the left. -/
theorem vertical_comp_between {a b : F.CoGrothendieck}
    {c : F.obj ⟨op a.base⟩} (r : a ⟶ b) (s : c ⟶ a.fiber) :
    (ι F a.base).map s ≫ r = (⟨r.base,s ≫ r.fiber⟩ : ⟨a.base, c⟩ ⟶ b) := by
  refine Hom.ext _ _ (Category.id_comp r.base) ?_
  let X := LocallyDiscrete.mk (op a.base)
  let q := r.base.op.toLoc
  let z := (F.map q).toFunctor.obj b.fiber
  let e := (F.mapId X).inv.toNatTrans
  change (s ≫ e.app a.fiber) ≫ (F.map (𝟙 X)).toFunctor.map r.fiber ≫
    (F.mapComp q (𝟙 X)).inv.toNatTrans.app b.fiber = _
  rw [Category.assoc, ← e.naturality_assoc, F.mapComp_id_right_inv_app q b.fiber]
  change s ≫ r.fiber ≫ ((F.mapId X).inv.toNatTrans.app z ≫
    (F.mapId X).hom.toNatTrans.app z ≫ (F.map₂ (ρ_ q).inv).toNatTrans.app b.fiber) = _
  have hz : (F.mapId X).inv.toNatTrans.app z ≫ (F.mapId X).hom.toNatTrans.app z = 𝟙 z :=
    ((Cat.Hom.toNatIso (F.mapId X)).app z).inv_hom_id
  rw [← Category.assoc ((F.mapId X).inv.toNatTrans.app z), hz]
  simp [X,q,Bicategory.Strict.rightUnitor_eqToIso,PrelaxFunctor.map₂_eqToHom]

set_option backward.isDefEq.respectTransparency false in
/-- Composition with a vertical arrow on the right keeps the base arrow
and composes by the pullback of the fibre arrow on the right. -/
theorem comp_vertical_between {a b : F.CoGrothendieck}
    {c : F.obj ⟨op b.base⟩} (r : a ⟶ b) (s : b.fiber ⟶ c) :
    r ≫ (ι F b.base).map s =
      (⟨r.base,r.fiber ≫ (F.map r.base.op.toLoc).toFunctor.map s⟩ : a ⟶ ⟨b.base,c⟩) := by
  refine Hom.ext _ _ (Category.comp_id r.base) ?_
  let q := r.base.op.toLoc
  let X := LocallyDiscrete.mk (op b.base)
  change r.fiber ≫ (F.map q).toFunctor.map (s ≫ (F.mapId X).inv.toNatTrans.app c) ≫
    (F.mapComp (𝟙 X) q).inv.toNatTrans.app c = _
  rw [Functor.map_comp, F.whiskerRight_mapId_inv_app q c]
  simp [X,Bicategory.Strict.leftUnitor_eqToIso,PrelaxFunctor.map₂_eqToHom,Category.assoc,
    ← Cat.Hom₂.comp_app]
  rfl

theorem vertical_comp {a b : F.CoGrothendieck} (r : a ⟶ b) (s : a.fiber ⟶ a.fiber) :
    (ι F a.base).map s ≫ r = (⟨r.base,s ≫ r.fiber⟩ : a ⟶ b) :=
  vertical_comp_between r s

theorem comp_vertical {a b : F.CoGrothendieck} (r : a ⟶ b) (s : b.fiber ⟶ b.fiber) :
    r ≫ (ι F b.base).map s =
      (⟨r.base,r.fiber ≫ (F.map r.base.op.toLoc).toFunctor.map s⟩ : a ⟶ b) :=
  comp_vertical_between r s

/-- A square with vertical arrows commutes exactly when the corresponding
square with the pulled-back fibre arrow commutes. -/
theorem verticalSquare_iff {a b : F.CoGrothendieck} (r : a ⟶ b)
    (s : a.fiber ⟶ a.fiber) (t : b.fiber ⟶ b.fiber) :
    r ≫ (ι F b.base).map t = (ι F a.base).map s ≫ r ↔
      r.fiber ≫ (F.map r.base.op.toLoc).toFunctor.map t = s ≫ r.fiber := by
  rw [comp_vertical,vertical_comp]
  refine ⟨fun h ↦ (Hom.congr h).trans (Category.comp_id _),?_⟩
  exact congrArg (fun q ↦ (⟨r.base,q⟩ : a ⟶ b))

end VerticalArrows

set_option backward.isDefEq.respectTransparency false in
/-- A morphism in a total category with invertible fibre component is
strongly Cartesian over its base arrow. -/
theorem isStronglyCartesian_of_fiber_isIso {F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v,w}}
    {a b : F.CoGrothendieck} (r : a ⟶ b) [IsIso r.fiber] :
    (forget F).IsStronglyCartesian r.base r := by
  let t := (ι F a.base).map r.fiber
  let L := cartesianLift b.fiber r.base
  have hl : t ≫ L = r := by
    refine Hom.ext (t ≫ L) r (Category.id_comp r.base) ?_
    let X := LocallyDiscrete.mk (op a.base)
    let q := r.base.op.toLoc
    let z := (F.map q).toFunctor.obj b.fiber
    change (r.fiber ≫ (F.mapId X).inv.toNatTrans.app z) ≫
      (F.map (𝟙 X)).toFunctor.map (𝟙 z) ≫ (F.mapComp q (𝟙 X)).inv.toNatTrans.app b.fiber = _
    rw [Functor.map_id, Category.id_comp, F.mapComp_id_right_inv_app q b.fiber]
    simp [X,z,Bicategory.Strict.rightUnitor_eqToIso,PrelaxFunctor.map₂_eqToHom,
      ← Cat.Hom₂.comp_app]
  letI : (forget F).IsHomLift (𝟙 a.base) t := IsHomLift.map _ t
  letI : (forget F).IsStronglyCartesian (𝟙 a.base) t := IsStronglyCartesian.of_isIso _ _ _
  letI : (forget F).IsStronglyCartesian r.base L := isStronglyCartesian_homCartesianLift _ _
  have hp : (forget F).IsStronglyCartesian (𝟙 a.base ≫ r.base) (t ≫ L) :=
    IsStronglyCartesian.comp (forget F)
  simpa only [Category.id_comp,hl] using hp

end FiberedGrothendieck

end Masullo
