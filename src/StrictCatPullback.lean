import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.CodiscreteCategory

open CategoryTheory

namespace Masullo.StrictCatPullback

universe u
variable {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
variable (F : A ⥤ C) (G : B ⥤ C)

/-- The ordinary strict pullback of two small categories. -/
@[ext]
structure Obj where
  left : A
  right : B
  matchObj : F.obj left = G.obj right

variable {F G}

@[ext]
structure Hom (a b : Obj F G) where
  left : a.left ⟶ b.left
  right : a.right ⟶ b.right
  matchHom : F.map left ≫ eqToHom b.matchObj = eqToHom a.matchObj ≫ G.map right

instance : SmallCategory (Obj F G) where
  Hom := Hom
  id _ := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp f g := ⟨f.left ≫ g.left, f.right ≫ g.right, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.matchHom, ← Category.assoc, f.matchHom, Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

variable (F G)

def fst : Obj F G ⥤ A where
  obj a := a.left
  map f := f.left

def snd : Obj F G ⥤ B where
  obj a := a.right
  map f := f.right

theorem condition : fst F G ⋙ F = snd F G ⋙ G := by
  refine Functor.ext (fun a => a.matchObj) ?_
  intro a b f
  change F.map f.left = eqToHom a.matchObj ≫ G.map f.right ≫ eqToHom b.matchObj.symm
  calc
    _ = (F.map f.left ≫ eqToHom b.matchObj) ≫ eqToHom b.matchObj.symm := by simp
    _ = _ := by rw [f.matchHom, Category.assoc]

variable {F G} {X : Type u} [SmallCategory X]

def lift (L : X ⥤ A) (R : X ⥤ B) (h : L ⋙ F = R ⋙ G) : X ⥤ Obj F G where
  obj x := ⟨L.obj x, R.obj x, Functor.congr_obj h x⟩
  map {x y} m := ⟨L.map m, R.map m, by
    have hm := Functor.congr_hom h m
    change F.map (L.map m) =
      eqToHom (Functor.congr_obj h x) ≫ G.map (R.map m) ≫
        eqToHom (Functor.congr_obj h y).symm at hm
    simp [hm, Category.assoc]⟩
  map_id x := Hom.ext (L.map_id x) (R.map_id x)
  map_comp f g := Hom.ext (L.map_comp f g) (R.map_comp f g)

@[simp] theorem lift_fst (L : X ⥤ A) (R : X ⥤ B) (h : L ⋙ F = R ⋙ G) :
    lift L R h ⋙ fst F G = L := rfl

@[simp] theorem lift_snd (L : X ⥤ A) (R : X ⥤ B) (h : L ⋙ F = R ⋙ G) :
    lift L R h ⋙ snd F G = R := rfl

theorem functor_ext {L R : X ⥤ Obj F G}
    (hL : L ⋙ fst F G = R ⋙ fst F G) (hR : L ⋙ snd F G = R ⋙ snd F G) : L = R := by
  have ho (x : X) : L.obj x = R.obj x :=
    Obj.ext (Functor.congr_obj hL x) (Functor.congr_obj hR x)
  refine Functor.ext ho ?_
  intro x y m
  apply Hom.ext
  · change (L ⋙ fst F G).map m =
      (fst F G).map (eqToHom (ho x) ≫ R.map m ≫ eqToHom (ho y).symm)
    simp only [Functor.map_comp, eqToHom_map]
    exact Functor.congr_hom hL m
  · change (L ⋙ snd F G).map m =
      (snd F G).map (eqToHom (ho x) ≫ R.map m ≫ eqToHom (ho y).symm)
    simp only [Functor.map_comp, eqToHom_map]
    exact Functor.congr_hom hR m



/-- The two projections determine the unique lift of any strictly
commuting pair of functors. -/
theorem existsUnique_lift (L : X ⥤ A) (R : X ⥤ B) (h : L ⋙ F = R ⋙ G) :
    ∃! J : X ⥤ Obj F G, J ⋙ fst F G = L ∧ J ⋙ snd F G = R := by
  refine ⟨lift L R h, ⟨lift_fst L R h, lift_snd L R h⟩, ?_⟩
  rintro J ⟨hL, hR⟩
  exact functor_ext (hL.trans (lift_fst L R h).symm) (hR.trans (lift_snd L R h).symm)

section Isomorphism

variable {K L : Cat.{u, u}} (J : K ⟶ L)
  (hJ : J.toFunctor.FullyFaithful) (ho : Function.Bijective J.toFunctor.obj)

private noncomputable def invObj (y : L) : K := (Equiv.ofBijective J.toFunctor.obj ho).symm y

private theorem invObj_right (y : L) : J.toFunctor.obj (invObj J ho y) = y :=
  (Equiv.ofBijective J.toFunctor.obj ho).apply_symm_apply y

set_option backward.isDefEq.respectTransparency false in
private noncomputable def strictInverse : L ⥤ K where
  obj := invObj J ho
  map {a b} f := hJ.preimage
    (eqToHom (invObj_right J ho a) ≫ f ≫ eqToHom (invObj_right J ho b).symm)
  map_id a := hJ.map_injective (by simp)
  map_comp f g := hJ.map_injective (by simp [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/-- Full faithfulness and a bijection of objects give a strict isomorphism
of small categories. -/
noncomputable def isoOfFullyFaithfulBijective : K ≅ L where
  hom := J
  inv := (strictInverse J hJ ho).toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    let e := Equiv.ofBijective J.toFunctor.obj ho
    have h (x : K) : (strictInverse J hJ ho).obj (J.toFunctor.obj x) = x := e.symm_apply_apply x
    refine Functor.ext h ?_
    intro a b f
    apply hJ.map_injective
    change J.toFunctor.map (hJ.preimage
      (eqToHom (invObj_right J ho (J.toFunctor.obj a)) ≫ J.toFunctor.map f ≫
        eqToHom (invObj_right J ho (J.toFunctor.obj b)).symm)) =
      J.toFunctor.map (eqToHom (h a) ≫ f ≫ eqToHom (h b).symm)
    simp only [hJ.map_preimage, Functor.map_comp, eqToHom_map]
  inv_hom_id := by
    apply Cat.Hom.ext
    refine Functor.ext (invObj_right J ho) ?_
    intro a b f
    exact hJ.map_preimage _

end Isomorphism


/-- Strict pullbacks can change under an equivalence of the middle groupoid.
The two maps initially select different isomorphic objects. -/
theorem strictPullback_middle_equivalence_obstruction :
    let L : Codiscrete Unit ⥤ Codiscrete Bool := Codiscrete.functorOfFun (fun _ => false)
    let R : Codiscrete Unit ⥤ Codiscrete Bool := Codiscrete.functorOfFun (fun _ => true)
    ∃ e : Codiscrete Bool ≌ Codiscrete Unit,
      IsEmpty (Obj L R) ∧ Nonempty (Obj (L ⋙ e.functor) (R ⋙ e.functor)) := by
  intro L R
  let e : Codiscrete Bool ≌ Codiscrete Unit :=
    { functor := Codiscrete.functorOfFun (fun _ => ())
      inverse := Codiscrete.functorOfFun (fun _ => false)
      unitIso := Codiscrete.natIso
      counitIso := Codiscrete.natIso }
  refine ⟨e, ⟨fun a => ?_⟩, ⟨⟨⟨()⟩, ⟨()⟩, rfl⟩⟩⟩
  exact Bool.false_ne_true (congrArg Codiscrete.as a.matchObj)

end Masullo.StrictCatPullback
