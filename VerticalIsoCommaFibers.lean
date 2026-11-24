import VerticalIsoComma
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.VerticalIsoComma

universe u

variable {D : Type u} [SmallCategory D]
  {X Y S : BasedCategory.{u, u} D} (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

/-- Restriction of a based functor to one fiber. -/
def restrictFiber {X S : BasedCategory.{u, u} D} (F : X ⥤ᵇ S) (U : D) :
    Fiber X.p U ⥤ Fiber S.p U where
  obj a := ⟨F.obj a.val, (F.w_obj a.val).trans a.property⟩
  map m := ⟨F.map (Fiber.fiberInclusion.map m),
    F.preserves_isHomLift (𝟙 U) (Fiber.fiberInclusion.map m)⟩
  map_id a := Fiber.hom_ext (F.map_id a.val)
  map_comp m n := Fiber.hom_ext (F.map_comp (Fiber.fiberInclusion.map m) (Fiber.fiberInclusion.map n))

/-- The ordinary iso-comma category of the restrictions to a fiber. -/
abbrev IsoCommaInFiber (U : D) :=
  (show ObjectProperty (Comma (restrictFiber F U) (restrictFiber G U)) from
    fun a => IsIso a.hom).FullSubcategory

private theorem verticalAt (q : Obj F G) {U : D} (h : X.p.obj q.left = U) :
    S.p.IsHomLift (𝟙 U) q.iso.hom := by
  rw [← h]
  exact q.vertical

private def comparisonInFiber (U : D) (a : Fiber (based F G).p U) :
    (restrictFiber F U).obj ⟨a.val.left, a.property⟩ ≅
      (restrictFiber G U).obj ⟨a.val.right, (base_eq a.val).trans a.property⟩ where
  hom := ⟨a.val.iso.hom, verticalAt F G a.val a.property⟩
  inv := ⟨a.val.iso.inv, by
    haveI : S.p.IsHomLift (𝟙 U) a.val.iso.hom := verticalAt F G a.val a.property
    exact IsHomLift.lift_id_inv S.p U a.val.iso⟩
  hom_inv_id := Fiber.hom_ext a.val.iso.hom_inv_id
  inv_hom_id := Fiber.hom_ext a.val.iso.inv_hom_id

/-- The canonical functor comparing the fiber of the two-fiber product
with the two-fiber product of the fibers. -/
def fiberComparison (U : D) : Fiber (based F G).p U ⥤ IsoCommaInFiber F G U where
  obj a := ⟨⟨⟨a.val.left, a.property⟩, ⟨a.val.right, (base_eq a.val).trans a.property⟩,
    (comparisonInFiber F G U a).hom⟩, inferInstance⟩
  map m := ⟨⟨
    ⟨m.val.left, (fst F G).preserves_isHomLift (𝟙 U) (Fiber.fiberInclusion.map m)⟩,
    ⟨m.val.right, (snd F G).preserves_isHomLift (𝟙 U) (Fiber.fiberInclusion.map m)⟩,
    Fiber.hom_ext m.val.square⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem fiberComparison_bijective (U : D) : Function.Bijective (fiberComparison F G U).obj := by
  constructor
  · intro a b h
    have ha : a.val.left = b.val.left := congrArg (fun c : IsoCommaInFiber F G U => c.obj.left.val) h
    have hb : a.val.right = b.val.right := congrArg (fun c : IsoCommaInFiber F G U => c.obj.right.val) h
    have hcOfEq {c d : IsoCommaInFiber F G U} (he : c = d) :
        HEq (Fiber.fiberInclusion.map c.obj.hom) (Fiber.fiberInclusion.map d.obj.hom) := by
      cases he
      rfl
    have hc : HEq a.val.iso.hom b.val.iso.hom := hcOfEq h
    apply Subtype.ext
    rcases a with ⟨⟨ax, ay, ai, hia⟩, ha0⟩
    rcases b with ⟨⟨bx, byy, bi, hib⟩, hb0⟩
    change ax = bx at ha
    change ay = byy at hb
    subst bx byy
    have hI : ai = bi := Iso.ext (eq_of_heq hc)
    subst bi
    rfl
  · rintro ⟨⟨a, b, m⟩, hm⟩
    letI : IsIso m := hm
    let e := Fiber.fiberInclusion.mapIso (asIso m)
    have h : S.p.IsHomLift (𝟙 U) e.hom := m.property
    let q : Obj F G := ⟨a.val, b.val, e, a.property.symm ▸ h⟩
    refine ⟨⟨q, a.property⟩, ?_⟩
    rfl

instance fiberComparison_faithful (U : D) : (fiberComparison F G U).Faithful where
  map_injective h := by
    apply Fiber.hom_ext
    apply Arrow.ext
    · exact congrArg (fun p => p.hom.left.val) h
    · exact congrArg (fun p => p.hom.right.val) h

instance fiberComparison_full (U : D) : (fiberComparison F G U).Full where
  map_surjective {a b} m := by
    have hl := m.hom.left.property
    have hr := m.hom.right.property
    let r : a.val ⟶ b.val := ⟨m.hom.left.val, m.hom.right.val,
      sameBase (𝟙 U) m.hom.left.val m.hom.right.val (ha := hl) (hb := hr),
      congrArg Subtype.val m.hom.w⟩
    haveI : X.p.IsHomLift (𝟙 U) ((fst F G).map r) := hl
    let x : a ⟶ b := ⟨r, (fst F G).isHomLift_map (𝟙 U) r⟩
    exact ⟨x, rfl⟩

/-- The fiber comparison is an equivalence, bijective on objects and
on each hom-set. -/
noncomputable def fiberComparisonEquivalence (U : D) :
    Fiber (based F G).p U ≌ IsoCommaInFiber F G U := by
  letI : (fiberComparison F G U).EssSurj :=
    ⟨fun a => let ⟨b, hb⟩ := (fiberComparison_bijective F G U).2 a; ⟨b, ⟨eqToIso hb⟩⟩⟩
  letI : (fiberComparison F G U).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact (fiberComparison F G U).asEquivalence

end Masullo.VerticalIsoComma
