import VerticalIsoComma
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift
open scoped CategoryTheory.BasedFunctor

namespace Masullo.VerticalIsoComma

universe u

variable {D : Type u} [SmallCategory D]
  {X Y S : BasedCategory.{u, u} D} {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}

/-- A based functor preserves the strongly Cartesian arrows for each
specified base arrow. -/
def PreservesCartesian {U V : BasedCategory.{u, u} D} (J : U ⥤ᵇ V) : Prop :=
  ∀ {R Q : D} {a b : U.obj} (f : R ⟶ Q) (φ : a ⟶ b),
    U.p.IsStronglyCartesian f φ → V.p.IsStronglyCartesian f (J.map φ)

theorem strong_of_components (hG : PreservesCartesian G)
    {R Q : D} {a b : Obj F G} (v : R ⟶ Q) (m : a ⟶ b)
    (hmL : X.p.IsStronglyCartesian v m.left) (hmR : Y.p.IsStronglyCartesian v m.right) :
    (based F G).p.IsStronglyCartesian v m := by
  letI := hmL
  letI := hmR
  haveI : S.p.IsStronglyCartesian v (G.map m.right) := hG v m.right hmR
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · haveI : X.p.IsHomLift v ((fst F G).map m) := hmL.toIsHomLift
    exact (fst F G).isHomLift_map v m
  intro c g n hn
  change Obj F G at c
  change X.p.obj c.left ⟶ R at g
  letI : (based F G).p.IsHomLift (g ≫ v) n := hn
  haveI hnL : X.p.IsHomLift (g ≫ v) n.left :=
    (fst F G).preserves_isHomLift (g ≫ v) n
  haveI hnR : Y.p.IsHomLift (g ≫ v) n.right :=
    (snd F G).preserves_isHomLift (g ≫ v) n
  let L := IsStronglyCartesian.map X.p v m.left (g := g) rfl n.left
  let M := IsStronglyCartesian.map Y.p v m.right (g := g) rfl n.right
  have hL : L ≫ m.left = n.left := IsStronglyCartesian.fac _ _ _ _ _
  have hM : M ≫ m.right = n.right := IsStronglyCartesian.fac _ _ _ _ _
  haveI hLi : X.p.IsHomLift g L := IsStronglyCartesian.map_isHomLift _ _ _ _ _
  haveI hMi : Y.p.IsHomLift g M := IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have hSquare : F.map L ≫ a.iso.hom = c.iso.hom ≫ G.map M := by
    haveI : S.p.IsHomLift g (F.map L ≫ a.iso.hom) :=
      IsHomLift.comp_lift_id_right' S.p g (F.map L) (X.p.obj a.left) a.iso.hom
    haveI : S.p.IsHomLift (𝟙 (X.p.obj c.left)) c.iso.hom := c.vertical
    haveI : S.p.IsHomLift g (c.iso.hom ≫ G.map M) :=
      IsHomLift.comp_lift_id_left' S.p (X.p.obj c.left) c.iso.hom g (G.map M)
    apply IsStronglyCartesian.ext S.p v (G.map m.right) g
    rw [Category.assoc, ← m.square, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hL, n.square,
      Category.assoc, ← CategoryTheory.Functor.map_comp, hM]
  let j : c ⟶ a := ⟨L, M, sameBase g L M (ha := hLi) (hb := hMi), hSquare⟩
  haveI : X.p.IsHomLift g ((fst F G).map j) := hLi
  refine ⟨j, ⟨(fst F G).isHomLift_map g j, Arrow.ext hL hM⟩, ?_⟩
  rintro k ⟨hk, hkn⟩
  letI : (based F G).p.IsHomLift g k := hk
  haveI : X.p.IsHomLift g k.left := (fst F G).preserves_isHomLift g k
  haveI : Y.p.IsHomLift g k.right := (snd F G).preserves_isHomLift g k
  apply Arrow.ext
  · exact IsStronglyCartesian.map_uniq X.p v m.left (g := g) rfl n.left k.left (congrArg Arrow.left hkn)
  · exact IsStronglyCartesian.map_uniq Y.p v m.right (g := g) rfl n.right k.right (congrArg Arrow.right hkn)

theorem exists_componentLift [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G)
    (a : Obj F G) (R : D) (f : R ⟶ X.p.obj a.left) :
    ∃ b : Obj F G, ∃ m : b ⟶ a,
      X.p.IsStronglyCartesian f m.left ∧ Y.p.IsStronglyCartesian f m.right := by
  obtain ⟨x, α, hα⟩ := IsPreFibered.exists_isCartesian X.p (a := a.left) rfl f
  obtain ⟨y, β, hβ⟩ := IsPreFibered.exists_isCartesian Y.p (a := a.right) (base_eq a) f
  letI := hα
  letI := hβ
  haveI haL : X.p.IsStronglyCartesian f α := inferInstance
  haveI haR : Y.p.IsStronglyCartesian f β := inferInstance
  haveI : S.p.IsStronglyCartesian f (F.map α) := hF f α haL
  haveI : S.p.IsStronglyCartesian f (G.map β) := hG f β haR
  let Q := X.p.obj a.left
  haveI : S.p.IsHomLift (𝟙 Q) a.iso.hom := a.vertical
  haveI : S.p.IsCartesian f (F.map α ≫ a.iso.hom) :=
    IsCartesian.of_comp_iso S.p f (F.map α) a.iso
  let ι := IsCartesian.domainUniqueUpToIso S.p f (G.map β) (F.map α ≫ a.iso.hom)
  have hr : X.p.obj x = R := domain_eq X.p f α
  have hι : S.p.IsHomLift (𝟙 (X.p.obj x)) ι.hom :=
    hr.symm ▸ (inferInstanceAs (S.p.IsHomLift (𝟙 R) ι.hom))
  let b : Obj F G := ⟨x, y, ι, hι⟩
  let m : b ⟶ a := ⟨α, β, sameBase (a := b) (b := a) f α β, by
    exact (IsCartesian.fac S.p f (G.map β) (F.map α ≫ a.iso.hom)).symm⟩
  exact ⟨b, m, haL, haR⟩

/-- If both arrows preserve Cartesian lifts, this two-fiber product of
based categories is fibered over the same base. -/
theorem isFibered [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G) :
    (based F G).p.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain ⟨b, m, hL, hR⟩ := exists_componentLift hF hG a R f
  exact ⟨b, m, strong_of_components hG f m hL hR⟩

private theorem strong_components [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G)
    {R Q : D} {a b : Obj F G} (f : R ⟶ Q) (m : a ⟶ b)
    (hm : (based F G).p.IsStronglyCartesian f m) :
    X.p.IsStronglyCartesian f m.left ∧ Y.p.IsStronglyCartesian f m.right := by
  let p := (based F G).p
  haveI hmLift : p.IsHomLift f m := hm.toIsHomLift
  have hb : X.p.obj b.left = Q := codomain_eq p f m
  subst Q
  obtain ⟨z, n, hL, hR⟩ := exists_componentLift hF hG b R f
  haveI hmStrong : p.IsStronglyCartesian f m := hm
  haveI hnStrong : p.IsStronglyCartesian f n := strong_of_components hG f n hL hR
  haveI hmLift' : p.IsHomLift f m := hmStrong.toIsHomLift
  haveI hmCart : p.IsCartesian f m := IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f m
  haveI hnCart : p.IsCartesian f n := IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f n
  let e := IsCartesian.domainUniqueUpToIso p f n m
  have heq : e.hom ≫ n = m := IsCartesian.fac p f n m
  let I := (fst F G).toFunctor.mapIso e
  let J := (snd F G).toFunctor.mapIso e
  haveI : (based F G).p.IsHomLift (𝟙 R) e.hom := by
    change p.IsHomLift (𝟙 R) e.hom
    exact IsCartesian.domainUniqueUpToIso_inv_isHomLift p f n m
  haveI hIlift : X.p.IsHomLift (𝟙 R) I.hom :=
    (fst F G).preserves_isHomLift (𝟙 R) e.hom
  haveI hJlift : Y.p.IsHomLift (𝟙 R) J.hom :=
    (snd F G).preserves_isHomLift (𝟙 R) e.hom
  have hLeq : I.hom ≫ n.left = m.left := congrArg Arrow.left heq
  have hReq : J.hom ≫ n.right = m.right := congrArg Arrow.right heq
  have hLc : X.p.IsCartesian f (I.hom ≫ n.left) := by
    have h := @IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ X.p _ _ _ _ f n.left hL
    exact @IsCartesian.of_iso_comp _ _ _ _ X.p _ _ _ _ f n.left h _ I hIlift
  have hRc : Y.p.IsCartesian f (J.hom ≫ n.right) := by
    have h := @IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ Y.p _ _ _ _ f n.right hR
    exact @IsCartesian.of_iso_comp _ _ _ _ Y.p _ _ _ _ f n.right h _ J hJlift
  haveI : X.p.IsCartesian f m.left := hLeq ▸ hLc
  haveI : Y.p.IsCartesian f m.right := hReq ▸ hRc
  exact ⟨IsFibered.isStronglyCartesian_of_isCartesian X.p f m.left,
    IsFibered.isStronglyCartesian_of_isCartesian Y.p f m.right⟩

/-- Both projections preserve Cartesian arrows, and the universal
functor preserves them whenever its components do. -/
theorem preserves_projections [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G) :
    PreservesCartesian (fst F G) ∧ PreservesCartesian (snd F G) :=
  ⟨fun f m hm => (strong_components hF hG f m hm).1,
   fun f m hm => (strong_components hF hG f m hm).2⟩

theorem preserves_lift {T : BasedCategory.{u, u} D}
    (hG : PreservesCartesian G) (A : T ⥤ᵇ X) (B : T ⥤ᵇ Y) (i : (A ⋙ F) ≅ (B ⋙ G))
    (hA : PreservesCartesian A) (hB : PreservesCartesian B) :
    PreservesCartesian (lift F G A B i) :=
  fun f m hm => strong_of_components hG f ((lift F G A B i).map m)
    (hA f m hm) (hB f m hm)

/-- When the factors are fibered in groupoids, every vertical arrow
in the two-fiber product is invertible. -/
theorem vertical_arrow_isIso
    (hX : ∀ (U : D) {a b : X.obj} (m : a ⟶ b), X.p.IsHomLift (𝟙 U) m → IsIso m)
    (hY : ∀ (U : D) {a b : Y.obj} (m : a ⟶ b), Y.p.IsHomLift (𝟙 U) m → IsIso m)
    {U : D} {a b : Obj F G} (m : a ⟶ b) (hm : (based F G).p.IsHomLift (𝟙 U) m) :
    IsIso m := by
  haveI : (based F G).p.IsHomLift (𝟙 U) m := hm
  have hx : X.p.IsHomLift (𝟙 U) m.left := (fst F G).preserves_isHomLift (𝟙 U) m
  have hy : Y.p.IsHomLift (𝟙 U) m.right := (snd F G).preserves_isHomLift (𝟙 U) m
  letI := hX U m.left hx
  letI := hY U m.right hy
  have hbase : X.p.obj a.left = U := @IsHomLift.domain_eq _ _ _ _ X.p _ _ _ _ _ _ hx
  let e := objectIso (asIso m.left) (asIso m.right) (hbase.symm ▸ hx) (hbase.symm ▸ hy) m.square
  have he : e.hom = m := Arrow.ext rfl rfl
  rw [← he]
  infer_instance

/-- Corollary E.5.7.11. The computed product is fibered in groupoids
when the factors are, with the same universal functor and projections
as in the category of based categories. -/
theorem fiber_isGroupoid [X.p.IsFibered] [Y.p.IsFibered]
    (hF : PreservesCartesian F) (hG : PreservesCartesian G)
    (hX : ∀ (U : D) {a b : X.obj} (m : a ⟶ b), X.p.IsHomLift (𝟙 U) m → IsIso m)
    (hY : ∀ (U : D) {a b : Y.obj} (m : a ⟶ b), Y.p.IsHomLift (𝟙 U) m → IsIso m) :
    (based F G).p.IsFibered ∧ PreservesCartesian (fst F G) ∧ PreservesCartesian (snd F G) ∧
      (∀ (U : D) {a b : Fiber (based F G).p U} (m : a ⟶ b), IsIso m) := by
  refine ⟨isFibered hF hG, (preserves_projections hF hG).1, (preserves_projections hF hG).2, ?_⟩
  intro U a b m
  letI hm : IsIso (Fiber.fiberInclusion.map m) := vertical_arrow_isIso hX hY _ m.property
  let i := asIso (Fiber.fiberInclusion.map m)
  letI : (based F G).p.IsHomLift (𝟙 U) i.hom := m.property
  let n : b ⟶ a := ⟨i.inv, IsHomLift.lift_id_inv (based F G).p U i⟩
  refine ⟨⟨n, ?_, ?_⟩⟩
  · exact Fiber.hom_ext i.hom_inv_id
  · exact Fiber.hom_ext i.inv_hom_id

end Masullo.VerticalIsoComma
