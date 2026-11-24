import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Whiskering

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Masullo

universe u

section Whiskering

variable {A B C D : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C] [SmallCategory D]

/-- Corrected Lemma E.5.1.2. The two units have the source and target of the
transformation respectively. -/
theorem vertical_composition_laws {F F' F'' F''' : A ⥤ B}
    (α : F ⟶ F') (β : F' ⟶ F'') (γ : F'' ⟶ F''') :
    𝟙 F ≫ α = α ∧ α ≫ 𝟙 F' = α ∧ (α ≫ β) ≫ γ = α ≫ β ≫ γ :=
  ⟨Category.id_comp _, Category.comp_id _, Category.assoc _ _ _⟩

/-- Postcomposition in Lemma E.5.1.6. The identity in (E.5.1.11) is on B. -/
def postcomposeFunctors (G : B ⥤ C) : (A ⥤ B) ⥤ (A ⥤ C) :=
  (Functor.whiskeringRight A B C).obj G

theorem postcomposeFunctors_laws (G : B ⥤ C) {F F' F'' : A ⥤ B}
    (α : F ⟶ F') (β : F' ⟶ F'') :
    𝟙 F ◫ 𝟙 G = 𝟙 (F ⋙ G) ∧
      (α ◫ 𝟙 G) ≫ (β ◫ 𝟙 G) = (α ≫ β) ◫ 𝟙 G ∧
      (Functor.rightUnitor F).inv ≫ (α ◫ 𝟙 (𝟭 B)) ≫ (Functor.rightUnitor F').hom = α := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp
  · simp only [hcomp_id, whiskerRight_comp]
  · ext x
    simp

/-- Precomposition in Lemma E.5.1.8. -/
def precomposeFunctors (F : A ⥤ B) : (B ⥤ C) ⥤ (A ⥤ C) :=
  (Functor.whiskeringLeft A B C).obj F

theorem precomposeFunctors_laws (F : A ⥤ B) {G G' G'' : B ⥤ C}
    (α : G ⟶ G') (β : G' ⟶ G'') :
    (𝟙 F ◫ α) ≫ (𝟙 F ◫ β) = 𝟙 F ◫ (α ≫ β) ∧
      (Functor.leftUnitor G).inv ≫ (𝟙 (𝟭 B) ◫ α) ≫ (Functor.leftUnitor G').hom = α := by
  refine ⟨?_, ?_⟩
  · simp only [id_hcomp, whiskerLeft_comp]
  · ext x
    simp

/-- The three compatibility identities of Lemma E.5.1.9, with the canonical
functor associators making the source and target types explicit. -/
theorem whiskering_compatibility {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (α : F ⟶ F') (β : G ⟶ G') (γ : H ⟶ H') :
    whiskerRight (whiskerRight α G) H =
      (Functor.associator F G H).hom ≫ whiskerRight α (G ⋙ H) ≫
        (Functor.associator F' G H).inv ∧
    whiskerLeft F (whiskerLeft G γ) =
      (Functor.associator F G H).inv ≫ whiskerLeft (F ⋙ G) γ ≫
        (Functor.associator F G H').hom ∧
    whiskerRight (whiskerLeft F β) H =
      (Functor.associator F G H).hom ≫ whiskerLeft F (whiskerRight β H) ≫
        (Functor.associator F G' H).inv :=
  ⟨whiskerRight_twice G H α, whiskerLeft_twice F G γ, whiskerRight_left F β H⟩

/-- The two expressions for horizontal composition in Lemma E.5.1.10. -/
theorem whisker_interchange {F F' : A ⥤ B} {G G' : B ⥤ C}
    (α : F ⟶ F') (β : G ⟶ G') :
    whiskerLeft F β ≫ whiskerRight α G' = whiskerRight α G ≫ whiskerLeft F' β :=
  whiskerLeft_comp_whiskerRight α β

/-- Associativity of horizontal composition from Lemma E.5.1.12. -/
theorem horizontal_associativity {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (α : F ⟶ F') (β : G ⟶ G') (γ : H ⟶ H') :
    ((α ◫ β) ◫ γ) ≫ (Functor.associator F' G' H').hom =
      (Functor.associator F G H).hom ≫ (α ◫ (β ◫ γ)) := by
  ext x
  simp [NatTrans.hcomp_app, Functor.map_comp, Category.assoc]

/-- Units for horizontal composition and the vertical identity in E.5.1.12. -/
theorem horizontal_units {F F' : A ⥤ B} (α : F ⟶ F') :
    (Functor.leftUnitor F).inv ≫ (𝟙 (𝟭 A) ◫ α) ≫ (Functor.leftUnitor F').hom = α ∧
    (Functor.rightUnitor F).inv ≫ (α ◫ 𝟙 (𝟭 B)) ≫ (Functor.rightUnitor F').hom = α ∧
    𝟙 (𝟭 A) ≫ 𝟙 (𝟭 A) = 𝟙 (𝟭 A) := by
  refine ⟨?_, ?_, Category.id_comp _⟩
  · ext x
    simp
  · ext x
    simp

/-- The horizontal-vertical interchange law in Lemma E.5.1.13. -/
theorem horizontal_vertical_interchange {F F' F'' : A ⥤ B} {G G' G'' : B ⥤ C}
    (α : F ⟶ F') (α' : F' ⟶ F'') (β : G ⟶ G') (β' : G' ⟶ G'') :
    (α ≫ α') ◫ (β ≫ β') = (α ◫ β) ≫ (α' ◫ β') := by
  ext x
  simp only [NatTrans.hcomp_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [β'.naturality_assoc]

/-- Composition bifunctor of Lemma E.5.1.14. Its unit and associativity
identities are verified by the laws above and the functor unitors and associator. -/
def functorCompositionBifunctor : ((A ⥤ B) × (B ⥤ C)) ⥤ (A ⥤ C) where
  obj p := p.1 ⋙ p.2
  map t := t.1 ◫ t.2
  map_id p := by
    ext x
    simp
  map_comp t s := horizontal_vertical_interchange _ _ _ _

end Whiskering

/-- Lemma E.4.1.3. The source and target compatibilities are carried by the
dependent arrow map. Preservation of composition forces identity preservation
because the image of an identity is an invertible idempotent. -/
def groupoidFunctorOfComposition {A B : Type u} [Groupoid A] [Groupoid B]
    (F : A → B) (map : ∀ {x y : A}, (x ⟶ y) → (F x ⟶ F y))
    (hmap : ∀ {x y z : A} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = map f ≫ map g) :
    A ⥤ B where
  obj := F
  map := map
  map_id x := by
    have h := hmap (𝟙 x) (𝟙 x)
    rw [Category.id_comp] at h
    apply (cancel_mono (map (𝟙 x))).mp
    simpa only [Category.id_comp] using h.symm
  map_comp := hmap

theorem groupoid_composition_iff_morphism {A B : Type u} [Groupoid A] [Groupoid B]
    (F : A → B) (map : ∀ {x y : A}, (x ⟶ y) → (F x ⟶ F y)) :
    (∀ {x y z : A} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = map f ≫ map g) ↔
      ∃ f : A ⥤ B, ∃ h : f.obj = F, ∀ {x y : A} (a : x ⟶ y),
        f.map a ≫ eqToHom (congrFun h y) = eqToHom (congrFun h x) ≫ map a := by
  constructor
  · intro h
    refine ⟨groupoidFunctorOfComposition F map h, rfl, ?_⟩
    intro x y a
    change map a ≫ eqToHom (rfl : F y = F y) = eqToHom (rfl : F x = F x) ≫ map a
    simp
  · rintro ⟨f, h, hmap⟩
    subst F
    have heq {x y : A} (a : x ⟶ y) : f.map a = map a := by
      have ha := hmap a
      change f.map a ≫ eqToHom (rfl : f.obj y = f.obj y) =
        eqToHom (rfl : f.obj x = f.obj x) ≫ map a at ha
      simpa using ha
    intro x y z a b
    simpa only [heq] using f.map_comp a b

/-- Lemma E.4.1.4. The inverse of one factorization cancels the other. -/
theorem groupoid_composite_cancellation {A : Type u} [Groupoid A] {a b b' c : A}
    (y : a ⟶ b) (x : b ⟶ c) (w : a ⟶ b') (z : b' ⟶ c) (h : y ≫ x = w ≫ z) :
    (w ≫ z) ≫ (inv x ≫ inv y) = 𝟙 a := by
  rw [← h]
  simp [Category.assoc]

/-- Lemma E.5.4.7, with the codomain groupoid as the hypothesis. -/
theorem naturalTransformation_isIso_of_groupoid {A B : Type u} [SmallCategory A] [Groupoid B]
    {F F' : A ⥤ B} (α : F ⟶ F') : IsIso α := by
  letI (x : A) : IsIso (α.app x) := inferInstance
  exact NatIso.isIso_of_isIso_app α

/-- The strict 2-category of groupoids in Lemma E.5.4.8. -/
abbrev SmallGroupoid₂ := Bicategory.InducedBicategory Cat.{u, u}
  (fun X : Grpd.{u, u} => Grpd.forgetToCat.obj X)

def groupoid₂Inclusion : StrictPseudofunctor SmallGroupoid₂.{u} Cat.{u, u} :=
  Bicategory.InducedBicategory.forget

/-- The inverse to the inclusion on each hom-category. -/
def groupoid₂HomInverse (X Y : SmallGroupoid₂.{u}) :
    (groupoid₂Inclusion.obj X ⟶ groupoid₂Inclusion.obj Y) ⥤ (X ⟶ Y) where
  obj := fun f => Bicategory.InducedBicategory.mkHom f
  map := fun η => Bicategory.InducedBicategory.mkHom₂ η

/-- Lemma E.5.4.8 uses isomorphisms of hom-categories. Both composites
are equal to their respective identity functors. -/
theorem groupoid₂Inclusion_homIso (X Y : SmallGroupoid₂.{u}) :
    groupoid₂Inclusion.mapFunctor X Y ⋙ groupoid₂HomInverse X Y = 𝟭 (X ⟶ Y) ∧
    groupoid₂HomInverse X Y ⋙ groupoid₂Inclusion.mapFunctor X Y =
      𝟭 (groupoid₂Inclusion.obj X ⟶ groupoid₂Inclusion.obj Y) := ⟨rfl, rfl⟩

/-- All three clauses of Lemma E.5.7.6. The displayed base arrows express the
typing of the lifts of the corresponding morphisms. -/
theorem stronglyCartesian_composition {D E : Type u} [SmallCategory D] [SmallCategory E]
    (p : E ⥤ D) {a b c : E} {r s t : D} (f : r ⟶ s) (g : s ⟶ t)
    (φ : a ⟶ b) (ψ : b ⟶ c) [p.IsStronglyCartesian f φ] [p.IsStronglyCartesian g ψ] :
    p.IsStronglyCartesian (f ≫ g) (φ ≫ ψ) := inferInstance

theorem iso_isStronglyCartesian {D E : Type u} [SmallCategory D] [SmallCategory E]
    (p : E ⥤ D) {a b : E} {r s : D} (f : r ⟶ s) (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso φ] :
    p.IsStronglyCartesian f φ := inferInstance

theorem iso_of_stronglyCartesian_over_iso {D E : Type u} [SmallCategory D] [SmallCategory E]
    (p : E ⥤ D) {a b : E} {r s : D} (f : r ⟶ s) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [IsIso f] : IsIso φ :=
  Functor.IsStronglyCartesian.isIso_of_base_isIso p f φ

/-- Lemma E.5.7.15. Strict pullbacks of small categories exist. -/
theorem smallCat_strict_pullbacks : HasPullbacks Cat.{u, u} := inferInstance

/-- Lemma E.5.7.16. Strict pullbacks also exist over a fixed small category. -/
theorem smallCat_over_strict_pullbacks (D : Cat.{u, u}) : HasPullbacks (Over D) := inferInstance

end Masullo
