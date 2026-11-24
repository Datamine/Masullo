import CompactlyGenerated
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

open CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace

namespace Masullo

universe u

/-- Continuous maps with the topology of Definition E.1.2.6. -/
def ProbeMap (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] := C(X, Y)

namespace ProbeMap

variable {X Y Z T : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace T]

instance : CoeFun (ProbeMap X Y) (fun _ => X → Y) :=
  ⟨fun f => (show C(X, Y) from f)⟩

theorem map_continuous (f : ProbeMap X Y) : Continuous f :=
  (show C(X, Y) from f).continuous

@[ext]
theorem ext {f g : ProbeMap X Y} (h : ∀ x, f x = g x) : f = g :=
  ContinuousMap.ext h

/-- A set-sized family of triples for the compact Hausdorff probe subbasis. -/
def Probe (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :=
  (K : CompHaus.{u}) × C(K, X) × Opens Y

def subbasic (a : Probe X Y) : Set (ProbeMap X Y) :=
  {f | ∀ k : a.1, f (a.2.1 k) ∈ a.2.2}

instance : TopologicalSpace (ProbeMap X Y) :=
  generateFrom (range (subbasic (X := X) (Y := Y)))

theorem topology_eq_generateFrom :
    (inferInstance : TopologicalSpace (ProbeMap X Y)) =
      generateFrom (range (subbasic (X := X) (Y := Y))) := rfl

/-- E.1.2.8. Choose one probe for each distinct subbasic open, obtaining
an indexing type in the same universe as the space of maps. -/
theorem small_subbasis :
    ∃ (I : Type u) (a : I → Probe X Y),
      range (subbasic ∘ a) = range (subbasic (X := X) (Y := Y)) ∧
      (inferInstance : TopologicalSpace (ProbeMap X Y)) =
        generateFrom (range (subbasic ∘ a)) := by
  classical
  let I := range (subbasic (X := X) (Y := Y))
  let a (S : I) : Probe X Y := S.property.choose
  have ha (S : I) : subbasic (a S) = S.val := S.property.choose_spec
  have hr : range (subbasic ∘ a) = I := by
    ext S
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨a i, rfl⟩
    · intro hS
      exact ⟨⟨S, hS⟩, ha ⟨S, hS⟩⟩
  exact ⟨I, a, hr, hr.symm ▸ topology_eq_generateFrom⟩

def restrict {K : CompHaus.{u}} (p : C(K, X)) (f : ProbeMap X Y) : C(K, Y) :=
  ⟨fun k => f (p k), f.map_continuous.comp p.continuous⟩

theorem continuous_iff_restrict (f : T → ProbeMap X Y) :
    Continuous f ↔ ∀ (K : CompHaus.{u}) (p : C(K, X)), Continuous (restrict p ∘ f) := by
  change Continuous[_, generateFrom (range (subbasic (X := X) (Y := Y)))] f ↔ _
  rw [continuous_generateFrom_iff]
  constructor
  · intro hf K p
    apply ContinuousMap.continuous_compactOpen.mpr
    intro A hA U hU
    letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
    let L := CompHaus.of A
    let q : C(L, X) := p.comp ⟨Subtype.val, continuous_subtype_val⟩
    have h := hf (subbasic ⟨L, q, ⟨U, hU⟩⟩) (mem_range_self _)
    convert h using 1
    ext t
    exact ⟨fun ht k => ht k.property, fun ht k hk => ht ⟨k, hk⟩⟩
  · intro hf S hS
    obtain ⟨⟨K, p, U⟩, h⟩ := hS
    rw [← h]
    have hOpen := (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ U.isOpen).preimage (hf K p)
    convert hOpen using 1
    ext t
    simp [subbasic, restrict, MapsTo]

end ProbeMap

/-- The manuscript's compactly generated function space. -/
abbrev KelleyMap (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :=
  Kelley (ProbeMap X Y)

namespace KelleyMap

variable {X Y Z T W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace T] [TopologicalSpace W]

instance : CoeFun (KelleyMap X Y) (fun _ => X → Y) :=
  ⟨fun f => (show ProbeMap X Y from f)⟩

theorem map_continuous (f : KelleyMap X Y) : Continuous f :=
  ProbeMap.map_continuous (show ProbeMap X Y from f)

@[ext]
theorem ext {f g : KelleyMap X Y} (h : ∀ x, f x = g x) : f = g :=
  ProbeMap.ext h

def map (p : C(T, X)) (q : C(Y, Z)) (f : KelleyMap X Y) : KelleyMap T Z :=
  show C(T, Z) from q.comp ((show C(X, Y) from f).comp p)

theorem continuous_map (p : C(T, X)) (q : C(Y, Z)) : Continuous (map p q) := by
  apply continuous_to_Kelley (X := KelleyMap X Y) (Y := ProbeMap T Z)
  apply (ProbeMap.continuous_iff_restrict _).mpr
  intro K k
  have h := (ProbeMap.continuous_iff_restrict (id : ProbeMap X Y → ProbeMap X Y)).mp
    continuous_id K (p.comp k)
  exact (ContinuousMap.continuous_postcomp q).comp (h.comp continuous_Kelley_forget)

@[simp] theorem map_apply (p : C(T, X)) (q : C(Y, Z)) (f : KelleyMap X Y) (t : T) :
    map p q f t = q (f (p t)) := rfl

@[simp] theorem map_id (f : KelleyMap X Y) : map (.id X) (.id Y) f = f :=
  ext fun _ => rfl

theorem map_comp {Z' : Type u} [TopologicalSpace Z']
    (p : C(T, X)) (q : C(Y, Z)) (p' : C(W, T)) (q' : C(Z, Z'))
    (f : KelleyMap X Y) :
    map p' q' (map p q f) = map (p.comp p') (q'.comp q) f :=
  ext fun _ => rfl

theorem continuous_iff_restrict [CompactlyGeneratedSpace T] (f : T → KelleyMap X Y) :
    Continuous f ↔ ∀ (K : CompHaus.{u}) (p : C(K, X)), Continuous (ProbeMap.restrict p ∘ f) := by
  have h := ProbeMap.continuous_iff_restrict (show T → ProbeMap X Y from f)
  exact ⟨fun hf => h.mp ((continuous_Kelley_forget (X := ProbeMap X Y)).comp hf),
    fun hf => continuous_to_Kelley (Y := ProbeMap X Y) (h.mpr hf)⟩

theorem continuous_uncurry_iff [CompactlyGeneratedSpace T] (f : T → KelleyMap X Y) :
    Continuous (fun z : Kelley (T × X) => f z.1 z.2) ↔ Continuous f := by
  rw [continuous_iff_restrict f]
  constructor
  · intro hf K p
    apply ContinuousMap.continuous_of_continuous_uncurry
    letI : CompactlyGeneratedSpace (T × K) :=
      (locallyCompact_compactlyGenerated_and_prod (X := T) (Y := K)).2
    exact hf.comp (continuous_to_Kelley (X := T × K)
      (Y := T × X) (continuous_id.prodMap p.continuous))
  · intro hf
    apply continuous_from_compactlyGenerated (X := T × X)
    intro K p
    let p₁ : C(K, T) := ContinuousMap.fst.comp p
    let p₂ : C(K, X) := ContinuousMap.snd.comp p
    have h := ContinuousMap.continuous_uncurry_of_continuous ⟨_, hf K p₂⟩
    exact h.comp (p₁.continuous.prodMk continuous_id)

/-- The evaluation map uses the Kelley product. -/
theorem continuous_eval : Continuous (fun z : Kelley (KelleyMap X Y × X) => z.1 z.2) :=
  (continuous_uncurry_iff (id : KelleyMap X Y → KelleyMap X Y)).mpr continuous_id

def curry [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    (f : KelleyMap (Kelley (X × Y)) Z) : KelleyMap X (KelleyMap Y Z) :=
  show C(X, KelleyMap Y Z) from
    ⟨fun x => (show C(Y, Z) from ⟨fun y => f (x, y), f.map_continuous.comp
      (continuous_to_Kelley (X := Y) (Y := X × Y) (continuous_const.prodMk continuous_id))⟩),
      (continuous_uncurry_iff _).mp f.map_continuous⟩

def uncurry [CompactlyGeneratedSpace X]
    (f : KelleyMap X (KelleyMap Y Z)) : KelleyMap (Kelley (X × Y)) Z :=
  show C(Kelley (X × Y), Z) from
    ⟨fun z => f z.1 z.2, (continuous_uncurry_iff _).mpr f.map_continuous⟩

private theorem continuous_pair [CompactlyGeneratedSpace T] {p : T → X} {q : T → Y}
    (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun t : T => (show Kelley (X × Y) from (p t, q t))) :=
  continuous_to_Kelley (Y := X × Y) (hp.prodMk hq)

theorem continuous_eval_const (x : X) : Continuous (fun f : KelleyMap X Y => f x) :=
  continuous_eval.comp (continuous_pair continuous_id continuous_const)

private theorem continuous_fstK : Continuous (fun p : Kelley (X × Y) => p.1) :=
  continuous_fst.comp (continuous_Kelley_forget (X := X × Y))

private theorem continuous_sndK : Continuous (fun p : Kelley (X × Y) => p.2) :=
  continuous_snd.comp (continuous_Kelley_forget (X := X × Y))

theorem continuous_curry [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    Continuous (curry (X := X) (Y := Y) (Z := Z)) := by
  apply (continuous_uncurry_iff _).mp
  apply (continuous_uncurry_iff _).mp
  let M := KelleyMap (Kelley (X × Y)) Z
  let P := Kelley (Kelley (M × X) × Y)
  have hp : Continuous (fun p : P => p.1.1) :=
    (continuous_fstK (X := M) (Y := X)).comp
      (continuous_fstK (X := Kelley (M × X)) (Y := Y))
  have hq : Continuous (fun p : P => p.1.2) :=
    (continuous_sndK (X := M) (Y := X)).comp
      (continuous_fstK (X := Kelley (M × X)) (Y := Y))
  exact (continuous_eval (X := Kelley (X × Y)) (Y := Z)).comp
    (continuous_pair hp (continuous_pair hq (continuous_sndK (X := Kelley (M × X)) (Y := Y))))

theorem continuous_uncurry [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    Continuous (uncurry (X := X) (Y := Y) (Z := Z)) := by
  apply (continuous_uncurry_iff _).mp
  let M := KelleyMap X (KelleyMap Y Z)
  let P := Kelley (M × Kelley (X × Y))
  have hp : Continuous (fun p : P => p.2.1) :=
    (continuous_fstK (X := X) (Y := Y)).comp (continuous_sndK (X := M) (Y := Kelley (X × Y)))
  have hq : Continuous (fun p : P => p.2.2) :=
    (continuous_sndK (X := X) (Y := Y)).comp (continuous_sndK (X := M) (Y := Kelley (X × Y)))
  have hf : Continuous (fun p : P => p.1 p.2.1) :=
    (continuous_eval (X := X) (Y := KelleyMap Y Z)).comp
      (continuous_pair (continuous_fstK (X := M) (Y := Kelley (X × Y))) hp)
  exact (continuous_eval (X := Y) (Y := Z)).comp (continuous_pair hf hq)

/-- E.1.2.12. Currying is a homeomorphism of internal mapping spaces. -/
def curryHomeomorph [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    KelleyMap (Kelley (X × Y)) Z ≃ₜ KelleyMap X (KelleyMap Y Z) where
  toFun := curry
  invFun := uncurry
  left_inv _ := ext fun _ => rfl
  right_inv _ := ext fun _ => ext fun _ => rfl
  continuous_toFun := continuous_curry
  continuous_invFun := continuous_uncurry

@[simp] theorem curryHomeomorph_apply [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    (f : KelleyMap (Kelley (X × Y)) Z) (x : X) (y : Y) :
    curryHomeomorph f x y = f (x, y) := rfl

theorem weaklyHausdorff (hY : Masullo.WeaklyHausdorff Y) :
    Masullo.WeaklyHausdorff (KelleyMap X Y) := by
  apply (weaklyHausdorff_iff_kelleyClosedDiagonal _).mpr
  intro K p
  have heq : {k | (p k).1 = (p k).2} =
      ⋂ x : X, {k | (p k).1 x = (p k).2 x} := by
    ext k
    exact ⟨fun h => mem_iInter.mpr fun x => congrArg (fun f : KelleyMap X Y => f x) h,
      fun h => KelleyMap.ext (mem_iInter.mp h)⟩
  rw [heq]
  exact isClosed_iInter fun x => weaklyHausdorff_kelleyClosedDiagonal hY K
    ⟨_, ((continuous_eval_const x).prodMap (continuous_eval_const x)).comp p.continuous⟩

def comp (f : KelleyMap X Y) (g : KelleyMap Y Z) : KelleyMap X Z :=
  show C(X, Z) from ⟨fun x => g (f x), g.map_continuous.comp f.map_continuous⟩

theorem continuous_comp :
    Continuous (fun p : Kelley (KelleyMap X Y × KelleyMap Y Z) => comp p.1 p.2) := by
  apply (continuous_uncurry_iff _).mp
  let P := Kelley (KelleyMap X Y × KelleyMap Y Z)
  have hf : Continuous (fun p : Kelley (P × X) => p.1.1 p.2) :=
    (continuous_eval (X := X) (Y := Y)).comp (continuous_pair
      ((continuous_fstK (X := KelleyMap X Y) (Y := KelleyMap Y Z)).comp
        (continuous_fstK (X := P) (Y := X))) (continuous_sndK (X := P) (Y := X)))
  have hg : Continuous (fun p : Kelley (P × X) => p.1.2) :=
    (continuous_sndK (X := KelleyMap X Y) (Y := KelleyMap Y Z)).comp
      (continuous_fstK (X := P) (Y := X))
  exact (continuous_eval (X := Y) (Y := Z)).comp (continuous_pair hg hf)

end KelleyMap

namespace CGMapping

private abbrev cgProduct (X Y : CompactlyGenerated.{u, u}) : CompactlyGenerated.{u, u} := CompactlyGenerated.of (Kelley (X × Y))

def product (X Y : CompactlyGenerated.{u, u}) : LimitCone (pair X Y) := by
  let fst : cgProduct X Y ⟶ X := ConcreteCategory.ofHom
    ⟨Prod.fst, KelleyMap.continuous_fstK (X := X) (Y := Y)⟩
  let snd : cgProduct X Y ⟶ Y := ConcreteCategory.ofHom
    ⟨Prod.snd, KelleyMap.continuous_sndK (X := X) (Y := Y)⟩
  let c := BinaryFan.mk fst snd
  refine ⟨c, BinaryFan.IsLimit.mk c (fun f g => ConcreteCategory.ofHom
    ⟨fun t => (f t, g t), KelleyMap.continuous_pair f.hom.hom.continuous g.hom.hom.continuous⟩)
      (fun _ _ => rfl) (fun _ _ => rfl) ?_⟩
  intro W f g h h₁ h₂
  exact ConcreteCategory.hom_ext _ _ fun t => Prod.ext
    (ConcreteCategory.congr_hom h₁ t) (ConcreteCategory.congr_hom h₂ t)

private def terminal : LimitCone (Functor.empty.{0} CompactlyGenerated.{u, u}) :=
  let P := CompactlyGenerated.of PUnit.{u + 1}
  ⟨asEmptyCone P, IsTerminal.ofUniqueHom (fun X =>
    ConcreteCategory.ofHom (ContinuousMap.const X PUnit.unit)) (fun _ _ =>
    ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _)⟩

noncomputable abbrev cartesian : CartesianMonoidalCategory CompactlyGenerated.{u, u} :=
  .ofChosenFiniteProducts terminal product

attribute [local instance] cartesian

abbrev internalHom (X Y : CompactlyGenerated.{u, u}) : CompactlyGenerated.{u, u} :=
  CompactlyGenerated.of (KelleyMap X Y)

abbrev internalHomFunctor (X : CompactlyGenerated.{u, u}) :
    CompactlyGenerated.{u, u} ⥤ CompactlyGenerated.{u, u} where
  obj := internalHom X
  map {_Y _Z} f := ConcreteCategory.ofHom
    ⟨KelleyMap.map (.id X) f.hom.hom, KelleyMap.continuous_map (.id X) f.hom.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def rightCurry (X Y Z : CompactlyGenerated.{u, u}) :
    ((MonoidalCategory.tensorLeft X).obj Y ⟶ Z) ≃ (Y ⟶ internalHom X Z) where
  toFun f := ConcreteCategory.ofHom
    (show C(Y, KelleyMap X Z) from KelleyMap.curry (X := Y) (Y := X) (Z := Z)
      (show C(Kelley (Y × X), Z) from ⟨fun p => f (p.2, p.1),
        f.hom.hom.continuous.comp (KelleyMap.continuous_pair
          (KelleyMap.continuous_sndK (X := Y) (Y := X))
          (KelleyMap.continuous_fstK (X := Y) (Y := X)))⟩))
  invFun f := ConcreteCategory.ofHom
    ⟨fun p => (show KelleyMap X Z from f p.2) p.1, (KelleyMap.map_continuous
      (KelleyMap.uncurry (X := Y) (Y := X) (Z := Z) f.hom.hom)).comp
      (KelleyMap.continuous_pair (KelleyMap.continuous_sndK (X := X) (Y := Y))
        (KelleyMap.continuous_fstK (X := X) (Y := Y)))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The adjunction of E.1.2.13, using the Kelley product and mapping space. -/
noncomputable def mappingAdjunction (X : CompactlyGenerated.{u, u}) :
    MonoidalCategory.tensorLeft X ⊣ internalHomFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rightCurry X
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

noncomputable abbrev monoidalClosed : MonoidalClosed CompactlyGenerated.{u, u} :=
  ⟨fun X => ⟨internalHomFunctor X, mappingAdjunction X⟩⟩

/-- E.1.2.10. Precomposition and postcomposition form one bifunctor. -/
def mappingBifunctor :
    CompactlyGenerated.{u, u}ᵒᵖ × CompactlyGenerated.{u, u} ⥤ CompactlyGenerated.{u, u} where
  obj p := internalHom p.1.unop p.2
  map f := ConcreteCategory.ofHom
    ⟨KelleyMap.map f.1.unop.hom.hom f.2.hom.hom,
      KelleyMap.continuous_map f.1.unop.hom.hom f.2.hom.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- E.1.2.13. The enrichment uses the internal function spaces and their
continuous composition. -/
noncomputable abbrev selfEnrichment :
    EnrichedCategory CompactlyGenerated.{u, u} CompactlyGenerated.{u, u} where
  Hom := internalHom
  id X := ConcreteCategory.ofHom
    (ContinuousMap.const PUnit (show KelleyMap X X from ContinuousMap.id X))
  comp _ _ _ := ConcreteCategory.ofHom ⟨_, KelleyMap.continuous_comp⟩
  id_comp _ _ := rfl
  comp_id _ _ := rfl
  assoc _ _ _ _ := rfl

end CGMapping

namespace CGWHMapping

private abbrev productSpace (X Y : CGWH.{u}) : CGWH.{u} :=
  CGWH.of (weaklyHausdorff_kelleyProduct X.property Y.property)

def product (X Y : CGWH.{u}) : LimitCone (pair X Y) := by
  let fst : productSpace X Y ⟶ X := CGWH.map
    ⟨fun p => p.1, KelleyMap.continuous_fstK (X := X.obj) (Y := Y.obj)⟩
  let snd : productSpace X Y ⟶ Y := CGWH.map
    ⟨fun p => p.2, KelleyMap.continuous_sndK (X := X.obj) (Y := Y.obj)⟩
  let c := BinaryFan.mk fst snd
  refine ⟨c, BinaryFan.IsLimit.mk c (fun f g => CGWH.map
    ⟨fun t => (f.hom t, g.hom t), KelleyMap.continuous_pair
      f.hom.hom.hom.continuous g.hom.hom.hom.continuous⟩) (fun _ _ => rfl) (fun _ _ => rfl) ?_⟩
  intro W f g h h₁ h₂
  apply cgwhForget.map_injective
  exact ConcreteCategory.hom_ext _ _ fun t => Prod.ext
    (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₁) t)
    (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom h₂) t)

private def terminal : LimitCone (Functor.empty.{0} CGWH.{u}) :=
  let P := CGWH.of (X := PUnit.{u + 1}) (fun _ k => (isCompact_range k.continuous).isClosed)
  ⟨asEmptyCone P, IsTerminal.ofUniqueHom (fun X =>
    CGWH.map (ContinuousMap.const X.obj PUnit.unit)) (fun _ _ =>
    cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ fun _ =>
      @Subsingleton.elim PUnit.{u + 1} inferInstance _ _))⟩

noncomputable abbrev cartesian : CartesianMonoidalCategory CGWH.{u} :=
  .ofChosenFiniteProducts terminal product

attribute [local instance] cartesian

abbrev internalHom (X Y : CGWH.{u}) : CGWH.{u} :=
  CGWH.of (KelleyMap.weaklyHausdorff (X := X.obj) Y.property)

abbrev internalHomFunctor (X : CGWH.{u}) : CGWH.{u} ⥤ CGWH.{u} where
  obj := internalHom X
  map {_Y _Z} f := ObjectProperty.homMk ((CGMapping.internalHomFunctor X.obj).map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

private noncomputable def rightCurry (X Y Z : CGWH.{u}) :
    ((MonoidalCategory.tensorLeft X).obj Y ⟶ Z) ≃ (Y ⟶ internalHom X Z) where
  toFun f := ObjectProperty.homMk (CGMapping.rightCurry X.obj Y.obj Z.obj f.hom)
  invFun f := ObjectProperty.homMk ((CGMapping.rightCurry X.obj Y.obj Z.obj).symm f.hom)
  left_inv _ := rfl
  right_inv _ := rfl

/-- E.2.2.10. The same cartesian closed structure restricts to CGWH. -/
noncomputable def mappingAdjunction (X : CGWH.{u}) :
    MonoidalCategory.tensorLeft X ⊣ internalHomFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rightCurry X
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

noncomputable abbrev monoidalClosed : MonoidalClosed CGWH.{u} :=
  ⟨fun X => ⟨internalHomFunctor X, mappingAdjunction X⟩⟩

end CGWHMapping

end Masullo
