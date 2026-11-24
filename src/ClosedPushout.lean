import CompactlyGenerated

open CategoryTheory CategoryTheory.Limits Function Set Topology TopologicalSpace

namespace Masullo

universe u

noncomputable section

variable {P X Z : Type u} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Z]
variable (p : C(P, Z)) (q : C(P, X))

/-- A set representative identifying each point of the embedded copy of P
with its image in X. The topology on the pushout will be the quotient topology. -/
private noncomputable def glueKey (a : X ⊕ Z) : X ⊕ Z := by
  classical
  exact a.elim Sum.inl (fun z => if hz : z ∈ range p then Sum.inl (q hz.choose) else Sum.inr z)

noncomputable abbrev glueSetoid : Setoid (X ⊕ Z) := Setoid.ker (glueKey p q)

abbrev GlueSpace := Quotient (glueSetoid p q)

abbrev glueProjection : X ⊕ Z → GlueSpace p q := @Quotient.mk' (X ⊕ Z) (glueSetoid p q)

abbrev glueLeft (x : X) : GlueSpace p q := glueProjection p q (Sum.inl x)

abbrev glueRight (z : Z) : GlueSpace p q := glueProjection p q (Sum.inr z)

private theorem glueKey_left (x : X) : glueKey p q (Sum.inl x) = Sum.inl x := rfl

private theorem glueKey_right (hp : Injective p) (t : P) :
    glueKey p q (Sum.inr (p t)) = Sum.inl (q t) := by
  classical
  have ht : p t ∈ range p := mem_range_self t
  have he : ht.choose = t := hp ht.choose_spec
  simp [glueKey, he]

private theorem glueKey_other {z : Z} (hz : z ∉ range p) :
    glueKey p q (Sum.inr z) = Sum.inr z := by
  classical
  change (if h : z ∈ range p then Sum.inl (q h.choose) else Sum.inr z) = Sum.inr z
  rw [dite_eq_right hz]

theorem glueLeft_eq_glueRight (hp : Injective p) (x : X) (z : Z) :
    glueLeft p q x = glueRight p q z ↔ ∃ t : P, p t = z ∧ q t = x := by
  change Quotient.mk'' (s₁ := glueSetoid p q) (Sum.inl x) = Quotient.mk'' (Sum.inr z) ↔ _
  rw [Quotient.eq'', Setoid.ker_def, glueKey_left]
  by_cases hz : z ∈ range p
  · obtain ⟨t, rfl⟩ := hz
    rw [glueKey_right p q hp, Sum.inl.injEq]
    constructor
    · intro h
      exact ⟨t, rfl, h.symm⟩
    · rintro ⟨s, hs, he⟩
      exact (he.symm.trans (congrArg q (hp hs)))
  · rw [glueKey_other p q hz]
    exact ⟨by simp, fun ⟨t, ht, _⟩ => (hz ⟨t, ht⟩).elim⟩

private theorem glueRight_eq_glueRight (hp : Injective p) (z w : Z) :
    glueRight p q z = glueRight p q w ↔
      z = w ∨ ∃ t s : P, p t = z ∧ p s = w ∧ q t = q s := by
  change Quotient.mk'' (s₁ := glueSetoid p q) (Sum.inr z) = Quotient.mk'' (Sum.inr w) ↔ _
  rw [Quotient.eq'', Setoid.ker_def]
  constructor
  · intro h
    by_cases hz : z ∈ range p <;> by_cases hw : w ∈ range p
    · obtain ⟨t, rfl⟩ := hz
      obtain ⟨s, rfl⟩ := hw
      rw [glueKey_right p q hp, glueKey_right p q hp] at h
      exact Or.inr ⟨t, s, rfl, rfl, Sum.inl.inj h⟩
    · obtain ⟨t, rfl⟩ := hz
      simp [glueKey_right p q hp, glueKey_other p q hw] at h
    · obtain ⟨s, rfl⟩ := hw
      simp [glueKey_other p q hz, glueKey_right p q hp] at h
    · exact Or.inl (Sum.inr.inj ((glueKey_other p q hz).symm.trans
        (h.trans (glueKey_other p q hw))))
  · rintro (rfl | ⟨t, s, rfl, rfl, h⟩)
    · rfl
    · rw [glueKey_right p q hp, glueKey_right p q hp, h]

theorem glueLeft_injective : Injective (glueLeft p q) := by
  intro x y h
  exact Sum.inl.inj (Quotient.exact' h)

theorem glueLeft_closedEmbedding (hp : IsClosedEmbedding p) :
    IsClosedEmbedding (glueLeft p q) := by
  have hproj : IsQuotientMap (glueProjection p q) := isQuotientMap_quotient_mk'
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (hproj.continuous.comp continuous_inl) (glueLeft_injective p q)
  intro S hS
  apply hproj.isClosed_preimage.mp
  apply isClosed_sum_iff.mpr
  have hL : Sum.inl ⁻¹' (glueProjection p q ⁻¹' (glueLeft p q '' S)) = S := by
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => (glueLeft_injective p q he) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hR : Sum.inr ⁻¹' (glueProjection p q ⁻¹' (glueLeft p q '' S)) = p '' (q ⁻¹' S) := by
    ext z
    constructor
    · rintro ⟨x, hx, he⟩
      obtain ⟨t, ht, hq⟩ := (glueLeft_eq_glueRight p q hp.injective x z).mp he
      exact ⟨t, show q t ∈ S from hq.symm ▸ hx, ht⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨q t, ht, (glueLeft_eq_glueRight p q hp.injective _ _).mpr ⟨t, rfl, rfl⟩⟩
  change IsClosed (Sum.inl ⁻¹' (glueProjection p q ⁻¹' (glueLeft p q '' S))) ∧
    IsClosed (Sum.inr ⁻¹' (glueProjection p q ⁻¹' (glueLeft p q '' S)))
  rw [hL, hR]
  exact ⟨hS, hp.isClosedMap _ (hS.preimage q.continuous)⟩

/-- The usual quotient universal property, in arbitrary topological spaces. -/
def glueDesc {Y : Type u} [TopologicalSpace Y] (hp : Injective p)
    (f : C(X, Y)) (g : C(Z, Y)) (h : ∀ t, f (q t) = g (p t)) :
    C(GlueSpace p q, Y) := by
  let k : C(X ⊕ Z, Y) := ⟨Sum.elim f g, continuous_sum_dom.mpr ⟨f.continuous, g.continuous⟩⟩
  have hk (a b : X ⊕ Z) (hab : glueSetoid p q a b) : k a = k b := by
    have hab' : glueProjection p q a = glueProjection p q b := Quotient.sound' hab
    cases a with
    | inl x =>
      cases b with
      | inl y =>
        have e := glueLeft_injective p q hab'
        exact congrArg f e
      | inr z =>
        obtain ⟨t, rfl, rfl⟩ := (glueLeft_eq_glueRight p q hp x z).mp hab'
        exact h t
    | inr z =>
      cases b with
      | inl x =>
        obtain ⟨t, rfl, rfl⟩ := (glueLeft_eq_glueRight p q hp x z).mp hab'.symm
        exact (h t).symm
      | inr w =>
        rcases (glueRight_eq_glueRight p q hp z w).mp hab' with rfl | ⟨t, s, rfl, rfl, e⟩
        · rfl
        · exact (h t).symm.trans ((congrArg f e).trans (h s))
  exact ⟨Quotient.lift k hk, k.continuous.quotient_lift hk⟩

def glueLeftMap : C(X, GlueSpace p q) :=
  ⟨glueLeft p q, continuous_quotient_mk'.comp continuous_inl⟩

def glueRightMap : C(Z, GlueSpace p q) :=
  ⟨glueRight p q, continuous_quotient_mk'.comp continuous_inr⟩

theorem glue_commutes (hp : Injective p) (t : P) :
    glueLeftMap p q (q t) = glueRightMap p q (p t) :=
  (glueLeft_eq_glueRight p q hp _ _).mpr ⟨t, rfl, rfl⟩

theorem glue_ext {Y : Type u} {f g : GlueSpace p q → Y}
    (hL : ∀ x, f (glueLeft p q x) = g (glueLeft p q x))
    (hR : ∀ z, f (glueRight p q z) = g (glueRight p q z)) : f = g := by
  funext t
  obtain ⟨a, rfl⟩ := (@Quotient.mk'_surjective _ (glueSetoid p q)) t
  cases a with
  | inl x => exact hL x
  | inr z => exact hR z

/-- The same quotient and inclusions give the pushout in all spaces. -/
def topCatGlue_isColimit (hp : Injective p) :
    IsColimit (PushoutCocone.mk (TopCat.ofHom (glueLeftMap p q))
      (TopCat.ofHom (glueRightMap p q)) (TopCat.ext (glue_commutes p q hp)) :
        PushoutCocone (TopCat.ofHom q) (TopCat.ofHom p)) := by
  refine PushoutCocone.IsColimit.mk _ (fun c => TopCat.ofHom
    (glueDesc p q hp c.inl.hom c.inr.hom (ConcreteCategory.congr_hom c.condition))) ?_ ?_ ?_
  · exact fun _ => TopCat.ext (fun _ => rfl)
  · exact fun _ => TopCat.ext (fun _ => rfl)
  · intro c f hL hR
    apply TopCat.ext
    exact congrFun (glue_ext p q (ConcreteCategory.congr_hom hL) (ConcreteCategory.congr_hom hR))

/-- The ordinary topological pullback is the original embedded space. -/
def gluePullbackHomeomorph (hp : IsClosedEmbedding p) :
    P ≃ₜ {a : X × Z // glueLeft p q a.1 = glueRight p q a.2} := by
  let f : P → {a : X × Z // glueLeft p q a.1 = glueRight p q a.2} :=
    fun t => ⟨(q t, p t), glue_commutes p q hp.injective t⟩
  have hf : Continuous f := (q.continuous.prodMk p.continuous).subtype_mk _
  have hinj : Injective f := fun _ _ h => hp.injective (congrArg (fun a => a.val.2) h)
  have hsurj : Surjective f := by
    rintro ⟨⟨x, z⟩, h⟩
    obtain ⟨t, ht, hq⟩ := (glueLeft_eq_glueRight p q hp.injective x z).mp h
    exact ⟨t, Subtype.ext (Prod.ext hq ht)⟩
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, hf, hp.isEmbedding.isInducing.continuous_iff.mpr ?_⟩
  have eq : p ∘ e.symm = fun a => a.val.2 :=
    funext fun a => congrArg (fun b => b.val.2) (e.apply_symm_apply a)
  change Continuous (p ∘ e.symm)
  rw [eq]
  exact continuous_snd.comp continuous_subtype_val

variable [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Z]

theorem glueSpace_weaklyHausdorff (hX : WeaklyHausdorff X) (hZ : WeaklyHausdorff Z)
    (hp : IsClosedEmbedding p) : WeaklyHausdorff (GlueSpace p q) := by
  let A := X ⊕ Z
  let left : X → A := Sum.inl
  let right : P → A := Sum.inr ∘ p
  have hl : IsClosedEmbedding left := IsClosedEmbedding.inl
  have hr : IsClosedEmbedding right := IsClosedEmbedding.inr.comp hp
  let D : Set (A × A) := {a | a.1 = a.2}
  let L : Set (X × P) := {a | a.1 = q a.2}
  let R : Set (P × X) := {a | q a.1 = a.2}
  let B : Set (P × P) := {a | q a.1 = q a.2}
  have hD : IsClosed (show Set (Kelley (A × A)) from D) := cgwh_isClosed_equalizer (X := Kelley (A × A)) (CGWH.weaklyHausdorff_sum hX hZ)
    ⟨Prod.fst, continuous_fst.comp continuous_Kelley_forget⟩
    ⟨Prod.snd, continuous_snd.comp continuous_Kelley_forget⟩
  have hL : IsClosed (show Set (Kelley (X × P)) from L) := cgwh_isClosed_equalizer (X := Kelley (X × P)) hX
    ⟨Prod.fst, continuous_fst.comp continuous_Kelley_forget⟩
    ⟨q ∘ Prod.snd, q.continuous.comp (continuous_snd.comp continuous_Kelley_forget)⟩
  have hR : IsClosed (show Set (Kelley (P × X)) from R) := cgwh_isClosed_equalizer (X := Kelley (P × X)) hX
    ⟨q ∘ Prod.fst, q.continuous.comp (continuous_fst.comp continuous_Kelley_forget)⟩
    ⟨Prod.snd, continuous_snd.comp continuous_Kelley_forget⟩
  have hB : IsClosed (show Set (Kelley (P × P)) from B) := cgwh_isClosed_equalizer (X := Kelley (P × P)) hX
    ⟨q ∘ Prod.fst, q.continuous.comp (continuous_fst.comp continuous_Kelley_forget)⟩
    ⟨q ∘ Prod.snd, q.continuous.comp (continuous_snd.comp continuous_Kelley_forget)⟩
  let E : Set (A × A) := D ∪ (Prod.map left right '' L ∪ (Prod.map right left '' R ∪ Prod.map right right '' B))
  have hE : IsClosed (show Set (Kelley (A × A)) from E) := hD.union (((kelleyProduct_closedEmbedding hl hr).isClosedMap L hL).union
    (((kelleyProduct_closedEmbedding hr hl).isClosedMap R hR).union
      ((kelleyProduct_closedEmbedding hr hr).isClosedMap B hB)))
  apply (weaklyHausdorff_quotient_iff_closed_relation A _).mpr
  convert hE using 1
  ext a
  obtain ⟨a, b⟩ := (show A × A from a)
  change glueSetoid p q a b ↔ (a, b) ∈ E
  rw [← Quotient.eq'']
  change (glueProjection p q a = glueProjection p q b) ↔ (a, b) ∈ E
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      change (glueLeft p q x = glueLeft p q y) ↔ _
      rw [(glueLeft_injective p q).eq_iff]
      simp [E, Set.mem_union, D, L, R, B, left, right, Set.mem_image, Prod.exists, Prod.map_apply]
      exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    | inr z =>
      change (glueLeft p q x = glueRight p q z) ↔ _
      rw [glueLeft_eq_glueRight p q hp.injective]
      simp [E, Set.mem_union, D, L, R, B, left, right, Set.mem_image, Prod.exists, Prod.map_apply, and_left_comm,
        and_comm]
      exact ⟨fun ⟨t, hx, hz⟩ => ⟨t, congrArg Sum.inl hx, congrArg Sum.inr hz⟩,
        fun ⟨t, hx, hz⟩ => ⟨t, Sum.inl.inj hx, Sum.inr.inj hz⟩⟩
  | inr z =>
    cases b with
    | inl x =>
      change (glueRight p q z = glueLeft p q x) ↔ _
      rw [eq_comm, glueLeft_eq_glueRight p q hp.injective]
      simp [E, Set.mem_union, D, L, R, B, left, right, Set.mem_image, Prod.exists, Prod.map_apply,
        and_left_comm, and_comm, eq_comm]
      exact ⟨fun ⟨t, hx, hz⟩ => ⟨t, congrArg Sum.inl hx, congrArg Sum.inr hz⟩,
        fun ⟨t, hx, hz⟩ => ⟨t, Sum.inl.inj hx, Sum.inr.inj hz⟩⟩
    | inr w =>
      change (glueRight p q z = glueRight p q w) ↔ _
      rw [glueRight_eq_glueRight p q hp.injective]
      simp [E, Set.mem_union, D, L, R, B, left, right, Set.mem_image, Prod.exists, Prod.map_apply,
        and_left_comm, and_comm]
      exact or_congr ⟨congrArg Sum.inr, Sum.inr.inj⟩
        ⟨fun ⟨t, s, h, ht, hs⟩ => ⟨t, s, h, congrArg Sum.inr ht, congrArg Sum.inr hs⟩,
          fun ⟨t, s, h, ht, hs⟩ => ⟨t, s, h, Sum.inr.inj ht, Sum.inr.inj hs⟩⟩

end

namespace CGWH

noncomputable section

variable {P X Z : CGWH.{u}} (p : P ⟶ Z) (q : P ⟶ X)

private abbrev pMap := p.hom.hom.hom
private abbrev qMap := q.hom.hom.hom

/-- The topological pushout of a closed inclusion is a CGWH space. -/
abbrev glueObject (hp : IsClosedEmbedding p.hom) : CGWH.{u} :=
  of (glueSpace_weaklyHausdorff (pMap p) (qMap q) X.property Z.property hp)

abbrev glueInl (hp : IsClosedEmbedding p.hom) : X ⟶ glueObject p q hp :=
  map (glueLeftMap (pMap p) (qMap q))

abbrev glueInr (hp : IsClosedEmbedding p.hom) : Z ⟶ glueObject p q hp :=
  map (glueRightMap (pMap p) (qMap q))

theorem glue_condition (hp : IsClosedEmbedding p.hom) :
    q ≫ glueInl p q hp = p ≫ glueInr p q hp := by
  exact ext_hom (glue_commutes (pMap p) (qMap q) hp.injective)

/-- E.2.3.10. The quotient computes the pushout in CGWH and its left
inclusion is closed. The ordinary pullback is homeomorphic to P. -/
def closedPushout (hp : IsClosedEmbedding p.hom) :
    IsColimit (PushoutCocone.mk (glueInl p q hp) (glueInr p q hp) (glue_condition p q hp)) := by
  refine PushoutCocone.IsColimit.mk _ (fun c => map
    (glueDesc (pMap p) (qMap q) hp.injective c.inl.hom.hom.hom c.inr.hom.hom.hom
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom c.condition)))) ?_ ?_ ?_
  · intro c
    exact ext_hom (fun _ => rfl)
  · intro c
    exact ext_hom (fun _ => rfl)
  · intro c f hL hR
    apply ext_hom
    exact congrFun (glue_ext (pMap p) (qMap q)
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hL))
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom hR)))

theorem glueInl_closedEmbedding (hp : IsClosedEmbedding p.hom) :
    IsClosedEmbedding (glueInl p q hp).hom :=
  glueLeft_closedEmbedding (pMap p) (qMap q) hp

def closedPushoutPullback (hp : IsClosedEmbedding p.hom) :
    LimitCone (cospan (glueInl p q hp) (glueInr p q hp)) :=
  topologicalPullbackOfClosedEmbedding _ _ (glueInl_closedEmbedding p q hp)

def closedPushoutHomeomorph (hp : IsClosedEmbedding p.hom) :
    P.obj ≃ₜ FibrePoints (glueInl p q hp) (glueInr p q hp) :=
  gluePullbackHomeomorph (pMap p) (qMap q) hp

end

end CGWH

/-- Even with a quotient q, distinct points of Z can become equal.
The Z–Z part of the pushout relation must include pairs above equal q-values. -/
theorem glueRelation_has_nondiagonal_right_pair :
    let p : C(Bool, Bool) := ContinuousMap.id Bool
    let q : C(Bool, Unit) := ContinuousMap.const Bool ()
    IsClosedEmbedding p ∧ IsQuotientMap q ∧
      (false : Bool) ≠ true ∧ glueRight p q false = glueRight p q true := by
  dsimp only
  have hp : IsClosedEmbedding (ContinuousMap.id Bool) := IsClosedEmbedding.id
  have hq : IsQuotientMap (ContinuousMap.const Bool ()) :=
    isQuotientMap_iff_isClosed.mpr ⟨fun x => ⟨false, Subsingleton.elim _ x⟩,
      fun S => iff_of_true (isClosed_discrete S) (isClosed_discrete ((ContinuousMap.const Bool ()) ⁻¹' S))⟩
  exact ⟨hp, hq, Bool.false_ne_true, (glueRight_eq_glueRight _ _ hp.injective _ _).mpr
    (Or.inr ⟨false, true, rfl, rfl, rfl⟩)⟩

end Masullo
