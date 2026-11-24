import LocallyConstantTests
import InductiveTensorTopology
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.Option

open Filter Function Set Topology
open scoped Classical BigOperators TensorProduct

namespace Masullo

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism transports the locally constant compactly supported tests. -/
def locallyConstantTestCongr (e : X ≃ₜ Y) : locallyConstantTests X ≃ₗ[ℂ] locallyConstantTests Y where
  toFun f := ⟨f.val ∘ e.symm, f.property.1.comp_continuous e.symm.continuous,
    f.property.2.comp_isClosedEmbedding e.symm.isClosedEmbedding⟩
  invFun g := ⟨g.val ∘ e, g.property.1.comp_continuous e.continuous,
    g.property.2.comp_isClosedEmbedding e.isClosedEmbedding⟩
  left_inv f := Subtype.ext (funext fun x => congrArg f.val (e.symm_apply_apply x))
  right_inv g := Subtype.ext (funext fun y => congrArg g.val (e.apply_symm_apply y))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem locallyConstantTestCongr_apply (e : X ≃ₜ Y) (f : locallyConstantTests X) (y : Y) :
    (locallyConstantTestCongr e f).val y = f.val (e.symm y) := rfl

@[simp] theorem locallyConstantTestCongr_symm_apply (e : X ≃ₜ Y)
    (g : locallyConstantTests Y) (x : X) :
    ((locallyConstantTestCongr e).symm g).val x = g.val (e x) := rfl

variable [T2Space X] [T2Space Y]

/-- The product of test functions on the two factors. -/
def locallyConstantTestProduct :
    locallyConstantTests X →ₗ[ℂ] locallyConstantTests Y →ₗ[ℂ] locallyConstantTests (X × Y) := by
  let B (f : locallyConstantTests X) (g : locallyConstantTests Y) :
      locallyConstantTests (X × Y) := by
    let w (p : X × Y) := f.val p.1 * g.val p.2
    refine ⟨w, (f.property.1.comp_continuous continuous_fst).mul
      (g.property.1.comp_continuous continuous_snd), ?_⟩
    apply HasCompactSupport.of_support_subset_isCompact (f.property.2.prod g.property.2)
    intro p hp
    exact ⟨subset_tsupport f.val (fun h => hp (show w p = 0 by simp [w, h])),
      subset_tsupport g.val (fun h => hp (show w p = 0 by simp [w, h]))⟩
  let L (f : locallyConstantTests X) : locallyConstantTests Y →ₗ[ℂ] locallyConstantTests (X × Y) :=
    { toFun := B f
      map_add' := fun g h => Subtype.ext (funext fun p => mul_add (f.val p.1) (g.val p.2) (h.val p.2))
      map_smul' := fun c g => Subtype.ext (funext fun p => mul_left_comm (f.val p.1) c (g.val p.2)) }
  refine { toFun := L, map_add' := ?_, map_smul' := ?_ }
  · intro f g
    apply LinearMap.ext
    intro h
    exact Subtype.ext (funext fun p => add_mul (f.val p.1) (g.val p.1) (h.val p.2))
  · intro c f
    apply LinearMap.ext
    intro g
    exact Subtype.ext (funext fun p => mul_assoc c (f.val p.1) (g.val p.2))

@[simp] theorem locallyConstantTestProduct_apply (f : locallyConstantTests X)
    (g : locallyConstantTests Y) (p : X × Y) :
    (locallyConstantTestProduct f g).val p = f.val p.1 * g.val p.2 := rfl


/-- A section of a test function on a product, in the first variable. -/
def locallyConstantTestSection (f : locallyConstantTests (X × Y)) (y : Y) :
    locallyConstantTests X := by
  let e (x : X) := (x, y)
  have he : IsClosedEmbedding e := by
    refine ⟨isEmbedding_prodMkLeft y, ?_⟩
    have h : range e = (univ : Set X) ×ˢ {y} := by
      ext p
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨mem_univ _, mem_singleton _⟩
      · rintro ⟨_, hp⟩
        exact ⟨p.1, Prod.ext rfl (mem_singleton_iff.mp hp).symm⟩
    rw [h]
    exact isClosed_univ.prod isClosed_singleton
  exact ⟨f.val ∘ e, f.property.1.comp_continuous (continuous_id.prodMk continuous_const),
    f.property.2.comp_isClosedEmbedding he⟩

omit [T2Space X] in
@[simp] theorem locallyConstantTestSection_apply (f : locallyConstantTests (X × Y))
    (y : Y) (x : X) : (locallyConstantTestSection f y).val x = f.val (x, y) := rfl

omit [T2Space X] in
theorem locallyConstantTestSection_locallyConstant (f : locallyConstantTests (X × Y)) :
    IsLocallyConstant (locallyConstantTestSection f) := by
  let C := Prod.fst '' tsupport f.val
  have hC : IsCompact C := f.property.2.image continuous_fst
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  have ht (x : X) (_ : x ∈ C) : ∀ᶠ q : Y × X in 𝓝 (y, x), f.val (q.2, q.1) = f.val (x, y) :=
    (f.property.1.comp_continuous (continuous_snd.prodMk continuous_fst)).eventually_eq (y, x)
  have hloc (x : X) (hx : x ∈ C) : ∀ᶠ q : Y × X in 𝓝 (y, x),
      f.val (q.2, q.1) = f.val (q.2, y) := by
    have h₂ : ∀ᶠ q : Y × X in 𝓝 (y, x), f.val (q.2, y) = f.val (x, y) :=
      (f.property.1.comp_continuous (continuous_snd.prodMk continuous_const)).eventually_eq (y, x)
    filter_upwards [ht x hx, h₂] with q hq hq₂
    exact hq.trans hq₂.symm
  filter_upwards [hC.eventually_forall_of_forall_eventually (P := fun z x => f.val (x,z) = f.val (x,y)) hloc] with z hz
  apply Subtype.ext
  funext x
  change f.val (x, z) = f.val (x, y)
  by_cases hx : x ∈ C
  · exact hz x hx
  · have hzero (t : Y) : f.val (x, t) = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx ⟨(x,t), ht, rfl⟩)
    rw [hzero, hzero]

omit [T2Space X] in
theorem locallyConstantTestSection_range_finite (f : locallyConstantTests (X × Y)) :
    (range (locallyConstantTestSection f)).Finite := by
  let C := Prod.snd '' tsupport f.val
  letI : CompactSpace C := isCompact_iff_compactSpace.mp (f.property.2.image continuous_snd)
  have hr := ((locallyConstantTestSection_locallyConstant f).comp_continuous
    (continuous_subtype_val : Continuous ((↑) : C → Y))).range_finite
  refine (hr.insert (0 : locallyConstantTests X)).subset ?_
  rintro _ ⟨y, rfl⟩
  by_cases hy : y ∈ C
  · exact mem_insert_of_mem _ ⟨⟨y, hy⟩, rfl⟩
  · have hzero : locallyConstantTestSection f y = 0 := Subtype.ext (funext fun x =>
      show f.val (x,y) = 0 from image_eq_zero_of_notMem_tsupport
        (fun ht => hy ⟨(x,y), ht, rfl⟩))
    rw [hzero]
    exact mem_insert _ _


private def testSectionFiber (f : locallyConstantTests (X × Y))
    (g : locallyConstantTests X) (hg : g ≠ 0) : locallyConstantTests Y := by
  let C := Prod.snd '' tsupport f.val
  let s := {y | locallyConstantTestSection f y = g}
  have hs := (locallyConstantTestSection_locallyConstant f).isClopen_fiber g
  have hc : IsCompact C := f.property.2.image continuous_snd
  have hsubset : s ⊆ C := by
    intro y hy
    by_contra hn
    apply hg
    rw [← hy]
    exact Subtype.ext (funext fun x =>
      show f.val (x,y) = 0 from image_eq_zero_of_notMem_tsupport
        (fun ht => hn ⟨(x,y), ht, rfl⟩))
  exact compactOpenIndicator Y ⟨s, hc.of_isClosed_subset hs.1 hsubset, hs.2⟩

omit [T2Space X] in
private theorem testSectionFiber_apply (f : locallyConstantTests (X × Y))
    (g : locallyConstantTests X) (hg : g ≠ 0) (y : Y) :
    (testSectionFiber f g hg).val y =
      if locallyConstantTestSection f y = g then 1 else 0 := by
  classical
  change ({t | locallyConstantTestSection f t = g} : Set Y).indicator (fun _ => (1 : ℂ)) y = _
  rw [Set.indicator_apply]
  rfl

/-- When a product test is constant along a relation on its second coordinate,
its finite decomposition into pure products can use second factors that
are constant along the same relation. -/
theorem locallyConstantTest_mem_span_product_of_invariant
    (r : Y → Y → Prop) (f : locallyConstantTests (X × Y))
    (hf : ∀ x y z, r y z → f.val (x,y) = f.val (x,z)) :
    f ∈ Submodule.span ℂ {p | ∃ (a : locallyConstantTests X) (b : locallyConstantTests Y),
      (∀ y z, r y z → b.val y = b.val z) ∧ locallyConstantTestProduct a b = p} := by
  classical
  let s := (locallyConstantTestSection_range_finite f).toFinset.filter (· ≠ 0)
  let g (u : s) := testSectionFiber f u.val (Finset.mem_filter.mp u.property).2
  have hsum : (∑ u : s, locallyConstantTestProduct u.val (g u)) = f := by
    apply Subtype.ext
    funext p
    simp only [Submodule.coe_sum, Finset.sum_apply,
      locallyConstantTestProduct_apply]
    simp_rw [g, testSectionFiber_apply]
    by_cases hp : locallyConstantTestSection f p.2 = 0
    · have hne (u : s) : locallyConstantTestSection f p.2 ≠ u.val := by
        rw [hp]
        exact (Finset.mem_filter.mp u.property).2.symm
      simp only [hne, ite_false, mul_zero, Finset.sum_const_zero]
      exact (congrArg (fun u : locallyConstantTests X => u.val p.1) hp).symm
    · let u : s := ⟨locallyConstantTestSection f p.2, Finset.mem_filter.mpr
        ⟨(locallyConstantTestSection_range_finite f).mem_toFinset.mpr (mem_range_self _), hp⟩⟩
      rw [Finset.sum_eq_single u]
      · simp [u]
      · intro a _ ha
        have hne : locallyConstantTestSection f p.2 ≠ a.val :=
          fun h => ha (Subtype.ext h.symm)
        rw [ite_eq_right hne, mul_zero]
      · simp
  rw [← hsum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.subset_span
  refine ⟨a.val, g a, ?_, rfl⟩
  intro y z hr
  have he : locallyConstantTestSection f y = locallyConstantTestSection f z :=
    Subtype.ext (funext fun x ↦ hf x y z hr)
  simp only [g, testSectionFiber_apply, he]

private theorem locallyConstantTestProduct_lift_surjective :
    Surjective (TensorProduct.lift (locallyConstantTestProduct (X := X) (Y := Y))) := by
  intro f
  change f ∈ (TensorProduct.lift (locallyConstantTestProduct (X := X) (Y := Y))).range
  apply (Submodule.span_le.mpr ?_) (locallyConstantTest_mem_span_product_of_invariant
    (fun _ _ ↦ False) f (fun _ _ _ h ↦ h.elim))
  rintro _ ⟨a,b,_,rfl⟩
  exact ⟨a ⊗ₜ[ℂ] b, TensorProduct.lift.tmul _ _⟩

omit [T2Space X] in
/-- Taking a section at a fixed second coordinate is linear. -/
def locallyConstantTestSectionMap (y : Y) :
    locallyConstantTests (X × Y) →ₗ[ℂ] locallyConstantTests X where
  toFun f := locallyConstantTestSection f y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem locallyConstantTestProduct_lift_injective :
    Injective (TensorProduct.lift (locallyConstantTestProduct (X := X) (Y := Y))) := by
  let A := locallyConstantTests X
  let B := locallyConstantTests Y
  let L := TensorProduct.lift (locallyConstantTestProduct (X := X) (Y := Y))
  let b := Module.Free.chooseBasis ℂ A
  let e := TensorProduct.equivFinsuppOfBasisLeft b (N := B)
  have hcoeff (i : Module.Free.ChooseBasisIndex ℂ A) (y : Y) (u : A ⊗[ℂ] B) :
      (e u i).val y = b.coord i (locallyConstantTestSectionMap y (L u)) := by
    induction u using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, map_zero, map_zero]
      rfl
    | tmul a c =>
      change (TensorProduct.equivFinsuppOfBasisLeft b (a ⊗ₜ[ℂ] c) i).val y =
        b.coord i (locallyConstantTestSectionMap y (L (a ⊗ₜ[ℂ] c)))
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      have h : locallyConstantTestSectionMap y (L (a ⊗ₜ[ℂ] c)) = c.val y • a := by
        change locallyConstantTestSectionMap y ((TensorProduct.lift locallyConstantTestProduct)
          (a ⊗ₜ[ℂ] c)) = _
        rw [TensorProduct.lift.tmul]
        exact Subtype.ext (funext fun x => mul_comm _ _)
      rw [h, map_smul, b.coord_apply]
      exact mul_comm _ _
    | add a c ha hc =>
      simp only [map_add, Finsupp.add_apply, Submodule.coe_add, Pi.add_apply, ha, hc]
  intro u v huv
  apply e.injective
  ext i : 1
  apply Subtype.ext
  funext y
  rw [hcoeff, hcoeff, huv]

/-- The actual product test space is the algebraic tensor of the two test spaces. -/
def locallyConstantTestProductEquiv :
    (locallyConstantTests X ⊗[ℂ] locallyConstantTests Y) ≃ₗ[ℂ] locallyConstantTests (X × Y) :=
  LinearEquiv.ofBijective (TensorProduct.lift locallyConstantTestProduct)
    ⟨locallyConstantTestProduct_lift_injective, locallyConstantTestProduct_lift_surjective⟩

@[simp] theorem locallyConstantTestProductEquiv_tmul (f : locallyConstantTests X)
    (g : locallyConstantTests Y) :
    locallyConstantTestProductEquiv (f ⊗ₜ[ℂ] g) = locallyConstantTestProduct f g :=
  TensorProduct.lift.tmul _ _

/-- The product test space with its finest topology realizes the
inductive tensor product of the two finest test spaces. -/
def locallyConstantTestProductContinuousEquiv :
    let A := locallyConstantTests X
    let B := locallyConstantTests Y
    letI : TopologicalSpace A := finestLocallyConvexTopology A
    letI : TopologicalSpace B := finestLocallyConvexTopology B
    letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
    letI : TopologicalSpace (locallyConstantTests (X × Y)) := finestLocallyConvexTopology _
    (A ⊗[ℂ] B) ≃L[ℂ] locallyConstantTests (X × Y) := by
  let A := locallyConstantTests X
  let B := locallyConstantTests Y
  let C := locallyConstantTests (X × Y)
  letI : TopologicalSpace A := finestLocallyConvexTopology A
  letI : TopologicalSpace B := finestLocallyConvexTopology B
  letI : TopologicalSpace C := finestLocallyConvexTopology C
  letI : TopologicalSpace (A ⊗[ℂ] B) := inductiveTensorTopology A B
  letI : IsTopologicalAddGroup A := (finest_withSeminorms A).topologicalAddGroup
  letI : IsTopologicalAddGroup B := (finest_withSeminorms B).topologicalAddGroup
  letI : PolynormableSpace ℂ C := (finest_withSeminorms C).toPolynormableSpace
  letI : PolynormableSpace ℂ (A ⊗[ℂ] B) :=
    (inductiveTensor_withSeminorms (E := A) (F := B)).toPolynormableSpace
  refine ⟨locallyConstantTestProductEquiv, ?_, ?_⟩
  · change Continuous (TensorProduct.lift (locallyConstantTestProduct (X := X) (Y := Y)))
    refine (continuous_inductiveTensor_lift_iff locallyConstantTestProduct).mpr ⟨?_, ?_⟩
    · intro g
      exact finest_linear_continuous (locallyConstantTestProduct.flip g)
    · intro f
      exact finest_linear_continuous (locallyConstantTestProduct f)
  · exact finest_linear_continuous (E := C) (F := A ⊗[ℂ] B)
      (locallyConstantTestProductEquiv (X := X) (Y := Y)).symm.toLinearMap

/-- The tensor lift of an endomorphism on the first factor of a product of test spaces. -/
def locallyConstantTestMapFirst (L : locallyConstantTests X →ₗ[ℂ] locallyConstantTests X) :
    locallyConstantTests (X × Y) →ₗ[ℂ] locallyConstantTests (X × Y) :=
  locallyConstantTestProductEquiv.toLinearMap.comp
    ((TensorProduct.map L LinearMap.id).comp locallyConstantTestProductEquiv.symm.toLinearMap)

@[simp] theorem locallyConstantTestMapFirst_product
    (L : locallyConstantTests X →ₗ[ℂ] locallyConstantTests X) (f : locallyConstantTests X)
    (g : locallyConstantTests Y) :
    locallyConstantTestMapFirst L (locallyConstantTestProduct f g) =
      locallyConstantTestProduct (L f) g := by
  have he : locallyConstantTestProductEquiv.symm (locallyConstantTestProduct f g) = f ⊗ₜ[ℂ] g := by
    apply locallyConstantTestProductEquiv.injective
    rw [LinearEquiv.apply_symm_apply, locallyConstantTestProductEquiv_tmul]
  change locallyConstantTestProductEquiv ((TensorProduct.map L LinearMap.id)
    (locallyConstantTestProductEquiv.symm (locallyConstantTestProduct f g))) = _
  rw [he, TensorProduct.map_tmul, LinearMap.id_apply, locallyConstantTestProductEquiv_tmul]

/-- Tensor lifting acts on every section, so the result does not depend on a chosen
expansion into pure products. -/
theorem locallyConstantTestMapFirst_section
    (L : locallyConstantTests X →ₗ[ℂ] locallyConstantTests X) (f : locallyConstantTests (X × Y))
    (y : Y) :
    locallyConstantTestSection (locallyConstantTestMapFirst L f) y =
      L (locallyConstantTestSection f y) := by
  let sectionAt := locallyConstantTestSectionMap (X := X) y
  change sectionAt (locallyConstantTestMapFirst L f) = L (sectionAt f)
  obtain ⟨t, rfl⟩ := locallyConstantTestProductEquiv.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [locallyConstantTestProductEquiv_tmul, locallyConstantTestMapFirst_product]
    have hs (a : locallyConstantTests X) : sectionAt (locallyConstantTestProduct a b) =
        b.val y • a := Subtype.ext (funext fun x => mul_comm _ _)
    rw [hs, hs, map_smul]
  | add a b ha hb => simp only [map_add, ha, hb]


universe u v

section FiniteProduct

variable {ι : Type u} [Fintype ι] {X : ι → Type v}
  [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]

/-- The coordinatewise product of finitely many compactly supported locally
constant functions is itself a compactly supported locally constant test. -/
def locallyConstantTestPiProduct (f : ∀ i, locallyConstantTests (X i)) :
    locallyConstantTests (∀ i, X i) := by
  refine ⟨fun x => ∏ i, (f i).val (x i), ?_, ?_⟩
  · let g (i : ι) : LocallyConstant (∀ i, X i) ℂ :=
      ⟨fun x => (f i).val (x i), (f i).property.1.comp_continuous (continuous_apply i)⟩
    exact (LocallyConstant.unflip g).isLocallyConstant.comp fun y => ∏ i, y i
  · apply HasCompactSupport.of_support_subset_isCompact
    · exact isCompact_univ_pi fun i => (f i).property.2
    · intro x hx i _
      apply subset_closure
      change (f i).val (x i) ≠ 0
      intro h
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h)

@[simp] theorem locallyConstantTestPiProduct_apply (f : ∀ i, locallyConstantTests (X i))
    (x : ∀ i, X i) :
    (locallyConstantTestPiProduct f).val x = ∏ i, (f i).val (x i) := rfl

private def finiteTestPiOptionHomeomorph {ι : Type u} (X : Option ι → Type v)
    [∀ i, TopologicalSpace (X i)] :
    (∀ i, X i) ≃ₜ X none × (∀ i : ι, X (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  continuous_toFun := (continuous_apply none).prodMk
    (continuous_pi fun i => continuous_apply (some i))
  continuous_invFun := continuous_pi fun i => by
    cases i with
    | none => exact continuous_fst
    | some i => exact (continuous_apply i).comp continuous_snd

/-- Coordinatewise pure tests span the entire test space on any finite product.
In particular, locally constant tests with coupled coordinates are finite
linear combinations of separated tests. -/
theorem locallyConstantTest_span_piProduct :
    Submodule.span ℂ (Set.range (locallyConstantTestPiProduct (X := X))) = ⊤ := by
  classical
  refine Fintype.induction_empty_option
    (P := fun (I : Type u) (_ : Fintype I) =>
      ∀ (Y : I → Type v) [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)],
        Submodule.span ℂ (Set.range (locallyConstantTestPiProduct (X := Y))) = ⊤)
    ?_ ?_ ?_ ι X
  · intro α β _ e ih X _ _
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let Y : α → Type v := fun i => X (e i)
    let E : (∀ i, Y i) ≃ₜ (∀ i, X i) := Homeomorph.piCongrLeft e
    let L := locallyConstantTestCongr E
    let Q := Submodule.span ℂ (Set.range (locallyConstantTestPiProduct (X := X)))
    have hgen (f : ∀ i, locallyConstantTests (Y i)) :
        L (locallyConstantTestPiProduct f) ∈ Q := by
      let g : ∀ j : β, locallyConstantTests (X j) :=
        Equiv.piCongrLeft (fun j => locallyConstantTests (X j)) e f
      have heq : L (locallyConstantTestPiProduct f) = locallyConstantTestPiProduct g := by
        apply Subtype.ext
        funext x
        change ∏ i, (f i).val (x (e i)) = ∏ j, (g j).val (x j)
        symm
        rw [← e.prod_comp]
        apply Finset.prod_congr rfl
        intro i _
        rw [show g (e i) = f i from Equiv.piCongrLeft_apply_apply ..]
      rw [heq]
      exact Submodule.subset_span ⟨g, rfl⟩
    have hs : Submodule.span ℂ (Set.range (locallyConstantTestPiProduct (X := Y))) ≤
        Q.comap L.toLinearMap := Submodule.span_le.mpr (by rintro _ ⟨f, rfl⟩; exact hgen f)
    rw [ih Y] at hs
    apply top_unique
    intro f _
    have h := hs (show L.symm f ∈ (⊤ : Submodule ℂ (locallyConstantTests (∀ i, Y i))) from trivial)
    change L (L.symm f) ∈ Q at h
    rwa [L.apply_symm_apply] at h
  · intro X _ _
    let g : ∀ i : PEmpty, locallyConstantTests (X i) := fun i => nomatch i
    let x : ∀ i : PEmpty, X i := fun i => nomatch i
    apply Submodule.eq_top_iff'.mpr
    intro f
    have he : f = f.val x • locallyConstantTestPiProduct g := by
      apply Subtype.ext
      funext y
      have hy : x = y := funext fun i => nomatch i
      rw [← hy]
      change f.val x = f.val x * (∏ i : PEmpty, (g i).val (x i))
      simp
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · intro α _ ih X _ _
    let E := finiteTestPiOptionHomeomorph X
    let L := (locallyConstantTestCongr E).symm
    let Q := Submodule.span ℂ (Set.range (locallyConstantTestPiProduct (X := X)))
    have hpure (u : locallyConstantTests (X none))
        (v : ∀ i : α, locallyConstantTests (X (some i))) :
        L (locallyConstantTestProduct u (locallyConstantTestPiProduct v)) ∈ Q := by
      let g : ∀ i, locallyConstantTests (X i) := fun i => Option.casesOn i u v
      have he : L (locallyConstantTestProduct u (locallyConstantTestPiProduct v)) =
          locallyConstantTestPiProduct g := by
        apply Subtype.ext
        funext x
        change u.val (x none) * (∏ i : α, (v i).val (x (some i))) = ∏ i : Option α, (g i).val (x i)
        rw [Fintype.prod_option]
      rw [he]
      exact Submodule.subset_span ⟨g, rfl⟩
    have hp (u : locallyConstantTests (X none)) (v : locallyConstantTests (∀ i : α, X (some i))) :
        L (locallyConstantTestProduct u v) ∈ Q := by
      let M := L.toLinearMap.comp (locallyConstantTestProduct u)
      have hs : Submodule.span ℂ (Set.range (locallyConstantTestPiProduct
          (X := fun i : α => X (some i)))) ≤ Q.comap M :=
        Submodule.span_le.mpr (by rintro _ ⟨f, rfl⟩; exact hpure u f)
      rw [ih (fun i : α => X (some i))] at hs
      exact hs (show v ∈ (⊤ : Submodule ℂ _) from trivial)
    apply Submodule.eq_top_iff'.mpr
    intro f
    let T := L.toLinearMap.comp locallyConstantTestProductEquiv.toLinearMap
    obtain ⟨t, rfl⟩ : ∃ t, T t = f :=
      (L.surjective.comp locallyConstantTestProductEquiv.surjective) f
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Q.zero_mem
    | tmul u v => exact hp u v
    | add a b ha hb => rw [map_add]; exact Q.add_mem ha hb

end FiniteProduct

end
end Masullo
