import BergmanDifference
import ModulatedExponentialRadial
import StrictLimitQuotients

open Filter Function Set Topology TopologicalSpace
open scoped SchwartzMap

noncomputable section

universe u

namespace Masullo

section Quotient

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- Cancelling a closed embedding before taking a quotient gives the
canonical continuous linear equivalence onto the quotient of its image. -/
private theorem differenceImageQuotient (A P : V →L[ℂ] V) (hA : IsClosedEmbedding A) :
    let M := (A.comp P).range.comap A.range.subtype
    ∃ e : (V ⧸ P.range) ≃L[ℂ] (A.range ⧸ M), ∀ f,
      e (P.range.mkQ f) = M.mkQ ⟨A f, ⟨f, rfl⟩⟩ := by
  dsimp only
  let M := (A.comp P).range.comap A.range.subtype
  let e₀ := LinearEquiv.ofInjective A.toLinearMap hA.injective
  have he₀ (v : V) : (e₀ v : V) = A v := rfl
  have hsymm : Continuous e₀.symm := hA.isEmbedding.isInducing.continuous_iff.mpr <|
    continuous_subtype_val.congr fun v ↦
      (congrArg Subtype.val (e₀.apply_symm_apply v)).symm
  let e : V ≃L[ℂ] A.range := ⟨e₀, A.continuous.subtype_mk _, hsymm⟩
  have hmem (f : V) : e f ∈ M ↔ f ∈ P.range := by
    change (∃ g, A (P g) = A f) ↔ ∃ g, P g = f
    exact exists_congr fun _ ↦ hA.injective.eq_iff
  let F := P.range.liftQL (M.mkQL.comp e.toContinuousLinearMap) (fun f hf ↦
    (Submodule.Quotient.mk_eq_zero M).mpr ((hmem f).mpr hf))
  let J := M.liftQL (P.range.mkQL.comp e.symm.toContinuousLinearMap) (fun u hu ↦ by
    apply (Submodule.Quotient.mk_eq_zero P.range).mpr
    exact (hmem (e.symm u)).mp ((e.apply_symm_apply u).symm ▸ hu))
  refine ⟨ContinuousLinearEquiv.equivOfInverse F J ?_ ?_, fun _ ↦ rfl⟩
  · intro u
    obtain ⟨x, rfl⟩ := P.range.mkQ_surjective u
    change P.range.mkQ (e.symm (e x)) = P.range.mkQ x
    rw [e.symm_apply_apply]
  · intro u
    obtain ⟨x, rfl⟩ := M.mkQ_surjective u
    change M.mkQ (e (e.symm x)) = M.mkQ x
    rw [e.apply_symm_apply]

private theorem quotientStructure {Y : Type u} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [SeparableSpace Y] (hY : IsFrechetTVS Y) (hN : NuclearLocallyConvex.{u,u} Y)
    (M : Submodule ℂ Y) (hM : IsClosed (M : Set Y)) :
    SeparableSpace (Y ⧸ M) ∧ NuclearLocallyConvex.{u,u} (Y ⧸ M) ∧ IsFrechetTVS (Y ⧸ M) :=
  ⟨M.mkQ_surjective.denseRange.separableSpace M.continuous_mkQ,
    nuclearLocallyConvex_quotient hN M hM, isFrechetTVS_closedQuotient hY M hM⟩

private theorem frechet_of_linearEquiv {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] (hY : IsFrechetTVS Y) (e : Y ≃L[ℂ] Z) :
    IsFrechetTVS Z := by
  obtain ⟨hadd, hpoly, hm, hc⟩ := hY
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace Z := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup Z := isUniformAddGroup_of_addCommGroup
  exact ⟨inferInstance, (e.symm.toHomeomorph.isInducing.withSeminorms
    (f := e.symm.toLinearMap) (PolynormableSpace.withSeminorms ℂ Y)).toPolynormableSpace,
    e.symm.toHomeomorph.isEmbedding.metrizableSpace,
    (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp hc⟩

end Quotient

section Difference

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G)
  (hτ : ∀ t, m (τ t) = t) (w : PontryaginDual m.toMonoidHom.ker)
  (hm : IsProperMap m)

local notation "I" => (Set.univ : Set ℝ)
local notation "E" => ModulatedExponentialInductive m I
local notation "H" => modulatedDecayIsotype m w I
local notation "X" => PositiveRealExponentialDecay (Set.univ : Set ℝ)
local notation "χ" => extendModulatedCharacter m τ hτ w

private theorem univ_nonempty_real : (Set.univ : Set ℝ).Nonempty := ⟨0, mem_univ _⟩

/-- The joint left action restricts to the exponential Schwartz isotype. -/
def exponentialIsotypeTranslation (g : G) : H →L[ℂ] H := by
  let T := ModulatedExponentialInductive.translate m I g
  have hT : Continuous T :=
    (ModulatedExponentialInductive.continuous_translate m I hm (fun t ↦ ⟨τ t, hτ t⟩)
      univ_nonempty_real).comp (continuous_const.prodMk continuous_id)
  refine (⟨T, hT⟩ : E →L[ℂ] E).restrict fun f hf k x ↦ ?_
  change (T f).val (k.val⁻¹ * x) = (w k : ℂ) * (T f).val x
  rw [ModulatedExponentialInductive.translate_apply, ModulatedExponentialInductive.translate_apply,
    ← mul_assoc, mul_comm g⁻¹ _, mul_assoc]
  exact hf k (g⁻¹ * x)

@[simp] theorem exponentialIsotypeTranslation_apply (g : G) (f : H) (x : G) :
    (exponentialIsotypeTranslation m τ hτ w hm g f : E).val x = f.val.val (g⁻¹ * x) := rfl

local instance : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul

local instance : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul

local instance : IsTopologicalAddGroup E :=
  (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup

def exponentialIsotypeDifference (g : G) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - exponentialIsotypeTranslation m τ hτ w hm g⁻¹

private theorem isotypeDifference_apply (g : G) (f : H) (x : G) :
    (exponentialIsotypeDifference m τ hτ w hm g f : E).val x =
      f.val.val x - f.val.val (g * x) := by
  change f.val.val x - f.val.val (g⁻¹⁻¹ * x) = _
  rw [inv_inv]

private theorem isotypeDifference_isClosedEmbedding (g : G) (hg : 0 < (m g).toAdd) :
    IsClosedEmbedding (exponentialIsotypeDifference m τ hτ w hm g) := by
  obtain ⟨e, he, _⟩ := exists_modulatedExponentialRadialIsotype m τ hτ w hm
  let d := (m g).toAdd
  let c : Circle := (χ g)⁻¹
  let D := ContinuousLinearMap.id ℂ X - (c : ℂ) • exponentialSchwartzTranslation d
  have hD : IsClosedEmbedding D := exponentialSchwartzDifference_isClosedEmbedding d hg c
  have hconj (f : X) : exponentialIsotypeDifference m τ hτ w hm g (e f) = e (D f) := by
    apply Subtype.ext
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext x
    change (exponentialIsotypeDifference m τ hτ w hm g (e f) : E).val x = (e (D f) : E).val x
    rw [isotypeDifference_apply, he, he, he, map_mul m, map_mul (χ), mul_inv_rev, Circle.coe_mul]
    change f.val (m x).toAdd * (((χ x)⁻¹ : Circle) : ℂ) -
      f.val (d + (m x).toAdd) * ((((χ x)⁻¹ : Circle) : ℂ) * (c : ℂ)) =
      (f.val (m x).toAdd - (c : ℂ) * f.val ((m x).toAdd + d)) * (((χ x)⁻¹ : Circle) : ℂ)
    rw [add_comm d]
    ring
  have hEq : (exponentialIsotypeDifference m τ hτ w hm g : H → H) = e ∘ D ∘ e.symm :=
    funext fun v ↦ by simpa only [comp_apply, e.apply_symm_apply] using hconj (e.symm v)
  rw [hEq]
  exact e.toHomeomorph.isClosedEmbedding.comp (hD.comp e.symm.toHomeomorph.isClosedEmbedding)

/-- Cyclic differences composed in the indicated order, retaining multiplicity. -/
def exponentialIsotypeDifferenceProduct : List G → H →L[ℂ] H
  | [] => ContinuousLinearMap.id ℂ H
  | g :: gs => (exponentialIsotypeDifference m τ hτ w hm g).comp
    (exponentialIsotypeDifferenceProduct gs)

theorem exponentialIsotypeDifferenceProduct_isClosedEmbedding (gs : List G)
    (hg : ∀ g ∈ gs, 0 < (m g).toAdd) :
    IsClosedEmbedding (exponentialIsotypeDifferenceProduct m τ hτ w hm gs) := by
  induction gs with
  | nil => exact IsClosedEmbedding.id
  | cons g gs ih =>
    exact (isotypeDifference_isClosedEmbedding m τ hτ w hm g (hg g (.head _))).comp
      (ih fun a ha ↦ hg a (.tail _ ha))


private theorem isotype_ext {a b : H} (h : ∀ x, a.val.val x = b.val.val x) : a = b :=
  Subtype.ext (ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext (funext h)))

private theorem isotypeTranslate_product_commute (g : G) (gs : List G) (f : H) :
    exponentialIsotypeTranslation m τ hτ w hm g (exponentialIsotypeDifferenceProduct m τ hτ w hm gs f) =
      exponentialIsotypeDifferenceProduct m τ hτ w hm gs (exponentialIsotypeTranslation m τ hτ w hm g f) := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    let D := exponentialIsotypeDifference m τ hτ w hm a
    let P := exponentialIsotypeDifferenceProduct m τ hτ w hm gs
    let T := exponentialIsotypeTranslation m τ hτ w hm g
    change T (D (P f)) = D (P (T f))
    rw [← ih]
    apply isotype_ext m w
    intro x
    change (T (D (P f))).val.val x = (D (T (P f))).val.val x
    simp only [T, D, exponentialIsotypeTranslation_apply, isotypeDifference_apply]
    rw [← mul_assoc, mul_comm a g⁻¹, mul_assoc]

/-- The list product convention agrees with moving a last factor to the
front of a cyclic difference product, since all the translations commute. -/
theorem exponentialIsotypeDifferenceProduct_append_single (gs : List G) (g : G) :
    exponentialIsotypeDifferenceProduct m τ hτ w hm (gs ++ [g]) =
      (exponentialIsotypeDifference m τ hτ w hm g).comp
        (exponentialIsotypeDifferenceProduct m τ hτ w hm gs) := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    rw [List.cons_append, exponentialIsotypeDifferenceProduct, ih, exponentialIsotypeDifferenceProduct]
    apply ContinuousLinearMap.ext
    intro f
    let v := exponentialIsotypeDifferenceProduct m τ hτ w hm gs f
    change exponentialIsotypeDifference m τ hτ w hm a
      (exponentialIsotypeDifference m τ hτ w hm g v) =
      exponentialIsotypeDifference m τ hτ w hm g (exponentialIsotypeDifference m τ hτ w hm a v)
    apply isotype_ext m w
    intro x
    simp only [isotypeDifference_apply]
    rw [mul_left_comm]
    abel

include hτ hm in
private theorem exponentialIsotype_structure :
    SeparableSpace H ∧ NuclearLocallyConvex.{u,u} H ∧ IsFrechetTVS H := by
  obtain ⟨e, _, _⟩ := exists_modulatedExponentialRadialIsotype m τ hτ w hm
  let L := positiveRealFourierMellin I isOpen_univ ordConnected_univ univ_nonempty_real
  haveI : SeparableSpace (SchwartzBergman I) :=
    schwartzBergman_separable I isOpen_univ ordConnected_univ univ_nonempty_real
  haveI : SeparableSpace X := L.symm.surjective.denseRange.separableSpace L.symm.continuous
  exact ⟨e.surjective.denseRange.separableSpace e.continuous,
    nuclearLocallyConvex_of_equiv e (positiveRealExponentialDecay_nuclear I univ_nonempty_real),
    frechet_of_linearEquiv (positiveRealExponentialDecay_frechet I ordConnected_univ univ_nonempty_real) e⟩

/-- Lemma 4.6.1.3(1)–(2). Every list of expanding shifts has closed
difference-product range, with a separable nuclear Fréchet quotient. -/
theorem exponentialIsotypeDifferenceProduct_quotient (gs : List G)
    (hg : ∀ g ∈ gs, 0 < (m g).toAdd) :
    let R := (exponentialIsotypeDifferenceProduct m τ hτ w hm gs).range
    IsClosed (R : Set H) ∧ SeparableSpace (H ⧸ R) ∧
      NuclearLocallyConvex.{u,u} (H ⧸ R) ∧ IsFrechetTVS (H ⧸ R) := by
  dsimp only
  obtain ⟨hs, hn, hf⟩ := exponentialIsotype_structure m τ hτ w hm
  letI : SeparableSpace H := hs
  have hc := (exponentialIsotypeDifferenceProduct_isClosedEmbedding m τ hτ w hm gs hg).isClosed_range
  exact ⟨hc, quotientStructure hf hn _ hc⟩

/-- The last-factor quotient equivalence, its Fréchet structure, and
the compatible continuous actions on both quotients. -/
def HasCyclicDifferenceQuotient {V L : Type u} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [TopologicalSpace L]
    (A P : V →L[ℂ] V) (M : Submodule ℂ A.range) (T : L → V →L[ℂ] V) : Prop :=
  ∃ e : (V ⧸ P.range) ≃L[ℂ] (A.range ⧸ M),
    (∀ f : V, e (P.range.mkQ f) = M.mkQ ⟨A f, ⟨f, rfl⟩⟩) ∧
    SeparableSpace (A.range ⧸ M) ∧ NuclearLocallyConvex.{u,u} (A.range ⧸ M) ∧
    IsFrechetTVS (A.range ⧸ M) ∧
    ∃ (r : L × (V ⧸ P.range) → V ⧸ P.range) (s : L × (A.range ⧸ M) → A.range ⧸ M),
      Continuous r ∧ Continuous s ∧
      (∀ a (f : V), r (a, P.range.mkQ f) = P.range.mkQ (T a f)) ∧
      (∀ a (v : A.range), ∃ v' : A.range, v'.val = T a v.val ∧
        s (a, M.mkQ v) = M.mkQ v') ∧
      ∀ a y, e (r (a, y)) = s (a, e y)

private theorem cyclicDifferenceQuotient_of_closedEmbedding {V L : Type u} [AddCommGroup V]
    [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace L]
    (A P : V →L[ℂ] V) (hA : IsClosedEmbedding A) (T : L → V →L[ℂ] V)
    (hT : Continuous (fun p : L × V ↦ T p.1 p.2))
    (hAP : ∀ a f, T a (A f) = A (T a f))
    (hP : ∀ a f, T a (P f) = P (T a f))
    (hs : SeparableSpace (V ⧸ P.range)) (hn : NuclearLocallyConvex.{u,u} (V ⧸ P.range))
    (hf : IsFrechetTVS (V ⧸ P.range)) :
    HasCyclicDifferenceQuotient A P ((A.comp P).range.comap A.range.subtype) T := by
  let N := P.range
  let M := (A.comp P).range.comap A.range.subtype
  obtain ⟨F, hF⟩ := differenceImageQuotient A P hA
  letI : SeparableSpace (V ⧸ N) := hs
  have hInv (a : L) {f : V} (hf : f ∈ N) : T a f ∈ N := by
    obtain ⟨v, rfl⟩ := hf
    exact ⟨T a v, (hP a v).symm⟩
  let R (a : L) := N.liftQL (N.mkQL.comp (T a)) (fun f hf ↦
    (Submodule.Quotient.mk_eq_zero N).mpr (hInv a hf))
  let r (p : L × (V ⧸ N)) := R p.1 p.2
  have hrq (a : L) (f : V) : r (a, N.mkQ f) = N.mkQ (T a f) := rfl
  have hr : Continuous r := by
    have hid : IsOpenQuotientMap (id : L → L) := IsOpenQuotientMap.id
    have hq := hid.prodMap N.isOpenQuotientMap_mkQ
    apply hq.isQuotientMap.continuous_iff.mpr
    exact N.continuous_mkQ.comp hT
  let s (p : L × (A.range ⧸ M)) := F (r (p.1, F.symm p.2))
  have hs : Continuous s := F.continuous.comp (hr.comp
    (continuous_fst.prodMk (F.symm.continuous.comp continuous_snd)))
  refine ⟨F, hF, F.surjective.denseRange.separableSpace F.continuous, nuclearLocallyConvex_of_equiv F hn,
    frechet_of_linearEquiv hf F, r, s, hr, hs, hrq, ?_, ?_⟩
  · intro a v
    obtain ⟨f, hf⟩ := v.property
    have he : (⟨A f, ⟨f, rfl⟩⟩ : A.range) = v := Subtype.ext hf
    have hfa : F (N.mkQ f) = M.mkQ v := (hF f).trans (congrArg M.mkQ he)
    refine ⟨⟨A (T a f), ⟨T a f, rfl⟩⟩, (hAP a f).symm.trans (congrArg (T a) hf), ?_⟩
    change F (r (a, F.symm (M.mkQ v))) = _
    rw [← hfa, F.symm_apply_apply, hrq, hF]
  · intro a y
    change _ = F (r (a, F.symm (F y)))
    rw [F.symm_apply_apply]

set_option maxHeartbeats 900000 in
/-- Lemma 4.6.1.3(3). The last difference gives the quotient equivalence.
Both quotients carry the indicated jointly continuous translations. -/
theorem exponentialIsotypeDifferenceProduct_cancel (gs : List G)
    (hgs : ∀ a ∈ gs, 0 < (m a).toAdd) (g : G) (hg : 0 < (m g).toAdd) :
    let A := exponentialIsotypeDifference m τ hτ w hm g
    HasCyclicDifferenceQuotient A (exponentialIsotypeDifferenceProduct m τ hτ w hm gs)
      ((exponentialIsotypeDifferenceProduct m τ hτ w hm (gs ++ [g])).range.comap A.range.subtype)
      (exponentialIsotypeTranslation m τ hτ w hm) := by
  dsimp only
  rw [exponentialIsotypeDifferenceProduct_append_single m τ hτ w hm gs g]
  obtain ⟨_, hs, hn, hf⟩ := exponentialIsotypeDifferenceProduct_quotient m τ hτ w hm gs hgs
  refine cyclicDifferenceQuotient_of_closedEmbedding _ _
    (isotypeDifference_isClosedEmbedding m τ hτ w hm g hg) _ ?_ ?_
    (fun a f ↦ isotypeTranslate_product_commute m τ hτ w hm a gs f) hs hn hf
  · exact ((ModulatedExponentialInductive.continuous_translate m I hm (fun t ↦ ⟨τ t, hτ t⟩)
      univ_nonempty_real).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · intro a f
    exact isotypeTranslate_product_commute m τ hτ w hm a [g] f

end Difference

end Masullo
