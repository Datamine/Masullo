import BruhatSchwartzDifferences
import ModulatedExponentialRadial
import SchwartzCyclicPeriodization

open Function Set Topology
open scoped SchwartzMap

noncomputable section

namespace Masullo

set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G)
  (hτ : ∀ t, m (τ t) = t) (w : PontryaginDual m.toMonoidHom.ker)
  (hm : IsProperMap m) (I : Set ℝ) (hI : I.Nonempty)

local notation "E" => ModulatedExponentialInductive m I
local notation "H" => modulatedDecayIsotype m w I
local notation "X" => PositiveRealExponentialDecay I
local notation "χ" => extendModulatedCharacter m τ hτ w

local instance : IsTopologicalAddGroup E :=
  (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup

/-- The cyclic difference restricted to an interval-weighted norm-one isotype. -/
def modulatedDecayIsotypeDifference (g : G) : H →L[ℂ] H := by
  let T := ModulatedExponentialInductive.translate m I g⁻¹
  have hT : Continuous T :=
    (ModulatedExponentialInductive.continuous_translate m I hm (fun t ↦ ⟨τ t, hτ t⟩)
      hI).comp (continuous_const.prodMk continuous_id)
  have hpres : ∀ f ∈ H, T f ∈ H := by
    intro f hf k x
    rw [ModulatedExponentialInductive.translate_apply, ModulatedExponentialInductive.translate_apply,
      ← mul_assoc, mul_comm g⁻¹⁻¹ _, mul_assoc]
    exact hf k (g⁻¹⁻¹ * x)
  exact ContinuousLinearMap.id ℂ H - (⟨T, hT⟩ : E →L[ℂ] E).restrict hpres

omit [SecondCountableTopology G] in
theorem modulatedDecayIsotypeDifference_apply (g : G) (f : H) (x : G) :
    (modulatedDecayIsotypeDifference m τ hτ w hm I hI g f : E).val x =
      f.val.val x - f.val.val (g * x) := by
  change f.val.val x - f.val.val (g⁻¹⁻¹ * x) = _
  rw [inv_inv]

/-- Finite difference products in the actual interval-weighted isotype. -/
def modulatedDecayIsotypeDifferenceProduct (gs : List G) : H →L[ℂ] H :=
  gs.foldr (fun g A ↦ (modulatedDecayIsotypeDifference m τ hτ w hm I hI g).comp A)
    (ContinuousLinearMap.id ℂ _)

/-- One radial coordinate identification simultaneously intertwines every
cyclic difference product with the scalar product for the associated phases. -/
theorem exists_modulatedDecayRadialDifferenceModel :
    ∃ e : X ≃L[ℂ] H,
      (∀ f g, (e f : E).val g = f.val (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ)) ∧
      (∀ u x, (e.symm u).val x = (u : E).val (τ (Multiplicative.ofAdd x))) ∧
      ∀ (gs : List G) (f : X),
        modulatedDecayIsotypeDifferenceProduct m τ hτ w hm I hI gs (e f) =
          e (logDecayCyclicDifferenceProduct I hI
            (gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹)) f) := by
  obtain ⟨e, he, hr⟩ := exists_modulatedDecayRadialIsotype m τ hτ w I hI hm
  refine ⟨e, he, hr, fun gs f ↦ ?_⟩
  have hsingle (g : G) (f : X) :
      modulatedDecayIsotypeDifference m τ hτ w hm I hI g (e f) =
        e (logDecayCyclicDifference I hI ((m g).toAdd, (χ g)⁻¹) f) := by
    apply Subtype.ext
    apply ModulatedExponentialInductive.algebraicEquiv.injective
    apply Subtype.ext
    funext x
    change (modulatedDecayIsotypeDifference m τ hτ w hm I hI g (e f) : E).val x =
      (e (logDecayCyclicDifference I hI ((m g).toAdd, (χ g)⁻¹) f) : E).val x
    rw [modulatedDecayIsotypeDifference_apply, he, he, he, map_mul m, map_mul (χ), mul_inv_rev,
      Circle.coe_mul]
    change f.val (m x).toAdd * (((χ x)⁻¹ : Circle) : ℂ) -
      f.val ((m g).toAdd + (m x).toAdd) *
        ((((χ x)⁻¹ : Circle) : ℂ) * (((χ g)⁻¹ : Circle) : ℂ)) = _
    rw [logDecayCyclicDifference_apply, add_comm (m g).toAdd]
    ring
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    let ys := gs.map fun a ↦ ((m a).toAdd, (χ a)⁻¹)
    change modulatedDecayIsotypeDifference m τ hτ w hm I hI g
        (modulatedDecayIsotypeDifferenceProduct m τ hτ w hm I hI gs (e f)) =
      e (logDecayCyclicDifference I hI ((m g).toAdd, (χ g)⁻¹)
        (logDecayCyclicDifferenceProduct I hI ys f))
    rw [ih]
    exact hsingle g _

def quotientIntertwiningEquiv {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [ContinuousAdd A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [ContinuousAdd B]
    (e : A ≃L[ℂ] B) (P : A →L[ℂ] A) (Q : B →L[ℂ] B)
    (h : ∀ x, Q (e x) = e (P x)) : (A ⧸ P.range) ≃L[ℂ] (B ⧸ Q.range) := by
  let L := P.range.liftQL (Q.range.mkQL.comp e.toContinuousLinearMap) (by
    rintro _ ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero Q.range).mpr
    exact ⟨e x, h x⟩)
  let R := Q.range.liftQL (P.range.mkQL.comp e.symm.toContinuousLinearMap) (by
    rintro _ ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero P.range).mpr
    refine ⟨e.symm x, ?_⟩
    apply e.injective
    change e (P (e.symm x)) = e (e.symm (Q x))
    rw [e.apply_symm_apply, ← h, e.apply_symm_apply])
  have hright : RightInverse R L := by
    intro y
    obtain ⟨b, rfl⟩ := Q.range.mkQ_surjective y
    change Q.range.mkQ (e (e.symm b)) = Q.range.mkQ b
    rw [e.apply_symm_apply]
  have hleft : LeftInverse R L := by
    intro x
    obtain ⟨a, rfl⟩ := P.range.mkQ_surjective x
    change P.range.mkQ (e.symm (e a)) = P.range.mkQ a
    rw [e.symm_apply_apply]
  exact ⟨LinearEquiv.ofLinear L.toLinearMap R.toLinearMap
    (LinearMap.ext hright) (LinearMap.ext hleft), L.continuous, R.continuous⟩

/-- The actual weighted isotype quotient has the radial Schwartz quotient
as its continuous linear model, with the radial extension on representatives. -/
theorem exists_modulatedDecayRadialDifferenceQuotient (gs : List G) :
    let P := logDecayCyclicDifferenceProduct I hI (gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹))
    let Q := modulatedDecayIsotypeDifferenceProduct m τ hτ w hm I hI gs
    ∃ (e : X ≃L[ℂ] H) (q : (X ⧸ P.range) ≃L[ℂ] (H ⧸ Q.range)),
      (∀ u x, (e.symm u).val x = (u : E).val (τ (Multiplicative.ofAdd x))) ∧
      ∀ f, q (P.range.mkQ f) = Q.range.mkQ (e f) := by
  obtain ⟨e, _, hr, h⟩ := exists_modulatedDecayRadialDifferenceModel m τ hτ w hm I hI
  exact ⟨e, quotientIntertwiningEquiv e _ _ (h gs), hr, fun _ ↦ rfl⟩

local notation "S" => BruhatSchwartz G
local notation "K" => m.toMonoidHom.ker
local notation "ρ" => bruhatSchwartzTranslationAction (G := G)

local instance : UniformSpace S := bruhatSchwartzUniformSpace
local instance : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
local instance : T2Space S := bruhatSchwartz_t2
local instance : ContinuousSMul ℂ S := (PolynormableSpace.withSeminorms ℂ S).continuousSMul
local instance : IsTopologicalAddGroup S :=
  (PolynormableSpace.withSeminorms ℂ S).topologicalAddGroup

local notation "H₀" => fixedSubmodule (compactIsotypicAction K w ρ)

local instance : HasQuotient (↥H₀) (Submodule ℂ (↥H₀)) :=
  @Submodule.hasQuotient ℂ (↥H₀) _ (H₀).addCommGroup (H₀).module

/-- The ordinary Schwartz–Bruhat difference product restricted to an isotype. -/
def bruhatSchwartzIsotypeDifferenceProduct (gs : List G) : H₀ →L[ℂ] H₀ :=
  (bruhatSchwartzDifferenceProduct gs).restrict fun f hf ↦ by
    have hf₀ := (mem_circleIsotype_iff w.toMonoidHom ((ρ).comp (K).subtype) f).mp hf
    apply (mem_circleIsotype_iff w.toMonoidHom ((ρ).comp (K).subtype)
      (bruhatSchwartzDifferenceProduct gs f)).mpr
    intro k
    apply Subtype.ext
    funext x
    change (bruhatSchwartz_translate k.val (bruhatSchwartzDifferenceProduct gs f)).val x =
      (w k : ℂ) * (bruhatSchwartzDifferenceProduct gs f).val x
    rw [bruhatSchwartz_translate_apply]
    apply bruhatSchwartzDifferenceProduct_preserves_isotype w gs f
    intro l y
    have hy := congrArg (fun v : S ↦ v.val y) (hf₀ l)
    change (bruhatSchwartz_translate l.val f).val y = (w l : ℂ) * f.val y at hy
    rwa [bruhatSchwartz_translate_apply] at hy

include hm in
private theorem exists_bruhatSchwartzRadialDifferenceModel (gs : List G) :
    ∃ e : 𝓢(ℝ, ℂ) ≃L[ℂ] H₀,
      (∀ f g, (e f : S).val g = f (m g).toAdd * (((χ g)⁻¹ : Circle) : ℂ)) ∧
      ∀ f, bruhatSchwartzIsotypeDifferenceProduct m w gs (e f) =
        e (schwartzCyclicDifferenceProduct (gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹)) f) := by
  obtain ⟨e, he, _⟩ := exists_bruhatSchwartz_radialIsotype m τ hτ w hm
  refine ⟨e, he, fun f ↦ ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (bruhatSchwartzDifferenceProduct gs (e f : S)).val x =
    (e (schwartzCyclicDifferenceProduct (gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹)) f) : S).val x
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    let ys := gs.map fun a ↦ ((m a).toAdd, (χ a)⁻¹)
    let u := schwartzCyclicDifferenceProduct ys f
    change (bruhatSchwartzDifference g (bruhatSchwartzDifferenceProduct gs (e f : S))).val x =
      (e (schwartzCyclicDifference ((m g).toAdd, (χ g)⁻¹) u) : S).val x
    rw [bruhatSchwartzDifference_apply, ih x, ih (g * x), he, he, he,
      map_mul m, map_mul (χ), mul_inv_rev, Circle.coe_mul]
    change u (m x).toAdd * (((χ x)⁻¹ : Circle) : ℂ) -
      u ((m g).toAdd + (m x).toAdd) * ((((χ x)⁻¹ : Circle) : ℂ) * (((χ g)⁻¹ : Circle) : ℂ)) =
      schwartzCyclicDifference ((m g).toAdd, (χ g)⁻¹) u (m x).toAdd *
        (((χ x)⁻¹ : Circle) : ℂ)
    rw [schwartzCyclicDifference_apply, add_comm (m g).toAdd]
    ring

/-- On the actual norm-one isotype, the weighted-to-ordinary quotient
comparison is the continuous linear isomorphism induced by inclusion. -/
theorem exists_modulatedDecayIsotypeDifferenceQuotientComparison (h0 : (0 : ℝ) ∈ I)
    (gs : List G) (hgs : ∀ g ∈ gs, 0 < (m g).toAdd) :
    let P := modulatedDecayIsotypeDifferenceProduct m τ hτ w hm I hI gs
    let Q := bruhatSchwartzIsotypeDifferenceProduct m w gs
    ∃ (L : H →L[ℂ] H₀) (e : (H ⧸ P.range) ≃L[ℂ] ((↥H₀) ⧸ Q.range)),
      (∀ u x, (L u : S).val x = u.val.val x) ∧
      ∀ u, e (P.range.mkQ u) = Q.range.mkQ (L u) := by
  obtain ⟨eW, heW, _, hW⟩ := exists_modulatedDecayRadialDifferenceModel m τ hτ w hm I hI
  obtain ⟨eO, heO, hO⟩ := exists_bruhatSchwartzRadialDifferenceModel m τ hτ w hm gs
  let ys := gs.map fun g ↦ ((m g).toAdd, (χ g)⁻¹)
  have hy : ∀ y ∈ ys, 0 < y.1 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    exact hgs g hg
  let J := positiveRealExponentialDecay_zeroInclusion I h0
  let L := eO.toContinuousLinearMap.comp (J.comp eW.symm.toContinuousLinearMap)
  have hL (u : H) (x : G) : (L u : S).val x = u.val.val x := by
    change (eO (J (eW.symm u)) : S).val x = u.val.val x
    rw [heO, positiveRealExponentialDecay_zeroInclusion_apply]
    rw [← heW, eW.apply_symm_apply]
  let qW := quotientIntertwiningEquiv eW _ _ (hW gs)
  let qO := quotientIntertwiningEquiv (B := ↥H₀) eO (schwartzCyclicDifferenceProduct ys)
    (bruhatSchwartzIsotypeDifferenceProduct m w gs) hO
  let C := logDecayCyclicDifferenceProduct_quotientEquiv I h0 ys hy
  refine ⟨L, qW.symm.trans (C.trans qO), hL, fun u ↦ ?_⟩
  obtain ⟨f, rfl⟩ := eW.surjective u
  have hqw (f : X) : qW (Submodule.Quotient.mk f) = Submodule.Quotient.mk (eW f) := rfl
  change qO (C (qW.symm (Submodule.Quotient.mk (eW f)))) = Submodule.Quotient.mk (L (eW f))
  rw [← hqw, qW.symm_apply_apply]
  have hc (f : X) : C (Submodule.Quotient.mk f) = Submodule.Quotient.mk (J f) := rfl
  refine (congrArg qO (hc f)).trans ?_
  change Submodule.Quotient.mk (eO (J f)) = Submodule.Quotient.mk (eO (J (eW.symm (eW f))))
  rw [eW.symm_apply_apply]

private def restrictLogDecayWeights (J : Set ℝ) (hJ : J.Nonempty) (hJI : J ⊆ I) :
    X →L[ℂ] PositiveRealExponentialDecay J := by
  let L := (logExponentialDecaySubmodule I).subtype.codRestrict
    (logExponentialDecaySubmodule J) fun f ↦
      (Submodule.mem_iInf _).mpr fun a ↦ (Submodule.mem_iInf _).mp f.property ⟨a, hJI a.property⟩
  refine ⟨L, (positiveRealExponentialDecay_isEmbedding J hJ).isInducing.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro a
  let b : I := ⟨a, hJI a.property⟩
  have h := (continuous_apply b).comp (positiveRealExponentialDecay_isEmbedding I (hJ.mono hJI)).continuous
  refine h.congr fun f ↦ SchwartzMap.ext fun x ↦ ?_
  exact (logExponentialDecayTwist_apply I b f x).trans
    (logExponentialDecayTwist_apply J a (L f) x).symm

private theorem restrictLogDecayWeights_val (J : Set ℝ) (hJ : J.Nonempty) (hJI : J ⊆ I) (f : X) :
    (restrictLogDecayWeights I J hJ hJI f).val = f.val := rfl

/-- The comparison for nested weighted spaces is also induced by inclusion
on the corresponding actual norm-one isotypes. -/
theorem exists_modulatedDecayIsotypeDifferenceQuotientRestriction
    (J : Set ℝ) (hJI : J ⊆ I) (hJ : J.Nonempty) (hz : (0 : ℝ) ∈ J)
    (gs : List G) (hgs : ∀ g ∈ gs, 0 < (m g).toAdd) :
    let P := modulatedDecayIsotypeDifferenceProduct m τ hτ w hm I hI gs
    let Q := modulatedDecayIsotypeDifferenceProduct m τ hτ w hm J hJ gs
    let HJ := modulatedDecayIsotype m w J
    ∃ (L : H →L[ℂ] HJ) (e : (H ⧸ P.range) ≃L[ℂ] (HJ ⧸ Q.range)),
      (∀ u x, (L u).val.val x = u.val.val x) ∧
      ∀ u, e (P.range.mkQ u) = Q.range.mkQ (L u) := by
  obtain ⟨aI, eI, haI, heI⟩ :=
    exists_modulatedDecayIsotypeDifferenceQuotientComparison m τ hτ w hm I hI (hJI hz) gs hgs
  obtain ⟨aJ, eJ, haJ, heJ⟩ :=
    exists_modulatedDecayIsotypeDifferenceQuotientComparison m τ hτ w hm J hJ hz gs hgs
  obtain ⟨rI, hrI, _⟩ := exists_modulatedDecayRadialIsotype m τ hτ w I hI hm
  obtain ⟨rJ, hrJ, _⟩ := exists_modulatedDecayRadialIsotype m τ hτ w J hJ hm
  let L := rJ.toContinuousLinearMap.comp ((restrictLogDecayWeights I J hJ hJI).comp rI.symm.toContinuousLinearMap)
  have hL (u : H) (x : G) : (L u).val.val x = u.val.val x := by
    change (rJ (restrictLogDecayWeights I J hJ hJI (rI.symm u))).val.val x = _
    rw [hrJ, restrictLogDecayWeights_val, ← hrI, rI.apply_symm_apply]
  refine ⟨L, eI.trans eJ.symm, hL, fun u ↦ ?_⟩
  apply eJ.injective
  change eJ (eJ.symm (eI (Submodule.Quotient.mk u))) = eJ (Submodule.Quotient.mk (L u))
  rw [eJ.apply_symm_apply]
  have hx : aI u = aJ (L u) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact (haI u x).trans ((haJ (L u) x).trans (hL u x)).symm
  exact (heI u).trans ((congrArg _ hx).trans (heJ (L u)).symm)

end Masullo
