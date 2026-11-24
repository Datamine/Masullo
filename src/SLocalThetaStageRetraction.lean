import SLocalThetaStageProbe
import SLocalPrincipalValue
import FiniteRadialTests
import GlobalWeilUnitAverage

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Coord (S : Finset (Place F)) := (w : S) → w.val.adicCompletion F
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev FinTest (S : Finset (Place F)) := locallyConstantTests (Coord F S)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

variable (S : Finset (Place F)) (v : Place F)
local notation "T" => insert v S
local notation "K" => v.adicCompletion F

private def joinCoord (x : Coord F S) (a : K) : Coord F T :=
  fun w ↦ if h : w.val = v then h.symm ▸ a
    else x ⟨w.val, (Finset.mem_insert.mp w.property).resolve_left h⟩

@[simp] private theorem joinCoord_old (hv : v ∉ S) (x : Coord F S) (a : K) (w : S) :
    joinCoord F S v x a ⟨w.val, Finset.mem_insert_of_mem w.property⟩ = x w := by
  simp [joinCoord, ne_of_mem_of_not_mem w.property hv]

@[simp] private theorem joinCoord_new (x : Coord F S) (a : K) :
    joinCoord F S v x a ⟨v, Finset.mem_insert_self _ _⟩ = a := by
  simp [joinCoord]

private def splitCoord (hv : v ∉ S) : Coord F T ≃ₜ Coord F S × K where
  toFun x := (fun w ↦ x ⟨w.val, Finset.mem_insert_of_mem w.property⟩,
    x ⟨v, Finset.mem_insert_self _ _⟩)
  invFun p := joinCoord F S v p.1 p.2
  left_inv x := by
    funext w
    by_cases h : w.val = v
    · have hw : w = ⟨v, Finset.mem_insert_self _ _⟩ := Subtype.ext h
      subst w
      exact joinCoord_new F S v _ _
    · let w' : S := ⟨w.val, (Finset.mem_insert.mp w.property).resolve_left h⟩
      have hw : w = ⟨w'.val, Finset.mem_insert_of_mem w'.property⟩ := rfl
      rw [hw]
      exact joinCoord_old F S v hv _ _ w'
  right_inv p := Prod.ext (funext (joinCoord_old F S v hv p.1 p.2)) (joinCoord_new F S v p.1 p.2)
  continuous_toFun := (continuous_pi fun w ↦ continuous_apply _).prodMk (continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro w
    by_cases h : w.val = v
    · have hw : w = ⟨v, Finset.mem_insert_self _ _⟩ := Subtype.ext h
      subst w
      simpa only [joinCoord_new] using (continuous_snd : Continuous (Prod.snd : Coord F S × K → K))
    · let w' : S := ⟨w.val, (Finset.mem_insert.mp w.property).resolve_left h⟩
      have hw : w = ⟨w'.val, Finset.mem_insert_of_mem w'.property⟩ := rfl
      rw [hw]
      change Continuous (fun p : Coord F S × K ↦
        joinCoord F S v p.1 p.2 ⟨w'.val, Finset.mem_insert_of_mem w'.property⟩)
      simp_rw [joinCoord_old F S v hv]
      exact (continuous_apply w').comp continuous_fst

variable (hv : v ∉ S)

private def finiteSection (a : K) : FinTest F T →ₗ[ℂ] FinTest F S :=
  (locallyConstantTestSectionMap a).comp (locallyConstantTestCongr (splitCoord F S v hv)).toLinearMap

private theorem finiteSection_apply (a : K) (ψ : FinTest F T) (x : Coord F S) :
    (finiteSection F S v hv a ψ).val x = ψ.val (joinCoord F S v x a) := rfl

local instance finiteTestTopology (A : Finset (Place F)) : TopologicalSpace (FinTest F A) :=
  finestLocallyConvexTopology _

local instance testTensorTopology (A : Finset (Place F)) :
    TopologicalSpace (Arch F ⊗[ℂ] FinTest F A) := inductiveTensorTopology _ _

private def stageSection (a : K) : Test F T →ₗ[ℂ] Test F S :=
  (TensorProduct.lift (sLocalBruhatPure F S)).comp <|
    (TensorProduct.map (LinearMap.id : Arch F →ₗ[ℂ] Arch F) (finiteSection F S v hv a)).comp
      (sLocalBruhatTensorEquiv F T).symm.toLinearEquiv.toLinearMap

private theorem stageSection_pure (a : K) (φ : Arch F) (ψ : FinTest F T) :
    stageSection F S v hv a (sLocalBruhatPure F T φ ψ) =
      sLocalBruhatPure F S φ (finiteSection F S v hv a ψ) := by
  have h : (sLocalBruhatTensorEquiv F T) (φ ⊗ₜ[ℂ] ψ) = sLocalBruhatPure F T φ ψ :=
    TensorProduct.lift.tmul (f' := sLocalBruhatPure F T) _ _
  rw [← h]
  change TensorProduct.lift (sLocalBruhatPure F S)
    (TensorProduct.map LinearMap.id (finiteSection F S v hv a)
      ((sLocalBruhatTensorEquiv F T).symm ((sLocalBruhatTensorEquiv F T) (φ ⊗ₜ[ℂ] ψ)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lift.tmul]

private theorem stageSection_continuous (a : K) : Continuous (stageSection F S v hv a) := by
  apply continuous_sLocal_of_pure F T (PolynormableSpace.withSeminorms ℂ (Test F S))
  intro ψ
  change Continuous (fun φ ↦ stageSection F S v hv a (sLocalBruhatPure F T φ ψ))
  simp_rw [stageSection_pure]
  exact (GlobalBruhat.pure_continuous F _).subtype_mk _

private theorem stageSection_restrict (a : K) (f : Test F T) (x : SAdeles F S) :
    sLocalBruhatRestriction F S (stageSection F S v hv a f).val x =
      sLocalBruhatRestriction F T f.val (x.1, joinCoord F S v x.2 a) := by
  let e := sLocalBruhatTensorEquiv F T
  obtain ⟨t, rfl⟩ := e.surjective f
  let L := sLocalBruhatRestriction F S
  let M := sLocalBruhatRestriction F T
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu =>
    simp only [map_add, Submodule.coe_add, Pi.add_apply] at *
    rw [ht, hu]
  | tmul φ ψ =>
    change L (stageSection F S v hv a (sLocalBruhatPure F T φ ψ)).val x =
      M (sLocalBruhatPure F T φ ψ).val (x.1, joinCoord F S v x.2 a)
    dsimp only [L, M]
    rw [stageSection_pure, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict, finiteSection_apply]

private abbrev ValuationIndex := range (fun u : (sIntegerRing F T)ˣ ↦
  v.valuation F (sUnitToField F T u).val)

private def rep (k : ValuationIndex F S v) : (sIntegerRing F T)ˣ := k.property.choose

private theorem rep_spec (k : ValuationIndex F S v) :
    v.valuation F (sUnitToField F T (rep F S v k)).val = k.val := k.property.choose_spec

private def repIdele (k : ValuationIndex F S v) : Idele F :=
  principalIdele F (sUnitToField F T (rep F S v k))

private def shiftedCoordinate : K := ((chosenFiniteUniformizer F v)⁻¹ : Kˣ).val

private def sliceTerm (k : ValuationIndex F S v) : Test F T →ₗ[ℂ] Test F S :=
  let a := (repIdele F S v k).val.2 v
  let u := Units.map (sAdelesProjection F S).toMonoidHom (repIdele F S v k)
  (sLocalBruhatLeftTranslate F S u⁻¹).toLinearMap.comp
    (stageSection F S v hv a - stageSection F S v hv (a * shiftedCoordinate F v))

private theorem sliceTerm_continuous (k : ValuationIndex F S v) :
    Continuous (sliceTerm F S v hv k) :=
  (sLocalBruhatLeftTranslate F S _).continuous.comp
    ((stageSection_continuous F S v hv _).sub (stageSection_continuous F S v hv _))

private theorem sliceTerm_pure_support (ψ : FinTest F T) :
    ∃ s : Finset (ValuationIndex F S v), ∀ φ : Arch F,
      support (fun k ↦ sliceTerm F S v hv k (sLocalBruhatPure F T φ ψ)) ⊆ s := by
  let f := locallyConstantTestCongr (splitCoord F S v hv) ψ
  have h := sUnitOnePlace_section_sub_support_finite F S v f (rep F S v) (rep_spec F S v)
  refine ⟨h.toFinset, fun φ k hk ↦ h.mem_toFinset.mpr ?_⟩
  intro hz
  apply hk
  let a := (repIdele F S v k).val.2 v
  have he : finiteSection F S v hv a ψ = finiteSection F S v hv (a * shiftedCoordinate F v) ψ :=
    sub_eq_zero.mp hz
  change sliceTerm F S v hv k (sLocalBruhatPure F T φ ψ) = 0
  unfold sliceTerm
  rw [LinearMap.comp_apply, LinearMap.sub_apply, stageSection_pure, stageSection_pure, he,
    sub_self, map_zero]

private theorem sliceTerm_support (f : Test F T) :
    (support fun k ↦ sliceTerm F S v hv k f).Finite := by
  let e := sLocalBruhatTensorEquiv F T
  obtain ⟨x, rfl⟩ := e.surjective f
  induction x using TensorProduct.induction_on with
  | zero =>
    simp
  | tmul φ ψ =>
    obtain ⟨s, hs⟩ := sliceTerm_pure_support F S v hv ψ
    exact s.finite_toSet.subset (hs φ)
  | add x y hx hy =>
    refine (hx.union hy).subset ?_
    intro k hk
    change sliceTerm F S v hv k (e (x + y)) ≠ 0 at hk
    rw [map_add, map_add] at hk
    by_contra h
    rw [Set.mem_union, not_or] at h
    exact hk (by rw [notMem_support.mp h.1, notMem_support.mp h.2, add_zero])

private def stageRetractionLinear : Test F T →ₗ[ℂ] Test F S where
  toFun f := ∑ᶠ k, sliceTerm F S v hv k f
  map_add' f g := by
    simp only [map_add]
    exact finsum_add_distrib (sliceTerm_support F S v hv f) (sliceTerm_support F S v hv g)
  map_smul' c f := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (sliceTerm_support F S v hv f)).symm

/-- Signed finite-coordinate slices, translated by the chosen valuation
representatives, define a continuous operator on the actual test spaces. -/
def sLocalThetaStageTestRetraction : Test F T →L[ℂ] Test F S :=
  ⟨stageRetractionLinear F S v hv, by
    apply continuous_sLocal_of_pure F T (PolynormableSpace.withSeminorms ℂ (Test F S))
    intro ψ
    obtain ⟨s, hs⟩ := sliceTerm_pure_support F S v hv ψ
    change Continuous (fun φ ↦ ∑ᶠ k, sliceTerm F S v hv k (sLocalBruhatPure F T φ ψ))
    simp_rw [fun φ : Arch F ↦ finsum_eq_sum_of_support_subset _ (hs φ)]
    exact continuous_finsetSum s fun k _ ↦ (sliceTerm_continuous F S v hv k).comp
      ((GlobalBruhat.pure_continuous F _).subtype_mk _)⟩

private theorem projected_multiply (hv : v ∉ S) (k : ValuationIndex F S v)
    (x : Idele F) :
    sAdelesProjection F T ((repIdele F S v k) * x).val =
      let y := sAdelesProjection F S (repIdele F S v k).val * sAdelesProjection F S x.val
      (y.1, joinCoord F S v y.2 ((repIdele F S v k).val.2 v * x.val.2 v)) := by
  let a := ((repIdele F S v k) * x).val
  have e := (splitCoord F S v hv).left_inv ((sAdelesProjection F T a).2)
  exact Prod.ext rfl e.symm

private theorem sliceTerm_restrict (k : ValuationIndex F S v) (f : Test F T)
    (x : SAdeles F S) :
    sLocalBruhatRestriction F S (sliceTerm F S v hv k f).val x =
      let y := sAdelesProjection F S (repIdele F S v k).val * x
      let a := (repIdele F S v k).val.2 v
      sLocalBruhatRestriction F T f.val (y.1, joinCoord F S v y.2 a) -
      sLocalBruhatRestriction F T f.val (y.1, joinCoord F S v y.2 (a * shiftedCoordinate F v)) := by
  dsimp only [sliceTerm, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [sLocalBruhatLeftTranslate_restrict]
  simp only [LinearMap.sub_apply, Submodule.coe_sub, map_sub, Pi.sub_apply, stageSection_restrict]
  rfl

private def largerSummand (f : Test F T) (z : Idele F) (u : (sIntegerRing F T)ˣ) : ℂ :=
  sLocalBruhatRestriction F T f.val
    (sIntegerDiagonal F T u.val * sAdelesProjection F T z.val)

private theorem largerSummand_summable (f : Test F T) (z : Idele F) :
    Summable (largerSummand F S v f z) := by
  let g := Units.map (sAdelesProjection F T).toMonoidHom z
  exact (Additive.toMul.summable_iff).mp
    (sLocalTheta_restriction_summable F T f.val g).of_norm

private theorem largerSummand_eq (f : Test F T) (z : Idele F)
    (k : ValuationIndex F S v) (u : (sIntegerRing F S)ˣ) :
    largerSummand F S v f z (rep F S v k * sUnitInclusion F (Finset.subset_insert v S) u) =
      sLocalBruhatRestriction F T f.val (sAdelesProjection F T
        (repIdele F S v k * (principalIdele F (sUnitToField F S u) * z)).val) := by
  unfold largerSummand repIdele
  let d := sUnitToField F T
  let r := rep F S v k
  let j := sUnitInclusion F (Finset.subset_insert v S) u
  change sLocalBruhatRestriction F T f.val
    (sAdelesProjection F T (principalIdele F (d (r * j))).val * sAdelesProjection F T z.val) = _
  rw [map_mul d, show d j = sUnitToField F S u from rfl, map_mul (principalIdele F),
    ← mul_assoc]
  simp only [Units.val_mul, map_mul]
  rfl

/-- A test whose restriction is invariant under multiplication in the
new coordinate by local integral units. -/
def sLocalThetaNewPlaceInvariant (f : Test F T) : Prop :=
  ∀ (x : SAdeles F S) (a : K) (u : Kˣ), Valued.v u.val = 1 →
    sLocalBruhatRestriction F T f.val (x.1, joinCoord F S v x.2 (a * u.val)) =
      sLocalBruhatRestriction F T f.val (x.1, joinCoord F S v x.2 a)

private theorem singleCoordinate_outside (w : Place F) (hw : w ≠ v) (u : Kˣ) :
    (singleFiniteIdele F v u).val.2 w = 1 := by
  change Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v u.val w = 1
  exact Function.update_of_ne hw _ _

private theorem singleCoordinate_at (u : Kˣ) :
    (singleFiniteIdele F v u).val.2 v = u.val := by
  change Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v u.val v = u.val
  exact Function.update_self _ _ _

set_option maxHeartbeats 650000 in
private theorem fiber_difference (f : Test F T) (hf : sLocalThetaNewPlaceInvariant F S v f)
    (g : (SAdeles F S)ˣ) (k : ValuationIndex F S v) (u : (sIntegerRing F S)ˣ) :
    let z := (sLocalEmbed F S g).val
    let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
    let j := rep F S v k * sUnitInclusion F (Finset.subset_insert v S) u
    largerSummand F S v f z j - largerSummand F S v f (z * c) j =
      sLocalBruhatRestriction F S (sliceTerm F S v hv k f).val
        (sIntegerDiagonal F S u.val * g.val) := by
  dsimp only
  let z := (sLocalEmbed F S g).val
  let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
  let b := principalIdele F (sUnitToField F S u)
  let w := Units.map (algebraMap F K).toMonoidHom (sUnitToField F S u)
  have hw : Valued.v w.val = 1 := by
    have hb : ideleOrder F b v = 0 :=
      (sIdeleBlock_mem_iff F S b).mp (sPrincipal F S u).property v hv
    change Valued.v (b.val.2 v) = 1
    exact (ideleOrder_eq_zero_iff F b v).mp hb
  have hprojz : sAdelesProjection F S z.val = g.val := sLocalEmbed_project F S g
  have hprojc : sAdelesProjection F S c.val = 1 := by
    refine Prod.ext (by rfl) ?_
    funext j
    exact singleCoordinate_outside F v j.val (ne_of_mem_of_not_mem j.property hv) _
  have hproj (e : Bool) :
      sAdelesProjection F S (b * (if e then z * c else z)).val = sIntegerDiagonal F S u.val * g.val := by
    rw [Units.val_mul, map_mul]
    congr 1
    cases e
    · exact hprojz
    · change sAdelesProjection F S (z.val * c.val) = g.val
      rw [map_mul, hprojc, mul_one, hprojz]
  have hnew (e : Bool) :
      (b * (if e then z * c else z)).val.2 v = w.val * (if e then shiftedCoordinate F v else 1) := by
    have hz := sLocalEmbed_outside_one F S g v hv
    cases e
    · change w.val * z.val.2 v = w.val * 1
      rw [hz]
    · change w.val * (z.val.2 v * c.val.2 v) = w.val * shiftedCoordinate F v
      rw [hz, one_mul, singleCoordinate_at]
      rfl
  have h (e : Bool) :
      largerSummand F S v f (if e then z * c else z)
        (rep F S v k * sUnitInclusion F (Finset.subset_insert v S) u) =
      let y := sAdelesProjection F S (repIdele F S v k).val * (sIntegerDiagonal F S u.val * g.val)
      let a := (repIdele F S v k).val.2 v * (if e then shiftedCoordinate F v else 1)
      sLocalBruhatRestriction F T f.val (y.1, joinCoord F S v y.2 a) := by
    rw [largerSummand_eq, projected_multiply F S v hv]
    dsimp only
    rw [hproj, hnew]
    have hmul : (repIdele F S v k).val.2 v * (w.val * (if e then shiftedCoordinate F v else 1)) =
        ((repIdele F S v k).val.2 v * (if e then shiftedCoordinate F v else 1)) * w.val := by ring
    rw [hmul]
    exact hf _ _ w hw
  rw [sliceTerm_restrict]
  have h₀ := h false
  have h₁ := h true
  simp only [Bool.false_eq_true, ite_false, ite_true, mul_one] at h₀ h₁
  rw [h₀, h₁]

/-- The signed slice operator intertwines theta with the shifted difference on
tests invariant under the added coordinate's integral units. -/
theorem sLocalThetaStageTestRetraction_eval (f : Test F T)
    (hf : sLocalThetaNewPlaceInvariant F S v f) (g : (SAdeles F S)ˣ) :
    let z := (sLocalEmbed F S g).val
    let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
    sLocalThetaOnIdeles F S
      (sLocalBruhatRestriction F S (sLocalThetaStageTestRetraction F S v hv f).val) g =
      sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T f.val)
          (Units.map (sAdelesProjection F T).toMonoidHom z) -
        sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T f.val)
          (Units.map (sAdelesProjection F T).toMonoidHom (z * c)) := by
  dsimp only
  let z := (sLocalEmbed F S g).val
  let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
  let B := (sLocalThetaEval F S g).comp (Test F S).subtype
  let a := largerSummand F S v f z
  let b := largerSummand F S v f (z * c)
  change B (∑ᶠ k, sliceTerm F S v hv k f) =
    (∑' u : Additive (sIntegerRing F T)ˣ, a u.toMul) -
      (∑' u : Additive (sIntegerRing F T)ˣ, b u.toMul)
  rw [Additive.toMul.tsum_eq a, Additive.toMul.tsum_eq b,
    ← (largerSummand_summable F S v f z).tsum_sub (largerSummand_summable F S v f (z * c))]
  rw [sUnitOnePlace_tsum F S v hv _ ((largerSummand_summable F S v f z).sub
    (largerSummand_summable F S v f (z * c))) (rep F S v) (rep_spec F S v)]
  have h (k : ValuationIndex F S v) :
      (∑' u, (a - b) (rep F S v k * sUnitInclusion F (Finset.subset_insert v S) u)) =
        B (sliceTerm F S v hv k f) := by
    change _ = ∑' u : Additive (sIntegerRing F S)ˣ,
      sLocalBruhatRestriction F S (sliceTerm F S v hv k f).val
        (sIntegerDiagonal F S u.toMul.val * g.val)
    rw [← Additive.toMul.tsum_eq]
    exact tsum_congr fun u ↦ fiber_difference F S v hv f hf g k u.toMul
  change B (∑ᶠ k, sliceTerm F S v hv k f) =
    ∑' k, ∑' u, (a - b) (rep F S v k * sUnitInclusion F (Finset.subset_insert v S) u)
  simp_rw [h]
  have hfin := sliceTerm_support F S v hv f
  have hB : (support fun k ↦ B (sliceTerm F S v hv k f)).Finite := hfin.subset (by
    intro k hk
    by_contra hz
    apply hk
    change B (sliceTerm F S v hv k f) = 0
    rw [notMem_support.mp hz, map_zero])
  rw [tsum_eq_finsum hB]
  exact B.toAddMonoidHom.map_finsum hfin


private abbrev U := ↥(principalIntegralUnits F v)
private abbrev Split := Coord F S × K
private abbrev SplitTest := locallyConstantTests (Split F S v)

local instance : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance : MeasurableSpace (U F v) := borel _
local instance : BorelSpace (U F v) := ⟨rfl⟩

local instance : MulAction (U F v) (Split F S v) where
  smul u p := (p.1, u.val • p.2)
  one_smul p := Prod.ext rfl (one_smul (Kˣ) p.2)
  mul_smul u w p := Prod.ext rfl (mul_smul u.val w.val p.2)

local instance : ContinuousSMul (U F v) (Split F S v) where
  continuous_smul := continuous_snd.fst.prodMk
    ((continuous_subtype_val.comp continuous_fst).smul continuous_snd.snd)

private def splitUnitAction : U F v →* (SplitTest F S v →ₗ[ℂ] SplitTest F S v) where
  toFun u := locallyConstantTestTranslate (Split F S v) u
  map_one' := by ext f p; simp [locallyConstantTestTranslate]
  map_mul' u w := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext p
    change f.val ((u * w)⁻¹ • p) = f.val (w⁻¹ • u⁻¹ • p)
    rw [mul_inv_rev, mul_smul]

private theorem splitUnitAction_orbit (ψ : SplitTest F S v) :
    IsLocallyConstant (fun u ↦ splitUnitAction F S v u ψ) :=
  locallyConstantTestTranslate_orbit_locallyConstant _ ψ

private def unitHaar : Measure (U F v) := Measure.haarMeasure ⊤

local instance : (unitHaar F v).IsHaarMeasure := by
  unfold unitHaar
  infer_instance

private theorem unitHaar_univ : unitHaar F v univ = 1 := Measure.haarMeasure_self

private def splitAverage := fixedOrbitAverage (splitUnitAction F S v) (unitHaar F v)
  (splitUnitAction_orbit F S v)

private def liftSplit (L : SplitTest F S v →ₗ[ℂ] SplitTest F S v) : Test F T →L[ℂ] Test F T :=
  let e := locallyConstantTestCongr (splitCoord F S v hv)
  sLocalBruhatFiniteMap F T (e.symm.toLinearMap.comp (L.comp e.toLinearMap))

private def unitTranslate (u : U F v) : Test F T →L[ℂ] Test F T :=
  liftSplit F S v hv (splitUnitAction F S v u)

private def unitAverage : Test F T →L[ℂ] Test F T :=
  liftSplit F S v hv (splitAverage F S v)

private theorem liftSplit_pure (L : SplitTest F S v →ₗ[ℂ] SplitTest F S v)
    (φ : Arch F) (ψ : SplitTest F S v) :
    liftSplit F S v hv L (sLocalBruhatPure F T φ
      ((locallyConstantTestCongr (splitCoord F S v hv)).symm ψ)) =
    sLocalBruhatPure F T φ ((locallyConstantTestCongr (splitCoord F S v hv)).symm (L ψ)) := by
  unfold liftSplit
  rw [sLocalBruhatFiniteMap_pure]
  simp

private theorem unitTranslate_orbit (f : Test F T) :
    IsLocallyConstant (fun u ↦ unitTranslate F S v hv u f) := by
  let J := sLocalBruhatTensorEquiv F T
  obtain ⟨z, rfl⟩ := J.surjective f
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact IsLocallyConstant.const 0
  | add a b ha hb =>
    simp only [map_add] at *
    exact (ha.prodMk hb).comp (fun p ↦ p.1 + p.2)
  | tmul φ ψ =>
    let e := locallyConstantTestCongr (splitCoord F S v hv)
    change IsLocallyConstant (fun u ↦ liftSplit F S v hv (splitUnitAction F S v u)
      (sLocalBruhatPure F T φ ψ))
    rw [← (locallyConstantTestCongr (splitCoord F S v hv)).symm_apply_apply ψ]
    simp_rw [liftSplit_pure]
    exact (splitUnitAction_orbit F S v (e ψ)).comp (fun a ↦ sLocalBruhatPure F T φ (e.symm a))

private theorem unitAverage_apply (f : Test F T) (ℓ : Test F T →ₗ[ℂ] ℂ) :
    ℓ (unitAverage F S v hv f) = ∫ u, ℓ (unitTranslate F S v hv u f) ∂unitHaar F v := by
  let J := sLocalBruhatTensorEquiv F T
  obtain ⟨z, rfl⟩ := J.surjective f
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    symm
    apply integral_add
    · exact ((unitTranslate_orbit F S v hv (J a)).comp ℓ).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact ((unitTranslate_orbit F S v hv (J b)).comp ℓ).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  | tmul φ ψ =>
    let e := locallyConstantTestCongr (splitCoord F S v hv)
    let m := ((sLocalBruhatPure F T φ).comp e.symm.toLinearMap)
    change ℓ (liftSplit F S v hv (splitAverage F S v) (sLocalBruhatPure F T φ ψ)) =
      ∫ u, ℓ (liftSplit F S v hv (splitUnitAction F S v u) (sLocalBruhatPure F T φ ψ)) ∂unitHaar F v
    rw [← (locallyConstantTestCongr (splitCoord F S v hv)).symm_apply_apply ψ]
    simp_rw [liftSplit_pure]
    exact fixedOrbitAverage_apply _ _ _ (e ψ) (ℓ.comp m)


private def stagePoint (x : SAdeles F T) : SAdeles F S :=
  (x.1, (splitCoord F S v hv x.2).1)

private theorem stagePoint_join (x : SAdeles F T) :
    ((stagePoint F S v hv x).1,
      joinCoord F S v (stagePoint F S v hv x).2 (x.2 ⟨v, Finset.mem_insert_self _ _⟩)) = x :=
  Prod.ext rfl ((splitCoord F S v hv).left_inv x.2)

private def stageEval (x : SAdeles F T) : Test F T →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp ((sLocalBruhatRestriction F T).comp (Test F T).subtype)

private theorem stageEval_ext {f h : Test F T}
    (he : ∀ x, stageEval F S v x f = stageEval F S v x h) : f = h := by
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext z
  change GlobalBruhat.evaluation F z f.val = GlobalBruhat.evaluation F z h.val
  rw [sLocalBruhatRestriction_reconstruct F T f, sLocalBruhatRestriction_reconstruct F T h]
  exact congrArg (· * _) (he (sAdelesProjection F T z))

private theorem unitTranslate_eval (u : U F v) (f : Test F T) (x : SAdeles F S) (a : K) :
    stageEval F S v (x.1, joinCoord F S v x.2 a) (unitTranslate F S v hv u f) =
      stageEval F S v (x.1, joinCoord F S v x.2 (u.val.inv * a)) f := by
  let J := sLocalBruhatTensorEquiv F T
  obtain ⟨z, rfl⟩ := J.surjective f
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul φ ψ =>
    let e := locallyConstantTestCongr (splitCoord F S v hv)
    change stageEval F S v (x.1, joinCoord F S v x.2 a)
      (liftSplit F S v hv (splitUnitAction F S v u) (sLocalBruhatPure F T φ ψ)) =
      stageEval F S v (x.1, joinCoord F S v x.2 (u.val.inv * a)) (sLocalBruhatPure F T φ ψ)
    rw [← (locallyConstantTestCongr (splitCoord F S v hv)).symm_apply_apply ψ]
    rw [liftSplit_pure]
    change sLocalBruhatRestriction F T (sLocalBruhatPure F T φ
      (e.symm (splitUnitAction F S v u (e ψ)))).val (x.1, joinCoord F S v x.2 a) =
      sLocalBruhatRestriction F T (sLocalBruhatPure F T φ (e.symm (e ψ))).val
        (x.1, joinCoord F S v x.2 (u.val.inv * a))
    rw [sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
    simp only [e, locallyConstantTestCongr_symm_apply]
    have h (b : K) : splitCoord F S v hv (joinCoord F S v x.2 b) = (x.2, b) :=
      (splitCoord F S v hv).right_inv (x.2, b)
    rw [h, h]
    rfl

private theorem unitAverage_fixed (f : Test F T) (u : U F v) :
    unitTranslate F S v hv u (unitAverage F S v hv f) = unitAverage F S v hv f := by
  let J := sLocalBruhatTensorEquiv F T
  obtain ⟨z, rfl⟩ := J.surjective f
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul φ ψ =>
    let e := locallyConstantTestCongr (splitCoord F S v hv)
    change liftSplit F S v hv (splitUnitAction F S v u)
      (liftSplit F S v hv (splitAverage F S v) (sLocalBruhatPure F T φ ψ)) =
      liftSplit F S v hv (splitAverage F S v) (sLocalBruhatPure F T φ ψ)
    rw [← (locallyConstantTestCongr (splitCoord F S v hv)).symm_apply_apply ψ]
    simp only [liftSplit_pure]
    rw [show splitUnitAction F S v u (splitAverage F S v (e ψ)) = splitAverage F S v (e ψ)
      from fixedOrbitAverage_fixed _ _ _ _ u]

private theorem unitAverage_invariant (f : Test F T) :
    sLocalThetaNewPlaceInvariant F S v (unitAverage F S v hv f) := by
  intro x a u hu
  let w : U F v := ⟨u⁻¹, (finiteCompletion_norm_eq_one_iff F v u⁻¹).mpr (by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])⟩
  have h := unitTranslate_eval F S v hv w (unitAverage F S v hv f) x a
  rw [unitAverage_fixed F S v hv f w] at h
  exact (show stageEval F S v (x.1, joinCoord F S v x.2 a) (unitAverage F S v hv f) =
    stageEval F S v (x.1, joinCoord F S v x.2 (a * u.val)) (unitAverage F S v hv f) from
      h.trans (congrArg (fun b ↦ stageEval F S v (x.1, joinCoord F S v x.2 b)
        (unitAverage F S v hv f)) (by change u.val * a = a * u.val; exact mul_comm _ _))).symm

private theorem stageUnit_mul (hv : v ∉ S) (u : Kˣ) (x : SAdeles F S) (a : K) :
    sAdelesProjection F T (singleFiniteIdele F v u).val * (x.1, joinCoord F S v x.2 a) =
      (x.1, joinCoord F S v x.2 (u.val * a)) := by
  refine Prod.ext (by change (1 : InfiniteAdeleRing F) * x.1 = x.1; exact one_mul _) ?_
  funext w
  change (singleFiniteIdele F v u).val.2 w.val * joinCoord F S v x.2 a w =
    joinCoord F S v x.2 (u.val * a) w
  by_cases h : w.val = v
  · have hw : w = ⟨v, Finset.mem_insert_self _ _⟩ := Subtype.ext h
    subst w
    rw [singleCoordinate_at, joinCoord_new, joinCoord_new]
  · let w' : S := ⟨w.val, (Finset.mem_insert.mp w.property).resolve_left h⟩
    have hw : w = ⟨w'.val, Finset.mem_insert_of_mem w'.property⟩ := rfl
    rw [singleCoordinate_outside F v _ h, one_mul, hw, joinCoord_old F S v hv, joinCoord_old F S v hv]

private theorem unitTranslate_theta (u : U F v) (f : Test F T) (g : (SAdeles F T)ˣ) :
    sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T (unitTranslate F S v hv u f).val) g =
      sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T f.val)
        (Units.map (sAdelesProjection F T).toMonoidHom (singleFiniteIdele F v u.val⁻¹) * g) := by
  unfold sLocalThetaOnIdeles
  apply tsum_congr
  intro t
  let x := sIntegerDiagonal F T t.toMul.val * g.val
  let y := sAdelesProjection F T (singleFiniteIdele F v u.val⁻¹).val
  change stageEval F S v x (unitTranslate F S v hv u f) =
    stageEval F S v (sIntegerDiagonal F T t.toMul.val * (y * g.val)) f
  rw [show sIntegerDiagonal F T t.toMul.val * (y * g.val) = y * x from by dsimp [x]; ac_rfl]
  let p := stagePoint F S v hv x
  let a := x.2 ⟨v, Finset.mem_insert_self _ _⟩
  rw [← show (p.1, joinCoord F S v p.2 a) = x from stagePoint_join F S v hv x]
  rw [unitTranslate_eval F S v hv, stageUnit_mul F S v hv]
  rfl

/-- Projection to a stage containing the supported place and re-insertion
recover the original single-place idele. -/
theorem singleFiniteIdele_embedded_of_mem {A : Finset (Place F)} (hvA : v ∈ A) (u : Kˣ) :
    (sLocalEmbed F A (Units.map (sAdelesProjection F A).toMonoidHom
      (singleFiniteIdele F v u))).val = singleFiniteIdele F v u := by
  let g := singleFiniteIdele F v u
  let j := Units.map (sAdelesProjection F A).toMonoidHom g
  change (sLocalEmbed F A j).val = g
  apply Units.ext
  apply Prod.ext
  · rw [sLocalEmbed_arch]; rfl
  · apply RestrictedProduct.ext
    intro w
    change (sLocalEmbed F A j).val.val.2 w = g.val.2 w
    by_cases hw : w ∈ A
    · exact sLocalEmbed_finite F A j ⟨w,hw⟩
    · rw [sLocalEmbed_outside_one F A j w hw]
      exact (singleCoordinate_outside F v w (fun h ↦ hw (h ▸ hvA)) _).symm

private theorem singleFiniteIdele_embedded (u : Kˣ) :
    (sLocalEmbed F T (Units.map (sAdelesProjection F T).toMonoidHom
      (singleFiniteIdele F v u))).val = singleFiniteIdele F v u :=
  singleFiniteIdele_embedded_of_mem F v (Finset.mem_insert_self _ _) u

private theorem unitTranslate_eq_global (u : U F v) (f : Test F T) :
    (unitTranslate F S v hv u f).val =
      GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f.val := by
  let g := singleFiniteIdele F v u.val
  let j := Units.map (sAdelesProjection F T).toMonoidHom g
  have he := singleFiniteIdele_embedded F S v u.val
  suffices h : unitTranslate F S v hv u f = sLocalBruhatLeftTranslate F T j f by
    rw [h]
    change GlobalBruhat.leftTranslate F (sLocalEmbed F T j).val f.val = _
    rw [he]
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext b
  change GlobalBruhat.evaluation F b (unitTranslate F S v hv u f).val =
    GlobalBruhat.evaluation F b (sLocalBruhatLeftTranslate F T j f).val
  rw [sLocalBruhatRestriction_reconstruct F T, sLocalBruhatRestriction_reconstruct F T,
    sLocalBruhatLeftTranslate_restrict]
  congr 1
  let x := sAdelesProjection F T b
  let a := x.2 ⟨v, Finset.mem_insert_self _ _⟩
  let y := stagePoint F S v hv x
  change stageEval F S v x (unitTranslate F S v hv u f) =
    sLocalBruhatRestriction F T f.val (j.inv * x)
  have hj : j.inv = sAdelesProjection F T (singleFiniteIdele F v u.val⁻¹).val := rfl
  rw [hj, ← show (y.1, joinCoord F S v y.2 a) = x from stagePoint_join F S v hv x,
    unitTranslate_eval F S v hv, stageUnit_mul F S v hv]
  rfl

private theorem unitAverage_kernel {f : Test F T}
    (hf : f ∈ (sLocalThetaOperator F T).ker) :
    unitAverage F S v hv f ∈ (sLocalThetaOperator F T).ker := by
  apply LinearMap.mem_ker.mpr
  funext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  let ℓ := (sLocalThetaEval F T g).comp (Test F T).subtype
  change ℓ (unitAverage F S v hv f) = 0
  rw [unitAverage_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  change sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T (unitTranslate F S v hv u f).val) g = 0
  rw [unitTranslate_theta]
  exact congrFun (LinearMap.mem_ker.mp hf) (QuotientGroup.mk _)


private theorem finiteExtend_join (hv : v ∉ S) (ψ : FinTest F S) (x : Coord F S) (a : K) :
    (sLocalFiniteExtend F S T ψ).val (joinCoord F S v x a) =
      ψ.val x * (if a ∈ v.adicCompletionIntegers F then 1 else 0) := by
  rw [sLocalFiniteExtend_apply F (Finset.subset_insert v S)]
  simp only [joinCoord_old F S v hv]
  have h :
      (∀ w : (insert v S : Finset (Place F)), w.val ∉ S → joinCoord F S v x a w ∈ w.val.adicCompletionIntegers F) ↔
        a ∈ v.adicCompletionIntegers F := by
    refine ⟨fun h ↦ ?_, fun h w hw ↦ ?_⟩
    · have he := h ⟨v, Finset.mem_insert_self _ _⟩ hv
      rwa [joinCoord_new] at he
    · have he : w = ⟨v, Finset.mem_insert_self _ _⟩ :=
        Subtype.ext ((Finset.mem_insert.mp w.property).resolve_right hw)
      subst w
      rwa [joinCoord_new]
  by_cases ha : a ∈ v.adicCompletionIntegers F
  · rw [ite_eq_left (h.mpr ha), ite_eq_left ha]
  · rw [ite_eq_right (mt h.mp ha), ite_eq_right ha]

private theorem finiteBall_stage_pure
    (n : ℤ) (φ : Arch F) (ψ : FinTest F S) :
    (sLocalBruhatPure F T φ ((locallyConstantTestCongr (splitCoord F S v hv)).symm
      (locallyConstantTestProduct ψ (finiteValuationBallTest F v n)))).val =
    GlobalBruhat.leftTranslate F (singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n))
      (sLocalBruhatPure F S φ ψ).val := by
  let g := singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)
  let j := Units.map (sAdelesProjection F T).toMonoidHom g
  have he := singleFiniteIdele_embedded F S v (chosenFiniteUniformizer F v ^ n)
  let a := sLocalBruhatPure F T φ ((locallyConstantTestCongr (splitCoord F S v hv)).symm
      (locallyConstantTestProduct ψ (finiteValuationBallTest F v n)))
  let b := sLocalBruhatLeftTranslate F T j (sLocalBruhatTransition F (Finset.subset_insert v S)
      (sLocalBruhatPure F S φ ψ))
  have hab : a.val = b.val := by
    apply (GlobalBruhat.algebraicEquiv F).injective
    apply Subtype.ext
    funext z
    change GlobalBruhat.evaluation F z a.val = GlobalBruhat.evaluation F z b.val
    rw [sLocalBruhatRestriction_reconstruct F T a, sLocalBruhatRestriction_reconstruct F T b]
    congr 1
    let x := sAdelesProjection F T z
    let t := x.2 ⟨v, Finset.mem_insert_self _ _⟩
    let y := stagePoint F S v hv x
    change sLocalBruhatRestriction F T a.val x = sLocalBruhatRestriction F T b.val x
    rw [show b = sLocalBruhatLeftTranslate F T j (sLocalBruhatTransition F
      (Finset.subset_insert v S) (sLocalBruhatPure F S φ ψ)) from rfl,
      sLocalBruhatLeftTranslate_restrict, sLocalBruhatTransition_pure]
    have hj : j.inv = sAdelesProjection F T (singleFiniteIdele F v
        ((chosenFiniteUniformizer F v ^ n)⁻¹)).val := rfl
    rw [hj, ← show (y.1, joinCoord F S v y.2 t) = x from stagePoint_join F S v hv x,
      stageUnit_mul F S v hv]
    change sLocalBruhatRestriction F T
      (sLocalBruhatPure F T φ ((locallyConstantTestCongr (splitCoord F S v hv)).symm
        (locallyConstantTestProduct ψ (finiteValuationBallTest F v n)))).val _ = _
    rw [sLocalBruhatPure_restrict, sLocalBruhatPure_restrict, finiteExtend_join F S v hv,
      locallyConstantTestCongr_symm_apply, locallyConstantTestProduct_apply]
    rw [show splitCoord F S v hv (joinCoord F S v y.2 t) = (y.2,t) from
      (splitCoord F S v hv).apply_symm_apply (y.2,t)]
    rw [finiteValuationBallTest_apply_uniformizer]
  change a.val = _
  rw [hab]
  change GlobalBruhat.leftTranslate F (sLocalEmbed F T j).val (sLocalBruhatPure F S φ ψ).val = _
  rw [he]

private def uniformizerTranslateSpan : Submodule ℂ (GlobalBruhat F) :=
  Submodule.span ℂ {g | ∃ (n : ℤ) (f : Test F S),
    GlobalBruhat.leftTranslate F (singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)) f.val = g}

private theorem unitAverage_mem_uniformizerTranslateSpan (f : Test F T) :
    (unitAverage F S v hv f).val ∈ uniformizerTranslateSpan F S v := by
  let D := uniformizerTranslateSpan F S v
  let J := sLocalBruhatTensorEquiv F T
  obtain ⟨z, rfl⟩ := J.surjective f
  induction z using TensorProduct.induction_on with
  | zero =>
    change (unitAverage F S v hv (J 0)).val ∈ D
    simpa only [map_zero, Submodule.coe_zero] using (D.zero_mem : (0 : GlobalBruhat F) ∈ D)
  | add p q hp hq =>
    simpa only [map_add, Submodule.coe_add] using D.add_mem hp hq
  | tmul φ ψ =>
    let e := locallyConstantTestCongr (splitCoord F S v hv)
    let b := splitAverage F S v (e ψ)
    change (liftSplit F S v hv (splitAverage F S v) (sLocalBruhatPure F T φ ψ)).val ∈ D
    rw [← e.symm_apply_apply ψ, liftSplit_pure]
    change (sLocalBruhatPure F T φ (e.symm b)).val ∈ D
    let r (a a' : K) := ∃ u : U F v, a' = (u.val : K) * a
    have h (x : Coord F S) (a a' : K) (hr : r a a') : b.val (x,a) = b.val (x,a') := by
      obtain ⟨u,rfl⟩ := hr
      have hu := fixedOrbitAverage_fixed (splitUnitAction F S v) (unitHaar F v)
        (splitUnitAction_orbit F S v) (e ψ) u⁻¹
      exact congrArg (fun w : SplitTest F S v ↦ w.val (x,a)) hu |>.symm.trans (by
        change (splitUnitAction F S v u⁻¹ b).val (x,a) = b.val (x,(u.val : K) * a)
        simp [splitUnitAction, locallyConstantTestTranslate, inv_inv] <;> rfl)
    let L : SplitTest F S v →ₗ[ℂ] GlobalBruhat F :=
      (Test F T).subtype.comp ((sLocalBruhatPure F T φ).comp e.symm.toLinearMap)
    change b ∈ D.comap L
    have hb := locallyConstantTest_mem_span_product_of_invariant r b h
    apply (Submodule.span_le.mpr ?_) hb
    rintro _ ⟨p,q,hq,rfl⟩
    change L (locallyConstantTestProduct p q) ∈ D
    have hinv (a : K) (u : Kˣ) (hu : u ∈ finitePlaceIntegralUnits F v) :
        q.val (a * u.val) = q.val a := by
      apply (hq a (a * u.val) _).symm
      have hval : Valued.v u.val = 1 :=
        (localIntegralUnits_value F v u).mp hu
      exact ⟨⟨u, (finiteCompletion_norm_eq_one_iff F v u).mpr hval⟩, mul_comm _ _⟩
    obtain ⟨m,N,hq'⟩ := finiteValuationBallTest_expansion F v q hinv
    have hball (n : ℤ) : L (locallyConstantTestProduct p (finiteValuationBallTest F v n)) ∈ D := by
      change (sLocalBruhatPure F T φ (e.symm
        (locallyConstantTestProduct p (finiteValuationBallTest F v n)))).val ∈ D
      rw [finiteBall_stage_pure F S v hv]
      exact Submodule.subset_span ⟨n,sLocalBruhatPure F S φ p,rfl⟩
    let A := L.comp (locallyConstantTestProduct p)
    change A q ∈ D
    rw [hq', map_add, map_smul, map_sum]
    apply D.add_mem (D.smul_mem _ (hball _))
    apply Submodule.sum_mem
    intro n _
    rw [map_smul, map_sub]
    exact D.smul_mem _ (D.sub_mem (hball _) (hball _))

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

include hv in
/-- An observed test fixed by the additional integral units can be
represented at the smaller stage if all translated integer balls can. -/
theorem exists_sLocalBaseRepresentative_onePlace_of_fixed
    (L : GlobalBruhat F →ₗ[ℂ] Y)
    (f : Test F T)
    (hunit : ∀ (u : Kˣ), u ∈ finitePlaceIntegralUnits F v →
      L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u) f.val) = L f.val)
    (hshift : ∀ (n : ℤ) (f : Test F S), ∃ g : Test F S,
      L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)) f.val) =
        L g.val) : ∃ g : Test F S, L f.val = L g.val := by
  let P := L.comp (Test F S).subtype
  have hspan : uniformizerTranslateSpan F S v ≤ P.range.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,g,rfl⟩
    obtain ⟨g',hg'⟩ := hshift n g
    exact ⟨g',hg'.symm⟩
  have ha := hspan (unitAverage_mem_uniformizerTranslateSpan F S v hv f)
  change L (unitAverage F S v hv f).val ∈ P.range at ha
  have he : L (unitAverage F S v hv f).val = L f.val := by
    by_contra hn
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
    apply hl
    rw [map_sub]
    apply sub_eq_zero.mpr
    let B := l.comp (L.comp (Test F T).subtype)
    change B (unitAverage F S v hv f) = B f
    rw [unitAverage_apply]
    have hu (u : U F v) : B (unitTranslate F S v hv u f) = B f := by
      change l (L (unitTranslate F S v hv u f).val) = l (L f.val)
      rw [unitTranslate_eq_global F S v hv, hunit u.val _]
      exact (localIntegralUnits_value F v u.val).mpr
        ((finiteCompletion_norm_eq_one_iff F v u.val).mp u.property)
    simp only [hu, integral_const, measureReal_def, unitHaar_univ, ENNReal.toReal_one, one_smul]
  obtain ⟨g,hg⟩ := ha
  exact ⟨g, he.symm.trans hg.symm⟩

include hv in
/-- Eliminate an added place in a linear observation fixed by its integral
units when the uniformizer translates can be represented at the base stage. -/
theorem exists_sLocalBaseRepresentative_onePlace
    (L : GlobalBruhat F →ₗ[ℂ] Y)
    (hunit : ∀ (u : Kˣ), u ∈ finitePlaceIntegralUnits F v → ∀ f,
      L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u) f) = L f)
    (hshift : ∀ (n : ℤ) (f : Test F S), ∃ g : Test F S,
      L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)) f.val) =
        L g.val)
    (f : Test F T) : ∃ g : Test F S, L f.val = L g.val :=
  exists_sLocalBaseRepresentative_onePlace_of_fixed F S v hv L f (fun u hu ↦ hunit u hu f.val) hshift

private theorem transition_invariant (hv : v ∉ S) (f : Test F S) :
    sLocalThetaNewPlaceInvariant F S v (sLocalBruhatTransition F (Finset.subset_insert v S) f) := by
  intro x a u hu
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add b c hb hc => simp only [map_add, Submodule.coe_add, Pi.add_apply, hb, hc]
  | tmul φ ψ =>
    change stageEval F S v (x.1, joinCoord F S v x.2 (a * u.val))
      (sLocalBruhatTransition F (Finset.subset_insert v S) (sLocalBruhatPure F S φ ψ)) =
      stageEval F S v (x.1, joinCoord F S v x.2 a)
        (sLocalBruhatTransition F (Finset.subset_insert v S) (sLocalBruhatPure F S φ ψ))
    rw [sLocalBruhatTransition_pure]
    change sLocalBruhatRestriction F T (sLocalBruhatPure F T φ (sLocalFiniteExtend F S T ψ)).val
      (x.1, joinCoord F S v x.2 (a * u.val)) =
      sLocalBruhatRestriction F T (sLocalBruhatPure F T φ (sLocalFiniteExtend F S T ψ)).val
        (x.1, joinCoord F S v x.2 a)
    rw [sLocalBruhatPure_restrict, sLocalBruhatPure_restrict,
      finiteExtend_join F S v hv, finiteExtend_join F S v hv]
    have h : a * u.val ∈ v.adicCompletionIntegers F ↔ a ∈ v.adicCompletionIntegers F := by
      change Valued.v (a * u.val) ≤ 1 ↔ Valued.v a ≤ 1
      rw [map_mul, hu, mul_one]
    rw [h]

private theorem unitAverage_transition (f : Test F S) :
    unitAverage F S v hv (sLocalBruhatTransition F (Finset.subset_insert v S) f) =
      sLocalBruhatTransition F (Finset.subset_insert v S) f := by
  let b := sLocalBruhatTransition F (Finset.subset_insert v S) f
  apply stageEval_ext F S v
  intro z
  rw [unitAverage_apply]
  let x := stagePoint F S v hv z
  let a := z.2 ⟨v, Finset.mem_insert_self _ _⟩
  have ht (u : U F v) : stageEval F S v z (unitTranslate F S v hv u b) = stageEval F S v z b := by
    rw [← show (x.1, joinCoord F S v x.2 a) = z from stagePoint_join F S v hv z,
      unitTranslate_eval]
    have hu := (finiteCompletion_norm_eq_one_iff F v (u⁻¹ : U F v).val).mp (u⁻¹ : U F v).property
    change stageEval F S v (x.1, joinCoord F S v x.2 (u.val.inv * a)) b =
      stageEval F S v (x.1, joinCoord F S v x.2 a) b
    rw [mul_comm]
    exact transition_invariant F S v hv f x a u.val⁻¹ hu
  change (∫ u, stageEval F S v z (unitTranslate F S v hv u b) ∂unitHaar F v) =
    stageEval F S v z b
  simp only [ht, integral_const, measureReal_def, unitHaar_univ, ENNReal.toReal_one, one_smul]

/-- A continuous retraction of the theta quotient after one finite place is
adjoined. Averaging removes the local unit rotations before taking the signed slices. -/
def sLocalThetaStageRetraction (hv : v ∉ S) : SLocalThetaQuotient F T →L[ℂ] SLocalThetaQuotient F S := by
  let P := (sLocalThetaOperator F S).ker
  let Q := (sLocalThetaOperator F T).ker
  let R := (sLocalThetaStageTestRetraction F S v hv).comp (unitAverage F S v hv)
  refine Q.liftQL (P.mkQL.comp R) ?_
  intro f hf
  apply LinearMap.mem_ker.mpr
  apply (Submodule.Quotient.mk_eq_zero P).mpr
  apply LinearMap.mem_ker.mpr
  funext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  change sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S
    (sLocalThetaStageTestRetraction F S v hv (unitAverage F S v hv f)).val) g = 0
  rw [sLocalThetaStageTestRetraction_eval F S v hv _ (unitAverage_invariant F S v hv f) g]
  have h := LinearMap.mem_ker.mp (unitAverage_kernel F S v hv hf)
  let z := (sLocalEmbed F S g).val
  let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
  let p := Units.map (sAdelesProjection F T).toMonoidHom
  have h₀ := congrFun h (QuotientGroup.mk (p z))
  have h₁ := congrFun h (QuotientGroup.mk (p (z * c)))
  exact sub_eq_zero.mpr (h₀.trans h₁.symm)

theorem sLocalThetaStageRetraction_leftInverse :
    LeftInverse (sLocalThetaStageRetraction F S v hv)
      (sLocalThetaTransition F (Finset.subset_insert v S)) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let b := sLocalBruhatTransition F (Finset.subset_insert v S) f
  let R := sLocalThetaStageTestRetraction F S v hv
  change Submodule.Quotient.mk (R (unitAverage F S v hv b)) = Submodule.Quotient.mk f
  rw [unitAverage_transition F S v hv]
  apply (Submodule.Quotient.eq _).mpr
  apply LinearMap.mem_ker.mpr
  funext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  simp only [map_sub, Pi.sub_apply]
  apply sub_eq_zero.mpr
  change sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S (R b).val) g =
    sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g
  rw [sLocalThetaStageTestRetraction_eval F S v hv b (transition_invariant F S v hv f) g]
  exact sLocalTheta_onePlace_probe F S v hv f g

private theorem unitAverage_leftTranslate (a : (SAdeles F T)ˣ) (f : Test F T) :
    unitAverage F S v hv (sLocalBruhatLeftTranslate F T a f) =
      sLocalBruhatLeftTranslate F T a (unitAverage F S v hv f) := by
  let L := sLocalBruhatLeftTranslate F T a
  have h (u : U F v) : unitTranslate F S v hv u (L f) = L (unitTranslate F S v hv u f) := by
    apply Subtype.ext
    rw [unitTranslate_eq_global F S v hv]
    change GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val)
      (GlobalBruhat.leftTranslate F (sLocalEmbed F T a).val f.val) =
      GlobalBruhat.leftTranslate F (sLocalEmbed F T a).val (unitTranslate F S v hv u f).val
    rw [unitTranslate_eq_global F S v hv, globalBruhatLeftTranslate_mul,
      globalBruhatLeftTranslate_mul, mul_comm]
  change unitAverage F S v hv (L f) = L (unitAverage F S v hv f)
  by_contra hn
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
  apply hℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he := unitAverage_apply F S v hv f (ℓ.comp L.toLinearMap)
  rw [unitAverage_apply F S v hv]
  simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,h] using he.symm

private theorem thetaOnIdeles_leftTranslate (A : Finset (Place F))
    (a g : (SAdeles F A)ˣ) (f : Test F A) :
    sLocalThetaOnIdeles F A (sLocalBruhatRestriction F A (sLocalBruhatLeftTranslate F A a f).val) g =
      sLocalThetaOnIdeles F A (sLocalBruhatRestriction F A f.val) (a⁻¹*g) := by
  let π := QuotientGroup.mk' (sUnitImage F A)
  have h := sLocalThetaOperator_leftTranslate F A a f (π g)
  change sLocalThetaOperator F A _ (π g) = sLocalThetaOperator F A _ ((π a)⁻¹ * π g) at h
  rw [← map_inv, ← map_mul] at h
  exact h

/-- The one-place retraction intertwines every translation from the
smaller stage. The add-one-place average and shifted evaluations commute
with the old coordinates. -/
theorem sLocalThetaStageRetraction_translate (a : (SAdeles F S)ˣ) (q : SLocalThetaQuotient F T) :
    let aT := Units.map (sAdelesProjection F T).toMonoidHom (sLocalEmbed F S a).val
    sLocalThetaStageRetraction F S v hv (sLocalThetaTranslateIdeles F T aT q) =
      sLocalThetaTranslateIdeles F S a (sLocalThetaStageRetraction F S v hv q) := by
  intro aT
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let I := sLocalThetaStageTestRetraction F S v hv
  let b := unitAverage F S v hv f
  change Submodule.Quotient.mk (I (unitAverage F S v hv (sLocalBruhatLeftTranslate F T aT f))) =
    Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S a (I b))
  rw [unitAverage_leftTranslate F S v hv]
  apply (Submodule.Quotient.eq _).mpr
  apply LinearMap.mem_ker.mpr
  rw [map_sub, sub_eq_zero]
  funext c
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective c
  have h₁ := sLocalThetaStageTestRetraction_eval F S v hv
    (sLocalBruhatLeftTranslate F T aT b)
    (by rw [← unitAverage_leftTranslate F S v hv]; exact unitAverage_invariant F S v hv _) g
  have h₂ := sLocalThetaStageTestRetraction_eval F S v hv b
    (unitAverage_invariant F S v hv f) (a⁻¹ * g)
  let p := Units.map (sAdelesProjection F T).toMonoidHom
  let z := (sLocalEmbed F S g).val
  let d := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
  have hz : p (sLocalEmbed F S (a⁻¹ * g)).val = aT⁻¹ * p z := by
    change ((p.comp ((sIdeleBlock F S).subtype.comp (sLocalEmbed F S))) (a⁻¹ * g)) = _
    rw [map_mul,map_inv]
    rfl
  have hzd : p ((sLocalEmbed F S (a⁻¹ * g)).val * d) = aT⁻¹ * p (z*d) := by
    rw [map_mul,hz,map_mul,mul_assoc]
  change sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S (I _).val) g =
    sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S (sLocalBruhatLeftTranslate F S a (I b)).val) g
  rw [thetaOnIdeles_leftTranslate, h₁, h₂, thetaOnIdeles_leftTranslate, thetaOnIdeles_leftTranslate,
    hz, hzd]

/-- Each one-place transition is a topological embedding in the actual
quotient topology. -/
theorem sLocalThetaTransition_onePlace_isEmbedding (hv : v ∉ S) :
    IsEmbedding (sLocalThetaTransition F (Finset.subset_insert v S)) :=
  (sLocalThetaStageRetraction_leftInverse F S v hv).isEmbedding
    (sLocalThetaStageRetraction F S v hv).continuous
    (sLocalThetaTransition F (Finset.subset_insert v S)).continuous

/-- Point evaluation separates the actual S-local quotient. -/
theorem sLocalThetaQuotient_t2Space (A : Finset (Place F)) : T2Space (SLocalThetaQuotient F A) := by
  let L : SLocalThetaQuotient F A →ₗ[ℂ] ((SAdeles F A)ˣ → ℂ) :=
    LinearMap.pi (fun a ↦ (sLocalThetaQuotientEval F A a).toLinearMap)
  apply T2Space.of_injective_continuous (f := L)
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply LinearMap.mem_ker.mpr
    funext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    exact congrFun hq g
  · exact continuous_pi fun a ↦ (sLocalThetaQuotientEval F A a).continuous

/-- The range of a one-place transition is complemented and closed. -/
theorem sLocalThetaTransition_onePlace_isClosedEmbedding (hv : v ∉ S) :
    IsClosedEmbedding (sLocalThetaTransition F (Finset.subset_insert v S)) := by
  let j := sLocalThetaTransition F (Finset.subset_insert v S)
  let R := sLocalThetaStageRetraction F S v hv
  letI := sLocalThetaQuotient_t2Space F T
  refine ⟨sLocalThetaTransition_onePlace_isEmbedding F S v hv, ?_⟩
  have he : range j = {q | j (R q) = q} := by
    ext q
    refine ⟨?_, fun h ↦ ⟨R q, h⟩⟩
    rintro ⟨x, rfl⟩
    exact congrArg j (sLocalThetaStageRetraction_leftInverse F S v hv x)
  rw [he]
  exact isClosed_eq (j.continuous.comp R.continuous) continuous_id

theorem sLocalThetaTransition_refl (A : Finset (Place F)) :
    sLocalThetaTransition F (show A ⊆ A from le_rfl) = ContinuousLinearMap.id ℂ _ := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

theorem sLocalThetaTransition_comp {A B C : Finset (Place F)}
    (hAB : A ⊆ B) (hBC : B ⊆ C) :
    (sLocalThetaTransition F hBC).comp (sLocalThetaTransition F hAB) =
      sLocalThetaTransition F (hAB.trans hBC) := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

private theorem thetaRetraction_congr {A B C : Finset (Place F)} (hAB : A ⊆ B)
    (hAC : A ⊆ C) (he : B = C)
    (h : ∃ R : SLocalThetaQuotient F B →L[ℂ] SLocalThetaQuotient F A,
      LeftInverse R (sLocalThetaTransition F hAB)) :
    ∃ R : SLocalThetaQuotient F C →L[ℂ] SLocalThetaQuotient F A,
      LeftInverse R (sLocalThetaTransition F hAC) := by
  subst C
  exact h

private theorem thetaRetraction_union (A B : Finset (Place F)) (h : Disjoint B A) :
    ∃ R : SLocalThetaQuotient F (B ∪ A) →L[ℂ] SLocalThetaQuotient F A,
      LeftInverse R (sLocalThetaTransition F (show A ⊆ B ∪ A from Finset.subset_union_right)) := by
  induction B using Finset.induction_on with
  | empty =>
    apply thetaRetraction_congr F (show A ⊆ A from le_rfl) _ (Finset.empty_union A).symm
    exact ⟨ContinuousLinearMap.id ℂ _, by rw [sLocalThetaTransition_refl]; exact fun _ ↦ rfl⟩
  | insert v B hvB ih =>
    rw [Finset.disjoint_insert_left] at h
    let hAB : A ⊆ B ∪ A := Finset.subset_union_right
    let hBC : B ∪ A ⊆ insert v (B ∪ A) := Finset.subset_insert _ _
    apply thetaRetraction_congr F (hAB.trans hBC) _ (Finset.insert_union _ _ _).symm
    rw [← sLocalThetaTransition_comp F hAB hBC]
    obtain ⟨R, hR⟩ := ih h.2
    have hv : v ∉ B ∪ A := by simp [hvB, h.1]
    let Q := sLocalThetaStageRetraction F (B ∪ A) v hv
    refine ⟨R.comp Q, fun q ↦ ?_⟩
    change R (Q (sLocalThetaTransition F hBC (sLocalThetaTransition F hAB q))) = q
    rw [sLocalThetaStageRetraction_leftInverse F (B ∪ A) v hv, hR]

/-- Each inclusion of finite theta stages admits a continuous linear retraction. -/
theorem sLocalThetaTransition_exists_retraction {A B : Finset (Place F)} (h : A ⊆ B) :
    ∃ R : SLocalThetaQuotient F B →L[ℂ] SLocalThetaQuotient F A,
      LeftInverse R (sLocalThetaTransition F h) :=
  thetaRetraction_congr F Finset.subset_union_right h (Finset.sdiff_union_of_subset h)
    (thetaRetraction_union F A (B \ A) Finset.sdiff_disjoint)

/-- All finite-stage transitions of the ordinary theta quotient are closed
topological embeddings. -/
theorem sLocalThetaTransition_isClosedEmbedding {A B : Finset (Place F)} (h : A ⊆ B) :
    IsClosedEmbedding (sLocalThetaTransition F h) := by
  obtain ⟨R, hR⟩ := sLocalThetaTransition_exists_retraction F h
  let j := sLocalThetaTransition F h
  letI := sLocalThetaQuotient_t2Space F B
  refine ⟨hR.isEmbedding R.continuous j.continuous, ?_⟩
  have he : range j = {q | j (R q) = q} := by
    ext q
    refine ⟨?_, fun h ↦ ⟨R q, h⟩⟩
    rintro ⟨x, rfl⟩
    exact congrArg j (hR x)
  rw [he]
  exact isClosed_eq (j.continuous.comp R.continuous) continuous_id

end

end Masullo
