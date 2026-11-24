import IdeleIdealClasses
import Regulator
import Mathlib.Algebra.Module.NatInt

open Filter Function IsDedekindDomain Module NumberField Set Topology
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}
private abbrev InfiniteUnits := (InfiniteAdeleRing F)ˣ
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

/-- Put the two groups of logarithmic coordinates back into one vector,
indexed by the infinite places. -/
def splitArchLog (l : InfinitePlace F → ℝ) :
    (RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ) :=
  (fun v => Multiplicative.ofAdd (l v), fun v => Multiplicative.ofAdd (l v))

omit [NumberField F] in
theorem splitArchLog_continuous : Continuous (splitArchLog F) := by
  apply Continuous.prodMk <;> apply continuous_pi <;>
    intro v <;> exact continuous_ofAdd.comp (continuous_apply v.val)

omit [NumberField F] in
theorem splitArchLog_injective : Injective (splitArchLog F) := by
  intro x y h
  funext v
  by_cases hv : v.IsReal
  · exact congrArg (fun p : (RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ) =>
      Multiplicative.toAdd (p.1 ⟨v, hv⟩)) h
  · exact congrArg (fun p : (RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ) =>
      Multiplicative.toAdd (p.2 ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩)) h

def fullArchLog (a : InfiniteUnits F) (v : InfinitePlace F) : ℝ :=
  (v.mult : ℝ) * Real.log ‖a.val v‖

omit [NumberField F] in
theorem split_fullArchLog (a : InfiniteUnits F) :
    splitArchLog F (fullArchLog F a) = infiniteIdeleArchLog F a := by
  apply Prod.ext
  · funext v
    change Multiplicative.ofAdd ((v.val.mult : ℝ) * Real.log ‖a.val v.val‖) =
      Multiplicative.ofAdd (1 * Real.log ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal v.property
        (a.val v.val)‖)
    rw [v.property.mult_eq_one, Nat.cast_one,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.property).norm_map_of_map_zero
        (map_zero _)]
  · funext v
    change Multiplicative.ofAdd ((v.val.mult : ℝ) * Real.log ‖a.val v.val‖) =
      Multiplicative.ofAdd (2 * Real.log ‖InfinitePlace.Completion.extensionEmbedding v.val (a.val v.val)‖)
    rw [v.property.mult_eq_two, Nat.cast_ofNat,
      (InfinitePlace.Completion.isometry_extensionEmbedding v.val).norm_map_of_map_zero (map_zero _)]

omit [NumberField F] in
theorem fullArchLog_mul (a b : InfiniteUnits F) :
    fullArchLog F (a * b) = fullArchLog F a + fullArchLog F b := by
  apply splitArchLog_injective F
  have h : splitArchLog F (fullArchLog F a + fullArchLog F b) =
      splitArchLog F (fullArchLog F a) * splitArchLog F (fullArchLog F b) := rfl
  rw [split_fullArchLog, h, split_fullArchLog, split_fullArchLog, map_mul]

omit [NumberField F] in
theorem infiniteCoord_nonzero (a : InfiniteUnits F) (v : InfinitePlace F) :
    a.val v ≠ 0 := by
  have h := congrArg (fun x : InfiniteAdeleRing F => x v) a.val_inv
  change a.val v * a.inv v = 1 at h
  exact left_ne_zero_of_mul_eq_one h

theorem fullArchLog_sum (a : InfiniteUnits F) :
    ∑ v, fullArchLog F a v = Real.log ‖a.val‖ := by
  rw [InfiniteAdeleRing.norm_def, Real.log_prod (fun v _ =>
    pow_ne_zero _ (norm_ne_zero_iff.mpr (infiniteCoord_nonzero F a v)))]
  exact Finset.sum_congr rfl fun v _ => (Real.log_pow _ _).symm

theorem fullArchLog_mem_hyperplane (a : InfiniteUnits F) (h : ‖a.val‖ = 1) :
    fullArchLog F a ∈ regulatorHyperplane F := by
  change (∑ v : InfinitePlace F, LinearMap.proj v) (fullArchLog F a) = 0
  rw [LinearMap.sum_apply]
  change ∑ v, fullArchLog F a v = 0
  rw [fullArchLog_sum F a, h, Real.log_one]

def fieldToArch : Fˣ →* InfiniteUnits F :=
  Units.map (algebraMap F (InfiniteAdeleRing F))

theorem fullArchLog_unit (u : (𝓞 F)ˣ) :
    ∃ l : regulatorHyperplane F, l.val = fullArchLog F (fieldToArch F (integralUnitToField F u)) ∧
      regulatorHyperplaneEquiv F l = logEmbedding F (Additive.ofMul u) := by
  obtain ⟨l, hl, hu⟩ := regulator_coordinates F u
  refine ⟨l, funext fun v => ?_, hu⟩
  rw [hl]
  change (v.mult : ℝ) * Real.log (v (u : F)) =
    (v.mult : ℝ) * Real.log ‖algebraMap F v.Completion (u : F)‖
  have h := InfinitePlace.Completion.norm_coe (v := v) ((WithAbs.equiv v.1).symm (u : F))
  change ‖algebraMap F v.Completion (u : F)‖ = v (WithAbs.equiv v.1 ((WithAbs.equiv v.1).symm (u : F))) at h
  have hn : ‖algebraMap F v.Completion (u : F)‖ = v (u : F) :=
    h.trans (congrArg (fun z : F => v z) ((WithAbs.equiv v.1).apply_symm_apply (u : F)))
  exact congrArg (fun r : ℝ => (v.mult : ℝ) * Real.log r) hn.symm

def regToArchLog (x : logSpace F) :=
  splitArchLog F ((regulatorHyperplaneEquiv F).symm x).val

theorem regToArchLog_continuous : Continuous (regToArchLog F) :=
  (splitArchLog_continuous F).comp
    (continuous_subtype_val.comp (regulatorHyperplaneEquiv F).symm.continuous)

/-- A compact set containing representatives of all norm-one
Archimedean ideles modulo global integral units. -/
theorem archNormOne_compact_representatives :
    ∃ K : Set (InfiniteUnits F), IsCompact K ∧
      ∀ a : InfiniteUnits F, ‖a.val‖ = 1 →
        ∃ u : (𝓞 F)ˣ, fieldToArch F (integralUnitToField F u) * a ∈ K := by
  let P := ZSpan.fundamentalDomain (regulatorBasis F)
  let K := infiniteIdeleArchLog F ⁻¹' (regToArchLog F '' closure P)
  obtain ⟨hc, _, ht⟩ := regulator_fundamentalDomain F
  refine ⟨K, (infiniteIdeleArchLog_proper F).isCompact_preimage
    (hc.image (regToArchLog_continuous F)), ?_⟩
  intro a ha
  let A : regulatorHyperplane F := ⟨fullArchLog F a, fullArchLog_mem_hyperplane F a ha⟩
  let x := regulatorHyperplaneEquiv F A
  obtain ⟨v, hv, _⟩ := ht x
  obtain ⟨u, _, hu⟩ := Submodule.mem_map.mp v.property
  change logEmbedding F u = (v : logSpace F) at hu
  obtain ⟨l, hl, hreg⟩ := fullArchLog_unit F (Additive.toMul u)
  change regulatorHyperplaneEquiv F l = logEmbedding F u at hreg
  refine ⟨Additive.toMul u, ?_⟩
  change infiniteIdeleArchLog F (fieldToArch F (integralUnitToField F (Additive.toMul u)) * a)
    ∈ regToArchLog F '' closure P
  refine ⟨(v : logSpace F) + x, subset_closure hv, ?_⟩
  have he : (regulatorHyperplaneEquiv F).symm ((v : logSpace F) + x) = l + A := by
    rw [map_add, show x = regulatorHyperplaneEquiv F A from rfl,
      ContinuousLinearEquiv.symm_apply_apply, ← hu, ← hreg, ContinuousLinearEquiv.symm_apply_apply]
  unfold regToArchLog
  rw [he, ← split_fullArchLog, fullArchLog_mul, ← hl]
  rfl


private theorem arch_principal_mul (t : Fˣ) (b : Idele F) :
    (Homeomorph.prodUnits (principalIdele F t * b)).1 =
      fieldToArch F t * (Homeomorph.prodUnits b).1 := rfl

private theorem principal_class_one (t : Fˣ) : ideleClassMap F (principalIdele F t) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩

private theorem normOnePart_of_normOne (a : normOneIdeleClass F) :
    ideleClassNormOnePart F a.val = a := by
  have h : ideleClassLogNorm F a.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F a.val)) = Multiplicative.ofAdd 0
    rw [show ideleClassNorm F a.val = 1 from a.property, Real.log_one]
  apply Subtype.ext
  change a.val / ideleClassExpSection F (ideleClassLogNorm F a.val) = a.val
  rw [h, map_one, div_one]

/-- The norm-one class group is the continuous image of a finite union
of compact adelic blocks coming from the regulator and ideal classes. -/
theorem normOneIdeleClass_compact : CompactSpace (normOneIdeleClass F) := by
  letI : Finite (ClassGroup (𝓞 F)) := inferInstance
  let cl := (ideleIdealClass F).comp (ideleNorm F).ker.subtype
  choose g hg using ideleNormOne_idealClass_surjective F
  obtain ⟨K, hK, hcover⟩ := archNormOne_compact_representatives F
  let U : Set (FinAdeles F)ˣ := (finiteIntegralSubmonoid F).units
  let B : Set (Idele F) := Homeomorph.prodUnits ⁻¹' (K ×ˢ U)
  have hB : IsCompact B := Homeomorph.prodUnits.isCompact_preimage.mpr
    (hK.prod (finiteIntegralUnits_compact (F := F)))
  let D := ⋃ c : ClassGroup (𝓞 F), (fun b : Idele F => (g c).val * b) '' B
  have hD : IsCompact D := isCompact_iUnion fun c => hB.image
    (continuous_const.mul continuous_id)
  let f := ideleClassNormOnePart F ∘ ideleClassMap F
  have hf : Continuous f :=
    ((ideleClassSplitHomeomorph F).continuous.fst).comp (ideleClassMap_continuous F)
  apply isCompact_univ_iff.mp
  have hsur : f '' D = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨a₀, hay⟩ := ideleClassMap_surjective F y.val
    let a : (ideleNorm F).ker := ⟨a₀, by
      change ideleNorm F a₀ = 1
      rw [← ideleClassNorm_mk, hay]
      exact y.property⟩
    let c := cl a
    have hx : cl ((g c)⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, show cl (g c) = c from hg c]
      exact inv_mul_cancel c
    obtain ⟨t, b, hb, he⟩ := (ideleNormOne_idealClass_ker_iff F _).mp hx
    have ha : a.val = (g c).val * (principalIdele F t * b.val) := by
      change (g c).val⁻¹ * a.val = _ at he
      rw [← he, mul_inv_cancel_left]
    obtain ⟨u, hu⟩ := hcover (Homeomorph.prodUnits b.val).1 hb
    let e := principalIdele F (integralUnitToField F u)
    have hie : e ∈ (ideleDivisor F).ker :=
      (principalIdele_integral_iff F _).mpr ⟨u, rfl⟩
    have hb' : e * b.val ∈ B := by
      change Homeomorph.prodUnits (e * b.val) ∈ K ×ˢ U
      exact ⟨(arch_principal_mul F _ _) ▸ hu,
        (ideleDivisor_ker_iff_prodUnits F _).mp ((ideleDivisor F).ker.mul_mem hie b.property)⟩
    refine ⟨(g c).val * (e * b.val), mem_iUnion.mpr ⟨c, ⟨e * b.val, hb', rfl⟩⟩, ?_⟩
    have hp : ideleClassMap F ((g c).val * (e * b.val)) = y.val := by
      have hqa : ideleClassMap F a.val = y.val := hay
      rw [ha] at hqa
      simpa only [e, map_mul, principal_class_one] using hqa
    change ideleClassNormOnePart F _ = y
    rw [hp, normOnePart_of_normOne]
  rw [← hsur]
  exact hD.image hf

/-- The three assertions of Theorem A.1.4.3 for a number field. -/
theorem normOneIdeleClass_and_arithmetic_finiteness :
    CompactSpace (normOneIdeleClass F) ∧ T2Space (normOneIdeleClass F) ∧
    Monoid.FG (𝓞 F)ˣ ∧
    @finrank ℤ (Additive ((𝓞 F)ˣ ⧸ NumberField.Units.torsion F)) _ _
      (AddCommGroup.toIntModule _) =
      InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1 ∧
    Finite (ClassGroup (𝓞 F)) := by
  letI : T2Space (IdeleClass F) := ideleClasses_hausdorff
  refine ⟨normOneIdeleClass_compact F, inferInstance, inferInstance, ?_, inferInstance⟩
  rw [finrank_modTorsion, NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

end

end Masullo
