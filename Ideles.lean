import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped NumberField RestrictedProduct

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

/-- Appendix A.1.3 uses the topology on units induced by the pair
of the value and its inverse. Mathlib's unit topology is exactly this one. -/
abbrev Idele := (NumberField.AdeleRing (𝓞 F) F)ˣ

/-- The diagonal embedding of principal ideles, as in (A.1.3.5). -/
def principalIdele : Fˣ →* Idele F :=
  Units.map (algebraMap F (NumberField.AdeleRing (𝓞 F) F))

theorem principalIdele_injective : Function.Injective (principalIdele F) := by
  intro x y h
  apply Units.ext
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Units.val h)

/-- The subgroup of principal ideles. -/
def principalIdeles : Subgroup (Idele F) := (principalIdele F).range

/-- The quotient in Definition A.1.4.1, with Mathlib's quotient group topology. -/
abbrev IdeleClass := Idele F ⧸ principalIdeles F

def ideleClassMap : Idele F →* IdeleClass F :=
  QuotientGroup.mk' (principalIdeles F)

theorem ideleClassMap_surjective : Function.Surjective (ideleClassMap F) :=
  QuotientGroup.mk_surjective

theorem ideleClassMap_continuous : Continuous (ideleClassMap F) :=
  QuotientGroup.continuous_mk

private def finitePart : Idele F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map {
    toFun := fun x => x.2
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private theorem finiteValue_isUnit (a : Idele F) : IsUnit a.val.2 :=
  (finitePart F a).isUnit

/-- Finite-place norm factors are one away from finitely many places. -/
theorem finiteIdeleNorm_hasFiniteMulSupport (a : Idele F) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖a.val.2 v‖).HasFiniteMulSupport := by
  change {v : HeightOneSpectrum (𝓞 F) | ¬‖a.val.2 v‖ = 1}.Finite
  rw [← Filter.eventually_cofinite]
  filter_upwards [(FiniteAdeleRing.isUnit_iff.mp (finiteValue_isUnit F a)).2] with v hv
  rw [FinitePlace.norm_def, hv]
  simp

/-- The global modulus in (A.1.3.3), with squared complex-place norms. -/
def ideleNorm : Idele F →* ℝ where
  toFun a := (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖a.val.2 v‖
  map_one' := by
    change (∏ v : InfinitePlace F, ‖(1 : v.Completion)‖ ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : v.adicCompletion F)‖) = 1
    simp
  map_mul' a b := by
    change (∏ v : InfinitePlace F, ‖a.val.1 v * b.val.1 v‖ ^ v.mult) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖a.val.2 v * b.val.2 v‖) = _
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib,
      finprod_mul_distrib (finiteIdeleNorm_hasFiniteMulSupport F a)
        (finiteIdeleNorm_hasFiniteMulSupport F b)]
    ac_rfl

theorem ideleNorm_pos (a : Idele F) : 0 < ideleNorm F a := by
  have hf := (FiniteAdeleRing.isUnit_iff.mp (finiteValue_isUnit F a)).1
  have hi (v : InfinitePlace F) : a.val.1 v ≠ 0 := by
    have h : a.val.1 v * a.inv.1 v = 1 := by
      exact congrArg (fun x : NumberField.AdeleRing (𝓞 F) F => x.1 v) a.val_inv
    intro hv
    simp [hv] at h
  change 0 < (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖a.val.2 v‖
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (finiteIdeleNorm_hasFiniteMulSupport F a).toFinset)
    (fun _ h => (Set.Finite.mem_toFinset _).mpr h)]
  exact mul_pos (Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.mpr (hi v)) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (hf v))

theorem ideleNorm_principal (a : Fˣ) : ideleNorm F (principalIdele F a) = 1 := by
  change ‖algebraMap F (InfiniteAdeleRing F) (a : F)‖ *
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v‖) = 1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm]
  have h : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(algebraMap F
      (FiniteAdeleRing (𝓞 F) F) (a : F)) v‖) = ∏ᶠ w : FinitePlace F, w (a : F) := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FiniteAdeleRing.algebraMap_apply, FinitePlace.equivHeightOneSpectrum_symm_apply]
    rfl
  rw [h, FinitePlace.prod_eq_inv_abs_norm a.ne_zero]
  have hnorm : (Algebra.norm ℚ (a : F) : ℚ) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr a.ne_zero
  have hnormReal : ((|(Algebra.norm ℚ) (a : F)| : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr hnorm
  rw [Rat.cast_inv]
  exact mul_inv_cancel₀ hnormReal

private theorem norm_finite_eq_one_of_integral_pair (a : Idele F)
    (v : HeightOneSpectrum (𝓞 F)) (hx : a.val.2 v ∈ v.adicCompletionIntegers F)
    (hy : a.inv.2 v ∈ v.adicCompletionIntegers F) :
    ‖a.val.2 v‖ = 1 := by
  have hmul : a.val.2 v * a.inv.2 v = 1 := by
    exact congrArg (fun x : NumberField.AdeleRing (𝓞 F) F => x.2 v) a.val_inv
  have hx' : Valued.v (a.val.2 v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hx
  have hy' : Valued.v (a.inv.2 v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hy
  have hval : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul, hmul, map_one]
  have hv : Valued.v (a.val.2 v) = 1 := le_antisymm hx' <| calc
    1 = Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) := hval.symm
    _ ≤ Valued.v (a.val.2 v) := mul_le_of_le_one_right (zero_le) hy'
  rw [FinitePlace.norm_def, hv]
  simp

/-- The finite part of the modulus is a finite product on a neighborhood of
each idele. Both the value and inverse must be integral outside that finite set. -/
private theorem finiteNorm_continuous :
    Continuous (fun a : Idele F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖a.val.2 v‖) := by
  classical
  refine continuous_iff_continuousAt.mpr fun a => ?_
  let U := {v : HeightOneSpectrum (𝓞 F) |
    ¬(a.val.2 v ∈ v.adicCompletionIntegers F ∧ a.inv.2 v ∈ v.adicCompletionIntegers F)}
  have hfinite : U.Finite := by
    show {v : HeightOneSpectrum (𝓞 F) |
      ¬(a.val.2 v ∈ v.adicCompletionIntegers F ∧ a.inv.2 v ∈ v.adicCompletionIntegers F)}.Finite
    rw [← Filter.eventually_cofinite]
    exact a.val.2.2.and a.inv.2.2
  let S := hfinite.toFinset
  let V := {x : FiniteAdeleRing (𝓞 F) F | ∀ v ∉ S, x v ∈ v.adicCompletionIntegers F}
  have hV : IsOpen V := by
    change IsOpen {x : Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F] |
      ∀ v, v ∉ S → x.1 v ∈ v.adicCompletionIntegers F}
    exact RestrictedProduct.isOpen_forall_imp_mem (fun _ => Valued.isOpen_valuationSubring _)
  have hVval : a.val.2 ∈ V := fun v hv => by
    by_contra hn
    exact hv ((Set.Finite.mem_toFinset hfinite).mpr (fun h => hn h.1))
  have hVinv : a.inv.2 ∈ V := fun v hv => by
    by_contra hn
    exact hv ((Set.Finite.mem_toFinset hfinite).mpr (fun h => hn h.2))
  have hval : Continuous (fun b : Idele F => b.val.2) :=
    continuous_snd.comp Units.continuous_val
  have hinv : Continuous (fun b : Idele F => b.inv.2) :=
    continuous_snd.comp Units.continuous_coe_inv
  have hlocal :
      (fun b : Idele F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖b.val.2 v‖) =ᶠ[𝓝 a]
        (fun b : Idele F => ∏ v ∈ S, ‖b.val.2 v‖) := by
    filter_upwards [hval.continuousAt (hV.mem_nhds hVval),
      hinv.continuousAt (hV.mem_nhds hVinv)] with b hxb hyb
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hn
    exact hv (norm_finite_eq_one_of_integral_pair F b v (hxb v hn) (hyb v hn))
  apply (continuousAt_congr hlocal).mpr
  apply Continuous.continuousAt
  apply continuous_finsetProd
  intro v _
  exact (RestrictedProduct.continuous_eval v).norm.comp hval

theorem ideleNorm_continuous : Continuous (ideleNorm F) := by
  change Continuous (fun a : Idele F => (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖a.val.2 v‖)
  refine (continuous_finsetProd _ (fun v _ => ?_)).mul (finiteNorm_continuous F)
  have hval : Continuous (fun a : Idele F => a.val.1) :=
    continuous_fst.comp Units.continuous_val
  exact ((continuous_apply v).comp hval).norm.pow _

/-- The norm-one ideles form a closed subgroup, as in Lemma A.1.3.3. -/
theorem ideles_normOne_isClosed : IsClosed ((ideleNorm F).ker : Set (Idele F)) :=
  isClosed_eq (ideleNorm_continuous F) continuous_const

/-- The product formula descends the modulus to the idele class group. -/
def ideleClassNorm : IdeleClass F →* ℝ :=
  QuotientGroup.lift (principalIdeles F) (ideleNorm F) (by
    rintro _ ⟨a, rfl⟩
    exact ideleNorm_principal F a)

@[simp] theorem ideleClassNorm_mk (a : Idele F) :
    ideleClassNorm F (ideleClassMap F a) = ideleNorm F a := rfl

theorem ideleClassNorm_pos (a : IdeleClass F) : 0 < ideleClassNorm F a := by
  obtain ⟨x, rfl⟩ := ideleClassMap_surjective F a
  exact ideleNorm_pos F x

theorem ideleClassNorm_continuous : Continuous (ideleClassNorm F) := by
  apply (QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff.mpr
  exact ideleNorm_continuous F

open InfinitePlace in
private def realAtInfinitePlace (v : InfinitePlace F) : ℝ →+* v.Completion := by
  classical
  exact if h : IsReal v then (Completion.ringEquivRealOfIsReal h).symm.toRingHom
    else (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp
      Complex.ofRealHom

open InfinitePlace in
omit [NumberField F] in
private theorem realAtInfinitePlace_isometry (v : InfinitePlace F) :
    Isometry (realAtInfinitePlace F v) := by
  classical
  by_cases h : IsReal v
  · rw [realAtInfinitePlace, dite_eq_left h]
    exact (Completion.isometryEquivRealOfIsReal h).symm.isometry
  · rw [realAtInfinitePlace, dite_eq_right h]
    exact (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm.isometry.comp
      Complex.isometry_ofReal

/-- The real scalar embedding in an infinite completion, for both types of place. -/
abbrev infinitePlaceRealEmbedding (v : InfinitePlace F) : ℝ →+* v.Completion :=
  realAtInfinitePlace F v

theorem infinitePlaceRealEmbedding_isometry (v : InfinitePlace F) :
    Isometry (infinitePlaceRealEmbedding F v) :=
  realAtInfinitePlace_isometry F v

private def realScalarAdele : ℝ →* NumberField.AdeleRing (𝓞 F) F where
  toFun t := (fun v => realAtInfinitePlace F v t, 1)
  map_one' := by
    change (fun v => realAtInfinitePlace F v 1, (1 : FiniteAdeleRing (𝓞 F) F)) = (1, 1)
    simp [Pi.one_def]
  map_mul' a b := by
    change (fun v => realAtInfinitePlace F v (a * b), (1 : FiniteAdeleRing (𝓞 F) F)) =
      ((fun v => realAtInfinitePlace F v a) * (fun v => realAtInfinitePlace F v b), 1 * 1)
    simp [Pi.mul_def]

private theorem realScalarAdele_continuous : Continuous (realScalarAdele F) :=
  (continuous_pi fun v => (realAtInfinitePlace_isometry F v).continuous).prodMk continuous_const

private theorem ideleNorm_realScalar (t : ℝˣ) :
    ideleNorm F (Units.map (realScalarAdele F) t) = |(t : ℝ)| ^ Module.finrank ℚ F := by
  change (∏ v : InfinitePlace F, ‖realAtInfinitePlace F v (t : ℝ)‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : v.adicCompletion F)‖) = _
  simp_rw [(realAtInfinitePlace_isometry F _).norm_map_of_map_zero (map_zero _)]
  rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : v.adicCompletion F)‖) = 1 by simp,
    mul_one, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, Real.norm_eq_abs]

private def positiveExpUnit : Multiplicative ℝ →* ℝˣ where
  toFun t := Units.mk0 (Real.exp (Multiplicative.toAdd t / Module.finrank ℚ F))
    (Real.exp_pos _).ne'
  map_one' := by ext; simp
  map_mul' a b := by
    apply Units.ext
    change Real.exp ((Multiplicative.toAdd a + Multiplicative.toAdd b) /
      Module.finrank ℚ F) = Real.exp _ * Real.exp _
    rw [add_div, Real.exp_add]

private theorem positiveExpUnit_continuous : Continuous (positiveExpUnit F) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun t : Multiplicative ℝ =>
      Real.exp (Multiplicative.toAdd t / Module.finrank ℚ F)) :=
    Real.continuous_exp.comp (continuous_toAdd.div_const _)
  exact ⟨h, h.inv₀ fun _ => (Real.exp_pos _).ne'⟩

/-- A continuous homomorphic section of the idelic modulus, parametrized by
the logarithm of the positive real coordinate. -/
def ideleExpSection : Multiplicative ℝ →* Idele F :=
  (Units.map (realScalarAdele F)).comp (positiveExpUnit F)

theorem ideleExpSection_continuous : Continuous (ideleExpSection F) :=
  ((realScalarAdele_continuous F).units_map _).comp (positiveExpUnit_continuous F)

theorem ideleNorm_expSection (t : Multiplicative ℝ) :
    ideleNorm F (ideleExpSection F t) = Real.exp (Multiplicative.toAdd t) := by
  change ideleNorm F (Units.map (realScalarAdele F) (positiveExpUnit F t)) = _
  rw [ideleNorm_realScalar]
  change |Real.exp (Multiplicative.toAdd t / Module.finrank ℚ F)| ^ Module.finrank ℚ F = _
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 1
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := F)).ne'
  rw [mul_comm, div_mul_cancel₀ _ hd]

/-- The canonical section has the same real scalar at every infinite place,
and has component one at every finite place, as in Lemma A.2.2.4. -/
theorem ideleExpSection_components (t : Multiplicative ℝ) :
    (∀ v, (ideleExpSection F t).val.1 v = realAtInfinitePlace F v
      (Real.exp (Multiplicative.toAdd t / Module.finrank ℚ F))) ∧
    (ideleExpSection F t).val.2 = 1 := ⟨fun _ => rfl, rfl⟩

/-- In mixed coordinates the canonical norm section is ordinary positive
real scalar multiplication at the Archimedean component. -/
theorem ideleExpSection_mixed (t : Multiplicative ℝ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (ideleExpSection F t).val.1 =
      Real.exp (Multiplicative.toAdd t / Module.finrank ℚ F) •
        (1 : mixedEmbedding.mixedSpace F) := by
  classical
  let a := Real.exp (Multiplicative.toAdd t / Module.finrank ℚ F)
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply Prod.ext
  · funext v
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      ((ideleExpSection F t).val.1 v) = a * 1
    rw [(ideleExpSection_components F t).1]
    rw [realAtInfinitePlace, dite_eq_left v.property, mul_one]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal v.property).apply_symm_apply a
  · funext v
    change InfinitePlace.Completion.extensionEmbedding v.val
      ((ideleExpSection F t).val.1 v) = (a : ℂ) * 1
    rw [(ideleExpSection_components F t).1]
    have hn := InfinitePlace.not_isReal_iff_isComplex.mpr v.property
    rw [realAtInfinitePlace, dite_eq_right hn, mul_one]
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property).apply_symm_apply a

private def archimedeanExpAdele (w : InfinitePlace F → ℝ) :
    Multiplicative ℝ →* NumberField.AdeleRing (𝓞 F) F where
  toFun t := (fun v => realAtInfinitePlace F v (Real.exp (Multiplicative.toAdd t * w v)), 1)
  map_one' := by
    change (fun v => realAtInfinitePlace F v (Real.exp (0 * w v)), (1 : FiniteAdeleRing (𝓞 F) F)) = (1, 1)
    simp [Pi.one_def]
  map_mul' a b := by
    apply Prod.ext
    · funext v
      change realAtInfinitePlace F v (Real.exp ((Multiplicative.toAdd a + Multiplicative.toAdd b) * w v)) =
        realAtInfinitePlace F v (Real.exp (Multiplicative.toAdd a * w v)) *
          realAtInfinitePlace F v (Real.exp (Multiplicative.toAdd b * w v))
      rw [add_mul, Real.exp_add, map_mul]
    · exact (mul_one (1 : FiniteAdeleRing (𝓞 F) F)).symm

/-- Place-dependent exponents for a section of the idelic norm. -/
def archimedeanExpSection (w : InfinitePlace F → ℝ) : Multiplicative ℝ →* Idele F :=
  (archimedeanExpAdele F w).toHomUnits

theorem archimedeanExpSection_components (w : InfinitePlace F → ℝ) (t : Multiplicative ℝ) :
    (∀ v, (archimedeanExpSection F w t).val.1 v =
      realAtInfinitePlace F v (Real.exp (Multiplicative.toAdd t * w v))) ∧
    (archimedeanExpSection F w t).val.2 = 1 := ⟨fun _ => rfl, rfl⟩

theorem archimedeanExpSection_arch_norm (w : InfinitePlace F → ℝ) (t : Multiplicative ℝ)
    (v : InfinitePlace F) :
    ‖(archimedeanExpSection F w t).val.1 v‖ =
      Real.exp (Multiplicative.toAdd t * w v) := by
  rw [(archimedeanExpSection_components F w t).1 v,
    (realAtInfinitePlace_isometry F v).norm_map_of_map_zero (map_zero _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem archimedeanExpSection_continuous (w : InfinitePlace F → ℝ) :
    Continuous (archimedeanExpSection F w) := by
  have h : Continuous (archimedeanExpAdele F w) :=
    (continuous_pi fun v => (realAtInfinitePlace_isometry F v).continuous.comp
      (Real.continuous_exp.comp (continuous_toAdd.mul_const (w v)))).prodMk continuous_const
  exact Units.continuous_iff.mpr ⟨h, h.comp continuous_inv⟩

theorem ideleNorm_archimedeanExpSection (w : InfinitePlace F → ℝ) (t : Multiplicative ℝ) :
    ideleNorm F (archimedeanExpSection F w t) =
      Real.exp (Multiplicative.toAdd t * ∑ v : InfinitePlace F, w v * (v.mult : ℝ)) := by
  change (∏ v : InfinitePlace F,
    ‖realAtInfinitePlace F v (Real.exp (Multiplicative.toAdd t * w v))‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : v.adicCompletion F)‖) = _
  simp_rw [(realAtInfinitePlace_isometry F _).norm_map_of_map_zero (map_zero _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : v.adicCompletion F)‖) = 1 by simp,
    mul_one, ← Real.exp_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

open scoped Classical in
/-- The section concentrated at one infinite place, as in Definition A.2.2.5. -/
def onePlaceExpSection (v : InfinitePlace F) : Multiplicative ℝ →* Idele F :=
  archimedeanExpSection F fun w => if w = v then (v.mult : ℝ)⁻¹ else 0

theorem onePlaceExpSection_continuous (v : InfinitePlace F) :
    Continuous (onePlaceExpSection F v) := archimedeanExpSection_continuous F _

theorem ideleNorm_onePlaceExpSection (v : InfinitePlace F) (t : Multiplicative ℝ) :
    ideleNorm F (onePlaceExpSection F v t) = Real.exp (Multiplicative.toAdd t) := by
  classical
  rw [onePlaceExpSection, ideleNorm_archimedeanExpSection]
  have hv : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
  simp [ite_mul, hv]

/-- The section distributing the logarithmic norm equally among the infinite
places, as in Definition A.2.2.7. -/
def diagonalExpSection : Multiplicative ℝ →* Idele F :=
  archimedeanExpSection F fun v => ((v.mult : ℝ) * Fintype.card (InfinitePlace F))⁻¹

theorem diagonalExpSection_continuous : Continuous (diagonalExpSection F) :=
  archimedeanExpSection_continuous F _

theorem ideleNorm_diagonalExpSection (t : Multiplicative ℝ) :
    ideleNorm F (diagonalExpSection F t) = Real.exp (Multiplicative.toAdd t) := by
  rw [diagonalExpSection, ideleNorm_archimedeanExpSection]
  let n : ℝ := Fintype.card (InfinitePlace F)
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm (v : InfinitePlace F) : ((v.mult : ℝ) * n)⁻¹ * (v.mult : ℝ) = n⁻¹ := by
    field_simp [show (v.mult : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero, hn]
  simp only [← show n = (Fintype.card (InfinitePlace F) : ℝ) from rfl, hterm,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn, mul_one]

/-- The idelic norm written in the logarithmic coordinate on the positive reals. -/
def ideleLogNorm : Idele F →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (Real.log (ideleNorm F g))
  map_one' := by simp
  map_mul' g h := by
    change Multiplicative.ofAdd (Real.log (ideleNorm F (g * h))) =
      Multiplicative.ofAdd (Real.log (ideleNorm F g) + Real.log (ideleNorm F h))
    rw [map_mul, Real.log_mul (ideleNorm_pos F g).ne' (ideleNorm_pos F h).ne']

theorem ideleLogNorm_continuous : Continuous (ideleLogNorm F) := by
  apply continuous_ofAdd.comp
  apply continuous_iff_continuousAt.mpr
  intro g
  exact (Real.continuousAt_log (ideleNorm_pos F g).ne').comp (ideleNorm_continuous F).continuousAt

/-- The multiplication map from a section and the kernel is an isomorphism.
Applied to `ideleLogNorm`, this gives the group map of Lemma A.2.2.9. -/
def splitNormMulEquiv {G R : Type*} [CommGroup G] [Group R]
    (f : G →* R) (s : R →* G) (hs : ∀ t, f (s t) = t) : R × f.ker ≃* G where
  toFun p := s p.1 * p.2.val
  invFun g := ⟨f g, ⟨g / s (f g), by
    change f (g / s (f g)) = 1
    rw [map_div, hs, div_self']⟩⟩
  left_inv := by
    rintro ⟨t, u⟩
    have hu : f u.val = 1 := u.property
    have htu : f (s t * u.val) = t := by rw [map_mul, hs, hu, mul_one]
    apply Prod.ext htu
    apply Subtype.ext
    change s t * u.val / s (f (s t * u.val)) = u.val
    rw [htu, mul_comm, mul_div_cancel_right]
  right_inv g := by
    change s (f g) * (g / s (f g)) = g
    rw [mul_comm, div_mul_cancel]
  map_mul' p q := by
    change s (p.1 * q.1) * (p.2.val * q.2.val) = (s p.1 * p.2.val) * (s q.1 * q.2.val)
    rw [map_mul, mul_mul_mul_comm]

/-- A continuous homomorphic section of the idelic norm yields the topological
product decomposition in Lemma A.2.2.9. -/
def ideleSplitHomeomorph (s : Multiplicative ℝ →* Idele F)
    (hs : ∀ t, ideleLogNorm F (s t) = t) (hsc : Continuous s) :
    Multiplicative ℝ × (ideleLogNorm F).ker ≃ₜ Idele F where
  toEquiv := (splitNormMulEquiv (ideleLogNorm F) s hs).toEquiv
  continuous_toFun := (hsc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (ideleLogNorm_continuous F).prodMk
    ((continuous_id.div' (hsc.comp (ideleLogNorm_continuous F))).subtype_mk _)

/-- The section descends along the principal-idele quotient. -/
def ideleClassExpSection : Multiplicative ℝ →* IdeleClass F :=
  (ideleClassMap F).comp (ideleExpSection F)

theorem ideleClassExpSection_continuous : Continuous (ideleClassExpSection F) :=
  (ideleClassMap_continuous F).comp (ideleExpSection_continuous F)

theorem ideleClassNorm_expSection (t : Multiplicative ℝ) :
    ideleClassNorm F (ideleClassExpSection F t) = Real.exp (Multiplicative.toAdd t) :=
  ideleNorm_expSection F t

/-- Lemma A.2.2.1 in logarithmic coordinates. Over ℚ the canonical section
has positive real component `exp t` and trivial finite components, and it
is a section also after passing to the class group. -/
theorem rationalCanonicalSection (t : Multiplicative ℝ) :
    (∀ v, (ideleExpSection ℚ t).val.1 v = realAtInfinitePlace ℚ v
      (Real.exp (Multiplicative.toAdd t))) ∧
    (ideleExpSection ℚ t).val.2 = 1 ∧
    ideleClassNorm ℚ (ideleClassExpSection ℚ t) = Real.exp (Multiplicative.toAdd t) := by
  have h := ideleExpSection_components ℚ t
  refine ⟨?_, h.2, ideleClassNorm_expSection ℚ t⟩
  simpa using h.1

theorem ideleClassNorm_range : Set.range (ideleClassNorm F) = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨g, rfl⟩
    exact ideleClassNorm_pos F g
  · intro hr
    exact ⟨ideleClassExpSection F (Multiplicative.ofAdd (Real.log r)),
      (ideleClassNorm_expSection F _).trans (Real.exp_log hr)⟩

/-- The norm-one group in (A.1.4.2), as a closed subgroup of the quotient. -/
def normOneIdeleClass : Subgroup (IdeleClass F) := (ideleClassNorm F).ker

theorem normOneIdeleClass_isClosed : IsClosed (normOneIdeleClass F : Set (IdeleClass F)) :=
  isClosed_eq (ideleClassNorm_continuous F) continuous_const

/-- The log modulus has codomain the additive real group, written multiplicatively. -/
def ideleClassLogNorm : IdeleClass F →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (Real.log (ideleClassNorm F g))
  map_one' := by simp
  map_mul' g h := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F (g * h))) =
      Multiplicative.ofAdd (Real.log (ideleClassNorm F g) + Real.log (ideleClassNorm F h))
    rw [map_mul, Real.log_mul (ideleClassNorm_pos F g).ne' (ideleClassNorm_pos F h).ne']

theorem ideleClassLogNorm_continuous : Continuous (ideleClassLogNorm F) := by
  apply continuous_ofAdd.comp
  apply continuous_iff_continuousAt.mpr
  intro g
  exact (Real.continuousAt_log (ideleClassNorm_pos F g).ne').comp
    (ideleClassNorm_continuous F).continuousAt

@[simp] theorem ideleClassLogNorm_expSection (t : Multiplicative ℝ) :
    ideleClassLogNorm F (ideleClassExpSection F t) = t := by
  change Multiplicative.ofAdd (Real.log (ideleClassNorm F (ideleClassExpSection F t))) = t
  rw [ideleClassNorm_expSection, Real.log_exp]
  rfl

/-- Project an idele class to its norm-one component by dividing by the section. -/
def ideleClassNormOnePart (g : IdeleClass F) : normOneIdeleClass F :=
  ⟨g / ideleClassExpSection F (ideleClassLogNorm F g), by
    change ideleClassNorm F (g / ideleClassExpSection F (ideleClassLogNorm F g)) = 1
    rw [div_eq_mul_inv, map_mul]
    have h : ideleClassNorm F (ideleClassExpSection F (ideleClassLogNorm F g)) =
        ideleClassNorm F g := by
      rw [ideleClassNorm_expSection]
      exact Real.exp_log (ideleClassNorm_pos F g)
    rw [← h]
    rw [← map_mul, mul_inv_cancel, map_one]⟩

/-- The group splitting used to separate the norm coordinate in Chapter 3. -/
def ideleClassSplit : IdeleClass F ≃* normOneIdeleClass F × Multiplicative ℝ where
  toFun g := (ideleClassNormOnePart F g, ideleClassLogNorm F g)
  invFun p := p.1.val * ideleClassExpSection F p.2
  left_inv g := div_mul_cancel (a := g) _
  right_inv := by
    rintro ⟨u, t⟩
    have hu : ideleClassLogNorm F u.val = 1 := by
      change Multiplicative.ofAdd (Real.log (ideleClassNorm F u.val)) = 1
      have h : ideleClassNorm F u.val = 1 := u.property
      simp [h]
    have ht : ideleClassLogNorm F (u.val * ideleClassExpSection F t) = t := by simp [hu]
    apply Prod.ext
    · apply Subtype.ext
      change (u.val * ideleClassExpSection F t) /
        ideleClassExpSection F (ideleClassLogNorm F (u.val * ideleClassExpSection F t)) = u.val
      rw [ht, mul_div_cancel_right]
    · exact ht
  map_mul' g h := by
    apply Prod.ext
    · apply Subtype.ext
      change g * h / ideleClassExpSection F (ideleClassLogNorm F (g * h)) =
        (g / ideleClassExpSection F (ideleClassLogNorm F g)) *
          (h / ideleClassExpSection F (ideleClassLogNorm F h))
      simp only [map_mul]
      exact mul_div_mul_comm g h (ideleClassExpSection F (ideleClassLogNorm F g))
        (ideleClassExpSection F (ideleClassLogNorm F h))
    · exact map_mul _ _ _

/-- The splitting is compatible with the quotient and subgroup topologies. -/
def ideleClassSplitHomeomorph : IdeleClass F ≃ₜ normOneIdeleClass F × Multiplicative ℝ where
  toEquiv := (ideleClassSplit F).toEquiv
  continuous_toFun := by
    apply Continuous.prodMk _ (ideleClassLogNorm_continuous F)
    exact (continuous_id.div' ((ideleClassExpSection_continuous F).comp
      (ideleClassLogNorm_continuous F))).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((ideleClassExpSection_continuous F).comp continuous_snd)

end Masullo
