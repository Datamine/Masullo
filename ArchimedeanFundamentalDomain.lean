import NormOneClassCompact
import AngularSectors
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open Function IsDedekindDomain NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

abbrev InfiniteIdeles := (InfiniteAdeleRing F)ˣ

/-- The compact-set translate bound uses the closed discrete principal
idele subgroup. -/
theorem principalIdele_finite_translates {K D : Set (Idele F)}
    (hK : IsCompact K) (hD : IsCompact D) :
    {t : Fˣ | ∃ x ∈ D, principalIdele F t * x ∈ K}.Finite := by
  let P := principalIdeles F
  let C := (fun p : Idele F × Idele F => p.1 / p.2) '' (K ×ˢ D)
  have hC : IsCompact C := (hK.prod hD).image (continuous_fst.div' continuous_snd)
  letI : DiscreteTopology P := principalIdeles_discrete
  have hfinite : ((↑) ⁻¹' C : Set P).Finite :=
    (principalIdeles_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hC).finite_of_discrete
  let j : Fˣ → P := fun t => ⟨principalIdele F t, ⟨t, rfl⟩⟩
  have hj : Injective j := fun _ _ h => principalIdele_injective F (congrArg Subtype.val h)
  refine (hfinite.preimage hj.injOn).subset ?_
  rintro t ⟨x, hx, htx⟩
  exact ⟨(principalIdele F t * x, x), ⟨htx, hx⟩, mul_div_cancel_right _ _⟩

private def archCoordinateComplexRingHom (v : InfinitePlace F) :
    InfiniteAdeleRing F →+* ℂ where
  toFun a := InfinitePlace.Completion.extensionEmbedding v (a v)
  map_one' := map_one _
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  map_mul' _ _ := map_mul _ _ _

private def archCoordinateComplex (v : InfinitePlace F) : InfiniteIdeles F →* ℂˣ :=
  Units.map (archCoordinateComplexRingHom F v)

omit [NumberField F] in
private theorem archCoordinateComplex_continuous (v : InfinitePlace F) :
    Continuous (archCoordinateComplex F v) := by
  apply Continuous.units_map
  exact (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)

omit [NumberField F] in
private theorem complexCoord_globalUnit (v : InfinitePlace F) (u : (𝓞 F)ˣ) :
    archCoordinateComplex F v (fieldToArch F (integralUnitToField F u)) =
      Units.complexEmbedding v.embedding u := by
  apply Units.ext
  let k := (u : F)
  have h := InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm k)
  change InfinitePlace.Completion.extensionEmbedding v (algebraMap F v.Completion k) =
     v.embedding (WithAbs.equiv v.1 ((WithAbs.equiv v.1).symm k)) at h
  exact h.trans (congrArg v.embedding ((WithAbs.equiv v.1).apply_symm_apply k))

/-- The phase at the designated place uses its chosen embedding into
the complex numbers. At a real place it takes the two real signs. -/
def infiniteIdelePhase (v : InfinitePlace F) : InfiniteIdeles F →* Circle :=
  complexUnitPhase.comp (archCoordinateComplex F v)

omit [NumberField F] in
theorem infiniteIdelePhase_continuous (v : InfinitePlace F) : Continuous (infiniteIdelePhase F v) :=
  complexUnitPhase_continuous.comp (archCoordinateComplex_continuous F v)

private theorem torsionPhase_of_norm_one (v : InfinitePlace F) (u : torsion F) :
    (infiniteIdelePhase F v (fieldToArch F (integralUnitToField F u.val)) : ℂ) =
      (Units.complexEmbedding v.embedding u.val : ℂ) := by
  have hn : ‖(Units.complexEmbedding v.embedding u.val : ℂ)‖ = 1 := by
    change ‖v.embedding (u.val : F)‖ = 1
    rw [InfinitePlace.norm_embedding_eq]
    exact (Units.mem_torsion F).mp u.property v
  change (complexUnitPhase (archCoordinateComplex F v
    (fieldToArch F (integralUnitToField F u.val))) : ℂ) = _
  rw [complexCoord_globalUnit, complexUnitPhase_of_norm_one _ hn]

/-- The roots of unity in the integral units act faithfully at each
place and realize every root of unity of the given order in its phase. -/
private theorem torsionPhase_card (v : InfinitePlace F) :
    ∀ r : rootsOfUnity (torsionOrder F) Circle, ∃! u : torsion F,
      infiniteIdelePhase F v (fieldToArch F (integralUnitToField F u.val)) = (r.val : Circle) := by
  intro r
  let rc := rootsOfUnityCircleEquiv (torsionOrder F) r
  have hm : rc.val ∈ (torsion F).map (Units.complexEmbedding v.embedding) := by
    rw [map_complexEmbedding_torsion]
    exact rc.property
  obtain ⟨u, hu, hur⟩ := hm
  have h : infiniteIdelePhase F v (fieldToArch F (integralUnitToField F u)) = (r.val : Circle) := by
    apply Subtype.ext
    rw [torsionPhase_of_norm_one F v ⟨u, hu⟩, hur]
    exact rootsOfUnityCircleEquiv_apply _ r
  refine ⟨⟨u, hu⟩, h, ?_⟩
  intro w hw
  apply Subtype.ext
  apply Units.complexEmbedding_injective v.embedding
  apply Units.ext
  rw [← torsionPhase_of_norm_one F v w, ← torsionPhase_of_norm_one F v ⟨u, hu⟩]
  exact congrArg (fun c : Circle => (c : ℂ)) (hw.trans h.symm)


/-- The subgroup of Archimedean ideles of product modulus one. -/
def archNormOne : Subgroup (InfiniteIdeles F) :=
  ((archTotalLogHom F).comp (infiniteAdeleUnitsMixed F).toMonoidHom).ker

theorem archNormOne_iff (a : InfiniteIdeles F) : a ∈ archNormOne F ↔ ‖a.val‖ = 1 := by
  change infiniteAdeleUnitsMixed F a ∈ (archTotalLogHom F).ker ↔ _
  rw [archTotalLog_ker_iff]
  exact iff_of_eq (congrArg (fun r : ℝ => r = 1) (archModulus_of_infiniteAdele F a.val))

theorem archNormOne_closed : IsClosed (archNormOne F : Set (InfiniteIdeles F)) :=
  isClosed_eq ((archTotalLogHom_continuous F).comp
    (infiniteAdeleUnitsMixed F).continuous) continuous_const

private def archLogHyperplane (a : archNormOne F) : regulatorHyperplane F :=
  ⟨fullArchLog F a.val, fullArchLog_mem_hyperplane F a.val ((archNormOne_iff F a.val).mp a.property)⟩

/-- The regulator coordinates of an Archimedean norm-one idele. -/
def archRegulatorLog : archNormOne F →* Multiplicative (logSpace F) where
  toFun a := Multiplicative.ofAdd (regulatorHyperplaneEquiv F (archLogHyperplane F a))
  map_one' := by
    have h : archLogHyperplane F 1 = 0 := by
      apply Subtype.ext
      funext v
      change (v.mult : ℝ) * Real.log ‖(1 : v.Completion)‖ = 0
      simp
    rw [h, map_zero]
    rfl
  map_mul' a b := by
    have h : archLogHyperplane F (a * b) = archLogHyperplane F a + archLogHyperplane F b :=
      Subtype.ext (fullArchLog_mul F a.val b.val)
    rw [h, map_add]
    rfl

theorem archRegulatorLog_continuous : Continuous (archRegulatorLog F) := by
  apply continuous_ofAdd.comp
  apply (regulatorHyperplaneEquiv F).continuous.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  have hval : Continuous (fun a : archNormOne F => a.val.val) :=
    (Units.continuous_val : Continuous (Units.val : InfiniteIdeles F → InfiniteAdeleRing F)).comp
      continuous_subtype_val
  have h : Continuous (fun a : archNormOne F => ‖a.val.val v‖) :=
    ((continuous_apply v).comp hval).norm
  have hl : Continuous (fun a : archNormOne F => Real.log ‖a.val.val v‖) := by
    exact Real.continuous_log.comp (h.subtype_mk (fun a =>
      norm_ne_zero_iff.mpr (infiniteCoord_nonzero F a.val v)))
  exact hl.const_mul _

private theorem fullArchLog_positive (a : InfiniteIdeles F) : 0 < ‖a.val‖ := by
  rw [InfiniteAdeleRing.norm_def]
  exact Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.mpr (infiniteCoord_nonzero F a v)) _

theorem archRegulatorLog_surjective : Surjective (archRegulatorLog F) := by
  intro x
  have hs : Surjective (infiniteIdeleArchLog F) := fun p => by
    obtain ⟨a, ha⟩ := archLogHom_surjective F p
    exact ⟨(infiniteAdeleUnitsMixed F).symm a, by
      change archLogHom F (infiniteAdeleUnitsMixed F ((infiniteAdeleUnitsMixed F).symm a)) = p
      rwa [ContinuousMulEquiv.apply_symm_apply]⟩
  let l := (regulatorHyperplaneEquiv F).symm (Multiplicative.toAdd x)
  obtain ⟨a, ha⟩ := hs (splitArchLog F l.val)
  have hl : fullArchLog F a = l.val := by
    apply splitArchLog_injective F
    rwa [split_fullArchLog]
  have hsum : ∑ v, fullArchLog F a v = 0 := by
    rw [hl]
    exact (mem_regulatorHyperplane F l.val).mp l.property
  have hm : a ∈ archNormOne F := by
    rw [archNormOne_iff]
    rw [fullArchLog_sum] at hsum
    rw [← Real.exp_log (fullArchLog_positive F a), hsum, Real.exp_zero]
  refine ⟨⟨a, hm⟩, ?_⟩
  have h : archLogHyperplane F ⟨a, hm⟩ = l := Subtype.ext hl
  change Multiplicative.ofAdd (regulatorHyperplaneEquiv F (archLogHyperplane F ⟨a, hm⟩)) = x
  rw [h, ContinuousLinearEquiv.apply_symm_apply]
  rfl


private def regulatorLogInputs :
    Multiplicative (logSpace F) →*
      (({v : InfinitePlace F // v.IsReal} → Multiplicative ℝ) ×
        ({v : InfinitePlace F // v.IsComplex} → Multiplicative ℝ)) where
  toFun x := splitArchLog F ((regulatorHyperplaneEquiv F).symm x.toAdd).val
  map_one' := by
    change splitArchLog F ((regulatorHyperplaneEquiv F).symm 0).val = 1
    rw [map_zero]
    rfl
  map_mul' x y := by
    change splitArchLog F ((regulatorHyperplaneEquiv F).symm (x.toAdd + y.toAdd)).val = _
    rw [map_add]
    rfl

private def archRegulatorAmbientSection : Multiplicative (logSpace F) →* InfiniteIdeles F :=
  (infiniteAdeleUnitsMixed F).symm.toMonoidHom.comp ((archLogSection F).comp (regulatorLogInputs F))

private theorem archRegulatorAmbientSection_log (x : Multiplicative (logSpace F)) :
    fullArchLog F (archRegulatorAmbientSection F x) =
      ((regulatorHyperplaneEquiv F).symm x.toAdd).val := by
  apply splitArchLog_injective F
  rw [split_fullArchLog]
  change archLogHom F (infiniteAdeleUnitsMixed F
    ((infiniteAdeleUnitsMixed F).symm (archLogSection F (regulatorLogInputs F x)))) = _
  rw [ContinuousMulEquiv.apply_symm_apply, archLogHom_section]
  rfl

/-- Positive real coordinate lifts of the regulator logarithms. -/
def archRegulatorSection : Multiplicative (logSpace F) →* archNormOne F :=
  (archRegulatorAmbientSection F).codRestrict (archNormOne F) (fun x => by
    apply (archNormOne_iff F _).mpr
    have h := (mem_regulatorHyperplane F _).mp ((regulatorHyperplaneEquiv F).symm x.toAdd).property
    rw [← archRegulatorAmbientSection_log F x, fullArchLog_sum] at h
    rw [← Real.exp_log (fullArchLog_positive F _), h, Real.exp_zero])

theorem archRegulatorSection_continuous : Continuous (archRegulatorSection F) := by
  apply Continuous.subtype_mk
  apply (infiniteAdeleUnitsMixed F).symm.continuous.comp
  apply (archLogSection_continuous F).comp
  exact (splitArchLog_continuous F).comp
    (continuous_subtype_val.comp ((regulatorHyperplaneEquiv F).symm.continuous.comp continuous_toAdd))

theorem archRegulatorLog_section (x : Multiplicative (logSpace F)) :
    archRegulatorLog F (archRegulatorSection F x) = x := by
  change Multiplicative.ofAdd (regulatorHyperplaneEquiv F
    (archLogHyperplane F (archRegulatorSection F x))) = x
  have h : archLogHyperplane F (archRegulatorSection F x) =
      (regulatorHyperplaneEquiv F).symm x.toAdd :=
    Subtype.ext (archRegulatorAmbientSection_log F x)
  rw [h, ContinuousLinearEquiv.apply_symm_apply]
  rfl

private theorem archRegulatorLog_ker_iff (a : archNormOne F) :
    a ∈ (archRegulatorLog F).ker ↔ infiniteAdeleUnitsMixed F a.val ∈ (archLogHom F).ker := by
  change archRegulatorLog F a = 1 ↔ archLogHom F (infiniteAdeleUnitsMixed F a.val) = 1
  change archRegulatorLog F a = 1 ↔ infiniteIdeleArchLog F a.val = 1
  rw [← split_fullArchLog]
  have hl : archRegulatorLog F a = 1 ↔ archLogHyperplane F a = 0 := by
    change (regulatorHyperplaneEquiv F) (archLogHyperplane F a) = 0 ↔ _
    exact map_eq_zero_iff _ (regulatorHyperplaneEquiv F).injective
  rw [hl]
  have hz : splitArchLog F 0 = 1 := rfl
  rw [← hz]
  constructor
  · intro h
    exact congrArg (splitArchLog F ∘ Subtype.val) h
  · intro h
    exact Subtype.ext (splitArchLog_injective F h)

private def archRegulatorKernelToFull : (archRegulatorLog F).ker ≃ₜ* (archLogHom F).ker where
  toFun a := ⟨infiniteAdeleUnitsMixed F a.val.val, (archRegulatorLog_ker_iff F a.val).mp a.property⟩
  invFun a := by
    let b := (infiniteAdeleUnitsMixed F).symm a.val
    have h : b ∈ archNormOne F := by
      have he : infiniteIdeleArchLog F b = 1 := by
        change archLogHom F (infiniteAdeleUnitsMixed F ((infiniteAdeleUnitsMixed F).symm a.val)) = 1
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact a.property
      have hz : splitArchLog F 0 = 1 := rfl
      have he' : fullArchLog F b = 0 := splitArchLog_injective F
        ((split_fullArchLog F b).trans (he.trans hz.symm))
      have hsum := fullArchLog_sum F b
      rw [he', Pi.zero_def, Finset.sum_const_zero] at hsum
      exact (archNormOne_iff F b).mpr (by rw [← Real.exp_log (fullArchLog_positive F b),
        ← hsum, Real.exp_zero])
    let c : archNormOne F := ⟨b, h⟩
    exact ⟨c, (archRegulatorLog_ker_iff F c).mpr (by
      change archLogHom F (infiniteAdeleUnitsMixed F ((infiniteAdeleUnitsMixed F).symm a.val)) = 1
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact a.property)⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact (infiniteAdeleUnitsMixed F).symm_apply_apply a.val.val
  right_inv a := Subtype.ext ((infiniteAdeleUnitsMixed F).apply_symm_apply a.val)
  map_mul' a b := Subtype.ext ((infiniteAdeleUnitsMixed F).map_mul a.val.val b.val.val)
  continuous_toFun := Continuous.subtype_mk
    ((infiniteAdeleUnitsMixed F).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
    ((infiniteAdeleUnitsMixed F).symm.continuous.comp continuous_subtype_val) _) _

private def archNormOneRadialSplit :
    (Multiplicative (logSpace F) × (archRegulatorLog F).ker) ≃ₜ* archNormOne F where
  __ := splitNormMulEquiv (archRegulatorLog F) (archRegulatorSection F) (archRegulatorLog_section F)
  continuous_toFun := ((archRegulatorSection_continuous F).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (archRegulatorLog_continuous F).prodMk
    ((continuous_id.div' ((archRegulatorSection_continuous F).comp (archRegulatorLog_continuous F))).subtype_mk _)

/-- The actual Archimedean norm-one group has regulator coordinates,
real signs, and complex phases. -/
def archNormOnePolar :
    (Multiplicative (logSpace F) ×
      (({v : InfinitePlace F // v.IsReal} → Metric.sphere (0 : ℝ) 1) ×
       ({v : InfinitePlace F // v.IsComplex} → Circle))) ≃ₜ* archNormOne F :=
  let e := ((archRegulatorKernelToFull F).trans (archLogKernelPhases F)).symm
  let p : (Multiplicative (logSpace F) × _) ≃ₜ*
      (Multiplicative (logSpace F) × (archRegulatorLog F).ker) :=
    { __ := (MulEquiv.refl _).prodCongr e.toMulEquiv
      continuous_toFun := continuous_fst.prodMk (e.continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk (e.symm.continuous.comp continuous_snd) }
  p.trans (archNormOneRadialSplit F)


theorem archRegulatorLog_open : IsOpenMap (archRegulatorLog F) := by
  have e : (archRegulatorLog F : archNormOne F → Multiplicative (logSpace F)) =
      Prod.fst ∘ (archNormOneRadialSplit F).symm := rfl
  rw [e]
  exact isOpenMap_fst.comp (archNormOneRadialSplit F).symm.toHomeomorph.isOpenMap

omit [NumberField F] in
theorem archPhase_of_real_eq_one_or_neg_one {v : InfinitePlace F} (hv : v.IsReal)
    (a : InfiniteIdeles F) : infiniteIdelePhase F v a = 1 ∨ infiniteIdelePhase F v a = -1 := by
  let r := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (a.val v)
  have he : InfinitePlace.Completion.extensionEmbedding v (a.val v) = (r : ℂ) := by
    exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv (a.val v)).symm
  have hn : r ≠ 0 := by
    intro hr
    apply infiniteCoord_nonzero F a v
    apply (InfinitePlace.Completion.isometry_extensionEmbedding v).injective
    rw [he, hr, Complex.ofReal_zero, map_zero]
  rcases lt_or_gt_of_ne hn with hr | hr
  · right
    apply Subtype.ext
    change InfinitePlace.Completion.extensionEmbedding v (a.val v) /
      ((‖InfinitePlace.Completion.extensionEmbedding v (a.val v)‖ : ℝ) : ℂ) = -1
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr, Complex.ofReal_neg,
      div_neg, div_self (Complex.ofReal_ne_zero.mpr hn)]
  · left
    apply Subtype.ext
    change InfinitePlace.Completion.extensionEmbedding v (a.val v) /
      ((‖InfinitePlace.Completion.extensionEmbedding v (a.val v)‖ : ℝ) : ℂ) = 1
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self (Complex.ofReal_ne_zero.mpr hn)

/-- Embed integral units into the norm-one Archimedean group. -/
def globalUnitArch : (𝓞 F)ˣ →* archNormOne F :=
  ((fieldToArch F).comp (integralUnitToField F)).codRestrict (archNormOne F) (fun u => by
    obtain ⟨l, hl, _⟩ := fullArchLog_unit F u
    have hs : ∑ v, l.val v = 0 := (mem_regulatorHyperplane F l.val).mp l.property
    rw [hl, fullArchLog_sum] at hs
    change fieldToArch F (integralUnitToField F u) ∈ archNormOne F
    rw [archNormOne_iff, ← Real.exp_log (fullArchLog_positive F _), hs, Real.exp_zero])

theorem archRegulatorLog_globalUnit (u : (𝓞 F)ˣ) :
    archRegulatorLog F (globalUnitArch F u) = Multiplicative.ofAdd (logEmbedding F (Additive.ofMul u)) := by
  obtain ⟨l, hl, hq⟩ := fullArchLog_unit F u
  have h : archLogHyperplane F (globalUnitArch F u) = l := Subtype.ext hl.symm
  change Multiplicative.ofAdd (regulatorHyperplaneEquiv F (archLogHyperplane F (globalUnitArch F u))) = _
  rw [h, hq]

/-- The actual half-open Archimedean fundamental domain of the paper. -/
def archFundamentalDomain (v : InfinitePlace F) : Set (archNormOne F) :=
  {a | Multiplicative.toAdd (archRegulatorLog F a) ∈
      ZSpan.fundamentalDomain (regulatorBasis F) ∧
    infiniteIdelePhase F v a.val ∈ circleSector (torsionOrder F)}

theorem mem_archFundamentalDomain_iff_arg (v : InfinitePlace F) (a : archNormOne F) :
    a ∈ archFundamentalDomain F v ↔
      Multiplicative.toAdd (archRegulatorLog F a) ∈ ZSpan.fundamentalDomain (regulatorBasis F) ∧
      Complex.arg (archCoordinateComplex F v a.val : ℂ) ∈
        Ico 0 (2 * Real.pi / torsionOrder F) := by
  have h : 2 ≤ torsionOrder F := by
    have h₁ := torsionOrder_pos F
    have h₂ : 2 ∣ torsionOrder F := even_iff_two_dvd.mp (even_torsionOrder F)
    exact Nat.le_of_dvd h₁ h₂
  unfold archFundamentalDomain
  rw [Set.mem_ofPred_eq, mem_circleSector_iff_arg h]
  exact and_congr_right fun _ => by
    change Complex.arg (complexUnitPhase (archCoordinateComplex F v a.val) : ℂ) ∈ _ ↔ _
    rw [complexUnitPhase_arg]

theorem archFundamentalDomain_compact_closure (v : InfinitePlace F) :
    IsCompact (closure (archFundamentalDomain F v)) := by
  let P := ZSpan.fundamentalDomain (regulatorBasis F)
  let K := infiniteIdeleArchLog F ⁻¹' (regToArchLog F '' closure P)
  have hK : IsCompact K := (infiniteIdeleArchLog_proper F).isCompact_preimage
    ((regulator_fundamentalDomain F).1.image (regToArchLog_continuous F))
  have hK' : IsCompact ((Subtype.val : archNormOne F → InfiniteIdeles F) ⁻¹' K) :=
    (archNormOne_closed F).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hs : archFundamentalDomain F v ⊆ (Subtype.val : archNormOne F → InfiniteIdeles F) ⁻¹' K := by
    intro a ha
    change infiniteIdeleArchLog F a.val ∈ regToArchLog F '' closure P
    refine ⟨Multiplicative.toAdd (archRegulatorLog F a), subset_closure ha.1, ?_⟩
    unfold regToArchLog
    change splitArchLog F ((regulatorHyperplaneEquiv F).symm
      (regulatorHyperplaneEquiv F (archLogHyperplane F a))).val = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact split_fullArchLog F a.val
  exact hK'.closure_of_subset hs

private theorem torsionPhase_pow (v : InfinitePlace F) (u : torsion F) :
    infiniteIdelePhase F v (globalUnitArch F u.val).val ^ torsionOrder F = 1 := by
  have hu : u.val ^ torsionOrder F = 1 :=
    (mem_rootsOfUnity _ _).mp ((rootsOfUnity_eq_torsion F).symm ▸ u.property)
  change infiniteIdelePhase F v (fieldToArch F (integralUnitToField F u.val)) ^ torsionOrder F = 1
  rw [← map_pow, ← map_pow, ← map_pow, hu, map_one, map_one, map_one]


/-- The phase identifies the torsion units with all roots of unity of the
required order at any prescribed infinite place. -/
def torsionPhaseEquiv (v : InfinitePlace F) : torsion F ≃ rootsOfUnity (torsionOrder F) Circle :=
  Equiv.ofBijective (fun t => rootsOfUnity.mkOfPowEq
    (infiniteIdelePhase F v (globalUnitArch F t.val).val) (torsionPhase_pow F v t)) (by
      constructor
      · intro a b h
        let r := rootsOfUnity.mkOfPowEq
          (infiniteIdelePhase F v (globalUnitArch F a.val).val) (torsionPhase_pow F v a)
        obtain ⟨t, _, ht⟩ := torsionPhase_card F v r
        have hb : infiniteIdelePhase F v (globalUnitArch F b.val).val = (r.val : Circle) :=
          congrArg (fun s : rootsOfUnity (torsionOrder F) Circle => (s.val : Circle)) h.symm
        exact (ht a rfl).trans (ht b hb).symm
      · intro r
        obtain ⟨t, h, _⟩ := torsionPhase_card F v r
        exact ⟨t, Subtype.ext (Units.ext h)⟩)

theorem torsionPhaseEquiv_apply (v : InfinitePlace F) (t : torsion F) :
    ((torsionPhaseEquiv F v t).val : Circle) =
      infiniteIdelePhase F v (globalUnitArch F t.val).val := rfl

private theorem torsionArchLog_one (u : torsion F) :
    archRegulatorLog F (globalUnitArch F u.val) = 1 := by
  rw [archRegulatorLog_globalUnit]
  exact congrArg Multiplicative.ofAdd ((logEmbedding_eq_zero_iff (K := F)).mpr u.property)

private theorem archLogUnits_in_lattice (u : (𝓞 F)ˣ) :
    logEmbedding F (Additive.ofMul u) ∈ unitLattice F := by
  apply Submodule.mem_map.mpr
  exact ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩

/-- Integral units give a unique translate into the source domain. -/
theorem archFundamentalDomain_unique (v : InfinitePlace F) (a : archNormOne F) :
    ∃! u : (𝓞 F)ˣ, globalUnitArch F u * a ∈ archFundamentalDomain F v := by
  let L := archRegulatorLog F
  let x := Multiplicative.toAdd (L a)
  obtain ⟨d, hd, huniq⟩ := (regulator_fundamentalDomain F).2.2 x
  obtain ⟨w, _, hw⟩ := Submodule.mem_map.mp d.property
  change logEmbedding F w = d.val at hw
  let b := globalUnitArch F (Additive.toMul w) * a
  have hlog : Multiplicative.toAdd (L b) = d.val + x := by
    change Multiplicative.toAdd (L (globalUnitArch F (Additive.toMul w) * a)) = _
    rw [map_mul, archRegulatorLog_globalUnit]
    exact congrArg (fun q : logSpace F => q + x) hw
  let p := infiniteIdelePhase F v
  obtain ⟨r, hr, hruniq⟩ := circleSector_unique_rotation (torsionOrder F) (p b.val)
  obtain ⟨μ, hμ, hμuniq⟩ := torsionPhase_card F v r
  refine ⟨μ.val * Additive.toMul w, ?_, ?_⟩
  · change globalUnitArch F (μ.val * Additive.toMul w) * a ∈ _
    rw [map_mul, mul_assoc]
    change (globalUnitArch F μ.val * b) ∈ _
    constructor
    · change Multiplicative.toAdd (L (globalUnitArch F μ.val * b)) ∈ _
      rw [map_mul, torsionArchLog_one, one_mul, hlog]
      exact hd
    · change p ((globalUnitArch F μ.val).val * b.val) ∈ _
      rw [map_mul, show p (globalUnitArch F μ.val).val = (r.val : Circle) from hμ]
      exact hr
  · intro u hu
    have huL : (⟨logEmbedding F (Additive.ofMul u), archLogUnits_in_lattice F u⟩ :
        unitLattice F) = d := by
      apply huniq
      change logEmbedding F (Additive.ofMul u) + x ∈ _
      have h := hu.1
      change Multiplicative.toAdd (L (globalUnitArch F u * a)) ∈ _ at h
      rw [map_mul, archRegulatorLog_globalUnit] at h
      exact h
    have hlogs : logEmbedding F (Additive.ofMul u) = logEmbedding F w :=
      (congrArg Subtype.val huL).trans hw.symm
    let ν : torsion F := ⟨u / Additive.toMul w, (logEmbedding_eq_zero_iff (K := F)).mp (by
      change logEmbedding F (Additive.ofMul u - w) = 0
      rw [map_sub, hlogs, sub_self])⟩
    have hn : globalUnitArch F ν.val * b = globalUnitArch F u * a := by
      change globalUnitArch F (u / Additive.toMul w) *
        (globalUnitArch F (Additive.toMul w) * a) = _
      rw [← mul_assoc, ← map_mul, div_mul_cancel]
    let s := rootsOfUnity.mkOfPowEq (p (globalUnitArch F ν.val).val) (torsionPhase_pow F v ν)
    have hs : (s.val : Circle) * p b.val ∈ circleSector (torsionOrder F) := by
      change p (globalUnitArch F ν.val).val * p b.val ∈ _
      rw [← map_mul]
      change p (globalUnitArch F ν.val * b).val ∈ _
      rw [hn]
      exact hu.2
    have hEq : s = r := hruniq s hs
    have hν : ν = μ := hμuniq ν (congrArg (fun q : rootsOfUnity (torsionOrder F) Circle =>
      (q.val : Circle)) hEq)
    have hν' : u / Additive.toMul w = μ.val := congrArg Subtype.val hν
    rw [← hν', div_mul_cancel]


private theorem replace_archCoord (a : archNormOne F) (v : InfinitePlace F)
    (z : (v.Completion)ˣ) (hz : ‖z.val‖ = ‖a.val.val v‖) :
    ∃ b : archNormOne F, b.val.val v = z.val ∧ archRegulatorLog F b = archRegulatorLog F a := by
  let e : InfiniteIdeles F ≃* ((w : InfinitePlace F) → (w.Completion)ˣ) := MulEquiv.piUnits
  let b₀ := e.symm (Function.update (e a.val) v z)
  have hc (w : InfinitePlace F) :
      b₀.val w = ((Function.update (e a.val) v z) w).val := rfl
  have hn (w : InfinitePlace F) : ‖b₀.val w‖ = ‖a.val.val w‖ := by
    rw [hc]
    by_cases h : w = v
    · subst w
      rw [Function.update_self]
      exact hz
    · rw [Function.update_of_ne h]
      rfl
  have hb₀ : b₀ ∈ archNormOne F := by
    rw [archNormOne_iff, InfiniteAdeleRing.norm_def]
    have ha := (archNormOne_iff F a.val).mp a.property
    rw [InfiniteAdeleRing.norm_def] at ha
    simpa only [hn] using ha
  refine ⟨⟨b₀, hb₀⟩, ?_, ?_⟩
  · rw [hc, Function.update_self]
  · have h : archLogHyperplane F ⟨b₀, hb₀⟩ = archLogHyperplane F a := by
      apply Subtype.ext
      funext w
      change (w.mult : ℝ) * Real.log ‖b₀.val w‖ = (w.mult : ℝ) * Real.log ‖a.val.val w‖
      rw [hn]
    exact congrArg (fun l => Multiplicative.ofAdd (regulatorHyperplaneEquiv F l)) h

theorem complex_place_with_phase {v : InfinitePlace F} (hv : v.IsComplex)
    (a : archNormOne F) (c : Circle) :
    ∃ b : archNormOne F, infiniteIdelePhase F v b.val = c ∧
      archRegulatorLog F b = archRegulatorLog F a := by
  let r := ‖a.val.val v‖
  have hr : 0 < r := norm_pos_iff.mpr (infiniteCoord_nonzero F a.val v)
  let e := InfinitePlace.Completion.extensionEmbedding v
  obtain ⟨z, hz⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hv
    ((r : ℂ) * c)
  have hzp : ‖z‖ = r := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero e),
      show InfinitePlace.Completion.extensionEmbedding v z = (r : ℂ) * c from hz,
      norm_mul, c.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  let u : (v.Completion)ˣ := Units.mk0 z (norm_ne_zero_iff.mp (hzp.trans_ne hr.ne'))
  obtain ⟨b, hb, hlog⟩ := replace_archCoord F a v u hzp
  refine ⟨b, ?_, hlog⟩
  apply Subtype.ext
  change e (b.val.val v) / (‖e (b.val.val v)‖ : ℂ) = (c : ℂ)
  have he : e (b.val.val v) = (r : ℂ) * c := (congrArg e hb).trans hz
  rw [he, norm_mul, c.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')

private theorem real_place_with_positive_coordinate {v : InfinitePlace F} (hv : v.IsReal)
    (a : archNormOne F) :
    ∃ b : archNormOne F, 0 < (archCoordinateComplex F v b.val : ℂ).re ∧
      archRegulatorLog F b = archRegulatorLog F a := by
  let r := ‖a.val.val v‖
  have hr : 0 < r := norm_pos_iff.mpr (infiniteCoord_nonzero F a.val v)
  let e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  obtain ⟨z, hz⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hv r
  have hzp : ‖z‖ = r := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero e),
      show InfinitePlace.Completion.extensionEmbeddingOfIsReal hv z = r from hz,
      Real.norm_of_nonneg hr.le]
  let u : (v.Completion)ˣ := Units.mk0 z (norm_ne_zero_iff.mp (hzp.trans_ne hr.ne'))
  obtain ⟨b, hb, hlog⟩ := replace_archCoord F a v u hzp
  refine ⟨b, ?_, hlog⟩
  change 0 < (InfinitePlace.Completion.extensionEmbedding v (b.val.val v)).re
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  change 0 < e (b.val.val v)
  rw [hb]
  change 0 < e z
  rwa [hz]

/-- The half-open domain has nonempty interior in the Archimedean
norm-one group, including in unit rank zero. -/
theorem archFundamentalDomain_interior (v : InfinitePlace F) :
    (interior (archFundamentalDomain F v)).Nonempty := by
  let P := ZSpan.fundamentalDomain (regulatorBasis F)
  let L := Multiplicative.toAdd ∘ archRegulatorLog F
  let V := L ⁻¹' interior P
  have hV : IsOpen V := isOpen_interior.preimage
    (continuous_toAdd.comp (archRegulatorLog_continuous F))
  obtain ⟨x, hx⟩ := (regulator_fundamentalDomain F).2.1
  obtain ⟨a, ha⟩ := archRegulatorLog_surjective F (Multiplicative.ofAdd x)
  rcases v.isReal_or_isComplex with hr | hc
  · let U := {g : archNormOne F | 0 < (archCoordinateComplex F v g.val : ℂ).re}
    have hU : IsOpen U := isOpen_lt continuous_const
      (Complex.continuous_re.comp (Units.continuous_val.comp
        ((archCoordinateComplex_continuous F v).comp continuous_subtype_val)))
    obtain ⟨b, hb, hba⟩ := real_place_with_positive_coordinate F hr a
    have hVb : b ∈ V := by
      change L b ∈ interior P
      dsimp only [L, Function.comp_apply]
      rwa [hba, ha]
    refine ⟨b, interior_maximal ?_ (hV.inter hU) ⟨hVb, hb⟩⟩
    intro g hg
    refine (mem_archFundamentalDomain_iff_arg F v g).mpr ⟨interior_subset hg.1, ?_⟩
    change Complex.arg (InfinitePlace.Completion.extensionEmbedding v (g.val.val v)) ∈ _
    have hgpos : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hr (g.val.val v) := by
      have hg' := hg.2
      change 0 < (InfinitePlace.Completion.extensionEmbedding v (g.val.val v)).re at hg'
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr] at hg'
      exact hg'
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr, Complex.arg_ofReal_of_nonneg hgpos.le]
    exact ⟨le_rfl, div_pos Real.two_pi_pos (Nat.cast_pos.mpr (torsionOrder_pos F))⟩
  · obtain ⟨U, hU, ⟨c, hcU⟩, hUS⟩ := circleSector_hasInterior (torsionOrder F)
      (torsionOrder_ne_zero F)
    let f (g : archNormOne F) := infiniteIdelePhase F v g.val
    have hf : Continuous f := (infiniteIdelePhase_continuous F v).comp continuous_subtype_val
    obtain ⟨b, hb, hba⟩ := complex_place_with_phase F hc a c
    have hVb : b ∈ V := by
      change L b ∈ interior P
      dsimp only [L, Function.comp_apply]
      rwa [hba, ha]
    refine ⟨b, interior_maximal ?_ (hV.inter (hU.preimage hf)) ⟨hVb, by change infiniteIdelePhase F v b.val ∈ U; rwa [hb]⟩⟩
    exact fun g hg => ⟨interior_subset hg.1, hUS hg.2⟩


/-- The closure is compact also in the full Archimedean idele group. -/
theorem archFundamentalDomain_compact_closure_ambient (v : InfinitePlace F) :
    IsCompact (closure ((Subtype.val : archNormOne F → InfiniteIdeles F) ''
      archFundamentalDomain F v)) := by
  have he : IsClosedEmbedding (Subtype.val : archNormOne F → InfiniteIdeles F) :=
    (archNormOne_closed F).isClosedEmbedding_subtypeVal
  rw [he.closure_image_eq (archFundamentalDomain F v)]
  exact (archFundamentalDomain_compact_closure F v).image continuous_subtype_val

private abbrev FiniteIdeles := (FiniteAdeleRing (𝓞 F) F)ˣ

/-- Only finitely many translates of the closed Archimedean domain
can meet a compact set of norm-one Archimedean ideles. -/
theorem archFundamentalDomain_finite_translates (v : InfinitePlace F)
    {K : Set (archNormOne F)} (hK : IsCompact K) :
    {u : (𝓞 F)ˣ | ∃ x ∈ closure (archFundamentalDomain F v), globalUnitArch F u * x ∈ K}.Finite := by
  let E : Set (FiniteIdeles F) := (finiteIntegralSubmonoid F).units
  let f : Idele F ≃ₜ InfiniteIdeles F × FiniteIdeles F := Homeomorph.prodUnits
  let D := f ⁻¹' (((Subtype.val : archNormOne F → InfiniteIdeles F) '' (closure (archFundamentalDomain F v))) ×ˢ E)
  let T := f ⁻¹' (((Subtype.val : archNormOne F → InfiniteIdeles F) '' K) ×ˢ E)
  have hD : IsCompact D := f.isCompact_preimage.mpr
    (((archFundamentalDomain_compact_closure F v).image continuous_subtype_val).prod
      (finiteIntegralUnits_compact (F := F)))
  have hT : IsCompact T := f.isCompact_preimage.mpr
    ((hK.image continuous_subtype_val).prod (finiteIntegralUnits_compact (F := F)))
  refine (((principalIdele_finite_translates F hT hD).preimage
    (integralUnitToField_injective F).injOn)).subset ?_
  rintro u ⟨x, hx, hux⟩
  let a : Idele F := f.symm (x.val, 1)
  have ha : f a = (x.val, 1) := f.apply_symm_apply _
  have haD : a ∈ D := by
    change f a ∈ (((Subtype.val : archNormOne F → InfiniteIdeles F) '' (closure (archFundamentalDomain F v))) ×ˢ E)
    rw [ha]
    exact ⟨⟨x, hx, rfl⟩, (finiteIntegralSubmonoid F).units.one_mem⟩
  let t := integralUnitToField F u
  have htf : (f (principalIdele F t)).2 ∈ E :=
    (ideleDivisor_ker_iff_prodUnits F _).mp
      ((principalIdele_integral_iff F _).mpr ⟨u, rfl⟩)
  refine ⟨a, haD, ?_⟩
  change f (principalIdele F t * a) ∈ (((Subtype.val : archNormOne F → InfiniteIdeles F) '' K) ×ˢ E)
  have he : f (principalIdele F t * a) = f (principalIdele F t) * f a :=
    MulEquiv.prodUnits.map_mul _ _
  rw [he, ha]
  refine ⟨⟨globalUnitArch F u * x, hux, rfl⟩, ?_⟩
  change (f (principalIdele F t)).2 * 1 ∈ E
  rwa [mul_one]

/-- Saturating the half-open sector by the arithmetic roots of unity
recovers the full inverse image of the regulator parallelotope. -/
theorem archFundamentalDomain_torsion_saturation (v : InfinitePlace F) (a : archNormOne F) :
    (∃ u : torsion F, globalUnitArch F u.val * a ∈ archFundamentalDomain F v) ↔
      Multiplicative.toAdd (archRegulatorLog F a) ∈
        ZSpan.fundamentalDomain (regulatorBasis F) := by
  constructor
  · rintro ⟨u, hu⟩
    have h := hu.1
    change Multiplicative.toAdd (archRegulatorLog F (globalUnitArch F u.val * a)) ∈ _ at h
    rwa [map_mul, torsionArchLog_one, one_mul] at h
  · intro h
    let p := infiniteIdelePhase F v
    obtain ⟨r, hr, _⟩ := circleSector_unique_rotation (torsionOrder F) (p a.val)
    obtain ⟨u, hu, _⟩ := torsionPhase_card F v r
    refine ⟨u, ?_, ?_⟩
    · rwa [map_mul, torsionArchLog_one, one_mul]
    · change p ((globalUnitArch F u.val).val * a.val) ∈ _
      rw [map_mul, show p (globalUnitArch F u.val).val = (r.val : Circle) from hu]
      exact hr


/-- The half-open sector and parallelotope are Borel in the norm-one group. -/
theorem archFundamentalDomain_measurable [MeasurableSpace (archNormOne F)]
    [BorelSpace (archNormOne F)] (v : InfinitePlace F) :
    MeasurableSet (archFundamentalDomain F v) := by
  let L := Multiplicative.toAdd ∘ archRegulatorLog F
  have hL : Continuous L := continuous_toAdd.comp (archRegulatorLog_continuous F)
  let Q := ⋂ j, ((regulatorBasis F).coord j) ⁻¹' Ico (0 : ℝ) 1
  have hQ : MeasurableSet (L ⁻¹' Q) := by
    rw [show L ⁻¹' Q = ⋂ j, (((regulatorBasis F).coord j) ∘ L) ⁻¹' Ico (0 : ℝ) 1 from preimage_iInter]
    exact MeasurableSet.iInter fun j => measurableSet_Ico.preimage
      (((regulatorBasis F).coord j).continuous_of_finiteDimensional.comp hL).measurable
  let a := fun h : archNormOne F => (archCoordinateComplex F v h.val : ℂ)
  have ha : Continuous a := Units.continuous_val.comp
    ((archCoordinateComplex_continuous F v).comp continuous_subtype_val)
  have hA : MeasurableSet ((Complex.arg ∘ a) ⁻¹' Ico 0 (2 * Real.pi / torsionOrder F)) :=
    measurableSet_Ico.preimage (Complex.measurable_arg.comp ha.measurable)
  convert hQ.inter hA using 1
  ext h
  rw [mem_archFundamentalDomain_iff_arg F]
  apply and_congr_left
  intro _
  change L h ∈ ZSpan.fundamentalDomain (regulatorBasis F) ↔ L h ∈ Q
  rw [ZSpan.mem_fundamentalDomain, Set.mem_iInter]
  rfl

end

end Masullo
