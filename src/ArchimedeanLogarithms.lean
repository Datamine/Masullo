import AdelicTheta
import OneParameterFlows
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Units

open Filter Function Set Topology
open scoped Classical ContDiff NumberField

namespace Masullo

noncomputable section

section Scalar

variable {K : Type*} [RCLike K]

/-- The logarithm of the normalized scalar modulus. The exponent is one
at a real place and two at a complex place. -/
def scalarArchLog (w : ℝ) : Kˣ →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd (w * Real.log ‖(a : K)‖)
  map_one' := by simp
  map_mul' a b := by
    change Multiplicative.ofAdd (w * Real.log ‖(a : K) * (b : K)‖) =
      Multiplicative.ofAdd (w * Real.log ‖(a : K)‖ + w * Real.log ‖(b : K)‖)
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr a.ne_zero)
      (norm_ne_zero_iff.mpr b.ne_zero), mul_add]

theorem scalarArchLog_continuous (w : ℝ) : Continuous (scalarArchLog (K := K) w) := by
  change Continuous (fun u : Kˣ => Multiplicative.ofAdd (w * Real.log ‖(u : K)‖))
  have hN : Continuous (fun u : Kˣ => ‖(u : K)‖) := Units.continuous_val.norm
  have hL : Continuous (fun u : Kˣ => Real.log ‖(u : K)‖) :=
    continuous_iff_continuousAt.mpr fun a =>
      ContinuousAt.comp (f := fun u : Kˣ => ‖(u : K)‖) (x := a)
        (Real.continuousAt_log (norm_ne_zero_iff.mpr a.ne_zero)) hN.continuousAt
  exact continuous_ofAdd.comp (continuous_const.mul hL)

private def scalarArchSection (w : ℝ) : Multiplicative ℝ →* Kˣ where
  toFun t := Units.mk0 ((Real.exp (Multiplicative.toAdd t / w) : ℝ) : K)
    (RCLike.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  map_one' := by
    apply Units.ext
    simp
  map_mul' t u := by
    apply Units.ext
    change ((Real.exp ((Multiplicative.toAdd t + Multiplicative.toAdd u) / w) : ℝ) : K) = _
    rw [add_div, Real.exp_add, RCLike.ofReal_mul]
    rfl

private theorem scalarArchSection_continuous (w : ℝ) :
    Continuous (scalarArchSection (K := K) w) := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun t : Multiplicative ℝ =>
      ((Real.exp (Multiplicative.toAdd t / w) : ℝ) : K)) :=
    RCLike.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_toAdd.div_const w))
  refine ⟨h, ?_⟩
  exact h.inv₀ (fun _ => RCLike.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

private theorem scalarArchLog_section {w : ℝ} (hw : w ≠ 0) (t : Multiplicative ℝ) :
    scalarArchLog (K := K) w (scalarArchSection (K := K) w t) = t := by
  change Multiplicative.ofAdd (w * Real.log ‖((Real.exp (Multiplicative.toAdd t / w) : ℝ) : K)‖) = t
  rw [RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _), Real.log_exp, mul_comm w, div_mul_cancel₀ _ hw]
  rfl

private theorem scalarArchLog_ker_iff {w : ℝ} (hw : w ≠ 0) (a : Kˣ) :
    a ∈ (scalarArchLog (K := K) w).ker ↔ ‖(a : K)‖ = 1 := by
  change w * Real.log ‖(a : K)‖ = 0 ↔ _
  rw [mul_eq_zero, or_iff_right hw, Real.log_eq_zero]
  have hn : 0 < ‖(a : K)‖ := norm_pos_iff.mpr a.ne_zero
  constructor
  · rintro (h | h | h) <;> linarith
  · exact fun h => Or.inr (Or.inl h)

private theorem scalarArchLog_ker_compact {w : ℝ} (hw : w ≠ 0) :
    IsCompact ((scalarArchLog (K := K) w).ker : Set Kˣ) := by
  have hC : IsCompact (Metric.sphere (0 : K) 1) := isCompact_sphere _ _
  have he : ((scalarArchLog (K := K) w).ker : Set Kˣ) =
      Units.embedProduct K ⁻¹' (Metric.sphere (0 : K) 1 ×ˢ (MulOpposite.unop ⁻¹' Metric.sphere (0 : K) 1)) := by
    ext a
    refine (scalarArchLog_ker_iff hw a).trans ?_
    change ‖(a : K)‖ = 1 ↔
      (a : K) ∈ Metric.sphere (0 : K) 1 ∧ (↑a⁻¹ : K) ∈ Metric.sphere (0 : K) 1
    simp only [Metric.mem_sphere, dist_zero_right, Units.val_inv_eq_inv_val, norm_inv]
    exact ⟨fun h => ⟨h, by rw [h, inv_one]⟩, And.left⟩
  rw [he]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hC.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hC))

theorem scalarArchLog_proper {w : ℝ} (hw : w ≠ 0) : IsProperMap (scalarArchLog (K := K) w) := by
  let f := scalarArchLog (K := K) w
  let s := scalarArchSection (K := K) w
  haveI : CompactSpace f.ker := isCompact_iff_compactSpace.mp (scalarArchLog_ker_compact hw)
  let e : Multiplicative ℝ × f.ker ≃ₜ Kˣ := {
    toEquiv := (splitNormMulEquiv f s (scalarArchLog_section hw)).toEquiv
    continuous_toFun := ((scalarArchSection_continuous w).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
    continuous_invFun := (scalarArchLog_continuous w).prodMk
      ((continuous_id.div' ((scalarArchSection_continuous w).comp (scalarArchLog_continuous w))).subtype_mk _) }
  have he : f = Prod.fst ∘ e.symm := rfl
  rw [show ⇑(scalarArchLog (K := K) w) = Prod.fst ∘ e.symm from he]
  exact isProperMap_fst_of_compactSpace.comp e.symm.isProperMap

private def scalarArchAngularEquiv :
    Metric.sphere (0 : K) 1 ≃ₜ* (scalarArchLog (K := K) 1).ker where
  toFun u := ⟨unitSphereToUnits K u, (scalarArchLog_ker_iff one_ne_zero _).2
    (mem_sphere_zero_iff_norm.mp u.property)⟩
  invFun u := ⟨u.val.val, mem_sphere_zero_iff_norm.mpr ((scalarArchLog_ker_iff one_ne_zero _).1 u.property)⟩
  left_inv u := Subtype.ext rfl
  right_inv u := Subtype.ext (Units.ext rfl)
  map_mul' u v := Subtype.ext (map_mul (unitSphereToUnits K) _ _)
  continuous_toFun := by
    apply Continuous.subtype_mk _ _
    apply Units.continuous_iff.mpr
    exact ⟨continuous_subtype_val,
      continuous_subtype_val.inv₀ (fun u => ne_zero_of_mem_unit_sphere u)⟩
  continuous_invFun := (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

/-- Logarithmic radius and unit-sphere angle split the multiplicative group
of either archimedean scalar field. The radial coordinate is the logarithm
of the ordinary radius at both types of place. -/
def scalarArchPolar :
    Multiplicative ℝ × Metric.sphere (0 : K) 1 ≃ₜ* Kˣ := by
  let f := scalarArchLog (K := K) 1
  let s := scalarArchSection (K := K) 1
  let e : Multiplicative ℝ × f.ker ≃ₜ* Kˣ :=
    { toMulEquiv := splitNormMulEquiv f s (scalarArchLog_section one_ne_zero)
      continuous_toFun := ((scalarArchSection_continuous 1).comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (scalarArchLog_continuous 1).prodMk
        ((continuous_id.div' ((scalarArchSection_continuous 1).comp
          (scalarArchLog_continuous 1))).subtype_mk _) }
  let l : Multiplicative ℝ × Metric.sphere (0 : K) 1 ≃ₜ* Multiplicative ℝ × f.ker :=
    { toMulEquiv := (MulEquiv.refl _).prodCongr (scalarArchAngularEquiv (K := K)).toMulEquiv
      continuous_toFun := continuous_fst.prodMk ((scalarArchAngularEquiv (K := K)).continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk
        ((scalarArchAngularEquiv (K := K)).symm.continuous.comp continuous_snd) }
  exact l.trans e

@[simp] theorem scalarArchPolar_val (x : Multiplicative ℝ × Metric.sphere (0 : K) 1) :
    ((scalarArchPolar x : Kˣ) : K) = (Real.exp x.1.toAdd : K) * (x.2 : K) := by
  change (Real.exp (x.1.toAdd / 1) : K) * (x.2 : K) = _
  rw [div_one]

/-- The scalar logarithm is smooth off zero, and its real derivative
is surjective at every unit. -/
theorem scalarArchLog_submersion {w : ℝ} (hw : w ≠ 0) {a : K} (ha : a ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : K => w * Real.log ‖x‖) a ∧
    Surjective (fderiv ℝ (fun x : K => w * Real.log ‖x‖) a) := by
  let L (x : K) := w * Real.log ‖x‖
  have hL : ContDiffAt ℝ ∞ L a :=
    contDiffAt_const.mul ((contDiffAt_norm ℝ ha).log (norm_ne_zero_iff.mpr ha))
  let c (t : ℝ) : K := (Real.exp (t / w) : ℝ) • a
  have hc : ContDiff ℝ ∞ c :=
    (Real.contDiff_exp.comp (contDiff_id.div_const w)).smul contDiff_const
  have hc₀ : c 0 = a := by simp [c]
  have hcomp : L ∘ c = fun t => t + L a := by
    funext t
    change w * Real.log ‖((Real.exp (t / w) : ℝ) • a)‖ = _
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr ha), Real.log_exp, mul_add,
      mul_comm w (t / w), div_mul_cancel₀ _ hw]
  have hLd : DifferentiableAt ℝ L a := hL.differentiableAt (by simp)
  have hcd : DifferentiableAt ℝ c 0 := hc.differentiable (by simp) 0
  have hD := (hc₀.symm ▸ hLd.hasFDerivAt).comp 0 hcd.hasFDerivAt
  have hId := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).add_const (L a)
  rw [hcomp] at hD
  have hM := hD.unique hId
  refine ⟨hL, fun t => ⟨fderiv ℝ c 0 t, ?_⟩⟩
  have ht := DFunLike.congr_fun hM t
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hc₀] using ht

end Scalar

section InfinitePlaces

open NumberField

variable (F : Type*) [Field F] [NumberField F]

private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}
private abbrev Arch := mixedEmbedding.mixedSpace F
private abbrev LogVector := (RealPlaces F → ℝ) × (ComplexPlaces F → ℝ)

omit [NumberField F] in
/-- The real and complex coordinate isomorphism, with the topology on
the actual infinite adele ring. -/
def infiniteAdeleMixedHomeomorph : InfiniteAdeleRing F ≃ₜ Arch F where
  toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := infiniteAdele_toMixed_continuous F
  continuous_invFun := by
    apply continuous_pi
    intro v
    change Continuous (fun x : Arch F => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) v)
    by_cases hv : v.IsReal
    · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hv
      have he (x : Arch F) :
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) v = e.symm (x.1 ⟨v, hv⟩) := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact congrArg (fun y : Arch F => y.1 ⟨v, hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
      rw [show (fun x : Arch F => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) v) =
        (fun x => e.symm (x.1 ⟨v, hv⟩)) from funext he]
      exact e.symm.continuous.comp ((continuous_apply (⟨v, hv⟩ : RealPlaces F)).comp continuous_fst)
    · let hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv'
      have he (x : Arch F) :
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) v = e.symm (x.2 ⟨v, hv'⟩) := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact congrArg (fun y : Arch F => y.2 ⟨v, hv'⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
      rw [show (fun x : Arch F => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) v) =
        (fun x => e.symm (x.2 ⟨v, hv'⟩)) from funext he]
      exact e.symm.continuous.comp ((continuous_apply (⟨v, hv'⟩ : ComplexPlaces F)).comp continuous_snd)

/-- Transport the unit group of the infinite adele ring to mixed coordinates. -/
def infiniteAdeleUnitsMixed (F : Type*) [Field F] :
    (InfiniteAdeleRing F)ˣ ≃ₜ* (Arch F)ˣ where
  __ := Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
  continuous_toFun := Units.continuous_iff.mpr
    ⟨(infiniteAdeleMixedHomeomorph F).continuous.comp Units.continuous_val,
      (infiniteAdeleMixedHomeomorph F).continuous.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr
    ⟨(infiniteAdeleMixedHomeomorph F).symm.continuous.comp Units.continuous_val,
      (infiniteAdeleMixedHomeomorph F).symm.continuous.comp Units.continuous_coe_inv⟩

/-- The Archimedean units in their real and complex coordinates. -/
private def archUnitCoordinates :
    (Arch F)ˣ ≃ₜ ((RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ)) :=
  Homeomorph.prodUnits.trans
    (ContinuousMulEquiv.piUnits.toHomeomorph.prodCongr ContinuousMulEquiv.piUnits.toHomeomorph)

private def archUnitMulCoordinates :
    (Arch F)ˣ ≃* ((RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ)) :=
  MulEquiv.prodUnits.trans
    (ContinuousMulEquiv.piUnits.toMulEquiv.prodCongr ContinuousMulEquiv.piUnits.toMulEquiv)

omit [NumberField F] in
/-- Multiplicative real and complex coordinate splitting of the infinite ideles. -/
def infiniteAdeleUnitsCoordinates :
    (InfiniteAdeleRing F)ˣ ≃ₜ* ((RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ)) :=
  (infiniteAdeleUnitsMixed F).trans
    { toMulEquiv := archUnitMulCoordinates F
      continuous_toFun := (archUnitCoordinates F).continuous
      continuous_invFun := (archUnitCoordinates F).symm.continuous }

omit [NumberField F] in
@[simp] theorem infiniteAdeleUnitsCoordinates_real_val (a : (InfiniteAdeleRing F)ˣ)
    (v : RealPlaces F) :
    (((infiniteAdeleUnitsCoordinates F a).1 v : ℝˣ) : ℝ) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val).1 v := rfl

omit [NumberField F] in
@[simp] theorem infiniteAdeleUnitsCoordinates_complex_val (a : (InfiniteAdeleRing F)ˣ)
    (v : ComplexPlaces F) :
    (((infiniteAdeleUnitsCoordinates F a).2 v : ℂˣ) : ℂ) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F a.val).2 v := rfl

/-- The weighted logarithms of the real and complex absolute values. -/
def archLogVector (a : Arch F) : LogVector F :=
  (fun v => Real.log ‖a.1 v‖, fun v => 2 * Real.log ‖a.2 v‖)

def archLogHom : (Arch F)ˣ →*
    ((RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ)) :=
  ((MonoidHom.pi fun v : RealPlaces F =>
      (scalarArchLog (K := ℝ) 1).comp (Pi.evalMonoidHom (fun _ => ℝˣ) v)).prodMap
    (MonoidHom.pi fun v : ComplexPlaces F =>
      (scalarArchLog (K := ℂ) 2).comp (Pi.evalMonoidHom (fun _ => ℂˣ) v))).comp
  ((ContinuousMulEquiv.piUnits.toMulEquiv.prodCongr ContinuousMulEquiv.piUnits.toMulEquiv).toMonoidHom.comp
    MulEquiv.prodUnits.toMonoidHom)

omit [NumberField F] in
theorem archLogHom_proper :
    IsProperMap (archLogHom F) := by
  let L := fun a : RealPlaces F → ℝˣ => fun v => scalarArchLog (K := ℝ) 1 (a v)
  let M := fun a : ComplexPlaces F → ℂˣ => fun v => scalarArchLog (K := ℂ) 2 (a v)
  have hL : IsProperMap L := IsProperMap.pi_map fun _ => scalarArchLog_proper one_ne_zero
  have hM : IsProperMap M := IsProperMap.pi_map fun _ => scalarArchLog_proper two_ne_zero
  exact (hL.prodMap hM).comp (archUnitCoordinates F).isProperMap

omit [NumberField F] in
/-- A continuous section of the full Archimedean logarithm,
taking every local phase to the positive real axis. -/
def archLogSection :
    ((RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ)) →* (Arch F)ˣ :=
  (archUnitMulCoordinates F).symm.toMonoidHom.comp
    ((MonoidHom.pi fun v : RealPlaces F =>
        (scalarArchSection (K := ℝ) 1).comp (Pi.evalMonoidHom _ v)).prodMap
      (MonoidHom.pi fun v : ComplexPlaces F =>
        (scalarArchSection (K := ℂ) 2).comp (Pi.evalMonoidHom _ v)))

omit [NumberField F] in
theorem archLogSection_continuous : Continuous (archLogSection F) := by
  apply (archUnitCoordinates F).symm.continuous.comp
  exact (continuous_pi fun v : RealPlaces F => (scalarArchSection_continuous (K := ℝ) 1).comp
    ((continuous_apply v).comp continuous_fst)).prodMk
    (continuous_pi fun v : ComplexPlaces F => (scalarArchSection_continuous (K := ℂ) 2).comp
      ((continuous_apply v).comp continuous_snd))

omit [NumberField F] in
theorem archLogHom_section (t : (RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ)) :
    archLogHom F (archLogSection F t) = t := by
  let s :=
    (fun v => scalarArchSection (K := ℝ) 1 (t.1 v),
     fun v => scalarArchSection (K := ℂ) 2 (t.2 v))
  have he := (archUnitCoordinates F).apply_symm_apply s
  change
    (fun v => scalarArchLog (K := ℝ) 1 ((archUnitCoordinates F ((archUnitCoordinates F).symm s)).1 v),
     fun v => scalarArchLog (K := ℂ) 2 ((archUnitCoordinates F ((archUnitCoordinates F).symm s)).2 v)) = t
  rw [he]
  exact Prod.ext (funext fun v => scalarArchLog_section one_ne_zero (t.1 v))
    (funext fun v => scalarArchLog_section two_ne_zero (t.2 v))

omit [NumberField F] in
theorem archLogHom_surjective : Surjective (archLogHom F) :=
  fun t => ⟨archLogSection F t, archLogHom_section F t⟩

omit [NumberField F] in
private theorem realCoordinate_nonzero (a : (Arch F)ˣ) (v : RealPlaces F) :
    a.val.1 v ≠ 0 := by
  have h := congrArg (fun x : Arch F => x.1 v) a.val_inv
  change a.val.1 v * a.inv.1 v = 1 at h
  exact left_ne_zero_of_mul_eq_one h

omit [NumberField F] in
private theorem complexCoordinate_nonzero (a : (Arch F)ˣ) (v : ComplexPlaces F) :
    a.val.2 v ≠ 0 := by
  have h := congrArg (fun x : Arch F => x.2 v) a.val_inv
  change a.val.2 v * a.inv.2 v = 1 at h
  exact left_ne_zero_of_mul_eq_one h

/-- In the open real and complex coordinate chart of the unit group, the
map to the weighted logarithmic coordinates is smooth. -/
theorem archLogVector_smooth (a : (Arch F)ˣ) : ContDiffAt ℝ ∞ (archLogVector F) a.val := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro v
    have h : ContDiffAt ℝ ∞ (fun x : Arch F => x.1 v) a.val :=
      ((ContinuousLinearMap.proj (R := ℝ) v).comp
        (ContinuousLinearMap.fst ℝ (RealPlaces F → ℝ) (ComplexPlaces F → ℂ))).contDiff.contDiffAt
    have hr := ((scalarArchLog_submersion one_ne_zero (realCoordinate_nonzero F a v)).1).comp a.val h
    simpa only [Function.comp_def, one_mul] using hr
  · apply contDiffAt_pi.mpr
    intro v
    have h : ContDiffAt ℝ ∞ (fun x : Arch F => x.2 v) a.val :=
      ((ContinuousLinearMap.proj (R := ℝ) v).comp
        (ContinuousLinearMap.snd ℝ (RealPlaces F → ℝ) (ComplexPlaces F → ℂ))).contDiff.contDiffAt
    have hz : ContDiffAt ℝ ∞ ((fun z : ℂ => 2 * Real.log ‖z‖) ∘ (fun x : Arch F => x.2 v)) a.val :=
      ((scalarArchLog_submersion two_ne_zero (complexCoordinate_nonzero F a v)).1).comp a.val h
    exact hz

private def archRadial (a : Arch F) (t : LogVector F) : Arch F :=
  (fun v => Real.exp (t.1 v) * a.1 v,
   fun v => Real.exp (t.2 v / 2) • a.2 v)

private theorem archRadial_smooth (a : Arch F) : ContDiff ℝ ∞ (archRadial F a) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro v
    have h : ContDiff ℝ ∞ (fun t : LogVector F => t.1 v) :=
      ((ContinuousLinearMap.proj (R := ℝ) v).comp
        (ContinuousLinearMap.fst ℝ (RealPlaces F → ℝ) (ComplexPlaces F → ℝ))).contDiff
    exact (Real.contDiff_exp.comp h).mul contDiff_const
  · apply contDiff_pi.mpr
    intro v
    have h : ContDiff ℝ ∞ (fun t : LogVector F => t.2 v) :=
      ((ContinuousLinearMap.proj (R := ℝ) v).comp
        (ContinuousLinearMap.snd ℝ (RealPlaces F → ℝ) (ComplexPlaces F → ℝ))).contDiff
    exact (Real.contDiff_exp.comp (h.div_const 2)).smul contDiff_const

omit [NumberField F] in
private theorem archRadial_zero (a : Arch F) : archRadial F a 0 = a := by
  apply Prod.ext <;> funext v <;> simp [archRadial]

omit [NumberField F] in
private theorem archRadial_log (a : (Arch F)ˣ) :
    archLogVector F ∘ archRadial F a.val = fun t => t + archLogVector F a.val := by
  funext t
  apply Prod.ext
  · funext v
    change Real.log ‖Real.exp (t.1 v) * a.val.1 v‖ = t.1 v + Real.log ‖a.val.1 v‖
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (realCoordinate_nonzero F a v)),
      Real.log_exp]
  · funext v
    change 2 * Real.log ‖Real.exp (t.2 v / 2) • a.val.2 v‖ =
      t.2 v + 2 * Real.log ‖a.val.2 v‖
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (complexCoordinate_nonzero F a v)),
      Real.log_exp]
    ring

/-- The differential of the Archimedean logarithmic map surjects onto
the full space of logarithmic coordinates. A right inverse is obtained
by differentiating the positive radial rescaling. -/
theorem archLogVector_submersion (a : (Arch F)ˣ) :
    Surjective (fderiv ℝ (archLogVector F) a.val) := by
  let L := archLogVector F
  let c := archRadial F a.val
  have hL := (archLogVector_smooth F a).differentiableAt (by simp)
  have hc := (archRadial_smooth F a.val).differentiable (by simp) 0
  have hLoc : HasFDerivAt L (fderiv ℝ L a.val) (c 0) :=
    (archRadial_zero F a.val).symm ▸ hL.hasFDerivAt
  have h := hLoc.comp (0 : LogVector F) hc.hasFDerivAt
  change HasFDerivAt (L ∘ c) ((fderiv ℝ L a.val).comp (fderiv ℝ c 0)) 0 at h
  rw [show L ∘ c = fun t => t + L a.val from archRadial_log F a] at h
  have h' := h.unique ((hasFDerivAt_id (𝕜 := ℝ) (0 : LogVector F)).add_const (L a.val))
  intro t
  exact ⟨fderiv ℝ c 0 t, DFunLike.congr_fun h' t⟩

/-- The product formula for the Archimedean modulus in mixed coordinates. -/
def archModulus (a : Arch F) : ℝ :=
  (∏ v : RealPlaces F, ‖a.1 v‖) * (∏ v : ComplexPlaces F, ‖a.2 v‖ ^ 2)

theorem archModulus_of_infiniteAdele (a : InfiniteAdeleRing F) :
    archModulus F (InfiniteAdeleRing.ringEquiv_mixedSpace F a) = ‖a‖ := by
  rw [InfiniteAdeleRing.norm_def, ← Fintype.prod_subtype_mul_prod_subtype
    (fun v : InfinitePlace F => v.IsReal)]
  unfold archModulus
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [v.property.mult_eq_one, pow_one]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.property).norm_map_of_map_zero
      (map_zero _)) _
  · let e : ComplexPlaces F ≃ {v : InfinitePlace F // ¬ v.IsReal} :=
      Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex.symm)
    apply Fintype.prod_equiv e
    intro v
    change ‖InfinitePlace.Completion.extensionEmbedding v.val (a v.val)‖ ^ 2 =
      ‖a v.val‖ ^ v.val.mult
    rw [v.property.mult_eq_two,
      (InfinitePlace.Completion.isometry_extensionEmbedding v.val).norm_map_of_map_zero (map_zero _)]

theorem archLogVector_sum (a : (Arch F)ˣ) :
    (∑ v : RealPlaces F, (archLogVector F a.val).1 v) +
    (∑ v : ComplexPlaces F, (archLogVector F a.val).2 v) =
    Real.log (archModulus F a.val) := by
  have hR (v : RealPlaces F) : ‖a.val.1 v‖ ≠ 0 := norm_ne_zero_iff.mpr (realCoordinate_nonzero F a v)
  have hC (v : ComplexPlaces F) : ‖a.val.2 v‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (complexCoordinate_nonzero F a v))
  unfold archModulus
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _ => hR v)
      (Finset.prod_ne_zero_iff.mpr fun v _ => hC v), Real.log_prod (fun v _ => hR v),
    Real.log_prod (fun v _ => hC v)]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  change 2 * Real.log ‖a.val.2 v‖ = Real.log (‖a.val.2 v‖ ^ 2)
  rw [Real.log_pow]
  norm_num

/-- The norm-one locus lies in the trace-zero logarithmic hyperplane. -/
theorem archLogVector_normOne (a : (Arch F)ˣ) (ha : archModulus F a.val = 1) :
    (∑ v : RealPlaces F, (archLogVector F a.val).1 v) +
      (∑ v : ComplexPlaces F, (archLogVector F a.val).2 v) = 0 := by
  rw [archLogVector_sum F a, ha, Real.log_one]

private abbrev RealSigns := Metric.sphere (0 : ℝ) 1

theorem realSigns_eq_one_or_neg_one (x : RealSigns) : (x : ℝ) = 1 ∨ (x : ℝ) = -1 := by
  have hx := mem_sphere_zero_iff_norm.mp x.property
  rwa [Real.norm_eq_abs, abs_eq (by norm_num : 0 ≤ (1 : ℝ))] at hx

omit [NumberField F] in
private theorem archLogHom_kernel_iff (a : (Arch F)ˣ) :
    a ∈ (archLogHom F).ker ↔
      (∀ v : RealPlaces F, ‖((archUnitCoordinates F a).1 v : ℝ)‖ = 1) ∧
      (∀ v : ComplexPlaces F, ‖((archUnitCoordinates F a).2 v : ℂ)‖ = 1) := by
  change
    (fun v => scalarArchLog (K := ℝ) 1 ((archUnitCoordinates F a).1 v),
      fun v => scalarArchLog (K := ℂ) 2 ((archUnitCoordinates F a).2 v)) = 1 ↔ _
  constructor
  · intro h
    exact ⟨fun v => (scalarArchLog_ker_iff one_ne_zero _).mp (congrFun (congrArg Prod.fst h) v),
      fun v => (scalarArchLog_ker_iff two_ne_zero _).mp (congrFun (congrArg Prod.snd h) v)⟩
  · rintro ⟨h, h'⟩
    exact Prod.ext (funext fun v => (scalarArchLog_ker_iff one_ne_zero _).mpr (h v))
      (funext fun v => (scalarArchLog_ker_iff two_ne_zero _).mpr (h' v))

private def archAngular (a : (archLogHom F).ker) :
    (RealPlaces F → RealSigns) × (ComplexPlaces F → Circle) :=
  (fun v => ⟨((archUnitCoordinates F a.val).1 v : ℝ),
    mem_sphere_zero_iff_norm.mpr (((archLogHom_kernel_iff F a.val).mp a.property).1 v)⟩,
   fun v => ⟨((archUnitCoordinates F a.val).2 v : ℂ),
    mem_sphere_zero_iff_norm.mpr (((archLogHom_kernel_iff F a.val).mp a.property).2 v)⟩)

private theorem continuous_unitSphereToUnits {K : Type*} [RCLike K] :
    Continuous (unitSphereToUnits K) := by
  apply Units.continuous_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere

/-- Lemma A.2.3.2(2). The compact kernel consists of independent real
signs and complex phases, with their intrinsic topological group laws. -/
def archLogKernelPhases : (archLogHom F).ker ≃ₜ*
    ((RealPlaces F → RealSigns) × (ComplexPlaces F → Circle)) where
  toFun := archAngular F
  invFun p :=
    let a := (archUnitCoordinates F).symm
      (fun v => unitSphereToUnits ℝ (p.1 v), fun v => unitSphereToUnits ℂ (p.2 v))
    ⟨a, (archLogHom_kernel_iff F a).mpr (by
      dsimp [a]
      rw [(archUnitCoordinates F).apply_symm_apply]
      exact ⟨fun v => mem_sphere_zero_iff_norm.mp (p.1 v).property,
        fun v => mem_sphere_zero_iff_norm.mp ((p.2 v).property : (p.2 v : ℂ) ∈ Metric.sphere 0 1)⟩)⟩
  left_inv a := by
    apply Subtype.ext
    apply (archUnitCoordinates F).injective
    rw [(archUnitCoordinates F).apply_symm_apply]
    apply Prod.ext <;> funext v <;> apply Units.ext <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext v <;> apply Subtype.ext
    · change (((archUnitCoordinates F) ((archUnitCoordinates F).symm
        (fun v => unitSphereToUnits ℝ (p.1 v), fun v => unitSphereToUnits ℂ (p.2 v)))).1 v : ℝ) = _
      rw [(archUnitCoordinates F).apply_symm_apply]
      rfl
    · change (((archUnitCoordinates F) ((archUnitCoordinates F).symm
        (fun v => unitSphereToUnits ℝ (p.1 v), fun v => unitSphereToUnits ℂ (p.2 v)))).2 v : ℂ) = _
      rw [(archUnitCoordinates F).apply_symm_apply]
      rfl
  map_mul' a b := by
    have h := (archUnitMulCoordinates F).map_mul a.val b.val
    apply Prod.ext <;> funext v <;> apply Subtype.ext
    · exact congrArg (fun p : (RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ) => (p.1 v : ℝ)) h
    · exact congrArg (fun p : (RealPlaces F → ℝˣ) × (ComplexPlaces F → ℂˣ) => (p.2 v : ℂ)) h
  continuous_toFun := by
    have hk := (archUnitCoordinates F).continuous.comp
      (continuous_subtype_val : Continuous ((↑) : (archLogHom F).ker → (Arch F)ˣ))
    apply Continuous.prodMk
    · exact continuous_pi fun v => (Units.continuous_val.comp
        ((continuous_apply v).comp hk.fst)).subtype_mk _
    · exact continuous_pi fun v => (Units.continuous_val.comp
        ((continuous_apply v).comp hk.snd)).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (archUnitCoordinates F).symm.continuous.comp
    exact (continuous_pi fun v => continuous_unitSphereToUnits.comp
      ((continuous_apply v).comp continuous_fst)).prodMk
        (continuous_pi fun v => continuous_unitSphereToUnits.comp
          ((continuous_apply v).comp continuous_snd))

omit [NumberField F] in
theorem archLogKernel_compact : IsCompact ((archLogHom F).ker : Set (Arch F)ˣ) :=
  (archLogHom_proper F).isCompact_preimage isCompact_singleton

/-- Viewing the angular coordinates in the ambient Archimedean space,
the comparison is the identity. This supplies smooth ambient extensions
in both directions for the embedded real sign and complex circle loci. -/
theorem archLogKernelPhases_ambient :
    let j (p : (RealPlaces F → RealSigns) × (ComplexPlaces F → Circle)) : Arch F :=
      (fun v => (p.1 v : ℝ), fun v => (p.2 v : ℂ))
    (∀ a : (archLogHom F).ker, j (archLogKernelPhases F a) = a.val.val) ∧
    (∀ p, ((archLogKernelPhases F).symm p).val.val = j p) ∧
    ContDiff ℝ ∞ (id : Arch F → Arch F) := by
  dsimp only
  constructor
  · intro a
    rfl
  constructor
  · intro p
    have h := (archLogKernelPhases F).apply_symm_apply p
    rw [← h]
    rfl
  · exact contDiff_id

/-- The proper logarithmic homomorphism on the actual infinite ideles. -/
def infiniteIdeleArchLog :
    (InfiniteAdeleRing F)ˣ →* ((RealPlaces F → Multiplicative ℝ) × (ComplexPlaces F → Multiplicative ℝ)) :=
  (archLogHom F).comp (infiniteAdeleUnitsMixed F).toMonoidHom

omit [NumberField F] in
theorem infiniteIdeleArchLog_proper : IsProperMap (infiniteIdeleArchLog F) :=
  (archLogHom_proper F).comp (infiniteAdeleUnitsMixed F).toHomeomorph.isProperMap

/-- The sum of the logarithms of the normalized absolute values. -/
def archTotalLog (a : Arch F) : ℝ :=
  (∑ v : RealPlaces F, (archLogVector F a).1 v) +
  (∑ v : ComplexPlaces F, (archLogVector F a).2 v)

def archTotalLogHom : (Arch F)ˣ →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd (archTotalLog F a.val)
  map_one' := by simp [archTotalLog, archLogVector]
  map_mul' a b := by
    change Multiplicative.ofAdd (archTotalLog F (a.val * b.val)) =
      Multiplicative.ofAdd (archTotalLog F a.val + archTotalLog F b.val)
    congr 1
    have hR (v : RealPlaces F) :
        Real.log ‖a.val.1 v * b.val.1 v‖ = Real.log ‖a.val.1 v‖ + Real.log ‖b.val.1 v‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (realCoordinate_nonzero F a v))
        (norm_ne_zero_iff.mpr (realCoordinate_nonzero F b v))]
    have hC (v : ComplexPlaces F) :
        Real.log ‖a.val.2 v * b.val.2 v‖ = Real.log ‖a.val.2 v‖ + Real.log ‖b.val.2 v‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (complexCoordinate_nonzero F a v))
        (norm_ne_zero_iff.mpr (complexCoordinate_nonzero F b v))]
    simp only [archTotalLog, archLogVector, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
      hR, hC, mul_add, Finset.sum_add_distrib]
    abel

theorem archTotalLogHom_apply (a : (Arch F)ˣ) :
    Multiplicative.toAdd (archTotalLogHom F a) = Real.log (archModulus F a.val) :=
  archLogVector_sum F a

theorem archTotalLog_ker_iff (a : (Arch F)ˣ) :
    a ∈ (archTotalLogHom F).ker ↔ archModulus F a.val = 1 := by
  have hp : 0 < archModulus F a.val := mul_pos
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (realCoordinate_nonzero F a v))
    (Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.mpr (complexCoordinate_nonzero F a v)) _)
  change Multiplicative.toAdd (archTotalLogHom F a) = 0 ↔ _
  rw [archTotalLogHom_apply, Real.log_eq_zero]
  constructor
  · rintro (h | h | h) <;> linarith
  · exact fun h => Or.inr (Or.inl h)

theorem archTotalLog_smooth (a : (Arch F)ˣ) : ContDiffAt ℝ ∞ (archTotalLog F) a.val := by
  have h := archLogVector_smooth F a
  have h₁ (v : RealPlaces F) :
      ContDiffAt ℝ ∞ (fun x => (archLogVector F x).1 v) a.val := (contDiffAt_pi.mp h.fst) v
  have h₂ (v : ComplexPlaces F) :
      ContDiffAt ℝ ∞ (fun x => (archLogVector F x).2 v) a.val := (contDiffAt_pi.mp h.snd) v
  exact (ContDiffAt.sum fun v _ => h₁ v).add (ContDiffAt.sum fun v _ => h₂ v)

theorem archTotalLogHom_continuous : Continuous (archTotalLogHom F) := by
  change Continuous (fun a : (Arch F)ˣ => Multiplicative.ofAdd (archTotalLog F a.val))
  apply continuous_ofAdd.comp
  exact continuous_iff_continuousAt.mpr fun a =>
    (archTotalLog_smooth F a).continuousAt.comp Units.continuous_val.continuousAt

private def archSectionValue (τ : Multiplicative ℝ →* (Arch F)ˣ) (t : ℝ) : Arch F :=
  (τ (Multiplicative.ofAdd t)).val

/-- Any continuous real one-parameter subgroup of Archimedean units is smooth
in the standard finite product chart. -/
theorem archSection_smooth (τ : Multiplicative ℝ →* (Arch F)ˣ) (hτ : Continuous τ) :
    ContDiff ℝ ∞ (archSectionValue F τ) := by
  let e := archUnitMulCoordinates F
  let X := (RealPlaces F → ℝˣ)
  let Y := (ComplexPlaces F → ℂˣ)
  have hE : Continuous (e ∘ τ) := (archUnitCoordinates F).continuous.comp hτ
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro v
    let f := (Pi.evalMonoidHom (fun _ => ℝˣ) v).comp
      ((MonoidHom.fst X Y).comp (e.toMonoidHom.comp τ))
    have h : Continuous (fun t : ℝ => ((f (Multiplicative.ofAdd t)) : ℝ)) :=
      Units.continuous_val.comp (((continuous_apply v).comp hE.fst).comp continuous_ofAdd)
    exact (continuous_oneParameter_smooth f h).1
  · apply contDiff_pi.mpr
    intro v
    let f := (Pi.evalMonoidHom (fun _ => ℂˣ) v).comp
      ((MonoidHom.snd X Y).comp (e.toMonoidHom.comp τ))
    have h : Continuous (fun t : ℝ => ((f (Multiplicative.ofAdd t)) : ℂ)) :=
      Units.continuous_val.comp (((continuous_apply v).comp hE.snd).comp continuous_ofAdd)
    exact (continuous_oneParameter_smooth f h).1

/-- The splitting by any continuous homomorphic section of the norm, expressed
in logarithmic coordinates for the positive real factor. -/
def archSplit (τ : Multiplicative ℝ →* (Arch F)ˣ)
    (hτ : Continuous τ) (hs : ∀ t, archTotalLogHom F (τ t) = t) :
    (Multiplicative ℝ × (archTotalLogHom F).ker) ≃ₜ* (Arch F)ˣ where
  __ := splitNormMulEquiv (archTotalLogHom F) τ hs
  continuous_toFun := (hτ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (archTotalLogHom_continuous F).prodMk
    ((continuous_id.div' (hτ.comp (archTotalLogHom_continuous F))).subtype_mk _)

/-- Lemma A.2.3.11. The multiplication splitting and its inverse are smooth
in their natural ambient charts. The intrinsic norm-one locus carries the
induced smooth structure, and the norm coordinate is the logarithm. -/
theorem archSplit_smooth (τ : Multiplicative ℝ →* (Arch F)ˣ) (hτ : Continuous τ)
    (hs : ∀ t, archTotalLogHom F (τ t) = t) :
    let e := archSplit F τ hτ hs
    (∀ t u, (e (Multiplicative.ofAdd t, u)).val = archSectionValue F τ t * u.val.val) ∧
    (∀ a, (Multiplicative.toAdd (e.symm a).1, (e.symm a).2.val.val) =
      (archTotalLog F a.val, a.val * archSectionValue F τ (-archTotalLog F a.val))) ∧
    ContDiff ℝ ∞ (fun p : ℝ × Arch F => archSectionValue F τ p.1 * p.2) ∧
    (∀ a : (Arch F)ˣ, ContDiffAt ℝ ∞
      (fun x : Arch F => (archTotalLog F x, x * archSectionValue F τ (-archTotalLog F x))) a.val) := by
  have hh := archSection_smooth F τ hτ
  refine ⟨fun _ _ => rfl, ?_, (hh.comp contDiff_fst).mul contDiff_snd, ?_⟩
  · intro a
    apply Prod.ext
    · rfl
    change a.val * ((τ (archTotalLogHom F a))⁻¹ : (Arch F)ˣ).val =
      a.val * (τ (Multiplicative.ofAdd (-archTotalLog F a.val))).val
    rw [show Multiplicative.ofAdd (-archTotalLog F a.val) = (archTotalLogHom F a)⁻¹ from rfl, map_inv]
  · intro a
    have hl := archTotalLog_smooth F a
    exact hl.prodMk (contDiffAt_id.mul (hh.contDiffAt.comp a.val hl.neg))

end InfinitePlaces


end

end Masullo
