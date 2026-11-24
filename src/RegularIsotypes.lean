import CompactGroupAveraging
import LeftRegularRepresentation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Integral.Prod

open Filter Function MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (ν : Measure G) [ν.IsHaarMeasure]

/-- The regular representation as a monoid of continuous linear maps. -/
def leftRegularAction : G →* (HaarL2 ν →L[ℂ] HaarL2 ν) where
  toFun g := (leftRegularLinearIsometry ν g).toContinuousLinearMap
  map_one' := by
    ext f : 1
    change DomMulAct.mk ((1 : G)⁻¹) • f = f
    rw [inv_one, DomMulAct.mk_one, one_smul]
  map_mul' g h := by
    ext f : 1
    exact leftRegularUnitary_mul ν g h f

variable (H : Subgroup G) [CompactSpace H] (μ : Measure H) [μ.IsHaarMeasure]

/-- The restriction of the left regular representation to a subgroup. -/
abbrev subgroupRegularAction : H →* (HaarL2 ν →L[ℂ] HaarL2 ν) :=
  (leftRegularAction ν).comp H.subtype

/-- Pointwise averaging with the inverse character. The resulting function
will be identified almost everywhere with the Pettis average in (L^2). -/
def regularIsotypeKernel (ω : H →* Circle) (f : HaarL2 ν) (x : G) : ℂ :=
  ∫ g, (((ω g)⁻¹ : Circle) : ℂ) * f ((g : G)⁻¹ * x) ∂μ

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [ν.IsHaarMeasure] in
/-- The equivalent form of the orbit integral after changing the variable by inversion. -/
theorem regularIsotypeKernel_eq_direct (ω : H →* Circle) (f : HaarL2 ν) (x : G) :
    regularIsotypeKernel ν H μ ω f x =
      ∫ g, (ω g : ℂ) * f ((g : G) * x) ∂μ := by
  unfold regularIsotypeKernel
  have h := integral_inv_eq_self (fun g : H => (ω g : ℂ) * f ((g : G) * x)) μ
  simpa only [map_inv, Subgroup.coe_inv] using h

private theorem integral_norm_sq_bound {X : Type*} [MeasurableSpace X] (η : Measure X)
    [IsFiniteMeasure η] {f : X → ℂ} (hf : MemLp f 2 η) :
    ‖∫ x, f x ∂η‖ ^ 2 ≤ η.real univ * ∫ x, ‖f x‖ ^ 2 ∂η := by
  have htwo : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have hnorm : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) η := by simpa using hf.norm
  have hone : MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal 2) η := memLp_const _
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg htwo
    (Eventually.of_forall fun x => norm_nonneg (f x))
    (Eventually.of_forall fun _ => zero_le_one) hnorm hone
  simp only [mul_one, Real.rpow_ofNat, one_pow, integral_const, smul_eq_mul, mul_one] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂η := integral_nonneg fun _ => sq_nonneg _
  have hM : 0 ≤ η.real univ := ENNReal.toReal_nonneg
  have hb := sq_le_sq' (neg_nonpos.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    |>.trans (norm_nonneg (∫ x, f x ∂η))) ((norm_integral_le_integral_norm _).trans h)
  rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hM, mul_comm] at hb
  exact hb

private def regularIntegrand (ω : H →* Circle) (f : HaarL2 ν) (z : H × G) : ℂ :=
  (((ω z.1)⁻¹ : Circle) : ℂ) * f ((z.1 : G)⁻¹ * z.2)

omit [T2Space G] [LocallyCompactSpace G] [ν.IsHaarMeasure] [CompactSpace H] in
private theorem regularIntegrand_measurable (ω : H →* Circle) (hω : Continuous ω)
    (f : HaarL2 ν) : Measurable (regularIntegrand ν H ω f) :=
  (continuous_subtype_val.comp (hω.comp continuous_fst).inv).measurable.mul
    ((Lp.stronglyMeasurable f).measurable.comp
      ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd).measurable)

omit [T2Space G] in
private theorem regularIntegrand_memLp (ω : H →* Circle) (hω : Continuous ω)
    (f : HaarL2 ν) :
    MemLp (regularIntegrand ν H ω f) 2 (μ.prod ν) := by
  let K := regularIntegrand ν H ω f
  have hK : Measurable K := regularIntegrand_measurable ν H ω hω f
  have hKn (g : H) (x : G) : ‖K (g, x)‖ = ‖f ((g : G)⁻¹ * x)‖ := by
    change ‖(((ω g)⁻¹ : Circle) : ℂ) * f ((g : G)⁻¹ * x)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hsq : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).2
  apply (integrable_prod_iff (hK.norm.pow_const 2).aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall fun g => by
      simp_rw [hKn]
      exact (measurePreserving_mul_left ν (g : G)⁻¹).integrable_comp_of_integrable hsq
  · have hI (g : H) : (∫ y, ‖‖K (g, y)‖ ^ 2‖ ∂ν) = ∫ y, ‖f y‖ ^ 2 ∂ν := by
      simp_rw [norm_pow, norm_norm, hKn]
      exact integral_mul_left_eq_self (μ := ν) (fun y => ‖f y‖ ^ 2) (g : G)⁻¹
    simp_rw [hI]
    exact integrable_const _

omit [T2Space G] in
private theorem regularIsotypeKernel_memLp (ω : H →* Circle) (hω : Continuous ω)
    (f : HaarL2 ν) :
    MemLp (regularIsotypeKernel ν H μ ω f) 2 ν := by
  let K := regularIntegrand ν H ω f
  have hK : Measurable K := regularIntegrand_measurable ν H ω hω f
  have hprod : Integrable (fun z => ‖K z‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 (regularIntegrand_memLp ν H μ ω hω f)
  have hLim : Integrable (fun x => ∫ g, ‖K (g, x)‖ ^ 2 ∂μ) ν := hprod.integral_prod_right
  have hsm : StronglyMeasurable (regularIsotypeKernel ν H μ ω f) :=
    hK.stronglyMeasurable.integral_prod_left' (μ := μ)
  apply (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).mpr
  refine (hLim.const_mul (μ.real univ)).mono (hsm.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [hprod.prod_left_ae] with x hx
  have hφ : MemLp (fun g => K (g, x)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm
      (hK.comp measurable_prodMk_right).aestronglyMeasurable).mpr hx
  have hM : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hS : 0 ≤ ∫ g, ‖K (g, x)‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (mul_nonneg hM hS)]
  exact integral_norm_sq_bound μ hφ

omit [T2Space G] in
private theorem regularAverage_ae (ω : H →* Circle) (hω : Continuous ω)
    (Φ : HaarL2 ν →L[ℂ] HaarL2 ν)
    (hΦ : ∀ f, HasPositivePettisIntegral μ
      (fun g => twistedCircleAction ω (subgroupRegularAction ν H) g f) (Φ f))
    (f : HaarL2 ν) : (Φ f : G → ℂ) =ᵐ[ν] regularIsotypeKernel ν H μ ω f := by
  let K := regularIntegrand ν H ω f
  let Q := regularIsotypeKernel ν H μ ω f
  have hQ : MemLp Q 2 ν := regularIsotypeKernel_memLp ν H μ ω hω f
  have hEq : hQ.toLp Q = Φ f := by
    apply ext_inner_left ℂ
    intro w
    let A := twistedCircleAction ω (subgroupRegularAction ν H)
    have hKL : MemLp K 2 (μ.prod ν) := regularIntegrand_memLp ν H μ ω hω f
    have hw : MemLp (fun z : H × G => w z.2) 2 (μ.prod ν) := (Lp.memLp w).comp_snd μ
    have hprod : Integrable (fun z : H × G => ⟪w z.2, K z⟫_ℂ) (μ.prod ν) := by
      apply (L2.integrable_inner (𝕜 := ℂ) (hw.toLp _) (hKL.toLp K)).congr
      filter_upwards [hw.coeFn_toLp, hKL.coeFn_toLp] with z hwa hKa
      simp only [hwa, hKa]
    have hRow (g : H) : ((A g f : HaarL2 ν) : G → ℂ) =ᵐ[ν] fun x => K (g, x) := by
      change (↑↑((((ω g)⁻¹ : Circle) : ℂ) • leftRegularUnitary ν (g : G) f) : G → ℂ)
        =ᵐ[ν] fun x => K (g, x)
      exact (Lp.coeFn_smul _ _).trans ((leftRegularUnitary_ae ν (g : G) f).mono
        fun x hx => congrArg ((((ω g)⁻¹ : Circle) : ℂ) * ·) hx)
    have hRowInt (g : H) :
        (∫ x, ⟪w x, K (g, x)⟫_ℂ ∂ν) = ⟪w, A g f⟫_ℂ := by
      rw [L2.inner_def]
      exact integral_congr_ae ((hRow g).symm.mono fun x hx => congrArg (fun v => ⟪w x, v⟫_ℂ) hx)
    calc
      ⟪w, hQ.toLp Q⟫_ℂ = ∫ x, ⟪w x, Q x⟫_ℂ ∂ν := by
        rw [L2.inner_def]
        exact integral_congr_ae (hQ.coeFn_toLp.mono fun x hx => congrArg (fun v => ⟪w x, v⟫_ℂ) hx)
      _ = ∫ x, ∫ g, ⟪w x, K (g, x)⟫_ℂ ∂μ ∂ν := by
        apply integral_congr_ae
        have hp2 : Integrable (fun z => ‖K z‖ ^ 2) (μ.prod ν) :=
          (memLp_two_iff_integrable_sq_norm hKL.1).mp hKL
        have hm := regularIntegrand_measurable ν H ω hω f
        filter_upwards [hp2.prod_left_ae] with x hx
        have hLp : MemLp (fun g => K (g, x)) 2 μ :=
          (memLp_two_iff_integrable_sq_norm
            (hm.comp measurable_prodMk_right).aestronglyMeasurable).2 hx
        exact (integral_inner (memLp_one_iff_integrable.mp (hLp.mono_exponent one_le_two)) (w x)).symm
      _ = ∫ g, ∫ x, ⟪w x, K (g, x)⟫_ℂ ∂ν ∂μ := (integral_integral_swap hprod).symm
      _ = ∫ g, ⟪w, A g f⟫_ℂ ∂μ := integral_congr_ae (Eventually.of_forall hRowInt)
      _ = ⟪w, Φ f⟫_ℂ := (hΦ f (innerSL ℂ w)).2.symm
  rw [← hEq]
  exact hQ.coeFn_toLp

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [CompactSpace H] in
private theorem twistedRegular_inner (ω : H →* Circle) (g : H) (u v : HaarL2 ν) :
    let A := twistedCircleAction ω (subgroupRegularAction ν H)
    ⟪A g u, A g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  change ⟪(((ω g)⁻¹ : Circle) : ℂ) • leftRegularUnitary ν (g : G) u,
    (((ω g)⁻¹ : Circle) : ℂ) • leftRegularUnitary ν (g : G) v⟫_ℂ = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, ← Circle.coe_inv_eq_conj,
    ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul,
    LinearIsometryEquiv.inner_map_map]

omit [T2Space G] in
/-- Corollary 4.3.3.4. The pointwise and Pettis isotypic integrals coincide.
The normalized operators are orthogonal projectors, with orthogonal
ranges for different characters. -/
theorem regularIsotypicProjectors :
    ∃ Φ : {ω : H →* Circle // Continuous ω} → (HaarL2 ν →L[ℂ] HaarL2 ν),
      (∀ ω f, HasPositivePettisIntegral μ
        (fun g => twistedCircleAction ω.val (subgroupRegularAction ν H) g f) (Φ ω f) ∧
        (Φ ω f : G → ℂ) =ᵐ[ν] regularIsotypeKernel ν H μ ω.val f) ∧
      (∀ ω, ∃ hU : CompleteSpace (fixedSubmodule (twistedCircleAction ω.val
          (subgroupRegularAction ν H))),
        letI := hU
        (μ.real univ : ℂ)⁻¹ • Φ ω =
          (fixedSubmodule (twistedCircleAction ω.val (subgroupRegularAction ν H))).starProjection) ∧
      (∀ ω η, ω ≠ η → ∀ u v, ⟪Φ ω u, Φ η v⟫_ℂ = 0) := by
  let ρ := subgroupRegularAction ν H
  have hρ : Continuous (fun z : H × HaarL2 ν => ρ z.1 z.2) := by
    let inc : H × HaarL2 ν → G × HaarL2 ν := fun z => (z.1.val, z.2)
    have hi : Continuous inc := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    let A : G × HaarL2 ν → HaarL2 ν := fun z => leftRegularUnitary ν z.1 z.2
    have hA : Continuous A := leftRegularUnitary_continuous ν
    change Continuous (A ∘ inc)
    exact hA.comp hi
  have hall (ω : {ω : H →* Circle // Continuous ω}) :=
    (compactGroupIsotypicAverage ρ hρ ω.val ω.property μ).2
  choose Φ hΦ hRange hClosed hIdem hNorm hKer using hall
  refine ⟨Φ, fun ω f => ⟨hΦ ω f, regularAverage_ae ν H μ ω.val ω.property (Φ ω) (hΦ ω) f⟩,
    ?_, ?_⟩
  · intro ω
    let A := twistedCircleAction ω.val ρ
    let U := fixedSubmodule A
    have hU : CompleteSpace U := (hClosed ω).completeSpace_coe
    refine ⟨hU, ?_⟩
    let c : ℂ := μ.real univ
    have hc : c ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact (ENNReal.toReal_pos (isOpen_univ.measure_ne_zero μ univ_nonempty) (measure_ne_top μ _)).ne'
    apply ContinuousLinearMap.ext
    intro u
    change c⁻¹ • Φ ω u = U.starProjection u
    have hR : Φ ω u ∈ U := by
      change Φ ω u ∈ (U : Set (HaarL2 ν))
      exact (hRange ω).subset (mem_range_self u)
    symm
    apply U.eq_starProjection_of_mem_of_inner_eq_zero (U.smul_mem _ hR)
    intro v hv
    apply inner_eq_zero_symm.mp
    have hA (g : H) : ⟪v, A g u⟫_ℂ = ⟪v, u⟫_ℂ := by
      have hg : A g v = v := hv g
      have hh := twistedRegular_inner ν H ω.val g v u
      change ⟪A g v, A g u⟫_ℂ = ⟪v, u⟫_ℂ at hh
      rwa [hg] at hh
    have hP : ⟪v, Φ ω u⟫_ℂ = c * ⟪v, u⟫_ℂ := by
      change (innerSL ℂ v) (Φ ω u) = _
      rw [(hΦ ω u (innerSL ℂ v)).2]
      change (∫ g, ⟪v, A g u⟫_ℂ ∂μ) = _
      simp_rw [hA]
      rw [integral_const, Complex.real_smul]
    rw [inner_sub_right, inner_smul_right, hP, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, sub_self]
  · intro ω η hne u v
    obtain ⟨g, hg⟩ : ∃ g, ω.val g ≠ η.val g := by
      by_contra! h
      exact hne (Subtype.ext (MonoidHom.ext h))
    have hu := (mem_circleIsotype_iff ω.val ρ (Φ ω u)).1 ((hRange ω).subset (mem_range_self u)) g
    have hv := (mem_circleIsotype_iff η.val ρ (Φ η v)).1 ((hRange η).subset (mem_range_self v)) g
    have h := (leftRegularUnitary ν (g : G)).inner_map_map (Φ ω u) (Φ η v)
    change ⟪ρ g (Φ ω u), ρ g (Φ η v)⟫_ℂ = _ at h
    rw [hu, hv, inner_smul_left, inner_smul_right, ← mul_assoc, ← Circle.coe_inv_eq_conj] at h
    have h' : ((((ω.val g)⁻¹ : Circle) : ℂ) * (η.val g : ℂ) - 1) *
        ⟪Φ ω u, Φ η v⟫_ℂ = 0 := by rw [sub_mul, one_mul, h, sub_self]
    apply (mul_eq_zero.mp h').resolve_left
    intro hzero
    apply hg
    have hCircle : (ω.val g)⁻¹ * η.val g = 1 := Subtype.ext (sub_eq_zero.mp hzero)
    exact inv_mul_eq_one.mp hCircle

end

end Masullo
