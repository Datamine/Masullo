import ArchimedeanWeilAngular
import ComplexLogFourier
import RealWeilRadialCutoff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open Filter MeasureTheory Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

/-- Radial boundary of the disk centered at one with radius greater than one.
The parameter is the real part of the unit vector along the ray. -/
def complexWeilDiskBoundary (R x : ℝ) : ℝ :=
  x + Real.sqrt (x ^ 2 + (R ^ 2 - 1))

private theorem complexWeilDiskBoundary_sqrt_gt {R : ℝ} (hR : 1 < R) (x : ℝ) :
    |x| < Real.sqrt (x ^ 2 + (R ^ 2 - 1)) := by
  have hpos : 0 < R ^ 2 - 1 := by nlinarith
  refine (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp ?_
  rw [sq_abs, Real.sq_sqrt (by positivity)]
  linarith

theorem complexWeilDiskBoundary_pos {R : ℝ} (hR : 1 < R) (x : ℝ) :
    0 < complexWeilDiskBoundary R x := by
  unfold complexWeilDiskBoundary
  linarith [complexWeilDiskBoundary_sqrt_gt hR x, neg_abs_le x]

/-- Opposite rays in the shifted reference disk have reciprocal boundary
lengths up to the fixed factor given by the disk's power at the origin. -/
theorem complexWeilDiskBoundary_mul_opposite {R : ℝ} (hR : 1 < R) (x : ℝ) :
    complexWeilDiskBoundary R x * complexWeilDiskBoundary R (-x) = R ^ 2 - 1 := by
  have hpos : 0 ≤ x ^ 2 + (R ^ 2 - 1) := by nlinarith
  unfold complexWeilDiskBoundary
  rw [neg_sq]
  nlinarith [Real.sq_sqrt hpos]

theorem complexWeilDiskBoundary_log_opposite {R : ℝ} (hR : 1 < R) (x : ℝ) :
    Real.log (complexWeilDiskBoundary R x) + Real.log (complexWeilDiskBoundary R (-x)) =
      Real.log (R ^ 2 - 1) := by
  rw [← Real.log_mul (complexWeilDiskBoundary_pos hR x).ne'
    (complexWeilDiskBoundary_pos hR (-x)).ne', complexWeilDiskBoundary_mul_opposite hR]

/-- The shifted disk condition along a ray is exactly an upper bound on the radius. -/
theorem complexWeilDiskBoundary_le_iff {R r : ℝ} {u : ℂ}
    (hR : 1 < R) (hr : 0 ≤ r) (hu : ‖u‖ = 1) :
    ‖1 - (r : ℂ) * u‖ ≤ R ↔ r ≤ complexWeilDiskBoundary R u.re := by
  have hR₀ : 0 ≤ R := by linarith
  have hsq : ‖1 - (r : ℂ) * u‖ ^ 2 = 1 + r ^ 2 - 2 * r * u.re := by
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
      Complex.normSq_ofReal, ← Complex.sq_norm u, hu]
    simp only [one_pow, mul_one, one_mul, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, zero_mul, sub_zero]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) hR₀, hsq]
  let a := Real.sqrt (u.re ^ 2 + (R ^ 2 - 1))
  have ha₂ : a ^ 2 = u.re ^ 2 + (R ^ 2 - 1) := Real.sq_sqrt (by nlinarith)
  have hfac : (r - u.re + a) * (r - u.re - a) = 1 + r ^ 2 - 2 * r * u.re - R ^ 2 := by
    nlinarith [ha₂]
  have hp : 0 < r - u.re + a := by
    linarith [complexWeilDiskBoundary_sqrt_gt hR u.re, le_abs_self u.re]
  change 1 + r ^ 2 - 2 * r * u.re ≤ R ^ 2 ↔ r ≤ u.re + a
  rw [← sub_nonpos, ← hfac]
  constructor
  · intro h
    linarith [nonpos_of_mul_nonpos_right h hp]
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)

private theorem complexWeilDiskBoundary_bounds {R ρ : ℝ} (hR : 1 < R)
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R - 1) (θ : ℝ) :
    ρ ≤ complexWeilDiskBoundary R (Real.cos θ) ∧
      complexWeilDiskBoundary R (Real.cos θ) ≤ R + 1 := by
  let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := by simp [u, Complex.norm_exp, Complex.mul_re]
  have hRe : u.re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
  have hnorm (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) * u‖ = r := by
    simp [hu, Real.norm_of_nonneg hr]
  refine ⟨?_, ?_⟩
  · rw [← hRe, ← complexWeilDiskBoundary_le_iff hR hρ hu]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(ρ : ℂ) * u‖ := norm_sub_le _ _
      _ = 1 + ρ := by rw [hnorm ρ hρ, norm_one]
      _ ≤ _ := by linarith
  · let b := complexWeilDiskBoundary R (Real.cos θ)
    have hb : 0 ≤ b := (complexWeilDiskBoundary_pos hR _).le
    have hd : ‖1 - (b : ℂ) * u‖ ≤ R :=
      (complexWeilDiskBoundary_le_iff hR hb hu).2 (hRe ▸ le_rfl)
    change b ≤ R + 1
    calc
      b = ‖(b : ℂ) * u‖ := (hnorm b hb).symm
      _ = ‖1 - (1 - (b : ℂ) * u)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖(1 : ℂ)‖ + ‖1 - (b : ℂ) * u‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_one]; linarith

/-- The zero angular frequency of the kernel about the multiplicative origin. -/
theorem complexWeil_radialReference_average {r : ℝ} (hr : 0 < r) (hr₁ : r ≠ 1) :
    Real.circleAverage (fun u : ℂ => (((‖1 - u‖ ^ 2)⁻¹ : ℝ) : ℂ)) 0 r =
      if r < 1 then 1 / ((1 - r ^ 2 : ℝ) : ℂ) else 1 / ((r ^ 2 - 1 : ℝ) : ℂ) := by
  simpa only [zpow_zero, smul_eq_mul, Complex.real_smul, mul_one, Int.natAbs_zero, pow_zero] using
    complexWeil_angular_zpow hr hr₁ 0

/-- The angular integral of the logarithm of the shifted disk radius. -/
theorem complexWeilDiskBoundary_log_integral {R : ℝ} (hR : 1 < R) :
    (∫ θ in -Real.pi..Real.pi, Real.log (complexWeilDiskBoundary R (Real.cos θ))) =
      Real.pi * Real.log (R ^ 2 - 1) := by
  let f (θ : ℝ) := Real.log (complexWeilDiskBoundary R (Real.cos θ))
  have hf : Continuous f := by
    apply Continuous.log
    · unfold complexWeilDiskBoundary
      fun_prop
    · exact fun θ => (complexWeilDiskBoundary_pos hR _).ne'
  have hf' : Continuous (fun θ => f (θ + -Real.pi)) :=
    hf.comp (continuous_id.add continuous_const)
  change (∫ θ in -Real.pi..Real.pi, f θ) = _
  have hshift := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi) f (-Real.pi)
  rw [zero_add, add_neg_cancel] at hshift
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-Real.pi) 0)
    (hf.intervalIntegrable 0 Real.pi), ← hshift,
    ← intervalIntegral.integral_add (hf'.intervalIntegrable 0 Real.pi)
      (hf.intervalIntegrable 0 Real.pi)]
  calc
    _ = ∫ _ in (0 : ℝ)..Real.pi, Real.log (R ^ 2 - 1) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [f]
      rw [← sub_eq_add_neg, Real.cos_sub_pi, add_comm]
      exact complexWeilDiskBoundary_log_opposite hR (Real.cos θ)
    _ = _ := by simp [smul_eq_mul]

/-- The radial integrals of the reference disk with a squared-distance
hole, integrated over the full angular interval. -/
theorem complexWeilDiskBoundary_reference_integral {R ε : ℝ} (hR : 1 < R)
    (hε : 0 < ε) (hs : Real.sqrt ε ≤ R - 1) :
    (∫ θ in -Real.pi..Real.pi,
      ∫ ρ in Real.sqrt ε..complexWeilDiskBoundary R (Real.cos θ), ρ⁻¹) =
        Real.pi * (Real.log (R ^ 2 - 1) - Real.log ε) := by
  have hs₀ := Real.sqrt_pos.2 hε
  have hL (θ : ℝ) : Real.sqrt ε ≤ complexWeilDiskBoundary R (Real.cos θ) :=
    (complexWeilDiskBoundary_bounds hR hs₀.le hs θ).1
  have hf : Continuous (fun θ => Real.log (complexWeilDiskBoundary R (Real.cos θ))) := by
    apply Continuous.log
    · unfold complexWeilDiskBoundary
      fun_prop
    · exact fun θ => (complexWeilDiskBoundary_pos hR _).ne'
  simp_rw [show ∀ θ : ℝ, (∫ ρ in Real.sqrt ε..complexWeilDiskBoundary R (Real.cos θ), ρ⁻¹) =
      Real.log (complexWeilDiskBoundary R (Real.cos θ)) - Real.log (Real.sqrt ε) from fun θ => by
    rw [integral_inv_of_pos hs₀ (hs₀.trans_le (hL θ)),
      Real.log_div (complexWeilDiskBoundary_pos hR _).ne' hs₀.ne']]
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    complexWeilDiskBoundary_log_integral hR, intervalIntegral.integral_const,
    Real.log_sqrt hε.le, smul_eq_mul]
  ring

/-- In squared-radius coordinates the two nonsingular pieces of the reference
integral are elementary logarithms. -/
theorem complexWeil_radialReference_integral {R δ : ℝ} (hδ : 0 < δ)
    (hR : Real.exp δ ≤ R ^ 2) :
    (∫ s in (0 : ℝ)..Real.exp (-δ), (1 - s)⁻¹) +
      (∫ s in Real.exp δ..R ^ 2, (s - 1)⁻¹) =
        Real.log (R ^ 2 - 1) - 2 * Real.log (1 - Real.exp (-δ)) - δ := by
  have hneg : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hδ)
  have hpos : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  have hi (x : ℝ) (hx : x ∈ Set.uIcc 0 (Real.exp (-δ))) : 0 < 1 - x := by
    rw [Set.uIcc_of_le (Real.exp_pos _).le] at hx
    exact sub_pos.mpr (hx.2.trans_lt hneg)
  have ho (x : ℝ) (hx : x ∈ Set.uIcc (Real.exp δ) (R ^ 2)) : 0 < x - 1 := by
    rw [Set.uIcc_of_le hR] at hx
    exact sub_pos.mpr (hpos.trans_le hx.1)
  have hderiv (x : ℝ) : HasDerivAt (fun y => 1 - y) (-1 : ℝ) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    change HasDerivAt (fun y => 1 - y) (0 - 1) x at h
    simpa only [zero_sub] using h
  have hderiv' (x : ℝ) : HasDerivAt (fun y => y - 1) (1 : ℝ) x := by
    have h := (hasDerivAt_id x).sub (hasDerivAt_const x (1 : ℝ))
    change HasDerivAt (fun y => y - 1) (1 - 0) x at h
    simpa only [sub_zero] using h
  have hI : (∫ s in (0 : ℝ)..Real.exp (-δ), (1 - s)⁻¹) =
      -Real.log (1 - Real.exp (-δ)) := by
    calc
      _ = -Real.log (1 - Real.exp (-δ)) - -Real.log (1 - 0) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -Real.log (1 - x))
        · intro x hx
          have h := ((hderiv x).log (hi x hx).ne').neg
          change HasDerivAt (fun y => -Real.log (1 - y)) (-(-1 / (1 - x))) x at h
          simpa only [neg_div, neg_neg, one_div] using h
        · exact (continuous_const.sub continuous_id).continuousOn.inv₀
            (fun x hx => (hi x hx).ne') |>.intervalIntegrable
      _ = _ := by simp
  have hO : (∫ s in Real.exp δ..R ^ 2, (s - 1)⁻¹) =
      Real.log (R ^ 2 - 1) - Real.log (Real.exp δ - 1) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.log (x - 1))
    · intro x hx
      simpa only [one_div] using (hderiv' x).log (ho x hx).ne'
    · exact (continuous_id.sub continuous_const).continuousOn.inv₀
        (fun x hx => (ho x hx).ne') |>.intervalIntegrable
  have he : Real.exp δ - 1 = Real.exp δ * (1 - Real.exp (-δ)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hI, hO, he, Real.log_mul (Real.exp_ne_zero _) (sub_pos.mpr hneg).ne', Real.log_exp]
  ring

/-- The area integral for the additive cutoff of the shifted reference disk. -/
theorem complexWeil_additiveReference_integral {R ε : ℝ} (hR : 1 < R)
    (hε : 0 < ε) (hs : Real.sqrt ε ≤ R - 1) :
    (∫ z in {z : ℂ | ‖1 - z‖ ≤ R ∧ ε ≤ ‖z‖ ^ 2}, (‖z‖ ^ 2)⁻¹) =
      Real.pi * (Real.log (R ^ 2 - 1) - Real.log ε) := by
  let D := {z : ℂ | ‖1 - z‖ ≤ R ∧ ε ≤ ‖z‖ ^ 2}
  let B (θ : ℝ) := complexWeilDiskBoundary R (Real.cos θ)
  let α := Icc (Real.sqrt ε) (R + 1)
  let β := Ioo (-Real.pi) Real.pi
  let S := {p : ℝ × ℝ | p.1 ≤ B p.2}
  let g (p : ℝ × ℝ) := p.1⁻¹
  let k := S.indicator g
  have hs₀ := Real.sqrt_pos.2 hε
  have hD : MeasurableSet D :=
    (isClosed_le (continuous_const.sub continuous_id).norm continuous_const).measurableSet.inter
      (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet
  have hB : Continuous B := by unfold B complexWeilDiskBoundary; fun_prop
  have hS : MeasurableSet S := (isClosed_le continuous_fst (hB.comp continuous_snd)).measurableSet
  have hPolar := Complex.integral_comp_polarCoord_symm
    (D.indicator (fun z : ℂ => (‖z‖ ^ 2)⁻¹))
  change (∫ p in Complex.polarCoord.target, p.1 •
    D.indicator (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (Complex.polarCoord.symm p)) = _ at hPolar
  rw [integral_indicator hD] at hPolar
  change (∫ z in D, (‖z‖ ^ 2)⁻¹) = _
  rw [← hPolar, Complex.polarCoord_target]
  have hInt : IntegrableOn k (α ×ˢ β) (volume : Measure (ℝ × ℝ)) := by
    have hC : ContinuousOn g (α ×ˢ Icc (-Real.pi) Real.pi) :=
      continuous_fst.continuousOn.inv₀ fun p hp => (hs₀.trans_le hp.1.1).ne'
    have hg := (hC.integrableOn_compact (μ := volume) (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono (Subset.refl α) Ioo_subset_Icc_self)
    exact hg.indicator hS
  have hcong (p : ℝ × ℝ) (hp : p ∈ Ioi (0 : ℝ) ×ˢ β) :
      p.1 • D.indicator (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (Complex.polarCoord.symm p) =
        (α ×ˢ (univ : Set ℝ)).indicator k p := by
    let u : ℂ := Complex.exp ((p.2 : ℂ) * Complex.I)
    have hu : ‖u‖ = 1 := by simp [u, Complex.norm_exp, Complex.mul_re]
    have he : Complex.polarCoord.symm p = (p.1 : ℂ) * u := by
      simp only [Complex.polarCoord_symm_apply, u, Complex.exp_ofReal_mul_I]
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 :=
      (Complex.norm_polarCoord_symm p).trans (abs_of_pos hp.1)
    have hR' := (complexWeilDiskBoundary_bounds hR hs₀.le hs p.2).2
    have hεiff : ε ≤ p.1 ^ 2 ↔ Real.sqrt ε ≤ p.1 := by
      conv_lhs => rw [← Real.sq_sqrt hε.le]
      exact sq_le_sq₀ hs₀.le hp.1.le
    have hEq : Complex.polarCoord.symm p ∈ D ↔ p ∈ α ×ˢ (univ : Set ℝ) ∧ p ∈ S := by
      change ‖1 - Complex.polarCoord.symm p‖ ≤ R ∧ ε ≤ ‖Complex.polarCoord.symm p‖ ^ 2 ↔
        ((Real.sqrt ε ≤ p.1 ∧ p.1 ≤ R + 1) ∧ p.2 ∈ (univ : Set ℝ)) ∧ p.1 ≤ B p.2
      rw [hn, he, complexWeilDiskBoundary_le_iff hR hp.1.le hu,
        Complex.exp_ofReal_mul_I_re, hεiff]
      simp only [B, mem_univ, and_true]
      exact ⟨fun h => ⟨⟨h.2, h.1.trans hR'⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
    rw [show (α ×ˢ (univ : Set ℝ)).indicator k =
        ((α ×ˢ (univ : Set ℝ)) ∩ S).indicator g by
      change (α ×ˢ (univ : Set ℝ)).indicator (S.indicator g) = _
      rw [indicator_indicator]]
    by_cases h : Complex.polarCoord.symm p ∈ D
    · have hm : p ∈ (α ×ˢ (univ : Set ℝ)) ∩ S := hEq.mp h
      rw [indicator_of_mem h, indicator_of_mem hm, hn, smul_eq_mul]
      change p.1 * (p.1 ^ 2)⁻¹ = p.1⁻¹
      field_simp [(show 0 < p.1 from hp.1).ne']
    · have hm : p ∉ (α ×ˢ (univ : Set ℝ)) ∩ S := hEq.not.mp h
      rw [indicator_of_notMem h, indicator_of_notMem hm, smul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcong,
    setIntegral_indicator (measurableSet_Icc.prod MeasurableSet.univ)]
  rw [show (Ioi (0 : ℝ) ×ˢ β) ∩ (α ×ˢ (univ : Set ℝ)) = α ×ˢ β by
    rw [inter_comm]
    have hsub : α ⊆ Ioi (0 : ℝ) := fun r hr => hs₀.trans_le hr.1
    rw [prod_inter_prod, univ_inter, inter_eq_left.mpr hsub]]
  rw [Measure.volume_eq_prod] at hInt ⊢
  simp only [← Measure.prod_restrict, IntegrableOn] at hInt ⊢
  rw [integral_prod_symm k hInt]
  change (∫ θ in β, ∫ r in α, k (r, θ)) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← complexWeilDiskBoundary_reference_integral hR hε hs]
  apply intervalIntegral.integral_congr
  intro θ _
  obtain ⟨hlo, hhi⟩ := complexWeilDiskBoundary_bounds hR hs₀.le hs θ
  change (∫ r in α, (Iic (B θ)).indicator Inv.inv r) = _
  rw [setIntegral_indicator measurableSet_Iic,
    show α ∩ Iic (B θ) = Icc (Real.sqrt ε) (B θ) by
      ext r
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hhi⟩, h.2⟩⟩,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlo]

/-- Polar integration on a bounded radial shell, with the angle normalized
to a circle average and the radial Jacobian retained. -/
theorem complexWeil_integral_shell {f : ℂ → ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hf : ContinuousOn f {z : ℂ | ‖z‖ ∈ Icc a b}) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Ioc a b}, f z) =
      (2 * Real.pi) • ∫ r in Ioc a b, r • Real.circleAverage f 0 r := by
  let α := Ioc a b
  let β := Ioo (-Real.pi) Real.pi
  let D := {z : ℂ | ‖z‖ ∈ α}
  let g (p : ℝ × ℝ) := p.1 • f (circleMap 0 p.1 p.2)
  have hD : MeasurableSet D := measurableSet_Ioc.preimage continuous_norm.measurable
  have hPolar := Complex.integral_comp_polarCoord_symm (D.indicator f)
  change (∫ p in Complex.polarCoord.target, p.1 • D.indicator f (Complex.polarCoord.symm p)) =
    (∫ z, D.indicator f z) at hPolar
  rw [integral_indicator hD, Complex.polarCoord_target] at hPolar
  change (∫ z in D, f z) = _
  rw [← hPolar]
  have hc (p : ℝ × ℝ) (hp : p ∈ Ioi (0 : ℝ) ×ˢ β) :
      p.1 • D.indicator f (Complex.polarCoord.symm p) =
        (α ×ˢ (univ : Set ℝ)).indicator g p := by
    have hEq : Complex.polarCoord.symm p ∈ D ↔ p.1 ∈ α := by
      change ‖Complex.polarCoord.symm p‖ ∈ α ↔ _
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    by_cases hm : p.1 ∈ α
    · rw [indicator_of_mem (hEq.mpr hm),
        indicator_of_mem (show p ∈ α ×ˢ (univ : Set ℝ) from ⟨hm, trivial⟩)]
      have he : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
        rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I]
        simp
      rw [he]
    · rw [indicator_of_notMem (hEq.not.mpr hm),
        indicator_of_notMem (show p ∉ α ×ˢ (univ : Set ℝ) from fun h => hm h.1), smul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hc,
    setIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  rw [show (Ioi (0 : ℝ) ×ˢ β) ∩ (α ×ˢ (univ : Set ℝ)) = α ×ˢ β by
    have hsub : α ⊆ Ioi 0 := fun _ hr => ha.trans_lt hr.1
    rw [prod_inter_prod, inter_eq_right.mpr hsub, inter_univ]]
  have hInt : IntegrableOn g (α ×ˢ β) (volume : Measure (ℝ × ℝ)) := by
    have hparam : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
      unfold circleMap
      fun_prop
    have hg : ContinuousOn g (Icc a b ×ˢ Icc (-Real.pi) Real.pi) := by
      apply continuous_fst.continuousOn.smul
      refine hf.comp hparam.continuousOn fun p hp => ?_
      change ‖circleMap 0 p.1 p.2‖ ∈ Icc a b
      rw [norm_circleMap_zero, abs_of_nonneg (ha.trans hp.1.1)]
      exact hp.1
    exact (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
  rw [Measure.volume_eq_prod] at hInt ⊢
  rw [setIntegral_prod g hInt, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  have hArc :
      (∫ θ in β, f (circleMap 0 r θ)) = (2 * Real.pi) • Real.circleAverage f 0 r := by
    have he := Real.circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-Real.pi)
    rw [intervalIntegral.integral_comp_add_right (fun θ : ℝ => f (circleMap 0 r θ)),
      zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at he
    rw [he, smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  change (∫ θ in β, r • f (circleMap 0 r θ)) = _
  rw [integral_smul, hArc, smul_comm r]

private theorem complexWeil_integral_shell_reference {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hs : b < 1 ∨ 1 < a) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Ioc a b}, (‖1 - z‖ ^ 2)⁻¹) =
      Real.pi * ∫ s in a ^ 2..b ^ 2,
        (if b < 1 then 1 - s else s - 1)⁻¹ := by
  let j (z : ℂ) := (‖1 - z‖ ^ 2)⁻¹
  let g (s : ℝ) := (if b < 1 then 1 - s else s - 1)⁻¹
  have hneq (r : ℝ) (hr : r ∈ Icc a b) : r ≠ 1 := by
    rcases hs with h | h
    · exact (hr.2.trans_lt h).ne
    · exact (h.trans_le hr.1).ne'
  have hj : ContinuousOn j {z : ℂ | ‖z‖ ∈ Icc a b} := by
    apply ((continuous_const.sub continuous_id).norm.pow 2).continuousOn.inv₀
    intro z hz
    refine pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ?_))
    intro he
    change (1 : ℂ) = z at he
    apply hneq ‖z‖ hz
    rw [← he, norm_one]
  have hc := complexWeil_integral_shell (f := fun z => (j z : ℂ)) ha
    (Complex.continuous_ofReal.comp_continuousOn hj)
  rw [integral_complex_ofReal] at hc
  have hAve (r : ℝ) (hr : r ∈ Ioc a b) :
      Real.circleAverage (fun z => (j z : ℂ)) 0 r = (g (r ^ 2) : ℂ) := by
    rw [complexWeil_radialReference_average (ha.trans_lt hr.1) (hneq r (Ioc_subset_Icc_self hr))]
    rcases hs with h | h
    · simp [g, h, hr.2.trans_lt h, one_div]
    · have hr' : ¬r < 1 := (h.trans hr.1).not_gt
      have hb' : ¬b < 1 := (h.trans_le hab).not_gt
      simp [g, hr', hb', one_div]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => congrArg (r • ·) (hAve r hr))] at hc
  simp only [Complex.real_smul, ← Complex.ofReal_mul, integral_complex_ofReal] at hc
  have hc' : (∫ z in {z : ℂ | ‖z‖ ∈ Ioc a b}, j z) =
      (2 * Real.pi) * ∫ r in Ioc a b, r * g (r ^ 2) := by
    exact_mod_cast hc
  have hsq : ContinuousOn g ((fun r : ℝ => r ^ 2) '' uIcc a b) := by
    rcases hs with h | h
    · simp only [g, ite_eq_left h]
      apply (continuous_const.sub continuous_id).continuousOn.inv₀
      rintro _ ⟨r, hr, rfl⟩
      rw [uIcc_of_le hab] at hr
      have hr' := hr.2.trans_lt h
      have hp := ha.trans hr.1
      exact (show 0 < 1 - r ^ 2 by nlinarith).ne'
    · have hb' : ¬b < 1 := (h.trans_le hab).not_gt
      simp only [g, ite_eq_right hb']
      apply (continuous_id.sub continuous_const).continuousOn.inv₀
      rintro _ ⟨r, hr, rfl⟩
      rw [uIcc_of_le hab] at hr
      have hr' := h.trans_le hr.1
      exact (show 0 < r ^ 2 - 1 by nlinarith).ne'
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (f := fun r : ℝ => r ^ 2) (f' := fun r => 2 * r) (g := g)
    (fun r _ => by simpa using hasDerivAt_pow 2 r)
    (by fun_prop) hsq
  have hsimp (r : ℝ) : g (r ^ 2) * (2 * r) = 2 * (r * g (r ^ 2)) := by ring
  simp only [Function.comp_apply, hsimp, intervalIntegral.integral_const_mul] at hsubst
  rw [hc', ← intervalIntegral.integral_of_le hab]
  change 2 * Real.pi * _ = Real.pi * ∫ s in a ^ 2..b ^ 2, g s
  rw [← hsubst]
  ring

/-- The exact area integral of the multiplicative annuli in the reference disk. -/
theorem complexWeil_radialReference_area {R δ : ℝ} (hR : 1 < R) (hδ : 0 < δ)
    (hδR : Real.exp (δ / 2) ≤ R) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Ioc 0 (Real.exp (-δ / 2))}, (‖1 - z‖ ^ 2)⁻¹) +
      (∫ z in {z : ℂ | ‖z‖ ∈ Ioc (Real.exp (δ / 2)) R}, (‖1 - z‖ ^ 2)⁻¹) =
      Real.pi * (Real.log (R ^ 2 - 1) - 2 * Real.log (1 - Real.exp (-δ)) - δ) := by
  have hi : Real.exp (-δ / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ho : 1 < Real.exp (δ / 2) := Real.one_lt_exp_iff.mpr (half_pos hδ)
  rw [complexWeil_integral_shell_reference le_rfl (Real.exp_pos _).le (Or.inl hi),
    complexWeil_integral_shell_reference (Real.exp_pos _).le hδR (Or.inr ho)]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), ite_eq_left hi, ite_eq_right hR.not_gt]
  have hSq (x : ℝ) : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hSq, hSq, ← mul_add, complexWeil_radialReference_integral hδ]
  exact (hSq δ).symm ▸ (sq_le_sq₀ (Real.exp_pos _).le (by linarith : 0 ≤ R)).2 hδR

/-- Reciprocal annular cutoff in the shifted additive complex coordinate. -/
def complexWeilRadialDomain (δ : ℝ) : Set ℂ :=
  {z | 0 < ‖1 - z‖ ∧ (‖1 - z‖ ≤ Real.exp (-δ / 2) ∨ Real.exp (δ / 2) < ‖1 - z‖)}

private theorem complexWeilRadialDomain_measurable (δ : ℝ) :
    MeasurableSet (complexWeilRadialDomain δ) := by
  let n (z : ℂ) := ‖1 - z‖
  have hn : Continuous n := (continuous_const.sub continuous_id).norm
  exact (isOpen_lt continuous_const hn).measurableSet.inter
    ((isClosed_le hn continuous_const).measurableSet.union
      (isOpen_lt continuous_const hn).measurableSet)

private theorem complexWeil_integrable_cutoff_tendsto {D : ℝ → Set ℂ}
    (hm : ∀ δ, MeasurableSet (D δ))
    (hD : ∀ᵐ z : ℂ ∂volume, ∀ᶠ δ : ℝ in 𝓝[>] 0, z ∈ D δ)
    {g : ℂ → ℂ} (hg : Integrable g) :
    Tendsto (fun δ : ℝ => ∫ z in D δ, g z) (𝓝[>] 0) (𝓝 (∫ z, g z)) := by
  simp_rw [← integral_indicator (hm _)]
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖g z‖)
    (.of_forall fun δ => hg.aestronglyMeasurable.indicator (hm δ))
    (.of_forall fun δ => .of_forall fun z => ?_) hg.norm ?_
  · by_cases hz : z ∈ D δ
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  · filter_upwards [hD] with z hz
    apply tendsto_const_nhds.congr'
    exact hz.mono fun δ hδ => (indicator_of_mem hδ g).symm

theorem complexWeil_integrable_radialCutoff_tendsto {g : ℂ → ℂ} (hg : Integrable g) :
    Tendsto (fun δ : ℝ => ∫ z in complexWeilRadialDomain δ, g z)
      (𝓝[>] 0) (𝓝 (∫ z, g z)) := by
  apply complexWeil_integrable_cutoff_tendsto complexWeilRadialDomain_measurable _ hg
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (1 : ℂ)
  have hunit : ∀ᵐ z : ℂ ∂volume, ‖1 - z‖ ≠ 1 := by
    rw [ae_iff]
    have ht : {z : ℂ | ¬ ‖1 - z‖ ≠ 1} = Metric.sphere (1 : ℂ) 1 := by
      ext z
      simp [norm_sub_rev]
    rw [ht]
    exact Measure.addHaar_sphere volume (1 : ℂ) 1
  have hlim (s : ℝ) : Tendsto (fun δ : ℝ => Real.exp (s * δ)) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun δ : ℝ => Real.exp (s * δ)) 0 := by fun_prop
    simpa only [mul_zero, Real.exp_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hne, hunit] with z hz hz'
  have hp : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm)
  rcases lt_or_gt_of_ne hz' with h | h
  · have he := (hlim (-(1 / 2))).eventually (eventually_gt_nhds h)
    exact he.mono fun δ hδ => ⟨hp, Or.inl (by
      rw [show -δ / 2 = -(1 / 2) * δ by ring]
      exact hδ.le)⟩
  · have he := (hlim (1 / 2)).eventually (eventually_lt_nhds h)
    exact he.mono fun δ hδ => ⟨hp, Or.inr (by
      rwa [show δ / 2 = (1 / 2) * δ by ring])⟩

private def complexWeilDisk (R : ℝ) := {z : ℂ | ‖1 - z‖ ≤ R}

private theorem complexWeilDisk_eq_closedBall (R : ℝ) :
    complexWeilDisk R = Metric.closedBall (1 : ℂ) R := by
  ext z
  simp [complexWeilDisk, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]

private theorem complexWeil_shiftedDiskRemainder_integrable (h : 𝓢(ℂ, ℂ))
    {R : ℝ} (hR : 1 < R) :
    Integrable (fun z : ℂ => (‖z‖ ^ 2)⁻¹ •
      (h z - (complexWeilDisk R).indicator (fun _ => h 0) z)) := by
  let S := Metric.closedBall (0 : ℂ) 1
  let B := complexWeilDisk R
  let q (z : ℂ) := (‖z‖ ^ 2)⁻¹ • h 0
  let r := min 1 (R - 1)
  let K := {z : ℂ | r ≤ ‖z‖} ∩ (S ∪ B)
  have hr : 0 < r := lt_min zero_lt_one (sub_pos.mpr hR)
  have hB : IsCompact B := by
    unfold B
    rw [complexWeilDisk_eq_closedBall]
    exact isCompact_closedBall _ _
  have hS : IsCompact S := isCompact_closedBall _ _
  have hK : IsCompact K := (hS.union hB).inter_left (isClosed_le continuous_const continuous_norm)
  have hi : IntegrableOn q K := by
    apply ContinuousOn.integrableOn_compact hK
    apply (continuous_norm.pow 2).continuousOn.inv₀ (fun z hz =>
      pow_ne_zero _ (hr.trans_le hz.1).ne')
      |>.smul continuousOn_const
  have hsub (z : ℂ) (hz : ‖z‖ < r) : z ∈ S ∧ z ∈ B := by
    have hs : ‖z‖ ≤ 1 := hz.le.trans (min_le_left _ _)
    have hb : ‖z‖ ≤ R - 1 := hz.le.trans (min_le_right _ _)
    refine ⟨by simpa [S, Metric.mem_closedBall, dist_zero_right] using hs, ?_⟩
    change ‖1 - z‖ ≤ R
    have ht := norm_sub_le (1 : ℂ) z
    rw [norm_one] at ht
    linarith
  have hdiff₁ : S \ B ⊆ K := fun z hz =>
    ⟨le_of_not_gt fun h => hz.2 (hsub z h).2, Or.inl hz.1⟩
  have hdiff₂ : B \ S ⊆ K := fun z hz =>
    ⟨le_of_not_gt fun h => hz.2 (hsub z h).1, Or.inr hz.1⟩
  have hq₁ := (integrable_indicator_iff (hS.measurableSet.diff hB.measurableSet)).2
    (hi.mono_set hdiff₁)
  have hq₂ := (integrable_indicator_iff (hB.measurableSet.diff hS.measurableSet)).2
    (hi.mono_set hdiff₂)
  refine ((complexLogCutoffRemainder_integrable h).add (hq₁.sub hq₂)).congr
    (.of_forall fun z => ?_)
  have hS' : {z : ℂ | ‖z‖ ≤ 1} = S := by ext z; simp [S, Metric.mem_closedBall, dist_zero_right]
  change complexLogCutoffRemainder h z + ((S \ B).indicator q z - (B \ S).indicator q z) =
    (‖z‖ ^ 2)⁻¹ • (h z - B.indicator (fun _ => h 0) z)
  unfold complexLogCutoffRemainder
  rw [hS']
  by_cases hz₁ : z ∈ S <;> by_cases hz₂ : z ∈ B <;>
    simp [hz₁, hz₂, q, indicator_of_mem, indicator_of_notMem, sub_eq_add_neg]

private def complexWeilShiftedRemainder (h : 𝓢(ℂ, ℂ)) (R : ℝ) (z : ℂ) :=
  (‖z‖ ^ 2)⁻¹ • (h z - (complexWeilDisk R).indicator (fun _ => h 0) z)

private theorem complexWeil_cutoff_decompose (h : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 1 < R)
    {L : Set ℂ}
    (hi : IntegrableOn (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (L ∩ complexWeilDisk R)) :
    (∫ z in L, (‖z‖ ^ 2)⁻¹ • h z) =
      (∫ z in L, complexWeilShiftedRemainder h R z) +
        (∫ z in L ∩ complexWeilDisk R, (‖z‖ ^ 2)⁻¹) • h 0 := by
  let q (z : ℂ) := (‖z‖ ^ 2)⁻¹ • h 0
  let B := complexWeilDisk R
  have hB : MeasurableSet B := (isClosed_le (continuous_const.sub continuous_id).norm
    continuous_const).measurableSet
  have hq : IntegrableOn (B.indicator q) L := by
    change Integrable (B.indicator q) (volume.restrict L)
    rw [integrable_indicator_iff hB]
    change Integrable q ((volume.restrict L).restrict B)
    rw [Measure.restrict_restrict hB, inter_comm]
    exact hi.smul_const (h 0)
  have he (z : ℂ) : (‖z‖ ^ 2)⁻¹ • h z =
      complexWeilShiftedRemainder h R z + B.indicator q z := by
    by_cases hz : z ∈ B <;>
      simp [complexWeilShiftedRemainder, q, show complexWeilDisk R = B from rfl,
        hz, indicator_of_mem, indicator_of_notMem, smul_sub]
  simp_rw [he]
  have hrem : IntegrableOn (complexWeilShiftedRemainder h R) L :=
    (complexWeil_shiftedDiskRemainder_integrable h hR).integrableOn
  rw [integral_add hrem hq, setIntegral_indicator hB]
  change _ + (∫ z in L ∩ B, (‖z‖ ^ 2)⁻¹ • h 0) = _
  rw [integral_smul_const]

private theorem complexWeil_radialReference_shifted {R δ : ℝ} (hR : 1 < R)
    (hδ : 0 < δ) (hδR : Real.exp (δ / 2) ≤ R) :
    IntegrableOn (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (complexWeilRadialDomain δ ∩ complexWeilDisk R) ∧
      (∫ z in complexWeilRadialDomain δ ∩ complexWeilDisk R, (‖z‖ ^ 2)⁻¹) =
        Real.pi * (Real.log (R ^ 2 - 1) - 2 * Real.log (1 - Real.exp (-δ)) - δ) := by
  let I := Real.exp (-δ / 2)
  let O := Real.exp (δ / 2)
  let A := {x : ℂ | ‖x‖ ∈ Ioc 0 I}
  let B := {x : ℂ | ‖x‖ ∈ Ioc O R}
  let K := {x : ℂ | ‖x‖ ≤ I ∨ O ≤ ‖x‖} ∩ Metric.closedBall (0 : ℂ) R
  let u := MeasurableEquiv.subLeft (1 : ℂ)
  have hi : I < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ho : 1 < O := Real.one_lt_exp_iff.mpr (half_pos hδ)
  have hm : MeasurableSet B := measurableSet_Ioc.preimage continuous_norm.measurable
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left
    ((isClosed_le continuous_norm continuous_const).union (isClosed_le continuous_const continuous_norm))
  have hcont : ContinuousOn (fun x : ℂ => (‖1 - x‖ ^ 2)⁻¹) K := by
    apply ((continuous_const.sub continuous_id).norm.pow 2).continuousOn.inv₀
    intro x hx
    have hx₁ : (1 : ℂ) ≠ x := by
      rintro rfl
      have hw : ‖(1 : ℂ)‖ ≤ I ∨ O ≤ ‖(1 : ℂ)‖ := hx.1
      simp [hi.not_ge, ho.not_ge] at hw
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx₁))
  have hAK : A ⊆ K := fun x hx => ⟨Or.inl hx.2, by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx.2.trans (hi.le.trans hR.le)⟩
  have hBK : B ⊆ K := fun x hx => ⟨Or.inr hx.1.le, by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx.2⟩
  have hd : Disjoint A B := by
    rw [disjoint_left]
    intro x hx hx'
    exact (ho.trans hx'.1).not_ge (hx.2.trans hi.le)
  have himage : u '' (A ∪ B) = complexWeilRadialDomain δ ∩ complexWeilDisk R := by
    ext z
    have hu (x : ℂ) : u x = 1 - x := rfl
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hu]
      change (0 < ‖1 - (1 - x)‖ ∧ (‖1 - (1 - x)‖ ≤ I ∨ O < ‖1 - (1 - x)‖)) ∧
        ‖1 - (1 - x)‖ ≤ R
      rw [sub_sub_cancel]
      rcases hx with h | h
      · exact ⟨⟨h.1, Or.inl h.2⟩, h.2.trans (hi.le.trans hR.le)⟩
      · exact ⟨⟨(zero_lt_one.trans ho).trans h.1, Or.inr h.1⟩, h.2⟩
    · intro hz
      refine ⟨1 - z, ?_, by rw [hu, sub_sub_cancel]⟩
      rcases hz.1.2 with h | h
      · exact Or.inl ⟨hz.1.1, h⟩
      · exact Or.inr ⟨h, hz.2⟩
  have h₁ := Measure.measurePreserving_sub_left volume (1 : ℂ)
  have hA := (hcont.integrableOn_compact hK (μ := volume)).mono_set hAK
  have hB := (hcont.integrableOn_compact hK (μ := volume)).mono_set hBK
  rw [← himage]
  refine ⟨((h₁.restrict_image_emb u.measurableEmbedding (A ∪ B)).integrable_comp_emb
    u.measurableEmbedding).1 (hA.union hB), ?_⟩
  change (∫ z in (fun x : ℂ => 1 - x) '' (A ∪ B), (‖z‖ ^ 2)⁻¹) = _
  rw [h₁.setIntegral_image_emb u.measurableEmbedding, setIntegral_union hd hm hA hB]
  exact complexWeil_radialReference_area hR hδ hδR

private theorem complexWeil_shiftedRemainder_total (h : 𝓢(ℂ, ℂ)) :
    (∫ z, complexWeilShiftedRemainder h 2 z) + (Real.pi * Real.log (2 ^ 2 - 1)) • h 0 =
      ∫ z, complexLogCutoffRemainder h z := by
  let D (ε : ℝ) := {z : ℂ | ε ≤ ‖z‖ ^ 2}
  have hm (ε : ℝ) : MeasurableSet (D ε) :=
    (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet
  have hD : ∀ᵐ z : ℂ ∂volume, ∀ᶠ ε : ℝ in 𝓝[>] 0, z ∈ D ε := by
    have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using measure_singleton (0 : ℂ)
    filter_upwards [hne] with z hz
    have ht : ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖z‖ ^ 2 :=
      Iio_mem_nhds (sq_pos_of_pos (norm_pos_iff.mpr hz))
    exact (ht.filter_mono nhdsWithin_le_nhds).mono fun _ hε => hε.le
  have hlim := complexWeil_integrable_cutoff_tendsto hm hD
    (g := complexWeilShiftedRemainder h 2) (complexWeil_shiftedDiskRemainder_integrable h (by norm_num))
  have ha : Tendsto (fun ε : ℝ => (2 : ℝ)⁻¹ • complexLogCutoff h ε) (𝓝[>] 0)
      (𝓝 (∫ z, complexLogCutoffRemainder h z)) := by
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] using
      (complexLogCutoff_tendsto h).const_smul ((2 : ℝ)⁻¹)
  apply tendsto_nhds_unique _ ha
  refine (hlim.add_const ((Real.pi * Real.log (2 ^ 2 - 1)) • h 0)).congr' ?_
  have hs' : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 := Iio_mem_nhds (by norm_num)
  have hs := hs'.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  filter_upwards [self_mem_nhdsWithin, hs] with ε hε hε'
  have hp : 0 < ε := hε
  have hsqrt : Real.sqrt ε ≤ 2 - 1 := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hε'.le
  have hi : IntegrableOn (fun z : ℂ => (‖z‖ ^ 2)⁻¹) (D ε ∩ complexWeilDisk 2) := by
    have hK : IsCompact (D ε ∩ complexWeilDisk 2) := by
      rw [complexWeilDisk_eq_closedBall]
      exact (isCompact_closedBall _ _).inter_left
        (isClosed_le continuous_const (continuous_norm.pow 2))
    apply ContinuousOn.integrableOn_compact hK
    exact (continuous_norm.pow 2).continuousOn.inv₀ fun z hz =>
      (hp.trans_le hz.1).ne'
  have hval : (∫ z in D ε ∩ complexWeilDisk 2, (‖z‖ ^ 2)⁻¹) =
      Real.pi * (Real.log (2 ^ 2 - 1) - Real.log ε) := by
    rw [show D ε ∩ complexWeilDisk 2 = {z : ℂ | ‖1 - z‖ ≤ 2 ∧ ε ≤ ‖z‖ ^ 2} by
      ext z
      exact and_comm]
    exact complexWeil_additiveReference_integral (by norm_num) hp hsqrt
  change _ + _ = (2 : ℝ)⁻¹ • complexLogCutoff h ε
  rw [complexLogCutoff, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul,
    complexWeil_cutoff_decompose h (by norm_num) hi, hval, mul_sub, sub_smul]
  abel

/-- The normalized annular finite part has the same limit as the
squared-distance finite part on the complex plane. -/
theorem complexWeil_radialAreaCutoff_tendsto (h : 𝓢(ℂ, ℂ)) :
    Tendsto (fun δ : ℝ => Real.pi⁻¹ • (∫ z in complexWeilRadialDomain δ, (‖z‖ ^ 2)⁻¹ • h z) +
      (2 * Real.log δ : ℝ) • h 0) (𝓝[>] 0)
      (𝓝 (Real.pi⁻¹ • ∫ z, complexLogCutoffRemainder h z)) := by
  have hlim := complexWeil_integrable_radialCutoff_tendsto
    (g := complexWeilShiftedRemainder h 2) (complexWeil_shiftedDiskRemainder_integrable h (by norm_num))
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, Real.exp (δ / 2) < 2 := by
    have hc : ContinuousAt (fun δ : ℝ => Real.exp (δ / 2)) 0 := by fun_prop
    have ht : Tendsto (fun δ : ℝ => Real.exp (δ / 2)) (𝓝[>] 0) (𝓝 1) := by
      simpa only [zero_div, Real.exp_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (Iio_mem_nhds (by norm_num))
  have hlog := idelicWeil_radialCounterterm_logLimit.const_mul (-2)
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have herr := (hlog.sub hδ).smul_const (h 0)
  simp only [mul_zero, sub_zero, zero_smul] at herr
  have hsum := ((hlim.add_const ((Real.pi * Real.log (2 ^ 2 - 1)) • h 0)).const_smul Real.pi⁻¹).add herr
  rw [add_zero, complexWeil_shiftedRemainder_total h] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδR
  obtain ⟨hi, he⟩ := complexWeil_radialReference_shifted (by norm_num) hδ hδR.le
  rw [complexWeil_cutoff_decompose h (by norm_num) hi, he]
  simp only [smul_add, smul_smul, inv_mul_cancel_left₀ Real.pi_ne_zero]
  module

/-- The circle average in the shifted complex coordinate, including the
Jacobian of squared logarithmic radius. -/
def complexWeilShiftedRadial (h : ℂ → ℂ) (r : ℝ) : ℂ :=
  (r ^ 2 : ℝ) • Real.circleAverage (fun x : ℂ => (‖1 - x‖ ^ 2)⁻¹ • h (1 - x)) 0 r

private theorem complexWeil_exp_half_images (δ : ℝ) :
    (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) '' Ici δ = Ioc 0 (Real.exp (-δ / 2)) ∧
      (fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t)) '' Ici δ = Ici (Real.exp (δ / 2)) := by
  refine ⟨?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
      change δ ≤ t at ht
      linarith
    · rintro ⟨hr, hr'⟩
      refine ⟨-2 * Real.log r, ?_, ?_⟩
      · change δ ≤ -2 * Real.log r
        have hb := Real.log_le_log hr hr'
        rw [Real.log_exp] at hb
        linarith
      · change Real.exp (-(1 / 2 : ℝ) * (-2 * Real.log r)) = r
        rw [show -(1 / 2 : ℝ) * (-2 * Real.log r) = Real.log r by ring, Real.exp_log hr]
  · ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      apply Real.exp_le_exp.mpr
      change δ ≤ t at ht
      linarith
    · intro hr
      have hp := (Real.exp_pos (δ / 2)).trans_le hr
      refine ⟨2 * Real.log r, ?_, ?_⟩
      · change δ ≤ 2 * Real.log r
        have hb := Real.log_le_log (Real.exp_pos _) hr
        rw [Real.log_exp] at hb
        linarith
      · change Real.exp ((1 / 2 : ℝ) * (2 * Real.log r)) = r
        rw [show (1 / 2 : ℝ) * (2 * Real.log r) = Real.log r by ring, Real.exp_log hp]

/-- The shifted additive annuli give the weighted circle averages at reciprocal
log radii, with the complex normalization by plane measure. -/
theorem complexWeil_radialAreaCutoff_eq_log (h : ℂ → ℂ) (hh : Continuous h)
    (hc : HasCompactSupport h) {δ : ℝ} (hδ : 0 < δ) :
    Real.pi⁻¹ • (∫ z in complexWeilRadialDomain δ, (‖z‖ ^ 2)⁻¹ • h z) =
      ∫ t in Ioi δ, complexWeilShiftedRadial h (Real.exp (t / 2)) +
        complexWeilShiftedRadial h (Real.exp (-t / 2)) := by
  let I := Real.exp (-δ / 2)
  let O := Real.exp (δ / 2)
  let f (x : ℂ) := (‖1 - x‖ ^ 2)⁻¹ • h (1 - x)
  let G (r : ℝ) := r • Real.circleAverage f 0 r
  let u := MeasurableEquiv.subLeft (1 : ℂ)
  have hi : I < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ho : 1 < O := Real.one_lt_exp_iff.mpr (half_pos hδ)
  have hcs : HasCompactSupport (fun x : ℂ => h (1 - x)) :=
    hc.comp_homeomorph (oneSubHomeomorph ℂ)
  obtain ⟨M, hM⟩ := hcs.isCompact.isBounded.exists_norm_le
  let R := max (O + 1) M
  have hOR : O ≤ R := (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)
  let A := {x : ℂ | ‖x‖ ∈ Ioc 0 I}
  let B := {x : ℂ | ‖x‖ ∈ Ioc O R}
  let B' := {x : ℂ | ‖x‖ ∈ Ioi O}
  have hfz (x : ℂ) (hx : R < ‖x‖) : f x = 0 := by
    have hn : h (1 - x) = 0 := by
      by_contra! hn
      exact ((hM x (subset_tsupport _ hn)).trans (le_max_right _ _)).not_gt hx
    simp [f, hn]
  have hGz (r : ℝ) (hr : R < r) : G r = 0 := by
    have hr₀ : 0 ≤ r := ((Real.exp_pos _).le.trans hOR).trans hr.le
    have he : Real.circleAverage f 0 r = Real.circleAverage (fun _ : ℂ => (0 : ℂ)) 0 r := by
      apply Real.circleAverage_congr_sphere
      intro x hx
      have hx' : ‖x‖ = r := by simpa [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hr₀] using hx
      exact hfz x (hx'.symm ▸ hr)
    rw [Real.circleAverage_const] at he
    simp [G, he]
  have hfc {a b : ℝ} (hs : b < 1 ∨ 1 < a) :
      ContinuousOn f {x : ℂ | ‖x‖ ∈ Icc a b} := by
    refine (((continuous_const.sub continuous_id).norm.pow 2).continuousOn.inv₀ ?_).smul
      (hh.comp (continuous_const.sub continuous_id)).continuousOn
    intro x hx
    refine pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ?_))
    intro he
    change (1 : ℂ) = x at he
    subst x
    have hh₁ : ‖(1 : ℂ)‖ ∈ Icc a b := hx
    rw [norm_one] at hh₁
    exact hs.elim (fun h => h.not_ge hh₁.2) (fun h => h.not_ge hh₁.1)
  have hgc {a b : ℝ} (ha : 0 ≤ a) (hs : b < 1 ∨ 1 < a) : ContinuousOn G (Icc a b) := by
    apply continuous_id.continuousOn.smul
    apply Real.ContinuousOn.circleAverage
    · simpa only [sub_zero] using hfc hs
    · exact fun _ hr => ha.trans hr.1
  have haint : IntegrableOn G (Ioc 0 I) :=
    (hgc le_rfl (Or.inl hi)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hbint : IntegrableOn G (Ioc O R) :=
    (hgc (Real.exp_pos _).le (Or.inr ho)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hbo : IntegrableOn G (Ioi O) :=
    hbint.of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr =>
      hGz r (lt_of_not_ge fun h => hr.2 ⟨hr.1, h⟩)
  have hbEq : (∫ r in Ioi O, G r) = ∫ r in Ioc O R, G r :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hr => hr.1) fun r hr => hGz r (lt_of_not_ge fun h => hr.2 ⟨hr.1, h⟩)
  have hbEq' : (∫ x in B', f x) = ∫ x in B, f x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioi.preimage continuous_norm.measurable) (fun _ hx => hx.1)
      fun x hx => hfz x (lt_of_not_ge fun h => hx.2 ⟨hx.1, h⟩)
  have hm : MeasurableSet B' := measurableSet_Ioi.preimage continuous_norm.measurable
  have hd : Disjoint A B' := by
    rw [disjoint_left]
    intro x hx hx'
    exact (ho.trans hx').not_ge (hx.2.trans hi.le)
  have himage : u '' (A ∪ B') = complexWeilRadialDomain δ := by
    ext z
    have hu (x : ℂ) : u x = 1 - x := rfl
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hu]
      change 0 < ‖1 - (1 - x)‖ ∧ (‖1 - (1 - x)‖ ≤ I ∨ O < ‖1 - (1 - x)‖)
      rw [sub_sub_cancel]
      rcases hx with h | h
      · exact ⟨h.1, Or.inl h.2⟩
      · exact ⟨(zero_lt_one.trans ho).trans h, Or.inr h⟩
    · intro hz
      refine ⟨1 - z, ?_, by rw [hu, sub_sub_cancel]⟩
      exact hz.2.imp (fun h => ⟨hz.1, h⟩) id
  have h₁ := Measure.measurePreserving_sub_left (volume : Measure ℂ) 1
  have hfa : IntegrableOn f A := by
    have hK : IsCompact {x : ℂ | ‖x‖ ∈ Icc 0 I} := by
      have he : {x : ℂ | ‖x‖ ∈ Icc 0 I} = Metric.closedBall 0 I := by
        ext x
        simp [Metric.mem_closedBall, dist_zero_right, norm_nonneg]
      rw [he]
      exact isCompact_closedBall _ _
    exact ((hfc (Or.inl hi)).integrableOn_compact hK).mono_set fun _ hx => Ioc_subset_Icc_self hx
  have hfb : IntegrableOn f B' := by
    have hK : IsCompact {x : ℂ | ‖x‖ ∈ Icc O R} := by
      have he : {x : ℂ | ‖x‖ ∈ Icc O R} =
          {x : ℂ | O ≤ ‖x‖} ∩ Metric.closedBall 0 R := by
        ext x
        simp [Metric.mem_closedBall, dist_zero_right]
      rw [he]
      exact (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)
    have hfB : IntegrableOn f B :=
      ((hfc (Or.inr ho)).integrableOn_compact hK).mono_set fun _ hx => Ioc_subset_Icc_self hx
    exact hfB.of_forall_sdiff_eq_zero hm fun x hx => hfz x (lt_of_not_ge fun h => hx.2 ⟨hx.1, h⟩)
  rw [← himage]
  change Real.pi⁻¹ • (∫ z in (fun x : ℂ => 1 - x) '' (A ∪ B'), (‖z‖ ^ 2)⁻¹ • h z) = _
  rw [h₁.setIntegral_image_emb u.measurableEmbedding]
  change Real.pi⁻¹ • (∫ x in A ∪ B', f x) = _
  rw [setIntegral_union hd hm hfa hfb, hbEq',
    complexWeil_integral_shell le_rfl (hfc (Or.inl hi)),
    complexWeil_integral_shell (Real.exp_pos _).le (hfc (Or.inr ho))]
  change Real.pi⁻¹ • ((2 * Real.pi) • (∫ r in Ioc 0 I, G r) +
    (2 * Real.pi) • (∫ r in Ioc O R, G r)) = _
  rw [← hbEq, ← integral_Ici_eq_integral_Ioi (x := O)]
  obtain ⟨heI, heO⟩ := complexWeil_exp_half_images δ
  obtain ⟨hI, hIe⟩ := weilRadialExp_change (-(1 / 2 : ℝ)) δ (by norm_num) G (heI ▸ haint)
  have hbIci : IntegrableOn G (Ici O) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hbo
  obtain ⟨hO, hOe⟩ := weilRadialExp_change (1 / 2) δ (by norm_num) G
    (heO ▸ hbIci)
  rw [heI] at hIe
  rw [heO] at hOe
  rw [hIe, hOe, ← integral_Ici_eq_integral_Ioi, ← smul_add, smul_smul,
    show Real.pi⁻¹ * (2 * Real.pi) = 2 by field_simp [Real.pi_ne_zero],
    add_comm, ← integral_add hO hI, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro t _
  simp only [abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)), smul_add,
    G, smul_smul, complexWeilShiftedRadial]
  rw [show (1 / 2 : ℝ) * t = t / 2 by ring, show -(1 / 2 : ℝ) * t = -t / 2 by ring]
  congr 1 <;> { congr 1; ring }

end
end Masullo
