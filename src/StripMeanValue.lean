import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.MetricSpace.Thickening

open Filter MeasureTheory Set Metric Complex Real Topology
open scoped ENNReal

namespace Masullo

private theorem polar_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I]
  simp

private theorem circleArc_integral_constant {f : ℂ → ℂ} {r : ℝ}
    (h : circleAverage f 0 r = f 0) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) = (2 * Real.pi) • f 0 := by
  have hc := circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (fun θ : ℝ => f (circleMap 0 r θ))] at hc
  have he : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [zero_add, he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, h] at hc
  rw [hc, smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

private theorem integral_ball_zero_eq_smul {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) :
    (∫ z in ball (0 : ℂ) R, f z) = (Real.pi * R ^ 2) • f 0 := by
  let α := Ioo (0 : ℝ) R
  let β := Ioo (-Real.pi) Real.pi
  let g (p : ℝ × ℝ) := p.1 • f (circleMap 0 p.1 p.2)
  have hPolar := Complex.integral_comp_polarCoord_symm ((ball (0 : ℂ) R).indicator f)
  have hIndicator : EqOn
      (fun p : ℝ × ℝ => p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p))
      ((Iio R ×ˢ (univ : Set ℝ)).indicator g) Complex.polarCoord.target := by
    intro p hp
    change p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) =
      (Iio R ×ˢ (univ : Set ℝ)).indicator g p
    have hp0 : 0 < p.1 := hp.1
    have he : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p.1 < R := by
      rw [mem_ball_zero_iff, norm_polarCoord_symm, abs_of_pos hp0]
    by_cases hpr : p.1 < R
    · have hm : p ∈ Iio R ×ˢ (univ : Set ℝ) := ⟨hpr, mem_univ _⟩
      rw [indicator_of_mem (he.mpr hpr) f, indicator_of_mem hm g]
      exact congrArg (fun z => p.1 • f z) (polar_eq_circleMap p)
    · have hm : p ∉ Iio R ×ˢ (univ : Set ℝ) := fun h => hpr h.1
      rw [indicator_of_notMem (he.not.mpr hpr) f, indicator_of_notMem hm g, smul_zero]
  have hRing : (Iio R ×ˢ (univ : Set ℝ)) ∩ Complex.polarCoord.target = α ×ˢ β := by
    ext p
    change (p.1 < R ∧ p.2 ∈ (univ : Set ℝ)) ∧ (0 < p.1 ∧ p.2 ∈ β) ↔
      (0 < p.1 ∧ p.1 < R) ∧ p.2 ∈ β
    simp
    tauto
  have hInt : IntegrableOn g (α ×ˢ β) (volume : Measure (ℝ × ℝ)) := by
    have hcont : ContinuousOn g (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) := by
      have hparam : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
        unfold circleMap
        fun_prop
      refine continuous_fst.continuousOn.smul (hf.continuousOn.comp hparam.continuousOn ?_)
      intro p hp
      rw [closure_ball _ hR.ne']
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hp.1.1]
      exact hp.1.2
    exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [integral_indicator isOpen_ball.measurableSet] at hPolar
  have ht : MeasurableSet Complex.polarCoord.target :=
    Complex.polarCoord.open_target.measurableSet
  change (∫ p in Complex.polarCoord.target, p.1 • (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) =
    (∫ z in ball (0 : ℂ) R, f z) at hPolar
  rw [← hPolar, setIntegral_congr_fun ht hIndicator,
    setIntegral_indicator (measurableSet_Iio.prod MeasurableSet.univ), inter_comm Complex.polarCoord.target, hRing]
  rw [Measure.volume_eq_prod] at hInt ⊢
  rw [setIntegral_prod g hInt]
  have hinner (r : ℝ) (hr : r ∈ α) : (∫ θ in β, g (r,θ)) = r • ((2 * Real.pi) • f 0) := by
    have hsub : ball (0 : ℂ) |r| ⊆ ball (0 : ℂ) R :=
      ball_subset_ball (by rw [abs_of_pos hr.1]; exact hr.2.le)
    have hav := (hf.mono hsub).circleAverage
    rw [show (fun θ => g (r, θ)) = (fun θ => r • f (circleMap 0 r θ)) from rfl, integral_smul]
    rw [circleArc_integral_constant hav]
  rw [setIntegral_congr_fun measurableSet_Ioo hinner]
  have hrscalar : (∫ r in α, r : ℝ) = R ^ 2 / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le]
    simp [integral_id]
  rw [integral_smul_const, hrscalar, smul_smul]
  congr 1
  ring


private theorem integral_ball_eq_smul {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) :
    (∫ z in ball c R, f z) = (Real.pi * R ^ 2) • f c := by
  let g (z : ℂ) := f (c + z)
  have hg : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    have ht : Differentiable ℂ (fun z : ℂ => c + z) := by fun_prop
    apply hf.comp ht.differentiableOn
    intro z hz
    rw [closure_ball _ hR.ne'] at hz
    simpa [Metric.mem_closedBall] using hz
  have hEq : (ball c R).indicator f ∘ (fun z : ℂ => c + z) = (ball (0 : ℂ) R).indicator g := by
    funext z
    have he : c + z ∈ ball c R ↔ z ∈ ball 0 R := by simp [Metric.mem_ball]
    by_cases hz : z ∈ ball (0 : ℂ) R
    · simp [Function.comp_apply, indicator_of_mem (he.mpr hz), indicator_of_mem hz, g]
    · simp [Function.comp_apply, indicator_of_notMem (he.not.mpr hz), indicator_of_notMem hz]
  calc
    _ = ∫ z : ℂ, (ball c R).indicator f z := (integral_indicator isOpen_ball.measurableSet).symm
    _ = ∫ z : ℂ, ((ball c R).indicator f ∘ (fun z : ℂ => c + z)) z := by
      symm
      exact (measurePreserving_add_left volume c).integral_comp
        (MeasurableEquiv.addLeft c).measurableEmbedding _
    _ = ∫ z in ball (0 : ℂ) R, g z := by rw [hEq, integral_indicator isOpen_ball.measurableSet]
    _ = _ := by simpa [g] using integral_ball_zero_eq_smul hR hg

private theorem convexOn_normSq : ConvexOn ℝ univ (fun z : ℂ => ‖z‖ ^ 2) := by
  have hrange : (norm : ℂ → ℝ) '' (univ : Set ℂ) = Ici 0 := by
    ext r
    constructor
    · rintro ⟨z, _, rfl⟩
      exact norm_nonneg z
    · intro hr
      exact ⟨(r : ℂ), mem_univ _, by rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ r from hr)]⟩
  have hpow : ConvexOn ℝ ((norm : ℂ → ℝ) '' (univ : Set ℂ)) (fun r => r ^ 2) := by
    rw [hrange]
    exact convexOn_pow 2
  apply hpow.comp (convexOn_norm convex_univ)
  rw [hrange]
  exact fun x hx y _ hxy => pow_le_pow_left₀ hx hxy 2

/-- The squared modulus of a holomorphic function is at most its disk
average at the center, with the exact area constant. -/
theorem normSq_le_ball_average {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) :
    Real.pi * R ^ 2 * ‖f c‖ ^ 2 ≤ ∫ z in ball c R, ‖f z‖ ^ 2 := by
  let D := ball c R
  have hC : 0 < Real.pi * R ^ 2 := by positivity
  have hvol : volume D = ENNReal.ofReal (Real.pi * R ^ 2) := by
    rw [show D = ball c R from rfl, Complex.volume_ball]
    rw [← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), NNReal.coe_real_pi]
    rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (sq_nonneg R), mul_comm]
  have hfin : volume D ≠ ∞ := hvol.trans_ne ENNReal.ofReal_ne_top
  have hpos : volume D ≠ 0 := hvol.trans_ne (ENNReal.ofReal_pos.mpr hC).ne'
  have hfi : IntegrableOn f D := (hf.continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set
    ball_subset_closedBall
  have hgi : IntegrableOn (fun z => ‖f z‖ ^ 2) D :=
    ((hf.continuousOn.norm.pow 2).integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  have hJ := convexOn_normSq.map_set_average_le ((continuous_norm.pow 2).continuousOn)
    isClosed_univ hpos hfin (.of_forall fun _ => mem_univ _) hfi hgi
  have hA : volume.real (ball c R) = Real.pi * R ^ 2 := by
    change volume.real D = _
    rw [measureReal_def, hvol, ENNReal.toReal_ofReal hC.le]
  simp only [setAverage_eq, show D = ball c R from rfl, hA, integral_ball_eq_smul hR hf,
    inv_smul_smul₀ hC.ne'] at hJ
  change ‖f c‖ ^ 2 ≤ (Real.pi * R ^ 2)⁻¹ * ∫ z in D, ‖f z‖ ^ 2 at hJ
  exact (le_inv_mul_iff₀ hC).mp hJ


/-- Lemma B.5.3.5. An L² return on the open neighborhood implies a uniform
return on the compact set, with the disk-area factor `π δ²`. -/
theorem stripReturn_sup_of_localL2 {a b : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Ioo a b))
    {K U : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (_hU : IsOpen U) (hc : IsCompact (closure U))
    (hUS : closure U ⊆ Complex.re ⁻¹' Ioo a b)
    {δ X t : ℝ} (hδ : 0 < δ) (hX : 0 < X)
    (hball : ∀ z ∈ K, ball z δ ⊆ U)
    (hL2 : (∫ z in U, ‖f (z + (t : ℂ) * I) - f z‖ ^ 2) < π * δ ^ 2 * X ^ 2) :
    sSup ((fun z => ‖f (z + (t : ℂ) * I) - f z‖) '' K) < X := by
  let S := Complex.re ⁻¹' Ioo a b
  let g (z : ℂ) := f (z + (t : ℂ) * I) - f z
  have hg : DifferentiableOn ℂ g S := by
    have hshift : MapsTo (fun z : ℂ => z + (t : ℂ) * I) S S := by
      intro z hz
      change a < (z + (t : ℂ) * I).re ∧ (z + (t : ℂ) * I).re < b
      have hzero : ((t : ℂ) * I).re = 0 := by simp [mul_re]
      simpa [add_re, hzero, S] using hz
    exact (hf.comp (by fun_prop) hshift).sub hf
  have hK' : K ⊆ U := fun z hz => hball z hz (mem_ball_self hδ)
  have hgcont : ContinuousOn (fun z => ‖g z‖) K := hg.continuousOn.norm.mono
    (hK'.trans (subset_closure.trans hUS))
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hne hgcont
  have hzBound : sSup ((fun z => ‖g z‖) '' K) ≤ ‖g z‖ := by
    apply csSup_le (hne.image _)
    rintro _ ⟨w, hw, rfl⟩
    exact hzmax hw
  have hzclosed : closedBall z δ ⊆ closure U := by
    rw [← closure_ball z hδ.ne']
    exact closure_mono (hball z hzK)
  have hintegrable : IntegrableOn (fun w => ‖g w‖ ^ 2) U :=
    ((hg.continuousOn.norm.pow 2).mono hUS |>.integrableOn_compact hc).mono_set subset_closure
  have hmono : (∫ w in ball z δ, ‖g w‖ ^ 2) ≤ ∫ w in U, ‖g w‖ ^ 2 :=
    setIntegral_mono_set hintegrable (Eventually.of_forall fun w => sq_nonneg ‖g w‖)
      (Eventually.of_forall (hball z hzK))
  have hm := (normSq_le_ball_average hδ (hg.mono (hzclosed.trans hUS))).trans hmono
  have hstrict : π * δ ^ 2 * ‖g z‖ ^ 2 < π * δ ^ 2 * X ^ 2 := hm.trans_lt hL2
  have hsq : ‖g z‖ ^ 2 < X ^ 2 := lt_of_mul_lt_mul_left hstrict (by positivity)
  have hzlt : ‖g z‖ < X := by
    by_contra! h
    exact (not_lt_of_ge (pow_le_pow_left₀ hX.le h 2)) hsq
  exact hzBound.trans_lt hzlt

/-- Every compact set in an open strip admits the neighborhoods used in the
local L² return estimate. -/
theorem stripReturn_compact_neighborhood {a b : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hKS : K ⊆ Complex.re ⁻¹' Ioo a b) :
    ∃ (U : Set ℂ) (δ : ℝ), IsOpen U ∧ 0 < δ ∧ IsCompact (closure U) ∧
      closure U ⊆ Complex.re ⁻¹' Ioo a b ∧ ∀ z ∈ K, ball z δ ⊆ U := by
  have hS : IsOpen (Complex.re ⁻¹' Ioo a b) := isOpen_Ioo.preimage Complex.continuous_re
  obtain ⟨δ, hδ, ht⟩ := hK.exists_cthickening_subset_open hS hKS
  let U := Metric.thickening δ K
  have hsub : closure U ⊆ Metric.cthickening δ K :=
    Metric.closure_thickening_subset_cthickening δ K
  refine ⟨U, δ, Metric.isOpen_thickening, hδ,
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hsub,
    hsub.trans ht, ?_⟩
  intro z hz w hw
  exact Metric.mem_thickening_iff.mpr ⟨z, hz, hw⟩

end Masullo
