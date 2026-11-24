import HomogeneousThetaMellin
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

/- The formulation of the triangular covariance and pole-bound filtration
   follows the corrections recorded by mccorvie/riemann-masullo at 5e4b212
   under Apache-2.0. This proof uses the actual continued Mellin transforms. -/

noncomputable section

private def circleExtension (c : ℂ) (R : ℝ) (u : C(Metric.sphere c R, ℂ)) (w : ℂ) : ℂ :=
  if h : w ∈ Metric.sphere c R then u ⟨w, h⟩ else 0

private theorem circleExtension_continuousOn (c : ℂ) (R : ℝ)
    (u : C(Metric.sphere c R, ℂ)) : ContinuousOn (circleExtension c R u) (Metric.sphere c R) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert u.continuous using 1
  funext w
  exact dite_eq_left w.property

private def laurentCircleIntegrand (c : ℂ) (R : ℝ) (k : ℕ)
    (u : C(Metric.sphere c R, ℂ)) (w : ℂ) : ℂ :=
  (w - c) ^ k / (w - c) * circleExtension c R u w

private theorem laurentCircleIntegrand_continuousOn (c : ℂ) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (u : C(Metric.sphere c R, ℂ)) :
    ContinuousOn (laurentCircleIntegrand c R k u) (Metric.sphere c R) := by
  apply (((continuous_id.sub continuous_const).pow k).continuousOn.div
    (continuous_id.sub continuous_const).continuousOn ?_).mul (circleExtension_continuousOn c R u)
  intro z hz
  apply sub_ne_zero.mpr
  intro he
  change z = c at he
  subst z
  exact hR.ne' (by simpa using (Metric.mem_sphere.mp hz).symm)

/-- The normalized contour functional for Laurent exponent `-k` on a
circle. Its input is a continuous function on the circle with the uniform norm. -/
def laurentCircleFunctional (c : ℂ) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    C(Metric.sphere c R, ℂ) →L[ℂ] ℂ := by
  letI : CompactSpace (Metric.sphere c R) := isCompact_iff_compactSpace.mp (isCompact_sphere c R)
  let I := laurentCircleIntegrand c R k
  let a := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  let L : C(Metric.sphere c R, ℂ) →ₗ[ℂ] ℂ := {
    toFun u := a * circleIntegral (I u) c R
    map_add' u v := by
      change a * circleIntegral (I (u + v)) c R = _
      rw [circleIntegral.integral_congr hR.le
        (show EqOn (I (u + v)) (fun w ↦ I u w + I v w) (Metric.sphere c R) by
          intro w hw
          simp only [I, laurentCircleIntegrand, circleExtension, dite_eq_left hw, ContinuousMap.add_apply, mul_add]),
        circleIntegral.integral_add
          ((laurentCircleIntegrand_continuousOn c R hR k u).circleIntegrable hR.le)
          ((laurentCircleIntegrand_continuousOn c R hR k v).circleIntegrable hR.le)]
      exact mul_add _ _ _
    map_smul' b u := by
      change a * circleIntegral (I (b • u)) c R = b * (a * circleIntegral (I u) c R)
      rw [circleIntegral.integral_congr hR.le
        (show EqOn (I (b • u)) (fun w ↦ b * I u w) (Metric.sphere c R) by
          intro w hw
          simp only [I, laurentCircleIntegrand, circleExtension, dite_eq_left hw,
            ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm]),
        circleIntegral.integral_const_mul, mul_left_comm] }
  refine L.mkContinuous (‖a‖ * (2 * Real.pi * |R| * (R ^ k / R))) ?_
  intro u
  have hi : ∀ w ∈ Metric.sphere c R, ‖I u w‖ ≤ (R ^ k / R) * ‖u‖ := by
    intro w hw
    have he : ‖w - c‖ = R := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hw
    simp only [I, laurentCircleIntegrand, circleExtension, dite_eq_left hw, norm_mul, norm_div,
      norm_pow, he]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm u ⟨w, hw⟩) (by positivity)
  change ‖a * circleIntegral (I u) c R‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (circleIntegral.norm_integral_le_of_norm_le_const hR.le hi)
    (norm_nonneg a)).trans_eq (by rw [abs_of_pos hR]; ring)

theorem laurentCircleFunctional_apply (c : ℂ) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (u : C(Metric.sphere c R, ℂ)) (f : ℂ → ℂ)
    (hf : ∀ w : Metric.sphere c R, u w = f w.val) :
    laurentCircleFunctional c R hR k u =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun w ↦ (w - c) ^ k / (w - c) * f w) c R := by
  change _ * circleIntegral (laurentCircleIntegrand c R k u) c R = _
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro w hw
  simp only [laurentCircleIntegrand, circleExtension, dite_eq_left hw, hf]

/-- The circle integral for exponent `-k` is the Taylor coefficient at
index `N-k` of the holomorphic function after clearing a pole of order at most `N`. -/
theorem laurentCircle_eq_taylor_of_cleared {c : ℂ} {R : ℝ} (hR : 0 < R)
    (f g : ℂ → ℂ) (N k : ℕ) (hg : DifferentiableOn ℂ g (Metric.closedBall c R))
    (heq : EqOn g (fun w ↦ (w - c)^N * f w) (Metric.sphere c R)) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun w ↦ (w - c)^k / (w - c) * f w) c R =
      if k ≤ N then iteratedDeriv (N - k) g c / ((N - k).factorial : ℂ) else 0 := by
  let A := 2 * (Real.pi : ℂ) * Complex.I
  have hA : A ≠ 0 := Complex.two_pi_I_ne_zero
  have hne (w : ℂ) (hw : w ∈ Metric.sphere c R) : w - c ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    subst w
    exact hR.ne' (by simpa using (Metric.mem_sphere.mp hw).symm)
  by_cases h : k ≤ N
  · rw [ite_eq_left h]
    have hi : EqOn (fun w ↦ (w - c)^k / (w - c) * f w)
        (fun w ↦ (1 / (w - c)^(N-k+1)) • g w) (Metric.sphere c R) := by
      intro w hw
      simp only [heq hw, smul_eq_mul]
      have hp : (w - c)^N = (w - c)^k * (w - c)^(N-k) := by
        rw [← pow_add, Nat.add_sub_of_le h]
      rw [hp, pow_succ]
      field_simp [hne w hw]
    rw [circleIntegral.integral_congr hR.le hi, hg.circleIntegral_one_div_sub_center_pow_smul hR]
    change A⁻¹ * ((A / ((N - k).factorial : ℂ)) * iteratedDeriv (N - k) g c) = _
    field_simp [hA]
  · rw [ite_eq_right h]
    let b (w : ℂ) := (w - c)^(k-N) * g w
    have hb : DifferentiableOn ℂ b (Metric.closedBall c R) :=
      ((differentiableOn_id.sub_const c).pow (k - N)).mul hg
    have hi : EqOn (fun w ↦ (w - c)^k / (w - c) * f w)
        (fun w ↦ (1 / (w - c)^(0+1 : ℕ)) • b w) (Metric.sphere c R) := by
      intro w hw
      simp only [b, heq hw, zero_add, pow_one, smul_eq_mul]
      have hp : (w - c)^k = (w - c)^(k-N) * (w - c)^N := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [hp]
      field_simp [hne w hw]
    rw [circleIntegral.integral_congr hR.le hi, hb.circleIntegral_one_div_sub_center_pow_smul hR]
    have hz : b c = 0 := by
      simp [b, zero_pow (show k - N ≠ 0 by omega)]
    simp [iteratedDeriv_zero, hz]

private theorem analyticAt_of_meromorphicOrder_nonneg_and_continuous {f : ℂ → ℂ} {c : ℂ}
    (hm : Meromorphic f) (hc : ContinuousAt f c) (ho : 0 ≤ meromorphicOrderAt f c) :
    AnalyticAt ℂ f c := by
  let g := toMeromorphicNFOn f univ
  have hEq : g =ᶠ[𝓝[≠] c] f :=
    hm.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ c)
  have hg : AnalyticAt ℂ g c := by
    apply (meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ c)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_congr hEq]
    exact ho
  have he := (hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc).mp hEq
  exact hg.congr he

private theorem laurentClear_order {f : ℂ → ℂ} {c : ℂ} (hm : Meromorphic f) (N : ℕ) :
    meromorphicOrderAt (fun w ↦ (w - c)^N * f w) c =
      (N : ℤ) + meromorphicOrderAt f c := by
  let g (w : ℂ) := (w - c)^N
  have hg : AnalyticAt ℂ g c := (analyticAt_id.sub analyticAt_const).pow N
  change meromorphicOrderAt (g * f) c = _
  rw [meromorphicOrderAt_mul hg.meromorphicAt (hm c)]
  have he : meromorphicOrderAt g c = (N : WithTop ℤ) :=
    meromorphicOrderAt_pow_id_sub_const (x := c) (n := N)
  rw [he]
  push_cast
  rfl

/-- Clearing a pole preserves its analytic values off the center and adds the clearing exponent to the order. -/
theorem laurentClear_analyticOnNhd {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hm : Meromorphic f) (N : ℕ) (ho : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c)
    (hreg : ∀ w ∈ Metric.closedBall c R \ {c}, AnalyticAt ℂ f w) :
    let g := toMeromorphicNFOn (fun w ↦ (w - c)^N * f w) univ
    AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      EqOn g (fun w ↦ (w - c)^N * f w) (Metric.closedBall c R \ {c}) ∧
      meromorphicOrderAt g c = (N : ℤ) + meromorphicOrderAt f c := by
  let p (w : ℂ) := (w - c)^N * f w
  let g := toMeromorphicNFOn p univ
  have hp : Meromorphic p := fun w ↦
    (((analyticAt_id.sub (analyticAt_const (v := c))).pow N).meromorphicAt.mul (hm w))
  have hEq (w : ℂ) : g =ᶠ[𝓝[≠] w] p :=
    hp.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ w)
  have hn (w : ℂ) : MeromorphicNFAt g w := meromorphicNFOn_toMeromorphicNFOn p univ (mem_univ w)
  have he (w : ℂ) : meromorphicOrderAt g w = meromorphicOrderAt p w :=
    meromorphicOrderAt_congr (hEq w)
  have hg (w : ℂ) (hw : w ∈ Metric.closedBall c R) : AnalyticAt ℂ g w := by
    apply (hn w).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [he w]
    by_cases h : w = c
    · subst w
      rw [laurentClear_order hm]
      exact (by simp : (0 : WithTop ℤ) ≤
        ((N : ℤ) : WithTop ℤ) + ((-(N : ℤ) : ℤ) : WithTop ℤ)).trans (add_le_add_right ho _)
    · exact (((analyticAt_id.sub analyticAt_const).pow N).mul
        (hreg w ⟨hw, h⟩)).meromorphicOrderAt_nonneg
  refine ⟨hg, ?_, (he c).trans (laurentClear_order hm N)⟩
  intro w hw
  have hpc : ContinuousAt p w :=
    (((analyticAt_id.sub analyticAt_const).pow N).mul (hreg w hw)).continuousAt
  exact ((hg w hw.1).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hpc).mp
    (hEq w) |>.eq_of_nhds

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S
private abbrev ArchUnits := (InfiniteAdeleRing F)ˣ

/-- A disk around any point can be chosen with no other Euler poles. -/
theorem exists_sLocalMellinLaurentDisk (ω : PontryaginDual (K F S)) (c : ℂ) :
    ∃ R : ℝ, 0 < R ∧ Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω := by
  let D := sLocalEulerDenominator F S ω
  have hD : AnalyticOnNhd ℂ D univ := fun z _ ↦ sLocalEulerDenominator_analytic F S ω z
  have h1 : D 1 ≠ 0 := sLocalEulerDenominator_ne_zero_of_pos F S ω (by norm_num)
  have ho : analyticOrderAt D c ≠ ⊤ := by
    intro hc
    exact h1 (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero c (fun z ↦ hD z trivial)).mp hc) 1)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ho
  obtain ⟨g, hg, hgc, hEq⟩ := ((hD c trivial).analyticOrderAt_eq_natCast).mp hn.symm
  have hNe : ∀ᶠ z in 𝓝[≠] c, D z ≠ 0 := by
    filter_upwards [hEq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
      (hg.continuousAt.eventually_ne hgc).filter_mono nhdsWithin_le_nhds] with z hz hz' hgz
    rw [hz]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz')) hgz
  obtain ⟨R, hR, hsub⟩ :=
    Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hNe)
  refine ⟨R / 2, half_pos hR, fun z hz ↦ ?_⟩
  rw [sLocalMellinRegularSet_iff_noEulerPole, ← not_lt, sLocalEulerFactor_order_lt_zero_iff]
  exact hsub (Metric.closedBall_subset_ball (half_lt_self hR) hz.1) hz.2

private theorem sphere_subset_sLocalMellinRegular (ω : PontryaginDual (K F S)) (c : ℂ)
    {R : ℝ} (hR : 0 < R)
    (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω) :
    Metric.sphere c R ⊆ sLocalMellinRegularSet F S ω := by
  intro z hz
  apply hD
  refine ⟨Metric.sphere_subset_closedBall hz, ?_⟩
  intro hz'
  rw [mem_singleton_iff.mp hz', Metric.mem_sphere, dist_self] at hz
  exact hR.ne' hz.symm

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- The Laurent contour of the actual S-local continued transform is a
continuous linear test functional, including at coincident Euler poles. -/
def sLocalLaurentCircleCoeff (ω : PontryaginDual (K F S)) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω)
    (k : ℕ) : StrongDual ℂ (E F S) :=
  (laurentCircleFunctional c R hR k).comp
    (sLocalMellinCompact F S μ ω (Metric.sphere c R) (isCompact_sphere c R)
      (sphere_subset_sLocalMellinRegular F S ω c hR hD))

theorem sLocalLaurentCircleCoeff_apply (ω : PontryaginDual (K F S)) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω)
    (k : ℕ) (f : E F S) :
    sLocalLaurentCircleCoeff F S μ ω c R hR hD k f =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun w ↦ (w - c) ^ k / (w - c) * Z F S μ ω f w) c R :=
  laurentCircleFunctional_apply c R hR k _ _ (fun _ ↦ rfl)

/-- Finite order of the reciprocal Euler product at the center. -/
def sLocalAllowedPoleOrder (ω : PontryaginDual (K F S)) (c : ℂ) : ℕ :=
  (analyticOrderAt (sLocalEulerDenominator F S ω) c).toNat

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ] in
theorem sLocalEulerFactor_order (ω : PontryaginDual (K F S)) (c : ℂ) :
    meromorphicOrderAt (sLocalEulerFactor F S ω) c = ((-(sLocalAllowedPoleOrder F S ω c : ℤ) : ℤ) : WithTop ℤ) := by
  let D := sLocalEulerDenominator F S ω
  have hD (z : ℂ) : AnalyticAt ℂ D z := sLocalEulerDenominator_analytic F S ω z
  have h1 : D 1 ≠ 0 := sLocalEulerDenominator_ne_zero_of_pos F S ω (by norm_num)
  have ho : analyticOrderAt D c ≠ ⊤ := by
    intro hc
    exact h1 (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero c hD).mp hc) 1)
  change meromorphicOrderAt D⁻¹ c = _
  rw [meromorphicOrderAt_inv, (hD c).meromorphicOrderAt_eq]
  unfold sLocalAllowedPoleOrder
  rw [← ENat.natCast_toNat ho, ENat.map_natCast]
  rfl

/-- The original zeta representative is analytic off the Euler divisor. -/
theorem sLocalZeta_analyticAt_regular (ω : PontryaginDual (K F S)) (f : E F S)
    {w : ℂ} (hw : w ∈ sLocalMellinRegularSet F S ω) :
    AnalyticAt ℂ (Z F S μ ω f) w := by
  apply analyticAt_of_meromorphicOrder_nonneg_and_continuous
    (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f)
    ((sLocalProductZetaContinued_continuousOn_regular F S μ ω f w hw).continuousAt
      ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds hw))
  exact ((sLocalMellinRegularSet_iff_noEulerPole F S ω w).mp hw).trans
    (sLocalZeta_poleOrder_le_euler F S μ ω f w)

/-- The contour returns a Laurent coefficient in the usual Taylor series of
the pole-cleared normal form. -/
theorem sLocalLaurentCircleCoeff_eq_taylor (ω : PontryaginDual (K F S)) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω)
    (k : ℕ) (f : E F S) :
    let N := sLocalAllowedPoleOrder F S ω c
    let G := toMeromorphicNFOn (fun w ↦ (w - c)^N * Z F S μ ω f w) univ
    sLocalLaurentCircleCoeff F S μ ω c R hR hD k f =
      if k ≤ N then iteratedDeriv (N - k) G c / ((N - k).factorial : ℂ) else 0 := by
  intro N G
  have hm := sLocalProductZetaContinued_meromorphic F S μ ω
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) f
  have hBound : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
    rw [← sLocalEulerFactor_order F S ω c]
    exact sLocalZeta_poleOrder_le_euler F S μ ω f c
  obtain ⟨hg, heq, _⟩ := laurentClear_analyticOnNhd hm N hBound
    (fun w hw ↦ sLocalZeta_analyticAt_regular F S μ ω f (hD hw))
  rw [sLocalLaurentCircleCoeff_apply]
  exact laurentCircle_eq_taylor_of_cleared hR _ G N k
    (fun w hw ↦ (hg w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ heq ⟨Metric.sphere_subset_closedBall hw,
      fun h ↦ hR.ne' (by simpa [mem_singleton_iff.mp h] using (Metric.mem_sphere.mp hw).symm)⟩)

theorem sLocalLaurentCircleCoeff_eq_of_radii (ω : PontryaginDual (K F S)) (c : ℂ)
    {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω)
    (hE : Metric.closedBall c T \ {c} ⊆ sLocalMellinRegularSet F S ω) (k : ℕ) :
    sLocalLaurentCircleCoeff F S μ ω c R hR hD k =
      sLocalLaurentCircleCoeff F S μ ω c T hT hE k := by
  apply ContinuousLinearMap.ext
  intro f
  rw [sLocalLaurentCircleCoeff_eq_taylor, sLocalLaurentCircleCoeff_eq_taylor]

/-- The Laurent coefficient at exponent `-k` of the S-local Mellin transform,
independent of the contour chosen around the center. -/
def sLocalLaurentCoeff (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) :
    StrongDual ℂ (E F S) :=
  let h := exists_sLocalMellinLaurentDisk F S ω c
  sLocalLaurentCircleCoeff F S μ ω c h.choose h.choose_spec.1 h.choose_spec.2 k

private theorem taylorPoleBound_iff {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (N m : ℕ) :
    (∀ k > m, k ≤ N → iteratedDeriv (N - k) f c = 0) ↔
      ((N - m : ℕ) : WithTop ℤ) ≤ meromorphicOrderAt f c := by
  have he : (∀ k > m, k ≤ N → iteratedDeriv (N - k) f c = 0) ↔
      ∀ i < N - m, iteratedDeriv i f c = 0 := by
    constructor
    · intro h i hi
      have hv := h (N - i) (by omega) (by omega)
      rwa [show N - (N - i) = i by omega] at hv
    · intro h k hk hN
      exact h (N - k) (by omega)
  rw [he, ← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf, hf.meromorphicOrderAt_eq]
  cases h : analyticOrderAt f c with
  | top => simp
  | coe n =>
    rw [ENat.map_natCast, ENat.natCast_le_natCast]
    change N - m ≤ n ↔ ((N - m : ℕ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ)
    norm_cast

/-- The prescribed pole bound is equivalent to vanishing of all Laurent
coefficients with index greater than the bound. -/
theorem sLocalLaurentCoeff_vanish_iff (ω : PontryaginDual (K F S)) (c : ℂ)
    (m : ℕ) (f : E F S) :
    (∀ k > m, sLocalLaurentCoeff F S μ ω c k f = 0) ↔
      ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
  let N := sLocalAllowedPoleOrder F S ω c
  let h := exists_sLocalMellinLaurentDisk F S ω c
  let R := h.choose
  let G := toMeromorphicNFOn (fun w ↦ (w - c)^N * Z F S μ ω f w) univ
  have hm : Meromorphic (Z F S μ ω f) := sLocalProductZetaContinued_meromorphic F S μ ω _ _ f
  have hBound : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
    rw [← sLocalEulerFactor_order F S ω c]
    exact sLocalZeta_poleOrder_le_euler F S μ ω f c
  obtain ⟨hg', _, hgo⟩ := laurentClear_analyticOnNhd hm N hBound
    (fun w hw ↦ sLocalZeta_analyticAt_regular F S μ ω f (h.choose_spec.2 hw))
  have hg : AnalyticAt ℂ G c := hg' c (Metric.mem_closedBall_self h.choose_spec.1.le)
  have hcoeff (k : ℕ) : sLocalLaurentCoeff F S μ ω c k f =
      if k ≤ N then iteratedDeriv (N - k) G c / ((N - k).factorial : ℂ) else 0 :=
    sLocalLaurentCircleCoeff_eq_taylor F S μ ω c _ h.choose_spec.1 h.choose_spec.2 k f
  have hfact (i : ℕ) : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have he : (∀ k > m, sLocalLaurentCoeff F S μ ω c k f = 0) ↔
      ∀ k > m, k ≤ N → iteratedDeriv (N - k) G c = 0 := by
    constructor
    · intro hz k hk hle
      have hval := hz k hk
      rwa [hcoeff, ite_eq_left hle, div_eq_zero_iff, or_iff_left (hfact _)] at hval
    · intro hz k hk
      rw [hcoeff]
      split_ifs with hle
      · rw [hz k hk hle, zero_div]
      · rfl
  rw [he, taylorPoleBound_iff hg, hgo]
  by_cases hle : m ≤ N
  · cases hz : meromorphicOrderAt (Z F S μ ω f) c with
    | top => simp
    | coe n =>
      change (((N - m : ℕ) : ℤ) : WithTop ℤ) ≤ ((N : ℤ) : WithTop ℤ) + (n : WithTop ℤ) ↔
        ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ)
      rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
      omega
  · have h' : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c :=
      (WithTop.coe_le_coe.mpr (by omega : -(m : ℤ) ≤ -(N : ℤ))).trans hBound
    have go : (0 : WithTop ℤ) ≤ (N : ℤ) + meromorphicOrderAt (Z F S μ ω f) c :=
      (by simp : (0 : WithTop ℤ) ≤ ((N : ℤ) : WithTop ℤ) + ((-(N : ℤ) : ℤ) : WithTop ℤ)).trans
        (add_le_add_right hBound _)
    rw [Nat.sub_eq_zero_of_le (by omega : N ≤ m)]
    exact ⟨fun _ ↦ h', fun _ ↦ go⟩

/-- A nonzero coefficient of negative exponent detects a pole on the
particular test, of at least the indicated order. -/
theorem sLocalLaurentCoeff_ne_zero_imp_order (ω : PontryaginDual (K F S)) (c : ℂ)
    {k : ℕ} (hk : 0 < k) (f : E F S) (hf : sLocalLaurentCoeff F S μ ω c k f ≠ 0) :
    meromorphicOrderAt (Z F S μ ω f) c ≤ ((-(k : ℤ) : ℤ) : WithTop ℤ) ∧
      0 < sLocalAllowedPoleOrder F S ω c := by
  have ho : ¬ (((-((k - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c) :=
    fun h ↦ hf ((sLocalLaurentCoeff_vanish_iff F S μ ω c (k - 1) f).mpr h k (by omega))
  have hh : meromorphicOrderAt (Z F S μ ω f) c ≤ ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
    cases h : meromorphicOrderAt (Z F S μ ω f) c with
    | top => simp [h] at ho
    | coe n =>
      rw [h, WithTop.coe_le_coe] at ho
      rw [WithTop.coe_le_coe]
      omega
  refine ⟨hh, ?_⟩
  have hE := (sLocalZeta_poleOrder_le_euler F S μ ω f c).trans hh
  rw [sLocalEulerFactor_order F S ω c, WithTop.coe_le_coe] at hE
  omega

/-- Translation acts on Laurent coefficients by an upper triangular formula.
Only the top coefficient is forced to transform by the character for every translation. -/
theorem sLocalLaurentCoeff_translate [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
    (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) (hk : k ≤ sLocalAllowedPoleOrder F S ω c)
    (u : (SAdeles F S)ˣ) (f : E F S) :
    let q : SIdeleQuotient F S := QuotientGroup.mk u
    let a : ℂ := ((sLocalZetaSplit F S).symm q).1
    sLocalLaurentCoeff F S μ ω c k (sLocalBruhatLeftTranslate F S u f) =
      sLocalZetaWeight F S ω c q * ∑ j ∈ Finset.range (sLocalAllowedPoleOrder F S ω c - k + 1),
        a^j / (j.factorial : ℂ) * sLocalLaurentCoeff F S μ ω c (k+j) f := by
  intro q a
  let N := sLocalAllowedPoleOrder F S ω c
  let h := exists_sLocalMellinLaurentDisk F S ω c
  let R := h.choose
  let G := toMeromorphicNFOn (fun w ↦ (w - c)^N * Z F S μ ω f w) univ
  let W (w : ℂ) := sLocalZetaWeight F S ω w q
  let b : ℂ := (ω ((sLocalZetaSplit F S).symm q).2 : Circle)
  have hW : ∀ w, AnalyticAt ℂ W w := fun w ↦
    (((analyticAt_id.mul analyticAt_const).cexp).mul analyticAt_const)
  have hWd (j : ℕ) : iteratedDeriv j W c = W c * a^j := by
    change iteratedDeriv j (fun w ↦ Complex.exp (w * a) * b) c = _
    simp only [show (fun w : ℂ ↦ Complex.exp (w * a) * b) =
        (fun w ↦ Complex.exp (a * w) * b) from funext fun w ↦ by rw [mul_comm w a],
      iteratedDeriv_mul_const_field, iteratedDeriv_cexp_const_mul]
    change (a ^ j * Complex.exp (a * c)) * b = Complex.exp (c * a) * b * a ^ j
    rw [mul_comm a c]
    ring
  have hm : Meromorphic (Z F S μ ω f) := sLocalProductZetaContinued_meromorphic F S μ ω _ _ f
  have hBound : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
    rw [← sLocalEulerFactor_order F S ω c]
    exact sLocalZeta_poleOrder_le_euler F S μ ω f c
  obtain ⟨hg, heq, _⟩ := laurentClear_analyticOnNhd hm N hBound
    (fun w hw ↦ sLocalZeta_analyticAt_regular F S μ ω f (h.choose_spec.2 hw))
  have hs := sphere_subset_sLocalMellinRegular F S ω c h.choose_spec.1 h.choose_spec.2
  have hEq : EqOn (W * G) (fun w ↦ (w - c)^N * Z F S μ ω (sLocalBruhatLeftTranslate F S u f) w)
      (Metric.sphere c R) := by
    intro w hw
    have hR : 0 < R := h.choose_spec.1
    have hmem : w ∈ Metric.closedBall c R \ {c} := ⟨Metric.sphere_subset_closedBall hw, fun he ↦
      hR.ne' (by simpa [mem_singleton_iff.mp he] using (Metric.mem_sphere.mp hw).symm)⟩
    have he : G w = (w - c)^N * Z F S μ ω f w := heq hmem
    have ht : Z F S μ ω (sLocalBruhatLeftTranslate F S u f) w = W w * Z F S μ ω f w :=
      sLocalProductZetaContinued_leftTranslate F S μ ω u f (hs hw)
    change W w * G w = (w - c)^N * Z F S μ ω (sLocalBruhatLeftTranslate F S u f) w
    rw [he, ht, mul_left_comm]
  change sLocalLaurentCircleCoeff F S μ ω c R h.choose_spec.1 h.choose_spec.2 k
    (sLocalBruhatLeftTranslate F S u f) = _
  rw [sLocalLaurentCircleCoeff_apply, laurentCircle_eq_taylor_of_cleared h.choose_spec.1 _ _ N k
    (fun w hw ↦ ((hW w).mul (hg w hw)).differentiableAt.differentiableWithinAt) hEq, ite_eq_left hk]
  let n := N - k
  have hGc := hg c (Metric.mem_closedBall_self h.choose_spec.1.le)
  have hcoeff (j : ℕ) (hj : j ≤ n) : sLocalLaurentCoeff F S μ ω c (k+j) f =
      iteratedDeriv (n - j) G c / ((n - j).factorial : ℂ) := by
    change sLocalLaurentCircleCoeff F S μ ω c R h.choose_spec.1 h.choose_spec.2 (k+j) f = _
    rw [sLocalLaurentCircleCoeff_eq_taylor, ite_eq_left (show k + j ≤ N by omega),
      show N - (k + j) = n - j by omega]
  change iteratedDeriv n (W * G) c / (n.factorial : ℂ) =
    W c * ∑ j ∈ Finset.range (n+1), a^j / (j.factorial : ℂ) * sLocalLaurentCoeff F S μ ω c (k+j) f
  rw [iteratedDeriv_mul (hW c).contDiffAt hGc.contDiffAt, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hfac (i : ℕ) : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hn : ((n.choose j : ℕ) : ℂ) * (j.factorial : ℂ) * ((n-j).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  rw [hWd, hcoeff j hj']
  rw [← hn]
  have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  field_simp [hc, hfac j, hfac (n-j)]
  ring

/-- The top permitted coefficient is an eigendistribution for the full
S-idelic action. -/
theorem sLocalLaurentCoeff_top_translate [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
    (ω : PontryaginDual (K F S)) (c : ℂ) (u : (SAdeles F S)ˣ) (f : E F S) :
    let N := sLocalAllowedPoleOrder F S ω c
    sLocalLaurentCoeff F S μ ω c N (sLocalBruhatLeftTranslate F S u f) =
      sLocalZetaWeight F S ω c (QuotientGroup.mk u) * sLocalLaurentCoeff F S μ ω c N f := by
  intro N
  simpa only [show sLocalAllowedPoleOrder F S ω c = N from rfl, Nat.sub_self, zero_add,
    Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, add_zero]
    using sLocalLaurentCoeff_translate F S μ ω c N (le_refl N) u f

/-- When the radial coordinate vanishes, every coefficient transforms by
the prescribed character. -/
theorem sLocalLaurentCoeff_normOne_translate [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
    (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) (u : (SAdeles F S)ˣ)
    (hu : ((sLocalZetaSplit F S).symm (QuotientGroup.mk u)).1 = 0) (f : E F S) :
    sLocalLaurentCoeff F S μ ω c k (sLocalBruhatLeftTranslate F S u f) =
      (ω ((sLocalZetaSplit F S).symm (QuotientGroup.mk u)).2 : ℂ) *
        sLocalLaurentCoeff F S μ ω c k f := by
  let N := sLocalAllowedPoleOrder F S ω c
  by_cases hk : k ≤ N
  · have he := sLocalLaurentCoeff_translate F S μ ω c k hk u f
    dsimp only at he
    rw [he]
    simp only [sLocalZetaWeight, hu, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [zero_pow hj]
    · intro ha
      exact (ha (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim
  · have hz (g : E F S) : sLocalLaurentCoeff F S μ ω c k g = 0 := by
      have ho : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω g) c := by
        rw [← sLocalEulerFactor_order F S ω c]
        exact sLocalZeta_poleOrder_le_euler F S μ ω g c
      exact (sLocalLaurentCoeff_vanish_iff F S μ ω c N g).mpr ho k (by omega)
    rw [hz, hz, mul_zero]

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [MeasurableSpace (ArchUnits F)] [BorelSpace (ArchUnits F)]
  (ν : Measure (K F S)) [ν.IsHaarMeasure]

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ)
  Measure.count (sLocalClassHaar F S ν))

set_option maxHeartbeats 1600000 in
/-- Laurent contours descend to the actual S-local homogeneous theta quotient. -/
def sLocalThetaLaurentCircleCoeff (ω : PontryaginDual (K F S)) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω)
    (k : ℕ) : StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω) := by
  let f := sLocalLaurentCircleCoeff F S μ ω c R hR hD k
  apply (sLocalHomogeneousThetaKernel F S ν ω).liftQL f
  intro x hx
  change f x = 0
  have hz : sLocalContinuedMellinComponent F S μ ω x = 0 := by
    have he := map_zero (sLocalHomogeneousContinuedMellin F S μ ν hν ω)
    rw [← (Submodule.Quotient.mk_eq_zero _).mpr hx] at he
    exact he
  change laurentCircleFunctional c R hR k
    (sLocalMellinCompact F S μ ω (Metric.sphere c R) (isCompact_sphere c R)
      (sphere_subset_sLocalMellinRegular F S ω c hR hD) x) = 0
  have he : sLocalMellinCompact F S μ ω (Metric.sphere c R) (isCompact_sphere c R)
      (sphere_subset_sLocalMellinRegular F S ω c hR hD) x = 0 := by
    apply ContinuousMap.ext
    intro w
    rw [sLocalMellinCompact_apply, ContinuousMap.zero_apply]
    have hw := congrArg (fun g : C(sLocalMellinRegularSet F S ω, ℂ) ↦
      g ⟨w.val, sphere_subset_sLocalMellinRegular F S ω c hR hD w.property⟩) hz
    simpa only [sLocalContinuedMellinComponent_apply, ContinuousMap.zero_apply] using hw
  rw [he, map_zero]

@[simp] theorem sLocalThetaLaurentCircleCoeff_mk (ω : PontryaginDual (K F S)) (c : ℂ)
    (R : ℝ) (hR : 0 < R) (hD : Metric.closedBall c R \ {c} ⊆ sLocalMellinRegularSet F S ω)
    (k : ℕ) (f : E F S) :
    sLocalThetaLaurentCircleCoeff F S μ ν hν ω c R hR hD k (Submodule.Quotient.mk f) =
      sLocalLaurentCircleCoeff F S μ ω c R hR hD k f := rfl

/-- The coefficient at exponent `-k` on the actual homogeneous theta quotient. -/
def sLocalThetaLaurentCoeff (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) :
    StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω) :=
  let h := exists_sLocalMellinLaurentDisk F S ω c
  sLocalThetaLaurentCircleCoeff F S μ ν hν ω c h.choose h.choose_spec.1 h.choose_spec.2 k

@[simp] theorem sLocalThetaLaurentCoeff_mk (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) (f : E F S) :
    sLocalThetaLaurentCoeff F S μ ν hν ω c k (Submodule.Quotient.mk f) =
      sLocalLaurentCoeff F S μ ω c k f := rfl

/-- The coefficient first descends through the ordinary theta quotient
and then through the quotient for its prescribed character. -/
def sLocalOrdinaryThetaLaurentCoeff (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) :
    StrongDual ℂ (SLocalThetaQuotient F S) :=
  (sLocalThetaLaurentCoeff F S μ ν hν ω c k).comp (sLocalThetaToComponent F S ν ω)

@[simp] theorem sLocalOrdinaryThetaLaurentCoeff_mk (ω : PontryaginDual (K F S))
    (c : ℂ) (k : ℕ) (f : E F S) :
    sLocalOrdinaryThetaLaurentCoeff F S μ ν hν ω c k (Submodule.Quotient.mk f) =
      sLocalLaurentCoeff F S μ ω c k f := rfl

/-- The subspace with the specified bound on every pole of this component. -/
def sLocalThetaPoleBound (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    Submodule ℂ (SLocalHomogeneousThetaQuotient F S ν ω) :=
  ⨅ i : {p : ℂ × ℕ // m p.1 < p.2}, (sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2).ker

theorem mem_sLocalThetaPoleBound_mk (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) (f : E F S) :
    (Submodule.Quotient.mk f : SLocalHomogeneousThetaQuotient F S ν ω) ∈
      sLocalThetaPoleBound F S μ ν hν ω m ↔
      ∀ c, ((-(m c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
  simp only [sLocalThetaPoleBound, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h c
    exact (sLocalLaurentCoeff_vanish_iff F S μ ω c (m c) f).mp
      (fun k hk ↦ h ⟨(c, k), hk⟩)
  · intro h i
    exact (sLocalLaurentCoeff_vanish_iff F S μ ω i.val.1 (m i.val.1) f).mpr
      (h i.val.1) i.val.2 i.property

theorem sLocalThetaPoleBound_isClosed (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    IsClosed (sLocalThetaPoleBound F S μ ν hν ω m :
      Set (SLocalHomogeneousThetaQuotient F S ν ω)) := by
  rw [show (sLocalThetaPoleBound F S μ ν hν ω m :
      Set (SLocalHomogeneousThetaQuotient F S ν ω)) =
    ⋂ i : {p : ℂ × ℕ // m p.1 < p.2}, {q |
      sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2 q = 0} by
      ext q
      simp [sLocalThetaPoleBound, LinearMap.mem_ker]]
  exact isClosed_iInter fun i ↦
    isClosed_eq (sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2).continuous continuous_const

set_option maxHeartbeats 1600000 in
/-- The coefficients above the prescribed bound strongly generate the
annihilator of the corresponding pole subspace. -/
theorem sLocalThetaPoleBound_strongClosure (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    closure (Submodule.span ℂ (range fun i : {p : ℂ × ℕ // m p.1 < p.2} ↦
      sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2) :
      Set (StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω))) =
      {L | ∀ q ∈ sLocalThetaPoleBound F S μ ν hν ω m, L q = 0} := by
  let Q := SLocalHomogeneousThetaQuotient F S ν ω
  obtain ⟨hN, hC, _⟩ := sLocalHomogeneousTheta_primalStructure F S ν ω
  letI : T2Space Q := hN.1
  letI : PolynormableSpace ℂ Q := hN.2.1
  letI : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  letI : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Q := hC
  letI : BarrelledSpace ℂ Q := (sLocalHomogeneousTheta_barrelled F S ν ω).1
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear hN
  apply strongDual_closure_span_eq_annihilator e he
  intro q
  simp [sLocalThetaPoleBound, LinearMap.mem_ker]

/-- Only centers on the allowed Euler pole divisor are needed to generate
the strong annihilator. -/
theorem sLocalThetaPoleBound_strongClosure_at_poles (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    closure (Submodule.span ℂ (range fun i : {p : ℂ × ℕ //
      m p.1 < p.2 ∧ 0 < sLocalAllowedPoleOrder F S ω p.1} ↦
      sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2) :
      Set (StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω))) =
      {L | ∀ q ∈ sLocalThetaPoleBound F S μ ν hν ω m, L q = 0} := by
  let A : Submodule ℂ (StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω)) :=
    Submodule.span ℂ (range fun i : {p : ℂ × ℕ // m p.1 < p.2} ↦
      sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2)
  let B : Submodule ℂ (StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω)) :=
    Submodule.span ℂ (range fun i : {p : ℂ × ℕ //
      m p.1 < p.2 ∧ 0 < sLocalAllowedPoleOrder F S ω p.1} ↦
      sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2)
  have he : B = A := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨⟨i.val, i.property.1⟩, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases h : 0 < sLocalAllowedPoleOrder F S ω i.val.1
      · exact Submodule.subset_span ⟨⟨i.val, i.property, h⟩, rfl⟩
      · have hz : sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2 = 0 := by
          apply ContinuousLinearMap.ext
          intro q
          obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
          rw [sLocalThetaLaurentCoeff_mk, zero_apply]
          by_contra hn
          exact h (sLocalLaurentCoeff_ne_zero_imp_order F S μ ω i.val.1
            (Nat.zero_le (m i.val.1) |>.trans_lt i.property) f hn).2
        change sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2 ∈ B
        rw [hz]
        exact B.zero_mem
  change closure (B : Set (StrongDual ℂ (SLocalHomogeneousThetaQuotient F S ν ω))) = _
  rw [he]
  exact sLocalThetaPoleBound_strongClosure F S μ ν hν ω m

end

end Masullo
