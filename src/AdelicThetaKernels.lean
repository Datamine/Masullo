import AdelicZetaContinuation
import CompactCharacterCompleteness
import Mathlib.Analysis.Fourier.Inversion

open Filter Function MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Q := IdeleClass F
private abbrev G := Idele F
private abbrev ray (t : ℝ) : Q F := ideleClassExpSection F (Multiplicative.ofAdd t)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (G F) := borel _

private theorem canonical_radial (ν : Measure (K F)) (f : GlobalBruhat F)
    (ω : PontryaginDual (K F)) (z : ℂ) (t : ℝ) :
    globalRadialZetaIntegrand F ν f (compactIdeleClassCharacter F ω)
      (compactIdeleClassCharacter_unitary F ω) z (ideleClassExpSection F) t =
        Complex.exp (z * (t : ℂ)) * adelicHomogeneousTheta F ν ω
          (GlobalBruhat.algebraicEquiv F f).val (ray F t) := by
  rw [globalRadialZetaIntegrand_canonical, compactIdeleClassCharacter_apply_ray,
    normOnePontryaginCharacter_compactIdeleClassCharacter, one_mul]

private theorem canonical_continued_eq_radial
    (ν : Measure (K F)) [ν.IsHaarMeasure] (f : GlobalBruhat F)
    (ω : PontryaginDual (K F)) (z : ℂ) (hz : 1 < z.re) :
    globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z =
      ∫ t : ℝ, Complex.exp (z * (t : ℂ)) * adelicHomogeneousTheta F ν ω
        (GlobalBruhat.algebraicEquiv F f).val (ray F t) := by
  have he := globalRadialZeta_eq_continued F ν f (compactIdeleClassCharacter F ω)
    (compactIdeleClassCharacter_unitary F ω) (κ := 0) Complex.zero_re
    (fun t => by simp) (ideleClassExpSection F) (fun t => ideleClassNorm_expSection F _) z (Or.inl hz)
  rw [← he]
  exact integral_congr_ae (.of_forall (canonical_radial F ν f ω z))

/-- The homogeneous theta kernel is detected by the continued zeta
transform on any one vertical line in its half-plane of absolute convergence. -/
theorem adelicHomogeneousTheta_zero_iff_verticalZeta (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (ω : PontryaginDual (K F)) (σ : ℝ) (hσ : 1 < σ) :
    (∀ q, adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q = 0) ↔
      ∀ y : ℝ, globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0
        ((σ : ℂ) + (y : ℂ) * Complex.I) = 0 := by
  let Θ := adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val
  have hz (y : ℝ) : 1 < ((σ : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hσ
  constructor
  · intro h y
    rw [canonical_continued_eq_radial F ν f ω _ (hz y)]
    simp [h]
  · intro h
    let R (t : ℝ) := Complex.exp ((σ : ℂ) * (t : ℂ)) * Θ (ray F t)
    have hI : Integrable R := by
      have hi := globalRadialZeta_integrable F ν f (compactIdeleClassCharacter F ω)
        (compactIdeleClassCharacter_unitary F ω) (σ : ℂ) (ideleClassExpSection F)
        (fun _ => ideleClassNorm_expSection F _) (Or.inl (by simpa using hσ))
      exact hi.congr (.of_forall (canonical_radial F ν f ω (σ : ℂ)))
    have hC : Continuous R :=
      (by fun_prop : Continuous (fun t : ℝ => Complex.exp ((σ : ℂ) * (t : ℂ)))).mul
        ((adelicHomogeneousTheta_continuous F ν ω (GlobalBruhat.algebraicEquiv F f).property).comp
          ((ideleClassExpSection_continuous F).comp continuous_ofAdd))
    have hF : 𝓕 R = 0 := by
      funext y
      let b := -2 * Real.pi * y
      let z := (σ : ℂ) + (b : ℂ) * Complex.I
      have hZ := h b
      rw [canonical_continued_eq_radial F ν f ω z (hz b)] at hZ
      change 𝓕 R y = 0
      rw [← hZ, Real.fourier_eq']
      apply integral_congr_ae (.of_forall fun t => ?_)
      simp only [R, RCLike.inner_apply, conj_trivial, smul_eq_mul]
      change Complex.exp ((↑(-2 * Real.pi * (y * t)) : ℂ) * Complex.I) *
        (Complex.exp ((σ : ℂ) * (t : ℂ)) * Θ (ray F t)) =
          Complex.exp (z * (t : ℂ)) * Θ (ray F t)
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      simp only [z, b, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
      ring
    have hinv := hC.fourierInv_fourier_eq hI (hF ▸ integrable_zero _ _ _)
    have hr (t : ℝ) : Θ (ray F t) = 0 := by
      have ht := congrFun hinv t
      rw [hF, Real.fourierInv_eq'] at ht
      have ht' : R t = 0 := by
        simpa only [Pi.zero_apply, smul_zero, integral_zero] using ht.symm
      exact (mul_eq_zero.mp ht').resolve_left (Complex.exp_ne_zero _)
    intro q
    obtain ⟨⟨t, k⟩, rfl⟩ := (ideleClassLogCoordinates F).surjective q
    change Θ (k.val * ray F t) = 0
    rw [show Θ (k.val * ray F t) = (ω k : ℂ)⁻¹ * Θ (ray F t) from
      adelicHomogeneousTheta_translate F ν ω _ k (ray F t), hr t, mul_zero]

/-- A continued component vanishing on the initial half-plane vanishes
everywhere, with analytic values also at its possible poles. -/
theorem globalZetaContinued_zero_of_halfPlane (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (ω : PontryaginDual (K F))
    (hzero : ∀ z : ℂ, 1 < z.re →
      globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z = 0) :
    ∀ z, globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z = 0 := by
  let χ := compactIdeleClassCharacter F ω
  let Z := globalZetaContinued F ν f χ 0
  have hχ : IsUnitary F χ := compactIdeleClassCharacter_unitary F ω
  have hm := globalZetaContinued_meromorphic F ν f χ hχ 0
  have ht : meromorphicOrderAt Z (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hU : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with z hz
    exact hzero z hz
  have htop (z : ℂ) : meromorphicOrderAt Z z = ⊤ := by
    by_contra hne
    exact (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ z) (mem_univ (2 : ℂ)) hne) ht
  have hAna (z : ℂ) : AnalyticAt ℂ Z z := by
    have hp := globalZetaContinued_pole_order F ν f χ hχ 0
    let a := ∫ k : K F, (χ k.val : ℂ) ∂ν
    let u := (GlobalBruhat.algebraicEquiv F f).val
    let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
    rcases eq_or_ne z 0 with rfl | hz0
    · have hp0 : if a * u 0 = 0 then AnalyticAt ℂ Z 0
            else meromorphicOrderAt Z 0 = (-1 : ℤ) := by
        simpa only [neg_zero] using hp.1
      split_ifs at hp0 with hh
      · exact hp0
      · rw [htop 0] at hp0
        exact (WithTop.top_ne_coe hp0).elim
    rcases eq_or_ne z 1 with rfl | hz1
    · have hp1 : if a * v 0 = 0 then AnalyticAt ℂ Z 1
            else meromorphicOrderAt Z 1 = (-1 : ℤ) := by
        simpa only [sub_zero] using hp.2
      split_ifs at hp1 with hh
      · exact hp1
      · rw [htop 1] at hp1
        exact (WithTop.top_ne_coe hp1).elim
    · exact globalZetaContinued_analyticAt F ν f χ hχ 0 z
        (by simpa using hz0) (by simpa using sub_ne_zero.mpr hz1)
  intro z
  have hn : Z =ᶠ[𝓝[≠] z] (fun _ => 0) := meromorphicOrderAt_eq_top_iff.mp (htop z)
  exact (((hAna z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp hn).eq_of_nhds

/-- The isotypic kernel in Lemma 5.1.2.1(2), including the full
meromorphically continued character component. -/
theorem adelicHomogeneousTheta_zero_iff_continuedZeta (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (ω : PontryaginDual (K F)) :
    (∀ q, adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q = 0) ↔
      ∀ z : ℂ, globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z = 0 := by
  constructor
  · intro h
    apply globalZetaContinued_zero_of_halfPlane F ν f ω
    intro z hz
    rw [canonical_continued_eq_radial F ν f ω z hz]
    simp [h]
  · intro h
    exact (adelicHomogeneousTheta_zero_iff_verticalZeta F ν f ω 2 (by norm_num)).2 (fun y => h _)

/-- Compact Fourier completeness recovers ordinary theta from its
homogeneous projections. -/
theorem adelicTheta_zero_iff_homogeneous_zero (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) :
    (∀ q, adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q = 0) ↔
      ∀ (ω : PontryaginDual (K F)) q,
        adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q = 0 := by
  let u := GlobalBruhat.algebraicEquiv F f
  constructor
  · intro h ω q
    simp [adelicHomogeneousTheta, h]
  · intro h q
    letI : T1Space (Q F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
    letI : T2Space (K F) := inferInstance
    letI : ν.Regular := normOneIdeleClass_haar_regular F ν
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    let g (k : K F) := adelicTheta F u.val (k.val * q)
    have hg : Continuous g :=
      (adelicTheta_continuous F (bruhat_theta_continuous_and_invariant u.property).1).comp
        (show Continuous (fun k : K F => k.val * q) from
          continuous_subtype_val.mul (continuous_const (y := q)))
    have hZ (ω : PontryaginDual (K F)) : ∫ k, star (ω k : ℂ) * g k ∂ν = 0 := by
      have he : (fun k => star (ω k : ℂ) * g k) = fun k => (ω⁻¹ k : ℂ) * g k := by
        funext k
        exact congrArg (· * g k) (Circle.coe_inv_eq_conj (ω k)).symm
      rw [he]
      exact h ω⁻¹ q
    have hae := ae_eq_zero_of_character_integral_eq_zero ν
      (hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hZ
    have h1 : g 1 = (0 : ℂ) := congrFun ((hg.ae_eq_iff_eq ν continuous_const).mp hae) 1
    change adelicTheta F u.val ((1 : Q F) * q) = 0 at h1
    have he : (1 : Q F) * q = q := one_mul q
    exact (congrArg (adelicTheta F u.val) he).symm.trans h1

/-- The ordinary theta and continued zeta kernels coincide, as in
Lemma 5.1.2.1(1). -/
theorem adelicTheta_zero_iff_continuedZeta (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) :
    (∀ q, adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q = 0) ↔
      ∀ (ω : PontryaginDual (K F)) (z : ℂ),
        globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z = 0 := by
  rw [adelicTheta_zero_iff_homogeneous_zero F ν f]
  exact forall_congr' (adelicHomogeneousTheta_zero_iff_continuedZeta F ν f)

/-- The kernel of the continued zeta component as a genuine test subspace.
It is presented by the continuous idelic functionals on one vertical line. -/
def globalIdelicZetaComponentKernel (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (K F)) : Submodule ℂ (GlobalBruhat F) :=
  ⨅ y : ℝ, (idelicZetaCLM F μ (compactIdeleClassCharacter F ω)
    (compactIdeleClassCharacter_unitary F ω) (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) (by norm_num)).ker

/-- The ordinary kernel over the entire quasi-character space. -/
def globalIdelicZetaKernel (μ : Measure (G F)) [μ.IsHaarMeasure] :
    Submodule ℂ (GlobalBruhat F) :=
  ⨅ ω : PontryaginDual (K F), globalIdelicZetaComponentKernel F μ ω

theorem mem_globalIdelicZetaComponentKernel (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (ω : PontryaginDual (K F)) (f : GlobalBruhat F) :
    f ∈ globalIdelicZetaComponentKernel F μ ω ↔
      ∀ z : ℂ, globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0 z = 0 := by
  let χ := compactIdeleClassCharacter F ω
  let hχ := compactIdeleClassCharacter_unitary F ω
  have h (y : ℝ) : 1 < (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I).re := by norm_num
  have he (y : ℝ) :
      globalZetaContinued F ν f χ 0 (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        idelicZetaCLM F μ χ hχ (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) (h y) f := by
    rw [idelicZetaCLM_apply]
    exact globalZetaContinued_eq_idelic F μ ν hν f χ hχ Complex.zero_re
      (fun t => by simp [χ]) _ (h y)
  simp only [globalIdelicZetaComponentKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  have hline : (∀ y : ℝ, idelicZetaCLM F μ χ hχ (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) (h y) f = 0) ↔
      ∀ y : ℝ, globalZetaContinued F ν f χ 0 (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0 :=
    forall_congr' fun y => Iff.of_eq (congrArg (· = 0) (he y).symm)
  change (∀ y : ℝ, idelicZetaCLM F μ χ hχ (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) (h y) f = 0) ↔ _
  exact hline.trans ((adelicHomogeneousTheta_zero_iff_verticalZeta F ν f ω 2
    (by norm_num)).symm.trans (adelicHomogeneousTheta_zero_iff_continuedZeta F ν f ω))

/-- Both isotypic and ordinary kernels in Lemma 5.1.2.1 are equalities
on the actual test subspaces. -/
theorem globalIdelicZetaKernels_eq_theta (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) μ Measure.count (globalClassMeasure F ν))
    (f : GlobalBruhat F) :
    ((f ∈ globalIdelicZetaKernel F μ) ↔
      ∀ q, adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q = 0) ∧
    ∀ ω : PontryaginDual (K F), (f ∈ globalIdelicZetaComponentKernel F μ ω) ↔
      ∀ q, adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q = 0 := by
  have hω (ω : PontryaginDual (K F)) :=
    (mem_globalIdelicZetaComponentKernel F μ ν hν ω f).trans
      (adelicHomogeneousTheta_zero_iff_continuedZeta F ν f ω).symm
  refine ⟨?_, hω⟩
  rw [globalIdelicZetaKernel, Submodule.mem_iInf]
  exact (forall_congr' hω).trans (adelicTheta_zero_iff_homogeneous_zero F ν f).symm

end

end Masullo
