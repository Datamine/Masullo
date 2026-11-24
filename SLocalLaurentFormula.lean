import SLocalLaurentCoefficients
import SLocalEulerPoles
import SLocalPrincipalZeta

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- The normalized Taylor coefficient of an analytic germ. -/
def taylorCoeff (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial : ℂ)

theorem taylorCoeff_congr {f g : ℂ → ℂ} {c : ℂ}
    (h : f =ᶠ[𝓝 c] g) (n : ℕ) : taylorCoeff f c n = taylorCoeff g c n := by
  unfold taylorCoeff
  rw [h.iteratedDeriv_eq n]

@[simp] theorem taylorCoeff_zero (f : ℂ → ℂ) (c : ℂ) : taylorCoeff f c 0 = f c := by
  simp [taylorCoeff]

theorem taylorCoeff_mul {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) (n : ℕ) :
    taylorCoeff (f * g) c n =
      ∑ j ∈ Finset.range (n+1), taylorCoeff f c j * taylorCoeff g c (n-j) := by
  unfold taylorCoeff
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hfac (i : ℕ) : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hle).ne'
  have hn : (n.choose j : ℂ) * (j.factorial : ℂ) * ((n-j).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  rw [← hn]
  field_simp [hc, hfac j, hfac (n-j)]

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S

/-- The number of simple local Euler poles is the allowed Laurent order. -/
theorem sLocalAllowedPoleOrder_eq_count (ω : PontryaginDual (K F S)) (c : ℂ) :
    sLocalAllowedPoleOrder F S ω c = sLocalPoleCount F S ω c := by
  obtain ⟨U, hU, hUnz, he, _⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω c
  have h := (sLocalEulerDenominator_analytic F S ω c).analyticOrderAt_eq_natCast.mpr
    ⟨U, hU, hUnz, he⟩
  unfold sLocalAllowedPoleOrder
  rw [h, ENat.toNat_natCast]

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

/-- The entire numerator of the actual continued zeta transform. -/
def sLocalEulerNormalizedMellin (ω : PontryaginDual (K F S)) (f : E F S) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z ↦ sLocalEulerDenominator F S ω z * Z F S μ ω f z) univ

theorem sLocalEulerNormalizedMellin_entire (ω : PontryaginDual (K F S)) (f : E F S) :
    AnalyticOnNhd ℂ (sLocalEulerNormalizedMellin F S μ ω f) univ :=
  sLocalEulerDenominator_mul_zeta_entire F S μ ω f

theorem sLocalEulerNormalizedMellin_eq_germ (ω : PontryaginDual (K F S)) (f : E F S) (c : ℂ) :
    sLocalEulerNormalizedMellin F S μ ω f =ᶠ[𝓝[≠] c]
      fun w ↦ sLocalEulerDenominator F S ω w * Z F S μ ω f w :=
  (show MeromorphicOn (fun w ↦ sLocalEulerDenominator F S ω w * Z F S μ ω f w) univ from
    fun w _ ↦ (sLocalEulerDenominator_analytic F S ω w).meromorphicAt.mul
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f w)).toMeromorphicNFOn_eq_self_on_nhdsNE
        (mem_univ c)

set_option maxHeartbeats 1800000 in
/-- If the denominator is written as a power times a local analytic unit,
the Laurent coefficients are the Taylor coefficients of the normalized
Mellin transform divided by that unit. -/
theorem sLocalLaurentCoeff_eq_taylor_div_unit (ω : PontryaginDual (K F S))
    (f : E F S) (c : ℂ) (k : ℕ) (U : ℂ → ℂ) (hU : AnalyticAt ℂ U c) (hUne : U c ≠ 0)
    (he : sLocalEulerDenominator F S ω =ᶠ[𝓝 c]
      fun z ↦ (z - c) ^ sLocalAllowedPoleOrder F S ω c * U z) :
    let N := sLocalAllowedPoleOrder F S ω c
    sLocalLaurentCoeff F S μ ω c k f =
      if k ≤ N then taylorCoeff (U⁻¹ * sLocalEulerNormalizedMellin F S μ ω f) c (N-k) else 0 := by
  intro N
  let H := sLocalEulerNormalizedMellin F S μ ω f
  let P (w : ℂ) := (w - c)^N * Z F S μ ω f w
  let G := toMeromorphicNFOn P univ
  have hp : MeromorphicOn P univ := fun w _ ↦
    (((analyticAt_id.sub (analyticAt_const (v := c))).pow N).meromorphicAt.mul
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f w))
  have hH : AnalyticAt ℂ H c := sLocalEulerNormalizedMellin_entire F S μ ω f c trivial
  have hProd : AnalyticAt ℂ (U⁻¹ * H) c := (hU.inv hUne).mul hH
  have hG : G =ᶠ[𝓝[≠] c] U⁻¹ * H := by
    filter_upwards [hp.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ c),
      sLocalEulerNormalizedMellin_eq_germ F S μ ω f c, he.filter_mono nhdsWithin_le_nhds,
      (hU.continuousAt.eventually_ne hUne).filter_mono nhdsWithin_le_nhds] with w hw hHw hD hUw
    change G w = (U w)⁻¹ * H w
    change G w = P w at hw
    change H w = _ at hHw
    rw [hw, hHw, hD]
    change (w - c)^N * Z F S μ ω f w =
      (U w)⁻¹ * (((w - c)^N * U w) * Z F S μ ω f w)
    field_simp
  have hG' : G =ᶠ[𝓝 c] U⁻¹ * H :=
    ((meromorphicNFOn_toMeromorphicNFOn P univ (mem_univ c)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      hProd.meromorphicNFAt).mp hG
  let d := exists_sLocalMellinLaurentDisk F S ω c
  change sLocalLaurentCircleCoeff F S μ ω c d.choose d.choose_spec.1 d.choose_spec.2 k f = _
  rw [sLocalLaurentCircleCoeff_eq_taylor]
  change (if k ≤ N then taylorCoeff G c (N-k) else 0) = _
  rw [taylorCoeff_congr hG']

/-- The leading coefficient is the normalized Mellin value times the
product of the regular local Euler values and the residues of the singular
local Euler factors. The latter product is expressed by the reciprocal of
the product of the corresponding denominator values and derivatives. -/
theorem sLocalLaurentCoeff_top_localProduct (ω : PontryaginDual (K F S))
    (f : E F S) (c : ℂ) :
    sLocalLaurentCoeff F S μ ω c (sLocalPoleCount F S ω c) f =
      (sLocalEulerLeadingDenominator F S ω c)⁻¹ * sLocalEulerNormalizedMellin F S μ ω f c := by
  obtain ⟨U, hU, hUne, he, hu⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω c
  rw [← sLocalAllowedPoleOrder_eq_count F S ω c] at he ⊢
  rw [sLocalLaurentCoeff_eq_taylor_div_unit F S μ ω f c _ U hU hUne he,
    ite_eq_left (le_refl _), Nat.sub_self, taylorCoeff_zero]
  change (U c)⁻¹ * _ = _
  rw [hu]

/-- All Laurent coefficients up to the allowed order are the convolution
of the reciprocal local unit and the entire normalized Mellin transform. -/
theorem sLocalLaurentCoeff_localConvolution (ω : PontryaginDual (K F S))
    (f : E F S) (c : ℂ) (k : ℕ) (hk : k ≤ sLocalAllowedPoleOrder F S ω c)
    (U : ℂ → ℂ) (hU : AnalyticAt ℂ U c) (hUne : U c ≠ 0)
    (he : sLocalEulerDenominator F S ω =ᶠ[𝓝 c]
      fun z ↦ (z - c) ^ sLocalAllowedPoleOrder F S ω c * U z) :
    sLocalLaurentCoeff F S μ ω c k f =
      ∑ j ∈ Finset.range (sLocalAllowedPoleOrder F S ω c - k + 1),
        taylorCoeff U⁻¹ c j *
          taylorCoeff (sLocalEulerNormalizedMellin F S μ ω f) c
            (sLocalAllowedPoleOrder F S ω c - k - j) := by
  rw [sLocalLaurentCoeff_eq_taylor_div_unit F S μ ω f c k U hU hUne he, ite_eq_left hk]
  exact taylorCoeff_mul (hU.inv hUne) (sLocalEulerNormalizedMellin_entire F S μ ω f c trivial) _

/-- At a regular point the normalized Mellin value is the ordinary product
of the reciprocal Euler factor and the continued zeta value. -/
theorem normalizedMellin_eq_euler_mul_regular (ω : PontryaginDual (K F S))
    (f : E F S) (w : ℂ) (hw : w ∈ sLocalMellinRegularSet F S ω) :
    sLocalEulerNormalizedMellin F S μ ω f w =
      sLocalEulerDenominator F S ω w * Z F S μ ω f w := by
  have hg := (sLocalEulerNormalizedMellin_entire F S μ ω f w trivial).continuousAt
  have hZ := (sLocalProductZetaContinued_continuousOn_regular F S μ ω f w hw).continuousAt
    ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds hw)
  have hD := (sLocalEulerDenominator_analytic F S ω w).continuousAt
  exact ((hg.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hD.mul hZ)).mp
    (sLocalEulerNormalizedMellin_eq_germ F S μ ω f w)).eq_of_nhds

private theorem sLocalContinuedZeta_analyticAt_positive (ω : PontryaginDual (K F S))
    (f : E F S) (w : ℂ) (hw : 0 < w.re) : AnalyticAt ℂ (Z F S μ ω f) w := by
  have hD := sLocalEulerDenominator_ne_zero_of_pos F S ω hw
  have he : ∀ᶠ z in 𝓝 w, z ∈ sLocalMellinRegularSet F S ω := by
    filter_upwards [(sLocalEulerDenominator_analytic F S ω w).continuousAt.eventually_ne hD] with z hz
    rw [sLocalMellinRegularSet_iff_noEulerPole, ← not_lt, sLocalEulerFactor_order_lt_zero_iff]
    exact hz
  have hd : AnalyticAt ℂ
      (sLocalEulerNormalizedMellin F S μ ω f / sLocalEulerDenominator F S ω) w :=
    (sLocalEulerNormalizedMellin_entire F S μ ω f w trivial).div (sLocalEulerDenominator_analytic F S ω w) hD
  apply hd.congr
  filter_upwards [he, (sLocalEulerDenominator_analytic F S ω w).continuousAt.eventually_ne hD] with z hz hn
  have hf := normalizedMellin_eq_euler_mul_regular F S μ ω f z hz
  change sLocalEulerNormalizedMellin F S μ ω f z / sLocalEulerDenominator F S ω z =
    Z F S μ ω f z
  rw [hf, mul_comm, mul_div_cancel_right₀ _ hn]

/-- At a pole, the reflected functional equation implies the coefficient
formula. This takes the actual equation on punctured germs as a premise.
The leading Taylor term of the cleared Tate ratio retains the epsilon factor. -/
theorem sLocalLaurentCoeff_of_reflected_pair (ω : PontryaginDual (K F S)) (f g : E F S)
    (ε : ℂ → ℂ) (c : ℂ) (hc : sLocalEulerPoleLattices F S ω c)
    (hε : AnalyticAt ℂ ε c)
    (hFE : Z F S μ ω f =ᶠ[𝓝[≠] c] fun z =>
      sLocalExplicitTateFactor F S ω ε z * Z F S μ ω⁻¹ g (1-z)) :
    let N := sLocalPoleCount F S ω c
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V c ∧
      ((fun z ↦ (z-c)^N * sLocalExplicitTateFactor F S ω ε z) =ᶠ[𝓝[≠] c] V) ∧
      V c = ε c * sLocalEulerDenominator F S ω⁻¹ (1-c) / sLocalEulerLeadingDenominator F S ω c ∧
      ∀ k ≤ N, sLocalLaurentCoeff F S μ ω c k f =
        ∑ j ∈ Finset.range (N-k+1), taylorCoeff V c j *
          taylorCoeff (fun z ↦ Z F S μ ω⁻¹ g (1-z)) c (N-k-j) := by
  intro N
  obtain ⟨U, hU, hUne, he, hu⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω c
  have hN : sLocalAllowedPoleOrder F S ω c = N := sLocalAllowedPoleOrder_eq_count F S ω c
  let Dref (z : ℂ) := sLocalEulerDenominator F S ω⁻¹ (1-z)
  let Zref (z : ℂ) := Z F S μ ω⁻¹ g (1-z)
  let V := U⁻¹ * (ε * Dref)
  have hDref : AnalyticAt ℂ Dref c :=
    (sLocalEulerDenominator_analytic F S ω⁻¹ (1-c)).comp
      (f := fun w : ℂ ↦ 1-w) (analyticAt_const.sub analyticAt_id)
  have hV : AnalyticAt ℂ V c := (hU.inv hUne).mul (hε.mul hDref)
  have hcRe : c.re ≤ 0 := by
    by_contra h
    exact (sLocalEulerDenominator_ne_zero_of_pos F S ω (lt_of_not_ge h))
      ((sLocalEulerDenominator_eq_zero_iff_lattices F S ω c).mpr hc)
  have hrefPos : 0 < (1-c).re := by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr (hcRe.trans_lt zero_lt_one)
  have hZref : AnalyticAt ℂ Zref c :=
    (sLocalContinuedZeta_analyticAt_positive F S μ ω⁻¹ g (1-c) hrefPos).comp
      (f := fun w : ℂ ↦ 1-w) (analyticAt_const.sub analyticAt_id)
  have hClear : (fun z ↦ (z-c)^N * sLocalExplicitTateFactor F S ω ε z) =ᶠ[𝓝[≠] c] V := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      (hU.continuousAt.eventually_ne hUne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hUne' hwc
    have hn : w - c ≠ 0 := sub_ne_zero.mpr hwc
    change (w-c)^N * (ε w * (sLocalEulerDenominator F S ω w)⁻¹ * Dref w) =
      (U w)⁻¹ * (ε w * Dref w)
    rw [hw]
    field_simp
    ring
  have hGerm : (U⁻¹ * sLocalEulerNormalizedMellin F S μ ω f) =ᶠ[𝓝 c] (V * Zref) := by
    have hL := (hU.inv hUne).mul (sLocalEulerNormalizedMellin_entire F S μ ω f c trivial)
    apply (hL.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hV.mul hZref).continuousAt).mp
    filter_upwards [sLocalEulerNormalizedMellin_eq_germ F S μ ω f c, he.filter_mono nhdsWithin_le_nhds,
      (hU.continuousAt.eventually_ne hUne).filter_mono nhdsWithin_le_nhds, hFE, hClear]
      with w hH hD hUw hZw hVw
    change (U w)⁻¹ * sLocalEulerNormalizedMellin F S μ ω f w = V w * Zref w
    change Z F S μ ω f w = sLocalExplicitTateFactor F S ω ε w * Zref w at hZw
    change (w-c)^N * sLocalExplicitTateFactor F S ω ε w = V w at hVw
    rw [hH, hD, hZw, ← hVw]
    field_simp
    ring
  refine ⟨V, hV, hClear, ?_, ?_⟩
  · change (U c)⁻¹ * (ε c * Dref c) = ε c * Dref c / sLocalEulerLeadingDenominator F S ω c
    rw [← hu, div_eq_mul_inv, mul_comm]
  · intro k hk
    have he' : sLocalEulerDenominator F S ω =ᶠ[𝓝 c]
        fun z ↦ (z - c) ^ sLocalAllowedPoleOrder F S ω c * U z := by rw [hN]; exact he
    rw [sLocalLaurentCoeff_eq_taylor_div_unit F S μ ω f c k U hU hUne he', hN, ite_eq_left hk,
      taylorCoeff_congr hGerm]
    exact taylorCoeff_mul hV hZref _

/-- At a pole, the reflected functional equation implies the coefficient
formula. This takes the actual equation on punctured germs as a premise.
The leading Taylor term of the cleared Tate ratio retains the epsilon factor. -/
theorem sLocalLaurentCoeff_of_reflection (ω : PontryaginDual (K F S)) (f : E F S)
    (hS : ∀ g ∈ E F S, GlobalBruhat.fourier F g ∈ E F S)
    (ε : ℂ → ℂ) (c : ℂ) (hc : sLocalEulerPoleLattices F S ω c)
    (hε : AnalyticAt ℂ ε c)
    (hFE : Z F S μ ω f =ᶠ[𝓝[≠] c] fun z =>
      sLocalExplicitTateFactor F S ω ε z * Z F S μ ω⁻¹ (sLocalStageFourier F S hS f) (1-z)) :
    let N := sLocalPoleCount F S ω c
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V c ∧
      ((fun z ↦ (z-c)^N * sLocalExplicitTateFactor F S ω ε z) =ᶠ[𝓝[≠] c] V) ∧
      V c = ε c * sLocalEulerDenominator F S ω⁻¹ (1-c) / sLocalEulerLeadingDenominator F S ω c ∧
      ∀ k ≤ N, sLocalLaurentCoeff F S μ ω c k f =
        ∑ j ∈ Finset.range (N-k+1), taylorCoeff V c j *
          taylorCoeff (fun z ↦ Z F S μ ω⁻¹ (sLocalStageFourier F S hS f) (1-z)) c (N-k-j) :=
  sLocalLaurentCoeff_of_reflected_pair F S μ ω f (sLocalStageFourier F S hS f) ε c hc hε hFE

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (ν : Measure (K F S)) [ν.IsHaarMeasure]

private abbrev productHaar :=
  sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ)
  Measure.count (sLocalClassHaar F S ν))

/-- The principal-part coefficients removed by imposing a prescribed
remaining pole bound. Coefficients beyond the Euler multiplicity are omitted. -/
def sLocalThetaRemovedLaurentCoefficients (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ]
      ({p : ℂ × ℕ // m p.1 < p.2 ∧ p.2 ≤ sLocalPoleCount F S ω p.1} → ℂ) :=
  ContinuousLinearMap.pi fun i ↦
    sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2

set_option maxHeartbeats 1500000 in
/-- The space retaining a prescribed pole bound is exactly the kernel of
the finite-at-each-pole coefficient deletion map. -/
theorem sLocalThetaRemovedLaurentCoefficients_ker (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    (sLocalThetaRemovedLaurentCoefficients F S μ ν hν ω m).ker =
      sLocalThetaPoleBound F S μ ν hν ω m := by
  let A := sLocalThetaRemovedLaurentCoefficients F S μ ν hν ω m
  let Q := SLocalHomogeneousThetaQuotient F S ν ω
  change A.ker = sLocalThetaPoleBound F S μ ν hν ω m
  apply Submodule.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let x : Q := Submodule.Quotient.mk f
  change x ∈ A.ker ↔ x ∈ sLocalThetaPoleBound F S μ ν hν ω m
  rw [mem_sLocalThetaPoleBound_mk]
  constructor
  · intro h c
    have h0 : A x = 0 := h
    apply (sLocalLaurentCoeff_vanish_iff F S μ ω c (m c) f).mp
    intro k hk
    by_cases hle : k ≤ sLocalPoleCount F S ω c
    · let i : {p : ℂ × ℕ // m p.1 < p.2 ∧ p.2 ≤ sLocalPoleCount F S ω p.1} :=
        ⟨(c,k), hk, hle⟩
      have hi := congrFun h0 i
      exact hi
    · have hPo := sLocalZeta_poleOrder_le_euler F S μ ω f c
      rw [sLocalEulerFactor_order F S ω c, sLocalAllowedPoleOrder_eq_count F S ω c] at hPo
      exact (sLocalLaurentCoeff_vanish_iff F S μ ω c
        (sLocalPoleCount F S ω c) f).mpr hPo k (lt_of_not_ge hle)
  · intro h
    change A x = 0
    funext i
    exact (sLocalLaurentCoeff_vanish_iff F S μ ω i.val.1 (m i.val.1) f).mpr
      (h i.val.1) i.val.2 i.property.1

/-- The algebraically exact coefficient sequence has as its terminal
space the principal parts attained by the Mellin transform. -/
def sLocalThetaRemovedLaurentCoefficients_quotient (ω : PontryaginDual (K F S)) (m : ℂ → ℕ) :
    (SLocalHomogeneousThetaQuotient F S ν ω ⧸ sLocalThetaPoleBound F S μ ν hν ω m) ≃ₗ[ℂ]
      (sLocalThetaRemovedLaurentCoefficients F S μ ν hν ω m).range :=
  (Submodule.quotEquivOfEq _ _ (sLocalThetaRemovedLaurentCoefficients_ker F S μ ν hν ω m).symm).trans
    (sLocalThetaRemovedLaurentCoefficients F S μ ν hν ω m).toLinearMap.quotKerEquivRange

/-- Product of the actual Euler multipliers at the selected finite places. -/
def sLocalSelectedEulerMultiplier (ω : PontryaginDual (K F S)) (T : Finset S) (z : ℂ) : ℂ :=
  ∏ v ∈ T, finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) z

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem selectedFactor_analytic (ω : PontryaginDual (K F S)) (v : S) (z : ℂ) :
    AnalyticAt ℂ (finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v)) z := by
  classical
  let χ := sLocalFiniteZetaPhases F S ω v
  by_cases h : finiteZetaUnramified F v.val χ
  · have he : finiteZetaWeilMultiplier F v.val χ = finiteZetaDenominator F v.val χ := by
      funext w
      exact ite_eq_left h
    rw [he]
    exact finiteZetaDenominator_analytic F v.val χ z
  · have he : finiteZetaWeilMultiplier F v.val χ = fun _ ↦ (1 : ℂ) := by
      funext w
      exact ite_eq_right h
    rw [he]
    exact analyticAt_const

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem selectedFactor_simple (ω : PontryaginDual (K F S)) (v : S) (z : ℂ)
    (hz : finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) z = 0) :
    analyticOrderAt (finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v)) z = 1 := by
  classical
  let χ := sLocalFiniteZetaPhases F S ω v
  by_cases h : finiteZetaUnramified F v.val χ
  · have he : finiteZetaWeilMultiplier F v.val χ = finiteZetaDenominator F v.val χ := by
      funext w
      exact ite_eq_left h
    change finiteZetaWeilMultiplier F v.val χ z = 0 at hz
    rw [he] at hz
    change analyticOrderAt (finiteZetaWeilMultiplier F v.val χ) z = 1
    rw [he]
    exact finiteZetaDenominator_simple_zero F v.val χ z hz
  · exact (one_ne_zero (show (1 : ℂ) = 0 from (ite_eq_right h).symm.trans hz)).elim

include hν in
theorem sLocalWeilPrincipalValues_continued_pos (ω : PontryaginDual (K F S)) (T : Finset S)
    [(productHaar F S μ).IsHaarMeasure] (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    Z F S μ ω (sLocalWeilPrincipalValues F S T f) z =
      sLocalSelectedEulerMultiplier F S ω T z * Z F S μ ω f z := by
  induction T using Finset.induction_on generalizing f with
  | empty =>
    have hp : sLocalWeilPrincipalValues F S ∅ = 1 := rfl
    rw [hp, sLocalSelectedEulerMultiplier, Finset.prod_empty, one_mul]
    rfl
  | insert v T hT hIH =>
    have hp : sLocalWeilPrincipalValues F S (insert v T) =
        sLocalWeilPrincipalValue F S v * sLocalWeilPrincipalValues F S T :=
      Finset.noncommProd_insert_of_notMem T v _ _ hT
    rw [hp]
    change Z F S μ ω (sLocalWeilPrincipalValue F S v (sLocalWeilPrincipalValues F S T f)) z = _
    let g := sLocalWeilPrincipalValues F S T f
    have hg : Z F S μ ω g z = sLocalThetaZetaIntegral F S ν ω g z :=
      sLocalContinuedZeta_eq_theta F S μ ν hν ω g hz
    calc
      _ = sLocalThetaZetaIntegral F S ν ω (sLocalWeilPrincipalValue F S v g) z :=
        sLocalContinuedZeta_eq_theta F S μ ν hν ω _ hz
      _ = sLocalPrincipalZetaFactor F S ω z v * sLocalThetaZetaIntegral F S ν ω g z :=
        sLocalThetaZeta_weilPrincipalValue F S (productHaar F S μ) ν hν ω z v g hz
      _ = _ := by
        rw [← hg, sLocalPrincipalZetaFactor_eq_finiteZetaWeilMultiplier, hIH f]
        have hM : sLocalSelectedEulerMultiplier F S ω (insert v T) z =
            finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) z *
              sLocalSelectedEulerMultiplier F S ω T z := by
          unfold sLocalSelectedEulerMultiplier
          rw [Finset.prod_insert hT]
        rw [hM, mul_assoc]

include hν in
/-- The finite principal-value operator multiplies the entire continuation
as meromorphic germs by the selected Euler multipliers. -/
theorem sLocalWeilPrincipalValues_continued (ω : PontryaginDual (K F S)) (T : Finset S)
    (f : E F S) (c : ℂ) :
    Z F S μ ω (sLocalWeilPrincipalValues F S T f) =ᶠ[𝓝[≠] c]
      fun z ↦ sLocalSelectedEulerMultiplier F S ω T z * Z F S μ ω f z := by
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hA : Meromorphic (Z F S μ ω (sLocalWeilPrincipalValues F S T f)) :=
    sLocalProductZetaContinued_meromorphic F S μ ω _ _ _
  have hB : Meromorphic (fun z ↦ sLocalSelectedEulerMultiplier F S ω T z * Z F S μ ω f z) := by
    intro z
    have h : AnalyticAt ℂ (sLocalSelectedEulerMultiplier F S ω T) z :=
      T.analyticAt_fun_prod (fun v _ ↦ selectedFactor_analytic F S ω v z)
    exact h.meromorphicAt.mul (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f z)
  exact boundedPoleMellinSpace_unique_germs (isOpen_lt continuous_const Complex.continuous_re)
    ⟨1, by simp⟩ hA hB (fun z hz ↦ sLocalWeilPrincipalValues_continued_pos F S μ ν hν ω T f z hz) c

/-- The number of simple Euler poles removed by a selected finite product. -/
def sLocalSelectedFinitePoleCount (ω : PontryaginDual (K F S)) (T : Finset S) (c : ℂ) : ℕ :=
  (T.filter fun v ↦ finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v) c = 0).card

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The selected Euler multiplier vanishes to exactly the number of
selected local factors vanishing at the point. -/
theorem sLocalSelectedEulerMultiplier_order (ω : PontryaginDual (K F S)) (T : Finset S) (c : ℂ) :
    meromorphicOrderAt (sLocalSelectedEulerMultiplier F S ω T) c =
      (sLocalSelectedFinitePoleCount F S ω T c : WithTop ℤ) := by
  let P := sLocalSelectedEulerMultiplier F S ω T
  have hA : AnalyticAt ℂ P c :=
    T.analyticAt_fun_prod (fun v _ ↦ selectedFactor_analytic F S ω v c)
  obtain ⟨U, hU, hUne, he, _⟩ := analytic_finset_prod_factor_simpleZeros T
    (fun v ↦ finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v)) c
    (fun v _ ↦ selectedFactor_analytic F S ω v c) (fun v _ ↦ selectedFactor_simple F S ω v c)
  have hp := hA.analyticOrderAt_eq_natCast.mpr ⟨U, hU, hUne, he⟩
  rw [hA.meromorphicOrderAt_eq, hp, ENat.map_natCast]
  rfl

theorem sLocalSelectedEulerMultiplier_eventually_ne_zero
    (ω : PontryaginDual (K F S)) (T : Finset S) (c : ℂ) :
    ∀ᶠ z in 𝓝[≠] c, sLocalSelectedEulerMultiplier F S ω T z ≠ 0 := by
  have hA : AnalyticAt ℂ (sLocalSelectedEulerMultiplier F S ω T) c :=
    T.analyticAt_fun_prod (fun v _ ↦ selectedFactor_analytic F S ω v c)
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hA.meromorphicAt).mp
  rw [sLocalSelectedEulerMultiplier_order]
  exact WithTop.natCast_ne_top _

include hν in
/-- Finite principal values shift the meromorphic order by the number of
selected factors vanishing at the point. -/
theorem sLocalWeilPrincipalValues_order (ω : PontryaginDual (K F S)) (T : Finset S)
    (f : E F S) (c : ℂ) :
    meromorphicOrderAt (Z F S μ ω (sLocalWeilPrincipalValues F S T f)) c =
      (sLocalSelectedFinitePoleCount F S ω T c : WithTop ℤ) + meromorphicOrderAt (Z F S μ ω f) c := by
  let P := sLocalSelectedEulerMultiplier F S ω T
  have hA : AnalyticAt ℂ P c :=
    T.analyticAt_fun_prod (fun v _ ↦ selectedFactor_analytic F S ω v c)
  rw [meromorphicOrderAt_congr (sLocalWeilPrincipalValues_continued F S μ ν hν ω T f c)]
  change meromorphicOrderAt (P * Z F S μ ω f) c = _
  rw [meromorphicOrderAt_mul hA.meromorphicAt (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f c),
    sLocalSelectedEulerMultiplier_order F S ω T c]

include hν in
/-- Application of the finite principal-value operator removes exactly
the selected Euler orders from the universal pole bound. -/
theorem sLocalWeilPrincipalValues_pole_le (ω : PontryaginDual (K F S)) (T : Finset S)
    (f : E F S) (c : ℂ) :
    ((sLocalSelectedFinitePoleCount F S ω T c : ℤ) - (sLocalPoleCount F S ω c : ℤ) : ℤ) ≤
      meromorphicOrderAt (Z F S μ ω (sLocalWeilPrincipalValues F S T f)) c := by
  rw [sLocalWeilPrincipalValues_order F S μ ν hν ω T f c]
  have hf := sLocalZeta_poleOrder_le_euler F S μ ω f c
  rw [sLocalEulerFactor_order F S ω c, sLocalAllowedPoleOrder_eq_count F S ω c] at hf
  let a : ℤ := sLocalSelectedFinitePoleCount F S ω T c
  let b : ℤ := sLocalPoleCount F S ω c
  change ((a-b : ℤ) : WithTop ℤ) ≤ (a : WithTop ℤ) + meromorphicOrderAt (Z F S μ ω f) c
  rw [sub_eq_add_neg, WithTop.coe_add]
  exact add_le_add_right hf _

theorem sLocalSelectedFinitePoleCount_le (ω : PontryaginDual (K F S)) (T : Finset S) (c : ℂ) :
    sLocalSelectedFinitePoleCount F S ω T c ≤ sLocalPoleCount F S ω c := by
  apply le_trans _ (Nat.le_add_left _ _ : (sLocalFinitePolesAt F S ω c).card ≤ _)
  apply Finset.card_le_card
  intro v hv
  rw [sLocalFinitePolesAt, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩

include hν in
/-- The principal parts above the remaining pole bound vanish on the
image of the actual finite principal-value product. -/
theorem sLocalWeilPrincipalValues_removedLaurent_eq_zero (ω : PontryaginDual (K F S))
    (T : Finset S) (f : E F S) (c : ℂ) (k : ℕ)
    (hk : sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c < k) :
    sLocalLaurentCoeff F S μ ω c k (sLocalWeilPrincipalValues F S T f) = 0 := by
  apply (sLocalLaurentCoeff_vanish_iff F S μ ω c
    (sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c) _).mpr _ k hk
  have he : -((sLocalPoleCount F S ω c - sLocalSelectedFinitePoleCount F S ω T c : ℕ) : ℤ) =
      (sLocalSelectedFinitePoleCount F S ω T c : ℤ) - (sLocalPoleCount F S ω c : ℤ) := by
    have hh := sLocalSelectedFinitePoleCount_le F S ω T c
    omega
  rw [he]
  exact sLocalWeilPrincipalValues_pole_le F S μ ν hν ω T f c

end

end Masullo
