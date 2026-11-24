import SLocalTateProduct
import SLocalEntireStrip
import MellinAsymptoticExpansion

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Asymptotics Classical ContDiff NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S
private abbrev AUnits := (InfiniteAdeleRing F)ˣ
private abbrev Local (v : S) := (v.val.adicCompletion F)ˣ
private abbrev Characters := PontryaginDual (K F S)
private abbrev realParams (χ : Characters F S) := sLocalRealArchParameters F S χ
private abbrev complexParams (χ : Characters F S) := sLocalComplexArchParameters F S χ
private abbrev phase (χ : Characters F S) := sLocalFiniteZetaPhases F S χ
private abbrev finiteDen (χ : Characters F S) := sLocalFiniteZetaDenominator F S (phase F S χ)
private abbrev archDen (χ : Characters F S) :=
  archimedeanNumberFieldZetaDenominator F (realParams F S χ) (complexParams F S χ)

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable [MeasurableSpace (AUnits F)] [BorelSpace (AUnits F)]
  [∀ v : S, MeasurableSpace (Local F S v)] [∀ v : S, BorelSpace (Local F S v)]
  (μ : ∀ v : S, Measure (Local F S v))
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev μG := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
private abbrev Z (χ : Characters F S) (f : E F S) :=
  sLocalProductZetaContinued F S μ χ (realParams F S χ) (complexParams F S χ) f
private abbrev N (χ : Characters F S) (f : E F S) := sLocalEulerNormalizedMellin F S μ χ f
private abbrev D (χ : Characters F S) := sLocalEulerDenominator F S χ

/-- The normal meromorphic representative of the actual continued S-local zeta integral. -/
def sLocalContourZeta (χ : Characters F S) (f : E F S) : ℂ → ℂ :=
  toMeromorphicNFOn (Z F S μ χ f) univ

theorem sLocalContourZeta_normal (χ : Characters F S) (f : E F S) :
    MeromorphicNFOn (sLocalContourZeta F S μ χ f) univ :=
  meromorphicNFOn_toMeromorphicNFOn _ univ

theorem sLocalContourZeta_eq_germ (χ : Characters F S) (f : E F S) (z : ℂ) :
    sLocalContourZeta F S μ χ f =ᶠ[𝓝[≠] z] Z F S μ χ f :=
  (sLocalProductZetaContinued_meromorphic F S μ χ _ _ f).meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (mem_univ z)

private theorem contourZeta_analytic_eq_quotient (χ : Characters F S) (f : E F S)
    (z : ℂ) (hz : D F S χ z ≠ 0) :
    AnalyticAt ℂ (sLocalContourZeta F S μ χ f) z ∧
      sLocalContourZeta F S μ χ f z = N F S μ χ f z / D F S χ z := by
  let G := sLocalContourZeta F S μ χ f
  let H := N F S μ χ f / D F S χ
  have hD := sLocalEulerDenominator_analytic F S χ z
  have hH : AnalyticAt ℂ H z := (sLocalEulerNormalizedMellin_entire F S μ χ f z trivial).div hD hz
  have he : G =ᶠ[𝓝[≠] z] H := by
    filter_upwards [sLocalContourZeta_eq_germ F S μ χ f z,
      sLocalEulerNormalizedMellin_eq_germ F S μ χ f z,
      (hD.continuousAt.eventually_ne hz).filter_mono nhdsWithin_le_nhds] with w hw hN hn
    change sLocalContourZeta F S μ χ f w = N F S μ χ f w / D F S χ w
    change N F S μ χ f w = D F S χ w * Z F S μ χ f w at hN
    rw [hw,hN, mul_comm, mul_div_cancel_right₀ _ hn]
  have he' := ((sLocalContourZeta_normal F S μ χ f (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    hH.meromorphicNFAt).mp he
  exact ⟨hH.congr he'.symm, he'.eq_of_nhds⟩

theorem sLocalContourZeta_positive (χ : Characters F S) (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    sLocalContourZeta F S μ χ f z = sLocalIdelicZetaIntegral F S (μG F S μ) χ f z := by
  have hn := sLocalEulerDenominator_ne_zero_of_pos F S χ hz
  rw [(contourZeta_analytic_eq_quotient F S μ χ f z hn).2]
  have h := normalizedMellin_eq_mul_idelic F S μ χ f z hz
  change N F S μ χ f z = D F S χ z * sLocalIdelicZetaIntegral F S (μG F S μ) χ f z at h
  rw [h,mul_comm,mul_div_cancel_right₀ _ hn]

/-- The archimedean denominator stays nonzero at large absolute height, uniformly in the abscissa. -/
theorem sLocalArchDenominator_nonzero_at_height (χ : Characters F S) :
    ∃ T : ℝ, ∀ z : ℂ, T ≤ |z.im| → archDen F S χ z ≠ 0 := by
  let R := {v : InfinitePlace F // v.IsReal}
  let C := {v : InfinitePlace F // v.IsComplex}
  let a (v : R) := |(realParams F S χ v).1.im|
  let b (v : C) := |(complexParams F S χ v).1.im|
  refine ⟨(∑ v : R, a v) + (∑ v : C, b v) + 1, fun z hz ↦ ?_⟩
  unfold archDen archimedeanNumberFieldZetaDenominator
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv hn
    obtain ⟨j, hj⟩ := (realArchZetaDenominator_eq_zero_iff _ _).mp hn
    have he := congrArg Complex.im hj
    norm_num [Complex.mul_im] at he
    have h := Finset.single_le_sum (fun v _ ↦ abs_nonneg (realParams F S χ v).1.im) hv
    change a v ≤ ∑ v : R, a v at h
    have hz' : |z.im| = a v := by
      rw [show z.im = -(realParams F S χ v).1.im by linarith, abs_neg]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun v : C ↦ fun _ ↦ abs_nonneg (complexParams F S χ v).1.im)]
  · apply Finset.prod_ne_zero_iff.mpr
    intro v hv hn
    obtain ⟨j, hj⟩ := (complexArchZetaDenominator_eq_zero_iff _ _).mp hn
    have he := congrArg Complex.im hj
    simp only [Complex.add_im, Complex.neg_im, Complex.natCast_im, Complex.sub_im,
      Complex.div_ofNat_im, zero_div, neg_zero, sub_zero] at he
    have h := Finset.single_le_sum (fun v _ ↦ abs_nonneg (complexParams F S χ v).1.im) hv
    change b v ≤ ∑ v : C, b v at h
    have hz' : |z.im| = b v := by
      rw [show z.im = -(complexParams F S χ v).1.im by linarith, abs_neg]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun v : R ↦ fun _ ↦ abs_nonneg (realParams F S χ v).1.im)]

/-- Away from the finite Euler zeros the actual continued Mellin transform has
arbitrary polynomial decay at large heights, with a single explicit factor
for the reciprocal finite denominator. -/
theorem sLocalContourZeta_high_decay (χ : Characters F S) (f : E F S)
    (l r : ℝ) (n : ℕ) :
    ∃ C T : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → T ≤ |z.im| →
      finiteDen F S χ z ≠ 0 →
      AnalyticAt ℂ (sLocalContourZeta F S μ χ f) z ∧
      |z.im| ^ n * ‖sLocalContourZeta F S μ χ f z‖ ≤ C * ‖(finiteDen F S χ z)⁻¹‖ := by
  letI : (μG F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨m, hm, hweil⟩ := sLocalClassHaar_exists_weil F S (μG F S μ)
  letI := hm
  let p := sLocalPairedBergmanMellin F S m χ (Submodule.Quotient.mk f)
  obtain ⟨hR,hL⟩ := sLocalPairedBergmanMellin_idelic F S m χ (μG F S μ) hweil f
  obtain ⟨ε,hε,_,_,_,hFE⟩ := exists_sLocalTateProduct_fourier F S μ χ
  let P := sLocalTateEpsilonProduct F S χ ε
  let ρ := sLocalExplicitTateFactor F S χ P
  let H := sLocalContourZeta F S μ χ f
  let Q := finiteDen F S χ
  let a := min l 0
  let b := max r 1
  obtain ⟨C,T,k,hC,hpol⟩ := sLocalTateRatio_finiteCleared_norm_le_on_strip F S μ χ ε hε a (3/4)
    (by norm_num)
  obtain ⟨L,hLp⟩ := p.2.property.2.2 a (3/4) ((min_le_right _ _).trans (by norm_num))
    (fun z hz ↦ hz.2.trans_lt (by norm_num)) (n+k)
  obtain ⟨U,hUp⟩ := p.1.property.2.2 (1/2) b ((by norm_num : (1/2 : ℝ) ≤ 1).trans (le_max_right _ _))
    (fun z hz ↦ (by norm_num : (0 : ℝ) < 1/2).trans_le hz.1) n
  obtain ⟨V,hV⟩ := sLocalArchDenominator_nonzero_at_height F S χ
  let C' := max (C * (2 : ℝ)^k * max L 0) ((2 : ℝ)^S.card * max U 0)
  have hC' : 0 ≤ C' := (by positivity : 0 ≤ C * (2 : ℝ)^k * max L 0).trans (le_max_left _ _)
  refine ⟨C',max 1 (max V T),hC',fun z hz ht hn ↦ ?_⟩
  have hD : D F S χ z ≠ 0 := mul_ne_zero
    (hV z ((le_max_left _ _).trans ((le_max_right _ _).trans ht))) hn
  obtain ⟨ha,he⟩ := contourZeta_analytic_eq_quotient F S μ χ f z hD
  refine ⟨ha, ?_⟩
  have hbound : ‖Q z * (z ^ n * H z)‖ ≤ C' := by
    by_cases h : z.re ≤ 1/2
    · have hz' : z.re ∈ Icc a (3/4) := ⟨(min_le_left _ _).trans hz.1, by linarith⟩
      have hp : 0 < (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      have hN := normalizedMellin_eq_mul_idelic F S μ χ⁻¹ (sLocalSelectedFourier F S f) (1-z) hp
      change N F S μ χ⁻¹ (sLocalSelectedFourier F S f) (1-z) =
        D F S χ⁻¹ (1-z) * sLocalIdelicZetaIntegral F S (μG F S μ) χ⁻¹ (sLocalSelectedFourier F S f) (1-z) at hN
      have hFEz := hFE f z
      change N F S μ χ f z = P z * N F S μ χ⁻¹ (sLocalSelectedFourier F S f) (1-z) at hFEz
      have hLz : p.2.val z = sLocalIdelicZetaIntegral F S (μG F S μ) χ⁻¹
          (sLocalSelectedFourier F S f) (1-z) := hL z (by linarith)
      have hmatch : H z = ρ z * p.2.val z := by
        change H z = _ at he
        rw [he, hFEz, hN, hLz]
        change _ = (P z * (D F S χ z)⁻¹ * D F S χ⁻¹ (1-z)) * _
        simp only [div_eq_mul_inv]
        ring
      have hjoin : Q z * (z ^ n * H z) = (Q z * ρ z) * (z ^ n * p.2.val z) := by rw [hmatch]; ring
      rw [hjoin,norm_mul]
      have ht' : T ≤ |z.im| := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
      have hscale : 1 + |z.im| ≤ 2 * ‖z‖ := by
        linarith [Complex.abs_im_le_norm z, (le_max_left _ _).trans ht]
      calc
        _ ≤ (C * (1 + |z.im|)^k) * ‖z^n * p.2.val z‖ :=
          mul_le_mul_of_nonneg_right (hpol z hz' ht') (norm_nonneg _)
        _ ≤ (C * (2 * ‖z‖)^k) * ‖z^n * p.2.val z‖ := by gcongr
        _ = (C * (2 : ℝ)^k) * ‖z^(n+k) * p.2.val z‖ := by
          simp only [norm_mul,norm_pow,mul_pow,pow_add]; ring
        _ ≤ C' := (mul_le_mul_of_nonneg_left
          ((hLp (mem_image_of_mem _ hz')).trans (le_max_left _ _)) (by positivity)).trans (le_max_left _ _)
    · have hpos : 0 < z.re := by linarith
      have hz' : z.re ∈ Icc (1/2) b := ⟨le_of_not_ge h,hz.2.trans (le_max_left _ _)⟩
      have hmatch : H z = p.1.val z :=
        (sLocalContourZeta_positive F S μ χ f z hpos).trans (hR z hpos).symm
      rw [hmatch,norm_mul]
      exact (mul_le_mul (norm_sLocalFiniteZetaDenominator_le F S _ _ hpos)
        ((hUp (mem_image_of_mem _ hz')).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)).trans
          (le_max_right _ _)
  have hQ : 0 < ‖Q z‖ := norm_pos_iff.mpr hn
  simp only [norm_mul, norm_pow] at hbound
  have hnorm : ‖z‖ ^ n * ‖H z‖ ≤ C' * ‖(Q z)⁻¹‖ := by
    rw [norm_inv, ← div_eq_mul_inv, le_div_iff₀ hQ,mul_comm]
    exact hbound
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) _)
    (norm_nonneg _)).trans hnorm

/-- The actual radial theta profile in the positive modulus coordinate. -/
def sLocalContourTheta (m : Measure (K F S)) (χ : Characters F S) (f : E F S) (t : ℝ) : ℂ :=
  sLocalHomogeneousTheta F S m χ f.val
    (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd (Real.log t))))

/-- Mellin inversion on every positive line recovers the genuine homogeneous
theta profile for the quotient Haar measure specified by Weil unfolding. -/
theorem sLocalContourZeta_inverse_positive (m : Measure (K F S)) [m.IsHaarMeasure]
    (hweil : IsWeilQuotientMeasure (sUnitImage F S) (μG F S μ) Measure.count
      (sLocalClassHaar F S m))
    (χ : Characters F S) (f : E F S) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    mellinInv r (sLocalContourZeta F S μ χ f) t = sLocalContourTheta F S m χ f t := by
  letI : (μG F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  let φ := sLocalContourTheta F S m χ f
  obtain ⟨g,hg⟩ := exists_sLocalRadialSchwartz F S m χ f r hr
  have hprofile (x : ℝ) : g x = (Real.exp (r*x) : ℂ) * φ (Real.exp x) := by
    rw [hg, Complex.ofReal_exp, Complex.ofReal_mul]
    simp [φ, sLocalContourTheta, Real.log_exp]
  have hφ : MellinSchwartzAt φ r := mellinSchwartzAt_iff_positive_log.mpr
    ⟨g, funext fun x ↦ by rw [hprofile, Complex.real_smul]⟩
  have hf : ContinuousAt φ t := by
    have he (y : ℝ) (hy : 0 < y) : φ y = (Real.exp (-(r * Real.log y)) : ℂ) * g (Real.log y) := by
      rw [hprofile, Real.exp_log hy, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
        neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    have hc : ContinuousAt (fun y : ℝ ↦ (Real.exp (-(r * Real.log y)) : ℂ) * g (Real.log y)) t :=
      (Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_exp.continuousAt.comp ((continuousAt_const.mul
          (Real.continuousAt_log ht.ne')).neg))).mul
        (g.continuous.continuousAt.comp (Real.continuousAt_log ht.ne'))
    apply hc.congr
    filter_upwards [Ioi_mem_nhds ht] with y hy using (he y hy).symm
  have hM (z : ℂ) (hz : 0 < z.re) : sLocalContourZeta F S μ χ f z = mellin φ z := by
    rw [sLocalContourZeta_positive F S μ χ f z hz,
      (sLocalIdelicZeta_integrable_eq_theta F S (μG F S μ) m hweil χ f z hz).2,
      (sLocalThetaZeta_integrable_eq_radial F S m χ f z hz).2, mellin_eq_log_integral]
    simp [sLocalRadialMellin, φ, sLocalContourTheta, Real.log_exp]
  have hline (y : ℝ) : ((r : ℂ) + (y : ℂ)*I).re = r := by simp [Complex.mul_re]
  have hI : Complex.VerticalIntegrable (mellin φ) r := by
    obtain ⟨G,hG⟩ := exists_mellinVerticalSchwartz hφ
    change Integrable (fun y : ℝ ↦ mellin φ ((r : ℂ) + (y : ℂ) * I))
    have he : (fun y : ℝ ↦ mellin φ ((r : ℂ) + (y : ℂ) * I)) = (G : ℝ → ℂ) := by
      funext y
      rw [congrFun hG y]
      exact congrArg (mellin φ) (Complex.ext (hline y) (by simp [Complex.mul_im]))
    rw [he]
    exact G.integrable
  have heq : mellinInv r (sLocalContourZeta F S μ χ f) t = mellinInv r (mellin φ) t := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by dsimp only; rw [hM _ ((hline y).symm ▸ hr)]
  exact heq.trans (mellinInv_mellin_eq r φ ht
    (mellinConvergent_of_schwartzAt (s := (r : ℂ)) (by simpa using hφ)) hI hf)

/-- The distinct-pole contour expansion of the S-local theta profile.
The contour may be shifted to any negative line avoiding the Euler divisor,
and the error is the absolutely convergent inverse Mellin integral on that line. -/
theorem sLocalContourZeta_residue_expansion (m : Measure (K F S)) [m.IsHaarMeasure]
    (hweil : IsWeilQuotientMeasure (sUnitImage F S) (μG F S μ) Measure.count
      (sLocalClassHaar F S m))
    (χ : Characters F S) (f : E F S) {l r : ℝ} (hl : l < 0) (hr : 0 < r)
    (hnoPole : ∀ z : ℂ, z.re = l → D F S χ z ≠ 0) :
    let Z := sLocalContourZeta F S μ χ f
    let hZ : Meromorphic Z := fun z ↦ (sLocalContourZeta_normal F S μ χ f (mem_univ z)).meromorphicAt
    ∃ low high : ℕ → ℝ, Tendsto low atTop atBot ∧ Tendsto high atTop atTop ∧
      Complex.VerticalIntegrable Z l ∧
      (∀ J : Set ℝ, IsCompact J → J ⊆ Ioi 0 →
        TendstoUniformlyOn (fun j t ↦ mellinResidueWindow Z hZ l r (low j) (high j) t)
          (fun t ↦ sLocalContourTheta F S m χ f t - mellinInv l Z t) atTop J) ∧
      (mellinInv l Z =O[𝓝[>] (0 : ℝ)] fun t ↦ t^(-l)) := by
  intro Z hZ
  have hlr := hl.trans hr
  obtain ⟨B,T,hB,htop,hbot,hT⟩ :=
    sLocalFiniteZetaDenominator_bounded_inverse_strip_sequence F S (phase F S χ) hlr.le
  obtain ⟨L,hL,hLv⟩ := sLocalFiniteZetaDenominator_bounded_inverse_vertical F S (phase F S χ) hl.ne
  obtain ⟨R,hR,hRv⟩ := sLocalFiniteZetaDenominator_bounded_inverse_vertical F S (phase F S χ) hr.ne'
  obtain ⟨C,A,hC,hdec⟩ := sLocalContourZeta_high_decay F S μ χ f l r 2
  let v (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I
  have vr (x y : ℝ) : (v x y).re = x := by simp [v, Complex.mul_re]
  have vi (x y : ℝ) : (v x y).im = y := by simp [v, Complex.mul_im]
  let low (j : ℕ) := T (-(j : ℤ))
  let high (j : ℕ) := T (j : ℤ)
  have hlo : Tendsto low atTop atBot := hbot.comp
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hhi : Tendsto high atTop atTop := htop.comp tendsto_natCast_atTop_atTop
  have hleft (y : ℝ) : AnalyticAt ℂ Z (v l y) :=
    (contourZeta_analytic_eq_quotient F S μ χ f _ (hnoPole _ (vr _ _))).1
  have hright (y : ℝ) : AnalyticAt ℂ Z (v r y) :=
    (contourZeta_analytic_eq_quotient F S μ χ f _
      (sLocalEulerDenominator_ne_zero_of_pos F S χ ((vr _ _).symm ▸ hr))).1
  have hline (x M : ℝ) (hx : x ∈ Icc l r)
      (hreg : ∀ y, AnalyticAt ℂ Z (v x y))
      (hQ : ∀ y, finiteDen F S χ (v x y) ≠ 0 ∧
        ‖(finiteDen F S χ (v x y))⁻¹‖ ≤ M) :
      Complex.VerticalIntegrable Z x := by
    change Integrable (fun y : ℝ ↦ Z (v x y))
    refine integrable_of_power_tail (C := C*M) (R := A) ?_ (by norm_num : (1 : ℝ) < 2) ?_
    · exact continuous_iff_continuousAt.mpr fun y ↦ (hreg y).continuousAt.comp'
        (by fun_prop : ContinuousAt (v x) y)
    · intro y hy
      have hd := (hdec (v x y) ((vr _ _).symm ▸ hx) ((vi _ _).symm ▸ hy) (hQ y).1).2
      rw [vi] at hd
      rw [Real.rpow_two]
      exact hd.trans (mul_le_mul_of_nonneg_left (hQ y).2 hC)
  have hlI := hline l L ⟨le_rfl,hlr.le⟩ hleft (fun y ↦ hLv (v l y) (vr _ _))
  have hrI := hline r R ⟨hlr.le,le_rfl⟩ hright (fun y ↦ hRv (v r y) (vr _ _))
  have hHor : ∃ K : ℝ, ∀ᶠ j in atTop, ∀ x ∈ Icc l r,
      (AnalyticAt ℂ Z (v x (low j)) ∧ AnalyticAt ℂ Z (v x (high j))) ∧
      (|low j| * ‖Z (v x (low j))‖ ≤ K ∧ |high j| * ‖Z (v x (high j))‖ ≤ K) := by
    refine ⟨C*B, ?_⟩
    have he (k : ℤ) (y : ℝ) (hy : y = T k) (ht : max 1 A ≤ |y|) (x : ℝ) (hx : x ∈ Icc l r) :
        AnalyticAt ℂ Z (v x y) ∧ |y| * ‖Z (v x y)‖ ≤ C*B := by
      have hQ := hT k (v x y) ((vr _ _).symm ▸ hx) ((vi _ _).trans hy)
      obtain ⟨ha,hd⟩ := hdec (v x y) ((vr _ _).symm ▸ hx)
        ((vi _ _).symm ▸ (le_max_right _ _).trans ht) hQ.1
      rw [vi] at hd
      refine ⟨ha, ?_⟩
      have hone : 1 ≤ |y| := (le_max_left _ _).trans ht
      have hp : |y| ≤ |y|^2 := by nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr hone)]
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
        (hd.trans (mul_le_mul_of_nonneg_left hQ.2 hC))
    filter_upwards [(tendsto_abs_atBot_atTop.comp hlo).eventually (eventually_ge_atTop (max 1 A)),
      (tendsto_abs_atTop_atTop.comp hhi).eventually (eventually_ge_atTop (max 1 A))] with j hj hj' x hx
    exact ⟨⟨(he (-(j : ℤ)) _ rfl hj x hx).1,(he (j : ℤ) _ rfl hj' x hx).1⟩,
      (he (-(j : ℤ)) _ rfl hj x hx).2,(he (j : ℤ) _ rfl hj' x hx).2⟩
  refine ⟨low,high,hlo,hhi,hlI,?_,mellinInv_isBigO_nhdsGT_zero l Z⟩
  intro J hJ hpos
  have hu := mellinInv_sub_tendstoUniformlyOn_residue_windows hlr (sLocalContourZeta_normal F S μ χ f)
    hlo hhi hHor (fun y ↦ ⟨hleft y,hright y⟩) hlI hrI hJ hpos
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with j hj t ht
  rw [← sLocalContourZeta_inverse_positive F S μ m hweil χ f hr (hpos ht)]
  exact hj t ht

/-- The Euler divisor lies over the nonpositive half-integer abscissae. -/
theorem sLocalEulerDenominator_zero_re (χ : Characters F S) {z : ℂ}
    (hz : D F S χ z = 0) :
    ∃ n : ℕ, z.re = -(n : ℝ) / 2 := by
  have hp := (sLocalEulerDenominator_eq_zero_iff_lattices F S χ z).mp hz
  rcases hp with ⟨v,n,h⟩ | ⟨v,n,h⟩ | ⟨v,_,k,h⟩
  · refine ⟨2 * ((realParams F S χ v).2 % 2 + 2*n), ?_⟩
    have he := congrArg Complex.re h
    simp [Complex.mul_re,sLocalRealArchParameters_re] at he
    push_cast
    linarith
  · refine ⟨(complexParams F S χ v).2.natAbs + 2*n, ?_⟩
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.neg_re,sLocalComplexArchParameters_re,neg_zero,
      Complex.div_ofNat_re,Complex.natCast_re] at he
    push_cast
    linarith
  · refine ⟨0, ?_⟩
    rw [h]
    simp only [Complex.mul_re,Complex.I_re,mul_zero,Complex.I_im,mul_one,zero_sub,
      Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.mul_im,Complex.intCast_im,
      zero_mul,add_zero,Complex.div_im,Complex.ofReal_re]
    simp

private theorem exists_cutoff_between_poles (A : ℝ) :
    ∃ B > A, ∀ n : ℕ, (n : ℝ) / 2 ≤ B → (n : ℝ) / 2 ≤ A := by
  let U : ℝ := (↑⌊2*A⌋ + 1) / 2
  have hU : A < U := by
    have hf := Int.lt_floor_add_one (2*A)
    dsimp [U]
    linarith
  refine ⟨(A+U)/2, by linarith, fun n hn ↦ ?_⟩
  have hn' : (n : ℝ) < (↑⌊2*A⌋ : ℝ) + 1 := by dsimp [U] at hn; dsimp [U] at hU; linarith
  have hi : (n : ℤ) < ⌊2*A⌋ + 1 := by exact_mod_cast hn'
  have hj : (n : ℤ) ≤ ⌊2*A⌋ := by omega
  have hk : (n : ℝ) ≤ (↑⌊2*A⌋ : ℝ) := by exact_mod_cast hj
  linarith [Int.floor_le (2*A)]

/-- The contribution of a pole of order `n+1` uses the original
S-local Laurent coefficients with indices `k+1` for the log powers `k`. -/
theorem sLocalContourZeta_pole_powerLog (χ : Characters F S) (f : E F S) {p : ℂ}
    (hp : meromorphicOrderAt (sLocalContourZeta F S μ χ f) p < 0) :
    ∃ n : ℕ,
      meromorphicOrderAt (sLocalContourZeta F S μ χ f) p = (-((n : ℤ) + 1) : ℤ) ∧
      sLocalLaurentCoeff F S μ χ p (n+1) f ≠ 0 ∧ ∀ t : ℝ, 0 < t →
        meromorphicResidue (inverseMellinFactor t * sLocalContourZeta F S μ χ f) p =
          ∑ k ∈ Finset.range (n + 1),
            sLocalLaurentCoeff F S μ χ p (k+1) f *
              ((-1 : ℂ)^k / (k.factorial : ℂ)) * (t : ℂ)^(-p) * (Real.log t : ℂ)^k := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp.ne_top
  have hm' : m < 0 := by exact_mod_cast (hm ▸ hp : (m : WithTop ℤ) < 0)
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hm'
  have horder : meromorphicOrderAt (sLocalContourZeta F S μ χ f) p = (-((n : ℤ) + 1) : ℤ) := by
    simpa only [Int.negSucc_eq] using hm.symm
  let N := n + 1
  let P (w : ℂ) := (w-p)^N * Z F S μ χ f w
  let G := toMeromorphicNFOn P univ
  have hOrig : Meromorphic (Z F S μ χ f) :=
    sLocalProductZetaContinued_meromorphic F S μ χ _ _ f
  have hOrigOrder : meromorphicOrderAt (Z F S μ χ f) p = (-(N : ℤ) : ℤ) := by
    rw [← meromorphicOrderAt_congr (sLocalContourZeta_eq_germ F S μ χ f p), horder]
    rfl
  let d := exists_sLocalMellinLaurentDisk F S χ p
  let R := d.choose
  obtain ⟨hG,hEq,hGOrder⟩ := laurentClear_analyticOnNhd hOrig N hOrigOrder.ge
    (fun w hw ↦ sLocalZeta_analyticAt_regular F S μ χ f (d.choose_spec.2 hw))
  have hGa : AnalyticAt ℂ G p := hG p (Metric.mem_closedBall_self d.choose_spec.1.le)
  have hG0 : G p ≠ 0 := hGa.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp (by
    rw [hGOrder, hOrigOrder, ← WithTop.coe_add, add_neg_cancel]
    rfl)
  have hCoeff (k : ℕ) (hk : k ≤ N) :
      sLocalLaurentCoeff F S μ χ p k f = iteratedDeriv (N-k) G p / ((N-k).factorial : ℂ) := by
    change sLocalLaurentCircleCoeff F S μ χ p R d.choose_spec.1 d.choose_spec.2 k f = _
    rw [sLocalLaurentCircleCoeff_apply, laurentCircle_eq_taylor_of_cleared d.choose_spec.1 _ G N k
      (fun w hw ↦ (hG w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ hEq ⟨Metric.sphere_subset_closedBall hw,
        fun hz ↦ d.choose_spec.1.ne' (by simpa [mem_singleton_iff.mp hz] using (Metric.mem_sphere.mp hw).symm)⟩),
      ite_eq_left hk]
  have hP : Meromorphic P := fun w ↦
    (((analyticAt_id.sub (analyticAt_const (v := p))).pow N).meromorphicAt.mul (hOrig w))
  have hGerm : sLocalContourZeta F S μ χ f =ᶠ[𝓝[≠] p]
      fun z ↦ (z-p)^(-((n : ℤ)+1)) • G z := by
    filter_upwards [sLocalContourZeta_eq_germ F S μ χ f p,
      hP.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ p), self_mem_nhdsWithin]
      with w hw hgw hne
    change G w = P w at hgw
    have hne' : w-p ≠ 0 := sub_ne_zero.mpr hne
    rw [hw,hgw,show (n : ℤ)+1 = (N : ℤ) from rfl, zpow_neg,zpow_natCast,smul_eq_mul]
    exact (inv_mul_cancel_left₀ (pow_ne_zero N hne') _).symm
  refine ⟨n,horder,?_,fun t ht ↦ ?_⟩
  · change sLocalLaurentCoeff F S μ χ p N f ≠ 0
    rwa [hCoeff N le_rfl, Nat.sub_self, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  · rw [meromorphicResidue_inverseMellin_of_cleared hGa hG0 hGerm ht]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k + 1 ≤ N := Finset.mem_range.mp hk
    rw [hCoeff (k+1) hk', show N-(k+1) = n-k from by dsimp [N]; omega]

/-- The norm-one character factor extends a radial approximation to all
S-idele classes. -/
def sLocalContourLift (χ : Characters F S) (g : ℝ → ℂ) (q : SIdeleQuotient F S) : ℂ :=
  (((χ ((sLocalZetaSplit F S).symm q).2 : Circle) : ℂ)⁻¹) * g (sLocalClassModulus F S q)

theorem sLocalContourLift_cpow (χ : Characters F S) (p : ℂ) (q : SIdeleQuotient F S) :
    sLocalContourLift F S χ (fun t ↦ (t : ℂ)^(-p)) q =
      (sLocalZetaWeight F S χ p q)⁻¹ := by
  have ht := sLocalClassModulus_pos F S q
  have hLog : ((sLocalZetaSplit F S).symm q).1 = Real.log (sLocalClassModulus F S q) := by
    simpa only [Homeomorph.apply_symm_apply] using
      (sLocalZetaSplit_logModulus F S ((sLocalZetaSplit F S).symm q)).symm
  unfold sLocalContourLift sLocalZetaWeight
  dsimp only
  rw [hLog, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ← Complex.ofReal_log ht.le, mul_neg, mul_comm (Real.log (sLocalClassModulus F S q) : ℂ) p,
    Complex.exp_neg, mul_inv_rev]

theorem sLocalContourLift_theta (m : Measure (K F S)) [m.IsHaarMeasure]
    (χ : Characters F S) (f : E F S) (q : SIdeleQuotient F S) :
    sLocalContourLift F S χ (sLocalContourTheta F S m χ f) q =
      sLocalHomogeneousTheta F S m χ f.val q := by
  let e := sLocalZetaSplit F S
  let k := (e.symm q).2
  let g : SIdeleQuotient F S := QuotientGroup.mk (sLocalExpSection F S
    (Multiplicative.ofAdd (Real.log (sLocalClassModulus F S q))))
  have hLog : Real.log (sLocalClassModulus F S q) = (e.symm q).1 := by
    simpa only [Homeomorph.apply_symm_apply] using
      sLocalZetaSplit_logModulus F S ((sLocalZetaSplit F S).symm q)
  have hq : g * k.val = q := by
    have h := e.apply_symm_apply q
    change QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd (e.symm q).1)) * k.val = q at h
    simpa only [g, hLog] using h
  change (((χ k : Circle) : ℂ)⁻¹) * sLocalHomogeneousTheta F S m χ f.val g = _
  rw [← sLocalHomogeneousTheta_translate F S m χ f.val k g, mul_comm k.val g, hq]

private theorem continuous_contourClassModulus : Continuous (sLocalClassModulus F S) :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp (sQuotientNorm_proper F S).continuous)

/-- Corrected cutoff formulation of Theorem 7.1.2.3. It includes poles at
the cutoff, uses distinct centers, and extends the recurrent contour limit
uniformly over compact subsets of the full S-idele quotient. -/
theorem sLocalHomogeneousTheta_cutoff_expansion (m : Measure (K F S)) [m.IsHaarMeasure]
    (hweil : IsWeilQuotientMeasure (sUnitImage F S) (μG F S μ) Measure.count
      (sLocalClassHaar F S m))
    (χ : Characters F S) (f : E F S) {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    let Z := sLocalContourZeta F S μ χ f
    let hZ : Meromorphic Z := fun z ↦ (sLocalContourZeta_normal F S μ χ f (mem_univ z)).meromorphicAt
    ∃ (B : ℝ) (low high : ℕ → ℝ), A < B ∧ Tendsto low atTop atBot ∧ Tendsto high atTop atTop ∧
      Complex.VerticalIntegrable Z (-B) ∧
      (∀ (j : ℕ) (p : ℂ),
        p ∈ rectanglePoles Z (-B) r (low j) (high j) hZ.meromorphicOn ↔
          -A ≤ p.re ∧ p.im ∈ uIcc (low j) (high j) ∧ meromorphicOrderAt Z p < 0) ∧
      (∀ C : Set (SIdeleQuotient F S), IsCompact C →
        TendstoUniformlyOn
          (fun j ↦ sLocalContourLift F S χ (mellinResidueWindow Z hZ (-B) r (low j) (high j)))
          (fun q ↦ sLocalHomogeneousTheta F S m χ f.val q -
            sLocalContourLift F S χ (mellinInv (-B) Z) q) atTop C) ∧
      (∀ q : SIdeleQuotient F S, sLocalClassModulus F S q ≤ 1 →
        ‖sLocalContourLift F S χ (mellinInv (-B) Z) q‖ ≤
          ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖Z ((-B : ℝ) + (y : ℂ) * I)‖) *
            sLocalClassModulus F S q ^ A) := by
  intro Z hZ
  obtain ⟨B,hB,hcut⟩ := exists_cutoff_between_poles A
  have hBpos := hA.trans hB
  have hAB {p : ℂ} (hp : D F S χ p = 0) (hleft : -B ≤ p.re) : -A ≤ p.re := by
    obtain ⟨n, hn⟩ := sLocalEulerDenominator_zero_re F S χ hp
    have := hcut n (by linarith)
    linarith
  have hPole {p : ℂ} (hp : meromorphicOrderAt Z p < 0) : D F S χ p = 0 := by
    by_contra hn
    exact (not_lt_of_ge (contourZeta_analytic_eq_quotient F S μ χ f p hn).1.meromorphicOrderAt_nonneg) hp
  have hline (p : ℂ) (hp : p.re = -B) : D F S χ p ≠ 0 := by
    intro h
    have := hAB h hp.ge
    linarith
  obtain ⟨low,high,hlo,hhi,hI,hU,_⟩ := sLocalContourZeta_residue_expansion F S μ m hweil χ f
    (neg_neg_of_pos hBpos) hr hline
  refine ⟨B,low,high,hB,hlo,hhi,hI,?_,?_,?_⟩
  · intro j p
    rw [mem_rectanglePoles, Complex.mem_reProdIm, uIcc_of_le (show -B ≤ r by linarith)]
    constructor
    · rintro ⟨⟨hp, hy⟩, ho⟩
      exact ⟨hAB (hPole ho) hp.1, hy, ho⟩
    · rintro ⟨hp,hy,ho⟩
      obtain ⟨n,hn⟩ := sLocalEulerDenominator_zero_re F S χ (hPole ho)
      exact ⟨⟨⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) n]⟩,hy⟩,ho⟩
  · intro C hC
    let J := sLocalClassModulus F S '' C
    have hu := hU J (hC.image (continuous_contourClassModulus F S))
      (by rintro y ⟨q,_,rfl⟩; exact sLocalClassModulus_pos F S q)
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with j hj q hq
    have ht : sLocalClassModulus F S q ∈ J := ⟨q,hq,rfl⟩
    have hn : ‖(((χ ((sLocalZetaSplit F S).symm q).2 : Circle) : ℂ)⁻¹)‖ = 1 := by
      rw [norm_inv,Circle.norm_coe,inv_one]
    rw [← sLocalContourLift_theta F S m χ f q, dist_eq_norm]
    simp only [sLocalContourLift, ← mul_sub, norm_mul, hn, one_mul]
    simpa only [dist_eq_norm] using hj _ ht
  · intro q hq
    have ht := sLocalClassModulus_pos F S q
    have h := mellinInv_norm_le_verticalIntegral (-B) Z ht
    simp only [sLocalContourLift, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul]
    simp only [neg_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht hq hB.le) (by positivity))

end
end Masullo
