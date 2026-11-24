import ArchimedeanExplicitContour
import HeckeContourHeights
import HeckePrimePowerLimits
import HeckeConductorReflection
import ManuscriptHeckeRegularity
import Mathlib.Analysis.Meromorphic.Complex

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

theorem scaledGamma_analytic_ne_zero (k P : ℝ) (b s : ℂ)
    (h : ∀ n : ℕ, ((k : ℂ) * (s + b)) ≠ -(n : ℂ)) :
    AnalyticAt ℂ (scaledGamma k P b) s ∧ scaledGamma k P b s ≠ 0 := by
  have hzero := Complex.Gamma_ne_zero h
  have hinv : AnalyticAt ℂ (fun z : ℂ => (Gamma z)⁻¹) ((k : ℂ) * (s + b)) := by
    simpa only [one_div] using
      (differentiable_one_div_Gamma.analyticAt ((k : ℂ) * (s + b)))
  have hg : AnalyticAt ℂ Gamma ((k : ℂ) * (s + b)) := by
    have he := hinv.inv (inv_ne_zero hzero)
    change AnalyticAt ℂ (fun z : ℂ => ((Gamma z)⁻¹)⁻¹) ((k : ℂ) * (s + b)) at he
    simpa only [inv_inv] using he
  have harg : AnalyticAt ℂ (fun z : ℂ => (k : ℂ) * (z + b)) s :=
    analyticAt_const.fun_mul (analyticAt_id.add analyticAt_const)
  exact ⟨(analyticAt_const.fun_mul harg).cexp.fun_mul
    (hg.comp (f := fun z : ℂ => (k : ℂ) * (z+b)) harg),
    mul_ne_zero (exp_ne_zero _) hzero⟩

private theorem norm_complex_le_re_add_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  simpa only [Complex.re_add_im, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] using
    (norm_add_le (z.re : ℂ) ((z.im : ℂ) * I))

/-- The scaled Euler factor is regular and has linear logarithmic-derivative
growth high in the strip containing the contour. -/
theorem scaledGamma_high_strip (k P : ℝ) (hk : 0 < k) (hk₁ : k ≤ 1)
    (b : ℂ) (hb : 0 ≤ b.re) :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) 2 → T ≤ |z.im| →
      AnalyticAt ℂ (scaledGamma k P b) z ∧ scaledGamma k P b z ≠ 0 ∧
        ‖logDeriv (scaledGamma k P b) z‖ ≤ C * |z.im| := by
  obtain ⟨C, hC, hG⟩ := exists_norm_logDeriv_scaledGamma_le_high k P b
  refine ⟨max 1 (1/k + |b.im|), 4*C, le_max_left _ _, by positivity, fun z hz ht => ?_⟩
  have h₁ := (le_max_left (1 : ℝ) (1/k + |b.im|)).trans ht
  have h₂ := (le_max_right (1 : ℝ) (1/k + |b.im|)).trans ht
  have hre : -1 ≤ ((k : ℂ) * (z + b)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re]
    have h := mul_le_mul_of_nonneg_left (show -1 ≤ z.re + b.re by linarith [hz.1]) hk.le
    linarith
  have him : 1 ≤ |((k : ℂ) * (z + b)).im| := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im, abs_mul, abs_of_pos hk, ← div_le_iff₀' hk]
    have h := abs_sub_le z.im (z.im + b.im) 0
    have h' : |z.im| ≤ |b.im| + |z.im+b.im| := by
      simpa only [sub_add_cancel_left, abs_neg, sub_zero] using h
    linarith
  have hreg (n : ℕ) : (k : ℂ) * (z + b) ≠ -(n : ℂ) := by
    intro h
    rw [h] at him
    norm_num at him
  obtain ⟨ha, hne⟩ := scaledGamma_analytic_ne_zero k P b z hreg
  refine ⟨ha, hne, (hG z hre him).trans ?_⟩
  have hzre : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hzNorm := norm_complex_le_re_add_im z
  have hbound : 1 + ‖z‖ ≤ 4 * |z.im| := by linarith
  calc
    _ ≤ C * (4 * |z.im|) := mul_le_mul_of_nonneg_left hbound hC
    _ = _ := by ring

private theorem finiteGamma_high_strip {ι : Type*} [Fintype ι]
    (g : ι → ℂ → ℂ)
    (h : ∀ i, ∃ T C : ℝ, 1 ≤ T ∧ 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) 2 →
      T ≤ |z.im| → AnalyticAt ℂ (g i) z ∧ g i z ≠ 0 ∧ ‖logDeriv (g i) z‖ ≤ C * |z.im|) :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) 2 → T ≤ |z.im| →
      AnalyticAt ℂ (fun w ↦ ∏ i, g i w) z ∧ (∏ i, g i z) ≠ 0 ∧
        ‖logDeriv (fun w ↦ ∏ i, g i w) z‖ ≤ C * |z.im| := by
  choose T C hT hC hG using h
  refine ⟨1 + ∑ i, T i, ∑ i, C i, ?_, Finset.sum_nonneg (fun i _ => hC i), fun z hz ht => ?_⟩
  · have ht : 0 ≤ ∑ i, T i := Finset.sum_nonneg (fun i _ => (zero_le_one.trans (hT i)))
    linarith
  · have H (i : ι) := hG i z hz ((Finset.single_le_sum
        (fun j _ => zero_le_one.trans (hT j)) (Finset.mem_univ i)).trans (by linarith))
    refine ⟨Finset.analyticAt_fun_prod _ (fun i _ => (H i).1),
      Finset.prod_ne_zero_iff.mpr (fun i _ => (H i).2.1), ?_⟩
    rw [logDeriv_prod (s := Finset.univ) (f := g) (fun i _ => (H i).2.1)
      (fun i _ => (H i).1.differentiableAt)]
    calc
      _ ≤ ∑ i, ‖logDeriv (g i) z‖ := norm_sum_le _ _
      _ ≤ ∑ i, C i * |z.im| := Finset.sum_le_sum (fun i _ => (H i).2.2)
      _ = _ := by rw [Finset.sum_mul]

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}

variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev ω := sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu
private abbrev rparams := sLocalRealArchParameters F S (ω F χ S hs hu)
private abbrev cparams := sLocalComplexArchParameters F S (ω F χ S hs hu)

abbrev manuscriptHeckeRealGammaShift (t : ℝ) (v : R F) : ℂ :=
  (rparams F χ S hs hu v).1 + (((rparams F χ S hs hu v).2 % 2 : ℕ) : ℂ) - (t : ℂ) * I

abbrev manuscriptHeckeComplexGammaShift (t : ℝ) (v : C F) : ℂ :=
  (cparams F χ S hs hu v).1 + ((cparams F χ S hs hu v).2.natAbs : ℂ) / 2 - (t : ℂ) * I

/-- Archimedean factor of the manuscript's completed Euler product,
including division by two at each complex place. -/
def manuscriptHeckeArchGamma (t : ℝ) (z : ℂ) : ℂ :=
  (∏ v : R F, scaledGamma (1 / 2) Real.pi (manuscriptHeckeRealGammaShift F χ S hs hu t v) z) *
    ∏ v : C F, scaledGamma 1 (2 * Real.pi) (manuscriptHeckeComplexGammaShift F χ S hs hu t v) z

private theorem manuscriptHeckeArchGamma_eq (t : ℝ) (z : ℂ) :
    manuscriptHeckeArchGamma F χ S hs hu t z =
      (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F *
        (archimedeanNumberFieldZetaDenominator F (rparams F χ S hs hu)
          (cparams F χ S hs hu) (z - (t : ℂ) * I))⁻¹ := by
  unfold manuscriptHeckeArchGamma archimedeanNumberFieldZetaDenominator
  simp_rw [scaledGamma_real, scaledGamma_complex, realArchZetaDenominator, complexArchZetaDenominator,
    mul_inv, ← Finset.prod_inv_distrib, inv_inv]
  have hr (v : R F) : z + manuscriptHeckeRealGammaShift F χ S hs hu t v =
      z - (t : ℂ) * I + (rparams F χ S hs hu v).1 + ((rparams F χ S hs hu v).2 % 2 : ℕ) := by
    dsimp only [manuscriptHeckeRealGammaShift]
    ring
  have hc (v : C F) : z + manuscriptHeckeComplexGammaShift F χ S hs hu t v =
      z - (t : ℂ) * I + (cparams F χ S hs hu v).1 + ((cparams F χ S hs hu v).2.natAbs : ℂ) / 2 := by
    dsimp only [manuscriptHeckeComplexGammaShift]
    ring
  simp_rw [hr, hc, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

theorem manuscriptCompletedHeckeEuler_eq_archGamma_mul (t : ℝ) (z : ℂ) :
    manuscriptCompletedHeckeEuler F χ S hs hu t z =
      manuscriptHeckeArchGamma F χ S hs hu t z * manuscriptFiniteHeckeEuler F χ z := by
  rw [manuscriptHeckeArchGamma_eq]
  unfold manuscriptCompletedHeckeEuler
  rw [mul_assoc]

theorem manuscriptHeckeArchGamma_meromorphic (t : ℝ) :
    MeromorphicOn (manuscriptHeckeArchGamma F χ S hs hu t) univ := by
  intro z _
  have hg := (archimedeanNumberFieldZetaDenominator_analytic F (rparams F χ S hs hu)
    (cparams F χ S hs hu) (z - (t : ℂ) * I)).comp
    (f := fun w : ℂ => w - (t : ℂ) * I) (analyticAt_id.sub analyticAt_const)
  have he := (MeromorphicAt.const ((2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F) z).mul
    hg.meromorphicAt.inv
  exact he.congr (.of_forall fun w => (manuscriptHeckeArchGamma_eq F χ S hs hu t w).symm)

/-- The actual archimedean product is zero-free with linearly bounded
logarithmic derivative high in the contour strip. -/
theorem manuscriptHeckeArchGamma_high_strip (t : ℝ) :
    ∃ T D : ℝ, 1 ≤ T ∧ 0 ≤ D ∧ ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) 2 → T ≤ |z.im| →
      AnalyticAt ℂ (manuscriptHeckeArchGamma F χ S hs hu t) z ∧
      manuscriptHeckeArchGamma F χ S hs hu t z ≠ 0 ∧
      ‖logDeriv (manuscriptHeckeArchGamma F χ S hs hu t) z‖ ≤ D * |z.im| := by
  let G (v : R F) := scaledGamma (1 / 2) Real.pi (manuscriptHeckeRealGammaShift F χ S hs hu t v)
  let H (v : C F) := scaledGamma 1 (2 * Real.pi) (manuscriptHeckeComplexGammaShift F χ S hs hu t v)
  have hr (v : R F) : 0 ≤ (manuscriptHeckeRealGammaShift F χ S hs hu t v).re := by
    simp [manuscriptHeckeRealGammaShift, Complex.add_re, Complex.sub_re, Complex.mul_re, sLocalRealArchParameters_re]
  have hc (v : C F) : 0 ≤ (manuscriptHeckeComplexGammaShift F χ S hs hu t v).re := by
    simp [manuscriptHeckeComplexGammaShift, Complex.add_re, Complex.sub_re, Complex.mul_re,
      sLocalComplexArchParameters_re]
    positivity
  obtain ⟨T₁, D₁, hT₁, hD₁, hG⟩ := finiteGamma_high_strip G (fun v =>
    scaledGamma_high_strip (1 / 2) Real.pi (by norm_num) (by norm_num) _ (hr v))
  obtain ⟨T₂, D₂, _, hD₂, hH⟩ := finiteGamma_high_strip H (fun v =>
    scaledGamma_high_strip 1 (2 * Real.pi) one_pos le_rfl _ (hc v))
  refine ⟨max T₁ T₂, D₁+D₂, hT₁.trans (le_max_left _ _), add_nonneg hD₁ hD₂, fun z hz ht => ?_⟩
  obtain ⟨hG₁, hG₂, hG₃⟩ := hG z hz ((le_max_left _ _).trans ht)
  obtain ⟨hH₁, hH₂, hH₃⟩ := hH z hz ((le_max_right _ _).trans ht)
  refine ⟨hG₁.fun_mul hH₁, mul_ne_zero hG₂ hH₂, ?_⟩
  change ‖logDeriv (fun w ↦ (∏ v, G v w) * ∏ v, H v w) z‖ ≤ _
  rw [logDeriv_mul (f := fun w ↦ ∏ v, G v w) (g := fun w ↦ ∏ v, H v w)
    z hG₂ hH₂ hG₁.differentiableAt hH₁.differentiableAt, add_mul]
  exact (norm_add_le _ _).trans (add_le_add hG₃ hH₃)

local instance completedContourNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance completedContourNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance completedContourIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance completedContourIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
variable [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
variable (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
variable [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The actual completed function has exhausting horizontal edges on which
its logarithmic derivative is analytic and uniformly quadratically bounded. -/
theorem exists_manuscriptCompletedHecke_horizontal_contours (t : ℝ) :
    ∃ (L : ℂ → ℂ) (lo hi : ℕ → ℝ) (A : ℝ), 0 ≤ A ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
      ∀ᶠ j in atTop, ∀ x ∈ Icc (-1 : ℝ) 2, ∀ y ∈ ({lo j, hi j} : Set ℝ),
        let z : ℂ := ⟨x, y⟩
        AnalyticAt ℂ L z ∧ L z ≠ 0 ∧ AnalyticAt ℂ (logDeriv L) z ∧
          ‖logDeriv L z‖ ≤ A * |y| ^ 2 := by
  obtain ⟨L, lo, hi, A, hA, hL, he, hlo, hhi, hF⟩ :=
    exists_manuscriptFiniteHecke_horizontal_contours F ν η μ hν χ
  obtain ⟨T, D, hT, hD, hG⟩ := manuscriptHeckeArchGamma_high_strip F χ S hs hu t
  let G := manuscriptHeckeArchGamma F χ S hs hu t
  refine ⟨G * L, lo, hi, A+D, add_nonneg hA hD,
    (manuscriptHeckeArchGamma_meromorphic F χ S hs hu t).mul hL.meromorphicOn, ?_, hlo, hhi, ?_⟩
  · intro z hz
    rw [manuscriptCompletedHeckeEuler_eq_archGamma_mul]
    exact congrArg (G z * ·) (he hz)
  filter_upwards [tendsto_atBot.mp hlo (-T), tendsto_atTop.mp hhi T] with j hj₁ hj₂
  intro x hx y hy
  let z : ℂ := ⟨x, y⟩
  have hY : T ≤ |y| := by
    rcases mem_insert_iff.mp hy with rfl | h
    · exact (by linarith : T ≤ -(lo j)).trans (neg_le_abs _)
    · rw [mem_singleton_iff.mp h]
      exact hj₂.trans (le_abs_self _)
  obtain ⟨ha, hn, hf⟩ := hF j x hx y hy
  obtain ⟨ha', hn', hg⟩ := hG z hx hY
  have hAn : AnalyticAt ℂ (G * L) z := ha'.fun_mul ha
  have hne : (G * L) z ≠ 0 := mul_ne_zero hn' hn
  refine ⟨hAn, hne, hAn.deriv.fun_div hAn hne, ?_⟩
  change ‖logDeriv (fun w ↦ G w * L w) z‖ ≤ _
  rw [logDeriv_mul _ hn' hn ha'.differentiableAt ha.differentiableAt, add_mul]
  have hY₁ : 1 ≤ |y| := hT.trans hY
  have hD' : D * |y| ≤ D * |y| ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hY₁) (abs_nonneg y)]) hD
  exact (norm_add_le _ _).trans (add_comm (D * |y| ^ 2) _ ▸ add_le_add (hg.trans hD') hf)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem manuscriptHeckeArchGamma_regular_pos (t : ℝ) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (manuscriptHeckeArchGamma F χ S hs hu t) z ∧
      manuscriptHeckeArchGamma F χ S hs hu t z ≠ 0 := by
  let D (w : ℂ) := archimedeanNumberFieldZetaDenominator F (rparams F χ S hs hu)
    (cparams F χ S hs hu) (w - (t : ℂ) * I)
  have hD : AnalyticAt ℂ D z :=
    (archimedeanNumberFieldZetaDenominator_analytic F _ _ (z - (t : ℂ) * I)).comp
      (f := fun w : ℂ => w - (t : ℂ) * I) (analyticAt_id.sub analyticAt_const)
  have hDne : D z ≠ 0 := by
    apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
    · intro i
      simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, sLocalRealArchParameters_re] using hz
    · intro i
      simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, sLocalComplexArchParameters_re] using hz
  refine ⟨(analyticAt_const.fun_mul (hD.inv hDne)).congr (.of_forall fun w =>
    (manuscriptHeckeArchGamma_eq F χ S hs hu t w).symm), ?_⟩
  rw [manuscriptHeckeArchGamma_eq]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (by norm_num))) (inv_ne_zero hDne)

private theorem logDeriv_congr_nhds {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

private theorem normalized_germ_of_analytic {f g : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicOn f univ) (hg : AnalyticAt ℂ g z)
    (he : f =ᶠ[𝓝[≠] z] g) : toMeromorphicNFOn f univ =ᶠ[𝓝 z] g := by
  have hnorm := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)
  exact (hnorm.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg.meromorphicNFAt).mp
    ((hf.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).trans he)

include μ hν in
/-- The normalized continuation agrees with the actual Euler product and
has regular, polynomially bounded logarithmic derivative on the line of real part two. -/
theorem manuscriptCompletedHecke_normalized_right_contour (t : ℝ) (L : ℂ → ℂ)
    (hL : MeromorphicOn L univ)
    (he : EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re}) :
    let W := toMeromorphicNFOn L univ
    EqOn W (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
    (∀ z : ℂ, 1 < z.re → AnalyticAt ℂ W z ∧ W z ≠ 0) ∧
    ∃ T A : ℝ, 1 ≤ T ∧ 0 ≤ A ∧ ∀ y : ℝ,
      let z : ℂ := ⟨2, y⟩
      AnalyticAt ℂ W z ∧ W z ≠ 0 ∧ AnalyticAt ℂ (logDeriv W) z ∧
        (T ≤ |y| → ‖logDeriv W z‖ ≤ A * |y| ^ 2) := by
  intro W
  obtain ⟨f, u, _, hF, hFe, hFana, _⟩ :=
    exists_manuscriptFiniteHecke_polynomial_strips F ν η μ hν χ
  let G := manuscriptHeckeArchGamma F χ S hs hu t
  let P := G * f
  have hP : MeromorphicOn P univ := (manuscriptHeckeArchGamma_meromorphic F χ S hs hu t).mul hF
  have hPe : EqOn P (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} := by
    intro z hz
    rw [manuscriptCompletedHeckeEuler_eq_archGamma_mul]
    exact congrArg (G z * ·) (hFe hz)
  have hFa (z : ℂ) (hz : 1 < z.re) : AnalyticAt ℂ f z := by
    apply hFana z <;> intro heq
    · rw [heq] at hz
      norm_num [Complex.mul_re] at hz
    · rw [heq] at hz
      norm_num [Complex.add_re, Complex.mul_re] at hz
  have hReg (z : ℂ) (hz : 1 < z.re) :
      AnalyticAt ℂ G z ∧ G z ≠ 0 ∧ AnalyticAt ℂ f z ∧ f z ≠ 0 := by
    obtain ⟨hG, hGne⟩ := manuscriptHeckeArchGamma_regular_pos F χ S hs hu t (zero_lt_one.trans hz)
    refine ⟨hG, hGne, hFa z hz, ?_⟩
    rw [hFe hz]
    exact heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F χ _) hz
  have hWP (z : ℂ) (hz : 1 < z.re) : W =ᶠ[𝓝 z] P := by
    obtain ⟨hG, _, hF', _⟩ := hReg z hz
    exact normalized_germ_of_analytic hL (hG.fun_mul hF')
      (globalHeckeContinuation_unique_germ hL hP he hPe z)
  have hWReg (z : ℂ) (hz : 1 < z.re) : AnalyticAt ℂ W z ∧ W z ≠ 0 := by
    obtain ⟨hGa, hGne, hFa', hFne⟩ := hReg z hz
    have heq := hWP z hz
    exact ⟨(hGa.fun_mul hFa').congr heq.symm, heq.eq_of_nhds ▸ mul_ne_zero hGne hFne⟩
  refine ⟨fun z hz => (hWP z hz).eq_of_nhds.trans (hPe hz), hWReg, ?_⟩
  obtain ⟨T,D,hT,hD,hG⟩ := manuscriptHeckeArchGamma_high_strip F χ S hs hu t
  let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
  obtain ⟨M, hM, hMbound⟩ := heckePrimePowerTerm_majorant F c
    (norm_heckeEulerCoefficient_le_one F χ _) (a := 2) (by norm_num)
  have hM₀ : ∀ j, 0 ≤ M j := fun j => (norm_nonneg _).trans (hMbound j 2 (by norm_num))
  let B := ∑' j, M j
  have hB : 0 ≤ B := tsum_nonneg hM₀
  refine ⟨T, D+B, hT, add_nonneg hD hB, fun y => ?_⟩
  let z : ℂ := ⟨2,y⟩
  have hz : 1 < z.re := by norm_num [z]
  obtain ⟨hGa, hGne, hFa', hFne⟩ := hReg z hz
  obtain ⟨hwa, hwn⟩ := hWReg z hz
  refine ⟨hwa, hwn, hwa.deriv.fun_div hwa hwn, fun hy => ?_⟩
  have hFlog : ‖logDeriv f z‖ ≤ B := by
    have hnear : ∀ᶠ w : ℂ in 𝓝 z, 1 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    have hfg : f =ᶠ[𝓝 z] manuscriptFiniteHeckeEuler F χ := hnear.mono hFe
    rw [logDeriv_congr_nhds hfg, ← norm_neg]
    change ‖-logDeriv (fun s ↦ ∏' v, heckeEulerFactor F c v s) z‖ ≤ B
    rw [neg_logDeriv_heckeEulerProduct F c (norm_heckeEulerCoefficient_le_one F χ _) hz]
    have hS := summable_norm_heckePrimePowerTerm F c (norm_heckeEulerCoefficient_le_one F χ _) hz
    exact (norm_tsum_le_tsum_norm hS).trans (hS.tsum_le_tsum (fun j => hMbound j z le_rfl) hM)
  have hGlog := (hG z (by norm_num [z]) hy).2.2
  rw [logDeriv_congr_nhds (hWP z hz)]
  change ‖logDeriv (fun w ↦ G w * f w) z‖ ≤ (D+B) * |y|^2
  rw [logDeriv_mul z hGne hFne hGa.differentiableAt hFa'.differentiableAt, add_mul]
  have hy' : 1 ≤ |y| := hT.trans hy
  have hYsq : 1 ≤ |y| ^ 2 := one_le_pow₀ hy'
  exact (norm_add_le _ _).trans (add_le_add
    (hGlog.trans (mul_le_mul_of_nonneg_left (by nlinarith) hD))
    (hFlog.trans (by simpa using mul_le_mul_of_nonneg_left hYsq hB)))

include μ hν in
/-- A single normalized continuation has the required edge estimates on
rectangles exhausting the strip from minus one to two. -/
theorem exists_manuscriptCompletedHecke_contour_edges {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ (L : ℂ → ℂ) (lo hi : ℕ → ℝ) (A B T : ℝ),
      MeromorphicNFOn L univ ∧ EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      (∀ z : ℂ, z.re < 0 ∨ 1 < z.re → meromorphicOrderAt L z = 0) ∧
      0 ≤ A ∧ 0 ≤ B ∧ 1 ≤ T ∧ Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
      (∀ᶠ j in atTop, ∀ x ∈ Icc (-1 : ℝ) 2, ∀ y ∈ ({lo j,hi j} : Set ℝ),
        let z : ℂ := ⟨x,y⟩
        AnalyticAt ℂ L z ∧ L z ≠ 0 ∧ AnalyticAt ℂ (logDeriv L) z ∧
          ‖logDeriv L z‖ ≤ A * |y| ^ 2) ∧
      (∀ x ∈ ({-1,2} : Set ℝ), ∀ y : ℝ,
        let z : ℂ := ⟨x,y⟩
        AnalyticAt ℂ L z ∧ L z ≠ 0 ∧ AnalyticAt ℂ (logDeriv L) z ∧
          (T ≤ |y| → ‖logDeriv L z‖ ≤ B * |y| ^ 2)) ∧
      ∃ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
        (hUχ : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
          (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))
        (V : ℂ → ℂ), MeromorphicNFOn V univ ∧
        EqOn V (manuscriptCompletedHeckeEuler F χ⁻¹ U hU hUχ (-t)) {z | 1 < z.re} ∧
        ∀ y : ℝ, logDeriv L ⟨-1,y⟩ = -logDeriv V ⟨2,-y⟩ -
          (Real.log (heckeDiscriminantConductor F χ) : ℂ) := by
  obtain ⟨W, lo, hi, A, hA, hW, hWe, hlo, hhi, hHoriz⟩ :=
    exists_manuscriptCompletedHecke_horizontal_contours F χ S hs hu ν η μ hν t
  let L := toMeromorphicNFOn W univ
  have hL : MeromorphicNFOn L univ := meromorphicNFOn_toMeromorphicNFOn W univ
  obtain ⟨he, hRightReg, T₁, B₁, hT₁, hB₁, hRight⟩ :=
    manuscriptCompletedHecke_normalized_right_contour F χ S hs hu ν η μ hν t W hW hWe
  obtain ⟨U, hU, hUχ, Q, Q', a, hQ, hQ', hQe, hQ'e, ha, hRef, _⟩ :=
    exists_manuscriptCompletedHecke_conductorReflection F η ν μ hν χ S hs hu ht
  let V := toMeromorphicNFOn Q' univ
  obtain ⟨hVe, hDualReg, T₂, B₂, _, hB₂, hDual⟩ :=
    manuscriptCompletedHecke_normalized_right_contour F χ⁻¹ U hU hUχ ν η μ hν (-t) Q' hQ' hQ'e
  let k := (Real.log (heckeDiscriminantConductor F χ) : ℂ)
  let E (z : ℂ) := a * exp (k * (z - 1 / 2))
  have hE (p : ℂ) : AnalyticAt ℂ E p := by unfold E; fun_prop
  have hEne (p : ℂ) : E p ≠ 0 := mul_ne_zero ha (exp_ne_zero _)
  have hRefN (p : ℂ) : (fun z ↦ V (1 - z)) =ᶠ[𝓝[≠] p] L * E := by
    have hF := globalHeckeContinuation_unique_germ hL.meromorphicOn hQ he hQe p
    have hD := (reflect_punctured p).eventually (hQ'.toMeromorphicNFOn_eq_self_on_nhdsNE
      (mem_univ (1-p)))
    filter_upwards [hF, hD, hRef p] with z h₁ h₂ h₃
    change V (1-z) = Q' (1-z) at h₂
    change Q' (1-z) = Q z * E z at h₃
    change V (1-z) = L z * E z
    rw [h₂, h₃, h₁]
  let T := max T₁ T₂
  let B := B₁ + B₂ + ‖k‖
  have hT : 1 ≤ T := hT₁.trans (le_max_left _ _)
  have hLeftReg (p : ℂ) (hp : p.re < 0) : AnalyticAt ℂ L p ∧ L p ≠ 0 := by
    obtain ⟨hVa, hVne⟩ := hDualReg (1-p) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
    let P (z : ℂ) := V (1-z) / E z
    have hPa : AnalyticAt ℂ P p :=
      (hVa.comp (f := fun z : ℂ ↦ 1-z) (analyticAt_const.sub analyticAt_id)).fun_div (hE _) (hEne _)
    have hEq : L =ᶠ[𝓝[≠] p] P := by
      have hEv : ∀ᶠ z in 𝓝[≠] p, E z ≠ 0 := .of_forall hEne
      filter_upwards [hRefN p, hEv] with z hz hn
      change V (1-z) = L z * E z at hz
      change L z = V (1-z) / E z
      rw [hz, mul_div_cancel_right₀ _ hn]
    have hLg : L =ᶠ[𝓝 p] P :=
      ((hL (mem_univ p)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hPa.meromorphicNFAt).mp hEq
    exact ⟨hPa.congr hLg.symm, hLg.eq_of_nhds ▸ div_ne_zero hVne (hEne _)⟩
  have hRefY (y : ℝ) : logDeriv L ⟨-1,y⟩ = -logDeriv V ⟨2,-y⟩ - k := by
    let p : ℂ := ⟨-1,y⟩
    have hr : 1 - p = (⟨2,-y⟩ : ℂ) := by
      apply Complex.ext <;> norm_num [p, Complex.sub_re, Complex.sub_im]
    obtain ⟨hVa, _, _, _⟩ := hDual (-y)
    change AnalyticAt ℂ V (⟨2,-y⟩ : ℂ) at hVa
    rw [← hr] at hVa
    obtain ⟨hLa,hLn⟩ := hLeftReg p (by norm_num [p])
    change logDeriv L p = _
    rw [logDeriv_of_reflection hLa hVa (hE p) hLn (hEne p) (hRefN p), hr]
    exact congrArg ((-logDeriv V ⟨2,-y⟩) - ·) (logDeriv_conductor_multiplier a k ha p)
  refine ⟨L, lo, hi, A, B, T, hL, he, ?_, hA, by positivity, hT, hlo, hhi, ?_, ?_,
    U, hU, hUχ, V, meromorphicNFOn_toMeromorphicNFOn _ _, hVe, hRefY⟩
  · intro z hz
    exact ((hL (mem_univ z)).meromorphicOrderAt_eq_zero_iff).mpr
      ((hz.elim (hLeftReg z) (hRightReg z)).2)
  · filter_upwards [hHoriz] with j hj
    intro x hx y hy
    let z : ℂ := ⟨x,y⟩
    obtain ⟨hZa, hZn, _, hZb⟩ := hj x hx y hy
    have hh : L =ᶠ[𝓝 z] W := normalized_germ_of_analytic hW hZa EventuallyEq.rfl
    have hLa := hZa.congr hh.symm
    have hLn : L z ≠ 0 := hh.eq_of_nhds ▸ hZn
    exact ⟨hLa, hLn, hLa.deriv.fun_div hLa hLn, (logDeriv_congr_nhds hh).symm ▸ hZb⟩
  · intro x hx y
    rcases mem_insert_iff.mp hx with rfl | hx
    · let p : ℂ := ⟨-1,y⟩
      obtain ⟨_, _, _, hVb⟩ := hDual (-y)
      obtain ⟨hLa,hLn⟩ := hLeftReg p (by norm_num [p])
      refine ⟨hLa, hLn, hLa.deriv.fun_div hLa hLn, fun hy => ?_⟩
      rw [hRefY y]
      have hB := hVb (by rw [abs_neg]; exact (le_max_right _ _).trans hy)
      have hy' := hT.trans hy
      have hYsq : 1 ≤ |y| ^ 2 := one_le_pow₀ hy'
      have e₁ := (norm_sub_le (-logDeriv V ⟨2,-y⟩) k)
      rw [norm_neg] at e₁
      have e₂ : ‖logDeriv V ⟨2,-y⟩‖ ≤ B₂ * |y| ^ 2 := by simpa only [abs_neg] using hB
      have e₃ : ‖k‖ ≤ ‖k‖ * |y| ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hYsq (norm_nonneg k)
      refine e₁.trans ((add_le_add e₂ e₃).trans ?_)
      dsimp only [B]
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · rw [mem_singleton_iff.mp hx]
      obtain ⟨ha', hn, hd, hb⟩ := hRight y
      refine ⟨ha', hn, hd, fun hy => (hb ((le_max_left _ _).trans hy)).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (by dsimp [B]; linarith [norm_nonneg k]) (by positivity)

include μ hν in
/-- The centered Mellin test gives the completed Hecke contour comparison.
A summable divisor series has the integral difference as its unordered sum. -/
theorem exists_manuscriptCompletedHecke_centered_residue_contour
    {t : ℝ} (ht : HasHeckeHeight F χ t)
    (g : PositiveRealExponentialDecay (univ : Set ℝ)) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} ∧
      let Φ := fun z => mellin (g.val ∘ Real.log) (z - 1 / 2)
      let J := fun x y : ℝ => Φ ⟨x, y⟩ * logDeriv L ⟨x, y⟩
      Integrable (J (-1)) ∧ Integrable (J 2) ∧
      ((Summable (fun z => (MeromorphicOn.divisor L univ z : ℂ) * Φ z)) →
        HasSum (fun z => (MeromorphicOn.divisor L univ z : ℂ) * Φ z)
          (((∫ y : ℝ, J 2 y) - (∫ y : ℝ, J (-1) y)) / (2 * (Real.pi : ℂ)))) ∧
      ∃ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
        (hUχ : globalNormOneCharacter F (heckeNormOneRestriction F χ⁻¹) ∈
          (sUnramified F U : Set (QuasiCharacter (IdeleClass F))))
        (V : ℂ → ℂ), MeromorphicNFOn V univ ∧
        EqOn V (manuscriptCompletedHeckeEuler F χ⁻¹ U hU hUχ (-t)) {z | 1 < z.re} ∧
        ∀ y : ℝ, logDeriv L ⟨-1,y⟩ = -logDeriv V ⟨2,-y⟩ -
          (Real.log (heckeDiscriminantConductor F χ) : ℂ) := by
  obtain ⟨L, lo, hi, A, B, T, hL, he, hZero, hA, hB, _, hlo, hhi, hHoriz, hVert, hRef⟩ :=
    exists_manuscriptCompletedHecke_contour_edges F χ S hs hu ν η μ hν ht
  obtain ⟨hSch, _⟩ := exponentialLogProfile_mellinHypotheses g
  let Φ (z : ℂ) := mellin (g.val ∘ Real.log) (z - 1 / 2)
  have hD : MellinAffineStripBounds Φ (mellinWeight (g.val ∘ Real.log) (-(1/2))) (-1) 2 := by
    have h := (mellin_affine_exponential_bounds hSch (a := -1) (b := 2) (by norm_num) (-(1/2))).1
    simpa [Φ, sub_eq_add_neg] using h
  obtain ⟨C₃, _, h₃, _⟩ := hD.2 3
  obtain ⟨C₄, _, h₄, _⟩ := hD.2 4
  have hz (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I) = ⟨x,y⟩ := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  have hN : ∃ z : ℂ, meromorphicOrderAt L z ≠ ⊤ := by
    refine ⟨2, ?_⟩
    rw [hZero 2 (Or.inr (by norm_num))]
    simp
  have hSupport (z : ℂ) (hz : MeromorphicOn.divisor L univ z ≠ 0) : z.re ∈ Icc (-1 : ℝ) 2 := by
    have hInd : ¬ (z.re < 0 ∨ 1 < z.re) := by
      intro h
      apply hz
      rw [hL.meromorphicOn.divisor_apply (mem_univ z), hZero z h]
      simp
    exact ⟨by linarith [not_lt.mp (fun h => hInd (Or.inl h))],
      by linarith [not_lt.mp (fun h => hInd (Or.inr h))]⟩
  have hh : ∃ a c : ℝ, 0 ≤ a ∧ ∀ᶠ j in atTop, ∀ x ∈ Icc (-1 : ℝ) 2,
      ∀ y ∈ ({lo j, hi j} : Set ℝ),
        let z : ℂ := (x : ℂ) + (y : ℂ) * I
        AnalyticAt ℂ (logDeriv L) z ∧ ‖logDeriv L z‖ ≤ a * |y| ^ (2 : ℕ) ∧
          |y| ^ (2 + 1 : ℕ) * ‖Φ z‖ ≤ c := by
    refine ⟨A, C₃, hA, ?_⟩
    filter_upwards [hHoriz] with j hj
    intro x hx y hy
    rw [hz]
    obtain ⟨_, _, hA', hb⟩ := hj x hx y hy
    exact ⟨hA', hb, h₃ ⟨x,y⟩ hx.1 hx.2⟩
  have hv (x : ℝ) (hx : x ∈ ({-1,2} : Set ℝ)) :
      (∀ y : ℝ, AnalyticAt ℂ (logDeriv L) ((x : ℂ) + (y : ℂ) * I)) ∧
      ∃ b c r : ℝ, 0 ≤ b ∧ ∀ y : ℝ, r ≤ |y| →
        ‖logDeriv L ((x : ℂ) + (y : ℂ) * I)‖ ≤ b * |y| ^ (2 : ℕ) ∧
          |y| ^ (2 + 2 : ℕ) * ‖Φ ((x : ℂ) + (y : ℂ) * I)‖ ≤ c := by
    refine ⟨fun y => by rw [hz]; exact (hVert x hx y).2.2.1, B, C₄, T, hB, fun y hy => ?_⟩
    rw [hz]
    have hx' : x ∈ Icc (-1 : ℝ) 2 := by
      rcases mem_insert_iff.mp hx with he | he
      · rw [he]; norm_num
      · rw [mem_singleton_iff.mp he]; norm_num
    exact ⟨(hVert x hx y).2.2.2 hy, h₄ ⟨x,y⟩ hx'.1 hx'.2⟩
  obtain ⟨hI₁, hI₂, _, hSum⟩ := asymptotic_residue_logDeriv (a := -1) (b := 2) (m := 2)
    (by norm_num) hL.meromorphicOn hN (fun z _ => hD.1.analyticAt z) hlo hhi hh hv
  simp_rw [hz] at hI₁ hI₂ hSum
  refine ⟨L, hL, he, hI₁, hI₂, fun hs => ?_, hRef⟩
  have h := hSum hSupport hs
  convert h using 1
  rw [← mul_sub, mul_comm (2 * (Real.pi : ℂ)) I, mul_div_mul_left _ _ I_ne_zero]

include μ hν in
/-- In sufficiently high moving disks, completed Hecke divisor coefficients
in the critical strip are exactly the analytic multiplicities of the finite factor. -/
theorem manuscriptCompletedHecke_high_divisor_disk
    (t : ℝ) (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (he : EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re}) :
    ∃ (f : ℂ → ℂ) (N : ℕ) (T : ℝ), 0 < N ∧ 2 ≤ T ∧
      ∀ y : ℝ, T ≤ |y| →
        let c : ℂ := ⟨2,y⟩
        {p | p ∈ Metric.closedBall c 4 ∧ analyticOrderNatAt f p ≠ 0}.Finite ∧
        (∑ᶠ p ∈ Metric.closedBall c 4, (analyticOrderNatAt f p : ℝ)) ≤
          (N : ℝ) * Real.log |y| / Real.log 2 ∧
        ∀ p ∈ Metric.closedBall c 4, p.re ∈ Icc (0 : ℝ) 1 →
          MeromorphicOn.divisor L univ p = (analyticOrderNatAt f p : ℤ) := by
  obtain ⟨f, N, T₁, hN, hT₁, hf, hfe, hDisk⟩ :=
    exists_manuscriptFiniteHecke_disk_zero_estimates F ν η μ hν χ
  let G := manuscriptHeckeArchGamma F χ S hs hu t
  obtain ⟨T₂, D, hT₂, hD, hG⟩ := manuscriptHeckeArchGamma_high_strip F χ S hs hu t
  have hProd : MeromorphicOn (G * f) univ :=
    (manuscriptHeckeArchGamma_meromorphic F χ S hs hu t).mul hf.meromorphicOn
  have hAgree : EqOn (G * f) (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re} := by
    intro z hz
    rw [manuscriptCompletedHeckeEuler_eq_archGamma_mul]
    exact congrArg (G z * ·) (hfe hz)
  have hTwo : f 2 ≠ 0 := by
    rw [hfe (show 1 < (2 : ℂ).re by norm_num)]
    exact heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F χ _) (by norm_num)
  have hOrd₂ : meromorphicOrderAt f 2 = 0 := (hf (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hTwo
  have hFin (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ :=
    (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨2, mem_univ _⟩, by rw [hOrd₂]; simp⟩ ⟨z, mem_univ _⟩
  let T := max T₁ (T₂ + 4)
  refine ⟨f, N, T, hN, hT₁.trans (le_max_left _ _), fun y hy => ?_⟩
  obtain ⟨hAn, hc, hCount, _⟩ := hDisk y ((le_max_left _ _).trans hy)
  have hFinDisk := RiemannMasullo.finite_zeros_closedBall (by norm_num : (0 : ℝ) ≤ 4)
    (hAn.mono (Metric.closedBall_subset_closedBall (by norm_num))) hc
  refine ⟨hFinDisk.subset (fun p hp => ⟨hp.1, apply_eq_zero_of_analyticOrderNatAt_ne_zero hp.2⟩),
    hCount, fun p hp hs => ?_⟩
  have hIm : |p.im-y| ≤ 4 := (Complex.abs_im_le_norm (p - (⟨2,y⟩ : ℂ))).trans
    (mem_closedBall_iff_norm.mp hp)
  have hAbs := (abs_abs_sub_abs_le_abs_sub p.im y).trans hIm
  have hGt : T₂ ≤ |p.im| := by
    have h₁ := (le_max_right T₁ (T₂+4)).trans hy
    linarith [(abs_le.mp hAbs).1]
  obtain ⟨hGa, hGne, _⟩ := hG p ⟨by linarith [hs.1], by linarith [hs.2]⟩ hGt
  have hfa := hAn p (Metric.closedBall_subset_closedBall (by norm_num) hp)
  have hG₀ : meromorphicOrderAt G p = 0 := hGa.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hGne
  have hEq := globalHeckeContinuation_unique_germ hL hProd he hAgree p
  rw [hL.divisor_apply (mem_univ p), meromorphicOrderAt_congr hEq,
    meromorphicOrderAt_mul hGa.meromorphicAt hfa.meromorphicAt, hG₀, zero_add]
  have hNat : analyticOrderAt f p ≠ ⊤ := by
    intro hTop
    exact hFin p (by rw [hfa.meromorphicOrderAt_eq, hTop]; simp)
  rw [hfa.meromorphicOrderAt_eq, ← ENat.natCast_toNat hNat, ENat.map_natCast]
  rfl

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem manuscriptHeckeRealGammaShift_re_nonneg (t : ℝ) (v : R F) :
    0 ≤ (manuscriptHeckeRealGammaShift F χ S hs hu t v).re := by
  simp [manuscriptHeckeRealGammaShift, Complex.add_re, Complex.sub_re, Complex.mul_re,
    sLocalRealArchParameters_re]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem manuscriptHeckeComplexGammaShift_re_nonneg (t : ℝ) (v : C F) :
    0 ≤ (manuscriptHeckeComplexGammaShift F χ S hs hu t v).re := by
  simp [manuscriptHeckeComplexGammaShift, Complex.add_re, Complex.sub_re, Complex.mul_re,
    sLocalComplexArchParameters_re]
  positivity

private theorem scaledGamma_regular_pos_argument (k P : ℝ) (b z : ℂ)
    (h : 0 < ((k : ℂ) * (z + b)).re) :
    AnalyticAt ℂ (scaledGamma k P b) z ∧ scaledGamma k P b z ≠ 0 := by
  apply scaledGamma_analytic_ne_zero
  intro n he
  have hre := congrArg Complex.re he
  rw [he] at h
  simp at h
  exact h.not_ge (Nat.cast_nonneg _)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem manuscriptHeckeArchGamma_right_logDeriv_sum (t : ℝ) {z : ℂ} (hz : 0 < z.re) :
    logDeriv (manuscriptHeckeArchGamma F χ S hs hu t) z =
      (∑ v : R F, logDeriv (scaledGamma (1 / 2) Real.pi
        (manuscriptHeckeRealGammaShift F χ S hs hu t v)) z) +
      ∑ v : C F, logDeriv (scaledGamma 1 (2 * Real.pi)
        (manuscriptHeckeComplexGammaShift F χ S hs hu t v)) z := by
  let G (v : R F) := scaledGamma (1 / 2) Real.pi (manuscriptHeckeRealGammaShift F χ S hs hu t v)
  let H (v : C F) := scaledGamma 1 (2 * Real.pi) (manuscriptHeckeComplexGammaShift F χ S hs hu t v)
  have hG (v : R F) : AnalyticAt ℂ (G v) z ∧ G v z ≠ 0 := by
    refine scaledGamma_regular_pos_argument (1 / 2) Real.pi _ z ?_
    have hp := add_pos_of_pos_of_nonneg hz (manuscriptHeckeRealGammaShift_re_nonneg F χ S hs hu t v)
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.add_re] using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hp
  have hH (v : C F) : AnalyticAt ℂ (H v) z ∧ H v z ≠ 0 := by
    apply scaledGamma_regular_pos_argument
    simpa only [Complex.ofReal_one, one_mul, Complex.add_re] using
      add_pos_of_pos_of_nonneg hz (manuscriptHeckeComplexGammaShift_re_nonneg F χ S hs hu t v)
  change logDeriv (fun w => (∏ v, G v w) * ∏ v, H v w) z = _
  rw [logDeriv_mul (f := fun w => ∏ v, G v w) (g := fun w => ∏ v, H v w) z
    (Finset.prod_ne_zero_iff.mpr fun v _ => (hG v).2)
    (Finset.prod_ne_zero_iff.mpr fun v _ => (hH v).2)
    (Finset.analyticAt_fun_prod _ (fun v _ => (hG v).1)).differentiableAt
    (Finset.analyticAt_fun_prod _ (fun v _ => (hH v).1)).differentiableAt,
    logDeriv_prod (s := Finset.univ) (f := G) (fun v _ => (hG v).2) (fun v _ => (hG v).1.differentiableAt),
    logDeriv_prod (s := Finset.univ) (f := H) (fun v _ => (hH v).2) (fun v _ => (hH v).1.differentiableAt)]

include μ hν in
/-- On the right half-plane the completed logarithmic derivative splits
into the logarithmic derivatives of the actual finite and gamma products. -/
theorem manuscriptCompletedHecke_right_logDeriv_split (t : ℝ) (L : ℂ → ℂ)
    (he : EqOn L (manuscriptCompletedHeckeEuler F χ S hs hu t) {z | 1 < z.re})
    {z : ℂ} (hz : 1 < z.re) :
    logDeriv L z = logDeriv (manuscriptFiniteHeckeEuler F χ) z +
      logDeriv (manuscriptHeckeArchGamma F χ S hs hu t) z := by
  obtain ⟨f, u, _, _, hFe, hFa, _⟩ :=
    exists_manuscriptFiniteHecke_polynomial_strips F ν η μ hν χ
  let G := manuscriptHeckeArchGamma F χ S hs hu t
  obtain ⟨hG, hGne⟩ := manuscriptHeckeArchGamma_regular_pos F χ S hs hu t (zero_lt_one.trans hz)
  have hn : ∀ᶠ w : ℂ in 𝓝 z, 1 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hf : AnalyticAt ℂ f z := by
    apply hFa z <;> intro hEq
    · rw [hEq] at hz
      norm_num [Complex.mul_re] at hz
    · rw [hEq] at hz
      norm_num [Complex.add_re, Complex.mul_re] at hz
  have hfne : f z ≠ 0 := by
    rw [hFe hz]
    exact heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F χ _) hz
  have hLF : L =ᶠ[𝓝 z] fun w => G w * f w := hn.mono fun w hw => by
    change L w = G w * f w
    rw [he hw, manuscriptCompletedHeckeEuler_eq_archGamma_mul, hFe hw]
  rw [logDeriv_congr_nhds hLF, logDeriv_mul z hGne hfne hG.differentiableAt hf.differentiableAt,
    logDeriv_congr_nhds (hn.mono hFe), add_comm]

end

end Masullo
