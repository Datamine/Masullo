import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Complex Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology ContDiff

namespace Masullo

/-- The Schwartz condition for a Mellin weight, in the coordinate
`t = exp (-x)`. Reflection of the logarithmic coordinate preserves the
ordinary Schwartz space. -/
def MellinSchwartzAt (f : ℝ → ℂ) (σ : ℝ) : Prop :=
  ∃ g : 𝓢(ℝ, ℂ), ⇑g = fun x => Real.exp (-σ * x) • f (Real.exp (-x))

private noncomputable def laplaceKernel (h : ℝ → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-s * (x : ℂ)) * h x

private theorem mellin_eq_reflected_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ x, laplaceKernel (fun u => f (Real.exp (-u))) s x := by
  rw [mellin_eq_fourier, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  have hcoef : -2 * Real.pi * x * (s.im / (2 * Real.pi)) = -(s.im * x) := by
    field_simp
  have he : ((↑(-(s.im * x)) : ℂ) * I) +
      ((-s.re * x : ℝ) : ℂ) = -s * (x : ℂ) := by
    conv_rhs => rw [← Complex.re_add_im s]
    push_cast
    ring
  rw [laplaceKernel]
  simp only [Real.inner_apply, real_smul, ofReal_exp, smul_eq_mul, ← mul_assoc,
    ← Complex.exp_add, hcoef, he]

/-- Mellin integration in the increasing real logarithmic coordinate. -/
theorem mellin_eq_log_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f (Real.exp x) := by
  rw [mellin_eq_reflected_integral, ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [laplaceKernel]

private theorem exp_re_between_le {a b r : ℝ} (ha : a ≤ r) (hb : r ≤ b) (x : ℝ) :
    Real.exp (-r * x) ≤ Real.exp (-a * x) + Real.exp (-b * x) := by
  by_cases hx : 0 ≤ x
  · refine (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ha) hx)).trans ?_
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · refine (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (neg_le_neg hb) (le_of_not_ge hx))).trans ?_
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

private theorem laplaceKernel_le {h : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : ℝ) :
    ‖laplaceKernel h s x‖ ≤
      ‖Real.exp (-a * x) • h x‖ + ‖Real.exp (-b * x) • h x‖ := by
  rw [laplaceKernel, norm_mul, norm_exp]
  have he : (-s * (x : ℂ)).re = -s.re * x := by simp [Complex.mul_re]
  rw [he, norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _),
    Real.norm_of_nonneg (Real.exp_nonneg _), ← add_mul]
  exact mul_le_mul_of_nonneg_right (exp_re_between_le ha hb x) (norm_nonneg _)

private theorem laplaceKernel_continuous_x {h : ℝ → ℂ} (hh : Continuous h) (s : ℂ) :
    Continuous (laplaceKernel h s) := by
  unfold laplaceKernel
  fun_prop

private theorem laplaceKernel_hasDerivAt (h : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun w => laplaceKernel h w x) (-(x : ℂ) * laplaceKernel h s x) s := by
  have hd := (((hasDerivAt_id' s).neg.mul_const (x : ℂ)).cexp).mul_const (h x)
  simpa [laplaceKernel, mul_assoc, mul_left_comm, mul_comm] using hd

private theorem laplace_regular_on_closed_strip {h : ℝ → ℂ} {a b : ℝ}
    (hh : Continuous h) (A B : 𝓢(ℝ, ℂ))
    (hA : ⇑A = fun x => Real.exp (-a * x) • h x)
    (hB : ⇑B = fun x => Real.exp (-b * x) • h x) :
    ContinuousOn (fun s => ∫ x, laplaceKernel h s x) (Complex.re ⁻¹' Icc a b) ∧
    DifferentiableOn ℂ (fun s => ∫ x, laplaceKernel h s x) (Complex.re ⁻¹' Ioo a b) := by
  let M (x : ℝ) := ‖A x‖ + ‖B x‖
  have hM : Integrable M := A.integrable.norm.add B.integrable.norm
  have hMf : Integrable (fun x => ‖x‖ * M x) := by
    have hi : Integrable ((fun x => ‖x‖ * ‖A x‖) + fun x => ‖x‖ * ‖B x‖) := by
      simpa only [pow_one] using (A.integrable_pow_mul volume 1).add (B.integrable_pow_mul volume 1)
    convert hi using 1
    funext x
    exact mul_add ‖x‖ ‖A x‖ ‖B x‖
  have hbd (s : ℂ) (hs : s ∈ Complex.re ⁻¹' Icc a b) (x : ℝ) :
      ‖laplaceKernel h s x‖ ≤ M x := by
    simpa only [M, congrFun hA x, congrFun hB x] using laplaceKernel_le (h := h) hs.1 hs.2 x
  have hmeas (s : ℂ) : AEStronglyMeasurable (laplaceKernel h s) volume :=
    (laplaceKernel_continuous_x hh _).aestronglyMeasurable
  have hint (s : ℂ) (hs : s ∈ Complex.re ⁻¹' Icc a b) : Integrable (laplaceKernel h s) :=
    hM.mono' (hmeas s) (Eventually.of_forall (hbd s hs))
  refine ⟨?_, ?_⟩
  · intro s hs
    apply continuousWithinAt_of_dominated
    · exact Eventually.of_forall hmeas
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact Eventually.of_forall (hbd z hz)
    · exact hM
    · exact Eventually.of_forall fun x => (laplaceKernel_hasDerivAt h s x).continuousAt.continuousWithinAt
  · intro s hs
    have hS : Complex.re ⁻¹' Ioo a b ∈ 𝓝 s :=
      (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hs
    have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := laplaceKernel h) (F' := fun z x => -(x : ℂ) * laplaceKernel h z x)
      (bound := fun x => ‖x‖ * M x) hS (Eventually.of_forall hmeas)
      (hint s ⟨hs.1.le, hs.2.le⟩)
      ((continuous_ofReal.neg.mul (laplaceKernel_continuous_x hh s)).aestronglyMeasurable)
      (Eventually.of_forall fun x z hz => by
        rw [norm_mul, norm_neg, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hbd z ⟨hz.1.le, hz.2.le⟩ x) (norm_nonneg _))
      hMf (Eventually.of_forall fun x z _ => laplaceKernel_hasDerivAt h z x)
    exact hder.2.differentiableAt.differentiableWithinAt

private theorem norm_le_abs_re_add_abs_im (s : ℂ) : ‖s‖ ≤ |s.re| + |s.im| := by
  conv_lhs => rw [← Complex.re_add_im s]
  simpa using norm_add_le (s.re : ℂ) ((s.im : ℂ) * I)

private theorem mellin_vertical_schwartz {f : ℝ → ℂ} {σ : ℝ} (hσ : MellinSchwartzAt f σ) :
    ∃ g : 𝓢(ℝ, ℂ), ⇑g = fun y => mellin f ⟨σ, y⟩ := by
  obtain ⟨g, hg⟩ := hσ
  let u : ℝˣ := Units.mk0 (1 / (2 * Real.pi)) (by positivity)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ u) (𝓕 g), ?_⟩
  funext y
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, SchwartzMap.fourier_coe,
    mellin_eq_fourier, ← hg]
  change 𝓕 (⇑g) (y * (1 / (2 * Real.pi))) = _
  rw [mul_one_div]

/-- A Schwartz logarithmic Mellin weight has a Schwartz vertical trace. -/
theorem exists_mellinVerticalSchwartz {f : ℝ → ℂ} {a : ℝ} (h : MellinSchwartzAt f a) :
    ∃ g : 𝓢(ℝ, ℂ), ⇑g = fun y => mellin f ⟨a, y⟩ :=
  mellin_vertical_schwartz h

private theorem strip_closure {a b : ℝ} (hab : a < b) :
    closure (Complex.re ⁻¹' Ioo a b) = Complex.re ⁻¹' Icc a b := by
  have openEq : Complex.re ⁻¹' Ioo a b = Ioo a b ×ℂ (univ : Set ℝ) := by
    ext z
    simp [Complex.mem_reProdIm]
  rw [openEq, Complex.closure_reProdIm, closure_Ioo hab.ne, closure_univ]
  ext z
  simp [Complex.mem_reProdIm]

private theorem bound_on_edge {f : ℝ → ℂ} {a : ℝ}
    (g : 𝓢(ℝ, ℂ)) (hg : ⇑g = fun y => mellin f ⟨a, y⟩) (n : ℕ)
    (z : ℂ) (hz : z.re = a) :
    ‖z ^ n * mellin f z‖ ≤
      (|a| + 1) ^ n * (SchwartzMap.seminorm ℝ n 0 g + SchwartzMap.seminorm ℝ 0 0 g) := by
  have hz' : z = ⟨a, z.im⟩ := Complex.ext hz rfl
  have hg' : g z.im = mellin f z := by rw [congrFun hg, ← hz']
  have hbase : ‖z‖ ≤ (|a| + 1) * max 1 |z.im| := by
    have hm : 1 ≤ max 1 |z.im| := le_max_left _ _
    have hy : |z.im| ≤ max 1 |z.im| := le_max_right _ _
    calc
      ‖z‖ ≤ |a| + |z.im| := by simpa only [hz] using norm_le_abs_re_add_abs_im z
      _ ≤ |a| * max 1 |z.im| + max 1 |z.im| :=
        add_le_add (le_mul_of_one_le_right (abs_nonneg _) hm) hy
      _ = _ := by ring
  rw [norm_mul, norm_pow, ← hg']
  calc
    ‖z‖ ^ n * ‖g z.im‖ ≤ ((|a| + 1) * max 1 |z.im|) ^ n * ‖g z.im‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase _) (norm_nonneg _)
    _ = (|a| + 1) ^ n * (max 1 |z.im| ^ n * ‖g z.im‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total |z.im| 1 with h | h
      · rw [max_eq_left h, one_pow, one_mul]
        exact (SchwartzMap.norm_le_seminorm ℝ g z.im).trans (le_add_of_nonneg_left (apply_nonneg _ _))
      · rw [max_eq_right h, ← Real.norm_eq_abs]
        exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ g n z.im).trans
          (le_add_of_nonneg_right (apply_nonneg _ _))

open Asymptotics in
private theorem strip_polynomial_growth {F : ℂ → ℂ} {a b M : ℝ} (hab : a < b)
    (hM : 0 ≤ M) (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ M) (n : ℕ) :
    ∃ c < Real.pi / (b - a), ∃ B,
      (fun z => z ^ n * F z) =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo a b)] fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  let c := Real.pi / (2 * (b - a))
  have hc : 0 < c := by dsimp [c]; positivity
  have hclt : c < Real.pi / (b - a) := by
    dsimp [c]
    rw [mul_comm, div_mul_eq_div_div]
    linarith [show 0 < Real.pi / (b - a) by positivity]
  refine ⟨c, hclt, 1, IsBigO.of_bound ((|a| + |b| + 1) ^ n * M) ?_⟩
  have hpow : ∀ᶠ y : ℝ in atTop, y ^ n ≤ Real.exp (c * y) := by
    filter_upwards [(isLittleO_pow_exp_pos_mul_atTop n hc).bound one_pos]
      with y hy
    simpa only [one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)] using
      (le_abs_self (y ^ n)).trans (by simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.exp_nonneg _)] using hy)
  have hfar : ∀ᶠ z in comap (_root_.abs ∘ Complex.im) atTop,
      1 ≤ |z.im| ∧ |z.im| ^ n ≤ Real.exp (c * |z.im|) := by
    exact (eventually_comap.mpr (by
      filter_upwards [eventually_ge_atTop (1 : ℝ), hpow] with y hy hy'
      intro z hz
      change |z.im| = y at hz
      simpa only [hz] using And.intro hy hy'))
  filter_upwards [hfar.filter_mono inf_le_left,
    (eventually_mem_principal (Complex.re ⁻¹' Ioo a b)).filter_mono inf_le_right] with z hz hs
  have hr : |z.re| ≤ |a| + |b| := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hs.1, neg_le_abs a, abs_nonneg b]
    · linarith [hs.2, le_abs_self b, abs_nonneg a]
  have hnorm : ‖z‖ ≤ (|a| + |b| + 1) * |z.im| := by
    calc
      ‖z‖ ≤ |a| + |b| + |z.im| := (norm_le_abs_re_add_abs_im z).trans (add_le_add_left hr _)
      _ ≤ (|a| + |b|) * |z.im| + |z.im| :=
        add_le_add_left (le_mul_of_one_le_right (add_nonneg (abs_nonneg a) (abs_nonneg b)) hz.1) _
      _ = _ := by ring
  rw [norm_mul, norm_pow, one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    ‖z‖ ^ n * ‖F z‖ ≤ ((|a| + |b| + 1) * |z.im|) ^ n * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (hF z hs.1.le hs.2.le) (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [mul_pow, mul_right_comm _ _ M]
      exact mul_le_mul_of_nonneg_left
        (hz.2.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right zero_le_one |>.trans (Real.add_one_le_exp _)))) (by positivity)

/-- Masullo B.2.2.3. The power bound holds for every height on the closed strip. -/
theorem mellin_uniform_riemann_lebesgue {f : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hw : ∀ σ ∈ Icc a b, MellinSchwartzAt f σ) :
    ContinuousOn (mellin f) (Complex.re ⁻¹' Icc a b) ∧
    DifferentiableOn ℂ (mellin f) (Complex.re ⁻¹' Ioo a b) ∧
    (∀ σ ∈ Icc a b, ∃ g : 𝓢(ℝ, ℂ), ⇑g = fun y => mellin f ⟨σ, y⟩) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ^ n * ‖mellin f z‖ ≤ C := by
  obtain ⟨A, hA⟩ := hw a ⟨le_rfl, hab.le⟩
  obtain ⟨B, hB⟩ := hw b ⟨hab.le, le_rfl⟩
  let h (x : ℝ) := f (Real.exp (-x))
  have hh : Continuous h := by
    have he (x : ℝ) : Real.exp (a * x) • A x = h x := by
      rw [congrFun hA, ← mul_smul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_smul]
    have hwgt : Continuous (fun x : ℝ => Real.exp (a * x)) := by fun_prop
    exact (hwgt.smul A.continuous).congr he
  have hF : mellin f = fun z => ∫ x, laplaceKernel h z x := funext (mellin_eq_reflected_integral f)
  obtain ⟨hc, hd⟩ := laplace_regular_on_closed_strip hh A B hA hB
  rw [← hF] at hc hd
  have hv (σ : ℝ) (hs : σ ∈ Icc a b) := mellin_vertical_schwartz (hw σ hs)
  refine ⟨hc, hd, hv, ?_⟩
  let M := ∫ x : ℝ, ‖A x‖ + ‖B x‖
  have hM : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hbound (z : ℂ) (ha : a ≤ z.re) (hb : z.re ≤ b) : ‖mellin f z‖ ≤ M := by
    rw [hF]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _)
      (A.integrable.norm.add B.integrable.norm)
      (Eventually.of_forall fun x => ?_))
    simpa only [congrFun hA x, congrFun hB x] using laplaceKernel_le (h := h) ha hb x
  intro n
  obtain ⟨g, hg⟩ := hv a ⟨le_rfl, hab.le⟩
  obtain ⟨k, hk⟩ := hv b ⟨hab.le, le_rfl⟩
  let C₁ := (|a| + 1) ^ n * (SchwartzMap.seminorm ℝ n 0 g + SchwartzMap.seminorm ℝ 0 0 g)
  let C₂ := (|b| + 1) ^ n * (SchwartzMap.seminorm ℝ n 0 k + SchwartzMap.seminorm ℝ 0 0 k)
  let C := max 1 (max C₁ C₂)
  refine ⟨C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro z ha hb
  have hdiff : DiffContOnCl ℂ (fun s => s ^ n * mellin f s) (Complex.re ⁻¹' Ioo a b) := by
    refine ⟨(differentiableOn_id.pow n).mul hd, ?_⟩
    rw [strip_closure hab]
    exact (continuousOn_id.pow n).mul hc
  have hPL := PhragmenLindelof.vertical_strip hdiff (strip_polynomial_growth hab hM hbound n)
    (fun w hw => (bound_on_edge g hg n w hw).trans ((le_max_left C₁ C₂).trans (le_max_right 1 _)))
    (fun w hw => (bound_on_edge k hk n w hw).trans ((le_max_right C₁ C₂).trans (le_max_right 1 _)))
    ha hb
  rw [norm_mul, norm_pow] at hPL
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (abs_im_le_norm z) _)
    (norm_nonneg _)).trans hPL

/-- The reflected logarithmic condition agrees with the manuscript's positive
logarithmic coordinate. -/
theorem mellinSchwartzAt_iff_positive_log {f : ℝ → ℂ} {σ : ℝ} :
    MellinSchwartzAt f σ ↔
      ∃ g : 𝓢(ℝ, ℂ), ⇑g = fun x => Real.exp (σ * x) • f (Real.exp x) := by
  let e : ℝ ≃L[ℝ] ℝ := LinearIsometryEquiv.neg ℝ (E := ℝ)
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g, ?_⟩
    funext x
    simpa [e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using congrFun hg (-x)
  · rintro ⟨g, hg⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g, ?_⟩
    funext x
    simpa [e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using congrFun hg (-x)

/-- A Schwartz Mellin weight gives absolute convergence at the corresponding
complex exponent. -/
theorem mellinConvergent_of_schwartzAt {f : ℝ → ℂ} {s : ℂ}
    (hs : MellinSchwartzAt f s.re) : MellinConvergent f s := by
  obtain ⟨g, hg⟩ := mellinSchwartzAt_iff_positive_log.mp hs
  rw [MellinConvergent, ← Real.range_exp, ← image_univ,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn, integrableOn_univ]
  refine (g.integrable.norm).mono' ?_ (Eventually.of_forall fun x => ?_)
  · have hlog : Continuous (fun x : ℝ => f (Real.exp x)) := by
      have he (x : ℝ) : Real.exp (-(s.re * x)) • g x = f (Real.exp x) := by
        rw [congrFun hg, ← mul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
      have hw : Continuous (fun x : ℝ => Real.exp (-(s.re * x))) := by fun_prop
      exact (hw.smul g.continuous).congr he
    have hpow : Continuous (fun x : ℝ => (Real.exp x : ℂ) ^ (s - 1)) := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      exact (Complex.continuousAt_ofReal_cpow_const (Real.exp x) (s - 1)
        (Or.inr (Real.exp_pos x).ne')).comp (Real.continuous_exp.continuousAt (x := x))
    exact (Real.continuous_exp.abs.smul (hpow.smul hlog)).aestronglyMeasurable
  · change _ ≤ ‖g x‖
    rw [congrFun hg, norm_smul, norm_smul, norm_smul, norm_abs_eq_norm,
      Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg (Real.exp_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _), sub_re, one_re]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← mul_assoc, ← Real.exp_add]
    apply le_of_eq
    congr 1
    congr 1
    ring

/-- The growth condition printed in B.2.1.7(1)(c) cannot hold on a neighborhood
of a nonzero pole, even if the value at the pole is omitted. -/
theorem tendsto_mellin_growth_weighted_norm_at_pole {F : ℂ → ℂ} {p : ℂ}
    (hp : p ≠ 0) (ho : meromorphicOrderAt F p < 0) (β : ℝ) :
    Tendsto (fun s => ‖s‖ ^ β * ‖F s‖) (𝓝[≠] p) atTop := by
  have hweight : ContinuousAt (fun s : ℂ => ‖s‖ ^ β) p :=
    (Real.continuousAt_rpow_const ‖p‖ β (Or.inl (norm_ne_zero_iff.mpr hp))).comp
      continuous_norm.continuousAt
  have hF : Tendsto (fun s => ‖F s‖) (𝓝[≠] p) atTop :=
    (tendsto_norm_atTop_iff_cobounded).mpr (tendsto_cobounded_of_meromorphicOrderAt_neg ho)
  rw [show (fun s => ‖s‖ ^ β * ‖F s‖) = (fun s => ‖F s‖ * ‖s‖ ^ β) from funext fun _ => mul_comm _ _]
  exact Filter.Tendsto.atTop_mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hp) _)
    hF hweight.continuousWithinAt.tendsto


/-- The tail integral occurring in the manuscript's vertical Lᵖ estimate. -/
noncomputable def mellinLpTail (p : ℝ) (N : ℕ) : ℝ :=
  ∫ y : ℝ in (Ioo (-(1 / 2)) (1 / 2))ᶜ, |y| ^ (-(p * (N : ℝ)))

private theorem integrableOn_mellinLpTail {q : ℝ} (hq : 2 ≤ q) :
    IntegrableOn (fun y : ℝ => |y| ^ (-q)) (Ioo (-(1 / 2)) (1 / 2))ᶜ := by
  let S : Set ℝ := (Ioo (-(1 / 2)) (1 / 2))ᶜ
  let M := 2 + 2 * (1 / 2 : ℝ) ^ (-q)
  have H : Integrable (fun y : ℝ => M * (1 + y ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  have hm : Measurable (fun y : ℝ => |y| ^ (-q)) := by fun_prop
  refine H.integrableOn.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo.compl] with y hy
  have hy0 : 1 / 2 ≤ |y| := by
    by_contra! h
    exact hy (abs_lt.mp h)
  have hypos : 0 < |y| := (by norm_num : 0 < (1 / 2 : ℝ)).trans_le hy0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  by_cases hy1 : 1 ≤ |y|
  · have h1 : |y| ^ (-q) ≤ |y| ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    have h2 : 1 ≤ y ^ 2 := by rw [← sq_abs]; nlinarith
    have hs : 0 < y ^ 2 := zero_lt_one.trans_le h2
    rw [show |y| ^ (-2 : ℝ) = (y ^ 2)⁻¹ by rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]] at h1
    have hh : (y ^ 2)⁻¹ * (1 + y ^ 2) ≤ 2 := by
      rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hs]
      linarith
    exact ((mul_le_mul_of_nonneg_right h1 (by positivity)).trans hh).trans
      (le_add_of_nonneg_right (by positivity))
  · have hsmall : |y| ^ (-q) ≤ (1 / 2 : ℝ) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hy0 (by linarith)
    have hy2 : 1 + y ^ 2 ≤ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg y, lt_of_not_ge hy1]
    calc
      _ ≤ (1 / 2 : ℝ) ^ (-q) * 2 :=
        mul_le_mul hsmall hy2 (by positivity) (by positivity)
      _ ≤ M := by dsimp [M]; linarith [Real.rpow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (-q)]

private theorem lpNorm_le_of_vertical_bounds {g : 𝓢(ℝ, ℂ)} {B C p : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hp : 1 ≤ p) (hN : 1 < N)
    (hb : ∀ y : ℝ, ‖g y‖ ≤ B)
    (hc : ∀ y : ℝ, |y| ^ N * ‖g y‖ ≤ C) :
    lpNorm g (ENNReal.ofReal p) volume ≤
      (B ^ p + C ^ p * mellinLpTail p N) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hq : 2 ≤ p * (N : ℝ) := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hN')]
  have hqI := integrableOn_mellinLpTail hq
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hz : ENNReal.ofReal p ≠ ⊤ := by simp
  have hi : Integrable (fun y : ℝ => ‖g y‖ ^ p) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using (g.memLp (ENNReal.ofReal p)).integrable_norm_rpow hp' hz
  rw [lpNorm_eq_integral_norm_rpow_toReal hp' hz g.continuous.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, one_div]
  apply Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) _ (inv_nonneg.mpr hp0.le)
  rw [← integral_add_compl measurableSet_Ioo hi (s := Ioo (-(1 / 2)) (1 / 2))]
  apply add_le_add
  · have ht : IntegrableOn (fun _ : ℝ => B ^ p) (Ioo (-(1 / 2)) (1 / 2)) :=
      integrableOn_const (by simp)
    have H := integral_mono_of_nonneg (μ := volume.restrict (Ioo (-(1 / 2)) (1 / 2)))
      (Eventually.of_forall fun y : ℝ => Real.rpow_nonneg (norm_nonneg (g y)) p)
      ht (Eventually.of_forall fun y => Real.rpow_le_rpow (norm_nonneg _) (hb y) hp0.le)
    refine H.trans_eq ?_
    rw [setIntegral_const, Real.volume_real_Ioo]
    norm_num
  · rw [mellinLpTail, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y : ℝ =>
      Real.rpow_nonneg (norm_nonneg (g y)) p) (hqI.const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with y hy
    have hy0 : 0 < |y| := by
      by_contra! h
      exact hy (abs_lt.mp (h.trans_lt (by norm_num)))
    have hbound : ‖g y‖ ≤ C / |y| ^ N := (le_div_iff₀ (pow_pos hy0 N)).mpr (by
      rw [mul_comm]
      exact hc y)
    refine (Real.rpow_le_rpow (norm_nonneg _) hbound hp0.le).trans_eq ?_
    rw [Real.div_rpow hC (pow_nonneg hy0.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul hy0.le, mul_comm (N : ℝ) p, div_eq_mul_inv, ← Real.rpow_neg hy0.le]

private theorem mellin_differentiableAt_of_schwartz_weights {f : ℝ → ℂ} {z : ℂ}
    {a b : ℝ} (hz : z.re ∈ Ioo a b) (hw : ∀ σ ∈ Icc a b, MellinSchwartzAt f σ) :
    DifferentiableAt ℂ (mellin f) z := by
  have hD := (mellin_uniform_riemann_lebesgue (hz.1.trans hz.2) hw).2.1
  exact hD.differentiableAt ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hz)

/-- B.2.1.5 using the nonnegative Schwartz weights of Remark B.2.1.2.
The power estimates and the real Lᵖ bound are uniform in the closed substrip. -/
theorem mellin_forward_semiexponential {f : ℝ → ℂ}
    (hw : ∀ σ : ℝ, 0 ≤ σ → MellinSchwartzAt f σ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    (∀ z : ℂ, 0 < z.re → MellinConvergent f z ∧ DifferentiableAt ℂ (mellin f) z) ∧
    ∀ N : ℕ, ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ^ N * ‖mellin f z‖ ≤ C) ∧
      ∀ σ ∈ Icc a b, ∀ p : ℝ, 1 ≤ p → 1 < N →
        lpNorm (fun y : ℝ => mellin f ⟨σ, y⟩) (ENNReal.ofReal p) volume ≤
          (B ^ p + C ^ p * mellinLpTail p N) ^ (1 / p) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    refine ⟨mellinConvergent_of_schwartzAt (hw _ hz.le),
      mellin_differentiableAt_of_schwartz_weights (a := 0) (b := z.re + 1)
        ⟨hz, by linarith⟩ (fun σ hσ => hw σ hσ.1)⟩
  obtain ⟨_, _, hv, hR⟩ := mellin_uniform_riemann_lebesgue hab
    (fun σ hσ => hw σ (ha.le.trans hσ.1))
  intro N
  obtain ⟨C, hC, hcoef⟩ := hR N
  obtain ⟨B, hB, hbound⟩ := hR 0
  refine ⟨C, B, hC, hB, hcoef, ?_⟩
  intro σ hσ p hp hN
  obtain ⟨g, hg⟩ := hv σ hσ
  rw [← hg]
  apply lpNorm_le_of_vertical_bounds hC.le hp hN
  · intro y
    rw [congrFun hg]
    simpa only [pow_zero, one_mul] using hbound ⟨σ, y⟩ hσ.1 hσ.2
  · intro y
    rw [congrFun hg]
    exact hcoef ⟨σ, y⟩ hσ.1 hσ.2


private noncomputable def dampedSchwartzIntegral (w : ℂ) (g : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ x : ℝ, Complex.exp (w * (x : ℂ)) * g x

private theorem norm_dampedSchwartz_le {w : ℂ} (hw : 0 ≤ w.re)
    {g : 𝓢(ℝ, ℂ)} (hg : ∀ x > 0, g x = 0) (x : ℝ) :
    ‖Complex.exp (w * (x : ℂ)) * g x‖ ≤ ‖g x‖ := by
  by_cases hx : 0 < x
  · simp [hg x hx]
  rw [norm_mul, norm_exp]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_gt hx))

private theorem integrable_dampedSchwartz {w : ℂ} (hw : 0 ≤ w.re)
    {g : 𝓢(ℝ, ℂ)} (hg : ∀ x > 0, g x = 0) :
    Integrable (fun x : ℝ => Complex.exp (w * (x : ℂ)) * g x) := by
  have hc : Continuous (fun x : ℝ => Complex.exp (w * (x : ℂ))) := by fun_prop
  exact g.integrable.norm.mono' (hc.mul g.continuous).aestronglyMeasurable
    (Eventually.of_forall (norm_dampedSchwartz_le hw hg))

private theorem derivCLM_zero_on_positive {g : 𝓢(ℝ, ℂ)} (hg : ∀ x > 0, g x = 0) :
    ∀ x > 0, SchwartzMap.derivCLM ℂ ℂ g x = 0 := by
  intro x hx
  rw [SchwartzMap.derivCLM_apply]
  have he : (g : ℝ → ℂ) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hg y hy
  rw [he.deriv_eq, deriv_const]

private theorem dampedSchwartz_derivative {w : ℂ} (hw : 0 ≤ w.re)
    {g : 𝓢(ℝ, ℂ)} (hg : ∀ x > 0, g x = 0) :
    dampedSchwartzIntegral w (SchwartzMap.derivCLM ℂ ℂ g) =
      -w * dampedSchwartzIntegral w g := by
  have hE (x : ℝ) : HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ)))
      (w * Complex.exp (w * (x : ℂ))) x := by
    have h := (((hasDerivAt_id' (x : ℂ)).const_mul w).cexp).comp_ofReal
    simpa only [id, mul_one, one_mul, mul_comm w] using h
  have hI := integrable_dampedSchwartz hw hg
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => Complex.exp (w * (x : ℂ))) (v := (g : ℝ → ℂ))
    (u' := fun x : ℝ => w * Complex.exp (w * (x : ℂ)))
    (v' := fun x : ℝ => SchwartzMap.derivCLM ℂ ℂ g x)
    (fun x _ => hE x) (fun x _ => by rw [SchwartzMap.derivCLM_apply]; exact g.differentiableAt.hasDerivAt)
    (integrable_dampedSchwartz hw (derivCLM_zero_on_positive hg))
    (by
      change Integrable (fun x : ℝ => (w * Complex.exp (w * (x : ℂ))) * g x)
      simpa only [mul_assoc] using hI.const_mul w) hI
  unfold dampedSchwartzIntegral
  simpa only [mul_assoc, integral_const_mul, neg_mul] using hi

private theorem dampedSchwartz_iterated (n : ℕ) {w : ℂ} (hw : 0 ≤ w.re)
    {g : 𝓢(ℝ, ℂ)} (hg : ∀ x > 0, g x = 0) :
    dampedSchwartzIntegral w (((SchwartzMap.derivCLM ℂ ℂ : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[n]) g) =
      (-w) ^ n * dampedSchwartzIntegral w g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (derivCLM_zero_on_positive hg),
      dampedSchwartz_derivative hw hg, pow_succ, mul_assoc]

/-- A fixed Schwartz weight at the right boundary controls every lower
weight for functions supported in `t ≥ 1`. -/
theorem mellin_supported_left_halfplane_power {f : ℝ → ℂ} {b : ℝ}
    (hw : MellinSchwartzAt f b) (hs : ∀ t ∈ Ioo (0 : ℝ) 1, f t = 0) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, s.re ≤ b → |s.im| ^ n * ‖mellin f s‖ ≤ C := by
  obtain ⟨g, hg⟩ := hw
  have hgs : ∀ x > 0, g x = 0 := by
    intro x hx
    rw [congrFun hg, hs _ ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)⟩, smul_zero]
  let D : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ
  have hsupp (n : ℕ) : ∀ x > 0, ((D^[n]) g) x = 0 := by
    induction n with
    | zero => exact hgs
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact derivCLM_zero_on_positive ih
  intro n
  let G := (D^[n]) g
  have hG : 0 ≤ ∫ x : ℝ, ‖G x‖ := integral_nonneg fun x => norm_nonneg (G x)
  refine ⟨1 + ∫ x : ℝ, ‖G x‖, by linarith, ?_⟩
  intro s hs'
  let w : ℂ := (b : ℂ) - s
  have hw : 0 ≤ w.re := by simpa [w] using sub_nonneg.mpr hs'
  have hEq : mellin f s = dampedSchwartzIntegral w g := by
    rw [mellin_eq_reflected_integral, dampedSchwartzIntegral]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [laplaceKernel, congrFun hg, real_smul, ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    dsimp [w]
    ring
  have hsN := dampedSchwartz_iterated n hw hgs
  change dampedSchwartzIntegral w G = _ at hsN
  rw [hEq]
  have hem : |s.im| ≤ ‖w‖ := by simpa [w, abs_neg] using abs_im_le_norm w
  calc
    |s.im| ^ n * ‖dampedSchwartzIntegral w g‖ ≤ ‖w‖ ^ n * ‖dampedSchwartzIntegral w g‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hem _) (norm_nonneg _)
    _ = ‖dampedSchwartzIntegral w G‖ := by rw [hsN, norm_mul, norm_pow, norm_neg]
    _ ≤ ∫ x : ℝ, ‖G x‖ :=
      (norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          G.integrable.norm (Eventually.of_forall (norm_dampedSchwartz_le hw (hsupp n))))
    _ ≤ _ := by linarith


/-- The L¹ mass of the manuscript's symmetric exponential weight,
written in the reflected logarithmic coordinate. -/
noncomputable def mellinLogMass (f : ℝ → ℂ) (A : ℝ) :=
  ∫ x : ℝ, Real.exp (A * |x|) * ‖f (Real.exp (-x))‖

private theorem mellin_le_logMass {f : ℝ → ℂ} {A : ℝ} {s : ℂ}
    (hA : |s.re| ≤ A) (h₁ : MellinSchwartzAt f A) (h₂ : MellinSchwartzAt f (-A)) :
    ‖mellin f s‖ ≤ mellinLogMass f A := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  have hnorm (x : ℝ) (a : ℝ) (g : 𝓢(ℝ, ℂ))
      (hg : ⇑g = fun y => Real.exp (-a * y) • f (Real.exp (-y))) :
      ‖g x‖ = Real.exp (-a * x) * ‖f (Real.exp (-x))‖ := by
    rw [congrFun hg, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hAbs : AEStronglyMeasurable (fun x : ℝ =>
      Real.exp (A * |x|) * ‖f (Real.exp (-x))‖) volume := by
    have H (x : ℝ) : Real.exp (A * x) • u x = f (Real.exp (-x)) := by
      rw [congrFun hu, ← mul_smul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_smul]
    have hc : Continuous (fun x : ℝ => f (Real.exp (-x))) :=
      ((by fun_prop : Continuous (fun x : ℝ => Real.exp (A * x))).smul u.continuous).congr H
    exact ((by fun_prop : Continuous (fun x : ℝ => Real.exp (A * |x|))).mul hc.norm).aestronglyMeasurable
  have hI : Integrable (fun x : ℝ => Real.exp (A * |x|) * ‖f (Real.exp (-x))‖) := by
    apply (u.integrable.norm.add v.integrable.norm).mono' hAbs
    filter_upwards [] with x
    change ‖Real.exp (A * |x|) * ‖f (Real.exp (-x))‖‖ ≤ ‖u x‖ + ‖v x‖
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, hnorm x _ v hv, neg_neg]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · rw [abs_of_nonpos (le_of_not_ge hx), mul_neg, ← neg_mul, hnorm x _ u hu]
      exact le_add_of_nonneg_right (norm_nonneg _)
  unfold mellinLogMass
  rw [mellin_eq_reflected_integral]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) hI (Eventually.of_forall fun x => ?_))
  simp only [laplaceKernel, norm_mul, norm_exp]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_re]
  exact (le_abs_self _).trans (by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg x))

private theorem mellin_strip_lp_exponential {f : ℝ → ℂ} {a b : ℝ}
    (hw : ∀ σ : ℝ, MellinSchwartzAt f σ) (hab : a < b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ^ N * ‖mellin f z‖ ≤ C) ∧
      ∀ σ ∈ Icc a b, ∀ p : ℝ, 1 ≤ p → 1 < N →
        lpNorm (fun y : ℝ => mellin f ⟨σ, y⟩) (ENNReal.ofReal p) volume ≤
        ((mellinLogMass f (max |a| |b| + N)) ^ p + C ^ p * mellinLpTail p N) ^ (1 / p) := by
  obtain ⟨_, _, hV, hU⟩ := mellin_uniform_riemann_lebesgue hab (fun σ _ => hw σ)
  obtain ⟨C, hC, hPow⟩ := hU N
  refine ⟨C, hC, hPow, ?_⟩
  intro σ hσ p hp hN
  let A := max |a| |b| + N
  have ha : |σ| ≤ A := by
    apply abs_le.mpr
    have h₁ : |a| ≤ max |a| |b| := le_max_left _ _
    have h₂ : |b| ≤ max |a| |b| := le_max_right _ _
    have hn : 0 ≤ (N : ℝ) := by positivity
    constructor <;> linarith [hσ.1, hσ.2, neg_le_abs a, le_abs_self b]
  obtain ⟨g, hg⟩ := hV σ hσ
  rw [← hg]
  apply lpNorm_le_of_vertical_bounds (B := mellinLogMass f A) hC.le hp hN
  · intro y
    rw [congrFun hg]
    exact mellin_le_logMass (s := ⟨σ, y⟩) ha (hw A) (hw (-A))
  · intro y
    rw [congrFun hg]
    exact hPow ⟨σ, y⟩ hσ.1 hσ.2

private theorem mellin_entire_of_schwartz_weights {f : ℝ → ℂ}
    (hw : ∀ σ : ℝ, MellinSchwartzAt f σ) : Differentiable ℂ (mellin f) := by
  intro z
  exact mellin_differentiableAt_of_schwartz_weights (a := z.re - 1) (b := z.re + 1)
    ⟨by linarith, by linarith⟩ (fun σ _ => hw σ)

/-- B.2.1.9. Exponential decay is expressed by the Schwartz condition at
every real Mellin weight. The last clause gives a uniform Hardy bound
when the test function vanishes below one. -/
theorem mellin_exponential_decay {f : ℝ → ℂ} (hw : ∀ σ : ℝ, MellinSchwartzAt f σ) :
    (∀ s : ℂ, MellinConvergent f s) ∧ Differentiable ℂ (mellin f) ∧
    (∀ a b : ℝ, a < b → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ^ N * ‖mellin f z‖ ≤ C) ∧
      ∀ σ ∈ Icc a b, ∀ p : ℝ, 1 ≤ p → 1 < N →
        lpNorm (fun y : ℝ => mellin f ⟨σ, y⟩) (ENNReal.ofReal p) volume ≤
          ((mellinLogMass f (max |a| |b| + N)) ^ p + C ^ p * mellinLpTail p N) ^ (1 / p)) ∧
    ((∀ t ∈ Ioo (0 : ℝ) 1, f t = 0) →
      (∀ b : ℝ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ z : ℂ, z.re ≤ b → |z.im| ^ N * ‖mellin f z‖ ≤ C) ∧
      ∀ b p : ℝ, 1 ≤ p → ∃ K : ℝ, ∀ σ ≤ b,
        MemLp (fun y : ℝ => mellin f ⟨σ, y⟩) (ENNReal.ofReal p) volume ∧
        lpNorm (fun y : ℝ => mellin f ⟨σ, y⟩) (ENNReal.ofReal p) volume ≤ K) := by
  refine ⟨fun s => mellinConvergent_of_schwartzAt (hw s.re),
    mellin_entire_of_schwartz_weights hw,
    fun a b hab N => mellin_strip_lp_exponential hw hab N, ?_⟩
  intro hs
  have hP (b : ℝ) := mellin_supported_left_halfplane_power (hw b) hs
  refine ⟨hP, ?_⟩
  intro b p hp
  obtain ⟨C, hC, hCbd⟩ := hP b 2
  obtain ⟨B, _, hBbd⟩ := hP b 0
  refine ⟨(B ^ p + C ^ p * mellinLpTail p 2) ^ (1 / p), ?_⟩
  intro σ hσ
  obtain ⟨g, hg⟩ := mellin_vertical_schwartz (hw σ)
  rw [← hg]
  refine ⟨g.memLp _, lpNorm_le_of_vertical_bounds hC.le hp (by decide) ?_ ?_⟩
  · intro y
    rw [congrFun hg]
    simpa only [pow_zero, one_mul] using hBbd ⟨σ, y⟩ hσ
  · intro y
    rw [congrFun hg]
    exact hCbd ⟨σ, y⟩ hσ


/-- The uniform L¹ bound needed for the one-edge Cauchy formula, for
Mellin transforms of tests supported on `t ≥ 1`. -/
theorem mellin_supported_uniform_vertical_L1 {f : ℝ → ℂ}
    (hw : ∀ σ : ℝ, MellinSchwartzAt f σ)
    (hs : ∀ t ∈ Ioo (0 : ℝ) 1, f t = 0) (b : ℝ) :
    ∃ K : ℝ, ∀ σ ≤ b, (∫ y : ℝ, ‖mellin f ⟨σ, y⟩‖) ≤ K := by
  obtain ⟨K, hK⟩ := ((mellin_exponential_decay hw).2.2.2 hs).2 b 1 le_rfl
  refine ⟨K, fun σ hσ => ?_⟩
  obtain ⟨hMp, hL⟩ := hK σ hσ
  rw [← lpNorm_one_eq_integral_norm hMp.aestronglyMeasurable]
  simpa using hL

/-- Multiplication of the Mellin test function by a real weight. -/
noncomputable def mellinWeight (f : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (c : ℂ)) • f t

/-- Inversion in the positive norm variable. -/
noncomputable def mellinReflect (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t⁻¹

theorem mellinSchwartzAt_weight {f : ℝ → ℂ} {c σ : ℝ}
    (h : MellinSchwartzAt f (σ + c)) : MellinSchwartzAt (mellinWeight f c) σ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, funext fun x => ?_⟩
  rw [congrFun hg, mellinWeight, ← Complex.ofReal_cpow (Real.exp_nonneg _),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  change _ = Real.exp (-σ * x) • (Real.exp (-x * c) • f (Real.exp (-x)))
  rw [← mul_smul, ← Real.exp_add]
  congr 2
  ring

theorem mellinSchwartzAt_reflect {f : ℝ → ℂ} {σ : ℝ}
    (h : MellinSchwartzAt f (-σ)) : MellinSchwartzAt (mellinReflect f) σ := by
  obtain ⟨g, hg⟩ := mellinSchwartzAt_iff_positive_log.mp h
  refine ⟨g, funext fun x => ?_⟩
  rw [congrFun hg, mellinReflect, ← Real.exp_neg, neg_neg]

@[simp]
theorem mellin_weight (f : ℝ → ℂ) (c : ℝ) (s : ℂ) :
    mellin (mellinWeight f c) s = mellin f (s + c) :=
  mellin_cpow_smul f s c

@[simp]
theorem mellin_reflect (f : ℝ → ℂ) (s : ℂ) :
    mellin (mellinReflect f) s = mellin f (-s) := by
  change mellin (fun t : ℝ => f t⁻¹) s = mellin f (-s)
  simpa [Real.rpow_neg_one, div_neg] using mellin_comp_rpow f s (-1)

private theorem meromorphic_mul_mellin_decay {f F : ℂ → ℂ} {a b A B : ℝ}
    (hf : MeromorphicOn f (Complex.re ⁻¹' Ioo a b)) (hF : Differentiable ℂ F)
    (hA : 0 ≤ A)
    (hGrowth : ∃ T : ℝ, ∀ z : ℂ, a < z.re → z.re < b → T ≤ |z.im| →
      ‖f z‖ ≤ A * |z.im| ^ B)
    (hDecay : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      |z.im| ^ N * ‖F z‖ ≤ C) :
    MeromorphicOn (fun z => f z * F z) (Complex.re ⁻¹' Ioo a b) ∧
    ∀ N : ℕ, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ z : ℂ, a < z.re → z.re < b → T ≤ |z.im| →
        |z.im| ^ N * ‖f z * F z‖ ≤ C := by
  refine ⟨fun z hz => (hf z hz).mul (hF.analyticAt z).meromorphicAt, ?_⟩
  intro N
  obtain ⟨K, hK⟩ := exists_nat_ge B
  obtain ⟨C, hC, hCbd⟩ := hDecay (N + K)
  obtain ⟨T, hT⟩ := hGrowth
  refine ⟨1 + A * C, max 1 T, by positivity, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro z ha hb hz
  have ht : T ≤ |z.im| := (le_max_right _ _).trans hz
  have h1 : 1 ≤ |z.im| := (le_max_left _ _).trans hz
  have hP : |z.im| ^ B ≤ |z.im| ^ K := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le h1 hK
  rw [norm_mul]
  calc
    _ ≤ |z.im| ^ N * ((A * |z.im| ^ K) * ‖F z‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ((hT z ha hb ht).trans
          (mul_le_mul_of_nonneg_left hP hA)) (norm_nonneg _)) (by positivity)
    _ = A * (|z.im| ^ (N + K) * ‖F z‖) := by rw [pow_add]; ring
    _ ≤ A * C := mul_le_mul_of_nonneg_left (hCbd z ha.le hb.le) hA
    _ ≤ _ := by linarith

/-- The strip estimates used by B.2.1.10, including the displayed Lᵖ
bound for the corresponding weighted test function. -/
def MellinAffineStripBounds (F : ℂ → ℂ) (g : ℝ → ℂ) (a b : ℝ) : Prop :=
  Differentiable ℂ F ∧
  ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    (∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ^ N * ‖F z‖ ≤ C) ∧
    ∀ σ ∈ Icc a b, ∀ p : ℝ, 1 ≤ p → 1 < N →
      lpNorm (fun y : ℝ => F ⟨σ, y⟩) (ENNReal.ofReal p) volume ≤
        ((mellinLogMass g (max |a| |b| + N)) ^ p + C ^ p * mellinLpTail p N) ^ (1 / p)

private theorem mellin_affineStripBounds {g : ℝ → ℂ} {a b : ℝ}
    (h : ∀ σ, MellinSchwartzAt g σ) (hab : a < b) :
    MellinAffineStripBounds (mellin g) g a b :=
  ⟨mellin_entire_of_schwartz_weights h, mellin_strip_lp_exponential h hab⟩

/-- B.2.1.10(1), allowing any real shift and either reflection of the
Mellin argument. Order zero of the power estimate gives boundedness. -/
theorem mellin_affine_exponential_bounds {f : ℝ → ℂ}
    (hw : ∀ σ : ℝ, MellinSchwartzAt f σ) {a b : ℝ} (hab : a < b) (c : ℝ) :
    MellinAffineStripBounds (fun s => mellin f (s + c)) (mellinWeight f c) a b ∧
    MellinAffineStripBounds (fun s => mellin f (c - s)) (mellinWeight (mellinReflect f) (-c)) a b := by
  constructor
  · have h := mellin_affineStripBounds (g := mellinWeight f c)
      (fun σ => mellinSchwartzAt_weight (hw (σ + c))) hab
    have he : mellin (mellinWeight f c) = fun s => mellin f (s + c) := funext (mellin_weight f c)
    rwa [he] at h
  · have h := mellin_affineStripBounds (g := mellinWeight (mellinReflect f) (-c))
      (fun σ => mellinSchwartzAt_weight (mellinSchwartzAt_reflect (hw (-(σ + -c))))) hab
    have he : mellin (mellinWeight (mellinReflect f) (-c)) = fun s => mellin f (c - s) := by
      funext s
      rw [mellin_weight, mellin_reflect]
      push_cast
      congr 1
      ring
    rwa [he] at h

/-- B.2.1.10(2), for either shifted Mellin factor. The printed reference
to (B.2.1.26) here refers to the decay inequality (B.2.1.27). -/
theorem meromorphic_mul_mellin_affine_decay {f : ℝ → ℂ} {g : ℂ → ℂ}
    (hw : ∀ σ : ℝ, MellinSchwartzAt f σ) {a b A B : ℝ} (hab : a < b)
    (hg : MeromorphicOn g (Complex.re ⁻¹' Ioo a b)) (hA : 0 ≤ A)
    (hGrowth : ∃ T : ℝ, ∀ z : ℂ, a < z.re → z.re < b → T ≤ |z.im| →
      ‖g z‖ ≤ A * |z.im| ^ B) (c : ℝ) :
    ∀ F ∈ ({(fun s => mellin f (s + c)), fun s => mellin f (c - s)} : Set (ℂ → ℂ)),
      MeromorphicOn (fun z => g z * F z) (Complex.re ⁻¹' Ioo a b) ∧
      ∀ N : ℕ, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
        ∀ z : ℂ, a < z.re → z.re < b → T ≤ |z.im| →
          |z.im| ^ N * ‖g z * F z‖ ≤ C := by
  have hh (F : ℂ → ℂ) (w : ℝ → ℂ) (hF : MellinAffineStripBounds F w a b) :
      MeromorphicOn (fun z => g z * F z) (Complex.re ⁻¹' Ioo a b) ∧
      ∀ N : ℕ, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
        ∀ z : ℂ, a < z.re → z.re < b → T ≤ |z.im| →
          |z.im| ^ N * ‖g z * F z‖ ≤ C :=
    meromorphic_mul_mellin_decay hg hF.1 hA hGrowth (fun N => by
      obtain ⟨C, hC, hB, _⟩ := hF.2 N
      exact ⟨C, hC, hB⟩)
  obtain ⟨hplus, hminus⟩ := mellin_affine_exponential_bounds hw hab c
  rintro F hF
  rcases mem_insert_iff.mp hF with rfl | h
  · exact hh _ _ hplus
  · obtain rfl := mem_singleton_iff.mp h
    exact hh _ _ hminus


private theorem continuousAt_mellin_test_of_weight {f : ℝ → ℂ} {a t : ℝ}
    (hw : MellinSchwartzAt f a) (ht : 0 < t) : ContinuousAt f t := by
  obtain ⟨g, hg⟩ := hw
  have hlog := Real.continuousAt_log ht.ne'
  have hw' : ContinuousAt (fun y => Real.exp (-a * Real.log y)) t :=
    Real.continuous_exp.continuousAt.comp' (continuousAt_const.mul hlog)
  have hg' : ContinuousAt (fun y => g (-Real.log y)) t := g.continuous.continuousAt.comp' hlog.neg
  apply (hw'.smul hg').congr
  filter_upwards [Ioi_mem_nhds ht] with y hy
  change Real.exp (-a * Real.log y) • g (-Real.log y) = f y
  rw [congrFun hg, neg_neg, Real.exp_log hy, ← mul_smul, ← Real.exp_add]
  simp

private theorem verticalIntegrable_mellin_of_weight {f : ℝ → ℂ} {a : ℝ}
    (hw : MellinSchwartzAt f a) : VerticalIntegrable (mellin f) a := by
  obtain ⟨g, hg⟩ := mellin_vertical_schwartz hw
  have he (y : ℝ) : (a : ℂ) + (y : ℂ) * I = ⟨a, y⟩ := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  simpa only [VerticalIntegrable, he, hg] using g.integrable (μ := volume)

set_option maxHeartbeats 600000 in
/-- A Mellin contour with a geometric-series multiplier recovers the
one-sided sequence of samples, starting at the specified offset.
The sign of the scale selects the positive or the negative powers. -/
theorem mellin_geometric_contour {f : ℝ → ℂ} {a d θ : ℝ}
    (hw : MellinSchwartzAt f a) (had : 0 < a * d) (j : ℕ) :
    let S := fun y : ℝ => (a : ℂ) + (y : ℂ) * I
    let r := fun y : ℝ => Complex.exp ((θ : ℂ) * I - (d : ℂ) * S y)
    HasSum (fun n : ℕ => Complex.exp (((θ * (n + j : ℕ) : ℝ) : ℂ) * I) *
        f (Real.exp (d * (n + j : ℕ))))
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ y : ℝ, mellin f (S y) * r y ^ j * (1 - r y)⁻¹) := by
  dsimp only
  let S := fun y : ℝ => (a : ℂ) + (y : ℂ) * I
  let r := fun y : ℝ => Complex.exp ((θ : ℂ) * I - (d : ℂ) * S y)
  let q := Real.exp (-(a * d))
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr had)
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hr (y : ℝ) : ‖r y‖ = q := by
    dsimp only [r]
    rw [norm_exp]
    congr 1
    simp [S, Complex.mul_re, Complex.mul_im, mul_comm]
  have hI : Integrable (fun y : ℝ => mellin f (S y)) :=
    verticalIntegrable_mellin_of_weight hw
  let H (n : ℕ) (y : ℝ) := mellin f (S y) * r y ^ (n + j)
  have hn (n : ℕ) (y : ℝ) : ‖H n y‖ = ‖mellin f (S y)‖ * q ^ (n + j) := by
    simp only [H, norm_mul, norm_pow, hr]
  have hH (n : ℕ) : Integrable (H n) := by
    refine (hI.norm.mul_const (q ^ (n + j))).mono' ?_ (Eventually.of_forall fun y => (hn n y).le)
    have hc : Continuous (fun y : ℝ => r y ^ (n + j)) := by dsimp [r, S]; fun_prop
    exact hI.aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hSumH : Summable (fun n : ℕ => ∫ y : ℝ, ‖H n y‖) := by
    have hh : Summable (fun n : ℕ => q ^ (n + j)) := by
      simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq).mul_right (q ^ j)
    refine (hh.mul_left (∫ y : ℝ, ‖mellin f (S y)‖)).congr fun n => ?_
    simp only [hn, integral_mul_const]
  have hsum := (hasSum_integral_of_summable_integral_norm hH hSumH).const_smul
    (1 / (2 * Real.pi) : ℝ)
  have hSeries (y : ℝ) :
      (∑' n : ℕ, H n y) = mellin f (S y) * r y ^ j * (1 - r y)⁻¹ := by
    simp only [H, pow_add, mul_assoc, tsum_mul_left,
      tsum_mul_right, tsum_geometric_of_norm_lt_one ((hr y).trans_lt hq)]
    ring
  simp only [hSeries] at hsum
  refine hsum.congr_fun fun n => ?_
  symm
  let k : ℕ := n + j
  let t := Real.exp (d * k)
  have ht : 0 < t := Real.exp_pos _
  have hInv := mellinInv_mellin_eq a f ht (mellinConvergent_of_schwartzAt hw)
    (verticalIntegrable_mellin_of_weight hw) (continuousAt_mellin_test_of_weight hw ht)
  have hker (y : ℝ) : r y ^ k =
      Complex.exp (((θ * k : ℝ) : ℂ) * I) * ((t : ℂ) ^ (-(S y))) := by
    dsimp only [r]
    rw [← Complex.exp_nat_mul, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne')]
    have hlog : Complex.log (t : ℂ) = (↑(d * k : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log ht.le]
      simp [t]
    rw [hlog, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpoint (y : ℝ) :
      H n y = Complex.exp (((θ * k : ℝ) : ℂ) * I) *
        ((t : ℂ) ^ (-(S y)) • mellin f (S y)) := by
    change mellin f (S y) * r y ^ k = _
    rw [hker, smul_eq_mul]
    ring
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, H n y) =
    Complex.exp (((θ * k : ℝ) : ℂ) * I) * f t
  simp_rw [hpoint, integral_const_mul, ← smul_eq_mul (Complex.exp _), smul_comm (1 / (2 * Real.pi) : ℝ)]
  change _ * mellinInv a (mellin f) t = _
  simp [hInv, smul_eq_mul]


/-- The right-hand contour in B.4.1.7 sums the samples at the strictly
positive prime powers. Its real parameter `d` is the logarithm of the
prime norm, and `θ` is the phase of the unramified character. -/
theorem mellin_prime_power_right_contour {f : ℝ → ℂ} {a d θ : ℝ}
    (hw : MellinSchwartzAt f a) (ha : 0 < a) (hd : 0 < d) :
    let S := fun y : ℝ => (a : ℂ) + (y : ℂ) * I
    HasSum (fun n : ℕ => Complex.exp (((θ * (n + 1 : ℕ) : ℝ) : ℂ) * I) *
        f (Real.exp (d * (n + 1 : ℕ))))
      ((1 / (2 * Real.pi) : ℝ) •
        ∫ y : ℝ, -mellin f (S y) / (1 - Complex.exp ((d : ℂ) * S y - (θ : ℂ) * I))) := by
  dsimp only
  have hh := mellin_geometric_contour (θ := θ) hw (mul_pos ha hd) 1
  dsimp only at hh
  convert hh using 2
  apply integral_congr_ae
  filter_upwards [] with y
  let z := (a : ℂ) + (y : ℂ) * I
  let r := Complex.exp ((θ : ℂ) * I - (d : ℂ) * z)
  have hr0 : r ≠ 0 := Complex.exp_ne_zero _
  have hr1 : r ≠ 1 := by
    have hn : ‖r‖ < 1 := by
      dsimp only [r]
      rw [norm_exp]
      apply Real.exp_lt_one_iff.mpr
      simp [Complex.mul_re, Complex.mul_im, z, mul_pos hd ha]
    intro h
    simp [h] at hn
  have hr' : Complex.exp ((d : ℂ) * z - (θ : ℂ) * I) = r⁻¹ := by
    rw [show (d : ℂ) * z - (θ : ℂ) * I = -((θ : ℂ) * I - (d : ℂ) * z) by ring,
      Complex.exp_neg]
  change -mellin f z / (1 - Complex.exp ((d : ℂ) * z - (θ : ℂ) * I)) =
    mellin f z * r ^ 1 * (1 - r)⁻¹
  rw [hr', pow_one]
  have h : 1 - r⁻¹ = (r - 1) / r := by field_simp
  rw [h, div_div_eq_mul_div, show r - 1 = -(1 - r) by ring]
  simp only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg, mul_assoc]


/-- A right contour and a left contour together recover the bilateral
prime-power sum. The left contour contributes the sample at one and
all negative prime powers. -/
theorem mellin_prime_power_two_contours {f : ℝ → ℂ} {a b d θ : ℝ}
    (hwa : MellinSchwartzAt f a) (hwb : MellinSchwartzAt f b)
    (ha : 0 < a) (hb : b < 0) (hd : 0 < d) :
    let sample := fun m : ℤ => Complex.exp (((θ * m : ℝ) : ℂ) * I) * f (Real.exp (d * m))
    let V := fun x y : ℝ => (x : ℂ) + (y : ℂ) * I
    let contour := fun x : ℝ => (1 / (2 * Real.pi) : ℝ) •
      ∫ y : ℝ, -mellin f (V x y) / (1 - Complex.exp ((d : ℂ) * V x y - (θ : ℂ) * I))
    Summable sample ∧ (∑' m : ℤ, sample m) = contour a - contour b := by
  dsimp only
  let F (m : ℤ) := Complex.exp (((θ * m : ℝ) : ℂ) * I) * f (Real.exp (d * m))
  let V (x y : ℝ) := (x : ℂ) + (y : ℂ) * I
  let J (x : ℝ) := (1 / (2 * Real.pi) : ℝ) •
    ∫ y : ℝ, -mellin f (V x y) / (1 - Complex.exp ((d : ℂ) * V x y - (θ : ℂ) * I))
  have hpos : HasSum (fun n : ℕ => F ((n + 1 : ℕ) : ℤ)) (J a) := by
    simpa only [F, J, V, Int.cast_natCast] using
      mellin_prime_power_right_contour (θ := θ) hwa ha hd
  have hneg : HasSum (fun n : ℕ => F (-(n : ℤ))) (-J b) := by
    have hraw := mellin_geometric_contour (d := -d) (θ := -θ) hwb
      (mul_pos_of_neg_of_neg hb (neg_lt_zero.mpr hd)) 0
    dsimp only at hraw
    have hs (y : ℝ) :
        ((↑(-θ) : ℂ) * I - ((↑(-d) : ℂ) * V b y)) =
          (d : ℂ) * V b y - (θ : ℂ) * I := by push_cast; ring
    have he : -J b = (1 / (2 * Real.pi) : ℝ) •
        ∫ y : ℝ, mellin f (V b y) * (1 - Complex.exp ((d : ℂ) * V b y - (θ : ℂ) * I))⁻¹ := by
      simp only [J, ← smul_neg, ← integral_neg, neg_div, neg_neg]
      congr 1
    rw [he]
    change HasSum (fun n : ℕ => F (-(n : ℤ))) _
    convert hraw using 1
    · funext n
      simp only [Nat.add_zero, F, Int.cast_neg, Int.cast_natCast, mul_neg, neg_mul]
    · congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [pow_zero, mul_one]
      rw [← hs y]
  have hp : Summable (fun n : ℕ => F (n : ℤ)) :=
    (summable_nat_add_iff 1).mp hpos.summable
  have hs : Summable F := summable_int_iff_summable_nat_and_neg.mpr ⟨hp, hneg.summable⟩
  change Summable F ∧ (∑' m : ℤ, F m) = J a - J b
  refine ⟨hs, ?_⟩
  rw [tsum_int_eq_zero_add_tsum_pnat hs]
  have hpn : (∑' n : ℕ+, F ((n : ℕ) : ℤ)) = J a := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => F (n : ℤ))]
    exact hpos.tsum_eq
  have hmn : (∑' n : ℕ+, F (-((n : ℕ) : ℤ))) = -J b - F 0 := by
    have ht := hneg.tsum_eq
    rw [hneg.summable.tsum_eq_zero_add] at ht
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => F (-(n : ℤ)))]
    simp only [Nat.cast_zero, neg_zero] at ht
    exact eq_sub_of_add_eq (by simpa only [add_comm] using ht)
  rw [hpn, hmn]
  ring


theorem mellinPhase_hasTemperateGrowth (θ : ℝ) :
    (fun x : ℝ => Complex.exp (((θ : ℂ) * I) * (x : ℂ))).HasTemperateGrowth := by
  let c : ℂ := (θ : ℂ) * I
  let u := fun x : ℝ => Complex.exp (c * (x : ℂ))
  have hcoe : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hu : ContDiff ℝ ∞ u := (contDiff_const.mul hcoe).cexp
  have hD (x : ℝ) : HasDerivAt u (c * u x) x := by
    have h := (((hasDerivAt_id' (x : ℂ)).const_mul c).cexp).comp_ofReal
    simpa only [u, id, mul_one, one_mul, mul_comm c] using h
  have hIter (n : ℕ) : iteratedDeriv n u = fun x => c ^ n * u x := by
    induction n with
    | zero => simp
    | succ n ih =>
      funext x
      rw [iteratedDeriv_succ, ih]
      exact ((hD x).const_mul (c ^ n)).deriv.trans (by simp only [pow_succ, c, mul_assoc])
  refine ⟨hu, fun n => ⟨0, ‖c‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hIter, norm_mul, norm_pow, pow_zero]
  simp [u, c, norm_exp, Complex.mul_re, Complex.mul_im]

private theorem summable_schwartz_integer_samples (g : 𝓢(ℝ, ℂ)) :
    Summable (fun m : ℤ => g (m : ℝ)) := by
  have h := Int.isClosedEmbedding_coe_real.tendsto_cocompact
  rw [cocompact_eq_cofinite] at h
  apply summable_of_isBigO (Real.summable_abs_int_rpow (b := (2 : ℝ)) (by norm_num))
  exact (g.isBigO_cocompact_rpow (-2)).comp_tendsto h

set_option maxHeartbeats 500000 in
/-- Poisson summation on a geometric lattice. Here `d` is the logarithm
of the lattice generator and `θ` is the character phase. -/
theorem mellin_poisson_geometric_lattice {f : ℝ → ℂ} {d : ℝ}
    (h0 : MellinSchwartzAt f 0) (hd : 0 < d) (θ : ℝ) :
    let sample := fun m : ℤ => Complex.exp (((θ * m : ℝ) : ℂ) * I) * f (Real.exp (d * m))
    let spectrum := fun m : ℤ => mellin f
      ((((θ + 2 * Real.pi * m) / d : ℝ) : ℂ) * I)
    Summable sample ∧ Summable spectrum ∧
      (d : ℂ) * (∑' m : ℤ, sample m) = ∑' m : ℤ, spectrum m := by
  dsimp only
  obtain ⟨g, hg0⟩ := h0
  have hg (x : ℝ) : g x = f (Real.exp (-x)) := by simpa using congrFun hg0 x
  let u : ℝˣ := Units.mk0 (-d) (neg_ne_zero.mpr hd.ne')
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ u) g
  let v := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => Complex.exp (((θ : ℂ) * I) * (x : ℂ))) G
  have hv (x : ℝ) : v x =
      Complex.exp (((θ * x : ℝ) : ℂ) * I) * g (-d * x) := by
    unfold v G
    rw [SchwartzMap.smulLeftCLM_apply_apply (mellinPhase_hasTemperateGrowth θ),
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, smul_eq_mul]
    change Complex.exp ((θ : ℂ) * I * (x : ℂ)) * g (x * (-d)) = _
    push_cast
    congr 2 <;> ring
  have hvs (m : ℤ) : v (m : ℝ) =
      Complex.exp (((θ * m : ℝ) : ℂ) * I) * f (Real.exp (d * m)) := by
    rw [hv, hg, neg_mul, neg_neg]
  let Y (m : ℤ) : ℝ := (θ - 2 * Real.pi * m) / d
  have hF (m : ℤ) : (d : ℂ) * (𝓕 v) (m : ℝ) = mellin f ((Y m : ℂ) * I) := by
    let h (x : ℝ) := Complex.exp (-((Y m : ℂ) * I) * (x : ℂ)) * g x
    have hEq : (𝓕 v) (m : ℝ) = ∫ x : ℝ, h (-d * x) := by
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hv, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
      dsimp only [h]
      congr 2
      have hY : Y m * d = θ - 2 * Real.pi * m := by
        dsimp [Y]
        exact div_mul_cancel₀ _ hd.ne'
      push_cast
      have hY' : (Y m : ℂ) * d = (θ : ℂ) - 2 * Real.pi * (m : ℂ) := by exact_mod_cast hY
      linear_combination -(I * (x : ℂ)) * hY'
    rw [hEq, Measure.integral_comp_mul_left, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hd)]
    rw [mellin_eq_reflected_integral]
    have hInt : (∫ x : ℝ, h x) = ∫ x : ℝ, laplaceKernel
        (fun t => f (Real.exp (-t))) ((Y m : ℂ) * I) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [h, laplaceKernel, hg]
    rw [hInt, real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hd.ne'), one_mul]
  have hPoint (m : ℤ) : Y (-m) = (θ + 2 * Real.pi * m) / d := by
    simp [Y]
  have hvSum := summable_schwartz_integer_samples v
  have hFSum := summable_schwartz_integer_samples (𝓕 v)
  have hNSum : Summable (fun m : ℤ => mellin f ((Y m : ℂ) * I)) :=
    (hFSum.mul_left (d : ℂ)).congr hF
  refine ⟨hvSum.congr hvs, (hNSum.comp_injective neg_injective).congr ?_, ?_⟩
  · intro m
    simp [hPoint]
  have hpois := SchwartzMap.tsum_eq_tsum_fourier v 0
  simp only [zero_add, AddCircle.coe_zero, fourier_eval_zero, mul_one] at hpois
  simp_rw [← hvs]
  rw [hpois, ← tsum_mul_left]
  calc
    _ = ∑' m : ℤ, mellin f ((Y m : ℂ) * I) := tsum_congr hF
    _ = _ := by
      rw [← (Equiv.neg ℤ).tsum_eq (f := fun m : ℤ => mellin f ((Y m : ℂ) * I))]
      simp only [Equiv.neg_apply, hPoint]

/-- The prime-power kernel times a Mellin transform is absolutely
integrable on every noncentral vertical line. -/
theorem integrable_prime_power_contour {f : ℝ → ℂ} {a d : ℝ}
    (hw : MellinSchwartzAt f a) (ha : a ≠ 0) (hd : 0 < d) (θ : ℝ) :
    Integrable (fun y : ℝ =>
      -mellin f ((a : ℂ) + (y : ℂ) * I) /
        (1 - Complex.exp ((d : ℂ) * ((a : ℂ) + (y : ℂ) * I) - (θ : ℂ) * I))) := by
  let E (y : ℝ) := Complex.exp ((d : ℂ) * ((a : ℂ) + (y : ℂ) * I) - (θ : ℂ) * I)
  let K := |1 - Real.exp (d * a)|
  have hK : 0 < K := by
    apply abs_pos.mpr
    intro he
    have h := (sub_eq_zero.mp he).symm
    rw [← Real.exp_zero] at h
    exact (mul_ne_zero hd.ne' ha) (Real.exp_injective h)
  have hbound (y : ℝ) : K ≤ ‖1 - E y‖ := by
    have hnorm : ‖E y‖ = Real.exp (d * a) := by
      simp [E, norm_exp, Complex.mul_re, Complex.mul_im]
    simpa only [K, hnorm, norm_one] using abs_norm_sub_norm_le (1 : ℂ) (E y)
  have hm := verticalIntegrable_mellin_of_weight hw
  change Integrable (fun y : ℝ => mellin f ((a : ℂ) + (y : ℂ) * I)) at hm
  have hden : Continuous (fun y : ℝ => 1 - E y) := by dsimp [E]; fun_prop
  have hinv := hden.inv₀ (fun y => norm_pos_iff.mp (hK.trans_le (hbound y)))
  refine (hm.norm.div_const K).mono' ?_ ?_
  · simp only [div_eq_mul_inv]
    change AEStronglyMeasurable
      ((-fun y : ℝ => mellin f ((a : ℂ) + (y : ℂ) * I)) * (fun y => 1 - E y)⁻¹) volume
    exact hm.aestronglyMeasurable.neg.mul hinv.aestronglyMeasurable
  · filter_upwards [] with y
    rw [norm_div, norm_neg]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hK (hbound y)

/-- Corrected B.4.1.7. The bilateral samples and the spectral samples are
absolutely summable, and their common value is the difference of the
right and left Mellin contours. -/
theorem mellin_prime_power_poisson_repaired {f : ℝ → ℂ} {a b d : ℝ}
    (hw : ∀ σ : ℝ, MellinSchwartzAt f σ) (ha : 0 < a) (hb : b < 0) (hd : 0 < d) (θ : ℝ) :
    let sample := fun m : ℤ => Complex.exp (((θ * m : ℝ) : ℂ) * I) * f (Real.exp (d * m))
    let spectrum := fun m : ℤ => mellin f
      ((((θ + 2 * Real.pi * m) / d : ℝ) : ℂ) * I)
    let V := fun x y : ℝ => (x : ℂ) + (y : ℂ) * I
    let kernel := fun x y : ℝ => -mellin f (V x y) /
      (1 - Complex.exp ((d : ℂ) * V x y - (θ : ℂ) * I))
    let contour := fun x : ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ, kernel x y
    Integrable (kernel a) ∧ Integrable (kernel b) ∧ Summable sample ∧ Summable spectrum ∧
      (d : ℂ) * (∑' m : ℤ, sample m) = ∑' m : ℤ, spectrum m ∧
      (d : ℂ) * (∑' m : ℤ, sample m) = (d : ℂ) * (contour a - contour b) := by
  obtain ⟨hS, hT, hEq⟩ := mellin_poisson_geometric_lattice (hw 0) hd θ
  refine ⟨integrable_prime_power_contour (hw a) ha.ne' hd θ,
    integrable_prime_power_contour (hw b) hb.ne hd θ, hS, hT, hEq, ?_⟩
  dsimp only
  rw [(mellin_prime_power_two_contours (θ := θ) (hw a) (hw b) ha hb hd).2]


set_option maxHeartbeats 700000 in
/-- A smooth logarithmic bump gives a counterexample to the single right
contour in the printed B.4.1.7. The bilateral sum retains the sample
at one, and the right contour misses it. -/
theorem mellin_prime_power_single_contour_obstruction {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∃ f : ℝ → ℂ, (∀ σ : ℝ, MellinSchwartzAt f σ) ∧
      (∑' m : ℤ, f (Real.exp (d * m))) = 1 ∧
      ((1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ,
        -mellin f ((a : ℂ) + (y : ℂ) * I) /
          (1 - Complex.exp ((d : ℂ) * ((a : ℂ) + (y : ℂ) * I)))) = 0 := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨d / 4, d / 2, by linarith, by linarith⟩
  let p : ℝ → ℂ := fun x => (ψ x : ℂ)
  let f : ℝ → ℂ := fun t => p (Real.log t)
  have hp : ContDiff ℝ ∞ p := Complex.ofRealCLM.contDiff.comp ψ.contDiff
  have hpc : HasCompactSupport p := ψ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hw (σ : ℝ) : MellinSchwartzAt f σ := by
    apply mellinSchwartzAt_iff_positive_log.mpr
    let H : ℝ → ℂ := fun x => Real.exp (σ * x) • p x
    have hc : HasCompactSupport H := by
      change HasCompactSupport ((fun x : ℝ => Real.exp (σ * x)) • p)
      exact hpc.smul_left
    have he : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (σ * x)) := by fun_prop
    have hHs : ContDiff ℝ ∞ H := he.smul hp
    refine ⟨hc.toSchwartzMap hHs, funext fun x => ?_⟩
    change H x = _
    simp [H, f, Real.log_exp]
  have hzero (m : ℤ) (hm : m ≠ 0) : f (Real.exp (d * m)) = 0 := by
    dsimp [f, p]
    rw [Real.log_exp, ψ.zero_of_le_dist]
    · simp
    · have hm' : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hd]
      change d / 2 ≤ d * |(m : ℝ)|
      nlinarith [mul_le_mul_of_nonneg_left hm' hd.le]
  have hcenter : f 1 = 1 := by
    dsimp [f, p]
    rw [Real.log_one, ψ.one_of_mem_closedBall]
    · simp
    · exact Metric.mem_closedBall_self ψ.rIn_pos.le
  refine ⟨f, hw, ?_, ?_⟩
  · rw [tsum_eq_single 0 hzero]
    simpa using hcenter
  · have h := mellin_prime_power_right_contour (θ := 0) (hw a) ha hd
    simp only [ofReal_zero, zero_mul, sub_zero] at h
    rw [← h.tsum_eq]
    have hz (n : ℕ) : f (Real.exp (d * (n + 1 : ℕ))) = 0 := by
      simpa only [Int.cast_natCast] using hzero (↑(n + 1) : ℤ) (by omega)
    simp only [Complex.exp_zero, one_mul, hz, tsum_zero]

end Masullo
