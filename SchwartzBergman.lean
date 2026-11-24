/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import VerticalCauchyIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped ContDiff NNReal ENNReal SchwartzMap

namespace Masullo

noncomputable section

section Seminorms

variable (X : Type*) [AddCommGroup X] [Module ℂ X] {ι : Type*}

/-- Paper: §C.2.3, p. 676. A type synonym distinguishes vector spaces equipped with
different tensor topologies on the same algebraic carrier. -/
def WithGeneratingSeminorms (_p : SeminormFamily ℂ X ι) := X

variable (p : SeminormFamily ℂ X ι)

instance : AddCommGroup (WithGeneratingSeminorms X p) := inferInstanceAs (AddCommGroup X)

instance : Module ℂ (WithGeneratingSeminorms X p) := inferInstanceAs (Module ℂ X)

instance : TopologicalSpace (WithGeneratingSeminorms X p) := p.moduleFilterBasis.topology

/-- Paper: §C.2.3, p. 676. The specified seminorms generate the topology on the synonym. -/
theorem withGeneratingSeminorms_spec :
    @WithSeminorms ℂ (WithGeneratingSeminorms X p) ι inferInstance inferInstance inferInstance p
      inferInstance := ⟨rfl⟩

instance : PolynormableSpace ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).toPolynormableSpace

instance : IsTopologicalAddGroup (WithGeneratingSeminorms X p) :=
  p.moduleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup

instance : UniformSpace (WithGeneratingSeminorms X p) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (WithGeneratingSeminorms X p) :=
  isUniformAddGroup_of_addCommGroup

end Seminorms

section Bergman

/-- Paper: Lemma D.3.1.1, p. 797. Bounds for one polynomial weight on every
interior strip persist after taking any number of complex derivatives. -/
theorem verticalStrip_weighted_iteratedDeriv_bounded (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Ioo a b)) (N : ℕ)
    (h : ∀ c d : ℝ, a < c → c < d → d < b →
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Ioo c d)))
    (k : ℕ) (c d : ℝ) (hac : a < c) (hcd : c < d) (hdb : d < b) :
    BddAbove ((fun z : ℂ ↦ ‖z ^ N * iteratedDeriv k f z‖) '' (Complex.re ⁻¹' Ioo c d)) := by
  let r := min (c - a) (b - d) / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have ha : a < c - r := by
    dsimp [r]
    linarith [min_le_left (c - a) (b - d)]
  have hb : d + r < b := by
    dsimp [r]
    linarith [min_le_right (c - a) (b - d)]
  obtain ⟨M, hM⟩ := h (c - r) (d + r) ha (by linarith) hb
  let B := 2 ^ N * max M 0
  refine ⟨k.factorial * B / (r / 4) ^ k, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change c < z.re ∧ z.re < d at hz
  -- Choose a circle on which the weight at the center is controlled by the boundary weight.
  obtain ⟨R, hRlo, hRhi, hweight⟩ : ∃ R : ℝ, r / 4 ≤ R ∧ R ≤ r ∧
      ∀ w ∈ Metric.sphere z R, ‖z‖ ≤ 2 * ‖w‖ := by
    by_cases hsmall : ‖z‖ ≤ r / 2
    · refine ⟨r, by linarith, le_rfl, ?_⟩
      intro w hw
      have hd := dist_le_norm_add_norm w z
      rw [Metric.mem_sphere.mp hw] at hd
      linarith [norm_nonneg w]
    · refine ⟨r / 4, le_rfl, by linarith, ?_⟩
      intro w hw
      have hd := norm_sub_norm_le z w
      rw [← dist_eq_norm, dist_comm, Metric.mem_sphere.mp hw] at hd
      linarith
  have hstrip {w : ℂ} (hw : w ∈ Metric.closedBall z R) :
      w ∈ Complex.re ⁻¹' Ioo (c - r) (d + r) := by
    have hd := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_re, abs_le] at hd
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hdiff := (hf.const_mul (z ^ N)).diffContOnCl_ball (c := z) (R := R)
    (fun w hw ↦ Ioo_subset_Ioo ha.le hb.le (hstrip hw))
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z R) : ‖z ^ N * f w‖ ≤ B := by
    have hwM := hM (mem_image_of_mem _ (hstrip (Metric.sphere_subset_closedBall hw)))
    calc
      ‖z ^ N * f w‖ = ‖z‖ ^ N * ‖f w‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 * ‖w‖) ^ N * ‖f w‖ := by
        gcongr
        exact hweight w hw
      _ = 2 ^ N * ‖w ^ N * f w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
      _ ≤ B := by
        dsimp [B]
        gcongr
        exact hwM.trans (le_max_left _ _)
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by linarith : 0 < R) hdiff hcircle
  rw [iteratedDeriv_const_mul_field] at hest
  apply hest.trans
  exact div_le_div_of_nonneg_left (by dsimp [B]; positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) hRlo k)

-- TODO(paper-gap): The proof's displayed denominator in (D.3.1.2) uses
-- σ + Re(z), although the real part of σ + iT - z is σ - Re(z).

/-- Paper: Definition D.3.1.3, p. 800. The strip conditions are closed under
the vector space operations. -/
theorem schwartzBergman_closure (I : Set ℝ) :
    let P (f : ℂ → ℂ) :=
      EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
      ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))
    P 0 ∧ (∀ {f g}, P f → P g → P (f + g)) ∧ (∀ c : ℂ, ∀ {f}, P f → P (c • f)) := by
  dsimp only
  refine ⟨⟨eqOn_refl _ _, differentiableOn_const 0, ?_⟩, ?_, ?_⟩
  · intro a b _ _ N
    exact ⟨0, by rintro _ ⟨z, _, rfl⟩; simp⟩
  · rintro f g ⟨hf, df, bf⟩ ⟨hg, dg, bg⟩
    refine ⟨fun z hz ↦ ?_, df.add dg, ?_⟩
    · simp [Pi.add_apply, hf hz, hg hz]
    · intro a b hab hI N
      obtain ⟨A, hA⟩ := bf a b hab hI N
      obtain ⟨B, hB⟩ := bg a b hab hI N
      refine ⟨A + B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (f z + g z)‖ ≤ _
      rw [mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hA ⟨z, hz, rfl⟩) (hB ⟨z, hz, rfl⟩))
  · rintro c f ⟨hf, df, bf⟩
    refine ⟨fun z hz ↦ ?_, df.const_mul c, ?_⟩
    · simp [Pi.smul_apply, hf hz]
    · intro a b hab hI N
      obtain ⟨A, hA⟩ := bf a b hab hI N
      refine ⟨‖c‖ * A, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (c * f z)‖ ≤ _
      rw [mul_left_comm, norm_mul]
      exact mul_le_mul_of_nonneg_left (hA ⟨z, hz, rfl⟩) (norm_nonneg _)

/-- Paper: Definition D.3.1.3, p. 800. These are the holomorphic functions
with rapid decay on every bounded-width strip whose real closure is contained in the interval.
Deviation: Functions are extended by zero outside their strip to give a common carrier.
Bounds are tested on closed substrips, which is equivalent on an open interval. -/
def schwartzBergmanSubmodule (I : Set ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
    ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))}
  zero_mem' := (schwartzBergman_closure I).1
  add_mem' := (schwartzBergman_closure I).2.1
  smul_mem' := (schwartzBergman_closure I).2.2

/-- Paper: Definition D.3.1.3, p. 800. The Gaussian restricted to a strip
gives a nonzero example whenever the strip is nonempty.
Deviation: Sanity check in the zero-extension representation. -/
theorem gaussian_mem_schwartzBergmanSubmodule (I : Set ℝ) (hI : IsOpen I) :
    (Complex.re ⁻¹' I).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) ∈
      schwartzBergmanSubmodule I := by
  refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
  · have h : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (z ^ 2)) := by fun_prop
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply (h z).congr_of_eventuallyEq
    filter_upwards [(hI.preimage Complex.continuous_re).mem_nhds hz] with w hw
    exact indicator_of_mem hw _
  · intro a b _ hab N
    let M := max |a| |b|
    refine ⟨N.factorial * Real.exp (1 + 2 * M ^ 2), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hstrip : z.re ∈ Icc a b := hz
    have hM : |z.re| ≤ M := abs_le_max_abs_abs hstrip.1 hstrip.2
    have hsq : z.re ^ 2 ≤ M ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hweight : ‖z‖ ^ N ≤ N.factorial * Real.exp ‖z‖ := by
      have h := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
      simpa [mul_comm] using h
    change ‖z ^ N * (Complex.re ⁻¹' I).indicator _ z‖ ≤ _
    rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hab hstrip), norm_mul, norm_pow, Complex.norm_exp]
    calc
      _ ≤ (N.factorial * Real.exp ‖z‖) * Real.exp (z ^ 2).re :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = N.factorial * Real.exp (‖z‖ + (z ^ 2).re) := by rw [Real.exp_add, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [pow_two, Complex.mul_re]
        nlinarith [Complex.sq_norm_sub_sq_re z, sq_nonneg (‖z‖ - 1 / 2)]

/-- Paper: (D.3.1.7), p. 799. Evaluate the polynomially weighted function on the
vertical line with real part a. -/
def weightedVerticalTrace (a : ℝ) (N : ℕ) (f : ℂ → ℂ) (x : ℝ) : ℂ :=
  let z : ℂ := (a : ℂ) + (x : ℂ) * Complex.I
  z ^ N * f z

/-- Paper: (D.3.1.7), p. 799. At zero height, the trace evaluates the weighted
function on the real axis. -/
theorem weightedVerticalTrace_zero_height (a : ℝ) (N : ℕ) (f : ℂ → ℂ) :
    weightedVerticalTrace a N f 0 = (a : ℂ) ^ N * f a := by
  simp [weightedVerticalTrace]

private theorem inverse_linear_weight_memLp (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) :
    MemLp (fun x : ℝ ↦ (1 + ‖x‖)⁻¹) p volume := by
  apply (integrable_norm_rpow_iff (by fun_prop) (zero_lt_one.trans hp).ne' hp'.ne).mp
  have hdim : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'.ne).2 hp
  have hnorm (x : ℝ) : ‖(1 + ‖x‖)⁻¹‖ = (1 + ‖x‖)⁻¹ := Real.norm_of_nonneg (by positivity)
  simpa only [hnorm, Real.rpow_neg_eq_inv_rpow] using
    (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := p.toReal) (by simpa using hdim))

private theorem weightedVerticalTrace_le_inverse_weight (a : ℝ) (N : ℕ) (f : ℂ → ℂ)
    (A B : ℝ) (hA : ∀ x, ‖weightedVerticalTrace a N f x‖ ≤ A)
    (hB : ∀ x, ‖weightedVerticalTrace a (N + 1) f x‖ ≤ B) (x : ℝ) :
    ‖weightedVerticalTrace a N f x‖ ≤ (A + B) * (1 + ‖x‖)⁻¹ := by
  let z : ℂ := (a : ℂ) + x * Complex.I
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_add, mul_one]
  apply add_le_add (hA x)
  have hx : ‖x‖ ≤ ‖z‖ := by simpa [Real.norm_eq_abs, z] using Complex.abs_im_le_norm z
  calc
    ‖weightedVerticalTrace a N f x‖ * ‖x‖ ≤
        ‖weightedVerticalTrace a N f x‖ * ‖z‖ :=
      mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖weightedVerticalTrace a (N + 1) f x‖ := by
      change ‖z ^ N * f z‖ * ‖z‖ = ‖z ^ (N + 1) * f z‖
      rw [← norm_mul, pow_succ, mul_right_comm]
    _ ≤ B := hB x

/-- Paper: Lemma D.3.1.2, p. 799. Each polynomially weighted trace belongs to
the indicated Lᵖ space.
Deviation: The single-line bounds also give this for an endpoint when the
carrier is used with a closed interval. -/
theorem schwartzBergman_trace_memLp (I : Set ℝ) (a : I)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) (N : ℕ) (f : schwartzBergmanSubmodule I) :
    MemLp (weightedVerticalTrace a N f.val) p volume := by
  let z (x : ℝ) : ℂ := (a.val : ℂ) + x * Complex.I
  have hz (x : ℝ) : (z x).re = a := by simp [z]
  have hc : Continuous z := by
    dsimp [z]
    fun_prop
  have hf : Continuous (f.val ∘ z) :=
    f.property.2.1.continuousOn.comp_continuous hc fun x ↦ by
      simp [mem_preimage, hz]
  have bound (k : ℕ) : ∃ C : ℝ, ∀ x, ‖z x ^ k * f.val (z x)‖ ≤ C := by
    obtain ⟨C, hC⟩ := f.property.2.2 a a le_rfl (by simp) k
    exact ⟨C, fun x ↦ hC ⟨z x, by simp [mem_preimage, hz], rfl⟩⟩
  obtain ⟨A, hA⟩ := bound N
  obtain ⟨B, hB⟩ := bound (N + 1)
  apply (inverse_linear_weight_memLp p hp hp').of_le_mul (c := A + B)
    ((hc.pow N).mul hf).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖)⁻¹)]
  exact weightedVerticalTrace_le_inverse_weight a N f.val A B hA hB x

/-- Paper: Definition D.3.1.3, p. 800. The weighted L² norm on one line
satisfies the seminorm laws. -/
theorem schwartzBergman_l2_seminorm (I : Set ℝ) (i : I × ℕ) :
    let q (f : schwartzBergmanSubmodule I) :=
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal
    (∀ f g, q (f + g) ≤ q f + q g) ∧ (∀ (c : ℂ) f, q (c • f) = ‖c‖ * q f) := by
  let T (f : schwartzBergmanSubmodule I) := weightedVerticalTrace i.1 i.2 f.val
  have hT (f : schwartzBergmanSubmodule I) : MemLp (T f) 2 volume :=
    schwartzBergman_trace_memLp I i.1 2 (by norm_num) (by norm_num) i.2 f
  constructor
  · intro f g
    have hadd : T (f + g) = T f + T g := by
      funext x
      simp [T, weightedVerticalTrace, mul_add]
    change (eLpNorm (T (f + g)) 2 volume).toReal ≤
      (eLpNorm (T f) 2 volume).toReal + (eLpNorm (T g) 2 volume).toReal
    simp only [toReal_eLpNorm (hT _).aestronglyMeasurable]
    rw [hadd]
    exact lpNorm_add_le (hT f) (by norm_num)
  · intro c f
    have hsmul : T (c • f) = c • T f := by
      funext x
      simp [T, weightedVerticalTrace, smul_eq_mul, mul_left_comm]
    change (eLpNorm (T (c • f)) 2 volume).toReal =
      ‖c‖ * (eLpNorm (T f) 2 volume).toReal
    simp only [toReal_eLpNorm (hT _).aestronglyMeasurable]
    rw [hsmul]
    exact lpNorm_const_smul c (T f) volume

/-- Definition D.3.1.3 cannot use positive rational lines for an arbitrary open interval. -/
theorem positive_abscissae_on_negative_interval_impossible :
    ¬ ∃ a : ℕ → ℚ, ∀ n, (0 : ℚ) < a n ∧ (a n : ℝ) ∈ Ioo (-2 : ℝ) (-1) := by
  rintro ⟨a, ha⟩
  have hp : (0 : ℝ) < (a 0 : ℝ) := by exact_mod_cast (ha 0).1
  linarith [(ha 0).2.2]

/-- Paper: Definition D.3.1.3, p. 800. Equip the Schwartz–Bergman
submodule with the topology of weighted L² convergence on interior vertical lines.
Deviation: Use all lines and p = 2 to make the choice-independent topology canonical.
Lemma D.3.1.2 identifies this with each of the paper's countable families. -/
abbrev SchwartzBergman (I : Set ℝ) :=
  WithGeneratingSeminorms (schwartzBergmanSubmodule I)
    (fun i : I × ℕ ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦
        (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2)

private theorem weightedVerticalTrace_lpNorm_le (a : ℝ) (N : ℕ) (f : ℂ → ℂ)
    {A B : ℝ} (hAB : 0 ≤ A + B)
    (hA : ∀ x, ‖weightedVerticalTrace a N f x‖ ≤ A)
    (hB : ∀ x, ‖weightedVerticalTrace a (N + 1) f x‖ ≤ B) :
    lpNorm (weightedVerticalTrace a N f) 2 volume ≤
      (A + B) * lpNorm (fun x : ℝ ↦ (1 + ‖x‖)⁻¹) 2 volume := by
  let g (x : ℝ) := (1 + ‖x‖)⁻¹
  have hg : MemLp g 2 volume := inverse_linear_weight_memLp 2 (by norm_num) (by norm_num)
  calc
    _ ≤ lpNorm ((A + B) • g) 2 volume :=
      lpNorm_mono_real (hg.const_smul _) (weightedVerticalTrace_le_inverse_weight a N f A B hA hB)
    _ = _ := by
      rw [lpNorm_const_smul]
      change ‖A + B‖ * _ = _
      rw [Real.norm_of_nonneg hAB]

/-- Uniform convergence on each vertical trace with every polynomial weight
implies convergence for the weighted L² topology. -/
theorem schwartzBergman_tendsto_of_weightedTrace {I : Set ℝ} {ι : Type*}
    {l : Filter ι} {u : ι → SchwartzBergman I} {v : SchwartzBergman I}
    (h : ∀ (a : I) (k : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ x, ‖weightedVerticalTrace a k (u i - v).val x‖ ≤ ε) :
    Tendsto u l (𝓝 v) := by
  apply ((withGeneratingSeminorms_spec _ _).tendsto_nhds u v).mpr
  rintro ⟨a, k⟩ ε hε
  let g (x : ℝ) := (1 + ‖x‖)⁻¹
  let C := lpNorm g 2 (volume : Measure ℝ)
  have hC : 0 ≤ C := lpNorm_nonneg
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [h a k δ hδ, h a (k + 1) δ hδ] with i h₁ h₂
  let F := weightedVerticalTrace a k (u i - v).val
  have hF := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) k (u i - v)
  change (eLpNorm F 2 volume).toReal < ε
  rw [toReal_eLpNorm hF.aestronglyMeasurable]
  calc
    lpNorm F 2 volume ≤ (δ + δ) * C :=
      weightedVerticalTrace_lpNorm_le a k (u i - v).val (by positivity) h₁ h₂
    _ < ε := by
      have he : ε = (δ + δ) * (C + 1) := by
        dsimp [δ]
        field_simp
        ring
      nth_rw 1 [he]
      exact mul_lt_mul_of_pos_left (by linarith) (by positivity)

/-- Polynomial bounds on weighted traces give polynomial bounds for every
continuous seminorm of the Schwartz–Bergman topology. -/
theorem schwartzBergman_seminorm_polynomial_bound {I : Set ℝ} {ι : Type*}
    (u : ι → SchwartzBergman I) (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i)
    (h : ∀ (a : I) (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, ‖weightedVerticalTrace a k (u i).val x‖ ≤ C * (w i)^k)
    (q : Seminorm ℂ (SchwartzBergman I)) (hq : Continuous q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (u i) ≤ C * (w i)^N := by
  let p := fun j : I × ℕ ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦
      (eLpNorm (weightedVerticalTrace j.1 j.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I j).1 (schwartzBergman_l2_seminorm I j).2
  have hW := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) p
  obtain ⟨s, K, _, hK⟩ := Seminorm.bound_of_continuous hW q hq
  let L := lpNorm (fun x : ℝ ↦ (1 + ‖x‖)⁻¹) 2 (volume : Measure ℝ)
  have hL : 0 ≤ L := lpNorm_nonneg
  have hb (j : I × ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ i, p j (u i) ≤ D * (w i)^(j.2+1) := by
    obtain ⟨A, hA, h₁⟩ := h j.1 j.2
    obtain ⟨B, hB, h₂⟩ := h j.1 (j.2+1)
    refine ⟨(A+B)*L, by positivity, fun i ↦ ?_⟩
    have hw₀ : 0 ≤ w i := zero_le_one.trans (hw i)
    have hle : (w i)^j.2 ≤ (w i)^(j.2+1) := pow_le_pow_right₀ (hw i) (Nat.le_succ _)
    have h₁' (x : ℝ) : ‖weightedVerticalTrace j.1 j.2 (u i).val x‖ ≤ A * (w i)^(j.2+1) :=
      (h₁ i x).trans (mul_le_mul_of_nonneg_left hle hA)
    have hm := schwartzBergman_trace_memLp I j.1 2 (by norm_num) (by norm_num) j.2 (u i)
    change (eLpNorm (weightedVerticalTrace j.1 j.2 (u i).val) 2 volume).toReal ≤ _
    rw [toReal_eLpNorm hm.aestronglyMeasurable]
    exact (weightedVerticalTrace_lpNorm_le j.1 j.2 (u i).val (by positivity) h₁' (h₂ i)).trans_eq
      (by change (_ + _) * L = _; ring)
  choose D hD hbound using hb
  let N := s.sup fun j : I × ℕ ↦ j.2 + 1
  refine ⟨(K : ℝ) * ∑ j ∈ s, D j,
    mul_nonneg K.coe_nonneg (Finset.sum_nonneg fun j _ ↦ hD j), N, fun i ↦ ?_⟩
  refine (hK (u i)).trans ?_
  change (K : ℝ) * (s.sup p) (show schwartzBergmanSubmodule I from u i) ≤ _
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  have hn (j : I × ℕ) : 0 ≤ D j * (w i)^N :=
    mul_nonneg (hD j) (pow_nonneg (zero_le_one.trans (hw i)) _)
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun j _ ↦ hn j)
  intro j hj
  have hpow : (w i)^(j.2+1) ≤ (w i)^N :=
    pow_le_pow_right₀ (hw i) (Finset.le_sup (f := fun j : I × ℕ ↦ j.2 + 1) hj)
  calc
    _ ≤ D j * (w i)^(j.2+1) := hbound j i
    _ ≤ D j * (w i)^N := mul_le_mul_of_nonneg_left hpow (hD j)
    _ ≤ _ := Finset.single_le_sum (fun j _ ↦ hn j) hj

section VerticalTraces

local notation "linePoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)

theorem exists_bracketing_lines {I : Set ℝ} (hI : IsOpen I) (a : I) :
    ∃ l r : I, (l : ℝ) < a ∧ (a : ℝ) < r := by
  obtain ⟨u, v, hav, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds a.property)
  obtain ⟨l, hul, hla⟩ := exists_between hav.1
  obtain ⟨r, har, hrv⟩ := exists_between hav.2
  exact ⟨⟨l, huv ⟨hul, hla.trans hav.2⟩⟩, ⟨r, huv ⟨hav.1.trans har, hrv⟩⟩, hla, har⟩

/-- Weighted values inside the strip are bounded by the two boundary trace norms. -/
private theorem bergman_interior_lp_bound {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (l r : I) (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D ≥ (0 : ℝ), ∀ (k : ℕ) (f : schwartzBergmanSubmodule I) (z : ℂ),
      (l : ℝ) + δ ≤ z.re → z.re ≤ (r : ℝ) - δ →
        ‖z ^ k * f.val z‖ ≤ D * (lpNorm (weightedVerticalTrace l k f.val) p volume +
          lpNorm (weightedVerticalTrace r k f.val) p volume) := by
  obtain ⟨C, hC, hkernel⟩ := verticalCauchy_lpBound p q hq hq' hδ
  refine ⟨C / (2 * Real.pi), by positivity, ?_⟩
  intro k f z hl hr
  have hlz : (l : ℝ) < z.re := by linarith
  have hzr : z.re < (r : ℝ) := by linarith
  obtain ⟨a, _, hal, _⟩ := exists_bracketing_lines hI l
  obtain ⟨_, b, _, hrb⟩ := exists_bracketing_lines hI r
  let F (w : ℂ) := w ^ k * f.val w
  have hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (a : ℝ) (b : ℝ)) :=
    (differentiableOn_id.pow k).mul (f.property.2.1.mono
      (preimage_mono (Ioo_subset_Icc_self.trans (hInt.out a.property b.property))))
  obtain ⟨M, hM⟩ := f.property.2.2 l r (hlz.trans hzr).le (hInt.out l.property r.property) (k+1)
  have hdec : ∀ᶠ y : ℝ in comap abs atTop, ∀ x ∈ Icc (l : ℝ) r, ‖F (linePoint x y)‖ ≤ max M 0 / |y| := by
    have ht : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
    filter_upwards [ht.eventually (eventually_gt_atTop 0)] with y hy
    intro x hx
    let w := linePoint x y
    have hw : w ∈ Complex.re ⁻¹' Icc (l : ℝ) r := by simpa [w] using hx
    have him : |y| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    apply (le_div_iff₀ hy).mpr
    calc ‖F w‖ * |y| ≤ ‖F w‖ * ‖w‖ := mul_le_mul_of_nonneg_left him (norm_nonneg _)
      _ = ‖w ^ (k+1) * f.val w‖ := by simp only [F, pow_succ, ← norm_mul]; congr 1; ring
      _ ≤ max M 0 := (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  have hL := hkernel (σ := (l : ℝ)) (z := z) (by rw [abs_of_neg (sub_neg.mpr hlz)]; linarith)
    (schwartzBergman_trace_memLp I l p hp hp' k f)
  have hR := hkernel (σ := (r : ℝ)) (z := z) (by rw [abs_of_pos (sub_pos.mpr hzr)]; linarith)
    (schwartzBergman_trace_memLp I r p hp hp' k f)
  have eq := verticalCauchyIntegral_sub_eq hF hal hrb ⟨hlz,hzr⟩ (le_max_right M 0) hdec hL.1 hR.1
  have hb := (norm_sub_le _ _).trans (add_le_add hR.2 hL.2)
  have hb' := (congrArg norm eq.symm).le.trans hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at hb'
  norm_num at hb'
  change ‖F z‖ ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 2 * Real.pi by positivity)).mpr
  calc ‖F z‖ * (2 * Real.pi) ≤ C * lpNorm (weightedVerticalTrace r k f.val) p volume +
        C * lpNorm (weightedVerticalTrace l k f.val) p volume := by simpa only [mul_comm ‖F z‖] using hb'
    _ = _ := by ring

/-- Differentiating a holomorphic function along a vertical trace introduces a factor of i. -/
private theorem hasDerivAt_vertical_iterate {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y))
      (Complex.I ^ (n+1) * iteratedDeriv (n+1) f (linePoint a x)) x := by
  have hU := hI.preimage Complex.continuous_re
  have han : ∀ m, AnalyticOnNhd ℂ (iteratedDeriv m f) (Complex.re ⁻¹' I) := by
    intro m
    induction m with
    | zero => simpa using hf.analyticOnNhd hU
    | succ m ih => rw [iteratedDeriv_succ]; exact fun z hz ↦ (ih z hz).deriv
  have hd := (han n _ (show linePoint a x ∈ Complex.re ⁻¹' I by simp)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I (x : ℂ) := by
    simpa using (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).const_add (a.val : ℂ))
  have h := ((hd.comp (x : ℂ) hline).comp_ofReal).const_mul (Complex.I ^ n)
  simpa only [Function.comp_apply, iteratedDeriv_succ, pow_succ, mul_left_comm,
    mul_assoc, mul_comm (deriv _ _)] using h

private theorem iteratedDeriv_vertical {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ ↦ f (linePoint a y)) =
      fun y ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_vertical_iterate hI a hf n x).deriv

/-- Both neighboring trace norms control each Schwartz seminorm on the intermediate line. -/
private theorem bergman_line_lp_bound {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (l a r : I) (hl : (l : ℝ) < a) (hr : (a : ℝ) < r)
    (p q : ℝ≥0∞) [ENNReal.HolderTriple p q 1] (hp : 1 < p) (hp' : p < ⊤)
    (hq : 1 < q) (hq' : q < ⊤) (k n : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ (f : schwartzBergmanSubmodule I) (y : ℝ),
      |y| ^ k * ‖iteratedDeriv n (fun u : ℝ ↦ f.val (linePoint a u)) y‖ ≤
        C * (lpNorm (weightedVerticalTrace l k f.val) p volume +
          lpNorm (weightedVerticalTrace r k f.val) p volume) := by
  let d := min ((a : ℝ) - l) ((r : ℝ) - a) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hl' : (l : ℝ) + 2 * d ≤ a := by dsimp [d]; linarith [min_le_left ((a : ℝ) - l) ((r : ℝ) - a)]
  have hr' : (a : ℝ) + 2 * d ≤ r := by dsimp [d]; linarith [min_le_right ((a : ℝ) - l) ((r : ℝ) - a)]
  obtain ⟨D, hD, hbound⟩ := bergman_interior_lp_bound hI hInt l r p q hp hp' hq hq' hd
  refine ⟨n.factorial * (2 ^ k * D) / (d/4)^n, by positivity, ?_⟩
  intro f y
  let z := linePoint a y
  have hre : z.re = a := by simp [z]
  let Q := lpNorm (weightedVerticalTrace l k f.val) p volume + lpNorm (weightedVerticalTrace r k f.val) p volume
  have hQ : 0 ≤ Q := add_nonneg lpNorm_nonneg lpNorm_nonneg
  obtain ⟨R, hRlo, hRhi, hweight⟩ : ∃ R : ℝ, d/4 ≤ R ∧ R ≤ d ∧
      ∀ w ∈ Metric.sphere z R, ‖z‖ ≤ 2 * ‖w‖ := by
    by_cases hz : ‖z‖ ≤ d/2
    · refine ⟨d, by linarith, le_rfl, ?_⟩
      intro w hw
      have ht := dist_le_norm_add_norm w z
      rw [Metric.mem_sphere.mp hw] at ht
      linarith
    · refine ⟨d/4, le_rfl, by linarith, ?_⟩
      intro w hw
      have ht := norm_sub_norm_le z w
      rw [← dist_eq_norm, dist_comm, Metric.mem_sphere.mp hw] at ht
      linarith
  have hstrip {w : ℂ} (hw : w ∈ Metric.closedBall z R) :
      (l : ℝ) + d ≤ w.re ∧ w.re ≤ (r : ℝ) - d := by
    have h := (Complex.abs_re_le_norm (w-z)).trans (mem_closedBall_iff_norm.mp hw)
    rw [Complex.sub_re, hre, abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hdiff := (f.property.2.1.const_mul (z ^ k)).diffContOnCl_ball (c := z) (R := R)
    (fun w hw ↦ hInt.out l.property r.property ⟨by linarith [(hstrip hw).1], by linarith [(hstrip hw).2]⟩)
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z R) : ‖z ^ k * f.val w‖ ≤ 2 ^ k * (D * Q) := by
    have hs := hstrip (Metric.sphere_subset_closedBall hw)
    calc ‖z ^ k * f.val w‖ = ‖z‖ ^ k * ‖f.val w‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 * ‖w‖)^k * ‖f.val w‖ := by gcongr; exact hweight w hw
      _ = 2 ^ k * ‖w ^ k * f.val w‖ := by rw [mul_pow, norm_mul, norm_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound k f w hs.1 hs.2) (by positivity)
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by linarith : 0 < R) hdiff hcircle
  rw [iteratedDeriv_const_mul_field, norm_mul, norm_pow] at hest
  rw [iteratedDeriv_vertical hI a f.property.2.1, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  calc |y| ^ k * ‖iteratedDeriv n f.val z‖ ≤ ‖z‖ ^ k * ‖iteratedDeriv n f.val z‖ := by
        gcongr
        simpa [z] using Complex.abs_im_le_norm z
    _ ≤ _ := hest
    _ ≤ n.factorial * (2 ^ k * (D * Q)) / (d/4)^n := div_le_div_of_nonneg_left
      (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) hRlo n)
    _ = _ := by dsimp only [Q]; ring

/-- Paper: Lemma D.3.1.2, p. 799. Restriction to a vertical line as a real Schwartz function. -/
private def bergmanLine {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a : I) : SchwartzBergman I →ₗ[ℂ] 𝓢(ℝ, ℂ) where
  toFun f := {
    toFun := fun x ↦ f.val (linePoint a x)
    smooth' := by
      apply contDiff_of_differentiable_iteratedDeriv
      intro n _ x
      rw [iteratedDeriv_vertical hI a f.property.2.1]
      exact (hasDerivAt_vertical_iterate hI a f.property.2.1 n x).differentiableAt
    decay' := by
      intro k n
      obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
      obtain ⟨C, _, h⟩ := bergman_line_lp_bound hI hInt l a r hl hr 2 2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) k n
      exact ⟨_, fun x ↦ by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using h f x⟩ }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Multiply a Schwartz function by the vertical polynomial weight and include it in Lᵖ. -/
private def weightedSchwartzLp (a : ℝ) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ p (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ p volume).comp (SchwartzMap.smulLeftCLM ℂ fun y : ℝ ↦ (linePoint a y)^k)

/-- Paper: (D.3.1.7), p. 799. The weighted Lᵖ norm of the trace on a single line. -/
private def bergmanLpSeminorm {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : I) (k : ℕ) : Seminorm ℂ (SchwartzBergman I) :=
  (normSeminorm ℂ _).comp ((weightedSchwartzLp a k p).toLinearMap.comp (bergmanLine hI hInt a))

private theorem bergmanLpSeminorm_apply {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : I) (k : ℕ) (f : SchwartzBergman I) :
    bergmanLpSeminorm hI hInt p a k f = lpNorm (weightedVerticalTrace a k f.val) p volume := by
  change ‖((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (linePoint a y)^k)) (bergmanLine hI hInt a f)).toLp p volume‖ = _
  rw [SchwartzMap.norm_toLp, toReal_eLpNorm (SchwartzMap.continuous _).aestronglyMeasurable]
  congr 1
  have hg : (fun y : ℝ ↦ (linePoint a y) ^ k).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.smulLeftCLM_apply hg]
  rfl

private theorem bergman_with_l2 {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) :
    WithSeminorms (fun i : I × ℕ ↦ bergmanLpSeminorm hI hInt 2 i.1 i.2) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have heq : (fun i : I × ℕ ↦ bergmanLpSeminorm hI hInt 2 i.1 i.2) = P := by
    funext i
    ext f
    exact (bergmanLpSeminorm_apply hI hInt 2 i.1 i.2 f).trans
      (toReal_eLpNorm (schwartzBergman_trace_memLp I i.1 2
        (by norm_num) (by norm_num) i.2 f).aestronglyMeasurable).symm
  rw [heq]
  exact withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P

private theorem continuous_bergmanLine_of_bracketing {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a l r : I) (hl : (l : ℝ) < a) (hr : (a : ℝ) < r)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [ENNReal.HolderTriple p q 1]
    (hp : 1 < p) (hp' : p < ⊤) (hq : 1 < q) (hq' : q < ⊤)
    [t : TopologicalSpace (SchwartzBergman I)] [IsTopologicalAddGroup (SchwartzBergman I)]
    (hL : ∀ k, Continuous (bergmanLpSeminorm hI hInt p l k))
    (hR : ∀ k, Continuous (bergmanLpSeminorm hI hInt p r k)) :
    Continuous (bergmanLine hI hInt a) := by
  apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
  rintro ⟨k,n⟩
  obtain ⟨C, hC, hb⟩ := bergman_line_lp_bound hI hInt l a r hl hr p q hp hp' hq hq' k n
  let c : ℝ≥0 := ⟨C,hC⟩
  apply Seminorm.continuous_of_le (q := c • (bergmanLpSeminorm hI hInt p l k + bergmanLpSeminorm hI hInt p r k))
    (((hL k).add (hR k)).const_smul c)
  intro f
  change SchwartzMap.seminorm ℂ k n (bergmanLine hI hInt a f) ≤
    C * (bergmanLpSeminorm hI hInt p l k f + bergmanLpSeminorm hI hInt p r k f)
  rw [bergmanLpSeminorm_apply, bergmanLpSeminorm_apply]
  apply SchwartzMap.seminorm_le_bound' _ _ _ _ (mul_nonneg hC (add_nonneg lpNorm_nonneg lpNorm_nonneg))
  exact hb f

private theorem continuous_bergmanLine {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (a : I) : Continuous (bergmanLine hI hInt a) := by
  obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
  have hc := (bergman_with_l2 hI hInt).continuous_seminorm
  exact continuous_bergmanLine_of_bracketing hI hInt a l r hl hr 2 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun k ↦ hc (l,k)) (fun k ↦ hc (r,k))

theorem le_topology_withSeminorms {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] [IsTopologicalAddGroup E] {u : TopologicalSpace E}
    {P : ι → Seminorm ℂ E} (hP : WithSeminorms (topology := u) P)
    (hc : ∀ i, Continuous[t, _] (P i)) : t ≤ u :=
  continuous_id_iff_le.mp (@WithSeminorms.continuous_of_continuous_comp ℂ ℂ E E ι
    _ _ _ _ _ _ (RingHom.id ℂ) _ P t _ u hP (LinearMap.id (R := ℂ)) hc)

private theorem bergman_embedding {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I) :
    IsEmbedding (fun (f : SchwartzBergman I) (a : I) ↦ bergmanLine hI hInt a f) := by
  let T := LinearMap.pi (bergmanLine hI hInt)
  change IsEmbedding T
  have hcont : Continuous T := continuous_pi (continuous_bergmanLine hI hInt)
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, ?_⟩
  · let t := TopologicalSpace.induced T inferInstance
    have hT : Continuous[t, _] T := continuous_induced_dom
    have hprod := withSeminorms_pi fun _ : I ↦ schwartz_withSeminorms ℂ ℝ ℂ
    have hsource := bergman_with_l2 hI hInt
    let : TopologicalSpace (SchwartzBergman I) := t
    let : IsTopologicalAddGroup (SchwartzBergman I) := (T.withSeminorms_induced hprod).topologicalAddGroup
    apply le_topology_withSeminorms (t := t) hsource
    rintro ⟨a,k⟩
    exact ((weightedSchwartzLp a k 2).continuous.comp ((continuous_apply a).comp hT)).norm
  · intro f g h
    apply Subtype.ext
    funext z
    by_cases hz : z.re ∈ I
    · have eq := congrArg (fun v : 𝓢(ℝ, ℂ) ↦ v z.im) (congrFun h ⟨z.re, hz⟩)
      change f.val (linePoint z.re z.im) = g.val (linePoint z.re z.im) at eq
      simpa only [Complex.re_add_im] using eq
    · exact (f.property.1 hz).trans (g.property.1 hz).symm

end VerticalTraces

/-- A family of transforms belongs to Lᵖ and generates the topology by its Lᵖ norms. -/
def GeneratesLpSeminorms {E ι X : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    (u : ι → E → X → ℂ) : Prop :=
  (∀ i f, MemLp (u i f) p μ) ∧
    ∃ P : SeminormFamily ℂ E ι, WithSeminorms P ∧
      ∀ i f, ENNReal.ofReal (P i f) = eLpNorm (u i f) p μ

/-- Paper: Lemma D.3.1.2, p. 799. Weighted Lᵖ norms on a sequence of lines
reaching both ends of the interval generate the Schwartz–Bergman topology.
Deviation: The endpoint condition is expressed by bracketing every real point of I. -/
theorem schwartzBergman_lp_generates (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (a : ℕ → I)
    (ha : ∀ x : I, (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) :
    GeneratesLpSeminorms volume p
      (fun (i : ℕ × ℕ) (f : SchwartzBergman I) ↦ weightedVerticalTrace (a i.1) i.2 f.val) := by
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  let q := ENNReal.conjExponent p
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp'
  have hq' : q < ⊤ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp
  let P : SeminormFamily ℂ (SchwartzBergman I) (ℕ × ℕ) := fun i ↦ bergmanLpSeminorm hI hInt p (a i.1) i.2
  have hmem (i : ℕ × ℕ) (f : SchwartzBergman I) := schwartzBergman_trace_memLp I (a i.1) p hp hp' i.2 f
  refine ⟨hmem, P, ?_, ?_⟩
  · have hc (i : ℕ × ℕ) : Continuous (P i) :=
      ((weightedSchwartzLp (a i.1) i.2 p).continuous.comp (continuous_bergmanLine hI hInt (a i.1))).norm
    let t : TopologicalSpace (SchwartzBergman I) := inferInstance
    let u := P.moduleFilterBasis.topology
    have hP : WithSeminorms (topology := u) P := ⟨rfl⟩
    refine WithSeminorms.mk (topology := t) ?_
    change t = u
    apply le_antisymm
    · exact le_topology_withSeminorms (t := t) hP hc
    · have h2 := bergman_with_l2 hI hInt
      let : TopologicalSpace (SchwartzBergman I) := u
      let : IsTopologicalAddGroup (SchwartzBergman I) := hP.topologicalAddGroup
      apply le_topology_withSeminorms (t := u) h2
      rintro ⟨s,k⟩
      obtain ⟨⟨j,hj⟩, m, hm⟩ := ha s
      have hs := continuous_bergmanLine_of_bracketing (t := u) hI hInt s (a j) (a m) hj hm p q
        hp hp' hq hq' (fun k ↦ hP.continuous_seminorm (j,k)) (fun k ↦ hP.continuous_seminorm (m,k))
      exact ((weightedSchwartzLp s k 2).continuous.comp hs).norm
  · intro i f
    dsimp only [P]
    rw [bergmanLpSeminorm_apply, ← toReal_eLpNorm (hmem i f).aestronglyMeasurable,
      ENNReal.ofReal_toReal (hmem i f).eLpNorm_ne_top]

/-- Paper: Lemma D.3.1.2, p. 799. The topology also comes from taking the
Schwartz restriction to each vertical line. -/
theorem schwartzBergman_schwartzLine_topology (I : Set ℝ) (hI : IsOpen I)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∃ T : SchwartzBergman I → (I → 𝓢(ℝ, ℂ)),
      (∀ f (a : I) x, T f a x = weightedVerticalTrace a 0 f.val x) ∧ IsEmbedding T :=
  by
    refine ⟨fun f a ↦ bergmanLine hI hInt a f, ?_, bergman_embedding hI hInt⟩
    intro f a x
    simp only [weightedVerticalTrace, pow_zero, one_mul]
    rfl

/-- Evaluation of each holomorphic derivative at an interior point of the
strip is continuous in the Schwartz–Bergman topology. -/
theorem exists_schwartzBergman_jetEvaluation {I : Set ℝ} (hI : IsOpen I)
    (hInt : OrdConnected I) (z : ℂ) (hz : z.re ∈ I) (n : ℕ) :
    ∃ L : SchwartzBergman I →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n f.val z := by
  let a : I := ⟨z.re, hz⟩
  let T : SchwartzBergman I →L[ℂ] 𝓢(ℝ, ℂ) :=
    ⟨bergmanLine hI hInt a, continuous_bergmanLine hI hInt a⟩
  let D := SchwartzMap.derivCLM ℂ ℂ ^ n
  let E : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
    { toFun := fun u ↦ u z.im
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := (BoundedContinuousFunction.lipschitz_eval_const z.im).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous }
  have hD (u : 𝓢(ℝ, ℂ)) (k : ℕ) :
      ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) u) = iteratedDeriv k u := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) u)) = _
      rw [ih]
  refine ⟨(Complex.I ^ n)⁻¹ • (E.comp (D.comp T)), fun f ↦ ?_⟩
  have hline : (a.val : ℂ) + (z.im : ℂ) * Complex.I = z := by
    change (z.re : ℂ) + z.im * Complex.I = z
    exact Complex.re_add_im z
  have hv : iteratedDeriv n ((T f) : ℝ → ℂ) z.im =
      Complex.I ^ n * iteratedDeriv n f.val ((a.val : ℂ) + (z.im : ℂ) * Complex.I) :=
    congrFun (iteratedDeriv_vertical hI a f.property.2.1 n) z.im
  change (Complex.I ^ n)⁻¹ * (D (T f)) z.im = _
  calc
    _ = (Complex.I ^ n)⁻¹ * iteratedDeriv n ((T f) : ℝ → ℂ) z.im :=
      congrArg ((Complex.I ^ n)⁻¹ * ·) (congrFun (hD (T f) n) z.im)
    _ = (Complex.I ^ n)⁻¹ *
        (Complex.I ^ n * iteratedDeriv n f.val ((a.val : ℂ) + (z.im : ℂ) * Complex.I)) :=
      congrArg ((Complex.I ^ n)⁻¹ * ·) hv
    _ = _ := by
      rw [hline, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is separable. -/
theorem schwartzBergman_separable (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : SeparableSpace (SchwartzBergman I) := by
  let : Nonempty I := hne.to_subtype
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq I
  have hbr (x : I) : (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n := by
    obtain ⟨l,r,hl,hr⟩ := exists_bracketing_lines hI x
    exact ⟨ha.exists_mem_open isOpen_Iio ⟨l,hl⟩, ha.exists_mem_open isOpen_Ioi ⟨r,hr⟩⟩
  obtain ⟨hmem, P, hP, hval⟩ := schwartzBergman_lp_generates I hI hInt hne a hbr 2 (by norm_num) (by norm_num)
  let L (i : ℕ × ℕ) := (weightedSchwartzLp (a i.1) i.2 2).toLinearMap.comp (bergmanLine hI hInt (a i.1))
  let T := LinearMap.pi L
  have heq (i : ℕ × ℕ) : P i = (normSeminorm ℂ _).comp (L i) := by
    ext f
    change P i f = bergmanLpSeminorm hI hInt 2 (a i.1) i.2 f
    rw [bergmanLpSeminorm_apply, ← toReal_eLpNorm (hmem i f).aestronglyMeasurable]
    exact (ENNReal.toReal_ofReal (apply_nonneg (P i) f)).symm.trans (congrArg ENNReal.toReal (hval i f))
  have hprod := withSeminorms_pi fun _ : ℕ × ℕ ↦ norm_withSeminorms ℂ (Lp ℂ 2 (volume : Measure ℝ))
  have hi : IsInducing T := by
    constructor
    apply le_antisymm
    · exact continuous_iff_le_induced.mp (continuous_pi fun i ↦
        (weightedSchwartzLp (a i.1) i.2 2).continuous.comp
          (continuous_bergmanLine hI hInt (a i.1)))
    · let t := TopologicalSpace.induced T inferInstance
      have hT : Continuous[t, _] T := continuous_induced_dom
      let : TopologicalSpace (SchwartzBergman I) := t
      let : IsTopologicalAddGroup (SchwartzBergman I) :=
        (T.withSeminorms_induced hprod).topologicalAddGroup
      apply le_topology_withSeminorms (t := t) hP
      intro i
      rw [heq]
      exact ((continuous_apply i).comp hT).norm
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have := hi.secondCountableTopology
  infer_instance

end Bergman


end
end Masullo
