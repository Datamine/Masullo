/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import SchwartzBergman
import SchwartzComplete
import TopologicalLinearLimits
import MellinStrip
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped ContDiff NNReal ENNReal SchwartzMap Asymptotics

namespace Masullo

noncomputable section

/-- Pullback along a continuous linear equivalence, with pullback by its inverse as inverse. -/
def schwartzChangeVariable (𝕜 : Type*) [RCLike 𝕜]
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    (e : D ≃L[ℝ] E) : 𝓢(E, F) ≃L[𝕜] 𝓢(D, F) where
  __ := SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 e
  invFun := SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 e.symm
  left_inv f := by ext x; change f (e (e.symm x)) = f x; rw [e.apply_symm_apply]
  right_inv f := by ext x; change f (e.symm (e x)) = f x; rw [e.symm_apply_apply]
  continuous_invFun := (SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 e.symm).continuous


/-- A bounded holomorphic function with polynomially weighted bounds on the two edges
of a vertical strip satisfies the same weighted bound throughout the strip. -/
theorem norm_pow_mul_le_on_verticalStrip {a b : ℝ} (hab : a < b) {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo a b)) {M : ℝ}
    (hM : ∀ z : ℂ, z.re ∈ Icc a b → ‖F z‖ ≤ M) (n : ℕ) {C : ℝ}
    (ha : ∀ z : ℂ, z.re = a → ‖z ^ n * F z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖z ^ n * F z‖ ≤ C)
    (z : ℂ) (hz : z.re ∈ Icc a b) : ‖z ^ n * F z‖ ≤ C := by
  let c := Real.pi / (b - a) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : DiffContOnCl ℂ (fun w : ℂ ↦ w ^ n * F w) (Complex.re ⁻¹' Ioo a b) :=
    ⟨(differentiableOn_id.pow n).mul hF.1, (continuousOn_id.pow n).mul hF.2⟩
  apply PhragmenLindelof.vertical_strip hd _ ha hb hz.1 hz.2
  refine ⟨c, half_lt_self (div_pos Real.pi_pos (sub_pos.mpr hab)), 1, ?_⟩
  let R := |a| + |b|
  apply Asymptotics.IsBigO.of_bound (M * (n.factorial / c ^ n) * Real.exp (c * R))
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro w hw
  have hRe : |w.re| ≤ R := by
    change a < w.re ∧ w.re < b at hw
    dsimp [R]
    exact abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hn : ‖w‖ ^ n ≤ (n.factorial / c ^ n) * Real.exp (c * ‖w‖) := by
    have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le (norm_nonneg w)) n
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith only [h]
  have he : Real.exp (c * ‖w‖) ≤ Real.exp (c * R) * Real.exp (c * |w.im|) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((Complex.norm_le_abs_re_add_abs_im w).trans (add_le_add hRe le_rfl)) hc.le)
  have hM0 := (norm_nonneg (F w)).trans (hM w ⟨hw.1.le, hw.2.le⟩)
  simp only [norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
  calc
    ‖w‖ ^ n * ‖F w‖ ≤ ((n.factorial / c ^ n) * Real.exp (c * ‖w‖)) * M :=
      mul_le_mul hn (hM w ⟨hw.1.le, hw.2.le⟩) (norm_nonneg _) (by positivity)
    _ ≤ ((n.factorial / c ^ n) * (Real.exp (c * R) * Real.exp (c * |w.im|))) * M := by gcongr
    _ ≤ _ := by
      have ht := Real.add_one_le_exp (Real.exp (c * |w.im|))
      have ht' : Real.exp (c * |w.im|) ≤ Real.exp (Real.exp (c * |w.im|)) := by linarith
      calc
        _ = (M * (n.factorial / c ^ n) * Real.exp (c * R)) * Real.exp (c * |w.im|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ht' (by positivity)


/-- A logarithmic profile has an absolutely convergent Mellin integral at `s` if its
exponential weight at the real part of `s` is integrable on the real line. -/
theorem mellinConvergent_of_integrable_logWeight (f : ℝ → ℂ) (s : ℂ)
    (h : Integrable (fun x : ℝ ↦ (Real.exp (s.re * x) : ℂ) * f x)) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  let phase (x : ℝ) := Complex.exp ((x : ℂ) * (s - s.re))
  have hc : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hunit (x : ℝ) : ‖phase x‖ ≤ 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  have changeVariables (g : ℝ → ℂ) :
      Integrable (fun x ↦ Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Ioi 0) := by
    rw [← integrableOn_univ, ← Real.range_exp, ← image_univ]
    symm
    simpa using integrableOn_image_iff_integrableOn_abs_deriv_smul
      .univ (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  apply (changeVariables _).mp
  apply (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hunit)).congr
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [phase, Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

section PositiveReal

/-- Paper: Definition D.3.2.1, p. 801. A real Schwartz map is viewed as a
function by the linear forgetful map. -/
def realSchwartzCoe : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Paper: Definition D.3.2.1, p. 801. Forgetting the Schwartz properties
retains the values of the function. -/
theorem realSchwartzCoe_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : realSchwartzCoe f x = f x := rfl

/-- Paper: Definition D.3.2.1, p. 801. In logarithmic coordinates, weighting
by tᵃ amounts to multiplying by exp(ax). -/
def logExponentialWeight (a : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  LinearMap.mulLeft ℂ (fun x : ℝ ↦ (Real.exp (a * x) : ℂ))

/-- Paper: Definition D.3.2.1, p. 801. The weight at exponent zero does not
change the function. -/
theorem logExponentialWeight_zero (f : ℝ → ℂ) : logExponentialWeight 0 f = f := by
  ext x
  simp [logExponentialWeight, LinearMap.mulLeft]

/-- Paper: Definition D.3.2.1, p. 801. A logarithmic profile belongs to the
decay submodule if each weighted profile is a real-line Schwartz function.
Deviation: The carrier is in the logarithmic coordinate x = log t. -/
def logExponentialDecaySubmodule (I : Set ℝ) : Submodule ℂ (ℝ → ℂ) :=
  ⨅ a : I, realSchwartzCoe.range.comap (logExponentialWeight a)

/-- A compactly supported smooth profile has Schwartz decay after every real exponential twist. -/
theorem mem_logExponentialDecaySubmodule_of_hasCompactSupport (I : Set ℝ) {f : ℝ → ℂ}
    (hs : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) : f ∈ logExponentialDecaySubmodule I := by
  apply (Submodule.mem_iInf _).2
  intro a
  let w (x : ℝ) : ℂ := Real.exp ((a : ℝ) * x)
  have hw : ContDiff ℝ ∞ w :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)
  exact ⟨(hs.mul_left (f := w)).toSchwartzMap (hw.mul hf), rfl⟩

/-- Paper: Definition D.3.2.1, p. 801. The multiplier Tₐ is the weighted
profile, bundled as a Schwartz map. -/
theorem logExponentialDecay_weight_mem_range (I : Set ℝ)
    (a : I) (f : logExponentialDecaySubmodule I) :
    logExponentialWeight a f.val ∈ realSchwartzCoe.range := by
  exact (Submodule.mem_iInf _).mp f.property a

/-- Paper: (D.3.2.1), p. 801. This is the linear multiplier to the space
of Schwartz functions in logarithmic coordinates. -/
def logExponentialDecayTwist (I : Set ℝ) (a : I) : logExponentialDecaySubmodule I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (LinearEquiv.ofInjective realSchwartzCoe DFunLike.coe_injective).symm.toLinearMap.comp
    (((logExponentialWeight a).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      realSchwartzCoe.range (logExponentialDecay_weight_mem_range I a))

/-- Paper: (D.3.2.1), p. 801. The bundled multiplier evaluates to
exp(ax) times the original logarithmic profile. -/
theorem logExponentialDecayTwist_apply (I : Set ℝ) (a : I)
    (f : logExponentialDecaySubmodule I) (x : ℝ) :
    logExponentialDecayTwist I a f x = (Real.exp ((a : ℝ) * x) : ℂ) * f.val x := by
  exact congrFun (LinearEquiv.ofInjective_symm_apply realSchwartzCoe
    (h := DFunLike.coe_injective)
    ⟨logExponentialWeight a f.val, logExponentialDecay_weight_mem_range I a f⟩) x

/-- Paper: Definition D.3.2.1, p. 801. The topology is induced by
all weighted Schwartz profiles, using the usual seminorms on the real Schwartz space.
Deviation: Positive real functions are represented by their logarithmic profiles. -/
abbrev PositiveRealExponentialDecay (I : Set ℝ) :=
  WithGeneratingSeminorms (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))

/-- Paper: Definition D.3.2.1, p. 801. The family of weighted profiles embeds
the decay space in a product of real Schwartz spaces. -/
theorem positiveRealExponentialDecay_isEmbedding (I : Set ℝ) (hne : I.Nonempty) :
    IsEmbedding (fun (f : PositiveRealExponentialDecay I) (a : I) ↦
      logExponentialDecayTwist I a f) := by
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hp := withSeminorms_pi fun _ : I ↦ schwartz_withSeminorms ℂ ℝ ℂ
  have hsource := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))
  change IsEmbedding T
  constructor
  · constructor
    apply le_antisymm
    · apply continuous_iff_le_induced.mp
      apply continuous_pi
      intro a
      let Tₐ : PositiveRealExponentialDecay I →ₗ[ℂ] 𝓢(ℝ, ℂ) := logExponentialDecayTwist I a
      change Continuous Tₐ
      apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp Tₐ
      intro i
      exact hsource.continuous_seminorm (a, i)
    · let t := TopologicalSpace.induced T inferInstance
      have hT : Continuous[t, _] T := continuous_induced_dom
      let : TopologicalSpace (PositiveRealExponentialDecay I) := t
      let : IsTopologicalAddGroup (PositiveRealExponentialDecay I) :=
        (T.withSeminorms_induced hp).topologicalAddGroup
      apply le_topology_withSeminorms (t := t) hsource
      rintro ⟨a, k, n⟩
      exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n)).comp
        ((continuous_apply a).comp hT)
  · intro f g h
    obtain ⟨a, ha⟩ := hne
    apply Subtype.ext
    funext x
    have hx := congrArg (fun F : 𝓢(ℝ, ℂ) ↦ F x) (congrFun h ⟨a, ha⟩)
    change logExponentialDecayTwist I ⟨a, ha⟩ f x = logExponentialDecayTwist I ⟨a, ha⟩ g x at hx
    rw [logExponentialDecayTwist_apply I ⟨a, ha⟩ f x,
      logExponentialDecayTwist_apply I ⟨a, ha⟩ g x] at hx
    exact mul_left_cancel₀ (by exact_mod_cast (Real.exp_pos (a * x)).ne') hx

private theorem logExponentialWeight_add (a b : ℝ) (f : ℝ → ℂ) :
    logExponentialWeight a (logExponentialWeight b f) = logExponentialWeight (a + b) f := by
  ext x
  change (Real.exp (a * x) : ℂ) * ((Real.exp (b * x) : ℂ) * f x) =
    (Real.exp ((a + b) * x) : ℂ) * f x
  rw [add_mul, Real.exp_add, Complex.ofReal_mul, mul_assoc]

private def logExponentialShift {I J : Set ℝ} (hJ : J.Nonempty) (a : ℝ)
    (ha : ∀ b ∈ J, b + a ∈ I) :
    PositiveRealExponentialDecay I →L[ℂ] PositiveRealExponentialDecay J := by
  let shift : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay J :=
    ((logExponentialWeight a).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      (logExponentialDecaySubmodule J) (fun f => (Submodule.mem_iInf _).mpr fun b => by
        change logExponentialWeight b (logExponentialWeight a f.val) ∈ realSchwartzCoe.range
        rw [logExponentialWeight_add]
        exact logExponentialDecay_weight_mem_range I ⟨b + a, ha b b.property⟩ f)
  refine ⟨shift, (positiveRealExponentialDecay_isEmbedding J hJ).isInducing.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro b
  let d : I := ⟨b + a, ha b b.property⟩
  have hI : I.Nonempty := ⟨d, d.property⟩
  have h := (continuous_apply d).comp (positiveRealExponentialDecay_isEmbedding I hI).continuous
  refine h.congr fun f => ?_
  apply DFunLike.ext
  intro x
  change logExponentialDecayTwist I d f x = logExponentialDecayTwist J b (shift f) x
  erw [logExponentialDecayTwist_apply, logExponentialDecayTwist_apply]
  exact congrFun (logExponentialWeight_add b a f.val).symm x

private theorem logExponentialShift_val {I J : Set ℝ} (hJ : J.Nonempty) (a : ℝ)
    (ha : ∀ b ∈ J, b + a ∈ I) (f : PositiveRealExponentialDecay I) :
    (logExponentialShift hJ a ha f).val = logExponentialWeight a f.val := rfl

/-- Remark D.3.3.6 for the positive real group. Multiplication by the modulus to power
`a` reindexes the defining Schwartz twists by subtracting `a` from the weight set.
Adapted from RiemannMasullo commit 3cb5076. -/
def positiveRealExponentialDecay_shift (I : Set ℝ) (hI : I.Nonempty) (a : ℝ) :
    PositiveRealExponentialDecay I ≃L[ℂ]
      PositiveRealExponentialDecay ((fun b : ℝ => b - a) '' I) := by
  let J := (fun b : ℝ => b - a) '' I
  have hJ : J.Nonempty := hI.image _
  let forward := logExponentialShift hJ a (I := I) (by
    rintro _ ⟨b, hb, rfl⟩
    rwa [sub_add_cancel])
  let backward := logExponentialShift hI (-a) (I := J) (fun b hb => ⟨b, hb, sub_eq_add_neg b a⟩)
  refine ContinuousLinearEquiv.equivOfInverse forward backward ?_ ?_
  · intro f
    apply Subtype.ext
    dsimp only [forward, backward]
    erw [logExponentialShift_val, logExponentialShift_val]
    rw [logExponentialWeight_add, neg_add_cancel, logExponentialWeight_zero]
  · intro f
    apply Subtype.ext
    dsimp only [forward, backward]
    erw [logExponentialShift_val, logExponentialShift_val]
    rw [logExponentialWeight_add, add_neg_cancel, logExponentialWeight_zero]

@[simp] theorem positiveRealExponentialDecay_shift_apply (I : Set ℝ) (hI : I.Nonempty)
    (a : ℝ) (f : PositiveRealExponentialDecay I) (x : ℝ) :
    (positiveRealExponentialDecay_shift I hI a f).val x = (Real.exp (a * x) : ℂ) * f.val x := by
  unfold positiveRealExponentialDecay_shift
  erw [ContinuousLinearEquiv.equivOfInverse_apply, logExponentialShift_val]
  rfl

private def phaseMultiplier (t : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  LinearMap.mulLeft ℂ (fun x : ℝ => Complex.exp (((t : ℂ) * Complex.I) * (x : ℂ)))

private def positiveRealExponentialDecay_phaseCLM (I : Set ℝ) (hI : I.Nonempty) (t : ℝ) :
    PositiveRealExponentialDecay I →L[ℂ] PositiveRealExponentialDecay I := by
  let phase : ℝ → ℂ := fun x => Complex.exp (((t : ℂ) * Complex.I) * (x : ℂ))
  let S := SchwartzMap.smulLeftCLM ℂ phase
  have hS (g : 𝓢(ℝ, ℂ)) (x : ℝ) : S g x = phase x * g x :=
    SchwartzMap.smulLeftCLM_apply_apply (mellinPhase_hasTemperateGrowth t) g x
  have comm (a : ℝ) (f : ℝ → ℂ) :
      logExponentialWeight a (phaseMultiplier t f) = phaseMultiplier t (logExponentialWeight a f) := by
    ext x
    change (Real.exp (a * x) : ℂ) * (phase x * f x) = phase x * ((Real.exp (a * x) : ℂ) * f x)
    exact mul_left_comm _ _ _
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I :=
    ((phaseMultiplier t).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      (logExponentialDecaySubmodule I) (fun f => (Submodule.mem_iInf _).mpr fun b => by
        change logExponentialWeight b (phaseMultiplier t f.val) ∈ realSchwartzCoe.range
        rw [comm]
        obtain ⟨g, hg⟩ := logExponentialDecay_weight_mem_range I b f
        refine ⟨S g, ?_⟩
        funext x
        change S g x = phase x * logExponentialWeight b f.val x
        rw [hS, ← hg]
        rfl)
  have hTop := (positiveRealExponentialDecay_isEmbedding I hI).isInducing
  refine ⟨T, hTop.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro b
  have h := S.continuous.comp ((continuous_apply b).comp hTop.continuous)
  refine h.congr fun f => ?_
  apply DFunLike.ext
  intro x
  change S (logExponentialDecayTwist I b f) x = logExponentialDecayTwist I b (T f) x
  erw [hS, logExponentialDecayTwist_apply, logExponentialDecayTwist_apply]
  change phase x * ((Real.exp ((b : ℝ) * x) : ℂ) * f.val x) =
    (Real.exp ((b : ℝ) * x) : ℂ) * (phase x * f.val x)
  exact mul_left_comm _ _ _

private theorem positiveRealExponentialDecay_phaseCLM_apply
    (I : Set ℝ) (hI : I.Nonempty) (t : ℝ) (f : PositiveRealExponentialDecay I) (x : ℝ) :
    (positiveRealExponentialDecay_phaseCLM I hI t f).val x =
      Complex.exp (((t : ℂ) * Complex.I) * (x : ℂ)) * f.val x := rfl

private def positiveRealExponentialDecay_phase (I : Set ℝ) (hI : I.Nonempty) (t : ℝ) :
    PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay I := by
  refine ContinuousLinearEquiv.equivOfInverse
    (positiveRealExponentialDecay_phaseCLM I hI t) (positiveRealExponentialDecay_phaseCLM I hI (-t))
    ?_ ?_
  · intro f
    apply Subtype.ext
    funext x
    erw [positiveRealExponentialDecay_phaseCLM_apply, positiveRealExponentialDecay_phaseCLM_apply]
    simp only [Complex.ofReal_neg, neg_mul, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_mul]
  · intro f
    apply Subtype.ext
    funext x
    erw [positiveRealExponentialDecay_phaseCLM_apply, positiveRealExponentialDecay_phaseCLM_apply]
    simp only [Complex.ofReal_neg, neg_mul, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, one_mul]

/-- A complex power of the positive real modulus shifts the real weights by its real part.
The imaginary part acts by continuous multiplication by a Schwartz multiplier. -/
def positiveRealExponentialDecay_complexTwist (I : Set ℝ) (hI : I.Nonempty) (s : ℂ) :
    PositiveRealExponentialDecay I ≃L[ℂ]
      PositiveRealExponentialDecay ((fun b : ℝ => b - s.re) '' I) :=
  (positiveRealExponentialDecay_phase I hI s.im).trans (positiveRealExponentialDecay_shift I hI s.re)

@[simp] theorem positiveRealExponentialDecay_complexTwist_apply
    (I : Set ℝ) (hI : I.Nonempty) (s : ℂ) (f : PositiveRealExponentialDecay I) (x : ℝ) :
    (positiveRealExponentialDecay_complexTwist I hI s f).val x =
      Complex.exp (s * (x : ℂ)) * f.val x := by
  unfold positiveRealExponentialDecay_complexTwist
  rw [ContinuousLinearEquiv.trans_apply, positiveRealExponentialDecay_shift_apply]
  unfold positiveRealExponentialDecay_phase
  erw [ContinuousLinearEquiv.equivOfInverse_apply, positiveRealExponentialDecay_phaseCLM_apply]
  rw [← mul_assoc, Complex.ofReal_exp, Complex.ofReal_mul, ← Complex.exp_add, ← add_mul,
    Complex.re_add_im]

/-- The real Gaussian as a Schwartz function. The polynomial derivative
and decay estimates are adapted from RiemannMasullo commit 8a354e6. -/
private def gaussianSchwartzProfile : 𝓢(ℝ, ℂ) := by
  let G : ℝ → ℂ := fun x ↦ (Real.exp (-(x ^ 2)) : ℂ)
  -- Differentiating p(x) exp(-x²) replaces p by p' - 2Xp.
  have hderiv (j : ℕ) : ∃ p : Polynomial ℝ,
      iteratedDeriv j G = fun x ↦ (↑(p.eval x * Real.exp (-(x ^ 2))) : ℂ) := by
    induction j with
    | zero => exact ⟨1, by simp [G]⟩
    | succ j ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.derivative - Polynomial.C 2 * Polynomial.X * p, ?_⟩
      rw [iteratedDeriv_succ, hp]
      funext x
      have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-(y ^ 2)))
          (Real.exp (-(x ^ 2)) * -(2 * x)) x := by
        simpa using! (((hasDerivAt_id x).pow 2).neg).exp
      apply (((p.hasDerivAt x).mul hexp).ofReal_comp.deriv).trans
      congr 1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
  have hbound (k j : ℕ) : ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedDeriv j G x‖ ≤ C := by
    obtain ⟨p, hp⟩ := hderiv j
    let M : ℝ := ∑ i ∈ p.support, ‖p.coeff i‖ * ((k + i).factorial : ℝ)
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ by positivity
    refine ⟨M * Real.exp (1 / 4), fun x ↦ ?_⟩
    have hpoly : ‖x‖ ^ k * ‖p.eval x‖ ≤ M * Real.exp |x| := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_pow, ← mul_left_comm, ← pow_add, Real.norm_eq_abs x, mul_assoc]
      have hfact : (0 : ℝ) < (k + i).factorial := by positivity
      have hpow := (div_le_iff₀ hfact).mp
        (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) (k + i))
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hpow) (norm_nonneg _)
    have hsquare : |x| + -(x ^ 2) ≤ 1 / 4 := by
      rw [← sq_abs x]
      nlinarith [sq_nonneg (|x| - 1 / 2)]
    rw [hp, Complex.norm_real, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
    calc
      _ ≤ (M * Real.exp |x|) * Real.exp (-(x ^ 2)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = M * Real.exp (|x| + -(x ^ 2)) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ M * Real.exp (1 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsquare) hM
  have hsmooth : ContDiff ℝ ∞ G :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun x : ℝ ↦ Real.exp (-(x ^ 2)))
  refine ⟨G, hsmooth, fun k j ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbound k j
  exact ⟨C, fun x ↦ by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC x⟩

/-- The Gaussian in the logarithmic coordinate lies in every real-weight decay space.
Completing the square expresses each weighted profile as a scaled Schwartz translate. -/
theorem gaussianLogProfile_mem_logExponentialDecaySubmodule (I : Set ℝ) :
    (fun x : ℝ => (Real.exp (-(x ^ 2)) : ℂ)) ∈ logExponentialDecaySubmodule I := by
  apply (Submodule.mem_iInf _).mpr
  intro a
  let c := (a : ℝ) / 2
  refine ⟨(Real.exp (c ^ 2) : ℂ) • gaussianSchwartzProfile.compSubConstCLM ℂ c, ?_⟩
  funext x
  change (Real.exp (c ^ 2) : ℂ) * (Real.exp (-((x - c) ^ 2)) : ℂ) =
    (Real.exp ((a : ℝ) * x) : ℂ) * (Real.exp (-(x ^ 2)) : ℂ)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  dsimp [c]
  ring

variable (I : Set ℝ)

local notation "E" => PositiveRealExponentialDecay I
local notation "D" => StrongDual ℂ E

open scoped BoundedContinuousFunction

private theorem isClosed_range_logExponentialDecayTwist (I : Set ℝ) (a : I) :
    IsClosed (range (fun (f : PositiveRealExponentialDecay I) (b : I) ↦
      logExponentialDecayTwist I b f)) := by
  let w (b : I) (x : ℝ) : ℂ := Real.exp ((b : ℝ) * x)
  have hw (b : I) (x : ℝ) : w b x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (Real.exp_pos ((b : ℝ) * x)).ne'
  have heval (b : I) (x : ℝ) : Continuous (fun g : I → 𝓢(ℝ, ℂ) ↦ g b x) :=
    (continuous_eval_const (F := ℝ →ᵇ ℂ) x).comp
      ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp (continuous_apply b))
  have hrange : range (fun (f : PositiveRealExponentialDecay I) (b : I) ↦
      logExponentialDecayTwist I b f) =
      ⋂ (b : I) (x : ℝ), {g : I → 𝓢(ℝ, ℂ) | w a x * g b x = w b x * g a x} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨f, rfl⟩ b x
      rw [logExponentialDecayTwist_apply I b f x, logExponentialDecayTwist_apply I a f x]
      exact mul_left_comm _ _ _
    · intro hg
      let f (x : ℝ) := g a x / w a x
      have hmatch (b : I) (x : ℝ) : w b x * f x = g b x := by
        rw [show w b x * f x = (w b x * g a x) / w a x by simp [f, mul_div_assoc]]
        exact (div_eq_iff (hw a x)).mpr ((hg b x).symm.trans (mul_comm _ _))
      have hf : f ∈ logExponentialDecaySubmodule I := by
        apply (Submodule.mem_iInf _).mpr
        intro b
        exact ⟨g b, funext fun x ↦ (hmatch b x).symm⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      funext b
      ext x
      rw [logExponentialDecayTwist_apply]
      exact hmatch b x
  rw [hrange]
  exact isClosed_iInter fun b ↦ isClosed_iInter fun x ↦
    isClosed_eq (continuous_const.mul (heval b x)) (continuous_const.mul (heval a x))

/-- Paper: Lemma D.3.2.3(1), p. 802. The closed embedding into the product of complete
Schwartz spaces gives completeness for the additive uniformity. -/
private theorem positiveRealExponentialDecay_complete (I : Set ℝ) (hne : I.Nonempty) :
    CompleteSpace (PositiveRealExponentialDecay I) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hT : IsUniformInducing T := AddMonoidHom.isUniformInducing_of_isInducing
    (f := T.toAddMonoidHom) (positiveRealExponentialDecay_isEmbedding I hne).isInducing
  obtain ⟨a, ha⟩ := hne
  exact (completeSpace_iff_isComplete_range hT).mpr
    (isClosed_range_logExponentialDecayTwist I ⟨a, ha⟩).isComplete

/-- A finite sum of Schwartz seminorms controlling the derivatives of an exponential twist
on the half-line where that exponential is at most one. -/
private def exponentialTwistBound (t : ℝ) (k n : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℝ≥0) * ‖t‖₊ ^ i) • SchwartzMap.seminorm ℂ k (n - i)

private theorem exponentialTwistBound_continuous (t : ℝ) (k n : ℕ) :
    Continuous (exponentialTwistBound t k n) := by
  apply Seminorm.continuous_finsetSum
  intro i _
  exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n - i)).const_smul _

/-- Leibniz's formula bounds the weighted derivative wherever the exponential is at most one. -/
private theorem weighted_deriv_exp_smul_le (t x : ℝ) (hx : t * x ≤ 0) (k n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    |x| ^ k * ‖iteratedDeriv n ((fun y ↦ Real.exp (t * y)) • ⇑g) x‖ ≤
      exponentialTwistBound t k n g := by
  have hexp : ContDiff ℝ n (fun y : ℝ ↦ Real.exp (t * y)) := by fun_prop
  have hderiv := iteratedDerivWithin_smul (Set.mem_univ x) uniqueDiffOn_univ
    hexp.contDiffAt.contDiffWithinAt (g.smooth n).contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul] at hderiv
  rw [hderiv]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg x) k)).trans ?_
  rw [Finset.mul_sum]
  simp only [exponentialTwistBound, FunLike.coe_sum, Finset.sum_apply, smul_apply, NNReal.smul_def,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, coe_nnnorm, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul, norm_smul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
  have h := g.le_seminorm' ℂ k (n - i) x
  have hcoeff : 0 ≤ (n.choose i : ℝ) * ‖t‖ ^ i := by positivity
  calc
    _ = ((n.choose i : ℝ) * ‖t‖ ^ i) * (Real.exp (t * x) *
        (|x| ^ k * ‖iteratedDeriv (n - i) g x‖)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      exact (mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr hx)).trans h

/-- The positive-real case of Lemma D.3.3.2. Two Schwartz twists give
Schwartz regularity at every intermediate exponent. -/
theorem logExponentialWeight_mem_schwartz_between {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {f : ℝ → ℂ} (ha : logExponentialWeight a f ∈ realSchwartzCoe.range)
    (hb : logExponentialWeight b f ∈ realSchwartzCoe.range) :
    logExponentialWeight c f ∈ realSchwartzCoe.range := by
  obtain ⟨g, hg⟩ := ha
  obtain ⟨h, hh⟩ := hb
  have changeWeight (d : ℝ) (u : 𝓢(ℝ, ℂ)) (hu : realSchwartzCoe u = logExponentialWeight d f) :
      logExponentialWeight c f = (fun x => Real.exp ((c - d) * x)) • ⇑u := by
    ext x
    change logExponentialWeight c f x = Real.exp ((c - d) * x) • u x
    rw [Complex.real_smul, ← realSchwartzCoe_apply, hu]
    have he := logExponentialWeight_add (c - d) d f
    rw [sub_add_cancel] at he
    exact congrFun he.symm x
  have hleft := changeWeight a g hg
  have hright := changeWeight b h hh
  have hsmooth : ContDiff ℝ ∞ (logExponentialWeight c f) := by
    rw [hleft]
    exact (by fun_prop : ContDiff ℝ ∞ (fun x => Real.exp ((c - a) * x))).smul (g.smooth ⊤)
  refine ⟨⟨_, hsmooth, fun k n => ?_⟩, rfl⟩
  refine ⟨exponentialTwistBound (c - a) k n g + exponentialTwistBound (c - b) k n h, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  rcases le_total x 0 with hx | hx
  · rw [hleft]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hac) hx)
      k n g).trans (le_add_of_nonneg_right (apply_nonneg _ _))
  · rw [hright]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcb) hx)
      k n h).trans (le_add_of_nonneg_left (apply_nonneg _ _))

/-- Paper: Lemma D.3.2.3(1), p. 802. On each half-line the corresponding endpoint
controls the Schwartz seminorm of every intermediate twist. -/
private theorem exponentialTwist_seminorm_le {I : Set ℝ} (a b c : I) (hba : b ≤ a) (hac : a ≤ c)
    (k n : ℕ) (f : logExponentialDecaySubmodule I) :
    SchwartzMap.seminorm ℂ k n (logExponentialDecayTwist I a f) ≤
      exponentialTwistBound (a - b : ℝ) k n (logExponentialDecayTwist I b f) +
      exponentialTwistBound (a - c : ℝ) k n (logExponentialDecayTwist I c f) := by
  have changeWeight (d : I) : ⇑(logExponentialDecayTwist I a f) =
      (fun x ↦ Real.exp (((a : ℝ) - d) * x)) • ⇑(logExponentialDecayTwist I d f) := by
    funext x
    change _ = Real.exp (((a : ℝ) - d) * x) • logExponentialDecayTwist I d f x
    rw [Complex.real_smul, logExponentialDecayTwist_apply,
      logExponentialDecayTwist_apply, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  intro x
  rcases le_total x 0 with hx | hx
  · rw [changeWeight b]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) hx)
      k n _).trans (le_add_of_nonneg_right (apply_nonneg _ _))
  · rw [changeWeight c]
    exact (weighted_deriv_exp_smul_le _ _ (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hac) hx)
      k n _).trans (le_add_of_nonneg_left (apply_nonneg _ _))

/-- Paper: Lemma D.3.2.3(1), p. 802. Two countable sequences of exponents bracket
every exponent of the interval and suffice to generate the topology. -/
private theorem exponentialDecay_metrizable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    MetrizableSpace (PositiveRealExponentialDecay I) := by
  have : Nonempty I := hne.to_subtype
  obtain ⟨lo, -, hlo⟩ := exists_seq_antitone_tendsto_atTop_atBot I
  obtain ⟨hi, -, hhi⟩ := exists_seq_monotone_tendsto_atTop_atTop I
  let d : ℕ ⊕ ℕ → I := Sum.elim lo hi
  let p (i : I × ℕ × ℕ) :=
    (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1)
  let q (j : (ℕ ⊕ ℕ) × ℕ × ℕ) := p (d j.1, j.2)
  let X := WithGeneratingSeminorms (logExponentialDecaySubmodule I) q
  let Y := PositiveRealExponentialDecay I
  have hp := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) p
  have hq := withGeneratingSeminorms_spec (logExponentialDecaySubmodule I) q
  let T (a : I) : X →ₗ[ℂ] 𝓢(ℝ, ℂ) := logExponentialDecayTwist I a
  have hc (j : ℕ ⊕ ℕ) : Continuous (T (d j)) := by
    apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp
    intro i
    exact hq.continuous_seminorm (j, i)
  let toFull : X →ₗ[ℂ] Y := LinearMap.id
  have hfull : Continuous toFull := by
    apply hp.continuous_of_continuous_comp
    rintro ⟨a, k, n⟩
    obtain ⟨l, hl⟩ := (hlo.eventually (eventually_le_atBot a)).exists
    obtain ⟨r, hr⟩ := (hhi.eventually (eventually_ge_atTop a)).exists
    let B := ((exponentialTwistBound (a - lo l : ℝ) k n).comp (T (lo l))) +
      ((exponentialTwistBound (a - hi r : ℝ) k n).comp (T (hi r)))
    have hB : Continuous B :=
      ((exponentialTwistBound_continuous _ _ _).comp (hc (.inl l))).add
        ((exponentialTwistBound_continuous _ _ _).comp (hc (.inr r)))
    exact Seminorm.continuous_of_le hB (fun f ↦ exponentialTwist_seminorm_le a _ _ hl hr k n f)
  let toCountable : Y →ₗ[ℂ] X := LinearMap.id
  have hcountable : Continuous toCountable := by
    apply hq.continuous_of_continuous_comp
    intro j
    exact hp.continuous_seminorm (d j.1, j.2)
  let e : Y ≃ₜ X := ⟨Equiv.refl _, hcountable, hfull⟩
  have : FirstCountableTopology X := hq.firstCountableTopology
  have : FirstCountableTopology Y := e.isInducing.firstCountableTopology
  have : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : T2Space Y := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  exact UniformSpace.metrizableSpace

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is Fréchet. -/
theorem positiveRealExponentialDecay_frechet (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsFrechetTVS E := by
  exact ⟨inferInstance, inferInstance, exponentialDecay_metrizable I hInt hne,
    positiveRealExponentialDecay_complete I hne⟩

/-- Paper: Proposition D.3.2.5, p. 802. On the strip, the positive-real Mellin
integral converges absolutely. The profile is pulled back by the real logarithm. -/
theorem positiveRealExponentialDecay_mellinConvergent (f : E) (s : ℂ) (hs : s.re ∈ I) :
    MellinConvergent (fun t ↦ f.val (Real.log t)) s := by
  apply mellinConvergent_of_integrable_logWeight
  have h : Integrable (fun x : ℝ ↦ logExponentialDecayTwist I ⟨s.re, hs⟩ f x) volume :=
    (logExponentialDecayTwist I ⟨s.re, hs⟩ f).integrable
  exact h.congr (Eventually.of_forall fun x ↦ logExponentialDecayTwist_apply I ⟨s.re, hs⟩ f x)

section MellinIsomorphism

open scoped Asymptotics FourierTransform

local notation "linePoint" => (fun (a y : ℝ) ↦ (a : ℂ) + y * Complex.I)
local notation "profile" => (fun (f : ℝ → ℂ) (t : ℝ) ↦ f (Real.log t))

/-- The Fourier argument corresponding to a unit of imaginary Mellin height. -/
private def fourierFrequencyScale :=
  (LinearEquiv.smulOfNeZero ℝ ℝ (2 * Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))).toContinuousLinearEquiv

/-- Paper: Proposition D.3.2.5, p. 802. Reflection, Fourier transform, and rescaling
turn an exponential twist into its vertical Mellin trace. -/
private def mellinLineEquiv : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ) :=
  (schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv).trans
    ((FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).trans (schwartzChangeVariable ℂ fourierFrequencyScale))

private theorem mellinLineEquiv_twist {I : Set ℝ} (a : I) (f : logExponentialDecaySubmodule I) (y : ℝ) :
    mellinLineEquiv (logExponentialDecayTwist I a f) y = mellin (profile f.val) (linePoint a y) := by
  let g := logExponentialDecayTwist I a f
  let r := schwartzChangeVariable ℂ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv g
  change (𝓕 r) ((2 * Real.pi)⁻¹ * y) = _
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add, Real.log_exp, div_eq_inv_mul]
  apply congrArg (fun h : ℝ → ℂ ↦ 𝓕 h ((2 * Real.pi)⁻¹ * y))
  funext x
  change logExponentialDecayTwist I a f (-x) = _
  rw [logExponentialDecayTwist_apply I a f (-x)]
  simp only [Complex.real_smul, mul_neg, neg_mul]

private theorem mellinLineEquiv_symm_apply {F : ℂ → ℂ} (a : ℝ) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ y, g y = F (linePoint a y)) (x : ℝ) :
    mellinLineEquiv.symm g x = (Real.exp (a * x) : ℂ) * mellinInv a F (Real.exp x) := by
  let r := (schwartzChangeVariable ℂ fourierFrequencyScale).symm g
  change (𝓕⁻ r) (-x) = _
  rw [SchwartzMap.fourierInv_coe, mellinInv_eq_fourierInv a F (Real.exp_pos x), Real.log_exp]
  have eq : ⇑r = (fun y : ℝ ↦ F (a + 2 * (Real.pi : ℂ) * y * Complex.I)) := by
    funext y
    change g (((2 * Real.pi)⁻¹)⁻¹ * y) = _
    rw [inv_inv, hg]
    push_cast
    rfl
  rw [eq, smul_eq_mul, ← mul_assoc]
  have hpow : ((Real.exp x : ℝ) : ℂ) ^ (-(a : ℂ)) = (Real.exp (-(a * x)) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private theorem mellinProfile_differentiable {I : Set ℝ} (hI : IsOpen I)
    (f : logExponentialDecaySubmodule I) : DifferentiableOn ℂ (mellin (profile f.val)) (Complex.re ⁻¹' I) := by
  intro z hz
  let a : I := ⟨z.re, hz⟩
  have cont : Continuous f.val := by
    have eq : f.val = (fun u : ℝ ↦ (Real.exp (-((a : ℝ) * u)) : ℂ) * logExponentialDecayTwist I a f u) := by
      funext x
      rw [logExponentialDecayTwist_apply I a f x, ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [eq]
    exact (by fun_prop : Continuous (fun u : ℝ ↦ (Real.exp (-((a : ℝ) * u)) : ℂ))).mul
      (logExponentialDecayTwist I a f).continuous
  obtain ⟨l, r, hl, hr⟩ := exists_bracketing_lines hI a
  have hloc : LocallyIntegrableOn (profile f.val) (Ioi 0) volume :=
    (cont.comp_continuousOn (Real.continuousOn_log.mono (fun x hx ↦ ne_of_gt hx))).locallyIntegrableOn measurableSet_Ioi
  have bound (c : I) {L : Filter ℝ} (hL : ∀ᶠ t in L, 0 < t) :
      profile f.val =O[L] (fun t : ℝ ↦ t ^ (-(c : ℝ))) := by
    let g := logExponentialDecayTwist I c f
    apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g)
    filter_upwards [hL] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos ht _), Real.rpow_def_of_pos ht, mul_comm (Real.log t)]
    simpa only [g, logExponentialDecayTwist_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm] using g.norm_le_seminorm ℂ (Real.log t)
  exact (mellin_differentiableAt_of_isBigO_rpow hloc (bound r (eventually_gt_atTop 0)) hr
    (bound l self_mem_nhdsWithin) hl).differentiableWithinAt

private theorem mellinProfile_strip_bound {I : Set ℝ} (l r : I) (f : logExponentialDecaySubmodule I) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc (l : ℝ) r → ‖mellin (profile f.val) z‖ ≤ C := by
  let G (a : I) := logExponentialDecayTwist I a f
  let B (x : ℝ) := ‖G l (-x)‖ + ‖G r (-x)‖
  have hi (a : I) : Integrable (fun x : ℝ ↦ ‖G a (-x)‖) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp
      ((G a).integrable (μ := volume)).norm.aestronglyMeasurable).2 (G a).integrable.norm
  refine ⟨∫ x, B x, fun z hz ↦ ?_⟩
  rw [mellin_eq_fourier]
  apply (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  apply integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) ((hi l).add (hi r))
  filter_upwards with x
  change ‖Real.exp (-z.re * x) • f.val (Real.log (Real.exp (-x)))‖ ≤ ‖G l (-x)‖ + ‖G r (-x)‖
  simp only [G, logExponentialDecayTwist_apply, norm_mul, Complex.norm_real, norm_smul, Real.log_exp,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_neg, ← neg_mul]
  rcases le_total x 0 with hx | hx
  · apply le_add_of_nonneg_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (neg_le_neg hz.2) hx)) (norm_nonneg _)
  · apply le_add_of_le_of_nonneg _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz.1) hx)) (norm_nonneg _)

private theorem mellinProfile_weighted_edge {I : Set ℝ} (a : I) (k : ℕ) (f : logExponentialDecaySubmodule I) :
    ∃ C : ℝ, ∀ z : ℂ, z.re = a → ‖z ^ k * mellin (profile f.val) z‖ ≤ C := by
  let g := mellinLineEquiv (logExponentialDecayTwist I a f)
  let w := fun y : ℝ ↦ (linePoint a y)^k
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  let h := SchwartzMap.smulLeftCLM ℂ w g
  refine ⟨SchwartzMap.seminorm ℂ 0 0 h, fun z hz ↦ ?_⟩
  have heq : linePoint a z.im = z := hz ▸ Complex.re_add_im z
  have hval : h z.im = z ^ k * mellin (profile f.val) z := by
    change SchwartzMap.smulLeftCLM ℂ w g z.im = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hw]
    change (linePoint a z.im)^k * mellinLineEquiv (logExponentialDecayTwist I a f) z.im = _
    rw [mellinLineEquiv_twist, heq]
  rw [← hval]
  exact h.norm_le_seminorm ℂ _

private theorem mellinProfile_mem_bergman {I : Set ℝ} (hI : IsOpen I)
    (f : logExponentialDecaySubmodule I) :
    (Complex.re ⁻¹' I).indicator (mellin (profile f.val)) ∈ schwartzBergmanSubmodule I := by
  let F := mellin (profile f.val)
  have hf := mellinProfile_differentiable hI f
  refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
  · exact hf.congr fun z hz ↦ indicator_of_mem hz _
  intro l r hlr hsub k
  let a : I := ⟨l, hsub (left_mem_Icc.mpr hlr)⟩
  let b : I := ⟨r, hsub (right_mem_Icc.mpr hlr)⟩
  obtain ⟨A, hA⟩ := mellinProfile_weighted_edge a k f
  obtain ⟨B, hB⟩ := mellinProfile_weighted_edge b k f
  refine ⟨max A B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ k * (Complex.re ⁻¹' I).indicator F z‖ ≤ _
  rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hsub hz)]
  rcases hlr.eq_or_lt with heq | hlt
  · exact (hA z (show z.re = l by linarith [hz.1, hz.2])).trans (le_max_left _ _)
  have hd : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo l r) := by
    refine ⟨hf.mono (preimage_mono (Ioo_subset_Icc_self.trans hsub)), ?_⟩
    rw [Complex.closure_preimage_re, closure_Ioo hlt.ne]
    exact hf.continuousOn.mono (preimage_mono hsub)
  obtain ⟨M, hM⟩ := mellinProfile_strip_bound a b f
  exact norm_pow_mul_le_on_verticalStrip hlt hd hM k
    (fun w hw ↦ (hA w hw).trans (le_max_left _ _)) (fun w hw ↦ (hB w hw).trans (le_max_right _ _)) z hz

/-- Moving the inverse contour between two lines preserves its value at every positive argument. -/
private theorem bergmanInv_shift_lt {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (F : SchwartzBergman I) (a b : I) (hab : (a : ℝ) < b) (u : ℝ) :
    mellinInv a F.val (Real.exp u) = mellinInv b F.val (Real.exp u) := by
  let z : ℂ := ((a : ℝ) + (b : ℝ)) / 2
  have haz : (a : ℝ) < z.re := by dsimp [z]; simp; linarith
  have hzb : z.re < (b : ℝ) := by dsimp [z]; simp; linarith
  let phase (w : ℂ) := Complex.exp (-(w * u))
  let K (w : ℂ) := phase w * F.val w
  let G (w : ℂ) := (w - z) * K w
  have hphase (w : ℂ) : ‖phase w‖ = Real.exp (-w.re * u) := by simp [phase, Complex.norm_exp, Complex.mul_re]
  have hpow (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ (-w) = phase w := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    dsimp [phase]
    ring_nf
  have line (s : I) : Integrable (fun y ↦ K (linePoint s y)) := by
    obtain ⟨T, hT, _⟩ := schwartzBergman_schwartzLine_topology I hI hInt ⟨s, s.property⟩
    have heq (y : ℝ) : T F s y = F.val (linePoint s y) := by simpa [weightedVerticalTrace] using hT F s y
    have htrace : Integrable (fun y : ℝ ↦ F.val (linePoint s y)) :=
      (T F s).integrable.congr (.of_forall heq)
    have hc : Continuous (fun y : ℝ ↦ phase (linePoint s y)) := by dsimp [phase]; fun_prop
    have hb (y : ℝ) : ‖phase (linePoint s y)‖ ≤ Real.exp (-(s : ℝ) * u) := by rw [hphase]; simp
    exact htrace.bdd_mul hc.aestronglyMeasurable (.of_forall hb)
  have eqline (s : I) (hs : (s : ℝ) ≠ z.re) (y : ℝ) : G (linePoint s y) / (linePoint s y - z) = K (linePoint s y) := by
    have hne : linePoint s y ≠ z := fun he ↦ hs (by simpa using congrArg Complex.re he)
    dsimp only [G]
    field_simp [sub_ne_zero.mpr hne]
  obtain ⟨l, _, hla, _⟩ := exists_bracketing_lines hI a
  obtain ⟨_, r, _, hbr⟩ := exists_bracketing_lines hI b
  have hG : DifferentiableOn ℂ G (Complex.re ⁻¹' Ioo (l : ℝ) r) :=
    (differentiable_id.sub_const z).differentiableOn.mul ((by dsimp [phase]; fun_prop : Differentiable ℂ phase).differentiableOn.mul
      (F.property.2.1.mono (preimage_mono (Ioo_subset_Icc_self.trans (hInt.out l.property r.property)))))
  obtain ⟨A,hA⟩ := F.property.2.2 a b hab.le (hInt.out a.property b.property) 1
  obtain ⟨B,hB⟩ := F.property.2.2 a b hab.le (hInt.out a.property b.property) 2
  obtain ⟨P,hP⟩ := (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ))).bddAbove_image
    (f := fun s : ℝ ↦ Real.exp (-s * u)) (by fun_prop)
  let C := max P 0 * (max B 0 + ‖z‖ * max A 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdec : ∀ᶠ y : ℝ in comap abs atTop, ∀ s ∈ Icc (a : ℝ) b, ‖G (linePoint s y)‖ ≤ C / |y| := by
    have ht : Tendsto (abs : ℝ → ℝ) (comap abs atTop) atTop := tendsto_comap
    filter_upwards [ht.eventually (eventually_gt_atTop 0)] with y hy s hs
    let w := linePoint s y
    have hw : w ∈ Complex.re ⁻¹' Icc (a : ℝ) b := by simpa [w] using hs
    have him : |y| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    have ha := hA (mem_image_of_mem _ hw)
    have hb := hB (mem_image_of_mem _ hw)
    simp only [pow_one, norm_mul, norm_pow] at ha hb
    have hp : ‖phase w‖ ≤ max P 0 := (hphase w).le.trans
      ((hP (mem_image_of_mem _ hw)).trans (le_max_left _ _))
    apply (le_div_iff₀ hy).mpr
    calc ‖G w‖ * |y| = ‖phase w‖ * (‖w-z‖ * |y| * ‖F.val w‖) := by simp only [G,K,norm_mul]; ring
      _ ≤ max P 0 * ((‖w‖ + ‖z‖) * ‖w‖ * ‖F.val w‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right P 0)
        calc _ = ‖w‖ ^ 2 * ‖F.val w‖ + ‖z‖ * (‖w‖ * ‖F.val w‖) := by ring
          _ ≤ _ := add_le_add (hb.trans (le_max_left _ _))
            (mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (norm_nonneg _))
  have h := verticalCauchyIntegral_sub_eq hG hla hbr ⟨haz,hzb⟩ hC hdec
    (by simpa only [Complex.VerticalIntegrable, eqline a haz.ne] using line a)
    (by simpa only [Complex.VerticalIntegrable, eqline b hzb.ne'] using line b)
  simp only [eqline b hzb.ne', eqline a haz.ne] at h
  have hi : (∫ y : ℝ, K (linePoint b y)) = ∫ y : ℝ, K (linePoint a y) :=
    sub_eq_zero.mp (by simpa [G] using h)
  simp only [mellinInv, hpow, smul_eq_mul]
  exact congrArg (fun v : ℂ ↦ (1 / (2 * Real.pi) : ℝ) • v) hi.symm

private theorem bergmanInv_shift {I : Set ℝ} (hI : IsOpen I) (hInt : OrdConnected I)
    (F : SchwartzBergman I) (a b : I) (u : ℝ) :
    mellinInv a F.val (Real.exp u) = mellinInv b F.val (Real.exp u) := by
  rcases lt_trichotomy (a : ℝ) (b : ℝ) with h | h | h
  · exact bergmanInv_shift_lt hI hInt F a b h u
  · rw [h]
  · exact (bergmanInv_shift_lt hI hInt F b a h u).symm

/-- The Mellin transform of a logarithmic profile, extended by zero outside the strip. -/
private def stripMellinLinear {I : Set ℝ} (hI : IsOpen I) : PositiveRealExponentialDecay I →ₗ[ℂ] SchwartzBergman I := by
  let B (f : PositiveRealExponentialDecay I) : SchwartzBergman I :=
    ⟨(Complex.re ⁻¹' I).indicator (mellin (profile f.val)), mellinProfile_mem_bergman hI f⟩
  let L (a : I) : PositiveRealExponentialDecay I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
    mellinLineEquiv.toLinearMap.comp (logExponentialDecayTwist I a)
  have hv (f : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
      (B f).val z = L ⟨z.re, hz⟩ f z.im := by
    change (Complex.re ⁻¹' I).indicator _ z = mellinLineEquiv (logExponentialDecayTwist I _ f) z.im
    rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' I from hz), mellinLineEquiv_twist ⟨z.re, hz⟩ f z.im]
    simp [Complex.re_add_im]
  refine ⟨⟨B, ?_⟩, ?_⟩
  · intro f g
    apply Subtype.ext
    funext z
    change (B (f+g)).val z = (B f).val z + (B g).val z
    by_cases hz : z.re ∈ I
    · rw [hv _ _ hz, hv f _ hz, hv g _ hz, map_add]; rfl
    · simp [B, indicator_of_notMem (show z ∉ Complex.re ⁻¹' I from hz)]
  · intro c f
    apply Subtype.ext
    funext z
    change (B (c • f)).val z = c • (B f).val z
    by_cases hz : z.re ∈ I
    · rw [hv _ _ hz, hv f _ hz, map_smul]; rfl
    · simp [B, indicator_of_notMem (show z ∉ Complex.re ⁻¹' I from hz)]

private theorem stripMellinLinear_apply {I : Set ℝ} (hI : IsOpen I)
    (f : PositiveRealExponentialDecay I) (s : ℂ) (hs : s.re ∈ I) :
    (stripMellinLinear hI f).val s = mellin (profile f.val) s :=
  indicator_of_mem (show s ∈ Complex.re ⁻¹' I from hs) _

/-- Paper: Proposition D.3.2.5, p. 802. The Mellin integral induces a unique
continuous linear equivalence with the Schwartz–Bergman space on the strip. -/
theorem existsUnique_positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃! M : E ≃L[ℂ] SchwartzBergman I, ∀ (f : E) (s : ℂ), s.re ∈ I →
      (M f).val s = mellin (fun t ↦ f.val (Real.log t)) s := by
  let M := stripMellinLinear hOpen
  let U := mellinLineEquiv
  obtain ⟨T, hval, hT⟩ := schwartzBergman_schwartzLine_topology I hOpen hInt hne
  have hline (F : SchwartzBergman I) (a : I) (y : ℝ) : T F a y = F.val (linePoint a y) := by
    simpa only [weightedVerticalTrace, pow_zero, one_mul] using hval F a y
  have hcomm (f : PositiveRealExponentialDecay I) (a : I) : T (M f) a = U (logExponentialDecayTwist I a f) := by
    ext y
    rw [hline, show (M f).val (linePoint a y) = _ from stripMellinLinear_apply hOpen f _ (by simp)]
    exact (mellinLineEquiv_twist a f y).symm
  have hE := positiveRealExponentialDecay_isEmbedding I hne
  have inj : Injective M := by
    intro f g h
    apply hE.injective
    funext a
    apply U.injective
    rw [← hcomm, ← hcomm, h]
  have surj : Surjective M := by
    intro F
    obtain ⟨c,hc⟩ := hne
    let f (u : ℝ) := mellinInv c F.val (Real.exp u)
    have htw (a : I) (u : ℝ) : U.symm (T F a) u = (Real.exp ((a : ℝ) * u) : ℂ) * f u := by
      rw [mellinLineEquiv_symm_apply a (T F a) (hline F a)]
      exact congrArg (_ * ·) (bergmanInv_shift hOpen hInt F a ⟨c,hc⟩ u)
    have hf : f ∈ logExponentialDecaySubmodule I := by
      apply (Submodule.mem_iInf _).mpr
      intro a
      exact ⟨U.symm (T F a), funext (htw a)⟩
    let g : PositiveRealExponentialDecay I := ⟨f,hf⟩
    have hg (a : I) : logExponentialDecayTwist I a g = U.symm (T F a) := by
      ext u
      exact (logExponentialDecayTwist_apply I a g u).trans (htw a u).symm
    refine ⟨g, hT.injective ?_⟩
    funext a
    rw [hcomm, hg, U.apply_symm_apply]
  let e := LinearEquiv.ofBijective M ⟨inj,surj⟩
  let A : PositiveRealExponentialDecay I ≃L[ℂ] SchwartzBergman I := {
    toLinearEquiv := e
    continuous_toFun := by
      apply hT.continuous_iff.mpr
      apply continuous_pi
      intro a
      exact (U.continuous.comp ((continuous_apply a).comp hE.continuous)).congr fun f ↦ (hcomm f a).symm
    continuous_invFun := by
      apply hE.continuous_iff.mpr
      apply continuous_pi
      intro a
      apply (U.symm.continuous.comp ((continuous_apply a).comp hT.continuous)).congr
      intro F
      change U.symm (T F a) = logExponentialDecayTwist I a (e.symm F)
      apply U.injective
      rw [U.apply_symm_apply, ← hcomm]
      exact congrArg (fun G ↦ T G a) (e.apply_symm_apply F).symm }
  refine ⟨A, stripMellinLinear_apply hOpen, ?_⟩
  intro A' hA'
  apply ContinuousLinearEquiv.ext
  funext f
  apply hT.injective
  funext a
  ext y
  rw [hline, hline, hA' f _ (by simp)]
  exact (stripMellinLinear_apply hOpen f _ (by simp)).symm

end MellinIsomorphism

/-- Paper: Definition D.3.2.6, p. 803. The Fourier–Mellin transform is
the continuous linear equivalence furnished by the Mellin integral. -/
def positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty) :
    E ≃L[ℂ] SchwartzBergman I :=
  Classical.choose (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is Fréchet. -/
theorem schwartzBergman_frechet (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : IsFrechetTVS (SchwartzBergman I) := by
  let M := positiveRealFourierMellin I hI hInt hne
  obtain ⟨_, _, hmetr, hcomp⟩ := positiveRealExponentialDecay_frechet I hInt hne
  have : MetrizableSpace (PositiveRealExponentialDecay I) := hmetr
  refine ⟨inferInstance, inferInstance, M.symm.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
  exact (M.isUniformEmbedding.isUniformInducing.completeSpace_congr M.surjective).mp hcomp

/-- Paper: Definition D.3.2.6, p. 803. Evaluation of the Fourier–Mellin
transform on the strip gives the absolutely convergent Mellin integral. -/
theorem positiveRealFourierMellin_apply (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (f : E) (s : ℂ) (hs : s.re ∈ I) :
    (positiveRealFourierMellin I hOpen hInt hne f).val s =
      mellin (fun t ↦ f.val (Real.log t)) s := by
  exact Classical.choose_spec (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists f s hs


end PositiveReal
end
end Masullo
