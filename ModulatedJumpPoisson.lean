import MellinPoissonJumps
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Poisson summation with log-coordinate jumps on modulated groups

The sign issue in (D.3.5.3) and the derivative hypothesis required by the cited
scalar argument were also identified in
`RiemannMasullo/AppD_SchwartzBruhat/Sec3b.lean` at
`db376192baf52253727c46e2b211619d4e6a3941`.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

private theorem logDecay_translate {u : ℝ → ℂ} (h : SuperExponentialLogDecay u) (r : ℝ) :
    SuperExponentialLogDecay (fun x => u (x + r)) := by
  refine ⟨⟨h.1.choose, fun x => h.1.choose_spec (x + r)⟩, fun n => ?_⟩
  obtain ⟨A, hA, hbound⟩ := h.global_bound n (Nat.cast_nonneg n)
  refine ⟨A * Real.exp ((n : ℝ) * |r|), 1, by positivity, zero_lt_one, fun x _ => ?_⟩
  have hx : |x| ≤ |x + r| + |r| := by
    have hh := abs_add_le (x + r) (-r)
    rwa [show x + r + -r = x by ring, abs_neg] at hh
  have he : -(n : ℝ) * |x + r| ≤ (n : ℝ) * |r| + -(n : ℝ) * |x| := by
    nlinarith only [mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [mul_assoc, ← Real.exp_add]
  exact (hbound _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hA.le)

private theorem add_between_rays (r x : ℝ) :
    Tendsto (fun t => t + r) (𝓝[<] x) (𝓝[<] (x + r)) ∧
      Tendsto (fun t => t + r) (𝓝[>] x) (𝓝[>] (x + r)) := by
  have h : Continuous (fun t : ℝ => t + r) := continuous_id.add continuous_const
  constructor
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(h.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < x)
    exact add_lt_add_left ht r
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(h.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
    exact add_lt_add_left ht r

/-- Frequencies for the positive exponential convention. -/
def modulatedPoissonFrequency (d : ℝ) (m : ℤ) : ℂ :=
  ((m : ℂ) * (2 * Real.pi * I)) / (d : ℂ)

private theorem jumpPoisson_shifted_logLattice {u v left right : ℝ → ℂ}
    (S : Finset ℝ) (hu : SuperExponentialLogDecay u) (hv : SuperExponentialLogDecay v)
    (hD : ∀ x ∉ S, HasDerivAt u (v x) x) (hcv : ContinuousOn v ((S : Set ℝ)ᶜ))
    (hl : ∀ x, Tendsto u (𝓝[<] x) (𝓝 (left x)))
    (hr : ∀ x, Tendsto u (𝓝[>] x) (𝓝 (right x))) {d : ℝ} (hd : 0 < d) (r : ℝ) :
    let midpoint (t : ℝ) := (left t + right t) / 2
    let freq := modulatedPoissonFrequency d
    Summable (fun n : ℤ => ‖midpoint (d * n + r)‖) ∧
      Tendsto (fun N : ℕ => (d : ℂ)⁻¹ * ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        Complex.exp (-freq m * (r : ℂ)) *
          ∫ t : ℝ, Complex.exp (freq m * (t : ℂ)) * u t) atTop
        (𝓝 (∑' n : ℤ, midpoint (d * n + r))) := by
  classical
  let φ (y : ℝ) := u (Real.log y + r)
  let J := S.map ⟨fun t => t - r, fun _ _ h => by linarith⟩
  have hJ (t : ℝ) : t ∈ J ↔ t + r ∈ S := by
    simp only [J, Finset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x - r + r ∈ S
      simpa only [sub_add_cancel] using hx
    · intro ht
      exact ⟨t + r, ht, add_sub_cancel_right t r⟩
  have hφ (t : ℝ) : φ (Real.exp t) = u (t + r) := by simp [φ]
  have hDs (t : ℝ) (ht : t ∉ J) :
      HasDerivAt (fun y => φ (Real.exp y)) (v (t + r)) t := by
    simp_rw [hφ]
    have hA : HasDerivAt (fun t : ℝ => t + r) 1 t := (hasDerivAt_id t).add_const r
    simpa only [Function.comp_def, one_smul] using
      (hD (t + r) (fun hm => ht ((hJ t).mpr hm))).scomp t hA
  have hvs : ContinuousOn (fun t => v (t + r)) ((J : Set ℝ)ᶜ) :=
    hcv.comp (continuous_id.add continuous_const).continuousOn (fun t ht hm => ht ((hJ t).mpr hm))
  have hls (t : ℝ) : Tendsto (fun y => φ (Real.exp y)) (𝓝[<] t) (𝓝 (left (t + r))) := by
    simp_rw [hφ]
    exact (hl (t + r)).comp (add_between_rays r t).1
  have hrs (t : ℝ) : Tendsto (fun y => φ (Real.exp y)) (𝓝[>] t) (𝓝 (right (t + r))) := by
    simp_rw [hφ]
    exact (hr (t + r)).comp (add_between_rays r t).2
  have hud : SuperExponentialLogDecay (fun t => φ (Real.exp t)) := by
    simp_rw [hφ]
    exact logDecay_translate hu r
  have hne : Real.exp d ≠ 1 := by
    intro he
    have he' := congrArg Real.log he
    rw [Real.log_exp, Real.log_one] at he'
    exact hd.ne' he'
  have h := mellin_poisson_finite_jumps φ J (fun t => v (t + r))
    (fun t => left (t + r)) (fun t => right (t + r))
    (Real.exp_pos d) hne 0 hud (logDecay_translate hv r) hDs hvs hls hrs
  dsimp only at h
  simp only [Real.log_exp, Complex.exp_zero, one_zpow, one_mul, zero_add, abs_of_pos hd] at h
  refine ⟨h.1, ?_⟩
  have hlim := h.2.const_mul ((d : ℂ)⁻¹)
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hd.ne'), one_mul] at hlim
  apply hlim.congr
  intro N
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  let w := modulatedPoissonFrequency d m
  change mellin φ w = Complex.exp (-w * (r : ℂ)) *
      ∫ t : ℝ, Complex.exp (w * (t : ℂ)) * u t
  rw [mellin_eq_log_integral, ← MeasureTheory.integral_const_mul]
  rw [← integral_add_right_eq_self (fun t : ℝ =>
    Complex.exp (-w * (r : ℂ)) * (Complex.exp (w * (t : ℂ)) * u t)) r]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hφ, ← mul_assoc, ← Complex.exp_add]
  push_cast
  congr 2
  ring

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The additive log of the modulus. -/
def modulatedLog (m : G →ₜ* Multiplicative ℝ) (g : G) : ℝ := Multiplicative.toAdd (m g)

/-- The given section identifies the group with its log coordinate and
the kernel of its modulus. -/
def modulatedLogSplit (m : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t) :
    (ℝ × m.toMonoidHom.ker) ≃ₜ G := by
  have hker (g : G) : g / τ (m g) ∈ m.toMonoidHom.ker := by
    change m (g / τ (m g)) = 1
    rw [map_div, hτ, div_self']
  refine
    { toFun := fun p => τ (Multiplicative.ofAdd p.1) * p.2.val
      invFun := fun g => (modulatedLog m g, ⟨g / τ (m g), hker g⟩)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := (τ.continuous_toFun.comp (continuous_ofAdd.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (continuous_toAdd.comp m.continuous_toFun).prodMk
        ((continuous_id.div' (τ.continuous_toFun.comp m.continuous_toFun)).subtype_mk hker) }
  · rintro ⟨t, k⟩
    have hk : m k.val = 1 := k.property
    have ht : m (τ (Multiplicative.ofAdd t) * k.val) = Multiplicative.ofAdd t := by
      rw [map_mul, hτ, hk, mul_one]
    apply Prod.ext
    · exact congrArg Multiplicative.toAdd ht
    · apply Subtype.ext
      change (τ (Multiplicative.ofAdd t) * k.val) / τ (m (τ (Multiplicative.ofAdd t) * k.val)) = _
      rw [ht, mul_comm, mul_div_cancel_right]
  · intro g
    change τ (m g) * (g / τ (m g)) = g
    rw [mul_comm, div_mul_cancel]

variable [MeasurableSpace G] [BorelSpace G]

/-- Haar normalization in the chosen splitting, with Lebesgue measure on
the log coordinate and the given measure on the kernel. -/
def modulatedLogMeasure (m : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)
    (ν : Measure m.toMonoidHom.ker) : Measure G :=
  Measure.map (modulatedLogSplit m τ hτ) (volume.prod ν)

/-- The pushed-forward product is a Haar measure. Its log pushforward
is Lebesgue measure when the kernel measure has mass one. -/
theorem modulatedLogMeasure_isHaar (m : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)
    (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsFiniteMeasure ν] :
    (modulatedLogMeasure m τ hτ ν).IsHaarMeasure := by
  let e := modulatedLogSplit m τ hτ
  let μ : Measure (ℝ × m.toMonoidHom.ker) := volume.prod ν
  have hμ : IsFiniteMeasureOnCompacts (Measure.map e μ) := Measure.IsFiniteMeasureOnCompacts.map μ e
  have hpos : Measure.IsOpenPosMeasure (Measure.map e μ) :=
    e.continuous.isOpenPosMeasure_map e.surjective
  change (Measure.map e μ).IsHaarMeasure
  refine {
    lt_top_of_isCompact := hμ.lt_top_of_isCompact
    open_pos := hpos.open_pos
    map_mul_left_eq_self := ?_ }
  intro g
  let p := e.symm g
  let A : (ℝ × m.toMonoidHom.ker) → (ℝ × m.toMonoidHom.ker) :=
    Prod.map (p.1 + ·) (p.2 * ·)
  have hf : Measurable ((p.1 + ·) : ℝ → ℝ) := measurable_const.add measurable_id
  have hg : Measurable ((p.2 * ·) : m.toMonoidHom.ker → m.toMonoidHom.ker) :=
    (continuous_const.mul continuous_id).measurable
  have hA : Measurable A := hf.prodMap hg
  have hmA : Measure.map A μ = μ := by
    change Measure.map (Prod.map _ _) (volume.prod ν) = _
    rw [← Measure.map_prod_map volume ν hf hg, map_add_left_eq_self, map_mul_left_eq_self]
  have hcomp : (g * ·) ∘ e = e ∘ A := by
    funext q
    rw [Function.comp_apply, Function.comp_apply, ← e.apply_symm_apply g]
    change (τ (Multiplicative.ofAdd p.1) * p.2.val) *
        (τ (Multiplicative.ofAdd q.1) * q.2.val) =
      τ (Multiplicative.ofAdd (p.1 + q.1)) * (p.2.val * q.2.val)
    rw [show Multiplicative.ofAdd (p.1 + q.1) =
      Multiplicative.ofAdd p.1 * Multiplicative.ofAdd q.1 from rfl, map_mul]
    ac_rfl
  have hmul : Measurable ((g * ·) : G → G) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hmul e.continuous.measurable,
    hcomp, ← Measure.map_map e.continuous.measurable hA, hmA]

theorem modulatedLogMeasure_log_pushforward (m : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)
    (ν : Measure m.toMonoidHom.ker) [IsProbabilityMeasure ν] :
    Measure.map (modulatedLog m) (modulatedLogMeasure m τ hτ ν) = volume := by
  have hm : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous_toFun
  rw [modulatedLogMeasure, Measure.map_map hm.measurable (modulatedLogSplit m τ hτ).continuous.measurable]
  have he : modulatedLog m ∘ modulatedLogSplit m τ hτ = Prod.fst := by
    funext p
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.1) * p.2.val)) = p.1
    rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one, toAdd_ofAdd]
  rw [he, Measure.map_fst_prod, measure_univ, one_smul]

private theorem integral_modulatedLogMeasure (m : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : ∀ t, m (τ t) = t)
    (ν : Measure m.toMonoidHom.ker) [IsProbabilityMeasure ν] (U : ℝ → ℂ) :
    (∫ g, U (modulatedLog m g) ∂modulatedLogMeasure m τ hτ ν) = ∫ t, U t := by
  change (∫ g, U (modulatedLog m g) ∂Measure.map
    (modulatedLogSplit m τ hτ).toMeasurableEquiv (volume.prod ν)) = _
  rw [integral_map_equiv]
  have he (p : ℝ × m.toMonoidHom.ker) :
      modulatedLog m ((modulatedLogSplit m τ hτ).toMeasurableEquiv p) = p.1 := by
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.1) * p.2.val)) = p.1
    rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one, toAdd_ofAdd]
  simp_rw [he]
  rw [integral_fun_fst]
  rw [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

variable (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G)
  (hτ : ∀ t, m (τ t) = t)

/-- The twisted scalar profile on the log coordinate. -/
def modulatedTwistedProfile (χ : G →ₜ* Circle) (φ : G → ℂ) (t : ℝ) : ℂ :=
  (χ (τ (Multiplicative.ofAdd t)) : ℂ) * φ (τ (Multiplicative.ofAdd t))

omit [MeasurableSpace G] [BorelSpace G] in
include hτ in
private theorem modulatedTwist_factor (χ : G →ₜ* Circle) (φ : G → ℂ)
    (hφ : ∀ (k : m.toMonoidHom.ker) g, (χ k.val : ℂ) * φ (k.val * g) = φ g) (g : G) :
    (χ g : ℂ) * φ g = modulatedTwistedProfile τ χ φ (modulatedLog m g) := by
  let p := (modulatedLogSplit m τ hτ).symm g
  have hpg : τ (Multiplicative.ofAdd p.1) * p.2.val = g :=
    (modulatedLogSplit m τ hτ).apply_symm_apply g
  have hr : p.1 = modulatedLog m g := rfl
  rw [← hr, ← hpg]
  change (χ (τ (Multiplicative.ofAdd p.1) * p.2.val) : ℂ) * _ = _
  rw [map_mul, Circle.coe_mul, mul_assoc, mul_comm (τ (Multiplicative.ofAdd p.1)) p.2.val, hφ]
  rfl

/-- The midpoint representative, untwisted by the original unitary character. -/
def modulatedPoissonMidpoint (χ : G →ₜ* Circle) (left right : ℝ → ℂ) (g : G) : ℂ :=
  ((χ g : ℂ)⁻¹) * ((left (modulatedLog m g) + right (modulatedLog m g)) / 2)

omit [MeasurableSpace G] [BorelSpace G] in
include hτ in
/-- The midpoint replacement preserves every value on the continuous fibres. -/
theorem modulatedPoissonMidpoint_eq_of_continuous (χ : G →ₜ* Circle) (φ : G → ℂ)
    (hφ : ∀ (k : m.toMonoidHom.ker) g, (χ k.val : ℂ) * φ (k.val * g) = φ g)
    (left right : ℝ → ℂ) (g : G)
    (hc : ContinuousAt (modulatedTwistedProfile τ χ φ) (modulatedLog m g))
    (hl : Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[<] (modulatedLog m g))
      (𝓝 (left (modulatedLog m g))))
    (hr : Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[>] (modulatedLog m g))
      (𝓝 (right (modulatedLog m g)))) :
    modulatedPoissonMidpoint m χ left right g = φ g := by
  rw [modulatedPoissonMidpoint, tendsto_nhds_unique hl (hc.tendsto.mono_left nhdsWithin_le_nhds),
    tendsto_nhds_unique hr (hc.tendsto.mono_left nhdsWithin_le_nhds), ← modulatedTwist_factor m τ hτ χ φ hφ]
  have hn : (χ g : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [← two_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0),
    ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

omit [MeasurableSpace G] [BorelSpace G] in
include hτ in
/-- On each fibre, undoing the character twist gives the original
one-sided limits and hence their arithmetic mean. -/
theorem modulatedPoissonMidpoint_oneSided (χ : G →ₜ* Circle) (φ : G → ℂ)
    (hφ : ∀ (k : m.toMonoidHom.ker) g, (χ k.val : ℂ) * φ (k.val * g) = φ g)
    (left right : ℝ → ℂ) (t : ℝ) (k : m.toMonoidHom.ker)
    (hl : Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[<] t) (𝓝 (left t)))
    (hr : Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[>] t) (𝓝 (right t))) :
    let sectionAt (s : ℝ) := τ (Multiplicative.ofAdd s) * k.val
    let leftValue := ((χ (sectionAt t) : ℂ)⁻¹) * left t
    let rightValue := ((χ (sectionAt t) : ℂ)⁻¹) * right t
    Tendsto (fun s => φ (sectionAt s)) (𝓝[<] t) (𝓝 leftValue) ∧
      Tendsto (fun s => φ (sectionAt s)) (𝓝[>] t) (𝓝 rightValue) ∧
      modulatedPoissonMidpoint m χ left right (sectionAt t) = (leftValue + rightValue) / 2 := by
  let a (s : ℝ) := τ (Multiplicative.ofAdd s) * k.val
  have ha : Continuous a := (τ.continuous_toFun.comp continuous_ofAdd).mul continuous_const
  have hlog (s : ℝ) : modulatedLog m (a s) = s := by
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd s) * k.val)) = s
    rw [map_mul, hτ, show m k.val = 1 from k.property, mul_one, toAdd_ofAdd]
  let c (s : ℝ) := ((χ (a s) : ℂ)⁻¹)
  have hc : Continuous c :=
    (continuous_subtype_val.comp (χ.continuous_toFun.comp ha)).inv₀ fun s => Circle.coe_ne_zero _
  have he (s : ℝ) : c s * modulatedTwistedProfile τ χ φ s = φ (a s) := by
    have h := modulatedTwist_factor m τ hτ χ φ hφ (a s)
    rw [hlog s] at h
    rw [← h, ← mul_assoc]
    change ((χ (a s) : ℂ)⁻¹) * (χ (a s) : ℂ) * φ (a s) = _
    rw [inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
  change Tendsto (φ ∘ a) (𝓝[<] t) (𝓝 (c t * left t)) ∧
    Tendsto (φ ∘ a) (𝓝[>] t) (𝓝 (c t * right t)) ∧
    modulatedPoissonMidpoint m χ left right (a t) = (c t * left t + c t * right t) / 2
  refine ⟨?_, ?_, ?_⟩
  · exact (((hc.tendsto t).mono_left nhdsWithin_le_nhds).mul hl).congr he
  · exact (((hc.tendsto t).mono_left nhdsWithin_le_nhds).mul hr).congr he
  · change c t * ((left (modulatedLog m (a t)) + right (modulatedLog m (a t))) / 2) = _
    rw [hlog, ← mul_div_assoc, mul_add]

/-- Replacing the jump values leaves the Haar integrals unchanged. -/
theorem modulatedPoissonMidpoint_ae_eq
    (ν : Measure m.toMonoidHom.ker) [IsProbabilityMeasure ν]
    (χ : G →ₜ* Circle) (φ : G → ℂ)
    (hφ : ∀ (k : m.toMonoidHom.ker) g, (χ k.val : ℂ) * φ (k.val * g) = φ g)
    (S : Finset ℝ) (left right : ℝ → ℂ)
    (hC : ∀ t ∉ S, ContinuousAt (modulatedTwistedProfile τ χ φ) t)
    (hl : ∀ t, Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[<] t) (𝓝 (left t)))
    (hr : ∀ t, Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[>] t) (𝓝 (right t))) :
    modulatedPoissonMidpoint m χ left right =ᵐ[modulatedLogMeasure m τ hτ ν] φ := by
  have hm : Measurable (modulatedLog m) := (continuous_toAdd.comp m.continuous_toFun).measurable
  have hS : ∀ᵐ t ∂Measure.map (modulatedLog m) (modulatedLogMeasure m τ hτ ν),
      t ∈ (S : Set ℝ)ᶜ := by
    rw [modulatedLogMeasure_log_pushforward]
    apply ae_iff.mpr
    change volume ((S : Set ℝ)ᶜ)ᶜ = 0
    rw [compl_compl]
    exact S.finite_toSet.measure_zero volume
  have hF := (ae_map_iff hm.aemeasurable S.finite_toSet.measurableSet.compl).mp hS
  filter_upwards [hF] with g hg
  exact modulatedPoissonMidpoint_eq_of_continuous m τ hτ χ φ hφ left right g
    (hC _ hg) (hl _) (hr _)

set_option backward.isDefEq.respectTransparency false in
/-- Corrected D.3.5.1. With the positive exponential convention in the
integral, reconstruction uses the negative frequency at the evaluation
point. The character is absorbed into the profile before sampling.
The first log derivative of that profile has superexponential tails. -/
theorem modulated_poisson_finite_jumps
    (ν : Measure m.toMonoidHom.ker) [IsProbabilityMeasure ν]
    (γ : G) (hγ : 0 < modulatedLog m γ) (χ : G →ₜ* Circle) (φ : G → ℂ)
    (hφ : ∀ (k : m.toMonoidHom.ker) g, (χ k.val : ℂ) * φ (k.val * g) = φ g)
    (S : Finset ℝ) (v left right : ℝ → ℂ)
    (hu : SuperExponentialLogDecay (modulatedTwistedProfile τ χ φ))
    (hv : SuperExponentialLogDecay v)
    (hD : ∀ t ∉ S, HasDerivAt (modulatedTwistedProfile τ χ φ) (v t) t)
    (hcv : ContinuousOn v ((S : Set ℝ)ᶜ))
    (hl : ∀ t, Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[<] t) (𝓝 (left t)))
    (hr : ∀ t, Tendsto (modulatedTwistedProfile τ χ φ) (𝓝[>] t) (𝓝 (right t)))
    (x : G) :
    let d := modulatedLog m γ
    let freq := modulatedPoissonFrequency d
    let test := modulatedPoissonMidpoint m χ left right
    let samples (n : ℤ) := (χ (γ ^ n * x) : ℂ) * test (γ ^ n * x)
    Summable (fun n : ℤ => ‖samples n‖) ∧
      Tendsto (fun N : ℕ => (d : ℂ)⁻¹ * ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        Complex.exp (-freq k * (modulatedLog m x : ℂ)) *
          ∫ g, Complex.exp (freq k * (modulatedLog m g : ℂ)) * ((χ g : ℂ) * φ g)
            ∂modulatedLogMeasure m τ hτ ν) atTop (𝓝 (∑' n : ℤ, samples n)) := by
  let d := modulatedLog m γ
  let r := modulatedLog m x
  have hS (n : ℤ) :
      (χ (γ ^ n * x) : ℂ) * modulatedPoissonMidpoint m χ left right (γ ^ n * x) =
        (left (d * n + r) + right (d * n + r)) / 2 := by
    have hlog : modulatedLog m (γ ^ n * x) = d * n + r := by
      simp only [modulatedLog, map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul, d, r]
      rw [mul_comm]
    rw [modulatedPoissonMidpoint, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul, hlog]
  have hI (k : ℤ) :
      (∫ g, Complex.exp (modulatedPoissonFrequency d k * (modulatedLog m g : ℂ)) *
        ((χ g : ℂ) * φ g) ∂modulatedLogMeasure m τ hτ ν) =
        ∫ t : ℝ, Complex.exp (modulatedPoissonFrequency d k * (t : ℂ)) *
          modulatedTwistedProfile τ χ φ t := by
    simp_rw [modulatedTwist_factor m τ hτ χ φ hφ]
    exact integral_modulatedLogMeasure m τ hτ ν
      (fun t => Complex.exp (modulatedPoissonFrequency d k * (t : ℂ)) *
        modulatedTwistedProfile τ χ φ t)
  let samples (n : ℤ) := (χ (γ ^ n * x) : ℂ) *
    modulatedPoissonMidpoint m χ left right (γ ^ n * x)
  let coeff (k : ℤ) := ∫ g, Complex.exp (modulatedPoissonFrequency d k * (modulatedLog m g : ℂ)) *
    ((χ g : ℂ) * φ g) ∂modulatedLogMeasure m τ hτ ν
  change Summable (fun n => ‖samples n‖) ∧
    Tendsto (fun N : ℕ => (d : ℂ)⁻¹ * ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      Complex.exp (-modulatedPoissonFrequency d k * (r : ℂ)) * coeff k)
      atTop (𝓝 (∑' n : ℤ, samples n))
  rw [show samples = _ from funext hS, show coeff = _ from funext hI]
  exact jumpPoisson_shifted_logLattice S hu hv hD hcv hl hr hγ r

end Modulated


private theorem logDecay_of_continuous_compactSupport {u : ℝ → ℂ}
    (hcu : Continuous u) (hsu : HasCompactSupport u) : SuperExponentialLogDecay u := by
  obtain ⟨M, hM⟩ := hcu.norm.bddAbove_range_of_hasCompactSupport hsu.norm
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hsu.isCompact.isBounded
  refine ⟨⟨M, fun t => hM (mem_range_self t)⟩, fun n => ?_⟩
  refine ⟨1, |R| + 1, zero_lt_one, by positivity, fun t ht => ?_⟩
  have hzero : u t = 0 := by
    by_contra h
    have hmem : t ∈ tsupport u := subset_tsupport _ h
    have hball := hR hmem
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
    linarith [le_abs_self R]
  simpa only [hzero, norm_zero, one_mul] using Real.exp_nonneg (-(n : ℝ) * |t|)

/-- The printed sign in (D.3.5.3) reconstructs the reflection of the
periodized test. A smooth compactly supported bump separates the two values. -/
theorem modulated_poisson_printed_sign_obstruction :
    ∃ u : ℝ → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      (∑' n : ℤ, u ((n : ℝ) + 1 / 4)) = 1 ∧
      Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
        Complex.exp (modulatedPoissonFrequency 1 m * (1 / 4 : ℂ)) *
          ∫ t : ℝ, Complex.exp (modulatedPoissonFrequency 1 m * (t : ℂ)) * u t)
        atTop (𝓝 0) := by
  let b : ContDiffBump (1 / 4 : ℝ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  let u (t : ℝ) := (b t : ℂ)
  have hCu : ContDiff ℝ ∞ u := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hsu : HasCompactSupport u := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hwindow (t : ℝ) (ht : u t ≠ 0) : 1 / 8 < t ∧ t < 3 / 8 := by
    have hb : t ∈ Function.support b := fun hz => ht (by simp [u, hz])
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hb
    change -(1 / 8 : ℝ) < t - 1 / 4 ∧ t - 1 / 4 < 1 / 8 at hb
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hone : u (1 / 4) = 1 := by
    change (b (1 / 4) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt b.rIn_pos))]
    norm_num
  have hsample : (∑' n : ℤ, u ((n : ℝ) + 1 / 4)) = 1 := by
    rw [tsum_eq_single (0 : ℤ)]
    · simpa using hone
    · intro n hn
      by_contra hne
      obtain ⟨ha, hb⟩ := hwindow _ hne
      have hnl : (-(1 : ℤ) : ℝ) < (n : ℝ) := by push_cast; linarith
      have hnu : (n : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
      exact hn (by exact_mod_cast (show n = 0 by
        have h₁ : -1 < n := by exact_mod_cast hnl
        have h₂ : n < 1 := by exact_mod_cast hnu
        omega))
  have hreflection (n : ℤ) : u ((n : ℝ) + (-(1 / 4) : ℝ)) = 0 := by
    by_contra hne
    obtain ⟨ha, hb⟩ := hwindow _ hne
    have hnl : ((0 : ℤ) : ℝ) < (n : ℝ) := by push_cast; linarith
    have hnu : (n : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
    have h₁ : 0 < n := by exact_mod_cast hnl
    have h₂ : n < 1 := by exact_mod_cast hnu
    omega
  let v := deriv u
  have h₁ : ContDiff ℝ 1 u := hCu.of_le (by simp)
  have hc : Continuous v := h₁.continuous_deriv_one
  have hlim := (jumpPoisson_shifted_logLattice (u := u) (v := v) (left := u) (right := u) ∅
    (logDecay_of_continuous_compactSupport hCu.continuous hsu)
    (logDecay_of_continuous_compactSupport hc hsu.deriv)
    (fun t _ => (h₁.differentiable (by norm_num) t).hasDerivAt) hc.continuousOn
    (fun t => (hCu.continuous.tendsto t).mono_left nhdsWithin_le_nhds)
    (fun t => (hCu.continuous.tendsto t).mono_left nhdsWithin_le_nhds)
    (d := 1) zero_lt_one (-(1 / 4))).2
  have hzero : (∑' n : ℤ, (u ((1 : ℝ) * n + -(1 / 4)) + u ((1 : ℝ) * n + -(1 / 4))) / 2) = 0 := by
    simp only [one_mul, hreflection, zero_add, zero_div, tsum_zero]
  dsimp only at hlim
  rw [hzero] at hlim
  refine ⟨u, hCu, hsu, hsample, ?_⟩
  suffices he : ∀ k : ℤ,
      -modulatedPoissonFrequency 1 k * (↑(-(1 / 4 : ℝ)) : ℂ) =
        modulatedPoissonFrequency 1 k * (1 / 4 : ℂ) by
    simpa only [Complex.ofReal_one, inv_one, one_mul, he] using hlim
  intro k
  push_cast
  ring


end

end Masullo
