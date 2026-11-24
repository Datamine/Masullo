import SLocalThetaLargeNorm
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev IdeleS := (SAdeles F S)ˣ

private def liftLocalFlow (γ : Multiplicative ℝ →* IdeleS F S) : Multiplicative ℝ →* Idele F :=
  ((sIdeleBlock F S).subtype.comp (sLocalEmbed F S)).comp γ

private theorem liftLocalFlow_continuous (γ : Multiplicative ℝ →* IdeleS F S) (hγ : Continuous γ) :
    Continuous (liftLocalFlow F S γ) := by
  exact continuous_subtype_val.comp
    ((sBlockUnitProduct F S).symm.continuous.comp (hγ.prodMk continuous_const))

/-- Lemma 2.3.2.1. The directional derivative is a continuous linear endomorphism
of the actual S-local Schwartz–Bruhat test space. -/
def sLocalBruhatDerivative (γ : Multiplicative ℝ →* IdeleS F S) (hγ : Continuous γ) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S := by
  let g := liftLocalFlow F S γ
  let hg := liftLocalFlow_continuous F S γ hγ
  let D := GlobalBruhat.derivative F g hg
  have hD (f : sLocalBruhatImage F S) : D f.val ∈ sLocalBruhatImage F S :=
    sLocalBruhat_derivative_mem F S g hg f.val f.property
  exact ⟨(D.toLinearMap.comp (sLocalBruhatImage F S).subtype).codRestrict _ hD,
    (D.continuous.comp continuous_subtype_val).subtype_mk hD⟩

theorem sLocalBruhatDerivative_hasDerivAt (γ : Multiplicative ℝ →* IdeleS F S) (hγ : Continuous γ)
    (f : sLocalBruhatImage F S) (x : SAdeles F S) :
    HasDerivAt (fun t : ℝ => sLocalBruhatRestriction F S f.val
      ((γ (Multiplicative.ofAdd (Real.log t))).val * x))
      (sLocalBruhatRestriction F S (sLocalBruhatDerivative F S γ hγ f).val x) 1 := by
  let g := liftLocalFlow F S γ
  let hg := liftLocalFlow_continuous F S γ hγ
  let φ := GlobalBruhat.algebraicEquiv F f.val
  let a := sLocalBruhatPad F S x
  have hd := algebraicBruhatDeriv_hasDerivAt F g hg φ a
  have he (t : ℝ) :
      sLocalBruhatPad F S ((γ (Multiplicative.ofAdd (Real.log t))).val * x) =
        positiveParameterOrbit F g a t := by
    have h := sLocalEmbed_project F S (γ (Multiplicative.ofAdd (Real.log t)))
    rw [← h, sLocalBruhatPad_mul_project]
    rfl
  change HasDerivAt (fun t : ℝ => φ.val
    (sLocalBruhatPad F S ((γ (Multiplicative.ofAdd (Real.log t))).val * x))) _ 1
  simp only [he]
  exact hd

theorem sLocalBruhatDerivative_continuousProfile (γ : Multiplicative ℝ →* IdeleS F S)
    (hγ : Continuous γ) (f : sLocalBruhatImage F S) :
    Continuous (sLocalBruhatRestriction F S (sLocalBruhatDerivative F S γ hγ f).val) :=
  sLocalBruhatRestriction_continuous F S _

private theorem sLocalBruhat_log_orbit_hasDerivAt (γ : Multiplicative ℝ →* IdeleS F S)
    (hγ : Continuous γ) (f : sLocalBruhatImage F S) (x : SAdeles F S) (r : ℝ) :
    HasDerivAt (fun t : ℝ => sLocalBruhatRestriction F S f.val
      ((γ (Multiplicative.ofAdd t)).val * x))
      (sLocalBruhatRestriction F S (sLocalBruhatDerivative F S γ hγ f).val
        ((γ (Multiplicative.ofAdd r)).val * x)) r := by
  let b := (γ (Multiplicative.ofAdd r)).val * x
  let φ := sLocalBruhatRestriction F S f.val
  let D := sLocalBruhatRestriction F S (sLocalBruhatDerivative F S γ hγ f).val
  have he : HasDerivAt Real.exp 1 0 := by simpa only [Real.exp_zero] using Real.hasDerivAt_exp 0
  have h1 : HasDerivAt (fun t => φ ((γ (Multiplicative.ofAdd (Real.log t))).val * b))
      (D b) (Real.exp 0) := by
    simpa only [Real.exp_zero] using sLocalBruhatDerivative_hasDerivAt F S γ hγ f b
  have h₀ : HasDerivAt (fun t : ℝ => φ ((γ (Multiplicative.ofAdd t)).val * b)) (D b) 0 := by
    simpa only [Function.comp_def, Real.log_exp, one_smul] using h1.scomp 0 he
  have hs : HasDerivAt (fun t : ℝ => φ ((γ (Multiplicative.ofAdd t)).val * b)) (D b) (r - r) := by
    simpa only [sub_self] using h₀
  have hshift := hs.comp_sub_const r r
  have hf (t : ℝ) : (γ (Multiplicative.ofAdd (t - r))).val * b =
      (γ (Multiplicative.ofAdd t)).val * x := by
    dsimp [b]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul]
    change (γ (Multiplicative.ofAdd ((t - r) + r))).val * x = _
    rw [sub_add_cancel]
  simpa only [hf] using hshift

private theorem sLocalThetaOnIdeles_log_orbit_hasDerivAt (γ : Multiplicative ℝ →* IdeleS F S)
    (hγ : Continuous γ) (f : sLocalBruhatImage F S) (g : IdeleS F S) (r : ℝ) :
    HasDerivAt (fun t : ℝ => sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val)
      (γ (Multiplicative.ofAdd t) * g))
      (sLocalThetaOnIdeles F S
        (sLocalBruhatRestriction F S (sLocalBruhatDerivative F S γ hγ f).val)
        (γ (Multiplicative.ofAdd r) * g)) r := by
  let D := sLocalBruhatDerivative F S γ hγ f
  let a (t : ℝ) := γ (Multiplicative.ofAdd t) * g
  have ha : Continuous a := (hγ.comp continuous_ofAdd).mul continuous_const
  let U := Additive (sIntegerRing F S)ˣ
  let term (f₀ : GlobalBruhat F) (u : U) (t : ℝ) :=
    sLocalBruhatRestriction F S f₀ (sIntegerDiagonal F S u.toMul.val * (a t).val)
  have hterm (u : U) (t : ℝ) : HasDerivAt (term f.val u) (term D.val u t) t := by
    have hx (s : ℝ) :
        sIntegerDiagonal F S u.toMul.val * (a s).val =
          (γ (Multiplicative.ofAdd s)).val * (sIntegerDiagonal F S u.toMul.val * g.val) := by
      rw [show (a s).val = (γ (Multiplicative.ofAdd s)).val * g.val from rfl, mul_left_comm]
    simpa only [term, hx, D] using
      sLocalBruhat_log_orbit_hasDerivAt F S γ hγ f (sIntegerDiagonal F S u.toMul.val * g.val) t
  have hsum := hasSumLocallyUniformly_iff_tendstoLocallyUniformly.mp
    (sLocalTheta_hasSumLocallyUniformly F S D.val)
  have hlim : TendstoLocallyUniformly
      (fun (I : Finset U) t => ∑ u ∈ I, term D.val u t)
      (fun t => sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S D.val) (a t)) atTop :=
    hsum.comp a ha
  apply hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hlim.tendstoLocallyUniformlyOn
    (f := fun (I : Finset U) t => ∑ u ∈ I, term f.val u t) _ _ (mem_univ r)
  · exact Eventually.of_forall fun I t _ => HasDerivAt.fun_sum fun u _ => hterm u t
  · intro t _
    exact (sLocalTheta_restriction_summable F S f.val (a t)).of_norm.hasSum

private theorem sLocalTheta_log_orbit_hasDerivAt (γ : Multiplicative ℝ →* IdeleS F S)
    (hγ : Continuous γ) (f : sLocalBruhatImage F S) (q : SIdeleQuotient F S) (r : ℝ) :
    HasDerivAt (fun t : ℝ => sLocalTheta F S (sLocalBruhatRestriction F S f.val)
      (QuotientGroup.mk (γ (Multiplicative.ofAdd t)) * q))
      (sLocalTheta F S (sLocalBruhatRestriction F S (sLocalBruhatDerivative F S γ hγ f).val)
        (QuotientGroup.mk (γ (Multiplicative.ofAdd r)) * q)) r := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have he (t : ℝ) : QuotientGroup.mk (γ (Multiplicative.ofAdd t)) * QuotientGroup.mk g =
      QuotientGroup.mk (γ (Multiplicative.ofAdd t) * g) :=
    ((QuotientGroup.mk' (sUnitImage F S)).map_mul _ _).symm
  simpa only [he, sLocalTheta_mk] using sLocalThetaOnIdeles_log_orbit_hasDerivAt F S γ hγ f g r

section Homogeneous

variable [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)]

private theorem sLocalHomogeneousTheta_log_hasDerivAt_zero
    (γ : Multiplicative ℝ →* IdeleS F S) (hγ : Continuous γ)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : sLocalBruhatImage F S) (q : SIdeleQuotient F S) :
    HasDerivAt (fun t : ℝ => sLocalHomogeneousTheta F S μ ω f.val
      (QuotientGroup.mk (γ (Multiplicative.ofAdd t)) * q))
      (sLocalHomogeneousTheta F S μ ω (sLocalBruhatDerivative F S γ hγ f).val q) 0 := by
  let D := sLocalBruhatDerivative F S γ hγ f
  let a (t : ℝ) : SIdeleQuotient F S := QuotientGroup.mk (γ (Multiplicative.ofAdd t)) * q
  have hg : Continuous (fun t : ℝ =>
      (QuotientGroup.mk (γ (Multiplicative.ofAdd t)) : SIdeleQuotient F S)) :=
    QuotientGroup.continuous_mk.comp (hγ.comp continuous_ofAdd)
  have ha : Continuous a := hg.mul (continuous_const (y := q))
  have ha₀ : a 0 = q := by
    change QuotientGroup.mk' (sUnitImage F S) (γ 1) * q = q
    rw [map_one, map_one]
    exact one_mul q
  let v (f₀ : GlobalBruhat F) (t : ℝ) (k : SLocalThetaNormOne F S) : ℂ :=
    ((ω k : Circle) : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f₀) (k.val * a t)
  have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨M, hM, hb⟩ := sLocalHomogeneousTheta_compact_majorant F S μ ω D.val
    (a '' Icc (-1 : ℝ) 1) (isCompact_Icc.image ha)
  have hint (f₀ : GlobalBruhat F) (t : ℝ) : Integrable (v f₀ t) μ :=
    sLocalHomogeneousTheta_integrable F S μ ω f₀ (a t)
  have hdiff (t : ℝ) (k : SLocalThetaNormOne F S) :
      HasDerivAt (fun s => v f.val s k) (v D.val t k) t := by
    have he (s : ℝ) : k.val * a s = QuotientGroup.mk (γ (Multiplicative.ofAdd s)) * (k.val * q) := by
      exact mul_left_comm k.val
        (QuotientGroup.mk (γ (Multiplicative.ofAdd s)) : SIdeleQuotient F S) q
    simpa only [v, he, D] using
      (sLocalTheta_log_orbit_hasDerivAt F S γ hγ f (k.val * q) t).const_mul ((ω k : Circle) : ℂ)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := v f.val)
    (F' := v D.val) hs (Eventually.of_forall fun t => (hint f.val t).aestronglyMeasurable)
    (hint f.val 0) (hint D.val 0).aestronglyMeasurable
    (Eventually.of_forall fun k t ht => hb (a t) ⟨t, Ioo_subset_Icc_self ht, rfl⟩ k) hM
    (Eventually.of_forall fun k t _ => hdiff t k)).2
  simpa only [v, ha₀, sLocalHomogeneousTheta] using h

/-- Differentiation along the logarithmic flow at an arbitrary parameter. -/
theorem sLocalHomogeneousTheta_log_hasDerivAt
    (γ : Multiplicative ℝ →* IdeleS F S) (hγ : Continuous γ)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : sLocalBruhatImage F S) (r : ℝ) :
    HasDerivAt (fun t : ℝ => sLocalHomogeneousTheta F S μ ω f.val
      (QuotientGroup.mk (γ (Multiplicative.ofAdd t))))
      (sLocalHomogeneousTheta F S μ ω (sLocalBruhatDerivative F S γ hγ f).val
        (QuotientGroup.mk (γ (Multiplicative.ofAdd r)))) r := by
  let q : Multiplicative ℝ →* SIdeleQuotient F S :=
    (QuotientGroup.mk' (sUnitImage F S)).comp γ
  have h := sLocalHomogeneousTheta_log_hasDerivAt_zero F S γ hγ μ ω f (q (Multiplicative.ofAdd r))
  have hz : r - r = 0 := sub_self r
  have hr : HasDerivAt (fun t : ℝ ↦ t - r) 1 r := by
    simpa only [id_eq] using ((hasDerivAt_id r).sub_const r)
  have hd := h.scomp_of_eq r hr hz.symm
  simp only [one_smul] at hd
  have he : ((fun t : ℝ => sLocalHomogeneousTheta F S μ ω f.val
      (q (Multiplicative.ofAdd t) * q (Multiplicative.ofAdd r))) ∘ fun t => t - r) =
        fun t => sLocalHomogeneousTheta F S μ ω f.val (q (Multiplicative.ofAdd t)) := by
    funext t
    apply congrArg (sLocalHomogeneousTheta F S μ ω f.val)
    change q (Multiplicative.ofAdd (t - r)) * q (Multiplicative.ofAdd r) = _
    rw [← map_mul]
    exact congrArg (fun y : ℝ ↦ q (Multiplicative.ofAdd y)) (sub_add_cancel t r)
  exact he ▸ hd

/-- Proposition 2.3.2.2. The directional derivative passes through the S-unit
series and through the norm-one Haar character average. Both derivative
profiles are continuous on the S-idele quotient. -/
theorem sLocalTheta_directionalDerivatives (γ : Multiplicative ℝ →* IdeleS F S)
    (hγ : Continuous γ) (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) :
    let D := sLocalBruhatDerivative F S γ hγ f
    let φ := sLocalTheta F S (sLocalBruhatRestriction F S f.val)
    let φ' := sLocalTheta F S (sLocalBruhatRestriction F S D.val)
    let ψ := sLocalHomogeneousTheta F S μ ω f.val
    let ψ' := sLocalHomogeneousTheta F S μ ω D.val
    Continuous φ' ∧ Continuous ψ' ∧
      ∀ q : SIdeleQuotient F S,
        HasDerivAt (fun t : ℝ => φ (QuotientGroup.mk (γ (Multiplicative.ofAdd (Real.log t))) * q)) (φ' q) 1 ∧
        HasDerivAt (fun t : ℝ => ψ (QuotientGroup.mk (γ (Multiplicative.ofAdd (Real.log t))) * q)) (ψ' q) 1 := by
  let D := sLocalBruhatDerivative F S γ hγ f
  refine ⟨sLocalTheta_continuous F S D.val, sLocalHomogeneousTheta_continuous F S μ ω D.val, ?_⟩
  intro q
  have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have hz : (QuotientGroup.mk (γ (Multiplicative.ofAdd (Real.log 1))) : SIdeleQuotient F S) * q = q := by
    rw [Real.log_one]
    change QuotientGroup.mk' (sUnitImage F S) (γ 1) * q = q
    rw [map_one, map_one]
    exact one_mul q
  have h₁ := sLocalTheta_log_orbit_hasDerivAt F S γ hγ f q (Real.log 1)
  rw [hz] at h₁
  have h₂ : HasDerivAt (fun t : ℝ => sLocalHomogeneousTheta F S μ ω f.val
      (QuotientGroup.mk (γ (Multiplicative.ofAdd t)) * q))
      (sLocalHomogeneousTheta F S μ ω D.val q) (Real.log 1) := by
    simpa only [Real.log_one] using sLocalHomogeneousTheta_log_hasDerivAt_zero F S γ hγ μ ω f q
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, one_smul] using h₁.scomp 1 hlog
  · simpa only [Function.comp_def, one_smul] using h₂.scomp 1 hlog

end Homogeneous

end

end Masullo
