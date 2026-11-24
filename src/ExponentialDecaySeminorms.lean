/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import MellinBergman
import MellinCoordinates
import SchwartzFourierSeminorms

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal SchwartzMap

namespace Masullo

noncomputable section

set_option maxHeartbeats 800000

/-- Paper: (D.3.2.3–4), p. 803. In logarithmic coordinates the weighted
L² norm is the norm of this exponentially and polynomially weighted derivative. -/
def exponentialDecayL2Integrand (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) : ℂ :=
  ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ) * iteratedDeriv m f.val x

/-- Paper: (D.3.2.3–4), p. 803. At b = 0 the logarithmic power disappears,
leaving the pure exponential weight. -/
theorem exponentialDecayL2Integrand_zero_log (a : ℝ) (m : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    exponentialDecayL2Integrand a 0 m f x =
      (Real.exp (a * |x|) : ℂ) * iteratedDeriv m f.val x := by
  simp [exponentialDecayL2Integrand]

private def decayTwistCLM (c : ℝ) : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(ℝ, ℂ) :=
  ⟨logExponentialDecayTwist univ ⟨c, mem_univ c⟩,
    (continuous_apply (⟨c, mem_univ c⟩ : (univ : Set ℝ))).comp
      (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).continuous⟩

private theorem decayProfile_smooth (f : PositiveRealExponentialDecay univ) : ContDiff ℝ ∞ f.val := by
  have h : ⇑(decayTwistCLM 0 f) = f.val := by
    funext x
    change logExponentialDecayTwist univ ⟨0, _⟩ f x = _
    simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
      logExponentialDecayTwist_apply univ ⟨0, mem_univ (0 : ℝ)⟩ f x
  rw [← h]
  exact (decayTwistCLM 0 f).smooth _

/-- Differentiate the profile before applying the exponential twist. -/
private def decayWeightedDeriv (c : ℝ) (m : ℕ) : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((SchwartzMap.derivCLM ℂ ℂ - (c : ℂ) • ContinuousLinearMap.id ℂ _) ^ m).comp (decayTwistCLM c)

private theorem decayWeightedDeriv_apply (c : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ) :
    ⇑(decayWeightedDeriv c m f) =
      fun x : ℝ ↦ (Real.exp (c * x) : ℂ) * iteratedDeriv m f.val x := by
  induction m with
  | zero =>
    funext x
    exact logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f x
  | succ m ih =>
    funext x
    simp only [decayWeightedDeriv, pow_succ', ContinuousLinearMap.comp_apply] at ih ⊢
    change deriv (⇑(decayWeightedDeriv c m f)) x - c * decayWeightedDeriv c m f x = _
    change ⇑(decayWeightedDeriv c m f) = _ at ih
    rw [ih, iteratedDeriv_succ]
    have he : HasDerivAt (fun x : ℝ ↦ (Real.exp (c * x) : ℂ)) ((c * Real.exp (c * x) : ℝ) : ℂ) x := by
      apply HasDerivAt.ofReal_comp
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul c).exp
    have hd := ((decayProfile_smooth f).differentiable_iteratedDeriv m
      (by exact_mod_cast ENat.natCast_lt_top m)) x
    rw [(he.fun_mul hd.hasDerivAt).deriv]
    push_cast
    ring

/-- The polynomially weighted exponential envelope belongs to L² on both half-lines. -/
private theorem memLp_decayEnvelope (s b : ℝ) (hs : 0 < s) (hb : 0 ≤ b) :
    MemLp (fun x : ℝ ↦ |x| ^ b * Real.exp (-s * |x|)) 2 volume := by
  have hcont : Continuous (fun x : ℝ ↦ |x| ^ b * Real.exp (-s * |x|)) :=
    ((Real.continuous_rpow_const hb).comp continuous_abs).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  apply (integrable_norm_rpow_iff hcont.aestronglyMeasurable (by norm_num) (by norm_num)).mp
  have hpos : IntegrableOn
      (fun x : ℝ ↦ ‖|x| ^ b * Real.exp (-s * |x|)‖ ^ (2 : ℝ≥0∞).toReal) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (b := 2 * s) (s := b * 2)
      (by linarith) (by norm_num) (by positivity)).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    change 0 < x at hx
    dsimp only
    rw [abs_of_pos hx, Real.norm_of_nonneg (by positivity), ENNReal.toReal_ofNat,
      Real.rpow_two, mul_pow, Real.rpow_one, ← Real.rpow_mul_natCast hx.le, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa [Function.comp_def, neg_preimage] using hpos

private def decayL2ProfileMap (a b : ℝ) (m : ℕ) : PositiveRealExponentialDecay univ →ₗ[ℂ] (ℝ → ℂ) :=
  (LinearMap.mulLeft ℂ fun x : ℝ ↦ ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ)).comp
    (realSchwartzCoe.comp (decayWeightedDeriv 0 m).toLinearMap)

private theorem decayL2ProfileMap_apply (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) :
    decayL2ProfileMap a b m f x = exponentialDecayL2Integrand a b m f x := by
  change _ * (decayWeightedDeriv 0 m f x) = _
  rw [congrFun (decayWeightedDeriv_apply 0 m f) x]
  simp [exponentialDecayL2Integrand]

/-- Paper: Lemma D.3.2.7(1), p. 803. Each weighted derivative is in L² and its
L² norm defines a continuous seminorm. The choice b = 0 includes (D.3.2.3). -/
theorem exponentialDecayL2_continuous_seminorm (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    let w := exponentialDecayL2Integrand a b m
    (∀ f, MemLp (w f) 2 volume) ∧
      ∃ p : Seminorm ℂ (PositiveRealExponentialDecay univ), Continuous p ∧
        ∀ f, ENNReal.ofReal (p f) = eLpNorm (w f) 2 volume := by
  let T := decayL2ProfileMap a b m
  have hT (f : PositiveRealExponentialDecay univ) : T f = exponentialDecayL2Integrand a b m f :=
    funext (decayL2ProfileMap_apply a b m f)
  let H (x : ℝ) := |x| ^ b * Real.exp (-a * |x|)
  have hH : MemLp H 2 volume := memLp_decayEnvelope a b ha hb
  let q (c : ℝ) := (SchwartzMap.seminorm ℂ 0 0).comp (decayWeightedDeriv c m).toLinearMap
  let Q := q (2 * a) + q (-(2 * a))
  have hc (c : ℝ) : Continuous (q c) :=
    ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 0)).comp
      (decayWeightedDeriv c m).continuous
  have hQ : Continuous Q := (hc _).add (hc _)
  have hmeas (f : PositiveRealExponentialDecay univ) : AEStronglyMeasurable (T f) volume := by
    rw [hT]
    apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
        ((Real.continuous_rpow_const hb).comp continuous_abs))).mul
      ((decayProfile_smooth f).continuous_iteratedDeriv m (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))
  have hbound (f : PositiveRealExponentialDecay univ) : ∀ᵐ x ∂volume, ‖T f x‖ ≤ Q f * ‖H x‖ := by
    apply Eventually.of_forall
    intro x
    have hside (c : ℝ) (hx : c * x = (2 * a) * |x|) : ‖T f x‖ ≤ q c f * ‖H x‖ := by
      have he : Real.exp (a * |x|) = Real.exp (c * x) * Real.exp (-a * |x|) := by
        rw [← Real.exp_add, hx]
        congr 1
        ring
      have h := (decayWeightedDeriv c m f).norm_le_seminorm ℂ x
      change ‖decayWeightedDeriv c m f x‖ ≤ q c f at h
      calc
        ‖T f x‖ = ‖decayWeightedDeriv c m f x‖ * ‖H x‖ := by
          rw [hT, congrFun (decayWeightedDeriv_apply c m f) x]
          simp only [exponentialDecayL2Integrand, H, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le,
            Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) b), he]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    rcases le_total 0 x with hx | hx
    · exact (hside (2 * a) (by rw [abs_of_nonneg hx])).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg _ _)) (norm_nonneg _))
    · exact (hside (-(2 * a)) (by rw [abs_of_nonpos hx]; ring)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (apply_nonneg _ _)) (norm_nonneg _))
  have hm (f : PositiveRealExponentialDecay univ) : MemLp (T f) 2 volume :=
    hH.of_le_mul (hmeas f) (hbound f)
  let L : PositiveRealExponentialDecay univ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    { toFun := fun f ↦ (hm f).toLp (T f)
      map_add' := fun f g ↦ by simp only [map_add]; rfl
      map_smul' := fun c f ↦ by simp only [map_smul]; rfl }
  let p := (normSeminorm ℂ _).comp L
  have hp (f : PositiveRealExponentialDecay univ) : p f = (eLpNorm (T f) 2 volume).toReal :=
    Lp.norm_toLp _ (hm f)
  refine ⟨fun f ↦ hT f ▸ hm f, p, ?_, fun f ↦ ?_⟩
  · let C := (eLpNorm H 2 volume).toNNReal
    apply Seminorm.continuous_of_le (q := C • Q) (hQ.const_smul C)
    intro f
    rw [hp]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_ne_top)
      (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hbound f) 2)
    change _ ≤ (eLpNorm H 2 volume).toReal * Q f
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (apply_nonneg Q f), mul_comm] using h
  · rw [hp, hT f, ENNReal.ofReal_toReal]
    exact (hT f ▸ hm f).eLpNorm_ne_top


private theorem real_exp_twist_derivatives (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (Real.exp (c * x) : ℂ)) =
      fun x : ℝ => (c : ℂ) ^ n * (Real.exp (c * x) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have he : HasDerivAt (fun y : ℝ => (Real.exp (c * y) : ℂ))
        ((c * Real.exp (c * x) : ℝ) : ℂ) x := by
      apply HasDerivAt.ofReal_comp
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul c).exp
    rw [(he.const_mul ((c : ℂ) ^ n)).deriv, pow_succ, Complex.ofReal_mul]
    ring

private theorem decayTwist_derivative_expansion (c : ℝ) (n : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    iteratedDeriv n (decayTwistCLM c f) x =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℂ) * (c : ℂ) ^ j) * decayWeightedDeriv c (n - j) f x := by
  have he : ⇑(decayTwistCLM c f) = fun y : ℝ => (Real.exp (c * y) : ℂ) * f.val y :=
    funext fun y => logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f y
  have hreal : ContDiff ℝ n (fun y : ℝ => Real.exp (c * y)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hs : ContDiff ℝ n (fun y : ℝ => (Real.exp (c * y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  rw [he, iteratedDeriv_fun_mul hs.contDiffAt
    ((decayProfile_smooth f).of_le (by exact_mod_cast le_top)).contDiffAt]
  simp_rw [real_exp_twist_derivatives, decayWeightedDeriv_apply, ← mul_assoc]

private theorem polynomial_exponential_le (k : ℕ) {a c x : ℝ} (h : |c| + 1 ≤ a) :
    |x| ^ k * Real.exp (c * x) ≤ k.factorial * Real.exp (a * |x|) := by
  have hpow : |x| ^ k ≤ (k.factorial : ℝ) * Real.exp |x| := by
    simpa [mul_comm] using
      (div_le_iff₀ (by positivity : 0 < (k.factorial : ℝ))).mp
        (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k)
  calc
    _ ≤ (k.factorial : ℝ) * Real.exp |x| * Real.exp (c * x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * Real.exp (|x| + c * x) := by rw [Real.exp_add, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right h (abs_nonneg x)
      have habs := le_abs_self (c * x)
      rw [abs_mul] at habs
      linarith

private theorem decayTwist_derivativeLp_bound {a c : ℝ} (ha : 0 < a) (hc : |c| + 1 ≤ a)
    (k n : ℕ) (f : PositiveRealExponentialDecay univ) :
    lpNorm (fun x : ℝ => (x : ℂ) ^ k * iteratedDeriv n (decayTwistCLM c f) x) 2 volume ≤
      ∑ j ∈ Finset.range (n + 1), ‖((n.choose j : ℂ) * (c : ℂ) ^ j)‖ *
        (k.factorial : ℝ) * lpNorm (exponentialDecayL2Integrand a 0 (n - j) f) 2 volume := by
  let G (j : ℕ) (x : ℝ) := (x : ℂ) ^ k * decayWeightedDeriv c (n - j) f x
  let C (j : ℕ) : ℂ := (n.choose j : ℂ) * (c : ℂ) ^ j
  let H (j : ℕ) := exponentialDecayL2Integrand a 0 (n - j) f
  have hHp (j : ℕ) : MemLp (H j) 2 volume :=
    (exponentialDecayL2_continuous_seminorm a 0 ha le_rfl _).1 f
  have hG (j : ℕ) (x : ℝ) : ‖G j x‖ ≤ (k.factorial : ℝ) * ‖H j x‖ := by
    simp only [G, H, exponentialDecayL2Integrand_zero_log, decayWeightedDeriv_apply,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (polynomial_exponential_le k hc) (norm_nonneg _)
  have hGp (j : ℕ) : MemLp (G j) 2 volume :=
    (hHp j).of_le_mul (by
      dsimp [G]
      apply Continuous.aestronglyMeasurable
      exact (Complex.continuous_ofReal.pow k).mul (decayWeightedDeriv c (n - j) f).continuous)
      (Eventually.of_forall (hG j))
  have he : (fun x : ℝ => (x : ℂ) ^ k * iteratedDeriv n (decayTwistCLM c f) x) =
      ∑ j ∈ Finset.range (n + 1), C j • G j := by
    funext x
    rw [decayTwist_derivative_expansion, Finset.mul_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp [G, C, Pi.smul_apply, smul_eq_mul]; ring
  rw [he]
  refine (lpNorm_sum_le (fun j _ => (hGp j).const_smul (C j)) (by norm_num)).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [lpNorm_const_smul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have Hnorm : MemLp (fun x ↦ (k.factorial : ℝ) * ‖H j x‖) 2 volume :=
    (hHp j).norm.const_mul _
  calc
    _ ≤ lpNorm (fun x ↦ (k.factorial : ℝ) * ‖H j x‖) 2 volume :=
      lpNorm_mono_real Hnorm (hG j)
    _ = _ := by
      change lpNorm ((k.factorial : ℝ) • (fun x ↦ ‖H j x‖)) 2 volume = _
      rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        lpNorm_norm (hHp j).aestronglyMeasurable]

private theorem exponentialDecayL2_family {ι : Type*} (a b : ι → ℝ) (m : ι → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i)
    (hcover : ∀ c : ℝ, ∃ A : ℝ, |c| + 1 ≤ A ∧
      ∃ e : ℕ → ι, ∀ j, a (e j) = A ∧ b (e j) = 0 ∧ m (e j) = j) :
    GeneratesLpSeminorms volume 2
      (fun i ↦ exponentialDecayL2Integrand (a i) (b i) (m i)) := by
  let E := PositiveRealExponentialDecay univ
  have hmem (i : ι) (f : E) :=
    (exponentialDecayL2_continuous_seminorm (a i) (b i) (ha i) (hb i) (m i)).1 f
  choose P hcont hval using fun i =>
    (exponentialDecayL2_continuous_seminorm (a i) (b i) (ha i) (hb i) (m i)).2
  let t : TopologicalSpace E := inferInstance
  have htop : t = (SeminormFamily.moduleFilterBasis P).topology := by
    let u : TopologicalSpace E := (SeminormFamily.moduleFilterBasis P).topology
    change t = u
    have hu : WithSeminorms (topology := u) P := ⟨rfl⟩
    have hsource := withGeneratingSeminorms_spec (logExponentialDecaySubmodule univ)
      (fun i : ↥(univ : Set ℝ) × ℕ × ℕ ↦
        (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist univ i.1))
    apply le_antisymm
    · exact le_topology_withSeminorms (t := t) hu hcont
    · let : TopologicalSpace E := u
      let : IsTopologicalAddGroup E := hu.topologicalAddGroup
      apply le_topology_withSeminorms (t := u) hsource
      rintro ⟨c, k, n⟩
      obtain ⟨A, hA, e, he⟩ := hcover c
      have hpos : 0 < A := (by positivity : (0 : ℝ) < |(c : ℝ)| + 1).trans_le hA
      let weight (k n j : ℕ) : ℝ≥0 :=
        ⟨‖((n.choose j : ℂ) * (c : ℂ) ^ j)‖ * (k.factorial : ℝ), by positivity⟩
      let Q (k n : ℕ) : Seminorm ℂ E :=
        ∑ j ∈ Finset.range (n + 1), weight k n j • P (e (n - j))
      have hQ (k n : ℕ) : Continuous (Q k n) := by
        exact Seminorm.continuous_finsetSum
          (fun j _ ↦ (hu.continuous_seminorm (e (n - j))).const_smul (weight k n j))
      have hnorm (j : ℕ) (f : E) :
          lpNorm (exponentialDecayL2Integrand A 0 j f) 2 volume = P (e j) f := by
        have hv := hval (e j) f
        have hm := hmem (e j) f
        rw [(he j).1, (he j).2.1, (he j).2.2] at hv hm
        rw [← toReal_eLpNorm hm.aestronglyMeasurable, ← hv, ENNReal.toReal_ofReal (apply_nonneg _ _)]
      have hbound (k n : ℕ) (f : E) :
          lpNorm (fun x : ℝ => (x : ℂ) ^ k * iteratedDeriv n (decayTwistCLM c f) x) 2 volume ≤
            Q k n f := by
        refine (decayTwist_derivativeLp_bound hpos hA k n f).trans ?_
        change _ ≤ FunLike.coeAddMonoidHom _ _ _
          (∑ j ∈ Finset.range (n + 1), weight k n j • P (e (n - j))) f
        simp only [map_sum, Finset.sum_apply]
        apply Finset.sum_le_sum
        intro j _
        change _ ≤ ‖((n.choose j : ℂ) * (c : ℂ) ^ j)‖ * (k.factorial : ℝ) * _
        rw [hnorm]
      let R := Q k n + (k : ℝ≥0) • Q (k - 1) n + Q k (n + 1)
      apply Seminorm.continuous_of_le (q := R) (((hQ k n).add
        ((hQ (k - 1) n).const_smul (k : ℝ≥0))).add (hQ k (n + 1)))
      intro f
      change SchwartzMap.seminorm ℂ k n (decayTwistCLM c f) ≤ R f
      refine (schwartz_seminorm_le_derivativeLp k n (decayTwistCLM c f)).trans ?_
      simp only [R, add_apply, smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_natCast]
      gcongr
      · exact hbound k n f
      · exact hbound (k - 1) n f
      · exact hbound k (n + 1) f
  exact ⟨hmem, P, ⟨htop⟩, hval⟩

/-- Lemma D.3.2.7(2). The symmetric exponential derivative norms generate
the decay topology for any unbounded sequence of positive exponents. -/
theorem exponentialDecayL2_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) 0 i.2) :=
  exponentialDecayL2_family (ι := ℕ × ℕ) (fun i ↦ a i.1) (fun _ ↦ 0) Prod.snd
    (fun i ↦ ha i.1) (fun _ ↦ le_rfl) (fun c ↦ by
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hunbounded (|c| + 1)
      exact ⟨a i, hi.le, fun j ↦ (i, j), fun j ↦ ⟨rfl, rfl, rfl⟩⟩)

/-- Lemma D.3.2.7(3). Including every nonnegative integer logarithmic weight
gives the same topology. -/
theorem exponentialDecayL2_log_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) i.2.1 i.2.2) :=
  exponentialDecayL2_family (ι := ℕ × ℕ × ℕ) (fun i ↦ a i.1) (fun i ↦ i.2.1) (fun i ↦ i.2.2)
    (fun i ↦ ha i.1) (fun _ ↦ Nat.cast_nonneg _) (fun c ↦ by
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hunbounded (|c| + 1)
      exact ⟨a i, hi.le, fun j ↦ (i, 0, j), fun _ ↦ ⟨rfl, by simp, rfl⟩⟩)

/-- The measure dt/t on the positive ray, considered as a measure on the real line. -/
def positiveRayHaar : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t ↦ ENNReal.ofReal t⁻¹)

theorem map_exp_volume_eq_positiveRayHaar :
    Measure.map Real.exp volume = positiveRayHaar := by
  ext S hS
  rw [Measure.map_apply Real.continuous_exp.measurable hS, positiveRayHaar,
    withDensity_apply _ hS, Measure.restrict_restrict hS]
  have he : Real.exp '' (Real.exp ⁻¹' S) = S ∩ Ioi 0 := by
    rw [image_preimage_eq_inter_range, Real.range_exp]
  rw [← he, lintegral_image_eq_lintegral_abs_deriv_mul
    (hS.preimage Real.continuous_exp.measurable)
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp [abs_of_nonneg (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The logarithmic L² expressions are the manuscript's Euler-derivative L²
expressions on the positive ray with respect to dt/t. -/
theorem exponentialDecayL2_eulerFormula (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ) :
    eLpNorm (exponentialDecayL2Integrand a b m f) 2 volume =
      eLpNorm (fun t : ℝ =>
        (((max t t⁻¹) ^ a * |Real.log t| ^ b : ℝ) : ℂ) *
          (eulerDerivative^[m] (fun y ↦ f.val (Real.log y))) t) 2 positiveRayHaar := by
  rw [← map_exp_volume_eq_positiveRayHaar, Real.isOpenEmbedding_exp.measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext x
  let φ (y : ℝ) := f.val (Real.log y)
  have hφ : ContDiffOn ℝ ∞ φ (Ioi 0) := (decayProfile_smooth f).contDiffOn.comp
    (Real.contDiffOn_log.mono (fun y hy ↦ (mem_Ioi.mp hy).ne')) (mapsTo_univ _ _)
  have hd := congrFun (eulerDerivative_iterate_comp_exp φ hφ m) x
  have hcomp : φ ∘ Real.exp = f.val := funext fun y ↦ by simp [φ]
  rw [hcomp] at hd
  have hmax : max (Real.exp x) (Real.exp x)⁻¹ = Real.exp |x| := by
    rw [← Real.exp_neg]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left (Real.exp_le_exp.mpr (by linarith))]
    · rw [abs_of_nonpos (le_of_not_ge hx), max_eq_right (Real.exp_le_exp.mpr (by linarith))]
  simp only [Function.comp_apply, φ] at hd
  simp only [exponentialDecayL2Integrand, Function.comp_apply, hmax, Real.log_exp, hd]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm a |x|]

end
end Masullo
