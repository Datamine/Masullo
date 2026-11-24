import MellinBergman
import MellinZeroExtension
import StrongDualBarrelled
import StrongDualNuclearPermanence

open Filter Function Set Topology
open scoped SchwartzMap ContDiff NNReal

noncomputable section

namespace Masullo

/-- The logarithmic decay space embeds into a product of nuclear Schwartz spaces. -/
theorem positiveRealExponentialDecay_nuclear.{v} (I : Set ℝ) (hI : I.Nonempty) :
    NuclearLocallyConvex.{v, 0} (PositiveRealExponentialDecay I) := by
  let L : PositiveRealExponentialDecay I →ₗ[ℂ] (I → 𝓢(ℝ, ℂ)) :=
    LinearMap.pi (logExponentialDecayTwist I)
  have hL : IsEmbedding L := positiveRealExponentialDecay_isEmbedding I hI
  let e := LinearEquiv.ofInjective L hL.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hL.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let A : PositiveRealExponentialDecay I ≃L[ℂ] L.range := ⟨e, h.continuous, h.symm.continuous⟩
  have hN : NuclearLocallyConvex.{v, 0} (I → 𝓢(ℝ, ℂ)) :=
    nuclearLocallyConvex_pi fun _ ↦ classicalSchwartz_nuclear ℝ
  exact nuclearLocallyConvex_of_equiv A.symm (nuclearLocallyConvex_submodule hN L.range)

/-- The decay space and its strong dual have the structure asserted in D.3.2.3(1)–(2). -/
theorem positiveRealExponentialDecay_structure (I : Set ℝ)
    (hI : OrdConnected I) (hne : I.Nonempty) :
    IsFrechetTVS (PositiveRealExponentialDecay I) ∧
    NuclearLocallyConvex.{0, 0} (PositiveRealExponentialDecay I) ∧
    MontelSpace ℂ (PositiveRealExponentialDecay I) ∧
    BarrelledSpace ℂ (PositiveRealExponentialDecay I) ∧
    CompleteSpace (StrongDual ℂ (PositiveRealExponentialDecay I)) ∧
    NuclearLocallyConvex.{0, 0} (StrongDual ℂ (PositiveRealExponentialDecay I)) ∧
    MontelSpace ℂ (StrongDual ℂ (PositiveRealExponentialDecay I)) ∧
    BarrelledSpace ℂ (StrongDual ℂ (PositiveRealExponentialDecay I)) := by
  let E := PositiveRealExponentialDecay I
  have hf := positiveRealExponentialDecay_frechet I hI hne
  have hn : NuclearLocallyConvex.{0, 0} E := positiveRealExponentialDecay_nuclear I hne
  letI : TopologicalSpace.MetrizableSpace E := hf.choose_spec.2.1
  letI : IsTopologicalAddGroup E := hf.choose
  letI : PolynormableSpace ℂ E := hf.choose_spec.1
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : BarrelledSpace ℂ E := isFrechetTVS_barrelled hf
  letI : CompleteSpace E :=
    IsUniformAddGroup.rightUniformSpace_eq (G := E) ▸ hf.choose_spec.2.2
  letI : CompleteSpace (StrongDual ℂ E) := inferInstance
  have hnD : NuclearLocallyConvex.{0, 0} (StrongDual ℂ E) := strongDual_nuclear_of_nuclear_frechet hf hn
  have hBD : BarrelledSpace ℂ (StrongDual ℂ E) := by
    apply strongDual_barrelled_of_bidually_surjective
    obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear (E := E) hn
    intro f
    obtain ⟨x, hx⟩ := e.surjective f
    exact ⟨x, ContinuousLinearMap.ext fun l ↦ (he x l).symm.trans (DFunLike.congr_fun hx l)⟩
  exact ⟨hf, hn,
    ⟨fun _ hs hb ↦ (nuclearLocallyConvex_totallyBounded hn hb).isCompact_of_isClosed hs⟩,
    inferInstance, inferInstance, hnD,
    ⟨fun _ hs hb ↦ (nuclearLocallyConvex_totallyBounded hnD hb).isCompact_of_isClosed hs⟩, hBD⟩

/-- D.3.2.3(3). The zero-exponent projection is the canonical inclusion into Schwartz space. -/
def positiveRealExponentialDecay_zeroInclusion (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    PositiveRealExponentialDecay I →L[ℂ] 𝓢(ℝ, ℂ) := by
  let a : I := ⟨0, h0⟩
  let M : PositiveRealExponentialDecay I → (I → 𝓢(ℝ, ℂ)) :=
    fun f b ↦ logExponentialDecayTwist I b f
  have hM : Continuous M := (positiveRealExponentialDecay_isEmbedding I ⟨0, h0⟩).continuous
  have ha : Continuous (fun p : I → 𝓢(ℝ, ℂ) ↦ p a) := continuous_apply a
  have h : Continuous (fun f : PositiveRealExponentialDecay I ↦ M f a) := ha.comp hM
  exact ⟨logExponentialDecayTwist I a, h⟩

theorem positiveRealExponentialDecay_zeroInclusion_apply (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (f : PositiveRealExponentialDecay I) (x : ℝ) :
    positiveRealExponentialDecay_zeroInclusion I h0 f x = f.val x := by
  change logExponentialDecayTwist I ⟨0, h0⟩ f x = _
  erw [logExponentialDecayTwist_apply]
  simp

theorem positiveRealExponentialDecay_zeroInclusion_injective (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    Injective (positiveRealExponentialDecay_zeroInclusion I h0) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have hx := congrArg (fun z : 𝓢(ℝ, ℂ) ↦ z x) hfg
  rwa [positiveRealExponentialDecay_zeroInclusion_apply, positiveRealExponentialDecay_zeroInclusion_apply] at hx

private def translationLinear (d : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  { toFun := fun f x ↦ f (x + d)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- Logarithmic translation acts continuously on the exponentially weighted
Schwartz space, with the scalar factor on each weighted profile. -/
def logExponentialDecayTranslation (I : Set ℝ) (hI : I.Nonempty) (d : ℝ) :
    PositiveRealExponentialDecay I →L[ℂ] PositiveRealExponentialDecay I := by
  let X := PositiveRealExponentialDecay I
  let S (a : I) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
    (Real.exp (-((a : ℝ) * d)) : ℂ) • SchwartzMap.compSubConstCLM ℂ (-d)
  have hS (a : I) (f : X) (x : ℝ) :
      S a (logExponentialDecayTwist I a f) x =
        logExponentialWeight a (translationLinear d f.val) x := by
    simp only [S, smul_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]
    erw [logExponentialDecayTwist_apply]
    change (Real.exp (-((a : ℝ) * d)) : ℂ) * ((Real.exp ((a : ℝ) * (x + d)) : ℂ) * f.val (x + d)) =
      (Real.exp ((a : ℝ) * x) : ℂ) * f.val (x + d)
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      show -((a : ℝ) * d) + (a : ℝ) * (x + d) = (a : ℝ) * x by ring]
  let T : X →ₗ[ℂ] X :=
    ((translationLinear d).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      (logExponentialDecaySubmodule I) fun f ↦ (Submodule.mem_iInf _).mpr fun a ↦
        ⟨S a (logExponentialDecayTwist I a f), funext (hS a f)⟩
  have hE := (positiveRealExponentialDecay_isEmbedding I hI).isInducing
  refine ⟨T, hE.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro a
  have h := (S a).continuous.comp ((continuous_apply a).comp hE.continuous)
  refine h.congr fun f ↦ SchwartzMap.ext fun x ↦ ?_
  erw [hS a f x, logExponentialDecayTwist_apply]
  rfl

@[simp] theorem logExponentialDecayTranslation_apply (I : Set ℝ) (hI : I.Nonempty)
    (d : ℝ) (f : PositiveRealExponentialDecay I) (x : ℝ) :
    (logExponentialDecayTranslation I hI d f).val x = f.val (x + d) := rfl

/-- The standard Mellin weight criterion and the logarithmic profile convention
used for the decay subspace describe exactly the same tests. -/
theorem logExponentialDecay_mem_iff_mellinSchwartzAt (I : Set ℝ) (f : ℝ → ℂ) :
    f ∈ logExponentialDecaySubmodule I ↔
      ∀ a ∈ I, MellinSchwartzAt (f ∘ Real.log) a := by
  rw [logExponentialDecaySubmodule, Submodule.mem_iInf]
  constructor
  · intro hf a ha
    obtain ⟨g, hg⟩ := hf ⟨a, ha⟩
    refine ⟨logarithmicSchwartzReflection g, ?_⟩
    funext x
    have hx := congrFun hg (-x)
    change g (-x) = (Real.exp (a * -x) : ℂ) * f (-x) at hx
    simpa [Function.comp_def, Real.log_exp, Complex.real_smul, mul_neg, neg_mul] using hx
  · intro hf a
    obtain ⟨g, hg⟩ := hf a.val a.property
    refine ⟨logarithmicSchwartzReflection g, ?_⟩
    funext x
    have hx := congrFun hg (-x)
    change g (-x) = Real.exp (-a.val * -x) • f (Real.log (Real.exp (- -x))) at hx
    exact (by simpa [realSchwartzCoe, logExponentialWeight, LinearMap.mulLeft,
      Complex.real_smul, Real.log_exp] using hx)

/-- Uniform half-line form of rapid exponential decay of all logarithmic derivatives. -/
def logDerivativesRapidOn (ε : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 0 ≤ ε * x → ‖iteratedDeriv n f x‖ ≤ C * Real.exp (-a * (ε * x))

private def twistCoefficient (t : ℝ) (n i : ℕ) : ℝ :=
  (n.choose i : ℝ) * ‖t‖ ^ i

private theorem twistCoefficient_nonneg (t : ℝ) (n i : ℕ) : 0 ≤ twistCoefficient t n i := by
  unfold twistCoefficient
  positivity

private theorem norm_twisted_iteratedDeriv_le (t x : ℝ) (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    ‖iteratedDeriv n ((fun y ↦ Real.exp (t * y)) • f) x‖ ≤
      Real.exp (t * x) *
        ∑ i ∈ Finset.range (n + 1), twistCoefficient t n i * ‖iteratedDeriv (n - i) f x‖ := by
  have h_exp : ContDiff ℝ n (fun y : ℝ ↦ Real.exp (t * y)) := by fun_prop
  have h_f : ContDiff ℝ n f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hD := iteratedDerivWithin_smul (Set.mem_univ x) uniqueDiffOn_univ
    h_exp.contDiffAt.contDiffWithinAt h_f.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, iteratedDeriv_exp_const_mul] at hD
  rw [hD, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul, norm_smul, norm_mul,
    Real.norm_of_nonneg (Real.exp_nonneg _), norm_pow]
  unfold twistCoefficient
  ring_nf
  rfl

private theorem logExponentialWeight_eq_smul (a : ℝ) (f : ℝ → ℂ) :
    logExponentialWeight a f = (fun x : ℝ ↦ Real.exp (a * x)) • f := by
  funext x
  exact Complex.real_smul.symm

/-- A fixed exponential weight can be tested on the polynomially weighted
derivatives of the original profile. -/
theorem logExponentialWeight_mem_range_iff (a : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    logExponentialWeight a f ∈ realSchwartzCoe.range ↔
      ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
        |x| ^ k * ‖iteratedDeriv n f x‖ ≤ C * Real.exp (-(a * x)) := by
  constructor
  · rintro ⟨g, hg⟩ k n
    have he : f = (fun x ↦ Real.exp (-a * x)) • ⇑g := by
      funext x
      have hx := congrFun hg x
      change g x = (Real.exp (a * x) : ℂ) * f x at hx
      change f x = Real.exp (-a * x) • g x
      rw [Complex.real_smul, hx, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
        neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    let C := ∑ i ∈ Finset.range (n + 1),
      twistCoefficient (-a) n i * SchwartzMap.seminorm ℂ k (n - i) g
    refine ⟨C, Finset.sum_nonneg (fun i _ ↦
      mul_nonneg (twistCoefficient_nonneg ..) (apply_nonneg _ _)), fun x ↦ ?_⟩
    conv_lhs => rw [he]
    refine (mul_le_mul_of_nonneg_left (norm_twisted_iteratedDeriv_le (-a) x n (g.smooth ⊤))
      (pow_nonneg (abs_nonneg x) _)).trans ?_
    rw [mul_left_comm, mul_comm C, ← neg_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (g.le_seminorm' ℂ k (n - i) x)
      (twistCoefficient_nonneg ..)
  · intro h
    rw [logExponentialWeight_eq_smul]
    have ha : ContDiff ℝ ∞ (fun x : ℝ ↦ Real.exp (a * x)) := by fun_prop
    refine ⟨⟨_, ha.smul hf, ?_⟩, rfl⟩
    intro k n
    choose C hC hbound using h k
    refine ⟨∑ i ∈ Finset.range (n + 1), twistCoefficient a n i * C (n - i), fun x ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    refine (mul_le_mul_of_nonneg_left (norm_twisted_iteratedDeriv_le a x n hf)
      (pow_nonneg (abs_nonneg x) _)).trans ?_
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = twistCoefficient a n i * (Real.exp (a * x) *
          (|x| ^ k * ‖iteratedDeriv (n - i) f x‖)) := by ring
      _ ≤ twistCoefficient a n i * (Real.exp (a * x) *
          (C (n - i) * Real.exp (-(a * x)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbound _ _) (Real.exp_nonneg _))
          (twistCoefficient_nonneg ..)
      _ = _ := by
        rw [mul_left_comm (Real.exp (a * x)), ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]

private theorem logExponentialDecay_implies_logDerivativesRapid (ε : ℝ) {f : ℝ → ℂ}
    (hf : ∀ a ≥ 0, logExponentialWeight (ε * a) f ∈ realSchwartzCoe.range) :
    logDerivativesRapidOn ε f := by
  intro n a ha
  obtain ⟨g, hg⟩ := hf a ha.le
  let t := -(ε * a)
  have he : f = (fun x ↦ Real.exp (t * x)) • ⇑g := by
    funext x
    have hx := congrFun hg x
    change g x = (Real.exp ((ε * a) * x) : ℂ) * f x at hx
    change f x = Real.exp (t * x) • g x
    rw [Complex.real_smul, hx, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have hz : t * x + (ε * a) * x = 0 := by dsimp [t]; ring
    rw [hz, Real.exp_zero, Complex.ofReal_one, one_mul]
  let C := ∑ i ∈ Finset.range (n + 1),
    twistCoefficient t n i * SchwartzMap.seminorm ℂ 0 (n - i) g
  refine ⟨C, Finset.sum_nonneg (fun i _ ↦
    mul_nonneg (twistCoefficient_nonneg ..) (apply_nonneg _ _)), fun x _ ↦ ?_⟩
  have h := norm_twisted_iteratedDeriv_le t x n (g.smooth ⊤)
  conv_lhs => rw [he]
  refine h.trans ?_
  rw [show t * x = -a * (ε * x) by dsimp [t]; ring, mul_comm C]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (by simpa using g.le_seminorm' ℂ 0 (n - i) x)
    (twistCoefficient_nonneg ..)

private theorem logDerivativesRapid_implies_logExponentialDecay (ε : ℝ)
    (hε : |ε| = 1) {f : ℝ → ℂ} (h0 : f ∈ realSchwartzCoe.range)
    (h : logDerivativesRapidOn ε f) :
    ∀ a ≥ 0, logExponentialWeight (ε * a) f ∈ realSchwartzCoe.range := by
  obtain ⟨g, hg⟩ := h0
  change ⇑g = f at hg
  subst f
  intro a ha
  let t := ε * a
  have ht : ContDiff ℝ ∞ (fun x : ℝ ↦ Real.exp (t * x)) := by fun_prop
  rw [logExponentialWeight_eq_smul]
  refine ⟨⟨_, ht.smul (g.smooth ⊤), ?_⟩, rfl⟩
  intro k n
  choose C hC₀ hC using fun m : ℕ ↦ h m (a + 1) (by linarith)
  let B (i : ℕ) := SchwartzMap.seminorm ℂ k (n - i) g + C (n - i) * (k.factorial : ℝ)
  refine ⟨∑ i ∈ Finset.range (n + 1), twistCoefficient t n i * B i, fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left (norm_twisted_iteratedDeriv_le t x n (g.smooth ⊤))
    (pow_nonneg (abs_nonneg x) _)).trans ?_
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [show |x| ^ k * Real.exp (t * x) *
      (twistCoefficient t n i * ‖iteratedDeriv (n - i) (⇑g) x‖) =
    twistCoefficient t n i * (|x| ^ k * Real.exp (t * x) *
      ‖iteratedDeriv (n - i) (⇑g) x‖) by ring]
  apply mul_le_mul_of_nonneg_left _ (twistCoefficient_nonneg ..)
  by_cases hx : 0 ≤ ε * x
  · have hxa : |x| = ε * x := by
      rw [← abs_of_nonneg hx, abs_mul, hε, one_mul]
    have hpow : |x| ^ k * Real.exp (-(ε * x)) ≤ (k.factorial : ℝ) := by
      rw [hxa, Real.exp_neg, ← div_eq_mul_inv]
      have hp := (div_le_iff₀ (by positivity : 0 < (k.factorial : ℝ))).mp
        (Real.pow_div_factorial_le_exp (ε * x) hx k)
      exact (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hp)
    calc
      _ ≤ |x| ^ k * Real.exp (t * x) *
          (C (n - i) * Real.exp (-(a + 1) * (ε * x))) :=
        mul_le_mul_of_nonneg_left (hC (n - i) x hx) (by positivity)
      _ = C (n - i) * (|x| ^ k * Real.exp (-(ε * x))) := by
        rw [show |x| ^ k * Real.exp (t * x) *
            (C (n - i) * Real.exp (-(a + 1) * (ε * x))) =
          C (n - i) * (|x| ^ k * (Real.exp (t * x) * Real.exp (-(a + 1) * (ε * x)))) by ring]
        rw [← Real.exp_add, show t * x + -(a + 1) * (ε * x) = -(ε * x) by dsimp [t]; ring]
      _ ≤ C (n - i) * (k.factorial : ℝ) := mul_le_mul_of_nonneg_left hpow (hC₀ _)
      _ ≤ B i := le_add_of_nonneg_left (apply_nonneg _ _)
  · have ht₀ : t * x ≤ 0 := by
      rw [show t * x = a * (ε * x) by dsimp [t]; ring]
      exact mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hx)
    calc
      _ = Real.exp (t * x) * (|x| ^ k * ‖iteratedDeriv (n - i) (⇑g) x‖) := by ring
      _ ≤ |x| ^ k * ‖iteratedDeriv (n - i) (⇑g) x‖ :=
        mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr ht₀)
      _ ≤ SchwartzMap.seminorm ℂ k (n - i) g := g.le_seminorm' ℂ k (n - i) x
      _ ≤ B i := le_add_of_nonneg_right (mul_nonneg (hC₀ _) (by positivity))

/-- The uniform bounds on a half-line are equivalent to little-o decay
toward that end for every positive exponent. -/
theorem logDerivativesRapidOn_iff_eventual (ε : ℝ) (hε : |ε| = 1) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    logDerivativesRapidOn ε f ↔
      ∀ (n : ℕ) (a : ℝ), 0 < a → ∀ δ : ℝ, 0 < δ → ∃ R : ℝ,
        ∀ x : ℝ, R ≤ ε * x → ‖iteratedDeriv n f x‖ ≤ δ * Real.exp (-a * (ε * x)) := by
  constructor
  · intro h n a ha δ hδ
    obtain ⟨C, hC, hbound⟩ := h n (a + 1) (by linarith)
    refine ⟨max 0 (Real.log ((C + 1) / δ)), fun x hx ↦ ?_⟩
    have hz := (le_max_left ..).trans hx
    have hlog := (le_max_right ..).trans hx
    have hE := (Real.log_le_iff_le_exp (show 0 < (C + 1) / δ by positivity)).mp hlog
    have hCexp : C * Real.exp (-(ε * x)) ≤ δ := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      exact (le_add_of_nonneg_right zero_le_one).trans (by
        simpa only [mul_comm δ] using (div_le_iff₀ hδ).mp hE)
    calc
      _ ≤ C * Real.exp (-(a + 1) * (ε * x)) := hbound x hz
      _ = (C * Real.exp (-(ε * x))) * Real.exp (-a * (ε * x)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCexp (Real.exp_nonneg _)
  · intro h n a ha
    obtain ⟨R, hbound⟩ := h n a ha 1 zero_lt_one
    let q (x : ℝ) := ‖iteratedDeriv n f x‖ * Real.exp (a * (ε * x))
    have hD := hf.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)
    have hq : Continuous q := hD.norm.mul (by fun_prop)
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -|R|) (b := |R|)).bddAbove_image hq.continuousOn
    refine ⟨max 1 B, zero_le_one.trans (le_max_left ..), fun x hx ↦ ?_⟩
    by_cases hR : R ≤ ε * x
    · exact (hbound x hR).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_nonneg _))
    · have hxR : x ∈ Icc (-|R|) |R| := by
        apply abs_le.mp
        calc
          |x| = ε * x := by rw [← abs_of_nonneg hx, abs_mul, hε, one_mul]
          _ ≤ R := le_of_not_ge hR
          _ ≤ |R| := le_abs_self _
      have hqB : q x ≤ B := hB (mem_image_of_mem q hxR)
      rw [show -a * (ε * x) = -(a * (ε * x)) by ring, Real.exp_neg, ← div_eq_mul_inv,
        le_div_iff₀ (Real.exp_pos _)]
      exact hqB.trans (le_max_right ..)

private theorem logExponentialDecay_direction_iff (ε : ℝ) (hε : |ε| = 1) (f : ℝ → ℂ) :
    (∀ a ≥ 0, logExponentialWeight (ε * a) f ∈ realSchwartzCoe.range) ↔
      f ∈ realSchwartzCoe.range ∧ logDerivativesRapidOn ε f := by
  constructor
  · intro h
    refine ⟨?_, logExponentialDecay_implies_logDerivativesRapid ε h⟩
    simpa only [mul_zero, logExponentialWeight_zero] using h 0 le_rfl
  · exact fun h ↦ logDerivativesRapid_implies_logExponentialDecay ε hε h.1 h.2

/-- D.3.2.3(4). Nonnegative exponents select forward semi-exponential tests. -/
theorem logExponentialDecay_mem_iff_forward (f : ℝ → ℂ) :
    f ∈ logExponentialDecaySubmodule (Ici 0) ↔
      f ∈ realSchwartzCoe.range ∧ logDerivativesRapidOn 1 f := by
  rw [← logExponentialDecay_direction_iff 1 (by norm_num) f]
  simp only [logExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap, one_mul]
  exact ⟨fun h a ha ↦ h ⟨a, ha⟩, fun h a ↦ h a.val a.property⟩

/-- D.3.2.3(5). Nonpositive exponents select backward semi-exponential tests. -/
theorem logExponentialDecay_mem_iff_backward (f : ℝ → ℂ) :
    f ∈ logExponentialDecaySubmodule (Iic 0) ↔
      f ∈ realSchwartzCoe.range ∧ logDerivativesRapidOn (-1) f := by
  rw [← logExponentialDecay_direction_iff (-1) (by norm_num) f]
  simp only [logExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap, neg_one_mul]
  exact ⟨fun h a ha ↦ h ⟨-a, neg_nonpos.mpr ha⟩,
    fun h a ↦ by simpa only [neg_neg] using h (-a.val) (neg_nonneg.mpr a.property)⟩

/-- D.3.2.3(6). All real exponents select tests with two-sided exponential decay. -/
theorem logExponentialDecay_mem_iff_twoSided (f : ℝ → ℂ) :
    f ∈ logExponentialDecaySubmodule univ ↔
      f ∈ realSchwartzCoe.range ∧ logDerivativesRapidOn 1 f ∧ logDerivativesRapidOn (-1) f := by
  have h : f ∈ logExponentialDecaySubmodule univ ↔
      f ∈ logExponentialDecaySubmodule (Ici 0) ∧ f ∈ logExponentialDecaySubmodule (Iic 0) := by
    simp only [logExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap]
    constructor
    · exact fun h ↦ ⟨fun a ↦ h ⟨a.val, mem_univ _⟩, fun a ↦ h ⟨a.val, mem_univ _⟩⟩
    · intro h a
      rcases le_total 0 a.val with ha | ha
      · exact h.1 ⟨a.val, ha⟩
      · exact h.2 ⟨a.val, ha⟩
  rw [h, logExponentialDecay_mem_iff_forward, logExponentialDecay_mem_iff_backward]
  exact ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2.2⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩⟩

/-- The two oriented bounds combine into decay in absolute logarithmic distance. -/
theorem logDerivativesRapid_twoSided_iff (f : ℝ → ℂ) :
    (logDerivativesRapidOn 1 f ∧ logDerivativesRapidOn (-1) f) ↔
      ∀ (n : ℕ) (a : ℝ), 0 < a → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x : ℝ, ‖iteratedDeriv n f x‖ ≤ C * Real.exp (-a * |x|) := by
  constructor
  · intro h n a ha
    obtain ⟨P, hP, hp⟩ := h.1 n a ha
    obtain ⟨N, _, hn⟩ := h.2 n a ha
    refine ⟨max P N, hP.trans (le_max_left ..), fun x ↦ ?_⟩
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      exact (by simpa only [one_mul] using hp x (by simpa only [one_mul] using hx) :
        ‖iteratedDeriv n f x‖ ≤ P * Real.exp (-a * x)).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_nonneg _))
    · rw [abs_of_nonpos (le_of_not_ge hx)]
      exact (by simpa only [neg_one_mul] using hn x (by simp [le_of_not_ge hx]) :
        ‖iteratedDeriv n f x‖ ≤ N * Real.exp (-a * -x)).trans
        (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_nonneg _))
  · intro h
    have bound (ε : ℝ) (hε : |ε| = 1) : logDerivativesRapidOn ε f := by
      intro n a ha
      obtain ⟨C, hC, hbound⟩ := h n a ha
      refine ⟨C, hC, fun x hx ↦ ?_⟩
      have heq : |x| = ε * x := by rw [← abs_of_nonneg hx, abs_mul, hε, one_mul]
      simpa only [heq] using hbound x
    exact ⟨bound 1 (by norm_num), bound (-1) (by norm_num)⟩

/-- A single Schwartz seminorm bounds the evaluations of one weighted
radial profile. Those evaluations separate all radial decay tests. -/
theorem exists_bounded_radialEvaluations (I : Set ℝ) (b : I) :
    ∃ (p : Seminorm ℂ (PositiveRealExponentialDecay I))
      (e : ℝ → PositiveRealExponentialDecay I →L[ℂ] ℂ),
      Continuous p ∧ (∀ x f, ‖e x f‖ ≤ p f) ∧ Injective (fun f x => e x f) := by
  let R := PositiveRealExponentialDecay I
  let T : R →ₗ[ℂ] 𝓢(ℝ, ℂ) := logExponentialDecayTwist I b
  have hT : Continuous T := (continuous_apply b).comp
    (positiveRealExponentialDecay_isEmbedding I ⟨b, b.property⟩).continuous
  let p : Seminorm ℂ R := (SchwartzMap.seminorm ℂ 0 0).comp T
  let e (x : ℝ) : R →L[ℂ] ℂ :=
    ⟨{ toFun := fun f => T f x
       map_add' := fun f g => by rw [T.map_add]; rfl
       map_smul' := fun c f => by rw [T.map_smul]; rfl },
      ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous).comp hT⟩
  refine ⟨p, e, ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 0)).comp hT,
    fun x f => SchwartzMap.norm_le_seminorm ℂ (T f) x, ?_⟩
  intro f g h
  apply Subtype.ext
  funext x
  have hf : T f x = (Real.exp ((b : ℝ) * x) : ℂ) * f.val x :=
    logExponentialDecayTwist_apply I b f x
  have hg : T g x = (Real.exp ((b : ℝ) * x) : ℂ) * g.val x :=
    logExponentialDecayTwist_apply I b g x
  have hx : T f x = T g x := congrFun h x
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    (hf.symm.trans (hx.trans hg))

end Masullo
