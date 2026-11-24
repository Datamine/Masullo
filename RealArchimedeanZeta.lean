import MellinTaylorContinuation
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Asymptotics Filter MeasureTheory Set
open scoped ContDiff SchwartzMap Topology
open Metric

namespace Masullo

noncomputable section

private abbrev Tests := 𝓢(ℝ, ℂ)

private def realZetaReflect : Tests →L[ℂ] Tests :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv

/-- Folding a real local test by the unitary sign character of parity `a`. -/
def realZetaProfile (a : ℕ) (f : Tests) : Tests :=
  f + ((-1 : ℂ) ^ a) • realZetaReflect f

@[simp] theorem realZetaProfile_apply (a : ℕ) (f : Tests) (t : ℝ) :
    realZetaProfile a f t = f t + (-1 : ℂ) ^ a * f (-t) := rfl

/-- Real-place zeta in the normalized real coordinate, with measure
`dx / |x|` absorbed into the power of the absolute value. -/
def realArchimedeanZetaIntegrand (a : ℕ) (f : Tests) (s : ℂ) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (s - 1) * (if x < 0 then (-1 : ℂ) ^ a else 1) * f x

def realArchimedeanZetaIntegral (a : ℕ) (f : Tests) (s : ℂ) : ℂ :=
  ∫ x, realArchimedeanZetaIntegrand a f s x

def realArchimedeanZetaContinued (a : ℕ) (f : Tests) (s : ℂ) : ℂ :=
  mellinTaylorContinued (realZetaProfile a f) s

/-- The real-place continuation evaluated at a fixed parameter is a tempered distribution. -/
def realArchimedeanZetaContinuedCLM (a : ℕ) (s : ℂ) : Tests →L[ℂ] ℂ :=
  (schwartzMellinContinuedCLM s).comp
    (ContinuousLinearMap.id ℂ Tests + ((-1 : ℂ) ^ a) • realZetaReflect)

@[simp] theorem realArchimedeanZetaContinuedCLM_apply (a : ℕ) (s : ℂ) (f : Tests) :
    realArchimedeanZetaContinuedCLM a s f = realArchimedeanZetaContinued a f s :=
  schwartzMellinContinuedCLM_apply s (realZetaProfile a f)

/-- The continued real-place zeta function agrees with the absolutely
convergent integral in the original right half-plane. -/
theorem realArchimedeanZetaContinued_eq_integral (a : ℕ) (f : Tests) {s : ℂ} (hs : 0 < s.re) :
    Integrable (realArchimedeanZetaIntegrand a f s) ∧
      realArchimedeanZetaContinued a f s = realArchimedeanZetaIntegral a f s := by
  let F₀ (x : ℝ) := (x : ℂ) ^ (s - 1) * f x
  let F₁ (x : ℝ) := (x : ℂ) ^ (s - 1) * ((-1 : ℂ) ^ a * f (-x))
  let G := realArchimedeanZetaIntegrand a f s
  have h₀ : IntegrableOn F₀ (Ioi 0) := by
    have h := (mellinTaylorContinued_eq_mellin f.smooth' (schwartz_radial_rapid f) hs).1
    exact h
  have h₁ : IntegrableOn F₁ (Ioi 0) := by
    let g := (-1 : ℂ) ^ a • realZetaReflect f
    have h := (mellinTaylorContinued_eq_mellin g.smooth' (schwartz_radial_rapid g) hs).1
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • g t) (Ioi 0) at h
    exact h
  have hpos : EqOn G F₀ (Ioi 0) := by
    intro x hx
    have hx' : 0 < x := hx
    simp [G, F₀, realArchimedeanZetaIntegrand, abs_of_pos hx', not_lt_of_ge hx'.le]
  have hneg : EqOn (fun x => G (-x)) F₁ (Ioi 0) := by
    intro x hx
    have hx' : 0 < x := hx
    simp [G, F₁, realArchimedeanZetaIntegrand, abs_of_pos hx', hx', mul_assoc]
  have hGi : IntegrableOn G (Ioi 0) := h₀.congr_fun hpos.symm measurableSet_Ioi
  have hGn : IntegrableOn G (Iio 0) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding (f := G) (s := Iio (0 : ℝ))
    apply h.mp
    have he : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by ext; simp
    rw [he]
    exact h₁.congr_fun hneg.symm measurableSet_Ioi
  have hGic : IntegrableOn G (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hGn
  have hGall : Integrable G := by
    have h := hGi.union hGic
    rwa [← compl_Ioi, union_compl_self, integrableOn_univ] at h
  refine ⟨hGall, ?_⟩
  have hmain : mellin (realZetaProfile a f : ℝ → ℂ) s =
      mellinTaylorContinued (realZetaProfile a f : ℝ → ℂ) s :=
    (mellinTaylorContinued_eq_mellin (realZetaProfile a f).smooth'
      (schwartz_radial_rapid (realZetaProfile a f)) hs).2
  rw [realArchimedeanZetaContinued, ← hmain, realArchimedeanZetaIntegral,
    ← integral_add_compl measurableSet_Ioi hGall, compl_Ioi, ← integral_comp_neg_Ioi 0 G, neg_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpos, setIntegral_congr_fun measurableSet_Ioi hneg,
    ← integral_add h₀ h₁]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp [F₀, F₁, smul_eq_mul, mul_add]

theorem realArchimedeanZetaContinued_meromorphic (a : ℕ) (f : Tests) :
    Meromorphic (realArchimedeanZetaContinued a f) :=
  mellinTaylorContinued_meromorphic (realZetaProfile a f).smooth' (schwartz_radial_rapid _)

theorem realArchimedeanZetaContinued_analyticAt (a : ℕ) (f : Tests) {s : ℂ}
    (hs : ∀ k : ℕ, s + k ≠ 0) : AnalyticAt ℂ (realArchimedeanZetaContinued a f) s :=
  mellinTaylorContinued_analyticAt (realZetaProfile a f).smooth' (schwartz_radial_rapid _) hs

theorem realZetaProfile_taylorCoeff (a k : ℕ) (f : Tests) :
    mellinTaylorCoeff (realZetaProfile a f) k =
      (1 + (-1 : ℂ) ^ (a + k)) * ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) := by
  have hf : ContDiff ℝ k (f : ℝ → ℂ) := f.smooth k
  have hg : ContDiff ℝ k (fun t : ℝ => (-1 : ℂ) ^ a • f (-t)) :=
    (hf.comp contDiff_neg).const_smul _
  simp only [mellinTaylorCoeff]
  change (k.factorial : ℂ)⁻¹ * iteratedDeriv k
    (fun t : ℝ => f t + (-1 : ℂ) ^ a • f (-t)) 0 = _
  rw [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,
    iteratedDeriv_fun_const_smul_field, iteratedDeriv_comp_neg]
  simp only [neg_zero, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    smul_eq_mul, pow_add]
  ring

/-- Real-place residue in ordinary derivative coordinates. The sign projection
cancels the coefficient when the character and derivative have opposite parity. -/
theorem realArchimedeanZetaContinued_residue (a k : ℕ) (f : Tests) :
    Tendsto (fun z => (z + k) * realArchimedeanZetaContinued a f z) (𝓝[≠] (-(k : ℂ)))
      (𝓝 ((1 + (-1 : ℂ) ^ (a + k)) * ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0))) := by
  rw [← realZetaProfile_taylorCoeff]
  exact mellinTaylorContinued_residue (realZetaProfile a f).smooth' (schwartz_radial_rapid _) k

theorem realArchimedeanZetaContinued_order (a k : ℕ) (f : Tests) :
    if (1 + (-1 : ℂ) ^ (a + k)) * ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) = 0 then
      AnalyticAt ℂ (realArchimedeanZetaContinued a f) (-(k : ℂ))
    else meromorphicOrderAt (realArchimedeanZetaContinued a f) (-(k : ℂ)) = (-1 : ℤ) := by
  rw [← realZetaProfile_taylorCoeff]
  exact mellinTaylorContinued_order (realZetaProfile a f).smooth' (schwartz_radial_rapid _) k

private def realZetaIteratedDeriv : ℕ → Tests →L[ℂ] Tests
  | 0 => ContinuousLinearMap.id ℂ Tests
  | k + 1 => (SchwartzMap.derivCLM ℂ ℂ).comp (realZetaIteratedDeriv k)

private theorem realZetaIteratedDeriv_apply (k : ℕ) (f : Tests) :
    (realZetaIteratedDeriv k f : ℝ → ℂ) = iteratedDeriv k f := by
  induction k with
  | zero => simp [realZetaIteratedDeriv]
  | succ k ih =>
    rw [iteratedDeriv_succ, ← ih]
    funext x
    exact SchwartzMap.derivCLM_apply ℂ (realZetaIteratedDeriv k f) x

/-- The real-place residue, as a continuous linear functional on tests. -/
def realArchimedeanZetaResidue (a k : ℕ) : Tests →L[ℂ] ℂ :=
  ((1 + (-1 : ℂ) ^ (a + k)) * (k.factorial : ℂ)⁻¹) •
    (((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).comp (realZetaIteratedDeriv k))

@[simp] theorem realArchimedeanZetaResidue_apply (a k : ℕ) (f : Tests) :
    realArchimedeanZetaResidue a k f =
      (1 + (-1 : ℂ) ^ (a + k)) * ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) := by
  change ((1 + (-1 : ℂ) ^ (a + k)) * (k.factorial : ℂ)⁻¹) *
      realZetaIteratedDeriv k f 0 = _
  rw [show realZetaIteratedDeriv k f 0 = iteratedDeriv k f 0 from
    congrFun (realZetaIteratedDeriv_apply k f) 0, mul_assoc]

/-- The distribution (D^kδ_0), with (D=(2πi)^{-1}∂), in the real coordinate. -/
def realZetaDeltaDerivative (k : ℕ) : Tests →L[ℂ] ℂ :=
  archimedeanDeltaDerivativeScale k •
    (((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).comp (realZetaIteratedDeriv k))

private theorem realZetaDeltaDerivative_apply (k : ℕ) (f : Tests) :
    realZetaDeltaDerivative k f = archimedeanDeltaDerivativeScale k * iteratedDeriv k f 0 := by
  change archimedeanDeltaDerivativeScale k * realZetaIteratedDeriv k f 0 = _
  rw [show realZetaIteratedDeriv k f 0 = iteratedDeriv k f 0 from
    congrFun (realZetaIteratedDeriv_apply k f) 0]

private theorem realArchimedeanZetaResidue_eq_scaledDelta (a k : ℕ) (h : Even (a + k)) :
    realArchimedeanZetaResidue a k =
      (2 * (2 * (Real.pi : ℂ)) ^ k * (-Complex.I) ^ k / (k.factorial : ℂ)) •
        realZetaDeltaDerivative k := by
  ext f
  rw [realArchimedeanZetaResidue_apply, h.neg_one_pow, smul_apply, realZetaDeltaDerivative_apply,
    smul_eq_mul, div_eq_mul_inv]
  calc
    _ = 2 * ((k.factorial : ℂ)⁻¹ * (1 * iteratedDeriv k f 0)) := by norm_num
    _ = _ := by rw [← archimedeanDeltaDerivativeScale_cancel k]; ring

/-- The two printed real constants in (3.3.2.7), with (m=2n). -/
theorem realArchimedeanZetaResidue_printed (n : ℕ) :
    realArchimedeanZetaResidue 0 (2 * n) =
      ((2 : ℂ) ^ (2 * n + 1) * (Real.pi : ℂ) ^ (2 * n) * (-1 : ℂ) ^ n /
        ((2 * n).factorial : ℂ)) • realZetaDeltaDerivative (2 * n) ∧
    realArchimedeanZetaResidue 1 (2 * n + 1) =
      ((-Complex.I) * (2 : ℂ) ^ (2 * n + 2) * (Real.pi : ℂ) ^ (2 * n + 1) * (-1 : ℂ) ^ n /
        ((2 * n + 1).factorial : ℂ)) • realZetaDeltaDerivative (2 * n + 1) := by
  have h₀ : Even (0 + 2 * n) := ⟨n, by omega⟩
  have h₁ : Even (1 + (2 * n + 1)) := ⟨n + 1, by omega⟩
  constructor
  · rw [realArchimedeanZetaResidue_eq_scaledDelta 0 _ h₀, archimedean_negativeI_even, mul_pow]
    congr 1
    rw [pow_succ (2 : ℂ) (2 * n)]
    ring
  · rw [realArchimedeanZetaResidue_eq_scaledDelta 1 _ h₁, pow_succ (-Complex.I),
      archimedean_negativeI_even, mul_pow]
    congr 1
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ (2 : ℂ) (2 * n + 1)]
    ring

/-- Prescribe a single ordinary Taylor jet with a compactly supported Schwartz test. -/
theorem exists_realZetaSchwartz_factorialJet (k : ℕ) :
    ∃ f : Tests, iteratedDeriv k f 0 = (k.factorial : ℂ) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by positivity, by norm_num⟩
  let u (x : ℝ) := b x * x ^ k
  let g (x : ℝ) : ℂ := (u x : ℂ)
  have hgc : HasCompactSupport g :=
    (b.hasCompactSupport.mul_right (f' := fun x : ℝ => x ^ k)).comp_left Complex.ofReal_zero
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp (b.contDiff.mul (contDiff_id.pow _))
  refine ⟨hgc.toSchwartzMap hg, ?_⟩
  change iteratedDeriv k g 0 = (k.factorial : ℂ)
  have he : g =ᶠ[𝓝 0] (fun x : ℝ => ((x ^ k : ℝ) : ℂ)) := by
    filter_upwards [b.eventuallyEq_one] with x hx
    change b x = (1 : ℝ) at hx
    simp only [g, u, hx, one_mul]
  rw [he.iteratedDeriv_eq k, iteratedDeriv_complex_ofReal k (h := fun x : ℝ => x ^ k) (contDiff_id.pow _)]
  simp [Nat.descFactorial_self]

/-- Every matching-parity pole is a genuine pole of the real-place family.
The residue normalization is two on the selected test. -/
theorem realArchimedeanZetaContinued_hasPole (a k : ℕ) (hparity : Even (a + k)) :
    ∃ f : Tests, realArchimedeanZetaResidue a k f = 2 ∧
      meromorphicOrderAt (realArchimedeanZetaContinued a f) (-(k : ℂ)) = (-1 : ℤ) := by
  obtain ⟨f, hf⟩ := exists_realZetaSchwartz_factorialJet k
  have hn : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hval : (1 + (-1 : ℂ) ^ (a + k)) * ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) = 2 := by
    rw [hparity.neg_one_pow, hf, inv_mul_cancel₀ hn, mul_one]
    norm_num
  refine ⟨f, (realArchimedeanZetaResidue_apply a k f).trans hval, ?_⟩
  simpa only [hval, OfNat.ofNat_ne_zero, ↓reduceIte] using realArchimedeanZetaContinued_order a k f

/-- The opposite-parity points are removable for every real-place test. -/
theorem realArchimedeanZetaContinued_oppositeParity (a k : ℕ) (f : Tests) (hparity : Odd (a + k)) :
    AnalyticAt ℂ (realArchimedeanZetaContinued a f) (-(k : ℂ)) := by
  simpa only [hparity.neg_one_pow, add_neg_cancel, zero_mul, ite_true] using
    realArchimedeanZetaContinued_order a k f


/-- On the odd real component the pole character is (x^{-1}|x|^{-2n}), as
in (3.3.2.3). The even component uses the absolute-value power alone. -/
theorem real_tamagawa_oddPoleCharacter (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    ((|x| : ℝ) : ℂ) ^ (-((2*n+1 : ℕ) : ℂ)) * (if x < 0 then -1 else 1) =
      (x : ℂ)⁻¹ * ((|x| : ℝ) : ℂ) ^ (-((2*n : ℕ) : ℂ)) := by
  have hN : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
  rw [show -((2*n+1 : ℕ) : ℂ) = -((2*n : ℕ) : ℂ) + (-1) by push_cast; ring,
    Complex.cpow_add _ _ hN, Complex.cpow_neg_one]
  by_cases h : x < 0
  · simp only [ite_eq_left h, abs_of_neg h, Complex.ofReal_neg, inv_neg]
    ring
  · rw [ite_eq_right h, abs_of_nonneg (le_of_not_gt h), mul_one, mul_comm]

/-- A real distribution-valued pole occurs exactly at the parity-selected
negative integers, and a test witnesses order minus one at each of them. -/
theorem realArchimedeanZetaContinued_hasPole_iff (a : ℕ) (c : ℂ) :
    (∃ f : Tests, meromorphicOrderAt (realArchimedeanZetaContinued a f) c = (-1 : ℤ)) ↔
      ∃ k : ℕ, c = -(k : ℂ) ∧ Even (a+k) := by
  constructor
  · rintro ⟨f, hf⟩
    have hn : ¬ AnalyticAt ℂ (realArchimedeanZetaContinued a f) c := by
      intro ha
      have h := ha.meromorphicOrderAt_nonneg
      rw [hf] at h
      change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at h
      have h' : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp h
      omega
    have h := mt (realArchimedeanZetaContinued_analyticAt a f (s := c)) hn
    push Not at h
    obtain ⟨k, hk⟩ := h
    have hc := eq_neg_of_add_eq_zero_left hk
    refine ⟨k, hc, ?_⟩
    by_contra hodd
    exact hn (hc ▸ realArchimedeanZetaContinued_oppositeParity a k f
      (Nat.not_even_iff_odd.mp hodd))
  · rintro ⟨k, rfl, hk⟩
    obtain ⟨f, _, hf⟩ := realArchimedeanZetaContinued_hasPole a k hk
    exact ⟨f, hf⟩

/-- The real-place Laurent expansion converges in the strong dual of Schwartz
space, with the residue functional supplied by the parity-selected real jet. -/
theorem realArchimedeanZetaContinued_strongPrincipalPart (a : ℕ) (c : ℂ) :
    ∃ (R : ℝ) (Z : ℂ → Tests →L[ℂ] ℂ) (P : Tests →L[ℂ] ℂ),
      0 < R ∧ StrongDualTaylorOnBall Z c R ∧
      (∀ z ∈ Metric.closedBall c R, realArchimedeanZetaContinuedCLM a z = Z z + (z-c)⁻¹ • P) ∧
      (∀ k : ℕ, c = -(k : ℂ) → P = realArchimedeanZetaResidue a k) ∧
      ((∀ k : ℕ, c ≠ -(k : ℂ)) → P = 0) := by
  obtain ⟨R, Z, P, hR, hZ, heq, hP, hzero⟩ := schwartzMellinContinued_strongPrincipalPart c
  let L : Tests →L[ℂ] Tests := ContinuousLinearMap.id ℂ Tests + ((-1 : ℂ) ^ a) • realZetaReflect
  have hT := @StrongDualTaylorOnBall.reparametrize Tests Tests _ _ _ _ _ _ Z c 1 R
    (by simpa only [one_mul] using hZ) one_ne_zero L
  refine ⟨R, fun z => (Z z).comp L, P.comp L, hR, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul, norm_one, div_one] using hT
  · intro z hz
    apply ContinuousLinearMap.ext
    intro f
    change schwartzMellinContinuedCLM z (L f) = Z z (L f) + (z-c)⁻¹ * P (L f)
    rw [heq z hz]
    rfl
  · intro k hk
    apply ContinuousLinearMap.ext
    intro f
    change P (L f) = realArchimedeanZetaResidue a k f
    rw [hP k hk (L f), realArchimedeanZetaResidue_apply]
    exact realZetaProfile_taylorCoeff a k f
  · intro hc
    simp [hzero hc]


end

end Masullo
