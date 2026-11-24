import ModulatedSobolevNorm
import CompactGroupMellin

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- All logarithmic twists are Schwartz functions valued in the sup norm on
the compact factor. The radial seminorms are uniform in the angular variable. -/
def modulatedExponentialProfiles : Submodule ℂ (ℝ → C(K, ℂ)) where
  carrier := {f | ∀ b : ℝ, ∃ F : 𝓢(ℝ, C(K, ℂ)), ∀ x,
    F x = (Real.exp (b * x) : ℂ) • f x}
  zero_mem' := by
    intro b
    exact ⟨0, fun _ => by simp⟩
  add_mem' {f g} hf hg := by
    intro b
    obtain ⟨F, hF⟩ := hf b
    obtain ⟨G, hG⟩ := hg b
    exact ⟨F + G, fun x => by rw [add_apply, hF, hG, Pi.add_apply, smul_add]⟩
  smul_mem' a f hf := by
    intro b
    obtain ⟨F, hF⟩ := hf b
    exact ⟨a • F, fun x => by rw [smul_apply, hF, Pi.smul_apply, smul_comm]⟩

local notation "Profiles" => (modulatedExponentialProfiles (K := K))

omit [T2Space K] in
theorem modulatedExponentialProfile_continuous (f : Profiles) : Continuous f.val := by
  obtain ⟨F, hF⟩ := f.property 0
  refine F.continuous.congr fun x => ?_
  simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_smul] using hF x

omit [T2Space K] in
theorem modulatedExponentialProfile_jointContinuous (f : Profiles) :
    Continuous (fun p : K × ℝ => f.val p.2 p.1) :=
  (modulatedExponentialProfile_continuous f |>.comp continuous_snd).eval continuous_fst

variable [MeasurableSpace K] [BorelSpace K]

/-- Uniform radial estimates extracted from a Schwartz stage on a compact
angular factor. The zeroth angular derivatives suffice for this comparison. -/
def HasUniformRadialSchwartzDerivatives (f : ℝ × K → ℂ) : Prop :=
  ∃ D : ℕ → ℝ × K → ℂ, D 0 = f ∧
    (∀ n, Continuous (D n)) ∧
    (∀ n x k, HasDerivAt (fun y : ℝ => D n (y, k)) (D (n + 1) (x, k)) x) ∧
    ∀ p n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x k, ‖x‖ ^ p * ‖D n (x, k)‖ ≤ C

/-- Every uniform radial Schwartz stage is Schwartz in the compact sup norm. -/
theorem HasUniformRadialSchwartzDerivatives.toUniformProfile {f : ℝ × K → ℂ}
    (hf : HasUniformRadialSchwartzDerivatives f) :
    ∃ F : 𝓢(ℝ, C(K, ℂ)), ∀ x k, F x k = f (x, k) := by
  obtain ⟨D, hD₀, hDcont, hDderiv, hbound⟩ := hf
  let A (n : ℕ) := curryCompactProfile (D n) (hDcont n)
  have hAderiv (n : ℕ) : deriv (A n) = A (n + 1) :=
    funext fun x => (curryCompactProfile_hasDerivAt _ _ (hDcont n) (hDcont (n + 1))
      (hDderiv n) x).deriv
  have hDiff (p : ℕ) (n : ℕ) : ContDiff ℝ p (A n) := by
    induction p generalizing n with
    | zero => exact contDiff_zero.mpr (curryCompactProfile_continuous (D n) (hDcont n))
    | succ p ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv, hAderiv]
      exact ⟨fun x => (curryCompactProfile_hasDerivAt _ _ (hDcont n) (hDcont (n + 1))
        (hDderiv n) x).differentiableAt, by simp, ih (n + 1)⟩
  have hAiter (n : ℕ) : iteratedDeriv n (A 0) = A n := by
    induction n with
    | zero => simp
    | succ n ih => rw [iteratedDeriv_succ, ih, hAderiv]
  let F : 𝓢(ℝ, C(K, ℂ)) :=
    { toFun := A 0
      smooth' := contDiff_infty.mpr (fun p => hDiff p 0)
      decay' := by
        intro p n
        obtain ⟨C, hC, h⟩ := hbound p n
        refine ⟨C, fun x => ?_⟩
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hAiter]
        have hnorm : ‖(‖x‖ ^ p : ℝ) • A n x‖ ≤ C := by
          apply (ContinuousMap.norm_le _ hC).mpr
          intro k
          rw [ContinuousMap.smul_apply, norm_smul,
            Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
          exact h x k
        rwa [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] at hnorm }
  exact ⟨F, fun x k => congrFun hD₀ (x, k)⟩

omit [CompactSpace K] [T2Space K] in
/-- Pullback along a compact angular factor map preserves all the uniform
radial estimates of an elementary stage. -/
theorem HasUniformRadialSchwartzDerivatives.pullback {P : Type*} [TopologicalSpace P]
    {f : ℝ × P → ℂ} (hf : HasUniformRadialSchwartzDerivatives f)
    {q : K → P} (hq : Continuous q) :
    HasUniformRadialSchwartzDerivatives (fun p : ℝ × K => f (p.1, q p.2)) := by
  obtain ⟨D, hD₀, hDcont, hDderiv, hbound⟩ := hf
  refine ⟨fun n p => D n (p.1, q p.2), ?_, ?_, ?_, ?_⟩
  · exact funext fun p => congrFun hD₀ (p.1, q p.2)
  · intro n
    exact (hDcont n).comp (continuous_fst.prodMk (hq.comp continuous_snd))
  · intro n x k
    exact hDderiv n x (q k)
  · intro p n
    obtain ⟨C, hC, h⟩ := hbound p n
    exact ⟨C, hC, fun x k => h x (q k)⟩

/-- A split group test whose twists have the finite-stage radial estimates
belongs to the full uniform profile space. -/
theorem modulatedExponentialProfile_of_stageEstimates (f : ℝ → C(K, ℂ))
    (hf : ∀ b : ℝ, HasUniformRadialSchwartzDerivatives
      (fun p : ℝ × K => (Real.exp (b * p.1) : ℂ) * f p.1 p.2)) :
    f ∈ Profiles := by
  intro b
  obtain ⟨F, hF⟩ := (hf b).toUniformProfile
  exact ⟨F, fun x => ContinuousMap.ext fun k => hF x k⟩

variable (μ : Measure K) [IsFiniteMeasure μ]

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] [BorelSpace K] [IsFiniteMeasure μ] in
private theorem stripProd_measure_eq (b s : ℝ) :
    μ.prod (stripMeasure b b s) = hardySobolevMeasure (μ.prod volume)
      (Prod.snd : K × ℝ → ℝ) b b s := by
  rw [stripMeasure_eq b b s le_rfl, hardySobolevMeasure, hardySobolevMeasure]
  simp only [id_eq]
  rw [prod_withDensity_right ((continuous_hardySobolevWeight b b s).measurable.ennreal_ofReal)]

/-- Uniformly Schwartz twists are square integrable for every indicated
weighted Sobolev norm. -/
theorem modulatedExponentialProfile_memLp (b : ℝ) (N : ℕ) (f : Profiles) :
    MemLp (fun p : K × ℝ => f.val p.2 p.1) 2
      (μ.prod (stripMeasure b b (2 * (N : ℝ)))) := by
  let s : ℝ := 2 * (N : ℝ)
  let f' (p : K × ℝ) := f.val p.2 p.1
  rw [stripProd_measure_eq]
  let ρ := hardySobolevMeasure (μ.prod volume) (Prod.snd : K × ℝ → ℝ) b b s
  have hFcont : Continuous f' := modulatedExponentialProfile_jointContinuous f
  change MemLp f' 2 ρ
  apply (memLp_two_iff_integrable_sq_norm hFcont.aestronglyMeasurable).mpr
  apply (integrable_hardySobolev_sq_iff (μ.prod volume) measurable_snd b b s f').mpr
  obtain ⟨F, hF⟩ := f.property b
  let P (x : ℝ) : ℂ := ((1 + x ^ 2 : ℝ) ^ N : ℝ)
  have hP : P.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp
    (((Function.HasTemperateGrowth.const (1 : ℝ)).add
      (Function.HasTemperateGrowth.id'.pow 2)).pow N)
  let J := SchwartzMap.smulLeftCLM (C(K, ℂ)) P F
  have hJnorm (x : ℝ) : ‖J x‖ = (1 + x ^ 2) ^ N * ‖F x‖ := by
    have hn : 0 ≤ (1 + x ^ 2) ^ N := by positivity
    rw [show J x = P x • F x from SchwartzMap.smulLeftCLM_apply_apply hP F x, norm_smul]
    congr 1
    change ‖(((1 + x ^ 2) ^ N : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg hn]
  have hI : Integrable (fun x => ‖J x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (J.memLp 2 volume).aestronglyMeasurable).mp
      (J.memLp 2 volume)
  have hbound : Integrable (fun p : K × ℝ => ‖J p.2‖ ^ 2) (μ.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hI (μ := μ)
  apply hbound.mono'
  · exact (((continuous_hardySobolevWeight b b s).comp continuous_snd).mul
      (hFcont.norm.pow 2)).aestronglyMeasurable
  · refine Eventually.of_forall fun p => ?_
    let x := p.2
    let W : ℝ := (1 + x ^ 2) ^ N
    have hW : 1 ≤ W := one_le_pow₀ (by linarith [sq_nonneg x] : (1 : ℝ) ≤ 1 + x ^ 2)
    have hN : s / 2 = (N : ℝ) := by dsimp [s]; ring
    have hfiber : ‖F x p.1‖ = Real.exp (b * x) * ‖f' p‖ := by
      rw [hF x, ContinuousMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    have hFbound : ‖F x p.1‖ ≤ ‖F x‖ := (F x).norm_coe_le_norm p.1
    have hD : hardySobolevWeight b b s x = Real.exp (b * x) ^ 2 * W := by
      simp only [hardySobolevWeight, max_self, hN, Real.rpow_natCast, W]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    change ‖hardySobolevWeight b b s x * ‖f' p‖ ^ 2‖ ≤ ‖J x‖ ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (hardySobolevWeight_nonneg ..) (sq_nonneg _)),
      hD, hJnorm]
    change Real.exp (b * x) ^ 2 * W * ‖f' p‖ ^ 2 ≤ (W * ‖F x‖) ^ 2
    calc
      _ = W * ‖F x p.1‖ ^ 2 := by rw [hfiber]; ring
      _ ≤ W * ‖F x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hFbound 2)
          (zero_le_one.trans hW)
      _ ≤ (W * ‖F x‖) ^ 2 := by
        rw [mul_pow]
        have hw' : W ≤ W ^ 2 := by
          simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hW (zero_le_one.trans hW)
        exact mul_le_mul_of_nonneg_right hw' (sq_nonneg _)

/-- The weighted group test class uses its physical pointwise profile. -/
def modulatedExponentialProfile_toLp (b : ℝ) (N : ℕ) (f : Profiles) :
    Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) :=
  (modulatedExponentialProfile_memLp μ b N f).toLp _

theorem modulatedExponentialProfile_toLp_ae (b : ℝ) (N : ℕ) (f : Profiles) :
    (modulatedExponentialProfile_toLp μ b N f : K × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure b b (2 * (N : ℝ)))]
      fun p => f.val p.2 p.1 :=
  (modulatedExponentialProfile_memLp μ b N f).coeFn_toLp

section Character

variable [CommGroup K]

private def profileCharacterMap (χ : PontryaginDual K) : C(K, ℂ) →L[ℂ] ℂ :=
  compactCharacterIntegral μ ⟨fun k => (χ k : ℂ), continuous_subtype_val.comp χ.continuous⟩
    (fun k => Circle.norm_coe (χ k))

omit [T2Space K] in
private theorem profileCharacterMap_apply (χ : PontryaginDual K) (f : C(K, ℂ)) :
    profileCharacterMap μ χ f = ∫ k, f k * (χ k : ℂ) ∂μ := rfl

/-- Taking a compact character coefficient commutes with every logarithmic
twist and produces an actual scalar exponential Schwartz test. -/
def modulatedExponentialProfile_character (χ : PontryaginDual K) (f : Profiles) :
    PositiveRealExponentialDecay univ := by
  let A := profileCharacterMap μ χ
  refine ⟨fun x => A (f.val x), ?_⟩
  apply (Submodule.mem_iInf _).mpr
  intro b
  obtain ⟨F, hF⟩ := f.property b.val
  refine ⟨F.postcompCLM A, funext fun x => ?_⟩
  change F.postcompCLM A x = (Real.exp (b.val * x) : ℂ) * A (f.val x)
  rw [SchwartzMap.postcompCLM_apply, hF, map_smul, smul_eq_mul]

omit [T2Space K] in
theorem modulatedExponentialProfile_character_apply (χ : PontryaginDual K) (f : Profiles)
    (x : ℝ) : (modulatedExponentialProfile_character μ χ f).val x =
      ∫ k, f.val x k * (χ k : ℂ) ∂μ := profileCharacterMap_apply μ χ (f.val x)

/-- The compact coefficient on the weighted product space extends the integral
coefficient on exponential Schwartz profiles. -/
theorem modulatedExponentialProfile_character_weighted (b : ℝ) (N : ℕ)
    (χ : PontryaginDual K) (f : Profiles) :
    lpTwoCharacterCoefficient χ (modulatedExponentialProfile_toLp μ b N f) =
      weightedLineTest b N (modulatedExponentialProfile_character μ χ f) := by
  let ν := stripMeasure b b (2 * (N : ℝ))
  let v := modulatedExponentialProfile_toLp μ b N f
  let g := modulatedExponentialProfile_character μ χ f
  have hf : ∀ᵐ p ∂ν.prod μ, v (p.2, p.1) = f.val p.1 p.2 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (modulatedExponentialProfile_toLp_ae μ b N f)
  apply Lp.ext
  filter_upwards [lpTwoCharacterCoefficient_ae χ v, Measure.ae_ae_of_ae_prod hf,
    stripSobolevTest_ae univ ⟨b, mem_univ b⟩ ⟨b, mem_univ b⟩ (2 * (N : ℝ)) g] with x hx hv hg
  change lpTwoCharacterCoefficient χ v x = weightedLineTest b N g x
  change weightedLineTest b N g x = g.val x at hg
  rw [hx.2, hg, modulatedExponentialProfile_character_apply]
  apply integral_congr_ae
  exact hv.mono fun k hk => (congrArg ((χ k : ℂ) * ·) hk).trans (mul_comm _ _)

/-- A character coordinate of the full Hilbert tensor, with values in the
scalar normalized Mellin line space. -/
def modulatedMellinLineCharacter (b : ℝ) (N : ℕ) (χ : PontryaginDual K) :
    Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) →L[ℂ] MellinLineCompletion b N :=
  (mellinLineEquiv b N).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lpTwoCharacterCoefficient χ).comp
      (modulatedMellinLineEquiv μ b N).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The full weighted Mellin isometry agrees with the initial normalized
character Mellin traces of every exponential Schwartz profile. -/
theorem modulatedMellinLineCharacter_onProfile (b : ℝ) (N : ℕ) (χ : PontryaginDual K) (f : Profiles) :
    (modulatedMellinLineCharacter μ b N χ
      (modulatedMellinLineEquiv μ b N (modulatedExponentialProfile_toLp μ b N f)) :
        MellinTraceHilbert N) =
      mellinLineTest b N (modulatedExponentialProfile_character μ χ f) := by
  let M := modulatedMellinLineEquiv μ b N
  let u := modulatedExponentialProfile_toLp μ b N f
  change ((mellinLineEquiv b N (lpTwoCharacterCoefficient χ (M.symm (M u)))) :
    MellinTraceHilbert N) = _
  rw [M.symm_apply_apply, modulatedExponentialProfile_character_weighted, mellinLineEquiv_onTest]

end Character

end
end Masullo
