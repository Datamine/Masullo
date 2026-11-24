import HardySobolevCutoff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Extend

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

local notation "Tests" => (PositiveRealExponentialDecay (univ : Set ℝ))
local notation "HeightL2" => (Lp ℂ 2 (volume : Measure ℝ))

private def mellinDerivativeLine (a : ℝ) (k : ℕ) (f : Tests) (y : ℝ) : ℂ :=
  iteratedDeriv k (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ)

private theorem mellinDerivativeLine_memLp (a : ℝ) (k : ℕ) (f : Tests) :
    MemLp (mellinDerivativeLine a k f) 2 volume :=
  (mellin_iteratedDeriv_line_energy f k a).1

private theorem mellinEvaluation_test_integrable (f : Tests) (k : ℕ) (z : ℂ) :
    Integrable (fun x => f.val x * mellinEvaluationKernel k z x) :=
  (integrable_mellin_test_moment f k z).congr (.of_forall fun x => by
    simp only [mellinEvaluationKernel]; ring)

private def mellinDerivativeLineLp (a : ℝ) (k : ℕ) : Tests →ₗ[ℂ] HeightL2 where
  toFun f := (mellinDerivativeLine_memLp a k f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(mellinDerivativeLine_memLp a k (f + g)).coeFn_toLp,
      (mellinDerivativeLine_memLp a k f).coeFn_toLp,
      (mellinDerivativeLine_memLp a k g).coeFn_toLp,
      Lp.coeFn_add ((mellinDerivativeLine_memLp a k f).toLp _)
        ((mellinDerivativeLine_memLp a k g).toLp _)] with y hfg hf hg hadd
    rw [hfg, hadd, Pi.add_apply, hf, hg]
    simp only [mellinDerivativeLine, mellinEvaluation_test_integral]
    let z : ℂ := ⟨a, y⟩
    change (∫ x, (f.val x + g.val x) * mellinEvaluationKernel k z x) = _
    simp_rw [add_mul]
    exact integral_add (mellinEvaluation_test_integrable f k z)
      (mellinEvaluation_test_integrable g k z)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(mellinDerivativeLine_memLp a k (c • f)).coeFn_toLp,
      (mellinDerivativeLine_memLp a k f).coeFn_toLp,
      Lp.coeFn_smul c ((mellinDerivativeLine_memLp a k f).toLp _)] with y hcf hf hsmul
    rw [hcf, RingHom.id_apply, hsmul, Pi.smul_apply, hf]
    simp only [mellinDerivativeLine, mellinEvaluation_test_integral]
    let z : ℂ := ⟨a, y⟩
    change (∫ x, (c * f.val x) * mellinEvaluationKernel k z x) =
      c • ∫ x, f.val x * mellinEvaluationKernel k z x
    simp_rw [mul_assoc]
    exact integral_const_mul c _

private theorem mellinDerivativeLineLp_norm_sq (a : ℝ) (k : ℕ) (f : Tests) :
    ‖mellinDerivativeLineLp a k f‖ ^ 2 = mellinLineEnergy f k a := by
  change ‖(mellinDerivativeLine_memLp a k f).toLp _‖ ^ 2 = _
  rw [Lp.norm_toLp, toReal_eLpNorm (mellinDerivativeLine_memLp a k f).aestronglyMeasurable]
  change lpNorm (fun y : ℝ => iteratedDeriv k
    (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ)) 2 volume ^ 2 = _
  rw [← sqrt_mellinLineEnergy f k a, Real.sq_sqrt (mellinLineEnergy_nonneg f k a)]

/-- Finite Hilbert tuple of the Mellin derivative traces. -/
abbrev MellinTraceHilbert (N : ℕ) := PiLp 2 (fun _ : Fin (N + 1) => HeightL2)

private def lineCoefficient (N k : ℕ) : ℝ :=
  Real.sqrt ((N.choose k : ℝ) / (2 * Real.pi))

/-- The test map uses the binomial coefficients and the Mellin Plancherel
normalization in its finite Hilbert norm. -/
def mellinLineTest (a : ℝ) (N : ℕ) : Tests →ₗ[ℂ] MellinTraceHilbert N where
  toFun f := WithLp.toLp 2 (fun k : Fin (N + 1) =>
    (lineCoefficient N k : ℂ) • mellinDerivativeLineLp a k f)
  map_add' f g := by
    ext k
    simp [smul_add]
  map_smul' c f := by
    apply PiLp.ext
    intro k
    change (lineCoefficient N k : ℂ) • mellinDerivativeLineLp a k (c • f) =
      c • (lineCoefficient N k : ℂ) • mellinDerivativeLineLp a k f
    rw [map_smul]
    exact smul_comm _ _ _

def weightedLineTest (a : ℝ) (N : ℕ) :
    Tests →L[ℂ] StripSobolev a a (2 * (N : ℝ)) :=
  stripSobolevTest univ ⟨a, mem_univ a⟩ ⟨a, mem_univ a⟩ (2 * (N : ℝ))

theorem mellinLineTest_norm (a : ℝ) (N : ℕ) (f : Tests) :
    ‖mellinLineTest a N f‖ = ‖weightedLineTest a N f‖ := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h (k : ℕ) : ‖(lineCoefficient N k : ℂ)‖ ^ 2 = (N.choose k : ℝ) / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, lineCoefficient, Real.sq_sqrt (by positivity)]
  have hnorm : ‖weightedLineTest a N f‖ =
      (eLpNorm f.val 2 (hardySobolevMeasure volume id a a (2 * (N : ℝ)))).toReal := by
    unfold weightedLineTest
    rw [Lp.norm_def, eLpNorm_congr_ae (stripSobolevTest_ae univ ⟨a, mem_univ a⟩
      ⟨a, mem_univ a⟩ (2 * (N : ℝ)) f), stripMeasure_eq _ _ _ le_rfl]
  have hsq : ‖mellinLineTest a N f‖ ^ 2 = ‖weightedLineTest a N f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [mellinLineTest, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, norm_smul,
      mul_pow, h, mellinDerivativeLineLp_norm_sq]
    have heq := hardySobolev_singleton_mellin_energy a N f
    rw [← hnorm] at heq
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    have hsum : (∑ k : Fin (N + 1), (N.choose (k : ℕ) : ℝ) * mellinLineEnergy f k a) =
        ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * mellinLineEnergy f k a :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => (N.choose k : ℝ) * mellinLineEnergy f k a) (N + 1)
    rw [hsum, ← heq, mul_comm (2 * Real.pi), mul_div_cancel_right₀ _ hπ.ne']
  nlinarith [norm_nonneg (mellinLineTest a N f), norm_nonneg (weightedLineTest a N f)]

/-- The completed line map is isometric and carries the smooth inputs to
their actual Mellin derivative traces. -/
def mellinLineIsometry (a : ℝ) (N : ℕ) :
    StripSobolev a a (2 * (N : ℝ)) →ₗᵢ[ℂ] MellinTraceHilbert N := by
  let j := weightedLineTest a N
  let T := (mellinLineTest a N).extendOfNorm j.toLinearMap
  have hd : DenseRange j := stripSobolevTest_denseRange univ ⟨a, mem_univ a⟩
    ⟨a, mem_univ a⟩ _
  have hb : ∃ C : ℝ, ∀ f, ‖mellinLineTest a N f‖ ≤ C * ‖j f‖ :=
    ⟨1, fun f => by rw [one_mul, mellinLineTest_norm]⟩
  refine { T.toLinearMap with norm_map' := fun u => ?_ }
  refine hd.induction (fun _ ⟨f, hf⟩ => ?_) (isClosed_eq T.continuous.norm continuous_norm) u
  change ‖T _‖ = ‖_‖
  rw [← hf, show T (j f) = mellinLineTest a N f from LinearMap.extendOfNorm_eq hd hb f]
  exact mellinLineTest_norm a N f

theorem mellinLineIsometry_onTest (a : ℝ) (N : ℕ) (f : Tests) :
    mellinLineIsometry a N (weightedLineTest a N f) = mellinLineTest a N f := by
  change ((mellinLineTest a N).extendOfNorm (weightedLineTest a N).toLinearMap)
      (weightedLineTest a N f) = mellinLineTest a N f
  have hd : DenseRange (weightedLineTest a N) :=
    stripSobolevTest_denseRange univ ⟨a, mem_univ a⟩ ⟨a, mem_univ a⟩ (2 * (N : ℝ))
  refine LinearMap.extendOfNorm_eq hd ⟨1, fun g => ?_⟩ f
  change ‖mellinLineTest a N g‖ ≤ 1 * ‖weightedLineTest a N g‖
  rw [one_mul, mellinLineTest_norm a N g]


/-- The closed Hilbert space generated by the actual Mellin derivative tuples. -/
def MellinLineCompletion (a : ℝ) (N : ℕ) : Submodule ℂ (MellinTraceHilbert N) :=
  (LinearMap.range (mellinLineTest a N)).topologicalClosure

theorem mellinLineIsometry_range (a : ℝ) (N : ℕ) :
    LinearMap.range (mellinLineIsometry a N).toLinearMap = MellinLineCompletion a N := by
  let V := mellinLineIsometry a N
  let j := weightedLineTest a N
  let S := MellinLineCompletion a N
  have hd : DenseRange j := stripSobolevTest_denseRange univ ⟨a, mem_univ a⟩ ⟨a, mem_univ a⟩ _
  have hclosed : IsClosed (S : Set (MellinTraceHilbert N)) := Submodule.isClosed_topologicalClosure _
  have hVr : IsClosed (range V) := V.isometry.isClosedEmbedding.isClosed_range
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact (closure_minimal (s := range j) (t := V ⁻¹' (S : Set _)) (by
      rintro _ ⟨f, rfl⟩
      change V (j f) ∈ S
      rw [show V (j f) = mellinLineTest a N f from mellinLineIsometry_onTest a N f]
      exact Submodule.le_topologicalClosure _ ((mellinLineTest a N).mem_range_self f))
      (hclosed.preimage V.continuous)) (hd u)
  · apply closure_minimal _ hVr
    rintro _ ⟨f, rfl⟩
    exact ⟨j f, mellinLineIsometry_onTest a N f⟩

/-- The completed Mellin map is a linear isometric equivalence to the
closure of the analytic line traces. -/
def mellinLineEquiv (a : ℝ) (N : ℕ) :
    StripSobolev a a (2 * (N : ℝ)) ≃ₗᵢ[ℂ] MellinLineCompletion a N :=
  (mellinLineIsometry a N).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (mellinLineIsometry_range a N))

theorem mellinLineEquiv_onTest (a : ℝ) (N : ℕ) (f : Tests) :
    (mellinLineEquiv a N (weightedLineTest a N f) : MellinTraceHilbert N) = mellinLineTest a N f :=
  mellinLineIsometry_onTest a N f

/-- Each normalized component of a completed line is the actual Mellin
derivative on the original entire exponential-decay tests. -/
theorem mellinLineEquiv_onTest_derivative_ae (a : ℝ) (N : ℕ) (f : Tests) (k : Fin (N + 1)) :
    (((mellinLineEquiv a N (weightedLineTest a N f)).val k) : ℝ → ℂ)
      =ᵐ[volume] fun y => (Real.sqrt ((N.choose (k : ℕ) : ℝ) / (2 * Real.pi)) : ℂ) *
        iteratedDeriv (k : ℕ) (mellin fun t => f.val (Real.log t)) (⟨a, y⟩ : ℂ) := by
  rw [mellinLineEquiv_onTest]
  change ((lineCoefficient N k : ℂ) • mellinDerivativeLineLp a k f : HeightL2) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (lineCoefficient N k : ℂ) (mellinDerivativeLineLp a k f),
    (mellinDerivativeLine_memLp a k f).coeFn_toLp] with y hy hd
  refine hy.trans ?_
  change (lineCoefficient N k : ℂ) * (mellinDerivativeLineLp a k f) y =
    (lineCoefficient N k : ℂ) * mellinDerivativeLine a k f y
  exact congrArg ((lineCoefficient N k : ℂ) * ·) hd

/-- Closed trace space for the indicated open logarithmic support. -/
def supportedMellinLineCompletion (a : ℝ) (N : ℕ) (U : Set ℝ) :
    Submodule ℂ (MellinTraceHilbert N) :=
  (supportedSobolevCompletion a a (2 * (N : ℝ)) U).map (mellinLineIsometry a N).toLinearMap

/-- The supported trace space is the closure of the supported test traces. -/
theorem supportedMellinLineCompletion_eq_closure (a : ℝ) (N : ℕ) (U : Set ℝ) :
    (supportedMellinLineCompletion a N U : Set (MellinTraceHilbert N)) =
      closure {T | ∃ f : Tests, (∀ x ∉ U, f.val x = 0) ∧ mellinLineTest a N f = T} := by
  let S := supportedSobolevCompletion a a (2 * (N : ℝ)) U
  let V := mellinLineIsometry a N
  let W := supportedMellinLineCompletion a N U
  let j (f : {f : Tests // ∀ x ∉ U, f.val x = 0}) : S :=
    supportedSobolevTest a a (2 * (N : ℝ)) U f.val f.property
  let A : Set (MellinTraceHilbert N) :=
    {T | ∃ f : Tests, (∀ x ∉ U, f.val x = 0) ∧ mellinLineTest a N f = T}
  letI : CompleteSpace S := inferInstanceAs
    (CompleteSpace (supportedSobolevCompletion a a (2 * (N : ℝ)) U))
  have hVr : IsClosed (range (fun u : S => V u.val)) :=
    (V.isometry.comp (isometry_subtype_coe (s := (S : Set _)))).isClosedEmbedding.isClosed_range
  change (W : Set (MellinTraceHilbert N)) = closure A
  have hrange : range (fun u : S => V u.val) = (W : Set (MellinTraceHilbert N)) := by
    ext v
    exact ⟨fun ⟨u, hu⟩ => ⟨u.val, u.property, hu⟩, fun ⟨u, hu, hv⟩ => ⟨⟨u, hu⟩, hv⟩⟩
  rw [← hrange]
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have hd : DenseRange j := supportedSobolevTest_denseRange a a (2 * (N : ℝ)) U
    exact (closure_minimal (s := range j) (t := (fun u : S => V u.val) ⁻¹' closure A) (by
      rintro _ ⟨f, rfl⟩
      apply subset_closure
      exact ⟨f.val, f.property, (mellinLineIsometry_onTest a N f.val).symm⟩)
      (isClosed_closure.preimage (V.continuous.comp continuous_subtype_val))) (hd u)
  · apply closure_minimal _ hVr
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨j ⟨f, hf⟩, mellinLineIsometry_onTest a N f⟩

def supportedMellinLineEquiv (a : ℝ) (N : ℕ) (U : Set ℝ) :
    supportedSobolevCompletion a a (2 * (N : ℝ)) U ≃ₗᵢ[ℂ] supportedMellinLineCompletion a N U := by
  let V := mellinLineIsometry a N
  let S := supportedSobolevCompletion a a (2 * (N : ℝ)) U
  let T : S →ₗᵢ[ℂ] MellinTraceHilbert N := V.comp S.subtypeₗᵢ
  exact T.equivRange.trans (LinearIsometryEquiv.ofEq _ _ (by
    ext u; exact ⟨fun ⟨f, h⟩ => ⟨f.val, f.property, h⟩, fun ⟨f, hf, h⟩ => ⟨⟨f, hf⟩, h⟩⟩))


theorem supportedMellinLineEquiv_onTest (a : ℝ) (N : ℕ) (U : Set ℝ)
    (f : Tests) (hf : ∀ x ∉ U, f.val x = 0) :
    (supportedMellinLineEquiv a N U (supportedSobolevTest a a (2 * (N : ℝ)) U f hf) :
      MellinTraceHilbert N) = mellinLineTest a N f :=
  mellinLineIsometry_onTest a N f

/-- Corollary 9.2.1.4. Evaluation extends to the supported line completion,
and its formula holds on every weighted L² class in that completion. -/
theorem supportedMellinLine_evaluation {b A : ℝ} (hA : 1 < A) {z : ℂ} (hz : z.re < b)
    (N k : ℕ) :
    let U := Ioi (-Real.log A)
    let s := 2 * (N : ℝ)
    let E := supportedSobolevCompletion b b s U
    let W := supportedMellinLineCompletion b N U
    ∃ L : StrongDual ℂ W,
      (∀ (f : Tests) (hf : ∀ x ∉ U, f.val x = 0),
        L (supportedMellinLineEquiv b N U (supportedSobolevTest b b s U f hf)) =
          iteratedDeriv k (mellin fun t => f.val (Real.log t)) z) ∧
      ∀ u : E,
        Integrable (fun x => u.val x * mellinEvaluationKernel k z x) ∧
        L (supportedMellinLineEquiv b N U u) = ∫ x, u.val x * mellinEvaluationKernel k z x := by
  intro U s E W
  have hcut : -Real.log A ≤ 0 := neg_nonpos.mpr (Real.log_nonneg hA.le)
  obtain ⟨l, hl⟩ := (hardySobolev_cutoff_mellinEvaluation_exists_iff (a := b)
    (s := s) hcut hz.le (by dsimp [s]; positivity) k).mpr (Or.inl hz)
  have hl' : ∀ (f : Tests) (hf : ∀ x ∉ U, f.val x = 0),
      l (supportedSobolevTest b b s U f hf) = ∫ x, f.val x * mellinEvaluationKernel k z x :=
    fun f hf => (hl f hf).trans (mellinEvaluation_test_integral f k z)
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq E l
  let g := (stripSobolevDuality b b s).symm G
  have hK : Continuous (mellinEvaluationKernel k z) := by unfold mellinEvaluationKernel; fun_prop
  have hg : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ U → g x = mellinEvaluationKernel k z x := by
    apply stripDual_rep_eq_on_support_of_testPairing b b s hK isOpen_Ioi G
    intro f hf
    exact (hG (supportedSobolevTest b b s U f hf)).trans (hl' f hf)
  let V := supportedMellinLineEquiv b N U
  refine ⟨l.comp V.symm.toContinuousLinearEquiv.toContinuousLinearMap, ?_, ?_⟩
  · intro f hf
    change l (V.symm (V (supportedSobolevTest b b s U f hf))) = _
    rw [V.symm_apply_apply]
    exact hl f hf
  · intro u
    have hu := (mem_supportedSobolevCompletion_iff b b s isOpen_Ioi u.val).mp u.property
    have hp : (fun x => u.val x * g x) =ᵐ[volume] fun x => u.val x * mellinEvaluationKernel k z x := by
      filter_upwards [hu, hg] with x hx hy
      by_cases h : x ∈ U
      · rw [hy h]
      · simp [hx h]
    refine ⟨(stripSobolevDuality_integrable b b s u.val g).congr hp, ?_⟩
    change l (V.symm (V u)) = _
    rw [V.symm_apply_apply, ← hG u, ← (stripSobolevDuality b b s).apply_symm_apply G,
      stripSobolevDuality_apply]
    exact integral_congr_ae hp


/-- The cutoff sequence and its Mellin trace sequence form a commuting
diagram with exact rows and isometric vertical arrows. -/
theorem supportedMellinLine_cutoff_diagram (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    let s := 2 * (N : ℝ)
    let L := supportedSobolevCompletion b b s (Ioo c 0)
    let M := supportedSobolevCompletion b b s (Ioi c)
    let R := supportedSobolevCompletion b b s (Ioi 0)
    let L' := supportedMellinLineCompletion b N (Ioo c 0)
    let M' := supportedMellinLineCompletion b N (Ioi c)
    let R' := supportedMellinLineCompletion b N (Ioi 0)
    ∃ (i : L →L[ℂ] M) (p : M →L[ℂ] R) (i' : L' →L[ℂ] M') (p' : M' →L[ℂ] R'),
      (∀ f : L, (i f).val = f.val) ∧
      (∀ f : M, ((p f).val : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (f.val : ℝ → ℂ)) ∧
      (∀ f, supportedMellinLineEquiv b N (Ioi c) (i f) =
        i' (supportedMellinLineEquiv b N (Ioo c 0) f)) ∧
      (∀ f, supportedMellinLineEquiv b N (Ioi 0) (p f) =
        p' (supportedMellinLineEquiv b N (Ioi c) f)) ∧
      (Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p) ∧
      (Injective i' ∧ IsClosed (range i') ∧ Exact i' p' ∧ Surjective p' ∧ IsOpenMap p') := by
  intro s L M R L' M' R'
  obtain ⟨i, p, hi, hp, hinj, hclosed, hex, hsurj, hopen⟩ := stripSobolev_cutoff_exact b b s c hc
  let el := (supportedMellinLineEquiv b N (Ioo c 0)).toContinuousLinearEquiv
  let em := (supportedMellinLineEquiv b N (Ioi c)).toContinuousLinearEquiv
  let er := (supportedMellinLineEquiv b N (Ioi 0)).toContinuousLinearEquiv
  let i' := em.toContinuousLinearMap.comp (i.comp el.symm.toContinuousLinearMap)
  let p' := er.toContinuousLinearMap.comp (p.comp em.symm.toContinuousLinearMap)
  have hi' (f : L') : i' f = em (i (el.symm f)) := rfl
  have hp' (f : M') : p' f = er (p (em.symm f)) := rfl
  refine ⟨i, p, i', p', hi, hp, ?_, ?_, ⟨hinj, hclosed, hex, hsurj, hopen⟩, ?_⟩
  · intro f
    change em (i f) = i' (el f)
    rw [hi', el.symm_apply_apply]
  · intro f
    change er (p f) = p' (em f)
    rw [hp', em.symm_apply_apply]
  · refine ⟨em.injective.comp (hinj.comp el.symm.injective), ?_, ?_,
      er.surjective.comp (hsurj.comp em.symm.surjective),
      er.toHomeomorph.isOpenMap.comp (hopen.comp em.symm.toHomeomorph.isOpenMap)⟩
    · have he : range i' = em '' range i := by
        ext f
        constructor
        · rintro ⟨g, rfl⟩
          exact ⟨i (el.symm g), ⟨el.symm g, rfl⟩, (hi' g).symm⟩
        · rintro ⟨g, ⟨f, rfl⟩, rfl⟩
          exact ⟨el f, by rw [hi', el.symm_apply_apply]⟩
      rw [he]
      exact em.toHomeomorph.isClosedMap _ hclosed
    · intro f
      rw [hp', ← er.map_zero, er.injective.eq_iff, hex]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨el v, by rw [hi', el.symm_apply_apply, hv, em.apply_symm_apply]⟩
      · rintro ⟨v, rfl⟩
        exact ⟨el.symm v, by rw [hi', em.symm_apply_apply]⟩

end
end Masullo
