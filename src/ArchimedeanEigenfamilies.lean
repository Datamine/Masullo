import ArchimedeanGammaTests
import ArchimedeanProductZeta
import StrongDualBarrelled
import VectorHolomorphyDerivatives

open Filter Function Set Topology
open scoped SchwartzMap

namespace Masullo

noncomputable section

private theorem entire_strongDual_of_analyticOperatorGerms
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [ContinuousSMul ℂ E] [CompleteSpace (StrongDual ℂ E)]
    (hEval : ∀ L : StrongDual ℂ (StrongDual ℂ E), ∃ x : E, ∀ f, L f = f x)
    (A : ℂ → E →L[ℂ] ℂ) (hA : ∀ c, AnalyticOperatorGerm A c) :
    ∃ N : ℂ → StrongDual ℂ E, Differentiable ℂ N ∧
      (∀ f, AnalyticOnNhd ℂ (fun z ↦ N z f) univ) ∧
      ∀ c, N =ᶠ[𝓝[≠] c] A := by
  classical
  choose B hB hT using hA
  let N (c : ℂ) := B c c
  have he (f : E) (c : ℂ) :
      (fun z ↦ A z f) =ᶠ[𝓝[≠] c] fun z ↦ B c z f :=
    (hB c).mono fun z h ↦ DFunLike.congr_fun h f
  have ha (f : E) (c : ℂ) : AnalyticAt ℂ (fun z ↦ B c z f) c := by
    have hD : DifferentiableOn ℂ (fun z ↦ B c z f) {z | ∃ D, HasOperatorTaylorEstimate (B c) z D} := by
      rintro z ⟨D, hD⟩
      exact (hD.hasDerivAt f).differentiableAt.differentiableWithinAt
    exact hD.analyticAt (hT c)
  have hM (f : E) : MeromorphicOn (fun z ↦ A z f) univ :=
    fun c _ ↦ (ha f c).meromorphicAt.congr (he f c).symm
  have hN (f : E) : (fun z ↦ N z f) = toMeromorphicNFOn (fun z ↦ A z f) univ := by
    funext c
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (hM f) (mem_univ c),
      (toMeromorphicNFAt_eventuallyEq_nhds_congr (he f c)).eq_of_nhds,
      toMeromorphicNFAt_eq_self.mpr (ha f c).meromorphicNFAt]
  have hHol (f : E) : AnalyticOnNhd ℂ (fun z ↦ N z f) univ := by
    rw [hN f]
    intro c hc
    apply (meromorphicNFOn_toMeromorphicNFOn _ _ hc).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn (hM f) hc, meromorphicOrderAt_congr (he f c)]
    exact (ha f c).meromorphicOrderAt_nonneg
  have hEq (c : ℂ) : N =ᶠ[𝓝[≠] c] A := by
    have hAOn : {z | B c z = A z} ∈ 𝓝[≠] c := (hB c).symm
    obtain ⟨U, hU, hUA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hAOn
    obtain ⟨V, hVU, hVo, hcV⟩ := mem_nhds_iff.mp (inter_mem hU (hT c))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hVo.mem_nhds hcV),
      self_mem_nhdsWithin] with z hz hzc
    have hz' : z ∈ V \ {c} := ⟨hz, hzc⟩
    have hopen : IsOpen (V \ {c}) := hVo.sdiff isClosed_singleton
    apply ContinuousLinearMap.ext
    intro f
    have hlocal : (fun t ↦ A t f) =ᶠ[𝓝[≠] z] fun t ↦ B c t f := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hz')] with t ht
      exact DFunLike.congr_fun (hUA ⟨(hVU ht.1).1, ht.2⟩).symm f
    have hZ : AnalyticAt ℂ (fun t ↦ B c t f) z := by
      have hdiff : DifferentiableOn ℂ (fun t ↦ B c t f) V := by
        intro t ht
        obtain ⟨D', hD'⟩ := (hVU ht).2
        exact (hD'.hasDerivAt f).differentiableAt.differentiableWithinAt
      exact hdiff.analyticAt (hVo.mem_nhds hz)
    change (fun t ↦ N t f) z = A z f
    rw [hN f, toMeromorphicNFOn_eq_toMeromorphicNFAt (hM f) (mem_univ z),
      (toMeromorphicNFAt_eventuallyEq_nhds_congr hlocal).eq_of_nhds, toMeromorphicNFAt_eq_self.mpr hZ.meromorphicNFAt]
    exact DFunLike.congr_fun (hUA ⟨(hVU hz).1, hzc⟩) f
  refine ⟨N, ?_, hHol, hEq⟩
  letI : PolynormableSpace ℂ (StrongDual ℂ E) := strongDual_withBoundedSeminorms.toPolynormableSpace
  apply differentiableOn_univ.mp
  apply differentiableOn_of_weaklyHolomorphicOn isOpen_univ
  intro L
  obtain ⟨x, hx⟩ := hEval L
  exact (hHol x).differentiableOn.congr fun z _ ↦ hx (N z)

private abbrev Zeros := Fin 0 → ℝ

private def scalarSchwartzLift (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    𝓢(V, ℂ) →L[ℂ] 𝓢(V × Zeros, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodUnique ℝ V Zeros)

private def scalarSchwartzEval : 𝓢(Zeros, ℂ) →L[ℂ] ℂ :=
  { toFun := fun f ↦ f 0
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    cont := (BoundedContinuousFunction.lipschitz_eval_const (0 : Zeros)).continuous.comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ Zeros ℂ).continuous }

private theorem scalarSchwartzLift_slice (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : 𝓢(V, ℂ)) : archimedeanSlice 0 (scalarSchwartzLift V f) = f := by
  ext x
  rw [archimedeanSlice_apply, scalarSchwartzLift, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, ContinuousLinearEquiv.prodUnique_apply]

private theorem realGammaCleared_localGerm (a : ℕ) (c : ℂ) :
    AnalyticOperatorGerm (fun z ↦ realArchZetaDenominator a z • realArchimedeanZetaContinuedCLM a z)
      c := by
  have h := realArchimedeanZetaInFirst_analyticOperatorGerm (Y := Zeros) a
    (realArchZetaDenominator_analytic a c) (by
      intro k hk hp
      apply inv_eq_zero.mpr
      apply not_ne_iff.mp
      intro hne
      exact (Nat.not_odd_iff_even.mpr hp) (((realArchZetaRegular_iff_gamma _ _).mpr hne) k hk))
  apply ((AnalyticOperatorGerm.const scalarSchwartzEval).comp
    (h.smul_comp_const (scalarSchwartzLift ℝ))).congr (.of_forall fun z ↦ ?_)
  ext f
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    realArchimedeanZetaContinuedCLM_apply]
  change realArchZetaDenominator a z * realArchimedeanZetaContinued a f z =
    realArchZetaDenominator a z * realArchimedeanZetaInFirst a z (scalarSchwartzLift ℝ f) 0
  rw [realArchimedeanZetaInFirst_apply, scalarSchwartzLift_slice]

attribute [local instance] complexZeta_circleMeasurable

private theorem complexGammaCleared_localGerm (m : ℤ) (c : ℂ) :
    AnalyticOperatorGerm (fun z ↦ complexArchZetaDenominator m z •
      complexArchimedeanZetaContinuedCLM complexTamagawaAngularMeasure m z) c := by
  have h := complexArchimedeanZetaInFirst_analyticOperatorGerm (Y := Zeros)
    complexTamagawaAngularMeasure m (complexArchZetaDenominator_analytic m c) (by
      intro k hk hp
      apply inv_eq_zero.mpr
      apply not_ne_iff.mp
      intro hne
      exact (((complexArchZetaRegular_iff_gamma _ _).mpr hne) k hk) hp)
  apply ((AnalyticOperatorGerm.const scalarSchwartzEval).comp
    (h.smul_comp_const (scalarSchwartzLift ℂ))).congr (.of_forall fun z ↦ ?_)
  ext f
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    complexArchimedeanZetaContinuedCLM_apply]
  change complexArchZetaDenominator m z *
      complexArchimedeanZetaContinued complexTamagawaAngularMeasure m f z =
    complexArchZetaDenominator m z * complexArchimedeanZetaInFirst complexTamagawaAngularMeasure
      m z (scalarSchwartzLift ℂ f) 0
  rw [complexArchimedeanZetaInFirst_apply, scalarSchwartzLift_slice]

private theorem gamma_normalized_family
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Z : ℂ → 𝓢(V, ℂ) →L[ℂ] ℂ) (G : ℂ → ℂ)
    (hA : ∀ c, AnalyticOperatorGerm (fun z ↦ (G z)⁻¹ • Z z) c)
    (hG : AnalyticOnNhd ℂ (fun z ↦ (G z)⁻¹) univ) (hG₀ : G 1 ≠ 0)
    (f₀ : 𝓢(V, ℂ)) (hf₀ : ∀ c, (fun z ↦ Z z f₀) =ᶠ[𝓝[≠] c] G) :
    ∃ N : ℂ → StrongDual ℂ 𝓢(V, ℂ), Differentiable ℂ N ∧
      (∀ f, AnalyticOnNhd ℂ (fun z ↦ N z f) univ) ∧ (∀ z, N z f₀ = 1) ∧
      ∀ c, Z =ᶠ[𝓝[≠] c] fun z ↦ G z • N z := by
  letI : CompleteSpace (StrongDual ℂ 𝓢(V, ℂ)) := classicalSchwartz_strongDual_complete V
  letI : PolynormableSpace ℂ 𝓢(V, ℂ) := (classicalSchwartz_isFrechet V).choose_spec.1
  have hEval (L : StrongDual ℂ (StrongDual ℂ 𝓢(V, ℂ))) : ∃ x : 𝓢(V, ℂ), ∀ f, L f = f x := by
    obtain ⟨e, he⟩ := classicalSchwartz_reflexive V
    exact ⟨e.symm L, fun f ↦ (DFunLike.congr_fun (e.apply_symm_apply L) f).symm.trans (he _ _)⟩
  obtain ⟨N, hN, hhol, he⟩ := entire_strongDual_of_analyticOperatorGerms hEval _ hA
  have hne (c : ℂ) : ∀ᶠ z in 𝓝[≠] c, G z ≠ 0 := by
    rcases (hG c (mem_univ c)).eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · have h := hG.eq_of_eventuallyEq (analyticOnNhd_const (v := (0 : ℂ))) hz
      exact (inv_ne_zero hG₀ (congrFun h 1)).elim
    · exact hz.mono fun z hz h ↦ hz (by simp [h])
  have hEq (c : ℂ) : Z =ᶠ[𝓝[≠] c] fun z ↦ G z • N z := by
    filter_upwards [he c, hne c] with z h hn
    rw [h, smul_smul, mul_inv_cancel₀ hn, one_smul]
  refine ⟨N, hN, hhol, fun z ↦ ?_, hEq⟩
  have hz : ∀ᶠ w in 𝓝[≠] z, N w f₀ = 1 := by
    filter_upwards [he z, hne z, hf₀ z] with w hw hn hh
    rw [show N w f₀ = (G w)⁻¹ * Z w f₀ from DFunLike.congr_fun hw f₀, hh, inv_mul_cancel₀ hn]
  have hlim := (((hhol f₀) z (mem_univ z)).continuousAt.tendsto).mono_left
    (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hz))

/-- The normalized real family is holomorphic in the strong dual everywhere,
including the exceptional parameters. The real Gaussian fixes the normalization. -/
theorem realGammaNormalized_distribution (a : ℕ) :
    let G (z : ℂ) := Complex.Gammaℝ (z + ((a % 2 : ℕ) : ℂ))
    ∃ (f₀ : 𝓢(ℝ, ℂ)) (N : ℂ → StrongDual ℂ 𝓢(ℝ, ℂ)),
      (∀ x : ℝ, f₀ x = (x : ℂ) ^ (a % 2) * (Real.exp (-Real.pi * ‖x‖^2) : ℂ)) ∧
      Differentiable ℂ N ∧ (∀ z, N z f₀ = 1) ∧
      ∀ c, realArchimedeanZetaContinuedCLM a =ᶠ[𝓝[≠] c] fun z ↦ G z • N z := by
  intro G
  obtain ⟨f, hf, he⟩ := exists_realGammaTest_explicit a
  have hG₀ : G 1 ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; positivity)
  obtain ⟨N, hN, _, hN₀, hEq⟩ := gamma_normalized_family ℝ
    (realArchimedeanZetaContinuedCLM a) G (realGammaCleared_localGerm a)
    (fun c _ ↦ realArchZetaDenominator_analytic a c) hG₀ f (fun c ↦ by simpa only [realArchimedeanZetaContinuedCLM_apply] using he c)
  exact ⟨f, N, hf, hN, hN₀, hEq⟩

/-- The angular Gaussian fixes the normalization of the entire complex
distribution family for the multiplicative Tamagawa measure. -/
theorem complexGammaNormalized_distribution (m : ℤ) :
    let G (z : ℂ) := Complex.Gammaℂ (z + (m.natAbs : ℂ) / 2)
    ∃ (f₀ : 𝓢(ℂ, ℂ)) (N : ℂ → StrongDual ℂ 𝓢(ℂ, ℂ)),
      (∀ x : ℂ, f₀ x = (x ^ (-m).toNat * star x ^ m.toNat) *
        ((Real.pi : ℂ)⁻¹ * (Real.exp (-(2 * Real.pi) * ‖x‖^2) : ℂ))) ∧
      Differentiable ℂ N ∧ (∀ z, N z f₀ = 1) ∧
      ∀ c, complexArchimedeanZetaContinuedCLM complexTamagawaAngularMeasure m
        =ᶠ[𝓝[≠] c] fun z ↦ G z • N z := by
  intro G
  obtain ⟨f, hf, he⟩ := exists_complexGammaTest_explicit m
  have hG₀ : G 1 ≠ 0 := by
    apply (complexArchZetaRegular_iff_gamma m 1).mp
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨N, hN, _, hN₀, hEq⟩ := gamma_normalized_family ℂ
    (complexArchimedeanZetaContinuedCLM complexTamagawaAngularMeasure m) G
    (complexGammaCleared_localGerm m) (fun c _ ↦ complexArchZetaDenominator_analytic m c)
    hG₀ f (fun c ↦ by simpa only [complexArchimedeanZetaContinuedCLM_apply] using he c)
  exact ⟨f, N, hf, hN, hN₀, hEq⟩

end
end Masullo
