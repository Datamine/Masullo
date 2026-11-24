import ModulatedIntervalEvaluation
import VerticalZeroCounts
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open Filter Function MeasureTheory Set Topology
open scoped InnerProductSpace ENNReal

namespace Masullo

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The projections onto a decreasing family of closed subspaces converge
strongly to the projection onto their intersection. -/
theorem antitone_starProjection_tendsto {ι : Type*} [Preorder ι]
    (K : ι → ClosedSubmodule ℂ H) (hK : Antitone K) (x : H) :
    Tendsto (fun i => (K i).starProjection x) atTop
      (𝓝 ((⨅ i, K i).starProjection x)) := by
  let S (i : ι) : Submodule ℂ H := (K i).toSubmoduleᗮ
  have hS : Monotone S := fun _ _ h => Submodule.orthogonal_le (hK h)
  let U : Submodule ℂ H := (⨆ i, S i).topologicalClosure
  have hU : IsClosed (U : Set H) := Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace U := hU.completeSpace_coe
  have hlim := Submodule.starProjection_tendsto_closure_iSup S hS x
  have hKi : (⨅ i, K i).toSubmodule = Uᗮ := by
    rw [show Uᗮ = (⨆ i, S i)ᗮ from Submodule.orthogonal_closure _, ← Submodule.iInf_orthogonal]
    ext v
    simp only [ClosedSubmodule.mem_toSubmodule_iff, ClosedSubmodule.mem_iInf, Submodule.mem_iInf]
    refine forall_congr' fun i => ?_
    change v ∈ (K i).toSubmodule ↔ v ∈ ((K i).toSubmoduleᗮ)ᗮ
    rw [Submodule.orthogonal_orthogonal_eq_closure,
      (K i).isClosed.submodule_topologicalClosure_eq]
  have he (i : ι) : (K i).starProjection x = x - (S i).starProjection x := by
    rw [show (S i).starProjection x = x - (K i).toSubmodule.starProjection x from
      Submodule.starProjection_orthogonal_val x, sub_sub_cancel]
  simp only [he]
  change Tendsto (fun i => x - (S i).starProjection x) atTop
    (𝓝 ((⨅ i, K i).toSubmodule.starProjection x))
  have hEq : (⨅ i, K i).toSubmodule.starProjection x = x - U.starProjection x := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · rw [hKi]
      exact Submodule.sub_starProjection_mem_orthogonal x
    · rw [sub_sub_cancel, hKi]
      exact U.le_orthogonal_orthogonal (U.starProjection_apply_mem x)
  rw [hEq]
  exact (tendsto_const_nhds (x := x)).sub hlim

variable {J : Type*}

/-- The common kernel of the bounded Mellin jets whose heights are at most T. -/
def heightJetKernel (height : J → ℝ) (eval : J → H →L[ℂ] ℂ) (T : ℝ) :
    ClosedSubmodule ℂ H :=
  ⨅ j : {j // height j ≤ T}, (⊥ : ClosedSubmodule ℂ ℂ).comap (eval j.val)

omit [CompleteSpace H] in
@[simp] theorem mem_heightJetKernel (height : J → ℝ) (eval : J → H →L[ℂ] ℂ)
    (T : ℝ) (u : H) :
    u ∈ heightJetKernel height eval T ↔ ∀ j, height j ≤ T → eval j u = 0 := by
  simp [heightJetKernel, Subtype.forall]

/-- The projections of (9.3.2.10) converge strongly to the projection onto
the common kernel of every selected jet. -/
theorem heightJetKernel_starProjection_tendsto (height : J → ℝ) (eval : J → H →L[ℂ] ℂ)
    (u : H) :
    Tendsto (fun T => (heightJetKernel height eval T).starProjection u) atTop
      (𝓝 ((⨅ j, (⊥ : ClosedSubmodule ℂ ℂ).comap (eval j)).starProjection u)) := by
  have hm : Antitone (heightJetKernel height eval) := by
    intro T₁ T₂ h u hu
    rw [mem_heightJetKernel] at hu ⊢
    exact fun j hj => hu j (hj.trans h)
  have hK : (⨅ T, heightJetKernel height eval T) =
      ⨅ j, (⊥ : ClosedSubmodule ℂ ℂ).comap (eval j) := by
    apply SetLike.ext
    intro v
    simp only [ClosedSubmodule.mem_iInf, mem_heightJetKernel, ClosedSubmodule.mem_comap,
      ClosedSubmodule.mem_bot]
    exact ⟨fun h j => h (height j) j le_rfl, fun h _ j _ => h j⟩
  simpa only [hK] using antitone_starProjection_tendsto _ hm u

/-- Strong convergence to the identity holds exactly when every included
jet vanishes identically. -/
theorem heightJetKernel_starProjection_tendsto_id_iff (height : J → ℝ)
    (eval : J → H →L[ℂ] ℂ) :
    (∀ u, Tendsto (fun T => (heightJetKernel height eval T).starProjection u)
      atTop (𝓝 u)) ↔ ∀ j, eval j = 0 := by
  let K : ClosedSubmodule ℂ H := ⨅ j, (⊥ : ClosedSubmodule ℂ ℂ).comap (eval j)
  constructor
  · intro h j
    ext v
    have he : K.starProjection v = v :=
      tendsto_nhds_unique (heightJetKernel_starProjection_tendsto height eval v) (h v)
    have hv := K.toSubmodule.starProjection_eq_self_iff.mp he
    exact ClosedSubmodule.mem_iInf.mp hv j
  · intro h u
    have hu : u ∈ K := by
      apply ClosedSubmodule.mem_iInf.mpr
      intro j
      change eval j u = 0
      rw [h j]
      rfl
    have he := K.toSubmodule.starProjection_eq_self_iff.mpr hu
    have ht := heightJetKernel_starProjection_tendsto height eval u
    change Tendsto _ _ (𝓝 (K.starProjection u)) at ht
    rwa [show K.starProjection u = u from he] at ht

section Mellin

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CommGroup K]
  (μ : Measure K) [IsFiniteMeasure μ]

private abbrev Strip (a b s : ℝ) := Lp ℂ 2 (μ.prod (stripMeasure a b s))

private def fullRadialSupport (a b s : ℝ) :
    Strip μ a b s →L[ℂ] lpTwoRadialSupport μ (stripMeasure a b s) univ :=
  (ContinuousLinearMap.id ℂ _).codRestrict _ (fun u => by
    change ∀ᵐ p ∂μ.prod (stripMeasure a b s), p.2 ∉ univ → u p = 0
    simp)

/-- The continuous evaluations selected for the corrected height cutoff.
All Mellin jets at interior zeros are included. At the boundary the
reciprocal-weight integrability criterion selects the bounded jets. -/
def BoundedStripMellinJet (a b s : ℝ) (L : ℂ → ℂ) :=
  {p : ℂ × ℕ // L p.1 = 0 ∧ p.2 < analyticOrderNatAt L p.1 ∧
    MemLp (mellinEvaluationKernel p.2 p.1) 2 (stripMeasure (-a) (-b) (-s))}

theorem mem_boundedStripMellinJet_of_interior {a b s : ℝ} (hs : 0 ≤ s)
    {L : ℂ → ℂ} {z : ℂ} (hz : L z = 0) {n : ℕ} (hn : n < analyticOrderNatAt L z)
    (hz' : z.re ∈ Ioo a b) :
    ∃ j : BoundedStripMellinJet a b s L, j.val = (z, n) :=
  ⟨⟨(z, n), hz, hn, (mellinEvaluationKernel_memLp_iff hz'.1.le hz'.2.le hs n).mpr
      (Or.inl hz')⟩, rfl⟩

private theorem stripMellinJet_exists (a b s : ℝ) (χ : PontryaginDual K)
    (L : ℂ → ℂ) (j : BoundedStripMellinJet a b s L) :
    ∃ F : Strip μ a b s →L[ℂ] ℂ, ∀ u,
      F u = modulatedIntervalMoment μ a b s χ (fullRadialSupport μ a b s u) j.val.2 j.val.1 := by
  have hj : MemLp ((univ : Set ℝ).indicator (mellinEvaluationKernel j.val.2 j.val.1))
      2 (stripMeasure (-a) (-b) (-s)) := by simpa only [indicator_univ] using j.property.2.2
  obtain ⟨A, hA, _⟩ :=
    modulatedInterval_mellinMoment_of_kernel μ a b s isOpen_univ χ j.val.2 j.val.1 hj
  exact ⟨A.comp (fullRadialSupport μ a b s), fun u => (hA _).2⟩

/-- Evaluation of a bounded logarithmic moment on the full weighted Hilbert space. -/
def stripMellinJet (a b s : ℝ) (χ : PontryaginDual K)
    (L : ℂ → ℂ) (j : BoundedStripMellinJet a b s L) : Strip μ a b s →L[ℂ] ℂ :=
  (stripMellinJet_exists μ a b s χ L j).choose

theorem stripMellinJet_apply (a b s : ℝ) (χ : PontryaginDual K)
    (L : ℂ → ℂ) (j : BoundedStripMellinJet a b s L) (u : Strip μ a b s) :
    stripMellinJet μ a b s χ L j u =
      modulatedIntervalMoment μ a b s χ (fullRadialSupport μ a b s u) j.val.2 j.val.1 :=
  (stripMellinJet_exists μ a b s χ L j).choose_spec u

/-- Corrected Theorem 9.3.2.6 on the full modulated Hardy–Sobolev space.
The projections converge in the strong operator topology to the common
kernel projection of the bounded Mellin jets. -/
theorem hardySobolevMellin_heightProjections_tendsto (a b s : ℝ) (χ : PontryaginDual K)
    (L : ℂ → ℂ) (u : Strip μ a b s) :
    Tendsto (fun T =>
      (heightJetKernel (fun j : BoundedStripMellinJet a b s L => |j.val.1.im|)
        (stripMellinJet μ a b s χ L) T).starProjection u) atTop
      (𝓝 ((⨅ j, (⊥ : ClosedSubmodule ℂ ℂ).comap
        (stripMellinJet μ a b s χ L j)).starProjection u)) :=
  heightJetKernel_starProjection_tendsto _ _ u

/-- The source conclusion on the same space holds precisely when the
weighted Mellin jet family contains no nonzero functional. -/
theorem hardySobolevMellin_heightProjections_tendsto_id_iff (a b s : ℝ) (χ : PontryaginDual K)
    (L : ℂ → ℂ) :
    (∀ u : Strip μ a b s, Tendsto (fun T =>
      (heightJetKernel (fun j : BoundedStripMellinJet a b s L => |j.val.1.im|)
        (stripMellinJet μ a b s χ L) T).starProjection u) atTop (𝓝 u)) ↔
      ∀ j, stripMellinJet μ a b s χ L j = 0 :=
  heightJetKernel_starProjection_tendsto_id_iff _ _

omit [BorelSpace K] [IsFiniteMeasure μ] in
/-- The constant character has a test of Mellin value one at the origin. -/
private theorem stripMellinMoment_zero_surjective [IsProbabilityMeasure μ]
    (a b s : ℝ) :
    ∃ u : Strip μ a b s,
      modulatedIntervalMoment μ a b s 1 (fullRadialSupport μ a b s u) 0 0 = 1 := by
  let A : Set (K × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  have hA : MeasurableSet A := MeasurableSet.univ.prod measurableSet_Icc
  have hmass : μ.prod (stripMeasure a b s) A ≠ ⊤ := by
    dsimp only [A]
    rw [Measure.prod_prod, measure_univ, one_mul]
    exact (stripMeasure_compact_lt_top a b s isCompact_Icc).ne
  let f : K × ℝ → ℂ := A.indicator (fun _ => 1)
  have hf : MemLp f 2 (μ.prod (stripMeasure a b s)) :=
    memLp_indicator_const 2 hA 1 (Or.inr hmass)
  refine ⟨hf.toLp f, ?_⟩
  have hac : μ.prod (volume : Measure ℝ) ≪ μ.prod (stripMeasure a b s) :=
    Measure.AbsolutelyContinuous.rfl.prod
      (absolutelyContinuous_amplitudeMeasure volume _ (stripSobolevAmplitude_continuous a b s).measurable
        (stripSobolevAmplitude_pos a b s))
  have hae : (fun p : K × ℝ => (fullRadialSupport μ a b s (hf.toLp f)).val p) =ᵐ[μ.prod volume] f :=
    hac.ae_le hf.coeFn_toLp
  have hkernel (x : ℝ) : mellinEvaluationKernel 0 0 x = 1 := by
    simp [mellinEvaluationKernel]
  have hχ (k : K) : ((1 : PontryaginDual K) k : ℂ) = 1 := rfl
  unfold modulatedIntervalMoment
  simp only [hkernel, hχ, one_mul, mul_one]
  rw [integral_congr_ae hae]
  have hm : μ.prod (volume : Measure ℝ) A = 1 := by
    simp [A, Measure.prod_prod, Real.volume_Icc]
  change (∫ p, A.indicator (fun _ => (1 : ℂ)) p ∂μ.prod volume) = 1
  rw [integral_indicator_const 1 hA, measureReal_def, hm, ENNReal.toReal_one, one_smul]

/-- The Gaussian difference from the zero-count counterexample has an
interior Mellin zero. Its height projections fail to converge to the identity. -/
theorem hardySobolevMellin_gaussian_identity_limit_fails [IsProbabilityMeasure μ] :
    let L : ℂ → ℂ := mellin (fun t => zeroCountGaussianTest (Real.log t))
    ¬ ∀ u : Strip μ (-1) 1 0, Tendsto (fun T =>
      (heightJetKernel (fun j : BoundedStripMellinJet (-1) 1 0 L => |j.val.1.im|)
        (stripMellinJet μ (-1) 1 0 1 L) T).starProjection u) atTop (𝓝 u) := by
  intro L
  have he : L = fun z : ℂ => Complex.exp (z ^ 2) * Complex.sin (z ^ 2) :=
    funext zeroCountGaussianTest_mellin
  have hL (z : ℂ) : AnalyticAt ℂ L z := by
    rw [he]
    have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ 2) z := analyticAt_id.pow 2
    exact hpow.cexp'.mul (Complex.analyticAt_sin.comp hpow)
  have hzero : L 0 = 0 := by simp [he]
  have hfinite : analyticOrderAt L 0 ≠ ⊤ := by
    intro h
    have h' := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 hL).mp h
    exact zeroCountGaussianTest_mellin_ne_zero (congrFun h' _)
  have horder : 0 < analyticOrderNatAt L 0 :=
    ENat.toNat_pos ((hL 0).analyticOrderAt_ne_zero.mpr hzero) hfinite
  obtain ⟨j, hj⟩ := mem_boundedStripMellinJet_of_interior (a := -1) (b := 1)
    (by norm_num : (0 : ℝ) ≤ 0) hzero horder (by norm_num)
  obtain ⟨u, hu⟩ := stripMellinMoment_zero_surjective μ (-1) 1 0
  intro hid
  have hjzero := (hardySobolevMellin_heightProjections_tendsto_id_iff
    μ (-1) 1 0 1 L).mp hid j
  have hz : stripMellinJet μ (-1) 1 0 1 L j u = 0 := by rw [hjzero]; rfl
  rw [stripMellinJet_apply, hj] at hz
  exact one_ne_zero (hu.symm.trans hz)

end Mellin

end

end Masullo
