import ModulatedSobolevContinuity

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "Angular" => m.toMonoidHom.ker
local notation "Profiles" => (modulatedExponentialProfiles (K := Angular))

/-- The actual group function obtained by evaluating the radial and compact profile. -/
def modulatedGroupProfile (f : Profiles) : C(G, ℂ) where
  toFun g := modulatedProfileFunction f ((Homeomorph.prodComm _ _)
    ((modulatedLogSplit m τ hτ).symm g))
  continuous_toFun := (modulatedExponentialProfile_jointContinuous f).comp
    ((Homeomorph.prodComm _ _).continuous.comp (modulatedLogSplit m τ hτ).symm.continuous)

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem modulatedGroupProfile_onSplit (f : Profiles) (x : ℝ) (k : Angular) :
    modulatedGroupProfile m τ hτ f (τ (Multiplicative.ofAdd x) * k.val) = f.val x k := by
  let e := modulatedLogSplit m τ hτ
  change modulatedProfileFunction f ((Homeomorph.prodComm _ _) (e.symm (e (x, k)))) = _
  rw [e.symm_apply_apply]
  rfl

/-- A continuous group test with the radial estimates supplied by each
Schwartz–Bruhat stage has the expected split exponential profile. -/
theorem modulatedGroupProfile_of_stageEstimates (f : C(G, ℂ))
    (hf : ∀ b : ℝ, HasUniformRadialSchwartzDerivatives
      (fun p : ℝ × Angular => (Real.exp (b * p.1) : ℂ) * f ((modulatedLogSplit m τ hτ) p))) :
    ∃ u : Profiles, modulatedGroupProfile m τ hτ u = f := by
  let e := modulatedLogSplit m τ hτ
  let F := curryCompactProfile (fun p => f (e p)) (f.continuous.comp e.continuous)
  have hF : F ∈ Profiles := modulatedExponentialProfile_of_stageEstimates F hf
  refine ⟨⟨F, hF⟩, ContinuousMap.ext (fun g => ?_)⟩
  obtain ⟨⟨x, k⟩, rfl⟩ := e.surjective g
  exact modulatedGroupProfile_onSplit m τ hτ ⟨F, hF⟩ x k

variable (μ : Measure m.toMonoidHom.ker) [IsFiniteMeasure μ]
include μ

/-- Send physical group tests into the completion for the actual weighted Haar measure. -/
def modulatedGroupProfile_inclusion (b : ℝ) (N : ℕ) : Profiles →ₗ[ℂ] (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ)))) :=
  (modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))).symm.toLinearMap.comp
    (modulatedExponentialProfile_inclusion μ b N)

theorem modulatedGroupProfile_inclusion_ae (b : ℝ) (N : ℕ) (f : Profiles) :
    (modulatedGroupProfile_inclusion m τ hτ μ b N f : G → ℂ)
      =ᵐ[modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ))] modulatedGroupProfile m τ hτ f := by
  let e := modulatedLogSplit m τ hτ
  let ν := stripMeasure b b (2 * (N : ℝ))
  let J := modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))
  let u := modulatedGroupProfile_inclusion m τ hτ μ b N f
  have he : MeasurePreserving e (ν.prod μ) (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ))) :=
    ⟨e.continuous.measurable, rfl⟩
  have hJu : J u = modulatedExponentialProfile_inclusion μ b N f := J.apply_symm_apply _
  have hA : ∀ᵐ p ∂μ.prod ν, u (e (p.2, p.1)) = modulatedGroupProfile m τ hτ f (e (p.2, p.1)) := by
    have h := modulatedSobolevGroupEquiv_ae m τ hτ μ b (2 * (N : ℝ)) u
    change (J u : Angular × ℝ → ℂ) =ᵐ[μ.prod ν] _ at h
    rw [hJu] at h
    filter_upwards [h, modulatedExponentialProfile_toLp_ae μ b N f] with p hp hq
    change modulatedExponentialProfile_inclusion μ b N f p = u (e (p.2, p.1)) at hp
    rw [← hp, show modulatedExponentialProfile_inclusion μ b N f p = f.val p.2 p.1 from hq]
    exact (modulatedGroupProfile_onSplit m τ hτ f p.2 p.1).symm
  have hB := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hA
  have hback := (he.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hB
  filter_upwards [hback] with g hg
  have hg' : u (e (e.symm g)) = modulatedGroupProfile m τ hτ f (e (e.symm g)) := hg
  simpa only [e.apply_symm_apply] using hg'


/-- With Haar measure on the compact kernel, the weighted test norm
separates the actual continuous group profiles. -/
theorem modulatedGroupProfile_inclusion_injective [μ.IsOpenPosMeasure] (b : ℝ) (N : ℕ) :
    Injective (modulatedGroupProfile_inclusion m τ hτ μ b N) := by
  intro f g hfg
  let ν := stripMeasure b b (2 * (N : ℝ))
  let J := modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))
  have hEqual :
      modulatedExponentialProfile_toLp μ b N f = modulatedExponentialProfile_toLp μ b N g :=
    J.symm.injective hfg
  have hAE : (fun p : Angular × ℝ => f.val p.2 p.1) =ᵐ[μ.prod ν]
      fun p => g.val p.2 p.1 := by
    have h := modulatedExponentialProfile_toLp_ae μ b N g
    rw [← hEqual] at h
    exact (modulatedExponentialProfile_toLp_ae μ b N f).symm.trans h
  have hν : (volume : Measure ℝ) ≪ ν :=
    absolutelyContinuous_amplitudeMeasure volume _
      (stripSobolevAmplitude_continuous b b (2 * (N : ℝ))).measurable
      (stripSobolevAmplitude_pos b b (2 * (N : ℝ)))
  have hbase : μ.prod (volume : Measure ℝ) ≪ μ.prod ν :=
    Measure.AbsolutelyContinuous.rfl.prod hν
  have heq := ((modulatedExponentialProfile_jointContinuous f).ae_eq_iff_eq
    (μ.prod (volume : Measure ℝ)) (modulatedExponentialProfile_jointContinuous g)).mp
      (hbase.ae_le hAE)
  exact Subtype.ext (funext fun x => ContinuousMap.ext (fun k => congrFun heq (k, x)))

/-- The full physical group tests are dense in the weighted Haar space. -/
theorem modulatedGroupProfile_dense [μ.WeaklyRegular] (b : ℝ) (N : ℕ) :
    DenseRange (modulatedGroupProfile_inclusion m τ hτ μ b N) := by
  let J := (modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))).symm
  exact J.surjective.denseRange.comp (modulatedExponentialProfile_dense μ b N) J.continuous

/-- The strict-support group tests into the group cutoff subspace. -/
def modulatedGroupProfile_cutoffInclusion (b : ℝ) (N : ℕ) (U : Set ℝ) :
    modulatedExponentialProfileCutoff (K := Angular) U →ₗ[ℂ]
      modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) U :=
  (modulatedGroupCutoffEquiv m τ hτ μ b (2 * (N : ℝ)) U).symm.toLinearMap.comp
    (modulatedExponentialProfile_cutoffInclusion μ b N U)

theorem modulatedGroupProfile_cutoffInclusion_val (b : ℝ) (N : ℕ) (U : Set ℝ)
    (f : modulatedExponentialProfileCutoff (K := Angular) U) :
    (modulatedGroupProfile_cutoffInclusion m τ hτ μ b N U f).val =
      modulatedGroupProfile_inclusion m τ hτ μ b N f.val := by
  let J := modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))
  let E := modulatedGroupCutoffEquiv m τ hτ μ b (2 * (N : ℝ)) U
  let w := modulatedExponentialProfile_cutoffInclusion μ b N U f
  apply J.injective
  change (E (E.symm w)).val = J (J.symm w.val)
  rw [E.apply_symm_apply, J.apply_symm_apply]

theorem modulatedGroupProfile_cutoff_dense [μ.WeaklyRegular] (b : ℝ) (N : ℕ) {U : Set ℝ}
    (hU : IsOpen U) : DenseRange (modulatedGroupProfile_cutoffInclusion m τ hτ μ b N U) := by
  let J := (modulatedGroupCutoffEquiv m τ hτ μ b (2 * (N : ℝ)) U).symm
  exact J.surjective.denseRange.comp (modulatedExponentialProfile_cutoff_dense μ b N hU) J.continuous

/-- The full weighted group Mellin transform, as an isometric isomorphism. -/
def modulatedGroupFullMellin (b : ℝ) (N : ℕ) : (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ)))) ≃ₗᵢ[ℂ]
    Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) :=
  (modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))).trans (modulatedMellinLineEquiv μ b N)

theorem modulatedGroupFullMellin_onProfile (b : ℝ) (N : ℕ) (f : Profiles) :
    modulatedGroupFullMellin m τ hτ μ b N (modulatedGroupProfile_inclusion m τ hτ μ b N f) =
      modulatedMellinLineEquiv μ b N (modulatedExponentialProfile_inclusion μ b N f) := by
  let J := modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))
  change modulatedMellinLineEquiv μ b N (J (J.symm _)) = _
  rw [J.apply_symm_apply]

/-- The completed group Mellin transform agrees on tests with the actual
integral against each compact character and the scalar Mellin line test. -/
theorem modulatedGroupFullMellin_character_onProfile (b : ℝ) (N : ℕ)
    (χ : PontryaginDual Angular) (f : Profiles) :
    (modulatedMellinLineCharacter μ b N χ
      (modulatedGroupFullMellin m τ hτ μ b N (modulatedGroupProfile_inclusion m τ hτ μ b N f)) :
      MellinTraceHilbert N) =
        mellinLineTest b N (modulatedExponentialProfile_character μ χ f) := by
  rw [modulatedGroupFullMellin_onProfile]
  exact modulatedMellinLineCharacter_onProfile μ b N χ f

/-- The actual group test inclusion is continuous whenever the radial Schwartz
twist is continuous on the test stage. -/
theorem modulatedGroupProfile_inclusion_continuous {A : Type*} [TopologicalSpace A]
    (b : ℝ) (N : ℕ) (f : A → Profiles) (hf : Continuous (fun a => modulatedProfileTwist b (f a))) :
    Continuous (fun a => modulatedGroupProfile_inclusion m τ hτ μ b N (f a)) :=
  (modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))).symm.continuous.comp
    (modulatedExponentialProfile_inclusion_continuous μ b N f hf)

/-- The physical strict-support tests have exactly the indicated closure in
the ambient weighted group space. -/
theorem modulatedGroupProfile_cutoffClosure [μ.WeaklyRegular] (b : ℝ) (N : ℕ)
    {U : Set ℝ} (hU : IsOpen U) :
    closure (range (fun f : modulatedExponentialProfileCutoff (K := Angular) U =>
      modulatedGroupProfile_inclusion m τ hτ μ b N f.val)) =
      (modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) U :
        Set (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ))))) := by
  let S := modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) U
  let J := modulatedSobolevGroupEquiv m τ hτ μ b (2 * (N : ℝ))
  have hS : IsClosed (S : Set (Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ))))) := by
    obtain ⟨_, hClosed, _⟩ := modulatedSobolev_radialProjection μ b (2 * (N : ℝ)) hU
    exact hClosed.preimage J.continuous
  let A := modulatedGroupProfile_cutoffInclusion m τ hτ μ b N U
  have hcomp : (fun f : modulatedExponentialProfileCutoff (K := Angular) U =>
      modulatedGroupProfile_inclusion m τ hτ μ b N f.val) = Subtype.val ∘ A :=
    funext fun f => (modulatedGroupProfile_cutoffInclusion_val m τ hτ μ b N U f).symm
  have hEmb : IsClosedEmbedding ((↑) : S → Lp ℂ 2
      (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ)))) := hS.isClosedEmbedding_subtypeVal
  rw [hcomp, range_comp]
  calc
    _ = (Subtype.val : S → _) '' closure (range A) := hEmb.closure_image_eq _
    _ = _ := by
      rw [(modulatedGroupProfile_cutoff_dense m τ hτ μ b N hU).closure_range, image_univ]
      exact Subtype.range_coe

omit [T2Space G] [CompactSpace m.toMonoidHom.ker] [IsFiniteMeasure μ] in
/-- Every individual logarithmic fiber has zero weighted Haar measure. -/
theorem modulatedGroupLog_ae_ne (b s c : ℝ) :
    ∀ᵐ g ∂modulatedSobolevMeasure m τ hτ μ b s, modulatedLog m g ≠ c := by
  let ν := stripMeasure b b s
  let e := modulatedLogSplit m τ hτ
  have he : MeasurePreserving e (ν.prod μ) (modulatedSobolevMeasure m τ hτ μ b s) :=
    ⟨e.continuous.measurable, rfl⟩
  have ha : ∀ᵐ x ∂ν, x ≠ c :=
    (amplitudeMeasure_absolutelyContinuous (volume : Measure ℝ)
      (stripSobolevAmplitude b b s)).ae_le ((volume : Measure ℝ).ae_ne c)
  have hp := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae ha
  have heq (p : ℝ × Angular) : modulatedLog m (e p) = p.1 := by
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.1) * p.2.val)) = _
    rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one]
    rfl
  have hs := (he.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hp
  filter_upwards [hs] with g hg
  change (e.symm g).1 ≠ c at hg
  rw [← heq, e.apply_symm_apply] at hg
  exact hg

/-- The physical lower-cutoff closure is the range of multiplication by
the closed-ray indicator in Theorem 9.2.1.5(1). -/
theorem modulatedGroupProfile_lowerIndicator [μ.WeaklyRegular] (b : ℝ) (N : ℕ) (c : ℝ) :
    let W := modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ))
    ∃ P : Lp ℂ 2 W →L[ℂ] Lp ℂ 2 W,
      IsClosed (range P) ∧ (∀ u, P (P u) = P u) ∧
      (∀ u, (P u : G → ℂ) =ᵐ[W] (modulatedLog m ⁻¹' Ici c).indicator (u : G → ℂ)) ∧
      closure (range (fun f : modulatedExponentialProfileCutoff (K := Angular) (Ioi c) =>
        modulatedGroupProfile_inclusion m τ hτ μ b N f.val)) = range P := by
  intro W
  let U := modulatedLog m ⁻¹' Ici c
  have hm : Measurable (modulatedLog m) := (continuous_toAdd.comp m.continuous).measurable
  obtain ⟨P, hPclosed, _, hP⟩ := lpTwo_measurableCutoff (μ := W) (hm measurableSet_Ici)
  refine ⟨P, hPclosed, fun u => (hP u).1, fun u => (hP u).2, ?_⟩
  rw [modulatedGroupProfile_cutoffClosure m τ hτ μ b N isOpen_Ioi]
  ext u
  rw [show u ∈ (modulatedGroupCutoff m τ hτ μ b (2 * (N : ℝ)) (Ioi c) : Set (Lp ℂ 2 W)) ↔
    ∀ᵐ g ∂W, modulatedLog m g ∉ Ioi c → u g = 0 from
    modulatedGroupCutoff_mem_iff m τ hτ μ b (2 * (N : ℝ)) (Ioi c) u]
  have hnull := modulatedGroupLog_ae_ne m τ hτ μ b (2 * (N : ℝ)) c
  constructor
  · intro hu
    refine ⟨u, Lp.ext ?_⟩
    filter_upwards [hu, (hP u).2] with g hg hp
    by_cases hh : g ∈ U
    · exact hp.trans (indicator_of_mem hh _)
    · have hn : modulatedLog m g ∉ Ioi c := fun h =>
        hh (show c ≤ modulatedLog m g from le_of_lt (show c < modulatedLog m g from h))
      exact hp.trans ((indicator_of_notMem hh _).trans (hg hn).symm)
  · rintro ⟨v, rfl⟩
    filter_upwards [hnull, (hP v).2] with g hn hp hg
    have hx : g ∉ U := fun h =>
      hg (lt_of_le_of_ne (show c ≤ modulatedLog m g from h) (Ne.symm hn))
    exact hp.trans (indicator_of_notMem hx _)

end
end Masullo
