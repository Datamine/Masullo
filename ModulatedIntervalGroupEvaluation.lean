import ModulatedIntervalEvaluation
import ModulatedJumpPoisson

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (μ : Measure m.toMonoidHom.ker) [IsFiniteMeasure μ]

local notation "Angular" => m.toMonoidHom.ker

/-- The physical interval-weighted measure and its comparison with split
coordinates for an arbitrary compact base. -/
theorem modulatedInterval_weightedHaar_split {a b s : ℝ} (hab : a ≤ b) :
    Measure.map (modulatedLogSplit m τ hτ) ((stripMeasure a b s).prod μ) =
      hardySobolevMeasure (modulatedLogMeasure m τ hτ μ) (modulatedLog m) a b s := by
  let e := modulatedLogSplit m τ hτ
  let w (x : ℝ) := (stripSobolevAmplitude a b s x ^ 2 : ℝ)
  have hw : Measurable (fun x => ENNReal.ofReal (w x)) :=
    ((stripSobolevAmplitude_continuous a b s).measurable.pow_const 2).ennreal_ofReal
  have hm : Measurable (modulatedLog m) := (continuous_toAdd.comp m.continuous).measurable
  have hlog (p : ℝ × Angular) : modulatedLog m (e p) = p.1 := by
    change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.1) * p.2.val)) = p.1
    rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one]
    rfl
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ g, f g ∂Measure.map e ((volume.withDensity fun x => ENNReal.ofReal (w x)).prod μ)) =
    ∫⁻ g, f g ∂(Measure.map e (volume.prod μ)).withDensity
      (fun g => ENNReal.ofReal (hardySobolevWeight a b s (modulatedLog m g)))
  simp_rw [← stripSobolevAmplitude_sq hab]
  change (∫⁻ g, f g ∂Measure.map e ((volume.withDensity fun x => ENNReal.ofReal (w x)).prod μ)) =
    ∫⁻ g, f g ∂(Measure.map e (volume.prod μ)).withDensity
      (fun g => ENNReal.ofReal (w (modulatedLog m g)))
  have he := e.continuous.measurable
  rw [prod_withDensity_left hw, lintegral_map hf he,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun p : ℝ × Angular => ENNReal.ofReal (w p.1)) from hw.comp measurable_fst)
      (show Measurable (fun p : ℝ × Angular => f (e p)) from hf.comp he),
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun g => ENNReal.ofReal (w (modulatedLog m g))) from hw.comp hm) hf,
    lintegral_map
      (show Measurable ((fun g => ENNReal.ofReal (w (modulatedLog m g))) * f) from
        (hw.comp hm).mul hf) he]
  exact lintegral_congr fun p => by simp only [Pi.mul_apply, hlog]

def intervalGroupChart : (Angular × ℝ) ≃ₜ G :=
  (Homeomorph.prodComm Angular ℝ).trans (modulatedLogSplit m τ hτ)

theorem intervalGroupChart_preserving (v : Measure ℝ) [SFinite v] :
    MeasurePreserving (intervalGroupChart m τ hτ) (μ.prod v)
      (Measure.map (modulatedLogSplit m τ hτ) (v.prod μ)) :=
  (show MeasurePreserving (modulatedLogSplit m τ hτ) (v.prod μ)
    (Measure.map (modulatedLogSplit m τ hτ) (v.prod μ)) from
    ⟨(modulatedLogSplit m τ hτ).continuous.measurable, rfl⟩).comp Measure.measurePreserving_swap

omit [MeasurableSpace G] [BorelSpace G] in
theorem intervalGroupChart_log (p : Angular × ℝ) :
    modulatedLog m (intervalGroupChart m τ hτ p) = p.2 := by
  change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.2) * p.1.val)) = p.2
  rw [map_mul, hτ, show m p.1.val = 1 from p.1.property, mul_one]
  rfl

/-- Express the supported weighted class as a function on the actual group. -/
def modulatedIntervalGroupProfile (a b s : ℝ) {U : Set ℝ}
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) : G → ℂ :=
  u.val ∘ (intervalGroupChart m τ hτ).symm

theorem modulatedIntervalGroupProfile_memLp {a b s : ℝ} (hab : a ≤ b) {U : Set ℝ}
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) :
    MemLp (modulatedIntervalGroupProfile m τ hτ μ a b s u) 2
      (hardySobolevMeasure (modulatedLogMeasure m τ hτ μ) (modulatedLog m) a b s) := by
  let e := intervalGroupChart m τ hτ
  rw [← modulatedInterval_weightedHaar_split m τ hτ μ hab]
  have he := (intervalGroupChart_preserving m τ hτ μ (stripMeasure a b s)).map_eq
  rw [← he]
  apply e.toMeasurableEquiv.memLp_map_measure_iff.mpr
  change MemLp ((u.val : Angular × ℝ → ℂ) ∘ e.symm ∘ e) 2 _
  rw [show ((u.val : Angular × ℝ → ℂ) ∘ e.symm ∘ e) = u.val from
    funext fun p => congrArg (fun q => u.val q) (e.symm_apply_apply p)]
  exact Lp.memLp u.val

/-- Every supported class in the physical interval-weighted space has a
split profile, so the group integral formula covers the entire source space. -/
theorem exists_modulatedIntervalGroupProfile_ae {a b s : ℝ} (hab : a ≤ b) {U : Set ℝ}
    (f : Lp ℂ 2 (hardySobolevMeasure
      (modulatedLogMeasure m τ hτ μ) (modulatedLog m) a b s))
    (hf : ∀ᵐ g ∂hardySobolevMeasure (modulatedLogMeasure m τ hτ μ) (modulatedLog m) a b s,
      modulatedLog m g ∉ U → f g = 0) :
    ∃ u : lpTwoRadialSupport μ (stripMeasure a b s) U,
      (f : G → ℂ) =ᵐ[hardySobolevMeasure (modulatedLogMeasure m τ hτ μ) (modulatedLog m) a b s]
        modulatedIntervalGroupProfile m τ hτ μ a b s u := by
  let e := intervalGroupChart m τ hτ
  let W := hardySobolevMeasure (modulatedLogMeasure m τ hτ μ) (modulatedLog m) a b s
  have he : MeasurePreserving e (μ.prod (stripMeasure a b s)) W := by
    dsimp only [W]
    rw [← modulatedInterval_weightedHaar_split m τ hτ μ hab]
    exact intervalGroupChart_preserving m τ hτ μ (stripMeasure a b s)
  let v := Lp.compMeasurePreservingₗᵢ ℂ e he f
  have hv : (v : Angular × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure a b s)] f ∘ e :=
    Lp.coeFn_compMeasurePreserving f he
  have hsupport : v ∈ lpTwoRadialSupport μ (stripMeasure a b s) U := by
    filter_upwards [hv, he.quasiMeasurePreserving.ae hf] with p hp hz hU
    exact hp.trans (hz (intervalGroupChart_log m τ hτ p ▸ hU))
  refine ⟨⟨v, hsupport⟩, ?_⟩
  filter_upwards [(he.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hv] with g hg
  have hg' : v (e.symm g) = f (e (e.symm g)) := hg
  rw [e.apply_symm_apply] at hg'
  exact hg'.symm

/-- The physical moment uses the extension of the compact character that
is trivial on the chosen section. Its integral is the split moment and is
absolutely convergent whenever the reciprocal kernel is square integrable. -/
theorem modulatedIntervalMoment_onGroup (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (χ : PontryaginDual Angular) (k : ℕ) (z : ℂ)
    (hg : MemLp (U.indicator (mellinEvaluationKernel k z)) 2 (stripMeasure (-a) (-b) (-s)))
    (u : lpTwoRadialSupport μ (stripMeasure a b s) U) :
    let e := intervalGroupChart m τ hτ
    let f (g : G) := (χ (e.symm g).1 : ℂ) *
      modulatedIntervalGroupProfile m τ hτ μ a b s u g * mellinEvaluationKernel k z (modulatedLog m g)
    Integrable f (modulatedLogMeasure m τ hτ μ) ∧
      modulatedIntervalMoment μ a b s χ u k z = ∫ g, f g ∂modulatedLogMeasure m τ hτ μ := by
  intro e f
  have he : MeasurePreserving e (μ.prod (volume : Measure ℝ)) (modulatedLogMeasure m τ hτ μ) :=
    intervalGroupChart_preserving m τ hτ μ volume
  have hF (p : Angular × ℝ) : (f ∘ e) p =
      (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel k z p.2 := by
    have hlog := intervalGroupChart_log m τ hτ p
    change modulatedLog m (e p) = p.2 at hlog
    simp only [f, Function.comp_apply, hlog, e.symm_apply_apply]
    change (χ p.1 : ℂ) * u.val ((intervalGroupChart m τ hτ).symm (e p)) *
      mellinEvaluationKernel k z p.2 = _
    change (χ p.1 : ℂ) * u.val (e.symm (e p)) * mellinEvaluationKernel k z p.2 = _
    rw [e.symm_apply_apply]
  obtain ⟨L, hL, _⟩ := modulatedInterval_mellinMoment_of_kernel μ a b s hU χ k z hg
  refine ⟨(he.integrable_comp_emb e.toMeasurableEquiv.measurableEmbedding).mp
    ((hL u).1.congr (.of_forall fun p => (hF p).symm)), ?_⟩
  rw [← he.integral_comp e.toMeasurableEquiv.measurableEmbedding f]
  exact integral_congr_ae (.of_forall fun p => (hF p).symm)

end
end Masullo
