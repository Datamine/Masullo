import ArchimedeanStandardNormProfile
import AdelicTheta

open Filter Function MeasureTheory NumberField NumberField.Units.dirichletUnitTheorem Set Topology
open scoped SchwartzMap NumberField Classical

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Tests := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

variable [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
  (μ : Measure (archNormOne F)) [μ.IsHaarMeasure]
  {J : Type*} [Fintype J] (r : J → InfiniteIdeles F) (χ : InfiniteIdeles F →ₜ* Circle)

/-- The character-weighted archimedean norm-one average of (6.2.2.3). -/
def archStandardThetaAverage (f : Tests F) (x : InfiniteIdeles F) : ℂ :=
  ∑ j, ∫ g : archNormOne F,
    f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * (χ (r j * g.val) : ℂ) ∂μ

/-- The average is jointly continuous in the Schwartz test and the idele.
A fixed integrable fibre kernel dominates a neighborhood of any pair. -/
theorem archStandardThetaAverage_jointContinuous :
    Continuous (fun p : Tests F × InfiniteIdeles F => archStandardThetaAverage F μ r χ p.1 p.2) := by
  letI : FirstCountableTopology (Tests F) :=
    (schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).firstCountableTopology
  letI : FirstCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isInducing.firstCountableTopology
  letI : FirstCountableTopology (InfiniteAdeleRing F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  letI : FirstCountableTopology (InfiniteIdeles F) := Units.isInducing_embedProduct.firstCountableTopology
  unfold archStandardThetaAverage
  apply continuous_finsetSum
  intro j _
  apply continuous_iff_continuousAt.mpr
  intro p
  let A (q : Tests F × InfiniteIdeles F) (g : archNormOne F) :=
    q.1 (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * q.2).val) * (χ (r j * g.val) : ℂ)
  let y := (r j)⁻¹ * p.2
  let K (g : archNormOne F) := archimedeanLogFibreKernel (max 0 (-Real.log ‖y.val‖))
    (fun w : {w : InfinitePlace F // w ≠ w₀} => fullArchLog F y w - (archRegulatorLog F g).toAdd w)
  obtain ⟨_, _, hK⟩ := archNormOne_logFibreKernel_integral F μ
  have hKi : Integrable K μ := (hK y).1
  let P := archLogFibreSchwartzControl F 0
  have hP : Continuous P :=
    ((schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).continuous_seminorm (0, 0)).max
      ((schwartz_withSeminorms ℂ (mixedEmbedding.mixedSpace F) ℂ).continuous_seminorm
        (2 * (Fintype.card (InfinitePlace F) * (0 + 1)), 0))
  let D := P p.1 + 1
  have hD : 0 ≤ D := add_nonneg ((apply_nonneg _ p.1).trans (le_max_left _ _)) zero_le_one
  have hPnear : ∀ᶠ q : Tests F × InfiniteIdeles F in 𝓝 p, P q.1 ≤ D :=
    ((hP.comp continuous_fst).continuousAt (x := p)).eventually
      (Iic_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
  have hLnear : ∀ᶠ q : Tests F × InfiniteIdeles F in 𝓝 p,
      ∀ w : InfinitePlace F, |fullArchLog F q.2 w - fullArchLog F p.2 w| ≤ 1 := by
    apply eventually_all.mpr
    intro w
    have h := ((fullArchLog_coordinate_continuous F w).comp continuous_snd).continuousAt (x := p)
    exact (h.eventually (Metric.ball_mem_nhds _ zero_lt_one)).mono fun q hq =>
      (by simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_def] using hq :
        |fullArchLog F q.2 w - fullArchLog F p.2 w| < 1).le
  have hInt (q : Tests F × InfiniteIdeles F) : Integrable (A q) μ := by
    obtain ⟨_, _, h⟩ := archNormOne_standardAverage_logBound F μ r χ q.1
    exact (h q.2).1 j
  have hCont (g : archNormOne F) : Continuous (fun q => A q g) := by
    let e : InfiniteIdeles F → mixedEmbedding.mixedSpace F :=
      fun x => InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val
    have he : Continuous e := (infiniteAdele_toMixed_continuous F).comp
      (Units.continuous_val.comp (continuous_const.mul continuous_id))
    let L := SchwartzMap.toBoundedContinuousFunctionCLM ℂ (mixedEmbedding.mixedSpace F) ℂ
    have hEval : Continuous (fun q : Tests F × InfiniteIdeles F => L q.1 (e q.2)) :=
      (continuous_eval : Continuous (fun p : BoundedContinuousFunction (mixedEmbedding.mixedSpace F) ℂ ×
        mixedEmbedding.mixedSpace F => p.1 p.2)).comp
          ((L.continuous.comp continuous_fst).prodMk (he.comp continuous_snd))
    exact hEval.mul_const (χ (r j * g.val) : ℂ)
  let n := Fintype.card (InfinitePlace F)
  refine continuousAt_of_dominated (F := A) (bound := fun g => D * Real.exp 1 ^ n * K g)
    (.of_forall fun q => (hInt q).aestronglyMeasurable) ?_ (hKi.const_mul _) (.of_forall fun g => (hCont g).continuousAt)
  filter_upwards [hPnear, hLnear] with q hPq hLq
  exact .of_forall fun g => by
    let b := (r j * g.val)⁻¹
    have he (w : InfinitePlace F) : |fullArchLog F (b * q.2) w - fullArchLog F (b * p.2) w| ≤ 1 := by
      rw [fullArchLog_mul, fullArchLog_mul]
      change |(fullArchLog F b w + fullArchLog F q.2 w) - (fullArchLog F b w + fullArchLog F p.2 w)| ≤ 1
      rw [add_sub_add_left_eq_sub]
      exact hLq w
    have hs : (∏ w, min 1 (Real.exp (-fullArchLog F (b * q.2) w))) ≤
        Real.exp 1 ^ n * ∏ w, min 1 (Real.exp (-fullArchLog F (b * p.2) w)) := by
      rw [show Real.exp 1 ^ n = ∏ _w : InfinitePlace F, Real.exp 1 by simp [n], ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun _ _ => le_min zero_le_one (Real.exp_pos _).le)
        (fun w _ => archLogFactor_le_of_shift (he w))
    have hb : (∏ w, min 1 (Real.exp (-fullArchLog F (b * p.2) w))) ≤ K g := by
      rw [show b * p.2 = g.val⁻¹ * y by simp only [b, y, mul_inv_rev, mul_assoc]]
      exact archLogFibre_product_le_kernel F y g
    have hq := archSchwartz_fullArchLog_weighted_le F 0 q.1 (b * q.2)
    simp only [Nat.cast_zero, zero_mul, Real.exp_zero, one_mul] at hq
    change ‖q.1 (InfiniteAdeleRing.ringEquiv_mixedSpace F (b * q.2).val) * (χ (r j * g.val) : ℂ)‖ ≤ _
    rw [norm_mul, Circle.norm_coe, mul_one]
    calc
      _ ≤ P q.1 * ∏ w, min 1 (Real.exp (-fullArchLog F (b * q.2) w)) := hq
      _ ≤ D * ∏ w, min 1 (Real.exp (-fullArchLog F (b * q.2) w)) :=
        mul_le_mul_of_nonneg_right hPq (Finset.prod_nonneg fun _ _ => le_min zero_le_one (Real.exp_pos _).le)
      _ ≤ D * (Real.exp 1 ^ n * ∏ w, min 1 (Real.exp (-fullArchLog F (b * p.2) w))) :=
        mul_le_mul_of_nonneg_left hs hD
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- The archimedean standard average is a continuous linear operator to
the compact-open space of continuous functions on the archimedean ideles. -/
def archStandardThetaAverageCLM : Tests F →L[ℂ] C(InfiniteIdeles F, ℂ) := by
  let L (f : Tests F) : C(InfiniteIdeles F, ℂ) :=
    ⟨archStandardThetaAverage F μ r χ f, (archStandardThetaAverage_jointContinuous F μ r χ).comp
      (continuous_const.prodMk continuous_id)⟩
  have hi (f : Tests F) (x : InfiniteIdeles F) (j : J) : Integrable (fun g : archNormOne F =>
      f (InfiniteAdeleRing.ringEquiv_mixedSpace F ((r j * g.val)⁻¹ * x).val) * (χ (r j * g.val) : ℂ)) μ := by
    obtain ⟨_, _, h⟩ := archNormOne_standardAverage_logBound F μ r χ f
    exact (h x).1 j
  refine ⟨{ toFun := L, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f h
    ext x
    change archStandardThetaAverage F μ r χ (f + h) x =
      archStandardThetaAverage F μ r χ f x + archStandardThetaAverage F μ r χ h x
    simp only [archStandardThetaAverage, add_apply, add_mul,
      integral_add (hi f x _) (hi h x _), Finset.sum_add_distrib]
  · intro c f
    ext x
    change archStandardThetaAverage F μ r χ (c • f) x = c * archStandardThetaAverage F μ r χ f x
    simp only [archStandardThetaAverage, smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul, Finset.mul_sum]
  · change Continuous L
    exact ContinuousMap.continuous_of_continuous_uncurry _ (archStandardThetaAverage_jointContinuous F μ r χ)

theorem archStandardThetaAverage_isClosed_ker :
    IsClosed ((archStandardThetaAverageCLM F μ r χ).ker : Set (Tests F)) :=
  (archStandardThetaAverageCLM F μ r χ).isClosed_ker

theorem archStandardThetaAverage_normRay (f : Tests F) (t : ℝ) :
    archStandardThetaAverageCLM F μ r χ f (archNormRay F t) =
      archStandardNormProfile F μ r χ f t := rfl

end
end Masullo
