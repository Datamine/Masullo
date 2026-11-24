import SchwartzPartialIntegral

open Filter Function MeasureTheory Set
open scoped ContDiff SchwartzMap Topology

namespace Masullo

noncomputable section

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
  {μ : Measure T} [IsFiniteMeasure μ]

variable {A : T → X →L[ℝ] Y} (hA : Continuous A) (hIso : ∀ t x, ‖A t x‖ = ‖x‖)
  {w : T → ℂ} (hw : Continuous w) (hw₁ : ∀ t, ‖w t‖ ≤ 1)

private abbrev AverageJet (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => X) ℂ

private def averageJet (A : T → X →L[ℝ] Y) (w : T → ℂ) (f : 𝓢(Y, ℂ)) (n : ℕ)
    (x : X) (t : T) : AverageJet X n :=
  w t • (iteratedFDeriv ℝ n f (A t x)).compContinuousLinearMap (fun _ => A t)

omit [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T] in
private theorem averageJet_eq (f : 𝓢(Y, ℂ)) (n : ℕ) (x : X) (t : T) :
    averageJet A w f n x t = w t • iteratedFDeriv ℝ n (f ∘ A t) x := by
  change _ = w t • iteratedFDeriv ℝ n (f.toFun ∘ A t) x
  rw [(A t).iteratedFDeriv_comp_right f.smooth' x (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)]
  rfl

omit [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T] in
include hA hw in
private theorem averageJet_continuous (f : 𝓢(Y, ℂ)) (n : ℕ) (x : X) :
    Continuous (averageJet A w f n x) := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n => X) (fun _ : Fin n => Y) ℂ
  have h₁ : Continuous (fun t => C (fun _ : Fin n => A t)) :=
    C.cont.comp (continuous_pi fun _ => hA)
  have h₂ : Continuous (fun t => iteratedFDeriv ℝ n f (A t x)) :=
    (f.smooth n).continuous_iteratedFDeriv'.comp (hA.clm_apply continuous_const)
  exact hw.smul (h₁.clm_apply h₂)

omit [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T] in
include hIso hw₁ in
private theorem averageJet_bound (f : 𝓢(Y, ℂ)) (k n : ℕ) (x : X) (t : T) :
    ‖x‖ ^ k * ‖averageJet A w f n x t‖ ≤ SchwartzMap.seminorm ℂ k n f := by
  have h := (iteratedFDeriv ℝ n f (A t x)).norm_compContinuousLinearMap_le (fun _ => A t)
  have hA₁ : ‖A t‖ ≤ 1 := (A t).opNorm_le_bound zero_le_one (fun z => by rw [hIso, one_mul])
  have hprod : ∏ _i : Fin n, ‖A t‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hA₁)
  have hj : ‖averageJet A w f n x t‖ ≤ ‖iteratedFDeriv ℝ n f (A t x)‖ := by
    rw [averageJet, norm_smul]
    calc
      _ ≤ 1 * (‖iteratedFDeriv ℝ n f (A t x)‖ * ∏ _i : Fin n, ‖A t‖) :=
        mul_le_mul (hw₁ t) h (norm_nonneg _) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hprod
  calc
    _ ≤ ‖A t x‖ ^ k * ‖iteratedFDeriv ℝ n f (A t x)‖ := by rw [hIso]; gcongr
    _ ≤ _ := SchwartzMap.le_seminorm ℂ k n f (A t x)

include hA hIso hw hw₁

private theorem averageJet_integrable (f : 𝓢(Y, ℂ)) (n : ℕ) (x : X) :
    Integrable (averageJet A w f n x) μ := by
  apply (integrable_const (SchwartzMap.seminorm ℂ 0 n f)).mono'
    (averageJet_continuous hA hw f n x).aestronglyMeasurable
  exact .of_forall fun t => by simpa only [pow_zero, one_mul] using averageJet_bound hIso hw₁ f 0 n x t

private theorem averageJet_integral_hasFDerivAt (f : 𝓢(Y, ℂ)) (n : ℕ) (x : X) :
    HasFDerivAt (fun x => ∫ t, averageJet A w f n x t ∂μ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) ℂ
        (∫ t, averageJet A w f (n + 1) x t ∂μ)) x := by
  let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) ℂ
  have hcomm : (∫ t, C (averageJet A w f (n + 1) x t) ∂μ) =
      C (∫ t, averageJet A w f (n + 1) x t ∂μ) := by
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (ContinuousLinearEquiv.integral_comp_comm (μ := μ) (𝕜 := ℝ) (E := AverageJet X (n + 1))
        (F := X →L[ℝ] AverageJet X n) C.toContinuousLinearEquiv (averageJet A w f (n + 1) x))
  change HasFDerivAt _ (C _) x
  rw [← hcomm]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F := averageJet A w f n) (F' := fun x t => C (averageJet A w f (n + 1) x t))
    (bound := fun _ => SchwartzMap.seminorm ℂ 0 (n + 1) f)
    univ_mem (.of_forall fun x => (averageJet_continuous hA hw f n x).aestronglyMeasurable)
    (averageJet_integrable hA hIso hw hw₁ f n x)
    (C.continuous.comp_aestronglyMeasurable (averageJet_continuous hA hw f (n + 1) x).aestronglyMeasurable)
    ?_ (integrable_const _) ?_
  · exact .of_forall fun t x _ => by
      rw [C.norm_map]
      simpa only [pow_zero, one_mul] using averageJet_bound hIso hw₁ f 0 (n + 1) x t
  · exact .of_forall fun t x _ => by
      let g : X → ℂ := f ∘ A t
      have hg : ContDiff ℝ ∞ g := f.smooth'.comp (A t).contDiff
      have hd : HasFDerivAt (iteratedFDeriv ℝ n g)
          (C (iteratedFDeriv ℝ (n + 1) g x)) x := by
        rw [← Function.comp_apply (f := C), ← fderiv_iteratedFDeriv]
        exact ((hg.differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).differentiableAt).hasFDerivAt
      have he : (fun z => averageJet A w f n z t) =
          fun z => w t • iteratedFDeriv ℝ n g z := funext fun z => averageJet_eq f n z t
      rw [he, averageJet_eq]
      exact hd.const_smul (w t)

private theorem average_integral_iteratedFDeriv (f : 𝓢(Y, ℂ)) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => ∫ t, w t * f (A t x) ∂μ) =
      fun x => ∫ t, averageJet A w f n x t ∂μ := by
  induction n with
  | zero =>
    funext x
    ext a
    rw [ContinuousMultilinearMap.integral_apply (averageJet_integrable hA hIso hw hw₁ f 0 x)]
    simp [averageJet, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    rw [Function.comp_apply, (averageJet_integral_hasFDerivAt hA hIso hw hw₁ f n x).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

/-- Averaging isometric linear pullbacks against a bounded weight on a finite
measure space preserves all the Schwartz seminorms up to the total measure. -/
def schwartzIsometricAverage : 𝓢(Y, ℂ) →L[ℂ] 𝓢(X, ℂ) :=
  SchwartzMap.mkCLM (fun f x => ∫ t, w t * f (A t x) ∂μ)
    (fun f g x => by
      have hi (f : 𝓢(Y, ℂ)) : Integrable (fun t => w t * f (A t x)) μ := by
        have h := averageJet_integrable (μ := μ) hA hIso hw hw₁ f 0 x
        exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => X) ℂ (fun i => nomatch i)).integrable_comp
          h |>.congr (.of_forall fun t => by simp [averageJet, iteratedFDeriv_zero_apply])
      simpa only [add_apply, mul_add] using integral_add (hi f) (hi g))
    (fun c f x => by
      simpa only [smul_apply, RingHom.id_apply, smul_eq_mul, mul_left_comm] using
        integral_const_mul c (fun t => w t * f (A t x)))
    (fun f => by
      apply contDiff_of_differentiable_iteratedFDeriv
      intro n _
      rw [average_integral_iteratedFDeriv hA hIso hw hw₁]
      exact fun x => (averageJet_integral_hasFDerivAt hA hIso hw hw₁ f n x).differentiableAt)
    (fun ⟨k, n⟩ => ⟨{(k, n)}, μ.real univ, measureReal_nonneg, fun f x => by
      rw [Finset.sup_singleton, average_integral_iteratedFDeriv hA hIso hw hw₁]
      change ‖x‖ ^ k * ‖∫ t, averageJet A w f n x t ∂μ‖ ≤ _
      rw [← Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) k), ← norm_smul, ← integral_smul,
        mul_comm (μ.real univ)]
      apply norm_integral_le_of_norm_le_const
      exact .of_forall fun t => by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) k)]
        exact averageJet_bound hIso hw₁ f k n x t⟩)

@[simp] theorem schwartzIsometricAverage_apply (f : 𝓢(Y, ℂ)) (x : X) :
    schwartzIsometricAverage (μ := μ) hA hIso hw hw₁ f x = ∫ t, w t * f (A t x) ∂μ := rfl

/-- An isometric average preserves the vanishing of an entire derivative
when that derivative vanishes at every point visited by the average. -/
theorem schwartzIsometricAverage_iteratedFDeriv_eq_zero
    (f : 𝓢(Y, ℂ)) (n : ℕ) (x : X) (hf : ∀ t, iteratedFDeriv ℝ n f (A t x) = 0) :
    iteratedFDeriv ℝ n (schwartzIsometricAverage (μ := μ) hA hIso hw hw₁ f) x = 0 := by
  change iteratedFDeriv ℝ n (fun x => ∫ t, w t * f (A t x) ∂μ) x = 0
  rw [average_integral_iteratedFDeriv hA hIso hw hw₁]
  change (∫ t, averageJet A w f n x t ∂μ) = 0
  have he (t : T) : averageJet A w f n x t = 0 := by
    unfold averageJet
    rw [hf]
    ext a
    simp
  have hh : (fun t : T ↦ averageJet A w f n x t) = fun _ ↦ (0 : AverageJet X n) :=
    funext he
  rw [hh, integral_zero]

end

end Masullo
