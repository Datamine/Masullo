import BruhatFractionalTraces
import Mathlib.Analysis.InnerProductSpace.Completion

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct InnerProductSpace

namespace Masullo

noncomputable section

private def extendCompletedIsometry {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (M : E →ₗᵢ[ℂ] F) :
    Completion E →ₗᵢ[ℂ] F := by
  let J : E →ₗᵢ[ℂ] Completion E := Completion.toComplₗᵢ
  let T := M.toLinearMap.extendOfNorm J.toLinearMap
  have hd : DenseRange J := Completion.denseRange_coe
  have hB : ∃ C : ℝ, ∀ x, ‖M x‖ ≤ C * ‖J x‖ := ⟨1, fun x => by simp⟩
  exact ⟨T.toLinearMap, fun x => hd.induction (fun _ ⟨z, hz⟩ => by
    rw [← hz]
    have he : T (J z) = M z := LinearMap.extendOfNorm_eq hd hB z
    change ‖T (J z)‖ = ‖J z‖
    rw [he, LinearIsometry.norm_map, LinearIsometry.norm_map])
    (isClosed_eq T.continuous.norm continuous_norm) x⟩

private theorem extendCompletedIsometry_coe {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (M : E →ₗᵢ[ℂ] F) (x : E) :
    extendCompletedIsometry M (x : Completion E) = M x := by
  have hd : DenseRange (Completion.toComplₗᵢ : E →ₗᵢ[ℂ] Completion E) := Completion.denseRange_coe
  have hB : ∃ C : ℝ, ∀ z, ‖M z‖ ≤ C * ‖(z : Completion E)‖ := ⟨1, fun z => by simp⟩
  exact LinearMap.extendOfNorm_eq hd hB x

section FiniteTensor

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]

private def tensorCoordinatesLinear :
    E ⊗[ℂ] PiLp 2 F →ₗ[ℂ] PiLp 2 (fun i => Completion (E ⊗[ℂ] F i)) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp <| LinearMap.pi fun i =>
    Completion.toComplₗᵢ.toLinearMap.comp
      (TensorProduct.map LinearMap.id ((LinearMap.proj i).comp (WithLp.linearEquiv 2 ℂ _).toLinearMap))

omit [Fintype ι] in
private theorem tensorCoordinatesLinear_tmul (u : E) (v : PiLp 2 F) (i : ι) :
    tensorCoordinatesLinear (u ⊗ₜ[ℂ] v) i =
      ((u ⊗ₜ[ℂ] v i : E ⊗[ℂ] F i) : Completion (E ⊗[ℂ] F i)) := by
  change (↑(TensorProduct.map _ _ (u ⊗ₜ[ℂ] v) : E ⊗[ℂ] F i) : Completion (E ⊗[ℂ] F i)) = _
  rw [TensorProduct.map_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def tensorCoordinatesIsometry :
    E ⊗[ℂ] PiLp 2 F →ₗᵢ[ℂ] PiLp 2 (fun i => Completion (E ⊗[ℂ] F i)) := by
  let T : E ⊗[ℂ] PiLp 2 F →ₗ[ℂ] PiLp 2 (fun i => Completion (E ⊗[ℂ] F i)) :=
    tensorCoordinatesLinear
  have h (x y : E ⊗[ℂ] PiLp 2 F) : inner ℂ (T x) (T y) = inner ℂ x y := by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, inner_zero_left, inner_zero_left]
    | add x x' hx hx' => rw [map_add, inner_add_left, inner_add_left, hx, hx']
    | tmul u v =>
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, inner_zero_right, inner_zero_right]
      | add y y' hy hy' => rw [map_add, inner_add_right, inner_add_right, hy, hy']
      | tmul u' v' =>
        rw [PiLp.inner_apply, TensorProduct.inner_tmul, PiLp.inner_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          change inner ℂ (tensorCoordinatesLinear (u ⊗ₜ[ℂ] v) i)
            (tensorCoordinatesLinear (u' ⊗ₜ[ℂ] v') i) = _
          rw [tensorCoordinatesLinear_tmul, tensorCoordinatesLinear_tmul,
            Completion.inner_coe, TensorProduct.inner_tmul]
  refine ⟨T, fun x => ?_⟩
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (T x), norm_eq_sqrt_re_inner (𝕜 := ℂ) x, h]

/-- The finite Hilbert coordinates of a completed tensor preserve its norm. -/
def tensorFiniteHilbertCoordinates :
    Completion (E ⊗[ℂ] PiLp 2 F) →ₗᵢ[ℂ] PiLp 2 (fun i => Completion (E ⊗[ℂ] F i)) :=
  extendCompletedIsometry tensorCoordinatesIsometry

theorem tensorFiniteHilbertCoordinates_tmul (u : E) (v : PiLp 2 F) (i : ι) :
    tensorFiniteHilbertCoordinates ((u ⊗ₜ[ℂ] v : E ⊗[ℂ] PiLp 2 F) : Completion (E ⊗[ℂ] PiLp 2 F)) i =
      ((u ⊗ₜ[ℂ] v i : E ⊗[ℂ] F i) : Completion (E ⊗[ℂ] F i)) := by
  unfold tensorFiniteHilbertCoordinates
  rw [extendCompletedIsometry_coe]
  exact tensorCoordinatesLinear_tmul u v i

end FiniteTensor

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]

local notation "Height" => Lp ℂ 2 (volume : Measure ℝ)

/-- The physical half-line tensor in the angular Plancherel coordinates,
with the corresponding scalar support restriction in the radial factor. -/
def modulatedSupportedAngularTensor (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b s : ℝ)
    {R : Set ℝ} (hR : IsOpen R) :
    lpTwoRadialSupport μ (stripMeasure b b s) R ≃ₗᵢ[ℂ]
      Completion (A ⊗[ℂ] supportedSobolevCompletion b b s R) :=
  (modulatedSupportedTensorEquiv μ b s hR).symm.trans
    (completionCongrIsometry (TensorProduct.congrIsometry U (.refl ℂ _)))

/-- The tensor with an even-degree Mellin line embeds isometrically into
the finite tuple of normalized derivative coordinates. -/
def mellinDerivativeTensor (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b : ℝ) (N : ℕ) :
    Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) →ₗᵢ[ℂ]
      PiLp 2 (fun _ : Fin (N + 1) => Completion (A ⊗[ℂ] Height)) :=
  tensorFiniteHilbertCoordinates.comp <|
    extendCompletedIsometry (Completion.toComplₗᵢ.comp
      (TensorProduct.mapIsometry U.toLinearIsometry
        (Submodule.subtypeₗᵢ (MellinLineCompletion b N))))

omit [SFinite μ] in
theorem mellinDerivativeTensor_tmul (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b : ℝ) (N : ℕ)
    (u : Lp ℂ 2 μ) (v : MellinLineCompletion b N) (k : Fin (N + 1)) :
    mellinDerivativeTensor μ U b N
        ((u ⊗ₜ[ℂ] v : Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) :
          Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N)) k =
      ((U u ⊗ₜ[ℂ] v.val k : A ⊗[ℂ] Height) : Completion (A ⊗[ℂ] Height)) := by
  unfold mellinDerivativeTensor
  change tensorFiniteHilbertCoordinates
    (extendCompletedIsometry (F := Completion (A ⊗[ℂ] MellinTraceHilbert N))
      (Completion.toComplₗᵢ.comp (TensorProduct.mapIsometry U.toLinearIsometry
      (Submodule.subtypeₗᵢ (MellinLineCompletion b N)))) _) k = _
  rw [extendCompletedIsometry_coe]
  change tensorFiniteHilbertCoordinates
    (↑(TensorProduct.map U.toLinearMap (MellinLineCompletion b N).subtype (u ⊗ₜ[ℂ] v)) :
      Completion (A ⊗[ℂ] MellinTraceHilbert N)) k = _
  rw [TensorProduct.map_tmul]
  exact tensorFiniteHilbertCoordinates_tmul (U u) v.val k

/-- Evaluate the angular variable of a completed derivative coordinate
with a bounded linear functional. -/
def mellinDerivativeAngularEval (L : A →L[ℂ] ℂ) : Completion (A ⊗[ℂ] Height) →L[ℂ] Height :=
  ((TensorProduct.lidIsometry ℂ Height).toLinearIsometry.toContinuousLinearMap.comp
    (L.rTensor Height)).toLinearMap.extendOfNorm Completion.toComplₗᵢ.toLinearMap

theorem mellinDerivativeAngularEval_tmul (L : A →L[ℂ] ℂ) (u : A) (v : Height) :
    mellinDerivativeAngularEval L ((u ⊗ₜ[ℂ] v : A ⊗[ℂ] Height) :
      Completion (A ⊗[ℂ] Height)) = L u • v := by
  let T := (TensorProduct.lidIsometry ℂ Height).toLinearIsometry.toContinuousLinearMap.comp
    (L.rTensor Height)
  let J : A ⊗[ℂ] Height →ₗᵢ[ℂ] Completion (A ⊗[ℂ] Height) := Completion.toComplₗᵢ
  have hd : DenseRange J := Completion.denseRange_coe
  have hb : ∃ C : ℝ, ∀ z, ‖T z‖ ≤ C * ‖J z‖ :=
    ⟨‖T‖, fun z => by simpa only [LinearIsometry.norm_map] using T.le_opNorm z⟩
  change T.toLinearMap.extendOfNorm J.toLinearMap (J (u ⊗ₜ[ℂ] v)) = _
  have h := LinearMap.extendOfNorm_eq (f := T.toLinearMap) (e := J.toLinearMap) hd hb (u ⊗ₜ[ℂ] v)
  refine h.trans ?_
  rfl

omit [SFinite μ] in
/-- On separated tests the coordinate is the actual normalized radial
Mellin derivative multiplied by the selected angular coefficient. -/
theorem mellinDerivativeTensor_onSeparated (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A)
    (L : A →L[ℂ] ℂ) (b : ℝ) (N : ℕ) (u : Lp ℂ 2 μ)
    (f : PositiveRealExponentialDecay (univ : Set ℝ)) (k : Fin (N + 1)) :
    (mellinDerivativeAngularEval L (mellinDerivativeTensor μ U b N
        ((u ⊗ₜ[ℂ] mellinLineEquiv b N (weightedLineTest b N f) :
          Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N) :
          Completion (Lp ℂ 2 μ ⊗[ℂ] MellinLineCompletion b N)) k) : ℝ → ℂ)
      =ᵐ[volume] fun y => L (U u) *
        ((Real.sqrt ((N.choose (k : ℕ) : ℝ) / (2 * Real.pi)) : ℂ) *
          iteratedDeriv (k : ℕ) (mellin fun t => f.val (Real.log t)) (⟨b, y⟩ : ℂ)) := by
  rw [mellinDerivativeTensor_tmul, mellinDerivativeAngularEval_tmul]
  refine (Lp.coeFn_smul (L (U u)) _).trans ?_
  exact (mellinLineEquiv_onTest_derivative_ae b N f k).mono fun y hy =>
    congrArg (L (U u) * ·) hy

section Character

variable [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ]

set_option maxHeartbeats 1800000 in
/-- Character extraction in a derivative coordinate commutes with taking
the scalar derivative tuple of the radial character coefficient. -/
theorem modulatedDerivativeTensor_character (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A)
    (L : A →L[ℂ] ℂ) (χ : PontryaginDual K)
    (hc : ∀ u : Lp ℂ 2 μ, L (U u) = ∫ k, (χ k : ℂ) * u k ∂μ)
    (b : ℝ) (N : ℕ) (k : Fin (N + 1)) (f : Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ))))) :
    mellinDerivativeAngularEval L
      (mellinDerivativeTensor μ U b N (modulatedMellinLineEquiv μ b N f) k) =
      (mellinLineIsometry b N (lpTwoCharacterCoefficient χ f)) k := by
  let E := Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b (2 * (N : ℝ))
  let P : Completion E ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) :=
    completedLpTwoTensorEquiv
  let T : Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) →L[ℂ] Height :=
    (mellinDerivativeAngularEval L).comp ((PiLp.proj _ _ k).comp
      ((mellinDerivativeTensor μ U b N).toContinuousLinearMap.comp
        (modulatedMellinLineEquiv μ b N).toLinearIsometry.toContinuousLinearMap))
  let D : Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))) →L[ℂ] Height :=
    (PiLp.proj _ _ k).comp ((mellinLineIsometry b N).toContinuousLinearMap.comp
      (lpTwoCharacterCoefficient χ))
  change T f = D f
  obtain ⟨v, rfl⟩ := P.surjective f
  refine Completion.denseRange_coe.induction_on v
    (isClosed_eq (T.continuous.comp P.continuous) (D.continuous.comp P.continuous)) ?_
  intro v
  let T₀ := T.toLinearMap.comp (P.toLinearMap.comp (Completion.toComplₗᵢ : E →ₗᵢ[ℂ] Completion E).toLinearMap)
  let D₀ := D.toLinearMap.comp (P.toLinearMap.comp (Completion.toComplₗᵢ : E →ₗᵢ[ℂ] Completion E).toLinearMap)
  change T₀ v = D₀ v
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul u w =>
    have hP : P ((u ⊗ₜ[ℂ] w : E) : Completion E) = lpTwoProduct u w :=
      completedLpTwoTensorEquiv_tmul u w
    change mellinDerivativeAngularEval L
        (mellinDerivativeTensor μ U b N (modulatedMellinLineEquiv μ b N
          (P ((u ⊗ₜ[ℂ] w : E) : Completion E))) k) =
      (mellinLineIsometry b N (lpTwoCharacterCoefficient χ (P ((u ⊗ₜ[ℂ] w : E) : Completion E)))) k
    rw [hP, modulatedMellinLineEquiv_tmul, mellinDerivativeTensor_tmul,
      mellinDerivativeAngularEval_tmul, lpTwoCharacterCoefficient_product μ b, hc u, map_smul]
    rfl

end Character

/-- A fractional line at even order, in the normalized derivative
coordinates and the chosen angular Plancherel model. -/
def fractionalDerivativeCoordinates (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b : ℝ) (N : ℕ) :
    FractionalMellinTensor μ (2 * (N : ℝ)) →ₗᵢ[ℂ]
      PiLp 2 (fun _ : Fin (N + 1) => Completion (A ⊗[ℂ] Height)) :=
  (mellinDerivativeTensor μ U b N).comp
    ((fractionalMellinTensor μ b (2 * (N : ℝ))).symm.trans
      (modulatedMellinLineEquiv μ b N)).toLinearIsometry

theorem fractionalDerivativeCoordinates_apply_line (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A)
    (b : ℝ) (N : ℕ) (f : Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ))))) :
    fractionalDerivativeCoordinates μ U b N (fractionalMellinTensor μ b (2 * (N : ℝ)) f) =
      mellinDerivativeTensor μ U b N (modulatedMellinLineEquiv μ b N f) := by
  change mellinDerivativeTensor μ U b N (modulatedMellinLineEquiv μ b N
    ((fractionalMellinTensor μ b (2 * (N : ℝ))).symm
      (fractionalMellinTensor μ b (2 * (N : ℝ)) f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem fractionalDerivativeCoordinates_energy (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b : ℝ) (N : ℕ)
    (v : FractionalMellinTensor μ (2 * (N : ℝ))) :
    (∑ k : Fin (N + 1), ‖fractionalDerivativeCoordinates μ U b N v k‖ ^ 2) = ‖v‖ ^ 2 := by
  rw [← PiLp.norm_sq_eq_of_L2, LinearIsometry.norm_map]

/-- Uniform control of the finitely many derivative coordinates at all
sampled abscissae is equivalent to convergence in the compact interval norm. -/
theorem modulatedDerivativeSamples_compact_tendsto_iff
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (S : Set ℝ) (hS : S ⊆ Icc a b) (ha : a ∈ closure S) (hb : b ∈ closure S)
    {ι : Type*} {l : Filter ι}
    (f : ι → Lp ℂ 2 (μ.prod (stripMeasure a b (2 * (N : ℝ))))) :
    Tendsto (fun i => ‖f i‖) l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ i in l,
      ∀ t (ht : t ∈ S) (k : Fin (N + 1)),
        ‖fractionalDerivativeCoordinates μ U t N (fractionalIntervalTrace μ hab _ (hS ht) (f i)) k‖ < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with i hi
    intro t ht k
    let v := fractionalIntervalTrace μ hab (2 * (N : ℝ)) (hS ht) (f i)
    have hc := PiLp.norm_apply_le (fractionalDerivativeCoordinates μ U t N v) k
    rw [LinearIsometry.norm_map] at hc
    exact (hc.trans (fractionalIntervalTrace_norm_le μ hab _ (hS ht) (f i))).trans_lt
      (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hi)
  · intro h ε hε
    let C : ℝ := 2 * ((N : ℝ) + 1)
    have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) N]
    let δ := ε / (2 * C)
    have hδ : 0 < δ := div_pos hε (by positivity)
    filter_upwards [h δ hδ] with i hi
    have hbound := fractionalInterval_uniformSamples_bound μ hab (2 * (N : ℝ))
      S hS ha hb (f i) ((N + 1 : ℕ) * δ ^ 2) (fun t ht => by
        rw [← fractionalDerivativeCoordinates_energy μ U t N]
        calc
          _ ≤ ∑ _ : Fin (N + 1), δ ^ 2 := Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hi t ht k).le 2
          _ = _ := by simp)
    have hCc : C ≤ C ^ 2 := by nlinarith
    have hbound' : ‖f i‖ ^ 2 ≤ (C * δ) ^ 2 := by
      rw [mul_pow]
      apply hbound.trans
      rw [← mul_assoc, Nat.cast_add, Nat.cast_one]
      exact mul_le_mul_of_nonneg_right hCc (sq_nonneg δ)
    have he : C * δ = ε / 2 := by
      dsimp [δ]
      field_simp
    rw [he] at hbound'
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (show ‖f i‖ < ε by nlinarith [norm_nonneg (f i)])

private theorem modulatedDerivativeSamples_ray_tendsto_iff
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (N : ℕ) (t : ℕ → ℝ)
    {ι : Type*} {l : Filter ι} (e : ι → ℝ)
    (v : ι → ℕ → FractionalMellinTensor μ (2 * (N : ℝ)))
    (hcon : ∀ i n, ‖v i n‖ ≤ e i) (hlim : ∀ i, Tendsto (fun n => ‖v i n‖) atTop (𝓝 (e i))) :
    Tendsto e l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ n (k : Fin (N + 1)),
      ‖fractionalDerivativeCoordinates μ U (t n) N (v i n) k‖ < ε := by
  have he : ∀ i, 0 ≤ e i := fun i => (norm_nonneg (v i 0)).trans (hcon i 0)
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with i hi
    intro n k
    have hc := PiLp.norm_apply_le (fractionalDerivativeCoordinates μ U (t n) N (v i n)) k
    rw [LinearIsometry.norm_map] at hc
    exact (hc.trans (hcon i n)).trans_lt (by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (he i)] using hi)
  · intro h ε hε
    let C : ℝ := (N : ℝ) + 1
    have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) N]
    let δ := ε / (2 * C)
    have hδ : 0 < δ := div_pos hε (by positivity)
    filter_upwards [h δ hδ] with i hi
    have hbound (n : ℕ) : ‖v i n‖ ^ 2 ≤ C * δ ^ 2 := by
      rw [← fractionalDerivativeCoordinates_energy μ U (t n) N]
      calc
        _ ≤ ∑ _ : Fin (N + 1), δ ^ 2 := Finset.sum_le_sum fun k _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hi n k).le 2
        _ = _ := by simp [C, Nat.cast_add]
    have hz := le_of_tendsto ((hlim i).pow 2) (.of_forall hbound)
    have hCc : C ≤ C ^ 2 := by nlinarith
    have hz' : e i ^ 2 ≤ (C * δ) ^ 2 := hz.trans (by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hCc (sq_nonneg _))
    have hE : C * δ = ε / 2 := by dsimp [δ]; field_simp
    rw [hE] at hz'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (he i)]
    nlinarith [he i]

/-- Uniform derivative samples approaching the right-ray boundary recover
its physical weighted topology. All test and completed profiles use the
finite-norm support condition. -/
theorem modulatedDerivativeSamples_right_tendsto_iff
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b : ℝ) (N : ℕ)
    (t : ℕ → Ici b) (ht : Tendsto t atTop (𝓝 (⟨b, self_mem_Ici⟩ : Ici b)))
    {ι : Type*} {l : Filter ι}
    (f : ι → Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))))
    (hf : ∀ i, ∀ᵐ p ∂μ.prod (stripMeasure b b (2 * (N : ℝ))), 0 < p.2 → f i p = 0) :
    Tendsto (fun i => ‖f i‖) l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ n (k : Fin (N + 1)),
      ‖fractionalDerivativeCoordinates μ U (t n) N
        (fractionalRightHalfLineTrace μ b _ (f i) (hf i) (t n)) k‖ < ε := by
  apply modulatedDerivativeSamples_ray_tendsto_iff μ U N (fun n => t n)
    (fun i => ‖f i‖) (fun i n => fractionalRightHalfLineTrace μ b _ (f i) (hf i) (t n))
  · exact fun i n => fractionalRightHalfLineTrace_norm_le μ b _ (f i) (hf i) (t n)
  · intro i
    have h := ((fractionalRightHalfLineTrace_continuousAt μ b _ (f i) (hf i)).tendsto.comp ht).norm
    rw [fractionalRightHalfLineTrace_endpoint, LinearIsometryEquiv.norm_map] at h
    exact h

/-- The same derivative sampling topology on the left half-line. -/
theorem modulatedDerivativeSamples_left_tendsto_iff
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] A) (b : ℝ) (N : ℕ)
    (t : ℕ → Iic b) (ht : Tendsto t atTop (𝓝 (⟨b, self_mem_Iic⟩ : Iic b)))
    {ι : Type*} {l : Filter ι}
    (f : ι → Lp ℂ 2 (μ.prod (stripMeasure b b (2 * (N : ℝ)))))
    (hf : ∀ i, ∀ᵐ p ∂μ.prod (stripMeasure b b (2 * (N : ℝ))), p.2 < 0 → f i p = 0) :
    Tendsto (fun i => ‖f i‖) l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ n (k : Fin (N + 1)),
      ‖fractionalDerivativeCoordinates μ U (t n) N
        (fractionalLeftHalfLineTrace μ b _ (f i) (hf i) (t n)) k‖ < ε := by
  apply modulatedDerivativeSamples_ray_tendsto_iff μ U N (fun n => t n)
    (fun i => ‖f i‖) (fun i n => fractionalLeftHalfLineTrace μ b _ (f i) (hf i) (t n))
  · exact fun i n => fractionalLeftHalfLineTrace_norm_le μ b _ (f i) (hf i) (t n)
  · intro i
    have h := ((fractionalLeftHalfLineTrace_continuousAt μ b _ (f i) (hf i)).tendsto.comp ht).norm
    rw [fractionalLeftHalfLineTrace_endpoint, LinearIsometryEquiv.norm_map] at h
    exact h

end
end Masullo
