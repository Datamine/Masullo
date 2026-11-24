import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Topology.UniformSpace.AbstractCompletion

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology Pointwise

namespace Masullo

noncomputable def complexMeasureIntegral {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X ℂ) (f : X → ℂ) : ℂ :=
  VectorMeasure.integral μ f (ContinuousLinearMap.mul ℝ ℂ)

/-- Weak integrability and the representing-vector identity, evaluated against every
continuous complex linear functional. -/
def HasPettisIntegral {X E : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (μ : VectorMeasure X ℂ) (f : X → E) (u : E) : Prop :=
  ∀ ℓ : E →L[ℂ] ℂ, μ.Integrable (ℓ ∘ f) ∧ ℓ u = complexMeasureIntegral μ (ℓ ∘ f)

private theorem complexMeasureIntegral_smul {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X ℂ) (c : ℂ) (f : X → ℂ) :
    complexMeasureIntegral μ (c • f) = c • complexMeasureIntegral μ f := by
  unfold complexMeasureIntegral VectorMeasure.integral
  apply setToFun_smul
  intro a s x
  by_cases hs : MeasurableSet s
  · change ((ContinuousLinearMap.mul ℝ ℂ) (a • x)) (μ s) =
        a • ((ContinuousLinearMap.mul ℝ ℂ) x) (μ s)
    exact mul_assoc _ _ _
  · rw [VectorMeasure.not_measurable (μ.transpose (ContinuousLinearMap.mul ℝ ℂ)) hs]
    simp

/-- The weak Pettis integral, as an element of the algebraic dual of the
continuous dual. -/
noncomputable def weakPettisIntegral {X E : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (μ : VectorMeasure X ℂ) (f : X → E)
    (hf : ∀ ℓ : E →L[ℂ] ℂ, μ.Integrable (ℓ ∘ f)) :
    Module.Dual ℂ (E →L[ℂ] ℂ) where
  toFun ℓ := complexMeasureIntegral μ (ℓ ∘ f)
  map_add' ℓ m := VectorMeasure.integral_add (hf ℓ) (hf m)
  map_smul' c ℓ := complexMeasureIntegral_smul μ c (ℓ ∘ f)

section Naturality

variable {X E F : Type*} [MeasurableSpace X]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Lemma C.4.3.8, the weak integral commutes with the dual of precomposition. -/
theorem weakPettisIntegral_comp (μ : VectorMeasure X ℂ) (T : E →L[ℂ] F) (f : X → E)
    (hf : ∀ ℓ : E →L[ℂ] ℂ, μ.Integrable (ℓ ∘ f)) :
    weakPettisIntegral μ (T ∘ f) (fun ℓ => hf (ℓ.comp T)) =
      (weakPettisIntegral μ f hf).comp
        (show (F →L[ℂ] ℂ) →ₗ[ℂ] (E →L[ℂ] ℂ) from
          { toFun := fun ℓ => ℓ.comp T
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }) := rfl

/-- Lemma C.4.3.8, the represented integral commutes with continuous linear maps. -/
theorem HasPettisIntegral.comp {μ : VectorMeasure X ℂ} {f : X → E} {u : E}
    (hf : HasPettisIntegral μ f u) (T : E →L[ℂ] F) :
    HasPettisIntegral μ (T ∘ f) (T u) :=
  fun ℓ => hf (ℓ.comp T)

end Naturality

private theorem complexMul_norm_le_one :
    ‖ContinuousLinearMap.mul ℝ ℂ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z)
  intro w
  exact (norm_mul z w).le

section Banach

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

private noncomputable def weakEvaluationsL1 (μ : VectorMeasure X ℂ) (f : X → E)
    (hf : ∀ ℓ : E →L[ℂ] ℂ, μ.Integrable (ℓ ∘ f)) :
    (E →L[ℂ] ℂ) →ₗ[ℂ] (X →₁[μ.variation] ℂ) where
  toFun ℓ := (hf ℓ).toL1 (ℓ ∘ f)
  map_add' ℓ m := Integrable.toL1_add _ _ (hf ℓ) (hf m)
  map_smul' c ℓ := Integrable.toL1_smul _ (hf ℓ) c

private theorem continuous_weakEvaluationsL1 (μ : VectorMeasure X ℂ) (f : X → E)
    (hf : ∀ ℓ : E →L[ℂ] ℂ, μ.Integrable (ℓ ∘ f)) :
    Continuous (weakEvaluationsL1 μ f hf) := by
  let L := weakEvaluationsL1 μ f hf
  apply L.continuous_of_seq_closed_graph
  intro φ ℓ y hφ hy
  obtain ⟨n, hn, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
  have heq (m : ℕ) : (L (φ (n m)) : X → ℂ) =ᵐ[μ.variation] φ (n m) ∘ f :=
    (hf (φ (n m))).coeFn_toL1
  apply Lp.ext
  filter_upwards [hsub, ae_all_iff.mpr heq, (hf ℓ).coeFn_toL1] with x hx hxm hlx
  have ht : Tendsto (fun m => φ (n m) (f x)) atTop (𝓝 (ℓ (f x))) :=
    ((ContinuousLinearMap.apply ℂ ℂ (f x)).continuous.tendsto ℓ).comp
      (hφ.comp hn.tendsto_atTop)
  exact (tendsto_nhds_unique (hx.congr hxm) ht).trans hlx.symm

/-- Lemma C.4.3.7. The weak integral is bounded on the Banach dual. If the
canonical map to the continuous bidual is onto, it has a representing vector. -/
theorem pettis_exists_of_reflexive
    (href : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ E))
    (μ : VectorMeasure X ℂ) (f : X → E)
    (hf : ∀ ℓ : E →L[ℂ] ℂ, μ.Integrable (ℓ ∘ f)) :
    ∃ u, HasPettisIntegral μ f u := by
  let L : (E →L[ℂ] ℂ) →L[ℂ] (X →₁[μ.variation] ℂ) :=
    ⟨weakEvaluationsL1 μ f hf, continuous_weakEvaluationsL1 μ f hf⟩
  have hbound (ℓ : E →L[ℂ] ℂ) : ‖weakPettisIntegral μ f hf ℓ‖ ≤ ‖L‖ * ‖ℓ‖ := by
    have h := VectorMeasure.norm_integral_le_lintegral_norm
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) (f := ℓ ∘ f)
    rw [← Integrable.norm_toL1_eq_lintegral_norm _ (hf ℓ)] at h
    exact (h.trans (mul_le_of_le_one_left (norm_nonneg _) complexMul_norm_le_one)).trans
      (L.le_opNorm ℓ)
  obtain ⟨u, hu⟩ := href ((weakPettisIntegral μ f hf).mkContinuous ‖L‖ hbound)
  exact ⟨u, fun ℓ => ⟨hf ℓ, DFunLike.congr_fun hu ℓ⟩⟩

end Banach

section Hilbert

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem hilbert_bidually_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ H) := by
  intro Λ
  let D := InnerProductSpace.toDual ℂ H
  let J : H →L[ℂ] ℂ :=
    { toFun := fun x => star (Λ (D x))
      map_add' := fun x y => by simp [map_add]
      map_smul' := fun c x => by simp [map_smulₛₗ, smul_eq_mul]
      cont := Complex.continuous_conj.comp (Λ.continuous.comp D.continuous) }
  obtain ⟨u, hu⟩ := D.surjective J
  refine ⟨u, ?_⟩
  ext ℓ
  obtain ⟨x, rfl⟩ := D.surjective ℓ
  have he : inner ℂ u x = star (Λ (D x)) := DFunLike.congr_fun hu x
  change inner ℂ x u = Λ (D x)
  rw [← inner_conj_symm, he]
  exact star_star _

/-- Corrected Lemma C.4.3.11. Weak measurability of all evaluations and
integrability of the operator norm against total variation give a bounded
operator representing the Pettis integrals of the evaluations. -/
theorem pettis_exists_boundedOperator (μ : VectorMeasure X ℂ) (F : X → H →L[ℂ] H)
    (hF : ∀ (u : H) (ℓ : H →L[ℂ] ℂ),
      AEMeasurable (fun x => ℓ (F x u)) μ.variation)
    (hN : Integrable (fun x => ‖F x‖) μ.variation) :
    ∃ T : H →L[ℂ] H, ∀ u, HasPettisIntegral μ (fun x => F x u) (T u) := by
  have pointwise (u : H) (ℓ : H →L[ℂ] ℂ) (x : X) :
      ‖ℓ (F x u)‖ ≤ (‖ℓ‖ * ‖u‖) * ‖F x‖ := by
    calc
      _ ≤ ‖ℓ‖ * ‖F x u‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (‖F x‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left ((F x).le_opNorm u) (norm_nonneg _)
      _ = _ := by ring
  have hint (u : H) (ℓ : H →L[ℂ] ℂ) :
      μ.Integrable (fun x => ℓ (F x u)) :=
    (hN.const_mul (‖ℓ‖ * ‖u‖)).mono' (hF u ℓ).aestronglyMeasurable
      (Eventually.of_forall (pointwise u ℓ))
  choose t ht using fun u : H =>
    pettis_exists_of_reflexive hilbert_bidually_surjective μ (fun x => F x u) (hint u)
  let M := ∫ x, ‖F x‖ ∂μ.variation
  have hM : 0 ≤ M := integral_nonneg fun x => norm_nonneg _
  have hnorm (u : H) : ‖t u‖ ≤ M * ‖u‖ := by
    apply NormedSpace.norm_le_dual_bound ℂ (t u) (mul_nonneg hM (norm_nonneg _))
    intro ℓ
    rw [(ht u ℓ).2]
    have h := VectorMeasure.norm_integral_le_integral_norm
      (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) (f := fun x => ℓ (F x u))
    have hI : 0 ≤ ∫ x, ‖ℓ (F x u)‖ ∂μ.variation := integral_nonneg fun x => norm_nonneg _
    calc
      _ ≤ ∫ x, ‖ℓ (F x u)‖ ∂μ.variation :=
        h.trans (mul_le_of_le_one_left hI complexMul_norm_le_one)
      _ ≤ ∫ x, (‖ℓ‖ * ‖u‖) * ‖F x‖ ∂μ.variation :=
        integral_mono (hint u ℓ).norm (hN.const_mul _) (pointwise u ℓ)
      _ = _ := by rw [integral_const_mul]; change (‖ℓ‖ * ‖u‖) * M = _; ring
  have separated {x y : H} (he : ∀ ℓ : H →L[ℂ] ℂ, ℓ x = ℓ y) : x = y :=
    (NormedSpace.inclusionInDoubleDualLi (E := H) ℂ).injective (ContinuousLinearMap.ext he)
  let A : H →ₗ[ℂ] H :=
    { toFun := t
      map_add' := fun u v => separated fun ℓ => by
        rw [map_add, (ht (u + v) ℓ).2, (ht u ℓ).2, (ht v ℓ).2]
        have he : (ℓ ∘ fun x => F x (u + v)) = (fun x => ℓ (F x u)) + (fun x => ℓ (F x v)) :=
          funext fun x => by simp [map_add]
        rw [he]
        exact VectorMeasure.integral_add (hint u ℓ) (hint v ℓ)
      map_smul' := fun c u => separated fun ℓ => by
        rw [RingHom.id_apply, map_smul, (ht (c • u) ℓ).2, (ht u ℓ).2]
        have he : (ℓ ∘ fun x => F x (c • u)) = c • (fun x => ℓ (F x u)) :=
          funext fun x => by simp [map_smul]
        rw [he]
        exact complexMeasureIntegral_smul μ c _ }
  exact ⟨A.mkContinuous M hnorm, ht⟩

end Hilbert

theorem seminorm_support {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [PolynormableSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) (u : E) :
    ∃ ℓ : E →L[ℂ] ℂ, ‖ℓ u‖ = p u ∧ ∀ v, ‖ℓ v‖ ≤ p v := by
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu], fun v => by simp⟩
  let S := ℂ ∙ u
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E u hu
  let a : Module.Dual ℂ S := (p u : ℂ) • e.symm.toLinearMap
  have ha (w : S) : ‖a w‖ = p w.val := by
    change ‖(p u : ℂ) * e.symm w‖ = p w.val
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg p u), mul_comm]
    rw [← map_smul_eq_mul]
    exact congrArg p (LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℂ E u hu w)
  obtain ⟨ℓ, hℓ, hbound⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm S a hp (fun w => (ha w).le)
  let w : S := ⟨u, Submodule.mem_span_singleton_self u⟩
  exact ⟨ℓ, (congrArg norm (hℓ w)).trans (ha w), hbound⟩

section WeakCompletion

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The algebraic dual of the continuous dual, with pointwise convergence. -/
abbrev WeakAlgebraicBidual :=
  WeakBilin (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ]
    (StrongDual ℂ E) →ₗ[ℂ] ℂ)

/-- Evaluation at a vector defines a linear form on the continuous dual. -/
noncomputable def weakBidualEval : E →ₗ[ℂ] WeakAlgebraicBidual E :=
  (topDualPairing ℂ E).flip

/-- Lemma C.4.1.1, continuity from the original topology. -/
theorem weakBidualEval_continuous : Continuous (weakBidualEval E) :=
  WeakBilin.continuous_of_continuous_eval _ fun ℓ => ℓ.continuous

/-- Lemma C.4.1.1, the weak topology is induced by the bidual inclusion. -/
theorem weakBidualEval_isEmbedding [PolynormableSpace ℂ E] [T2Space E] :
    IsEmbedding (fun x : WeakSpace ℂ E => weakBidualEval E x) := by
  have hzero (u : E) (h : ∀ ℓ : StrongDual ℂ E, ℓ u = 0) : u = 0 := by
    by_contra hu
    obtain ⟨p, hp⟩ := (PolynormableSpace.withSeminorms ℂ E).separating_of_T1 u hu
    obtain ⟨ℓ, hℓ, _⟩ := seminorm_support p.val p.property u
    exact hp (by simpa [h ℓ] using hℓ.symm)
  refine ⟨⟨induced_compose.symm⟩, ?_⟩
  intro x y hxy
  have hs : (x : E) - (y : E) = 0 := hzero _ fun ℓ => by
    have he := congrArg (fun z : WeakAlgebraicBidual E =>
      (show Module.Dual ℂ (StrongDual ℂ E) from z) ℓ) hxy
    exact (map_sub ℓ (x : E) (y : E)).trans (sub_eq_zero.mpr he)
  exact sub_eq_zero.mp hs

variable {E} {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Precomposition restricts the algebraic dual map to continuous functionals. -/
noncomputable def continuousTranspose (T : E →L[ℂ] F) : StrongDual ℂ F →ₗ[ℂ] StrongDual ℂ E where
  toFun ℓ := ℓ.comp T
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def weakBidualTranspose (T : E →L[ℂ] F) :
    WeakAlgebraicBidual E →ₗ[ℂ] WeakAlgebraicBidual F :=
  (continuousTranspose T).dualMap

noncomputable def weakDualTranspose (T : E →L[ℂ] F) : WeakDual ℂ F → WeakDual ℂ E :=
  fun ℓ => continuousTranspose T ℓ

/-- Lemma C.4.1.1, the two transpose maps are weakly continuous and
the evaluation inclusions are natural. -/
theorem weakBidualEval_naturality (T : E →L[ℂ] F) :
    Continuous (weakDualTranspose T) ∧
    Continuous (weakBidualTranspose T) ∧
    ∀ x, weakBidualTranspose T (weakBidualEval E x) = weakBidualEval F (T x) := by
  refine ⟨WeakDual.continuous_of_continuous_eval (fun x => WeakDual.eval_continuous (T x)), ?_, fun _ => rfl⟩
  exact WeakBilin.continuous_of_continuous_eval _ fun ℓ =>
    WeakBilin.eval_continuous _ (continuousTranspose T ℓ)

variable (E)

private theorem weakBidualEval_matches_finset (v : WeakAlgebraicBidual E)
    (s : Finset (StrongDual ℂ E)) :
    ∃ x : E, ∀ ℓ ∈ s, ℓ x = (show Module.Dual ℂ (StrongDual ℂ E) from v) ℓ := by
  let W := Submodule.span ℂ (↑s : Set (StrongDual ℂ E))
  letI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ s.finite_toSet
  let B : E →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
    W.subtype.dualMap.comp (topDualPairing ℂ E).flip
  have hB : Function.Injective B.flip := by
    intro ℓ m he
    exact Subtype.ext (ContinuousLinearMap.ext fun x =>
      DFunLike.congr_fun he x)
  have hsurj : Function.Surjective B := by
    exact (@LinearMap.flip_injective_iff₂ ℂ E W _ _ _ _ _ B _).mp hB
  obtain ⟨x, hx⟩ := hsurj (W.subtype.dualMap v)
  exact ⟨x, fun ℓ hℓ => DFunLike.congr_fun hx ⟨ℓ, Submodule.subset_span hℓ⟩⟩

/-- Evaluations on vectors are dense in the pointwise algebraic bidual.
On each finite set of functionals one can match the values exactly. -/
theorem weakBidualEval_dense : DenseRange (weakBidualEval E) := by
  intro v
  let P : WeakAlgebraicBidual E → (StrongDual ℂ E → ℂ) := fun u ℓ =>
    (show Module.Dual ℂ (StrongDual ℂ E) from u) ℓ
  have hP : IsInducing P := ⟨rfl⟩
  apply mem_closure_iff_nhds.mpr
  intro S hS
  rw [hP.nhds_eq_comap] at hS
  obtain ⟨U, hU, hUS⟩ := mem_comap.mp hS
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨s, w, hw, hwU⟩ := hU
  obtain ⟨x, hx⟩ := weakBidualEval_matches_finset E v s
  refine ⟨weakBidualEval E x, hUS (hwU ?_), mem_range_self x⟩
  intro ℓ hℓ
  change ℓ x ∈ w ℓ
  rw [hx ℓ hℓ]
  exact mem_of_mem_nhds (hw ℓ)

private noncomputable def weakBidualToFun (u : WeakAlgebraicBidual E) (ℓ : StrongDual ℂ E) : ℂ :=
  (show Module.Dual ℂ (StrongDual ℂ E) from u) ℓ

private theorem weakBidualToFun_closed : IsClosed (range (weakBidualToFun E)) := by
  let V := StrongDual ℂ E
  have he : range (weakBidualToFun E) =
      {f : V → ℂ | ∀ x y, f (x + y) = f x + f y} ∩
        {f : V → ℂ | ∀ a : ℂ, ∀ x, f (a • x) = a • f x} := by
    ext f
    constructor
    · rintro ⟨u, rfl⟩
      let w : Module.Dual ℂ V := u
      exact ⟨fun x y => map_add w x y, fun a x => map_smul w a x⟩
    · rintro ⟨hadd, hsmul⟩
      let w : Module.Dual ℂ V :=
        { toFun := f, map_add' := hadd, map_smul' := hsmul }
      exact ⟨w, rfl⟩
  rw [he]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
  · simp only [ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun x =>
      isClosed_eq (continuous_apply (a • x)) ((continuous_apply x).const_smul a)

/-- Pointwise uniform convergence on the algebraic bidual. -/
noncomputable abbrev weakBidualUniformity : UniformSpace (WeakAlgebraicBidual E) :=
  UniformSpace.comap (weakBidualToFun E) inferInstance

/-- Pointwise uniform convergence against the continuous dual of E. -/
noncomputable abbrev weakSpaceUniformity : UniformSpace (WeakSpace ℂ E) :=
  UniformSpace.comap (fun x : WeakSpace ℂ E => weakBidualEval E x) (weakBidualUniformity E)

theorem weakSpaceUniformity_topology [PolynormableSpace ℂ E] [T2Space E] :
    (weakSpaceUniformity E).toTopologicalSpace = (inferInstance : TopologicalSpace (WeakSpace ℂ E)) :=
  (weakBidualEval_isEmbedding E).isInducing.eq_induced.symm

/-- Lemma C.4.1.2, the algebraic bidual is a completion in the weak uniformity. -/
noncomputable def weakBidualCompletion :
    letI := weakSpaceUniformity E
    AbstractCompletion (WeakSpace ℂ E) := by
  letI := weakSpaceUniformity E
  letI := weakBidualUniformity E
  exact
    { space := WeakAlgebraicBidual E
      uniformStruct := weakBidualUniformity E
      coe := fun x => weakBidualEval E x
      isUniformInducing := ⟨rfl⟩
      complete := (completeSpace_iff_isComplete_range
        (show IsUniformInducing (weakBidualToFun E) from ⟨rfl⟩)).mpr
        (weakBidualToFun_closed E).isComplete
      separation := by
        have hinj : Function.Injective (weakBidualToFun E) := by
          intro x y h
          exact DFunLike.coe_injective (F := Module.Dual ℂ (StrongDual ℂ E)) h
        exact hinj.isEmbedding_induced.t0Space
      dense := weakBidualEval_dense E }

/-- Lemma C.4.1.2(1). Weak and original convex closures agree. When the
original closure is compact, its bidual image is the closure of the image. -/
theorem weakBidual_convex_closure [Module ℝ E] [IsScalarTower ℝ ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) :
    (toWeakSpace ℂ E) '' closure s = closure ((toWeakSpace ℂ E) '' s) ∧
      (IsCompact (closure s) → weakBidualEval E '' closure s = closure (weakBidualEval E '' s)) := by
  refine ⟨hs.toWeakSpace_closure ℂ, fun hK => ?_⟩
  have hcont := weakBidualEval_continuous E
  apply Set.Subset.antisymm (hcont.continuousOn.image_closure)
  haveI : T2Space (WeakAlgebraicBidual E) :=
    (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ]
      Module.Dual ℂ (StrongDual ℂ E))) Function.injective_id).t2Space
  exact closure_minimal (image_mono subset_closure) (hK.image hcont).isClosed

/-- Lemma C.4.1.2(2). The weak-bidual evaluation on a normed space factors
through its isometric inclusion in the continuous bidual. -/
theorem weakBidualEval_normed_factors {N : Type*} [NormedAddCommGroup N] [NormedSpace ℂ N] :
    Isometry (NormedSpace.inclusionInDoubleDual ℂ N) ∧
    ∀ x : N, (weakBidualEval N x : Module.Dual ℂ (StrongDual ℂ N)) =
      (NormedSpace.inclusionInDoubleDual ℂ N x).toLinearMap :=
  ⟨(NormedSpace.inclusionInDoubleDualLi (E := N) ℂ).isometry, fun _ => rfl⟩

end WeakCompletion

section MeanValue

variable {X E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]

/-- The complex absolutely convex hull, including zero in the empty case. -/
def complexAbsConvexHull (s : Set E) : Set E :=
  convexHull ℝ (Metric.closedBall (0 : ℂ) 1 • insert 0 s)

private theorem phase_normalizes (z : ℂ) :
    ∃ a : ℂ, ‖a‖ ≤ 1 ∧ (a * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hne : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  refine ⟨(starRingEnd ℂ z) / (‖z‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp.le, div_self hp.ne']
  · rw [div_mul_eq_mul_div, mul_comm (starRingEnd ℂ z) z, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_div, Complex.ofReal_re, pow_two,
      mul_div_cancel_right₀ _ hp.ne']

omit [IsScalarTower ℝ ℂ E] in
private theorem zero_mem_complexAbsConvexHull (s : Set E) : 0 ∈ complexAbsConvexHull s :=
  subset_convexHull ℝ _ ⟨0, by simp, 0, mem_insert _ _, zero_smul _ _⟩

omit [IsScalarTower ℝ ℂ E] in
theorem complexAbsConvexHull_of_nonempty {s : Set E} (hs : s.Nonempty) :
    complexAbsConvexHull s = convexHull ℝ (Metric.closedBall (0 : ℂ) 1 • s) := by
  have he : Metric.closedBall (0 : ℂ) 1 • insert 0 s = Metric.closedBall (0 : ℂ) 1 • s := by
    apply Subset.antisymm
    · rintro _ ⟨a, ha, y, hy, rfl⟩
      rcases mem_insert_iff.mp hy with rfl | hy
      · obtain ⟨x, hx⟩ := hs
        exact ⟨0, by simp, x, hx, (zero_smul _ _).trans (smul_zero a).symm⟩
      · exact ⟨a, ha, y, hy, rfl⟩
    · rintro _ ⟨a, ha, y, hy, rfl⟩
      exact ⟨a, ha, y, mem_insert_of_mem _ hy, rfl⟩
  exact congrArg (convexHull ℝ) he

theorem complexAbsConvexHull_balanced (s : Set E) : Balanced ℂ (complexAbsConvexHull s) := by
  intro a ha y hy
  obtain ⟨x, hx, rfl⟩ := mem_smul_set.mp hy
  let L : E →ₗ[ℝ] E := (LinearMap.lsmul ℂ E a).restrictScalars ℝ
  change x ∈ L ⁻¹' complexAbsConvexHull s
  refine convexHull_min ?_ ((convex_convexHull ℝ _).linear_preimage L) hx
  rintro _ ⟨b, hb, z, hz, rfl⟩
  apply subset_convexHull ℝ
  change a • (b • z) ∈ Metric.closedBall (0 : ℂ) 1 • insert 0 s
  have hb' : ‖b‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  exact ⟨a * b, by simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul] using
    (mul_le_one₀ ha (norm_nonneg _) hb'), z, hz, mul_smul _ _ _⟩

omit [IsScalarTower ℝ ℂ E] in
theorem complexAbsConvexHull_min {s T : Set E} (hs : s ⊆ T) (hzero : 0 ∈ T)
    (hb : Balanced ℂ T) (hT : Convex ℝ T) : complexAbsConvexHull s ⊆ T := by
  refine convexHull_min ?_ hT
  rintro _ ⟨a, ha, z, hz, rfl⟩
  exact hb a (by simpa only [Metric.mem_closedBall, dist_zero_right] using ha) <|
    smul_mem_smul_set <| insert_subset hzero hs hz

variable [TopologicalSpace E]

/-- A weak bidual vector lies in the closure of a convex set when all real parts
of its evaluations satisfy the scalar upper bounds of the set. -/
theorem weakBidual_mem_closure_of_le {C : Set E} (hC : Convex ℝ C)
    (v : WeakAlgebraicBidual E)
    (h : ∀ (ℓ : StrongDual ℂ E) (b : ℝ), (∀ x ∈ C, (ℓ x).re < b) →
      (weakBidualToFun E v ℓ).re ≤ b) :
    v ∈ closure (weakBidualEval E '' C) := by
  classical
  have hP : IsInducing (weakBidualToFun E) := ⟨rfl⟩
  apply mem_closure_iff_nhds.mpr
  intro S hS
  rw [hP.nhds_eq_comap] at hS
  obtain ⟨U, hU, hUS⟩ := mem_comap.mp hS
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨s, w, hw, hwU⟩ := hU
  let Q : E →L[ℂ] (s → ℂ) := ContinuousLinearMap.pi fun ℓ : s => ℓ.val
  let k : s → ℂ := fun ℓ => weakBidualToFun E v ℓ.val
  have hk : k ∈ closure (Q '' C) := by
    by_contra hn
    have hconv : Convex ℝ (Q '' C) := hC.linear_image (Q.restrictScalars ℝ).toLinearMap
    obtain ⟨L, b, hb, hbk⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconv.closure isClosed_closure hn
    let ℓ := L.comp Q
    obtain ⟨u, hu⟩ := weakBidualEval_matches_finset E v (insert ℓ s)
    have huQ : Q u = k := funext fun j => hu j.val (Finset.mem_insert_of_mem j.property)
    have hLk : L k = weakBidualToFun E v ℓ := by
      rw [← huQ]
      exact hu ℓ (Finset.mem_insert_self _ _)
    rw [hLk] at hbk
    exact hbk.not_ge (h ℓ b fun x hx => hb (Q x) (subset_closure (mem_image_of_mem Q hx)))
  let V : Set (s → ℂ) := Set.pi univ fun ℓ => w ℓ.val
  have hV : V ∈ 𝓝 k :=
    set_pi_mem_nhds (finite_univ : (univ : Set s).Finite) fun ℓ _ => hw ℓ.val
  obtain ⟨_, hy, x, hx, rfl⟩ := mem_closure_iff_nhds.mp hk V hV
  refine ⟨weakBidualEval E x, hUS (hwU ?_), mem_image_of_mem _ hx⟩
  intro ℓ hℓ
  exact hy (i := ⟨ℓ, hℓ⟩) (mem_univ _)

variable [MeasurableSpace X]

/-- Lemma C.4.3.1 with zero included in the hull when the domain is empty.
The proof separates a finite tuple of evaluations and applies the scalar
total-variation inequality after rotating each value to the positive axis. -/
theorem weakPettisIntegral_mem_closedHull (μ : VectorMeasure X ℂ)
    [IsFiniteMeasure μ.variation] (f : X → E)
    (hf : ∀ ℓ : StrongDual ℂ E, μ.Integrable (ℓ ∘ f)) :
    (show WeakAlgebraicBidual E from weakPettisIntegral μ f hf) ∈
      closure (weakBidualEval E '' (μ.variation.real univ • complexAbsConvexHull (range f))) := by
  classical
  let M := μ.variation.real univ
  let C : Set E := M • complexAbsConvexHull (range f)
  have hC : Convex ℝ C := (convex_convexHull ℝ _).smul M
  have hzero : (0 : E) ∈ C :=
    ⟨0, zero_mem_complexAbsConvexHull _, smul_zero M⟩
  let v : WeakAlgebraicBidual E := weakPettisIntegral μ f hf
  change v ∈ closure (weakBidualEval E '' C)
  by_cases hM : M = 0
  · have hm : μ.variation = 0 := Measure.measure_univ_eq_zero.mp
      ((ENNReal.toReal_eq_zero_iff _).mp hM |>.resolve_right (measure_ne_top _ _))
    have hv : v = weakBidualEval E 0 := by
      change weakPettisIntegral μ f hf = (weakBidualEval E 0 : Module.Dual ℂ (StrongDual ℂ E))
      ext ℓ
      change complexMeasureIntegral μ (ℓ ∘ f) = ℓ 0
      have he : (ℓ ∘ f) =ᵐ[μ.variation] (fun _ => (0 : ℂ)) := by
        rw [hm, ae_zero]
        exact Filter.eventually_bot
      rw [map_zero, complexMeasureIntegral, VectorMeasure.integral_congr_ae he]
      exact VectorMeasure.integral_zero
    exact subset_closure ⟨0, hzero, hv.symm⟩
  have hMpos : 0 < M := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
  apply weakBidual_mem_closure_of_le hC v
  intro ℓ b hb
  have hb0 : 0 ≤ b := by
    have hh := hb 0 hzero
    simpa using hh.le
  have hnorm (x : X) : ‖ℓ (f x)‖ ≤ b / M := by
    obtain ⟨a, ha, haz⟩ := phase_normalizes (ℓ (f x))
    have hy : M • (a • f x) ∈ C :=
      ⟨a • f x, subset_convexHull ℝ _
        ⟨a, by simpa [Metric.mem_closedBall, dist_zero_right] using ha,
          f x, mem_insert_of_mem _ (mem_range_self x), rfl⟩, rfl⟩
    have hh := hb (M • (a • f x)) hy
    change (ℓ (M • (a • f x))).re < b at hh
    rw [← algebraMap_smul ℂ M (a • f x), map_smul, map_smul, smul_eq_mul,
      smul_eq_mul] at hh
    change ((M : ℂ) * (a * ℓ (f x))).re < b at hh
    rw [Complex.re_ofReal_mul, haz] at hh
    apply (le_div_iff₀ hMpos).mpr
    simpa [mul_comm] using hh.le
  have hbound := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) (f := ℓ ∘ f)
    (Eventually.of_forall hnorm)
  have h' : ‖complexMeasureIntegral μ (ℓ ∘ f)‖ ≤ b := by
    apply hbound.trans
    calc
      (b / M) * ‖ContinuousLinearMap.mul ℝ ℂ‖ * M ≤ (b / M) * 1 * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left complexMul_norm_le_one (div_nonneg hb0 hMpos.le)) hMpos.le
      _ = b := by rw [mul_one, div_mul_cancel₀ _ hM]
  exact (Complex.re_le_norm _).trans h'

/-- In the weak bidual, the scale can be placed outside the closure. -/
theorem weakPettisIntegral_mem_scaledHull (μ : VectorMeasure X ℂ)
    [IsFiniteMeasure μ.variation] (f : X → E)
    (hf : ∀ ℓ : StrongDual ℂ E, μ.Integrable (ℓ ∘ f)) :
    (show WeakAlgebraicBidual E from weakPettisIntegral μ f hf) ∈
      (μ.variation.real univ : ℂ) •
        closure (weakBidualEval E '' complexAbsConvexHull (range f)) := by
  haveI : T2Space (WeakAlgebraicBidual E) :=
    (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ]
      Module.Dual ℂ (StrongDual ℂ E))) Function.injective_id).t2Space
  have h := weakPettisIntegral_mem_closedHull μ f hf
  have hs (x : E) : weakBidualEval E (μ.variation.real univ • x) =
      (μ.variation.real univ : ℂ) • weakBidualEval E x := by
    rw [← algebraMap_smul ℂ]
    exact map_smul (weakBidualEval E) _ x
  have he :
      weakBidualEval E '' (μ.variation.real univ • complexAbsConvexHull (range f)) =
        (μ.variation.real univ : ℂ) • (weakBidualEval E '' complexAbsConvexHull (range f)) := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨weakBidualEval E x, mem_image_of_mem _ hx,
        (hs x).symm⟩
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨μ.variation.real univ • x, ⟨x, hx, rfl⟩,
        hs x⟩
  rwa [he, closure_smul₀] at h

end MeanValue

section CompactSupport

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E]

/-- C.4.3.5 and the repaired (C.4.3.3). The representing integral lies in the
closed absolutely convex hull scaled by the total variation of the support. -/
theorem pettis_exists_of_hasCompactSupport (μ : VectorMeasure X ℂ)
    [IsFiniteMeasure μ.variation] {f : X → E}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ u ∈ μ.variation.real (tsupport f) • closure (complexAbsConvexHull (range f)),
      HasPettisIntegral μ f u := by
  haveI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let S := tsupport f
  have hS : MeasurableSet S := isClosed_closure.measurableSet
  let ν := μ.restrict S
  have hintμ (ℓ : StrongDual ℂ E) : μ.Integrable (ℓ ∘ f) := by
    have hcont : Continuous (ℓ ∘ f) := ℓ.continuous.comp hf
    obtain ⟨C, hC⟩ := (hc.isCompact_range hf).exists_bound_of_continuousOn ℓ.continuous.continuousOn
    exact (integrable_const C).mono' hcont.measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => hC (f x) (mem_range_self x))
  have hint (ℓ : StrongDual ℂ E) : ν.Integrable (ℓ ∘ f) := (hintμ ℓ).integrableOn
  let K := complexAbsConvexHull (range f)
  have hset : IsCompact (Metric.closedBall (0 : ℂ) 1 • insert 0 (range f)) := by
    rw [← Set.image2_smul, ← Set.image_prod]
    exact ((isCompact_closedBall _ _).prod ((hc.isCompact_range hf).insert 0)).image
      (continuous_fst.smul continuous_snd)
  have hK : IsCompact (closure K) :=
    isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := ℂ) hset.totallyBounded.convexHull
  let M := ν.variation.real univ
  let C : Set E := M • K
  have hv := weakPettisIntegral_mem_closedHull ν f hint
  have hMeq : M = μ.variation.real S := by
    change (μ.restrict S).variation.real univ = _
    rw [Measure.real, VectorMeasure.variation_restrict hS,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.real]
  have hC : Convex ℝ C := (convex_convexHull ℝ _).smul M
  have hCK : IsCompact (closure C) := by
    change IsCompact (closure (M • K))
    rw [closure_smul₀]
    exact hK.smul M
  rw [← (weakBidual_convex_closure E hC).2 hCK] at hv
  obtain ⟨u, hu, hue⟩ := hv
  refine ⟨u, ?_, fun ℓ => ⟨hintμ ℓ, ?_⟩⟩
  · change u ∈ closure (M • K) at hu
    rwa [closure_smul₀, hMeq] at hu
  · have he := congrArg (fun v : WeakAlgebraicBidual E => weakBidualToFun E v ℓ) hue
    change ℓ u = complexMeasureIntegral ν (ℓ ∘ f) at he
    rw [he]
    have hzero : S.indicator (ℓ ∘ f) = ℓ ∘ f := by
      funext x
      by_cases hx : x ∈ S
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        exact ((congrArg ℓ (image_eq_zero_of_notMem_tsupport hx)).trans (map_zero ℓ)).symm
    unfold complexMeasureIntegral
    rw [← VectorMeasure.integral_indicator hS, hzero]

end CompactSupport

section PositiveProduct

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The algebraic-dual Pettis integral for positive measures, including
measures that are not finite on the whole space. -/
noncomputable def positiveWeakPettisIntegral (μ : Measure X) (f : X → E)
    (hf : ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ f) μ) :
    Module.Dual ℂ (StrongDual ℂ E) where
  toFun ℓ := ∫ x, ℓ (f x) ∂μ
  map_add' ℓ m := integral_add (hf ℓ) (hf m)
  map_smul' c ℓ := integral_smul c (ℓ ∘ f)

/-- The positive-measure version of the represented Pettis integral. -/
def HasPositivePettisIntegral (μ : Measure X) (f : X → E) (u : E) : Prop :=
  ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ f) μ ∧ ℓ u = ∫ x, ℓ (f x) ∂μ

/-- C.4.4.1. Both represented inner integrals are weakly integrable,
and all three weak integrals agree on each continuous functional. -/
theorem pettis_fubini (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X × Y → E) (h : ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ f) (μ.prod ν))
    (g : X → E) (k : Y → E)
    (hg : ∀ x, HasPositivePettisIntegral ν (fun y => f (x, y)) (g x))
    (hk : ∀ y, HasPositivePettisIntegral μ (fun x => f (x, y)) (k y)) :
    ∃ (hμ : ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ g) μ)
      (hν : ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ k) ν),
      positiveWeakPettisIntegral (μ.prod ν) f h = positiveWeakPettisIntegral μ g hμ ∧
      positiveWeakPettisIntegral (μ.prod ν) f h = positiveWeakPettisIntegral ν k hν := by
  have hgy (ℓ : StrongDual ℂ E) : (ℓ ∘ g) = fun x => ∫ y, ℓ (f (x, y)) ∂ν :=
    funext fun x => (hg x ℓ).2
  have hkx (ℓ : StrongDual ℂ E) : (ℓ ∘ k) = fun y => ∫ x, ℓ (f (x, y)) ∂μ :=
    funext fun y => (hk y ℓ).2
  have hμ (ℓ : StrongDual ℂ E) : Integrable (ℓ ∘ g) μ := hgy ℓ ▸ (h ℓ).integral_prod_left
  have hν (ℓ : StrongDual ℂ E) : Integrable (ℓ ∘ k) ν := hkx ℓ ▸ (h ℓ).integral_prod_right
  refine ⟨hμ, hν, LinearMap.ext fun ℓ => ?_, LinearMap.ext fun ℓ => ?_⟩
  · change ∫ z, (ℓ ∘ f) z ∂(μ.prod ν) = ∫ x, (ℓ ∘ g) x ∂μ
    rw [hgy ℓ]
    exact integral_prod (ℓ ∘ f) (h ℓ)
  · change ∫ z, (ℓ ∘ f) z ∂(μ.prod ν) = ∫ y, (ℓ ∘ k) y ∂ν
    rw [hkx ℓ]
    exact integral_prod_symm (ℓ ∘ f) (h ℓ)

end PositiveProduct

section ProbabilityHull

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

omit [T2Space X] in
private theorem eval_integrable_of_compact (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → E} (hf : Continuous f) (ℓ : StrongDual ℂ E) : Integrable (ℓ ∘ f) μ :=
  (ℓ.continuous.comp hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Regard the Pettis integrals of a continuous function as a function
of the probability measure, with values in the weak algebraic bidual. -/
noncomputable def probabilityPettisIntegral {f : X → E} (hf : Continuous f)
    (μ : ProbabilityMeasure X) : WeakAlgebraicBidual E :=
  positiveWeakPettisIntegral (μ : Measure X) f (eval_integrable_of_compact _ hf)

omit [T2Space X] in
private theorem probability_integral_continuous {g : X → ℂ} (hg : Continuous g) :
    Continuous fun μ : ProbabilityMeasure X => ∫ x, g x ∂(μ : Measure X) := by
  have hg' (μ : ProbabilityMeasure X) : Integrable g (μ : Measure X) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : Continuous fun μ : ProbabilityMeasure X => (∫ x, g x ∂(μ : Measure X)).re := by
    have he (μ : ProbabilityMeasure X) :
        (∫ x, g x ∂(μ : Measure X)).re = ∫ x, (g x).re ∂(μ : Measure X) :=
      (integral_re (hg' μ)).symm
    simp_rw [he]
    exact ProbabilityMeasure.continuous_integral_continuousMap
      (⟨_, Complex.continuous_re.comp hg⟩ : C(X, ℝ))
  have hi : Continuous fun μ : ProbabilityMeasure X => (∫ x, g x ∂(μ : Measure X)).im := by
    have he (μ : ProbabilityMeasure X) :
        (∫ x, g x ∂(μ : Measure X)).im = ∫ x, (g x).im ∂(μ : Measure X) :=
      (integral_im (hg' μ)).symm
    simp_rw [he]
    exact ProbabilityMeasure.continuous_integral_continuousMap
      (⟨_, Complex.continuous_im.comp hg⟩ : C(X, ℝ))
  exact Complex.equivRealProdCLM.symm.continuous.comp (hr.prodMk hi)

omit [T2Space X] in
/-- Weak continuity of the probability barycentre map. -/
theorem probabilityPettisIntegral_continuous {f : X → E} (hf : Continuous f) :
    Continuous (probabilityPettisIntegral hf) :=
  WeakBilin.continuous_of_continuous_eval _ fun ℓ =>
    probability_integral_continuous (ℓ.continuous.comp hf)

private theorem probabilityPettisIntegral_dirac {f : X → E} (hf : Continuous f) (x : X) :
    probabilityPettisIntegral hf ⟨Measure.dirac x, by infer_instance⟩ = weakBidualEval E (f x) := by
  refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_
  exact integral_dirac _ x

variable [Module ℝ E] [IsScalarTower ℝ ℂ E]

/-- C.4.3.2(1), the weakly closed convex hull is the compact image of
probability measures. -/
theorem probabilityPettisIntegral_range_eq {f : X → E} (hf : Continuous f) :
    range (probabilityPettisIntegral hf) =
      closure (weakBidualEval E '' convexHull ℝ (range f)) ∧
    IsCompact (range (probabilityPettisIntegral hf)) := by
  classical
  have hK : IsCompact (range (probabilityPettisIntegral hf)) :=
    isCompact_range (probabilityPettisIntegral_continuous hf)
  haveI : T2Space (WeakAlgebraicBidual E) :=
    (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ]
      Module.Dual ℂ (StrongDual ℂ E))) Function.injective_id).t2Space
  refine ⟨Subset.antisymm ?_ ?_, hK⟩
  · rintro _ ⟨μ, rfl⟩
    apply weakBidual_mem_closure_of_le (convex_convexHull ℝ _) _
    intro ℓ b hb
    change (∫ x, ℓ (f x) ∂(μ : Measure X)).re ≤ b
    have he : (∫ x, ℓ (f x) ∂(μ : Measure X)).re =
        ∫ x, (ℓ (f x)).re ∂(μ : Measure X) :=
      (integral_re (eval_integrable_of_compact _ hf ℓ)).symm
    rw [he]
    have hh : Integrable (fun x => (ℓ (f x)).re) (μ : Measure X) :=
      (eval_integrable_of_compact _ hf ℓ).re
    have hle := integral_mono hh (integrable_const b)
      (fun x => (hb (f x) (subset_convexHull ℝ _ (mem_range_self x))).le)
    simpa using hle
  · apply closure_minimal _ hK.isClosed
    let R : Set E := (weakBidualEval E) ⁻¹' range (probabilityPettisIntegral hf)
    have hs : range f ⊆ R := by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨Measure.dirac x, by infer_instance⟩, probabilityPettisIntegral_dirac hf x⟩
    have hR : Convex ℝ R := by
      rintro x ⟨μ, hμ⟩ y ⟨ν, hν⟩ a b ha hb hab
      let ρ : Measure X := ENNReal.ofReal a • (μ : Measure X) + ENNReal.ofReal b • (ν : Measure X)
      haveI : IsProbabilityMeasure ρ :=
        ⟨by simp [ρ, ← ENNReal.ofReal_add ha hb, hab]⟩
      refine ⟨⟨ρ, inferInstance⟩, ?_⟩
      refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_
      have heμ := congrArg (fun v : WeakAlgebraicBidual E => weakBidualToFun E v ℓ) hμ
      have heν := congrArg (fun v : WeakAlgebraicBidual E => weakBidualToFun E v ℓ) hν
      change ∫ z, ℓ (f z) ∂(μ : Measure X) = ℓ x at heμ
      change ∫ z, ℓ (f z) ∂(ν : Measure X) = ℓ y at heν
      change ∫ z, ℓ (f z) ∂ρ = ℓ (a • x + b • y)
      rw [integral_add_measure, integral_smul_measure, integral_smul_measure,
        heμ, heν, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, map_add]
      · exact congrArg₂ (· + ·) ((ℓ.restrictScalars ℝ).map_smul a x).symm
          ((ℓ.restrictScalars ℝ).map_smul b y).symm
      · exact (eval_integrable_of_compact _ hf ℓ).smul_measure ENNReal.ofReal_ne_top
      · exact (eval_integrable_of_compact _ hf ℓ).smul_measure ENNReal.ofReal_ne_top
    exact image_subset_iff.mpr (convexHull_min hs hR)

/-- Regular probabilities give the same range as all probabilities, since
the regular representative agrees on all continuous scalar evaluations. -/
theorem regularProbabilityPettisIntegral_range_eq {f : X → E} (hf : Continuous f) :
    probabilityPettisIntegral hf '' {μ : ProbabilityMeasure X | (μ : Measure X).Regular} =
      closure (weakBidualEval E '' convexHull ℝ (range f)) ∧
    IsCompact (probabilityPettisIntegral hf '' {μ : ProbabilityMeasure X | (μ : Measure X).Regular}) := by
  have he : probabilityPettisIntegral hf '' {μ : ProbabilityMeasure X | (μ : Measure X).Regular} =
      range (probabilityPettisIntegral hf) := by
    apply Subset.antisymm (image_subset_range _ _)
    rintro _ ⟨μ, rfl⟩
    obtain ⟨ν, hν, hνfin, hνint⟩ := (μ : Measure X).exists_regular_eq_of_compactSpace
    have h1 := hνint (BoundedContinuousFunction.const X (1 : ℝ))
    change (∫ _ : X, (1 : ℝ) ∂(μ : Measure X)) = ∫ _ : X, (1 : ℝ) ∂ν at h1
    simp only [integral_const, MeasureTheory.measureReal_def, smul_eq_mul, mul_one,
      measure_univ, ENNReal.toReal_one] at h1
    haveI : IsProbabilityMeasure ν := ⟨(ENNReal.toReal_eq_one_iff _).mp h1.symm⟩
    let p : ProbabilityMeasure X := ⟨ν, inferInstance⟩
    refine ⟨p, hν, DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_⟩
    change (∫ x, ℓ (f x) ∂ν) = ∫ x, ℓ (f x) ∂(μ : Measure X)
    let g := (ℓ : E → ℂ) ∘ f
    have hg := ℓ.continuous.comp hf
    let r : CompactlySupportedContinuousMap X ℝ :=
      ⟨⟨_, Complex.continuous_re.comp hg⟩, HasCompactSupport.of_compactSpace _⟩
    let i : CompactlySupportedContinuousMap X ℝ :=
      ⟨⟨_, Complex.continuous_im.comp hg⟩, HasCompactSupport.of_compactSpace _⟩
    apply Complex.ext
    · exact (integral_re (eval_integrable_of_compact ν hf ℓ)).symm.trans
        ((hνint r.toBoundedContinuousFunction).symm.trans
          (integral_re (eval_integrable_of_compact (μ : Measure X) hf ℓ)))
    · exact (integral_im (eval_integrable_of_compact ν hf ℓ)).symm.trans
        ((hνint i.toBoundedContinuousFunction).symm.trans
          (integral_im (eval_integrable_of_compact (μ : Measure X) hf ℓ)))
  rw [he]
  exact probabilityPettisIntegral_range_eq hf

end ProbabilityHull

section ComplexDensity

variable {X : Type*} [MeasurableSpace X]

theorem complexDensity_variation_le (μ : Measure X) {w : X → ℂ}
    (hw : Integrable w μ) (hb : ∀ x, ‖w x‖ ≤ 1) :
    (μ.withDensityᵥ w).variation ≤ μ := by
  rw [Measure.variation_withDensityᵥ hw]
  have he : (fun x => ‖w x‖ₑ) ≤ᵐ[μ] (1 : X → ℝ≥0∞) :=
    Eventually.of_forall fun x => by
      change ‖w x‖ₑ ≤ 1
      simpa only [← ofReal_norm, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hb x)
  exact (withDensity_mono he).trans_eq (withDensity_one (μ := μ))

set_option maxHeartbeats 800000 in
/-- Integrating against a complex density of modulus at most one agrees
with integrating the product of the integrand and density. -/
theorem complexMeasureIntegral_withDensity (μ : Measure X) [IsFiniteMeasure μ]
    {w g : X → ℂ} (hw : Integrable w μ) (hb : ∀ x, ‖w x‖ ≤ 1)
    (hg : Measurable g) (hgi : Integrable g μ) :
    complexMeasureIntegral (μ.withDensityᵥ w) g = ∫ x, g x * w x ∂μ := by
  classical
  let ν := μ.withDensityᵥ w
  have hν : ν.variation ≤ μ := complexDensity_variation_le μ hw hb
  letI : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le μ hν
  have hprod (F : X → ℂ) (hf : Measurable F) (hi : Integrable F μ) :
      Integrable (fun x => F x * w x) μ := by
    apply hi.norm.mono' (hf.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖F x * w x‖ ≤ ‖F x‖
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb x)
  have hsi (s : SimpleFunc X ℂ) : Integrable s μ := by
    obtain ⟨C, hC⟩ := (s.finite_range.image norm).bddAbove
    exact Integrable.of_bound s.measurable.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (mem_image_of_mem norm (mem_range_self x)))
  have hsimple (s : SimpleFunc X ℂ) :
      complexMeasureIntegral ν s = ∫ x, s x * w x ∂μ := by
    induction s using SimpleFunc.induction with
    | @const c S hS =>
      change complexMeasureIntegral ν (S.indicator fun _ => c) =
        ∫ x, S.indicator (fun _ => c) x * w x ∂μ
      have he : (fun x => S.indicator (fun _ => c) x * w x) =
          S.indicator (fun x => c * w x) := by
        funext x
        by_cases hx : x ∈ S <;> simp [hx]
      rw [he, complexMeasureIntegral, VectorMeasure.integral_indicator_const _ hS,
        integral_indicator hS, integral_const_mul]
      exact congrArg (c * ·) (withDensityᵥ_apply hw hS)
    | @add s t _ hs ht =>
      change complexMeasureIntegral ν ((s : X → ℂ) + t) =
        ∫ x, (s x + t x) * w x ∂μ
      rw [complexMeasureIntegral,
        VectorMeasure.integral_add ((hsi s).mono_measure hν) ((hsi t).mono_measure hν)]
      change complexMeasureIntegral ν s + complexMeasureIntegral ν t = _
      simp_rw [add_mul]
      rw [hs, ht, integral_add (hprod _ s.measurable (hsi s)) (hprod _ t.measurable (hsi t))]
  let A := SimpleFunc.approxOn g hg (univ : Set ℂ) 0 (mem_univ 0)
  have ha (n : ℕ) (x : X) : ‖A n x‖ ≤ ‖g x‖ + ‖g x‖ :=
    SimpleFunc.norm_approxOn_zero_le hg (mem_univ 0) x n
  have ht (x : X) : Tendsto (fun n => A n x) atTop (𝓝 (g x)) :=
    SimpleFunc.tendsto_approxOn hg (mem_univ 0) (subset_closure (mem_univ _))
  have hB : Integrable (fun x => ‖g x‖ + ‖g x‖) μ := hgi.norm.add hgi.norm
  have hL : Tendsto (fun n => complexMeasureIntegral ν (A n)) atTop
      (𝓝 (complexMeasureIntegral ν g)) := by
    apply VectorMeasure.tendsto_integral_of_dominated_convergence (bound := fun x => ‖g x‖ + ‖g x‖)
    · exact fun n => (A n).measurable.aestronglyMeasurable
    · exact hB.mono_measure hν
    · exact fun n => Eventually.of_forall (ha n)
    · exact Eventually.of_forall ht
  have hR := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n x => A n x * w x) (f := fun x => g x * w x)
    (fun x => ‖g x‖ + ‖g x‖)
    (fun n => (A n).measurable.aestronglyMeasurable.mul hw.aestronglyMeasurable) hB
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hb x)).trans (ha n x))
    (Eventually.of_forall fun x => (ht x).mul tendsto_const_nhds)
  exact tendsto_nhds_unique (hL.congr (fun n => hsimple (A n))) hR

end ComplexDensity

section ComplexHull

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [ContinuousSMul ℂ E]

omit [CompactSpace X] in
private theorem regular_of_le_finite_innerRegular {ν μ : Measure X} [IsFiniteMeasure μ]
    [μ.InnerRegular] (hle : ν ≤ μ) : ν.Regular := by
  letI : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hle
  letI : ν.InnerRegular := ⟨by
    intro S hS r hr
    obtain ⟨K, hKS, hK, hKd⟩ := hS.exists_isCompact_sdiff_lt (measure_ne_top μ S)
      (μ := μ) (ne_of_gt (tsub_pos_of_lt hr))
    refine ⟨K, hKS, hK, ?_⟩
    have hd := (hle (S \ K)).trans_lt hKd
    rw [measure_sdiff hKS hK.measurableSet.nullMeasurableSet (measure_ne_top ν K)] at hd
    have hd' := (ENNReal.sub_lt_iff_lt_right (measure_ne_top ν K) (measure_mono hKS)).mp hd
    by_contra! hn
    exact hd'.not_ge ((add_le_add le_rfl hn).trans_eq (tsub_add_cancel_of_le hr.le))⟩
  infer_instance

/-- Weak Pettis integrals of a continuous function against complex Radon
measures of variation at most one. -/
def complexUnitPettisIntegrals (f : X → E) : Set (WeakAlgebraicBidual E) :=
  {v | ∃ μ : VectorMeasure X ℂ, μ.variation.Regular ∧ μ.variation univ ≤ 1 ∧
    ∃ hf : ∀ ℓ : StrongDual ℂ E, μ.Integrable (ℓ ∘ f),
      v = (show WeakAlgebraicBidual E from weakPettisIntegral μ f hf)}

set_option maxHeartbeats 800000 in
/-- C.4.3.2(2). The closed absolutely convex hull is the compact image of
complex Radon measures of variation at most one. A regular probability
on the product with the closed unit disk yields its complex density. -/
theorem complexUnitPettisIntegrals_eq {f : X → E} (hf : Continuous f) :
    complexUnitPettisIntegrals f =
      closure (weakBidualEval E '' complexAbsConvexHull (range f)) ∧
    IsCompact (complexUnitPettisIntegrals f) := by
  let C := complexAbsConvexHull (range f)
  have hC : Convex ℝ C := convex_convexHull ℝ _
  have hc0 : 0 ∈ C := zero_mem_complexAbsConvexHull _
  have hforward : complexUnitPettisIntegrals f ⊆ closure (weakBidualEval E '' C) := by
    rintro _ ⟨μ, _, hm, hμ, rfl⟩
    letI : IsFiniteMeasure μ.variation := ⟨hm.trans_lt ENNReal.one_lt_top⟩
    have h := weakPettisIntegral_mem_closedHull μ f hμ
    exact closure_mono (image_mono (show μ.variation.real univ • C ⊆ C from by
      rintro _ ⟨x, hx, rfl⟩
      exact hC.smul_mem_of_zero_mem hc0 hx ⟨ENNReal.toReal_nonneg,
        by simpa [MeasureTheory.measureReal_def] using ENNReal.toReal_mono ENNReal.one_ne_top hm⟩)) h
  by_cases hX : Nonempty X
  · letI := hX
    let D := Metric.closedBall (0 : ℂ) 1
    letI : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    let g : X × D → E := fun p => (p.2 : ℂ) • f p.1
    have hg : Continuous g := (continuous_subtype_val.comp continuous_snd).smul
      (hf.comp continuous_fst)
    have hr : range g = D • range f := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.2.val, p.2.property, f p.1, mem_range_self _, rfl⟩
      · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
        exact ⟨(x, ⟨a, ha⟩), rfl⟩
    have hCg : C = convexHull ℝ (range g) := by
      rw [hr]
      exact complexAbsConvexHull_of_nonempty (range_nonempty f)
    have hprob := regularProbabilityPettisIntegral_range_eq hg
    have hback : closure (weakBidualEval E '' C) ⊆ complexUnitPettisIntegrals f := by
      intro v hv
      rw [hCg, ← hprob.1] at hv
      obtain ⟨ρ, hρ, rfl⟩ := hv
      letI : (ρ : Measure (X × D)).Regular := hρ
      let w : X × D → ℂ := fun p => p.2.val
      have hw : Continuous w := continuous_subtype_val.comp continuous_snd
      have hb (p : X × D) : ‖w p‖ ≤ 1 := by
        have hp : dist (w p) 0 ≤ 1 := p.2.property
        simpa only [dist_zero_right] using hp
      have hwi : Integrable w (ρ : Measure (X × D)) :=
        Integrable.of_bound hw.measurable.aestronglyMeasurable 1 (Eventually.of_forall hb)
      let σ := (ρ : Measure (X × D)).withDensityᵥ w
      let μ : VectorMeasure X ℂ := σ.map Prod.fst
      have hσ : σ.variation ≤ (ρ : Measure (X × D)) :=
        complexDensity_variation_le _ hwi hb
      haveI : IsFiniteMeasure σ.variation := isFiniteMeasure_of_le _ hσ
      have hμ : μ.variation ≤ (ρ : Measure (X × D)).map Prod.fst :=
        VectorMeasure.variation_map_le.trans (Measure.map_mono hσ measurable_fst)
      haveI : Measure.InnerRegular ((ρ : Measure (X × D)).map Prod.fst) :=
        Measure.InnerRegular.map_of_continuous continuous_fst
      haveI : IsFiniteMeasure μ.variation := isFiniteMeasure_of_le _ hμ
      have hint (ℓ : StrongDual ℂ E) : μ.Integrable (ℓ ∘ f) :=
        eval_integrable_of_compact _ hf ℓ
      refine ⟨μ, regular_of_le_finite_innerRegular hμ, ?_, hint, ?_⟩
      · exact (hμ univ).trans_eq (by rw [Measure.map_apply measurable_fst MeasurableSet.univ,
          preimage_univ, measure_univ])
      · refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_
        change (∫ p, ℓ (g p) ∂(ρ : Measure (X × D))) = complexMeasureIntegral μ (ℓ ∘ f)
        have hφ : Continuous (ℓ ∘ f) := ℓ.continuous.comp hf
        have hfi : Integrable (fun p : X × D => ℓ (f p.1)) (ρ : Measure (X × D)) :=
          (hφ.comp continuous_fst).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        unfold complexMeasureIntegral
        rw [VectorMeasure.integral_map (μ := σ) measurable_fst hφ.measurable.aestronglyMeasurable
          (hfi.mono_measure hσ)]
        change _ = complexMeasureIntegral σ ((ℓ ∘ f) ∘ Prod.fst)
        rw [complexMeasureIntegral_withDensity _ hwi hb (hφ.measurable.comp measurable_fst) hfi]
        congr 1 with p
        change ℓ (w p • f p.1) = ℓ (f p.1) * w p
        rw [map_smul, smul_eq_mul, mul_comm]
    have he := Subset.antisymm hforward hback
    refine ⟨he, ?_⟩
    rw [he, hCg, ← hprob.1]
    exact hprob.2
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    have hC' : C = {0} := by
      simp [C, complexAbsConvexHull, range_eq_empty]
    have hclosure : closure (weakBidualEval E '' C) = {weakBidualEval E 0} := by
      haveI : T2Space (WeakAlgebraicBidual E) :=
        (WeakBilin.isEmbedding (B := (LinearMap.id : Module.Dual ℂ (StrongDual ℂ E) →ₗ[ℂ]
          Module.Dual ℂ (StrongDual ℂ E))) Function.injective_id).t2Space
      rw [hC', image_singleton, closure_singleton]
    have hback : weakBidualEval E 0 ∈ complexUnitPettisIntegrals f := by
      refine ⟨0, by rw [VectorMeasure.variation_zero]; infer_instance, by simp, fun _ => by simp, ?_⟩
      refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_
      change ℓ 0 = VectorMeasure.integral 0 (ℓ ∘ f) (ContinuousLinearMap.mul ℝ ℂ)
      rw [map_zero, VectorMeasure.integral_zero_vectorMeasure]
    have he : complexUnitPettisIntegrals f = {weakBidualEval E 0} :=
      Subset.antisymm (hclosure ▸ hforward) (singleton_subset_iff.mpr hback)
    exact ⟨he.trans hclosure.symm, he.symm ▸ isCompact_singleton⟩

end ComplexHull

section Weil

variable {G E : Type*} [Group G] [MeasurableSpace G]
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E] [T2Space E]

/-- C.4.4.5. The scalar Weil identity for the normalized quotient measure
implies the Pettis identity. The represented integrals on individual cosets
descend pointwise by left invariance on the subgroup. -/
theorem pettis_weil (H : Subgroup G) [MeasurableMul₂ H] [MeasurableSpace (G ⧸ H)]
    (μG : Measure G) (μH : Measure H) (ν : Measure (G ⧸ H)) [μH.IsMulLeftInvariant]
    (hWeil : ∀ (w : G → ℂ), Integrable w μG → ∀ q : G ⧸ H → ℂ,
      (∀ x : G, q (x : G ⧸ H) = ∫ h : H, w (x * h) ∂μH) →
      Integrable q ν ∧ ∫ x, w x ∂μG = ∫ y, q y ∂ν)
    (f : G → E) (hf : ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ f) μG)
    (F : G → E) (hF : ∀ g : G, HasPositivePettisIntegral μH (fun h : H => f (g * h)) (F g)) :
    ∃! q : G ⧸ H → E, (∀ g : G, q (g : G ⧸ H) = F g) ∧
      ∃ hq : ∀ ℓ : StrongDual ℂ E, Integrable (ℓ ∘ q) ν,
        positiveWeakPettisIntegral μG f hf = positiveWeakPettisIntegral ν q hq := by
  have hconst (x y : G) (hxy : QuotientGroup.leftRel H x y) : F x = F y := by
    have hm : x⁻¹ * y ∈ H := QuotientGroup.leftRel_apply.mp hxy
    let a : H := ⟨x⁻¹ * y, hm⟩
    have ha : x * (a : G) = y := by simp [a]
    apply (weakBidualEval_isEmbedding E).injective (a₁ := (F x : WeakSpace ℂ E))
      (a₂ := (F y : WeakSpace ℂ E))
    change (weakBidualEval E (F x) : Module.Dual ℂ (StrongDual ℂ E)) =
      (weakBidualEval E (F y) : Module.Dual ℂ (StrongDual ℂ E))
    refine DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ fun ℓ => ?_
    change ℓ (F x) = ℓ (F y)
    rw [(hF x ℓ).2, (hF y ℓ).2, ← ha]
    simpa only [Subgroup.coe_mul, mul_assoc] using
      (integral_mul_left_eq_self (μ := μH) (fun h : H => ℓ (f (x * h))) a).symm
  let q : G ⧸ H → E := Quotient.lift F hconst
  have hq (ℓ : StrongDual ℂ E) := hWeil (ℓ ∘ f) (hf ℓ) (ℓ ∘ q) fun x => (hF x ℓ).2
  refine ⟨q, ⟨fun _ => rfl, fun ℓ => (hq ℓ).1, LinearMap.ext fun ℓ => (hq ℓ).2⟩, ?_⟩
  rintro q' ⟨hq', _⟩
  funext y
  refine QuotientGroup.induction_on y fun x => ?_
  exact hq' x

end Weil

/-- Corrected Lemma C.4.3.9. The positive measure in the seminorm bound is the
total variation. The extended-real bound allows the right side to be infinite. -/
theorem pettis_seminorm_le_variation {X E : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (μ : VectorMeasure X ℂ) {f : X → E} {u : E} (h : HasPettisIntegral μ f u)
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ENNReal.ofReal (p u) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ.variation := by
  obtain ⟨ℓ, h₀, hℓ⟩ := seminorm_support p hp u
  have hb := VectorMeasure.norm_integral_le_lintegral_norm
    (μ := μ) (B := ContinuousLinearMap.mul ℝ ℂ) (f := ℓ ∘ f)
  rw [← h₀, (h ℓ).2]
  apply (ENNReal.ofReal_le_ofReal (hb.trans ?_)).trans
    (ENNReal.ofReal_toReal_le.trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hℓ (f x))))
  exact mul_le_of_le_one_left ENNReal.toReal_nonneg complexMul_norm_le_one

theorem HasPettisIntegral.sub {X E : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {μ : VectorMeasure X ℂ} {f g : X → E} {u v : E}
    (hf : HasPettisIntegral μ f u) (hg : HasPettisIntegral μ g v) :
    HasPettisIntegral μ (f - g) (u - v) := by
  intro ℓ
  have he : ℓ ∘ (f - g) = (ℓ ∘ f) - (ℓ ∘ g) := by ext x; exact map_sub ℓ (f x) (g x)
  rw [he, map_sub, (hf ℓ).2, (hg ℓ).2]
  exact ⟨(hf ℓ).1.sub (hg ℓ).1, (VectorMeasure.integral_sub (hf ℓ).1 (hg ℓ).1).symm⟩

/-- Lemma C.4.3.12. Uniform convergence in each continuous seminorm implies
convergence of the Pettis integrals for a measure of finite total variation. -/
theorem pettis_tendsto_of_uniform {X E I : Type*} [MeasurableSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (μ : VectorMeasure X ℂ) [IsFiniteMeasure μ.variation] {l : Filter I}
    {f : I → X → E} {g : X → E} {u : I → E} {v : E}
    (hf : ∀ i, HasPettisIntegral μ (f i) (u i)) (hg : HasPettisIntegral μ g v)
    (hunif : ∀ (p : Seminorm ℂ E), Continuous p →
      ∀ ε > 0, ∀ᶠ i in l, ∀ x, p (f i x - g x) < ε) :
    Tendsto u l (𝓝 v) := by
  let M := (μ.variation univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  apply ((PolynormableSpace.withSeminorms ℂ E).tendsto_nhds u v).mpr
  intro p ε hε
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδM : δ * M < ε := calc
    _ < δ * (M + 1) := by gcongr; exact lt_add_one M
    _ = ε := div_mul_cancel₀ ε (by positivity)
  filter_upwards [hunif p.val p.property δ hδ] with i hi
  have h := pettis_seminorm_le_variation μ ((hf i).sub hg) p.val p.property
  have hc : (∫⁻ x, ENNReal.ofReal (p.val ((f i - g) x)) ∂μ.variation) ≤
      ENNReal.ofReal δ * μ.variation univ := by
    rw [← lintegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hi x).le
  have hfin : ENNReal.ofReal δ * μ.variation univ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hr := ENNReal.toReal_mono hfin (h.trans hc)
  rw [ENNReal.toReal_ofReal (apply_nonneg p.val _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hδ.le] at hr
  exact hr.trans_lt hδM

/-- The signed special case of the printed inequality already fails at a negative atom. -/
theorem pettis_negativeAtom_obstruction :
    let μ : VectorMeasure Unit ℂ := VectorMeasure.dirac () (-1)
    let I := complexMeasureIntegral μ (fun _ => 1)
    ‖I‖ = 1 ∧ I.re = -1 := by
  dsimp [complexMeasureIntegral]
  rw [VectorMeasure.integral_dirac']
  · norm_num
  · exact stronglyMeasurable_const

/-- In (C.4.3.3) the full support can have zero complex mass while the
integral is nonzero. This uses the Borel measure on a finite discrete space. -/
theorem pettis_zeroMass_obstruction :
    letI : MeasurableSpace Bool := ⊤
    let μ : VectorMeasure Bool ℂ := VectorMeasure.dirac false 1 + VectorMeasure.dirac true (-1)
    let f : Bool → ℂ := fun x => if x then 2 else 1
    μ univ = 0 ∧ complexMeasureIntegral μ f = -1 := by
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  let ν₀ : VectorMeasure Bool ℂ := VectorMeasure.dirac false 1
  let ν₁ : VectorMeasure Bool ℂ := VectorMeasure.dirac true (-1)
  let f : Bool → ℂ := fun x => if x then 2 else 1
  change (ν₀ + ν₁) univ = 0 ∧ complexMeasureIntegral (ν₀ + ν₁) f = -1
  constructor
  · simp [ν₀, ν₁]
  · have hi (x : Bool) (a : ℂ) : (VectorMeasure.dirac x a).Integrable f := by
      change Integrable f (VectorMeasure.dirac x a).variation
      rw [VectorMeasure.variation_dirac]
      exact (integrable_dirac (f := f) (a := x) enorm_lt_top).smul_measure (by simp)
    unfold complexMeasureIntegral
    rw [VectorMeasure.integral_add_vectorMeasure (hi false 1) (hi true (-1))]
    norm_num [f]

end Masullo
