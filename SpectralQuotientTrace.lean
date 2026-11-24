import BoundedBasisLifts
import TraceClassNorm
import WeightedTrace
import WeightedL2Coordinates
import Mathlib.MeasureTheory.Function.L2Space

open Filter InnerProductSpace MeasureTheory Topology
open scoped InnerProductSpace

namespace Masullo

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Transport a nuclear representation through the section and quotient. -/
private def liftQuotientSeries (j : K →L[ℂ] H) (q : H →L[ℂ] K)
    (T : RankOneSeries ℕ K) : RankOneSeries ℕ H where
  image n := j (T.image n)
  functional n := q.adjoint (T.functional n)
  summableNorm := ((T.summableNorm.mul_left ‖q.adjoint‖).mul_left ‖j‖).of_nonneg_of_le
    (fun _ => by positivity) fun n => by
      rw [← mul_assoc ‖q.adjoint‖]
      exact (mul_le_mul (j.le_opNorm _) (q.adjoint.le_opNorm _) (norm_nonneg _) (by positivity)).trans_eq
        (by ring)

private theorem liftQuotientSeries_operator (j : K →L[ℂ] H) (q : H →L[ℂ] K)
    (T : RankOneSeries ℕ K) :
    (liftQuotientSeries j q T).operator = j.comp (T.operator.comp q) := by
  ext x
  simp only [RankOneSeries.operator_apply, ContinuousLinearMap.comp_apply]
  have hs : Summable (fun i => ⟪T.functional i, q x⟫_ℂ • T.image i) := by
    simpa only [ContinuousLinearMap.apply_apply, rankOne_apply] using
      (T.operator_summable.hasSum.mapL (ContinuousLinearMap.apply ℂ K (q x))).summable
  rw [j.map_tsum hs]
  exact tsum_congr fun n => by
    simp [liftQuotientSeries, ContinuousLinearMap.adjoint_inner_left]

private theorem liftQuotientSeries_trace (j : K →L[ℂ] H) (q : H →L[ℂ] K)
    (hqj : ∀ x, q (j x) = x) (T : RankOneSeries ℕ K) :
    (liftQuotientSeries j q T).trace = T.trace := by
  unfold RankOneSeries.trace
  exact tsum_congr fun n => by
    simp [liftQuotientSeries, ContinuousLinearMap.adjoint_inner_left, hqj]

/-- Transport preserves the trace when the map back is a left inverse. -/
theorem traceClass_transport (j : K →L[ℂ] H) (q : H →L[ℂ] K)
    (hqj : ∀ x, q (j x) = x) (T : TraceClass K) :
    ∃ U : TraceClass H, U.toOperator = j.comp (T.toOperator.comp q) ∧
      U.traceValue = T.traceValue := by
  obtain ⟨R, hR⟩ := T.toOperator_mem
  let S := liftQuotientSeries j q R
  refine ⟨TraceClass.ofSeries S, ?_, ?_⟩
  · change S.operator = _
    rw [liftQuotientSeries_operator, hR]
  · rw [TraceClass.traceValue_ofSeries, liftQuotientSeries_trace j q hqj]
    exact (T.traceValue_eq_of_operator R hR).symm

/-- Equation (10.4.2.5) and Proposition 10.4.2.4. Nuclearity of the induced
quotient operator suffices for the nuclear trace identity. -/
theorem spectralProjection_trace_of_quotient (N : Submodule ℂ H) [IsClosed (N : Set H)]
    (A : H →L[ℂ] H) (Q : TraceClass (H ⧸ N))
    (hQ : N.mkQL.comp A = Q.toOperator.comp N.mkQL) :
    ∃ T : TraceClass H,
      T.toOperator = Nᗮ.starProjection.comp A ∧ T.traceValue = Q.traceValue := by
  obtain ⟨_, _, e, he, hproj, _⟩ := hilbert_quotient_projection N
  let j := (Nᗮ.subtypeₗᵢ.comp e.toLinearIsometry).toContinuousLinearMap
  obtain ⟨T, hT, htrace⟩ := traceClass_transport j N.mkQL he Q
  refine ⟨T, ?_, htrace⟩
  rw [hT, ← hQ]
  exact ContinuousLinearMap.ext fun x => hproj (A x)

/-- A uniformly bounded strong cutoff converges after left multiplication in
the nuclear norm, over an arbitrary filter. -/
theorem traceClass_leftCompose_tendsto {ι : Type*} {l : Filter ι}
    (T : TraceClass H) (M : ι → H →L[ℂ] H) {C : ℝ}
    (hM : ∀ i, ‖M i‖ ≤ C) (hstrong : ∀ x, Tendsto (fun i => M i x) l (𝓝 x)) :
    Tendsto (fun i => TraceClass.leftCompose (M i) T) l (𝓝 T) := by
  obtain ⟨R, hR⟩ := T.toOperator_mem
  let D (i : ι) : RankOneSeries ℕ H := R.leftComp (M i - ContinuousLinearMap.id ℂ H)
  have hD (i : ι) : TraceClass.leftCompose (M i) T - T = TraceClass.ofSeries (D i) := by
    apply TraceClass.toOperator_injective
    change (M i).comp T.toOperator - T.toOperator = (D i).operator
    rw [RankOneSeries.operator_leftComp, hR, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.id_comp]
  have hm : Tendsto (fun i => (D i).mass) l (𝓝 0) := by
    have hz : (∑' _ : ℕ, (0 : ℝ)) = 0 := tsum_zero
    rw [← hz]
    refine tendsto_tsum_of_dominated_convergence (R.summableNorm.mul_left (C + 1)) ?_ ?_
    · intro n
      simpa [D, RankOneSeries.leftComp] using
        (((hstrong (R.image n)).sub_const (R.image n)).norm.mul_const ‖R.functional n‖)
    · exact Eventually.of_forall fun i n => by
        change ‖‖M i (R.image n) - R.image n‖ * ‖R.functional n‖‖ ≤
          (C + 1) * (‖R.image n‖ * ‖R.functional n‖)
        rw [Real.norm_of_nonneg (by positivity)]
        have h := ((M i).le_opNorm (R.image n)).trans
          (mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _))
        calc
          _ ≤ (C * ‖R.image n‖ + ‖R.image n‖) * ‖R.functional n‖ :=
            mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add_left h _))
              (norm_nonneg _)
          _ = _ := by ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hm
  intro i
  rw [hD]
  exact TraceClass.norm_ofSeries_le _

/-- Amplitude coordinates preserve the actual multiplication cutoff. -/
theorem amplitudeL2Iso_cutoffOperator {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (hw : Measurable w) (hp : ∀ x, 0 < w x)
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∀ x, ρ x ≤ 1)
    (f : Lp ℂ 2 (amplitudeMeasure μ w)) :
    amplitudeL2Iso μ w hw hp (cutoffOperator ρ hρ hρ₀ hρ₁ f) =
      cutoffOperator ρ hρ hρ₀ hρ₁ (amplitudeL2Iso μ w hw hp f) := by
  apply Lp.ext
  filter_upwards [amplitudeL2Iso_ae μ w hw hp (cutoffOperator ρ hρ hρ₀ hρ₁ f),
    (absolutelyContinuous_amplitudeMeasure μ w hw hp).ae_le (cutoffOperator_ae ρ hρ hρ₀ hρ₁ f),
    cutoffOperator_ae ρ hρ hρ₀ hρ₁ (amplitudeL2Iso μ w hw hp f),
    amplitudeL2Iso_ae μ w hw hp f] with x hleft hf hright ha
  rw [hleft, hf, hright, ha, Complex.real_smul, Complex.real_smul, mul_left_comm]

/-- Theorem 10.4.2.2. On weighted L², the actual cutoff converges in trace
norm after spectral projection of convolution, provided quotient convolution
is nuclear. The scalar limit is the quotient trace. -/
theorem spectralProjection_cutoff_trace_tendsto
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) {l : Filter ι}
    [l.IsCountablyGenerated] (N : Submodule ℂ (Lp ℂ 2 μ)) [IsClosed (N : Set (Lp ℂ 2 μ))]
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Q : TraceClass (Lp ℂ 2 μ ⧸ N))
    (hQ : N.mkQL.comp A = Q.toOperator.comp N.mkQL)
    (ρ : ι → X → ℝ) (hρ : ∀ i, Measurable (ρ i)) (hρ₀ : ∀ i x, 0 ≤ ρ i x)
    (hρ₁ : ∀ i x, ρ i x ≤ 1) (hevent : ∀ x, ∀ᶠ i in l, ρ i x = 1) :
    ∃ T : TraceClass (Lp ℂ 2 μ), ∃ S : ι → TraceClass (Lp ℂ 2 μ),
      T.toOperator = Nᗮ.starProjection.comp A ∧
      (∀ i, (S i).toOperator =
        (cutoffOperator (ρ i) (hρ i) (hρ₀ i) (hρ₁ i)).comp (Nᗮ.starProjection.comp A)) ∧
      Tendsto S l (𝓝 T) ∧
      Tendsto (fun i => (S i).traceValue) l (𝓝 Q.traceValue) := by
  obtain ⟨T, hT, htrace⟩ := spectralProjection_trace_of_quotient N A Q hQ
  let M i := cutoffOperator (μ := μ) (ρ i) (hρ i) (hρ₀ i) (hρ₁ i)
  have h := traceClass_leftCompose_tendsto T M (C := 1)
    (fun i => norm_cutoffOperator_le (ρ i) (hρ i) (hρ₀ i) (hρ₁ i))
    (cutoffOperator_tendsto ρ hρ hρ₀ hρ₁ hevent)
  refine ⟨T, fun i => TraceClass.leftCompose (M i) T, hT, fun i => ?_, h, ?_⟩
  · rw [TraceClass.leftCompose_toOperator, hT]
  · rw [← htrace]
    exact (TraceClass.traceCLM.continuous.tendsto T).comp h

/-- The limit calculation for convolution after projection in Theorem 10.4.2.8.
The remaining analytic input is trace class of the untruncated operator in
that order. The cyclic trace identity then removes the off-diagonal block. -/
theorem cutoff_convolutionAfterProjection_trace_tendsto
    {ι : Type*} {l : Filter ι}
    (N : Submodule ℂ H) [IsClosed (N : Set H)] (A : H →L[ℂ] H)
    (Q : TraceClass (H ⧸ N)) (hQ : N.mkQL.comp A = Q.toOperator.comp N.mkQL)
    (V : TraceClass H) (hV : V.toOperator = A.comp Nᗮ.starProjection)
    (M : ι → H →L[ℂ] H) {C : ℝ} (hM : ∀ i, ‖M i‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun i => M i x) l (𝓝 x)) :
    Tendsto (fun i => (TraceClass.leftCompose (M i) V).traceValue) l (𝓝 Q.traceValue) := by
  let P := Nᗮ.starProjection
  obtain ⟨hqP, _, e, _, he, _⟩ := hilbert_quotient_projection N
  have hq (x : H) : N.mkQL x = N.mkQL (P x) := DFunLike.congr_fun hqP x
  have hqA (x : H) : N.mkQL (A x) = Q.toOperator (N.mkQL x) := DFunLike.congr_fun hQ x
  have hPP (x : H) : P (P x) = P x :=
    Submodule.starProjection_eq_self_iff.mpr (Nᗮ.starProjection_apply_mem x)
  have hPAP (x : H) : P (A (P x)) = P (A x) := by
    rw [← he (A (P x)), ← he (A x), hqA, hqA, ← hq]
  obtain ⟨T, hT, hTtrace⟩ := spectralProjection_trace_of_quotient N A Q hQ
  obtain ⟨R, hR⟩ := V.toOperator_mem
  have hl : (R.leftComp P).operator = T.toOperator := by
    rw [RankOneSeries.operator_leftComp, hR, hV, hT]
    exact ContinuousLinearMap.ext hPAP
  have hr : (R.rightComp P).operator = V.toOperator := by
    rw [RankOneSeries.operator_rightComp, hR]
    apply ContinuousLinearMap.ext
    intro x
    change V.toOperator (P x) = V.toOperator x
    rw [hV]
    exact congrArg A (hPP x)
  have ht : V.traceValue = Q.traceValue := calc
    _ = (R.rightComp P).trace := V.traceValue_eq_of_operator _ hr
    _ = (R.leftComp P).trace := (R.trace_comp_cyclic P).symm
    _ = T.traceValue := (T.traceValue_eq_of_operator _ hl).symm
    _ = _ := hTtrace
  rw [← ht]
  exact (TraceClass.traceCLM.continuous.tendsto V).comp
    (traceClass_leftCompose_tendsto V M hM hstrong)

/-- Theorem 10.4.2.1. Once the quotient action is nuclear, the weighted
cutoff trace splits into the geometric and spectral traces. -/
theorem spectralProjection_cutoff_trace_split (N : Submodule ℂ H) [IsClosed (N : Set H)]
    (A M : H →L[ℂ] H) (Q : TraceClass (H ⧸ N))
    (hQ : N.mkQL.comp A = Q.toOperator.comp N.mkQL)
    (U : TraceClass H) (hU : U.toOperator = M.comp A) :
    ∃ T G S : TraceClass H, T.toOperator = Nᗮ.starProjection.comp A ∧
      G.toOperator = M.comp (N.starProjection.comp A) ∧
      S.toOperator = M.comp (Nᗮ.starProjection.comp A) ∧
      U.traceValue = G.traceValue + S.traceValue := by
  obtain ⟨T, hT, _⟩ := spectralProjection_trace_of_quotient N A Q hQ
  let S := TraceClass.leftCompose M T
  have hS : S.toOperator = M.comp (Nᗮ.starProjection.comp A) := by
    rw [TraceClass.leftCompose_toOperator, hT]
  refine ⟨T, U - S, S, hT, ?_, hS, ?_⟩
  · change U.toOperator - S.toOperator = _
    rw [hU, hS]
    exact ContinuousLinearMap.ext fun x => by
      have h := congrArg M (N.starProjection_add_starProjection_orthogonal (A x))
      simp only [map_add] at h
      change M (A x) - M (Nᗮ.starProjection (A x)) = M (N.starProjection (A x))
      exact sub_eq_iff_eq_add.mpr h.symm
  · change TraceClass.traceCLM U = TraceClass.traceCLM (U - S) + TraceClass.traceCLM S
    rw [map_sub, sub_add_cancel]

end

end Masullo
