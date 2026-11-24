import L2Multipliers
import NuclearKernelDiagonal
import TraceClassNorm

open Filter MeasureTheory
open scoped ENNReal

namespace Masullo

noncomputable section

section Measure

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
variable {ρ : X → ℂ} {B : ℝ}

/-- Multiplication of a square-integrable kernel in the target variable
is left composition by the actual L² multiplier. -/
theorem kernelIntegralOperator_mul_left
    (hρ : AEStronglyMeasurable ρ μ) (hB : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ B)
    {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ)) :
    let m (z : X × X) := ρ z.1 * k z
    ∃ hm : MemLp m 2 (μ.prod μ),
      kernelIntegralOperator (hm.toLp m) =
        (lpTwoComplexMultiplier hρ hB).comp (kernelIntegralOperator (hk.toLp k)) := by
  let m (z : X × X) := ρ z.1 * k z
  have hm : MemLp m 2 (μ.prod μ) :=
    memLp_bounded_complex_mul hρ.comp_fst (Measure.quasiMeasurePreserving_fst.ae hB) hk
  refine ⟨hm, ?_⟩
  ext f : 1
  apply Lp.ext
  filter_upwards [kernelIntegralOperator_apply_of_memLp hm f,
    kernelIntegralOperator_apply_of_memLp hk f,
    lpTwoComplexMultiplier_ae hρ hB (kernelIntegralOperator (hk.toLp k) f)] with x hx hkx hmx
  change kernelIntegralOperator (hm.toLp m) f x =
    lpTwoComplexMultiplier hρ hB (kernelIntegralOperator (hk.toLp k) f) x
  rw [hx.2, hmx, hkx.2, ← integral_const_mul]
  simp only [m, mul_assoc]

omit [SFinite μ] in
/-- Left multiplication multiplies the nuclear diagonal series by the same coefficient. -/
theorem RankOneSeries.diagonal_series_left_multiplier_ae
    (T : RankOneSeries ℕ (X →₂[μ] ℂ))
    (hρ : AEStronglyMeasurable ρ μ) (hB : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ B) :
    let S := T.leftComp (lpTwoComplexMultiplier hρ hB)
    (fun x => ∑' i, S.image i x * star (S.functional i x)) =ᵐ[μ]
      fun x => ρ x * (∑' i, T.image i x * star (T.functional i x)) := by
  let S := T.leftComp (lpTwoComplexMultiplier hρ hB)
  filter_upwards [ae_all_iff.mpr (fun i => lpTwoComplexMultiplier_ae hρ hB (T.image i))]
    with x hx
  change (∑' i, S.image i x * star (S.functional i x)) = _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  change lpTwoComplexMultiplier hρ hB (T.image i) x * star (T.functional i x) = _
  rw [hx i, mul_assoc]

omit [SFinite μ] in
/-- The bounded functional on trace class associated to an L∞ multiplier. -/
def traceClassMultiplierTest (hρ : MemLp ρ ⊤ μ) : TraceClass (X →₂[μ] ℂ) →L[ℂ] ℂ :=
  let M := lpTwoComplexMultiplier hρ.aestronglyMeasurable (ae_norm_le_essentialNorm hρ)
  TraceClass.traceCLM.comp
    ((TraceClass.leftCompose M).mkContinuous ‖M‖ (TraceClass.norm_leftCompose_le M))

omit [SFinite μ] in
theorem traceClassMultiplierTest_ofSeries (hρ : MemLp ρ ⊤ μ)
    (T : RankOneSeries ℕ (X →₂[μ] ℂ)) :
    let M := lpTwoComplexMultiplier hρ.aestronglyMeasurable (ae_norm_le_essentialNorm hρ)
    traceClassMultiplierTest hρ (TraceClass.ofSeries T) = (T.leftComp M).trace := by
  let M := lpTwoComplexMultiplier hρ.aestronglyMeasurable (ae_norm_le_essentialNorm hρ)
  change TraceClass.traceCLM (TraceClass.leftCompose M (TraceClass.ofSeries T)) = _
  rw [TraceClass.traceCLM_apply]
  apply TraceClass.traceValue_eq_of_operator
  exact T.operator_leftComp M

end Measure

end

end Masullo
