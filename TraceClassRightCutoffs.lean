import TraceClassNorm

open Filter InnerProductSpace Topology

namespace Masullo

noncomputable section

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Right composition by a bounded operator preserves the trace class. -/
def rightCompose (T : TraceClass H) (A : H →L[ℂ] H) : TraceClass H :=
  ⟨T.toOperator.comp A, nuclearOperators_comp_right A T.toOperator_mem⟩

@[simp] theorem rightCompose_toOperator (T : TraceClass H) (A : H →L[ℂ] H) :
    (T.rightCompose A).toOperator = T.toOperator.comp A := rfl

/-- Uniformly bounded right cutoffs converge in trace norm if their adjoints
converge strongly. The limit can be an orthogonal projection. -/
theorem rightCompose_tendsto {ι : Type*} {l : Filter ι}
    (T : TraceClass H) (A : ι → H →L[ℂ] H) (P : H →L[ℂ] H) {C : ℝ}
    (hA : ∀ i, ‖A i‖ ≤ C) (hstrong : ∀ x, Tendsto (fun i => (A i).adjoint x) l (𝓝 (P.adjoint x))) :
    Tendsto (fun i => T.rightCompose (A i)) l (𝓝 (T.rightCompose P)) := by
  obtain ⟨R, hR⟩ := T.toOperator_mem
  let D (i : ι) := R.rightComp (A i - P)
  have hD (i : ι) : T.rightCompose (A i) - T.rightCompose P = ofSeries (D i) := by
    apply toOperator_injective
    change T.toOperator.comp (A i) - T.toOperator.comp P = (D i).operator
    rw [RankOneSeries.operator_rightComp, hR, ContinuousLinearMap.comp_sub]
  have hm : Tendsto (fun i => (D i).mass) l (𝓝 0) := by
    have hz : (∑' _ : ℕ, (0 : ℝ)) = 0 := tsum_zero
    rw [← hz]
    refine tendsto_tsum_of_dominated_convergence (R.summableNorm.mul_left (C + ‖P‖)) ?_ ?_
    · intro n
      simpa [D, RankOneSeries.rightComp] using
        (((hstrong (R.functional n)).sub_const (P.adjoint (R.functional n))).norm.const_mul
          ‖R.image n‖)
    · exact Eventually.of_forall fun i n => by
        let hf := R.functional n
        have hnorm : ‖(A i - P).adjoint hf‖ ≤ (C + ‖P‖) * ‖hf‖ :=
          ((A i - P).adjoint.le_opNorm hf).trans (by
            rw [ContinuousLinearMap.adjoint.norm_map]
            exact mul_le_mul_of_nonneg_right ((norm_sub_le (A i) P).trans
              (add_le_add_left (hA i) _)) (norm_nonneg _))
        change ‖‖R.image n‖ * ‖(A i - P).adjoint hf‖‖ ≤ _
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          _ ≤ ‖R.image n‖ * ((C + ‖P‖) * ‖hf‖) :=
            mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
          _ = _ := by dsimp only [hf]; ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hm
  intro i
  rw [hD]
  exact norm_ofSeries_le _


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private def compressSeries (j : E →ₗᵢ[ℂ] H) (R : RankOneSeries ℕ H) : RankOneSeries ℕ E where
  image n := j.toContinuousLinearMap.adjoint (R.image n)
  functional n := j.toContinuousLinearMap.adjoint (R.functional n)
  summableNorm := R.summableNorm.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ by
    have h (x : H) : ‖j.toContinuousLinearMap.adjoint x‖ ≤ ‖x‖ := by
      refine (j.toContinuousLinearMap.adjoint.le_opNorm x).trans ?_
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_of_le_one_left (norm_nonneg _) j.norm_toContinuousLinearMap_le
    exact mul_le_mul (h _) (h _) (norm_nonneg _) (norm_nonneg _)

private theorem compressSeries_mass_le (j : E →ₗᵢ[ℂ] H) (R : RankOneSeries ℕ H) :
    (compressSeries j R).mass ≤ R.mass := by
  apply Summable.tsum_le_tsum _ (compressSeries j R).summableNorm R.summableNorm
  intro n
  have h (x : H) : ‖j.toContinuousLinearMap.adjoint x‖ ≤ ‖x‖ := by
    refine (j.toContinuousLinearMap.adjoint.le_opNorm x).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_of_le_one_left (norm_nonneg _) j.norm_toContinuousLinearMap_le
  exact mul_le_mul (h _) (h _) (norm_nonneg _) (norm_nonneg _)

private theorem compressSeries_operator (j : E →ₗᵢ[ℂ] H) (R : RankOneSeries ℕ H) :
    (compressSeries j R).operator =
      j.toContinuousLinearMap.adjoint.comp (R.operator.comp j.toContinuousLinearMap) := by
  ext x
  simp only [RankOneSeries.operator_apply, ContinuousLinearMap.comp_apply]
  let q := j.toContinuousLinearMap.adjoint
  have hs : Summable (fun i ↦ inner ℂ (R.functional i) (j x) • R.image i) := by
    simpa only [ContinuousLinearMap.apply_apply, rankOne_apply] using
      (R.operator_summable.hasSum.mapL (ContinuousLinearMap.apply ℂ H (j x))).summable
  change _ = q (∑' n, inner ℂ (R.functional n) (j x) • R.image n)
  rw [q.map_tsum hs]
  exact tsum_congr fun n ↦ by
    simp [compressSeries, q, ContinuousLinearMap.adjoint_inner_left]

/-- Compression along a Hilbert isometry is a trace-norm contraction. -/
def compress (j : E →ₗᵢ[ℂ] H) : TraceClass H →L[ℂ] TraceClass E := by
  let p := j.toContinuousLinearMap.adjoint
  let c (T : TraceClass H) : TraceClass E :=
    ⟨p.comp (T.toOperator.comp j.toContinuousLinearMap), by
      obtain ⟨R, hR⟩ := T.toOperator_mem
      exact ⟨compressSeries j R, (compressSeries_operator j R).trans (by rw [hR])⟩⟩
  let L : TraceClass H →ₗ[ℂ] TraceClass E := {
    toFun := c
    map_add' := fun T V ↦ toOperator_injective (by
      change p.comp ((T.toOperator + V.toOperator).comp j.toContinuousLinearMap) = _
      rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      rfl)
    map_smul' := fun a T ↦ toOperator_injective (by
      change p.comp ((a • T.toOperator).comp j.toContinuousLinearMap) = _
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rfl) }
  refine L.mkContinuous 1 fun T ↦ ?_
  rw [one_mul]
  change ‖c T‖ ≤ nuclearTraceNorm T.toOperator
  unfold nuclearTraceNorm
  apply le_csInf
  · obtain ⟨R, hR⟩ := T.toOperator_mem
    exact ⟨R.mass, R, hR, rfl⟩
  · rintro _ ⟨R, hR, rfl⟩
    have he : c T = ofSeries (compressSeries j R) := by
      apply toOperator_injective
      change p.comp (T.toOperator.comp j.toContinuousLinearMap) = (compressSeries j R).operator
      rw [compressSeries_operator, hR]
    rw [he]
    exact (norm_ofSeries_le _).trans (compressSeries_mass_le j R)

@[simp] theorem compress_toOperator (j : E →ₗᵢ[ℂ] H) (T : TraceClass H) :
    (compress j T).toOperator =
      j.toContinuousLinearMap.adjoint.comp (T.toOperator.comp j.toContinuousLinearMap) := rfl

/-- A trace-class operator with a right factor through the isotype has the
same trace as its compression to that isotype. -/
theorem compress_traceValue (j : E →ₗᵢ[ℂ] H) (T : TraceClass H)
    (hT : T.toOperator.comp
      (j.toContinuousLinearMap.comp j.toContinuousLinearMap.adjoint) = T.toOperator) :
    (compress j T).traceValue = T.traceValue := by
  obtain ⟨R, hR⟩ := T.toOperator_mem
  let q := j.toContinuousLinearMap
  let B := q.comp q.adjoint
  have hc := (compress j T).traceValue_eq_of_operator (compressSeries j R)
    ((compressSeries_operator j R).trans (by rw [hR, compress_toOperator]))
  have hr := T.traceValue_eq_of_operator (R.rightComp B) (by
    rw [RankOneSeries.operator_rightComp, hR]
    exact hT)
  rw [hc, hr]
  unfold RankOneSeries.trace
  apply tsum_congr
  intro n
  change inner ℂ (q.adjoint (R.functional n)) (q.adjoint (R.image n)) =
    inner ℂ (B.adjoint (R.functional n)) (R.image n)
  rw [← ContinuousLinearMap.adjoint_inner_left]
  simp only [B, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]

end TraceClass
end
end Masullo
