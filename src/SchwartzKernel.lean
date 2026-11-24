import NuclearIntegralOperators
import NuclearFactorization

/-! # The Schwartz kernel theorem for continuous bilinear forms -/

open Bornology Filter Function Set Topology

namespace Masullo

noncomputable section

universe u v

private theorem equicontinuous_of_seminorm_bound {X ι : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (p : Seminorm ℂ X) (hp : Continuous p) (f : ι → X →L[ℂ] ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ p x) : Equicontinuous (fun i x => f i x) := by
  intro x
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  have h : Tendsto (fun y => p (y - x)) (𝓝 x) (𝓝 0) := by
    apply (hp.comp (continuous_id.sub continuous_const)).tendsto'
    simp
  filter_upwards [h.eventually (Iio_mem_nhds hε)] with y hy i
  rw [dist_comm, dist_eq_norm, ← map_sub]
  exact (hf i (y - x)).trans_lt hy

/-- Theorem C.2.4.18. A jointly continuous scalar bilinear form has a nuclear
series if its first variable ranges over a nuclear space. The finite sums
converge uniformly on every von Neumann bounded subset of the product. -/
theorem schwartzKernel_bilinear {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F] [T2Space F]
    (hE : NuclearLocallyConvex.{u, u} E)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : Continuous (fun z : E × F => B z.1 z.2)) :
    ∃ (c : ℕ → ℂ) (f : ℕ → E →L[ℂ] ℂ) (g : ℕ → F →L[ℂ] ℂ),
      Summable (fun n => ‖c n‖) ∧ Equicontinuous (fun n x => f n x) ∧
      Equicontinuous (fun n y => g n y) ∧
      (∀ x y, HasSum (fun n => c n * f n x * g n y) (B x y)) ∧
      ∀ S : Set (E × F), IsVonNBounded ℂ S →
        TendstoUniformlyOn (fun t : Finset ℕ => fun z : E × F =>
          ∑ n ∈ t, c n * f n z.1 * g n z.2) (fun z => B z.1 z.2) atTop S := by
  letI : PolynormableSpace ℂ E := hE.2.1
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
  obtain ⟨q, s, hq, hs, hbound⟩ :=
    continuous_bilinear_bound B hB (normSeminorm ℂ ℂ) continuous_norm
  obtain ⟨p, hp, hqp, _, f, w, hf, hsum⟩ :=
    nuclearLocallyConvex_exists_rankOneTransition.{u, u} hE q hq
  obtain ⟨R⟩ := BanachNuclearExpansion.nonempty_of_rankOne_hasSum f w hf hsum
  let T := localBanachTransition q p hqp
  let j := localBanachMap p hp
  obtain ⟨d, hd, hdn⟩ := extendBilinearSecond s q B.flip fun y x => by
    change ‖B x y‖ ≤ s y * q x
    rw [mul_comm]
    exact hbound x y
  let D : F →L[ℂ] StrongDual ℂ (LocalBanach q) := ⟨d, by
    apply continuous_of_tendsto_nhds_zero d.toAddMonoidHom
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(hs.tendsto' 0 0 (map_zero s)).eventually (Iio_mem_nhds hε)] with y hy
    rw [dist_zero_right]
    exact (hdn y).trans_lt hy⟩
  let a (n : ℕ) := (R.functional n).comp j
  let b (n : ℕ) := (ContinuousLinearMap.apply ℂ ℂ (R.vector n)).comp D
  have hab (n : ℕ) (x : E) : ‖a n x‖ ≤ p x := by
    change ‖R.functional n (j x)‖ ≤ p x
    exact ((R.functional n).le_of_opNorm_le (R.functional_bound n) (j x)).trans_eq
      (by rw [one_mul]; exact norm_localBanachDenseMap p x)
  have hbb (n : ℕ) (y : F) : ‖b n y‖ ≤ s y := by
    change ‖d y (R.vector n)‖ ≤ s y
    exact ((d y).le_opNorm _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (R.vector_bound n)).trans (hdn y))
  have hval (x : E) (y : F) : D y (T (j x)) = B x y := by
    change d y (T (localBanachDenseMap p x)) = B x y
    rw [localBanachTransition_denseMap]
    exact hd y x
  refine ⟨R.coeff, a, b, R.coeff_summable, equicontinuous_of_seminorm_bound p hp a hab,
    equicontinuous_of_seminorm_bound s hs b hbb, ?_, ?_⟩
  · intro x y
    have h := (D y).hasSum (R.hasSum_apply (j x))
    change HasSum _ (D y (T (j x))) at h
    simpa only [hval, map_smul, smul_eq_mul, a, b, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using h
  · intro S hS
    let j₁ := j.comp (ContinuousLinearMap.fst ℂ E F)
    let j₂ := D.comp (ContinuousLinearMap.snd ℂ E F)
    obtain ⟨M, hM⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hS.image j₁)
    obtain ⟨N, hN⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (hS.image j₂)
    let A := 1 + |M|
    let C := 1 + |N|
    have hA : 0 < A := by dsimp [A]; positivity
    have hC : 0 < C := by dsimp [C]; positivity
    have hAb {z : E × F} (hz : z ∈ S) : ‖j z.1‖ ≤ A :=
      (hM _ (mem_image_of_mem j₁ hz)).trans
        ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))
    have hCb {z : E × F} (hz : z ∈ S) : ‖D z.2‖ ≤ C :=
      (hN _ (mem_image_of_mem j₂ hz)).trans
        ((le_abs_self N).trans (le_add_of_nonneg_left zero_le_one))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let L (t : Finset ℕ) := ∑ n ∈ t, R.coeff n • (R.functional n).smulRight (R.vector n)
    have hL : Tendsto L atTop (𝓝 T) := R.hasSum
    filter_upwards [Metric.tendsto_nhds.mp hL (ε / (C * A))
      (div_pos hε (mul_pos hC hA))] with t ht z hz
    have hseries : ∑ n ∈ t, R.coeff n * a n z.1 * b n z.2 = D z.2 (L t (j z.1)) := by
      simp only [L, sum_apply, map_sum, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul, a, b,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, mul_assoc]
    rw [hseries, ← hval z.1 z.2, dist_comm, dist_eq_norm, ← map_sub]
    change ‖D z.2 ((L t - T) (j z.1))‖ < ε
    rw [dist_eq_norm] at ht
    calc
      _ ≤ ‖D z.2‖ * ‖(L t - T) (j z.1)‖ := (D z.2).le_opNorm _
      _ ≤ C * (‖L t - T‖ * A) :=
        mul_le_mul (hCb hz)
          (((L t - T).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hAb hz) (norm_nonneg _)))
          (norm_nonneg _) hC.le
      _ = ‖L t - T‖ * (C * A) := by ring
      _ < ε := (lt_div_iff₀ (mul_pos hC hA)).mp ht

end

end Masullo
