import NuclearFrechetStrongDual
import PettisBounds

/-!
# Nuclearity detected by the strong dual

The neighborhood argument adapts the Apache-2.0 original proof of
Lemma C.2.4.11 from `RiemannMasullo/AppC_LCTVS/Sec2b.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`. The bounded-set estimate
uses the already verified rank-one series for a local Banach transition.
-/

open Bornology Filter Function Set Topology

namespace Masullo

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

private theorem norm_sum_with_phases {n : ℕ} (z : Fin n → ℂ) :
    ∃ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧ ‖∑ i, a i * z i‖ = ∑ i, ‖z i‖ := by
  let a (i : Fin n) : ℂ := (‖z i‖ : ℂ) / z i
  have ha (i : Fin n) : ‖a i‖ ≤ 1 := by
    dsimp [a]
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have he (i : Fin n) : a i * z i = (‖z i‖ : ℂ) := by
    by_cases hi : z i = 0
    · simp [a, hi]
    · exact div_mul_cancel₀ _ hi
  refine ⟨a, ha, ?_⟩
  simp only [he, ← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]

set_option maxHeartbeats 1200000 in
private theorem sum_bound_on_bounded [PolynormableSpace ℂ E]
    (hN : NuclearLocallyConvex.{u, u} (StrongDual ℂ E))
    (q : Seminorm ℂ E) (hq : Continuous q) (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
      (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → ∑ i, a i • x i ∈ B) →
        ∑ i, q (x i) ≤ C := by
  classical
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let D := StrongDual ℂ E
  letI : PolynormableSpace ℂ D := hN.2.1
  letI : IsTopologicalAddGroup D := (PolynormableSpace.withSeminorms ℂ D).topologicalAddGroup
  let b : {s : Set E // IsVonNBounded ℂ s} := ⟨B, hB⟩
  let p := strongDualBoundedSeminorm b
  have hp : Continuous p := strongDual_withBoundedSeminorms.continuous_seminorm b
  obtain ⟨r, hr, hpr, ι, f, w, hsum, hT⟩ :=
    nuclearLocallyConvex_exists_rankOneTransition.{u, u} hN p hp
  let j := localBanachMap r hr
  let j₀ := localBanachDenseMap p
  let T := localBanachTransition p r hpr
  let A := {g : D | ∀ y, ‖g y‖ ≤ q y}
  obtain ⟨M, hM, hb⟩ :=
    (PolynormableSpace.withSeminorms ℂ D).isVonNBounded_iff_seminorm_bounded.mp
      (strongDual_seminorm_test_bounded q hq) ⟨r, hr⟩
  refine ⟨M * ∑' k, ‖f k‖ * ‖w k‖, mul_nonneg hM.le
    (tsum_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)), fun n x hx ↦ ?_⟩
  have hxB (i : Fin n) : x i ∈ B := by
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using hx (Pi.single i 1) (fun k ↦ by
      by_cases hk : k = i <;> simp [hk])
  let l (i : Fin n) : D →ₗ[ℂ] ℂ :=
    { toFun := fun g ↦ g (x i)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hl (i : Fin n) (g : D) : ‖l i g‖ ≤ 1 * ‖j₀ g‖ := by
    rw [one_mul, norm_localBanachDenseMap]
    exact strongDualBoundedSeminorm_dom b g (hxB i)
  let e (i : Fin n) : StrongDual ℂ (LocalBanach p) := (l i).extendOfNorm j₀
  have he (i : Fin n) (g : D) : e i (j₀ g) = g (x i) :=
    LinearMap.extendOfNorm_eq (localBanachDenseMap_dense p) ⟨1, hl i⟩ g
  have hvec (y : LocalBanach p) : ∑ i, ‖e i y‖ ≤ ‖y‖ := by
    obtain ⟨a, ha, heq⟩ := norm_sum_with_phases (fun i ↦ e i y)
    rw [← heq]
    refine (localBanachDenseMap_dense p).induction_on y (isClosed_le (by fun_prop) continuous_norm)
      fun g ↦ ?_
    change ‖∑ i, a i * e i (j₀ g)‖ ≤ ‖localBanachDenseMap p g‖
    simp only [he, norm_localBanachDenseMap]
    rw [← show g (∑ i, a i • x i) = ∑ i, a i * g (x i) by
      simp only [map_sum, map_smul, smul_eq_mul]]
    exact strongDualBoundedSeminorm_dom b g (hx a ha)
  let iq := localBanachMap q hq
  choose g hg hgx using fun i : Fin n ↦ exists_dual_vector'' ℂ (iq (x i))
  let d (i : Fin n) : D := (g i).comp iq
  have hd (i : Fin n) : d i ∈ A := fun y ↦ by
    change ‖g i (iq y)‖ ≤ q y
    rw [← norm_localBanachDenseMap q y]
    exact ((g i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg (iq y)) (hg i))
  have hd' (i : Fin n) : ‖j (d i)‖ ≤ M := by
    change ‖localBanachDenseMap r (d i)‖ ≤ M
    rw [norm_localBanachDenseMap]
    exact (hb (d i) (hd i)).le
  let F := LocalBanach r →L[ℂ] LocalBanach p
  let L : F →L[ℂ] ℂ :=
    ∑ i, (e i).comp (ContinuousLinearMap.apply ℂ (LocalBanach p) (j (d i)))
  have hLd (S : F) : L S = ∑ i, e i (S (j (d i))) := by
    simp only [L, sum_apply, ContinuousLinearMap.comp_apply]
    exact Finset.sum_congr rfl (fun i _ ↦ rfl)
  have hLT : L T = ((∑ i, q (x i) : ℝ) : ℂ) := by
    rw [hLd, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change e i (T (localBanachDenseMap r (d i))) = _
    rw [localBanachTransition_denseMap, he]
    change g i (iq (x i)) = _
    rw [hgx]
    change (algebraMap ℝ ℂ) ‖localBanachDenseMap q (x i)‖ = _
    rw [norm_localBanachDenseMap]
    rfl
  have hnorm : ‖L T‖ = ∑ i, q (x i) := by
    rw [hLT, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ apply_nonneg q (x i))]
  rw [← hnorm, ← tsum_mul_left]
  refine (L.hasSum hT).norm_le_of_bounded (hsum.mul_left M).hasSum fun k ↦ ?_
  rw [hLd]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i, (M * ‖f k‖) * ‖e i (w k)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [ContinuousLinearMap.smulRight_apply, map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right
        (((f k).le_opNorm _).trans (by rw [mul_comm M]; gcongr; exact hd' i)) (norm_nonneg _)
    _ ≤ M * (‖f k‖ * ‖w k‖) := by
      rw [← Finset.mul_sum, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hvec (w k)) (mul_nonneg hM.le (norm_nonneg _))

/-- For a metrizable polynormable space, a bound for sums of seminorm values on
every bounded set of unit-disk combinations gives a bound on a zero-neighborhood. -/
private theorem sum_bound_on_nhds_of_bounded [PolynormableSpace ℂ E] [TopologicalSpace.MetrizableSpace E]
    (q : Seminorm ℂ E) (h : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
        (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ B) →
          ∑ i, q (x i) ≤ C) :
    ∃ U ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
      (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ U) →
        ∑ i, q (x i) ≤ C := by
  classical
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  by_contra! hfail
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  choose n x hx hlower using fun k : ℕ ↦ hfail (U k) (hU.mem k) (k : ℝ) (Nat.cast_nonneg k)
  -- The tail is small in any fixed seminorm. Only finitely many families precede it.
  let B : Set E := {y | ∃ k : ℕ, ∃ a : Fin (n k) → ℂ,
    (∀ i, ‖a i‖ ≤ 1) ∧ (∑ i, a i • x k i) = y}
  have hB : IsVonNBounded ℂ B := by
    apply (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨p, hp⟩
    obtain ⟨j, _, hj⟩ := hU.1.mem_iff.mp (p.ball_mem_nhds hp one_pos)
    let M := ∑ k ∈ Finset.range j, ∑ i, p (x k i)
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg p _
    refine ⟨M + 1, by linarith, ?_⟩
    rintro _ ⟨k, a, ha, rfl⟩
    change p (∑ i, a i • x k i) < M + 1
    by_cases hk : j ≤ k
    · have hmem := hj (hU.antitone hk (hx k a ha))
      exact ((p.mem_ball_zero.mp hmem).trans_le (by linarith))
    · refine lt_of_le_of_lt ?_ (lt_add_of_pos_right M one_pos)
      calc
        p (∑ i, a i • x k i) ≤ ∑ i, p (a i • x k i) :=
          Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
        _ ≤ ∑ i, p (x k i) := by
          apply Finset.sum_le_sum
          intro i _
          rw [map_smul_eq_mul]
          exact mul_le_of_le_one_left (apply_nonneg p _) (ha i)
        _ ≤ M := Finset.single_le_sum (f := fun k ↦ ∑ i, p (x k i))
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ apply_nonneg p _)
          (Finset.mem_range.mpr (lt_of_not_ge hk))
  obtain ⟨C, _, hC⟩ := h B hB
  obtain ⟨k, hk⟩ := exists_nat_gt C
  exact (not_lt_of_ge (hC (n k) (x k) fun a ha ↦ ⟨k, a, ha, rfl⟩)) (hk.trans (hlower k))

/-- Lemma C.2.4.11. A Fréchet space is nuclear exactly when its strong dual is nuclear. -/
theorem nuclearLocallyConvex_strongDual_iff (hFr : IsFrechetTVS E) :
    NuclearLocallyConvex.{u, u} (StrongDual ℂ E) ↔ NuclearLocallyConvex.{u, u} E := by
  refine ⟨fun h ↦ ?_, strongDual_nuclear_of_nuclear_frechet hFr⟩
  letI : IsTopologicalAddGroup E := hFr.choose
  letI : PolynormableSpace ℂ E := hFr.choose_spec.1
  letI : TopologicalSpace.MetrizableSpace E := hFr.choose_spec.2.1
  letI : T2Space E := inferInstance
  exact nuclearLocallyConvex_of_signedSum_bound fun q hq ↦
    sum_bound_on_nhds_of_bounded q (sum_bound_on_bounded h q hq)

end

end Masullo
