import AbsolutelySummingComposition
import NuclearIntegralOperators

/-!
# Nuclearity from finite sums with unit-disk coefficients

The local transition argument adapts the Apache-2.0 original proof in
`RiemannMasullo/AppC_LCTVS/Sec2b.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`.
-/

open Function Set Topology
open scoped Classical NNReal

namespace Masullo

noncomputable section

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

omit [TopologicalSpace E] in
private theorem absolutelySumming_transition
    (p q : Seminorm ℂ E) (hqp : q ≤ p) {W : Set E} (hW : p.ball 0 1 ⊆ W)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (n : ℕ) (x : Fin n → E),
      (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ W) →
        ∑ i, q (x i) ≤ C) :
    AbsolutelySumming.HasBound (localBanachTransition q p hqp) C := by
  intro n x M hM hx
  let j := localBanachDenseMap p
  let T := localBanachTransition q p hqp
  have hd : DenseRange (fun z : Fin n → E ↦ fun i ↦ j (z i)) :=
    DenseRange.piMap fun _ ↦ localBanachDenseMap_dense p
  have hb (y : Fin n → LocalBanach p) :
      ∑ i, ‖T (y i)‖ ≤ C * (M + ∑ i, ‖y i - x i‖) := by
    refine hd.induction_on y (isClosed_le (by fun_prop) (by fun_prop)) fun z ↦ ?_
    let N := M + ∑ i, ‖j (z i) - x i‖
    have hN : 0 ≤ N := add_nonneg hM (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    have hsum (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
        p (∑ i, a i • z i) ≤ N := by
      rw [← norm_localBanachDenseMap, map_sum]
      simp only [map_smul]
      obtain ⟨f, hf, hfs⟩ := exists_dual_vector'' ℂ (∑ i, a i • j (z i))
      have hnorm : ‖f (∑ i, a i • j (z i))‖ = ‖∑ i, a i • j (z i)‖ := by
        rw [hfs]
        change ‖((‖∑ i, a i • j (z i)‖ : ℝ) : ℂ)‖ = _
        exact Complex.norm_of_nonneg (norm_nonneg (∑ i, a i • j (z i)))
      rw [← hnorm, map_sum]
      refine (norm_sum_le _ _).trans ?_
      simp only [map_smul, norm_smul]
      refine (Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (norm_nonneg _) (ha i)).trans ?_
      have hdiff (i : Fin n) : ‖f (j (z i))‖ ≤ ‖f (x i)‖ + ‖j (z i) - x i‖ := by
        have hdist : ‖f (j (z i) - x i)‖ ≤ ‖j (z i) - x i‖ :=
          (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
        calc
          _ = ‖f (x i) + f (j (z i) - x i)‖ := by rw [← map_add, add_sub_cancel]
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hdist)
      exact (Finset.sum_le_sum fun i _ ↦ hdiff i).trans
        (by rw [Finset.sum_add_distrib]; exact add_le_add (hx f hf) le_rfl)
    have hs : ∑ i, q (z i) ≤ C * N := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      let r := N + ε / (C + 1)
      have hδ : 0 < ε / (C + 1) := by positivity
      have hr : 0 < r := add_pos_of_nonneg_of_pos hN hδ
      let c : ℂ := (r : ℂ)
      have hc : ‖c‖ = r := Complex.norm_of_nonneg hr.le
      have hz := h n (fun i ↦ c⁻¹ • z i) (fun a ha ↦ ?_)
      · simp only [map_smul_eq_mul, norm_inv, hc, ← Finset.mul_sum] at hz
        calc
          _ ≤ C * r := by simpa only [mul_comm] using (inv_mul_le_iff₀ hr).mp hz
          _ ≤ C * N + ε := by
            dsimp only [r]
            have hh := div_mul_cancel₀ ε (show C + 1 ≠ 0 by positivity)
            nlinarith
      · have he : (∑ i, a i • c⁻¹ • z i) = c⁻¹ • ∑ i, a i • z i := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
        apply hW
        apply p.mem_ball_zero.mpr
        rw [he, map_smul_eq_mul, norm_inv, hc, inv_mul_lt_iff₀ hr, mul_one]
        exact (hsum a ha).trans_lt (lt_add_of_pos_right _ hδ)
    have hj (i : Fin n) : ‖T (j (z i))‖ = q (z i) := by
      simp [T, j]
    simpa only [hj] using hs
  simpa [T] using hb x

/-- If every continuous seminorm admits a bound for the sum of its values
on finite families whose unit-disk linear combinations lie in one
zero-neighborhood, the space is nuclear. -/
theorem nuclearLocallyConvex_of_signedSum_bound
    [PolynormableSpace ℂ E] [T2Space E]
    (h : ∀ (q : Seminorm ℂ E), Continuous q →
      ∃ W ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧
        ∀ (n : ℕ) (x : Fin n → E),
          (∀ a : Fin n → ℂ, (∀ i, ‖a i‖ ≤ 1) → (∑ i, a i • x i) ∈ W) →
            ∑ i, q (x i) ≤ C) : NuclearLocallyConvex.{v, u} E := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  have step (q : Seminorm ℂ E) (hq : Continuous q) :
      ∃ (p : Seminorm ℂ E) (_ : Continuous p) (hqp : q ≤ p),
        ∃ C, 0 ≤ C ∧ AbsolutelySumming.HasBound (localBanachTransition q p hqp) C := by
    obtain ⟨W, hW, C, hC, hb⟩ := h q hq
    obtain ⟨⟨I, δ⟩, hδ, hδW⟩ :=
      (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball.mem_iff.mp hW
    let r₀ : Seminorm ℂ E := I.sup (fun i ↦ i.val)
    have hr₀ : Continuous r₀ := Seminorm.continuous_finsetSup (fun i _ ↦ i.property)
    let c : ℝ≥0 := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
    let r : Seminorm ℂ E := c • r₀
    have hr : Continuous r := hr₀.const_smul c
    let p := q ⊔ r
    have hqp : q ≤ p := le_sup_left
    have hsub : p.ball 0 1 ⊆ W := fun x hx ↦ by
      apply hδW
      apply r₀.mem_ball_zero.mpr
      have hx' := ((le_sup_right : r ≤ p) x).trans_lt (p.mem_ball_zero.mp hx)
      change δ⁻¹ * r₀ x < 1 at hx'
      simpa only [mul_one] using (inv_mul_lt_iff₀ hδ).mp hx'
    exact ⟨p, hq.sup hr, hqp, C, hC, absolutelySumming_transition p q hqp hsub hC hb⟩
  apply nuclearLocallyConvex_of_integralTransition
  intro q hq
  obtain ⟨p₁, hp₁, h₁, s₁⟩ := step q hq
  obtain ⟨p₂, hp₂, h₂, s₂⟩ := step p₁ hp₁
  obtain ⟨p₃, hp₃, h₃, s₃⟩ := step p₂ hp₂
  let t₁ := localBanachTransition q p₁ h₁
  let t₂ := localBanachTransition p₁ p₂ h₂
  let t₃ := localBanachTransition p₂ p₃ h₃
  have hdom := h₁.trans (h₂.trans h₃)
  have hcomp : t₁.comp (t₂.comp t₃) = localBanachTransition q p₃ hdom := by
    apply DFunLike.coe_injective
    apply (localBanachDenseMap_dense p₃).equalizer
      (t₁.comp (t₂.comp t₃)).continuous (localBanachTransition q p₃ hdom).continuous
    funext x
    simp [t₁, t₂, t₃]
  obtain ⟨ι, φ, y, hn, hs⟩ :=
    AbsolutelySumming.exists_rankOne_comp_three t₁ t₂ t₃ s₁ s₂ s₃
  exact ⟨p₃, hp₃, hdom, isIntegralOperator_of_rankOne_hasSum φ y hn (hcomp ▸ hs)⟩

end

end Masullo
