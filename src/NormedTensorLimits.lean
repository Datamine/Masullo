import ProjectiveTensorTopology
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

open Filter Function Set Topology
open scoped ComplexOrder Pointwise TensorProduct

namespace Masullo

noncomputable section

universe u v

variable {E : Type u} {F : Type v} {I J : Type*}
variable {A : I → Type*} {B : J → Type*}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
variable [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace ℂ (A i)]
variable [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℂ (B j)]

private def stageBallHull (i : ∀ n, A n →L[ℂ] E) (w : I → ℝ) : Set E :=
  absConvexHull ℂ (⋃ n, i n '' Metric.ball 0 (w n)⁻¹)

private theorem mem_stageBallHull (i : ∀ n, A n →L[ℂ] E) (w : I → ℝ) (n : I)
    {x : A n} (hx : x ∈ Metric.ball 0 (w n)⁻¹) : i n x ∈ stageBallHull i w :=
  subset_absConvexHull (mem_iUnion.mpr ⟨n, x, hx, rfl⟩)

private theorem stageBallHull_absorbent (i : ∀ n, A n →L[ℂ] E) (w : I → ℝ)
    (hw : ∀ n, 0 < w n) (hexhaust : ∀ x : E, ∃ n, x ∈ range (i n)) :
    Absorbent ℝ (stageBallHull i w) := by
  apply absorbent_iff_inv_smul.mpr
  intro x
  obtain ⟨n, y, rfl⟩ := hexhaust x
  have hn := Metric.ball_mem_nhds (0 : A n) (inv_pos.mpr (hw n))
  have h := absorbent_iff_inv_smul.mp (absorbent_nhds_zero (𝕜 := ℝ) hn) y
  filter_upwards [h] with c hc
  have he : i n (c⁻¹ • y) = c⁻¹ • i n y := ((i n).restrictScalars ℝ).map_smul c⁻¹ y
  rw [← he]
  exact mem_stageBallHull i w n hc

private def stageBallGauge (i : ∀ n, A n →L[ℂ] E) (w : I → ℝ)
    (hw : ∀ n, 0 < w n) (hexhaust : ∀ x : E, ∃ n, x ∈ range (i n)) : Seminorm ℂ E :=
  gaugeSeminorm balanced_absConvexHull ((convex_absConvexHull (𝕜 := ℂ)).lift ℝ)
    (stageBallHull_absorbent i w hw hexhaust)

private theorem stageBallGauge_continuous (i : ∀ n, A n →L[ℂ] E) (w : I → ℝ)
    (hw : ∀ n, 0 < w n) (hexhaust : ∀ x : E, ∃ n, x ∈ range (i n))
    (hlimit : ∀ p : Seminorm ℂ E,
      (∀ n, Continuous (p.comp (i n).toLinearMap)) → Continuous p) :
    Continuous (stageBallGauge i w hw hexhaust) := by
  apply hlimit
  intro n
  apply Seminorm.continuous (r := 2)
  refine mem_of_superset (Metric.ball_mem_nhds 0 (inv_pos.mpr (hw n))) fun x hx => ?_
  rw [Seminorm.ball_zero_eq]
  change gauge (stageBallHull i w) (i n x) < 2
  exact (gauge_le_one_of_mem (mem_stageBallHull i w n hx)).trans_lt (by norm_num)

private theorem seminorm_unitBall_absConvex {D : Type*} [AddCommGroup D] [Module ℂ D]
    (p : Seminorm ℂ D) : AbsConvex ℂ (p.closedBall 0 1) := by
  refine ⟨p.balanced_closedBall_zero _, convex_of_nonneg_surjective_algebraMap ℂ ?_ (p.convex_closedBall _ _)⟩
  intro z hz
  obtain ⟨r, hr, he⟩ := (RCLike.nonneg_iff_exists_ofReal (K := ℂ)).mp hz
  exact ⟨r, hr, he⟩

private theorem weighted_stage_tensor_bound
    (i : ∀ n, A n →L[ℂ] E) (j : ∀ n, B n →L[ℂ] F)
    (w : I → ℝ) (w' : J → ℝ) (hw : ∀ n, 0 < w n) (hw' : ∀ n, 0 < w' n)
    (Q : Seminorm ℂ (E ⊗[ℂ] F))
    (hQ : ∀ m n (x : A m) (y : B n),
      Q (i m x ⊗ₜ[ℂ] j n y) ≤ (w m * ‖x‖) * (w' n * ‖y‖)) :
    ∀ x ∈ stageBallHull i w, ∀ y ∈ stageBallHull j w', Q (x ⊗ₜ[ℂ] y) ≤ 1 := by
  have step (n : J) (y : B n) (hy : y ∈ Metric.ball 0 (w' n)⁻¹) :
      ∀ x ∈ stageBallHull i w, Q (x ⊗ₜ[ℂ] j n y) ≤ 1 := by
    let p := Q.comp ((TensorProduct.mk ℂ E F).flip (j n y))
    change ∀ x ∈ stageBallHull i w, p x ≤ 1
    intro x hx
    apply p.mem_closedBall_zero.mp
    refine absConvexHull_min ?_ (seminorm_unitBall_absConvex p) hx
    rintro _ hx
    obtain ⟨m, a, ha, rfl⟩ := mem_iUnion.mp hx
    apply p.mem_closedBall_zero.mpr
    have h₂ : w' n * ‖y‖ ≤ 1 := by
      have h' : ‖y‖ < (w' n)⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using hy
      exact (mul_le_mul_of_nonneg_left h'.le (hw' n).le).trans_eq (mul_inv_cancel₀ (hw' n).ne')
    have h₁' : ‖a‖ < (w m)⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    have h₁ : w m * ‖a‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left h₁'.le (hw m).le).trans_eq (mul_inv_cancel₀ (hw m).ne')
    exact (hQ m n a y).trans (mul_le_one₀ h₁ (mul_nonneg (hw' n).le (norm_nonneg _)) h₂)
  intro x hx y hy
  let p := Q.comp (TensorProduct.mk ℂ E F x)
  apply p.mem_closedBall_zero.mp
  refine absConvexHull_min ?_ (seminorm_unitBall_absConvex p) hy
  rintro _ hy
  obtain ⟨n, b, hb, rfl⟩ := mem_iUnion.mp hy
  exact p.mem_closedBall_zero.mpr (step n b hb x hx)

/-- Coordinatewise norm estimates with factorable weights give an actual
continuous projective tensor seminorm at the limits. -/
theorem projective_seminorm_of_weighted_stages
    (i : ∀ n, A n →L[ℂ] E) (j : ∀ n, B n →L[ℂ] F)
    (hexE : ∀ x : E, ∃ n, x ∈ range (i n)) (hexF : ∀ y : F, ∃ n, y ∈ range (j n))
    (hE : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (i n).toLinearMap)) → Continuous p)
    (hF : ∀ p : Seminorm ℂ F, (∀ n, Continuous (p.comp (j n).toLinearMap)) → Continuous p)
    (w : I → ℝ) (w' : J → ℝ) (hw : ∀ n, 0 < w n) (hw' : ∀ n, 0 < w' n)
    (Q : Seminorm ℂ (E ⊗[ℂ] F))
    (hQ : ∀ m n (x : A m) (y : B n),
      Q (i m x ⊗ₜ[ℂ] j n y) ≤ (w m * ‖x‖) * (w' n * ‖y‖)) :
    Continuous[projectiveTensorTopology E F, inferInstance] Q := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  let p := stageBallGauge i w hw hexE
  let r := stageBallGauge j w' hw' hexF
  have hp := stageBallGauge_continuous i w hw hexE hE
  have hr := stageBallGauge_continuous j w' hw' hexF hF
  have hbounded := weighted_stage_tensor_bound i j w w' hw hw' Q hQ
  let P : ProjectiveTensorTest E F := ⟨Q, p, r, hp, hr, fun x y => by
    have hh (ε : ℝ) (hε : 0 < ε) : Q (x ⊗ₜ[ℂ] y) ≤ (p x + ε) * (r y + ε) := by
      let d : ℝ := p x + ε
      let e : ℝ := r y + ε
      have hd : 0 < d := add_pos_of_nonneg_of_pos (apply_nonneg p x) hε
      have he : 0 < e := add_pos_of_nonneg_of_pos (apply_nonneg r y) hε
      have hx' : ((d : ℂ)⁻¹) • x ∈ stageBallHull i w := by
        have hc : p (((d : ℂ)⁻¹) • x) < 1 := by
          rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
          exact (inv_mul_lt_iff₀ hd).mpr (by simp [d, hε])
        exact setOfPred_gauge_lt_one_subset_self ((convex_absConvexHull (𝕜 := ℂ)).lift ℝ)
          (stageBallHull_absorbent i w hw hexE).zero_mem
          (stageBallHull_absorbent i w hw hexE) hc
      have hy' : ((e : ℂ)⁻¹) • y ∈ stageBallHull j w' := by
        have hc : r (((e : ℂ)⁻¹) • y) < 1 := by
          rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
          exact (inv_mul_lt_iff₀ he).mpr (by simp [e, hε])
        exact setOfPred_gauge_lt_one_subset_self ((convex_absConvexHull (𝕜 := ℂ)).lift ℝ)
          (stageBallHull_absorbent j w' hw' hexF).zero_mem
          (stageBallHull_absorbent j w' hw' hexF) hc
      have h := hbounded _ hx' _ hy'
      rw [TensorProduct.smul_tmul_smul, map_smul_eq_mul, norm_mul,
        norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hd.le,
        Real.norm_of_nonneg he.le, mul_assoc] at h
      have hle := (inv_mul_le_iff₀ he).mp ((inv_mul_le_iff₀ hd).mp h)
      exact hle.trans_eq (by dsimp [d, e]; ring)
    have hc : Continuous (fun ε : ℝ => (p x + ε) * (r y + ε)) := by fun_prop
    have ht : Tendsto (fun ε : ℝ => (p x + ε) * (r y + ε)) (𝓝[>] 0) (𝓝 (p x * r y)) := by
      have h := hc.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
      rw [ContinuousWithinAt, add_zero, add_zero] at h
      exact h
    haveI : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
    have hz : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Ioi 0 := self_mem_nhdsWithin
    exact isClosed_Ici.mem_of_tendsto ht (hz.mono fun ε hε => hh ε hε)⟩
  exact projectiveTensor_withSeminorms.continuous_seminorm P

theorem exists_positive_separate_weights (a : ℕ → ℕ → ℝ) :
    ∃ w v : ℕ → ℝ, (∀ m, 0 < w m) ∧ (∀ n, 0 < v n) ∧ ∀ m n, a m n ≤ w m * v n := by
  let w (m : ℕ) := 1 + ∑ n ∈ Finset.range (m + 1), max 0 (a m n)
  let v (n : ℕ) := 1 + ∑ m ∈ Finset.range (n + 1), max 0 (a m n)
  have hw (m : ℕ) : 1 ≤ w m := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  have hv (n : ℕ) : 1 ≤ v n := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  refine ⟨w, v, fun m => zero_lt_one.trans_le (hw m), fun n => zero_lt_one.trans_le (hv n), fun m n => ?_⟩
  by_cases hmn : n ≤ m
  · have ha : a m n ≤ w m := (le_max_right _ _).trans
      ((Finset.single_le_sum (fun j _ => le_max_left 0 (a m j))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))).trans
        (le_add_of_nonneg_left zero_le_one))
    exact ha.trans (le_mul_of_one_le_right (zero_le_one.trans (hw m)) (hv n))
  · have ha : a m n ≤ v n := (le_max_right _ _).trans
      ((Finset.single_le_sum (fun i _ => le_max_left 0 (a i n))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_of_not_ge hmn)))).trans
        (le_add_of_nonneg_left zero_le_one))
    exact ha.trans (le_mul_of_one_le_left (zero_le_one.trans (hv n)) (hw m))

private theorem normed_projective_elementary_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (q : Seminorm ℂ (X ⊗[ℂ] Y)) (hq : Continuous[projectiveTensorTopology X Y, inferInstance] q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y, q (x ⊗ₜ[ℂ] y) ≤ c * ‖x‖ * ‖y‖ := by
  letI : TopologicalSpace (X ⊗[ℂ] Y) := projectiveTensorTopology X Y
  have hW := projectiveTensor_withSeminorms (E := X) (F := Y)
  obtain ⟨s, D, -, hD⟩ := Seminorm.bound_of_continuous hW q hq
  have ht (P : ProjectiveTensorTest X Y) :
      ∃ r : ℝ, 0 ≤ r ∧ ∀ x y, P.tensor (x ⊗ₜ[ℂ] y) ≤ r * ‖x‖ * ‖y‖ := by
    obtain ⟨a, ha, h₁⟩ := Seminorm.bound_of_continuous_normedSpace P.first P.first_continuous
    obtain ⟨b, hb, h₂⟩ := Seminorm.bound_of_continuous_normedSpace P.second P.second_continuous
    refine ⟨a * b, (mul_pos ha hb).le, fun x y => ?_⟩
    exact (P.bound x y).trans ((mul_le_mul (h₁ x) (h₂ y)
      (apply_nonneg _ _) (mul_nonneg ha.le (norm_nonneg _))).trans_eq (by ring))
  choose r hr hb using ht
  let c : ℝ := ∑ P ∈ s, r P
  have hc : 0 ≤ c := Finset.sum_nonneg fun P _ => hr P
  refine ⟨D * c, mul_nonneg D.coe_nonneg hc, fun x y => ?_⟩
  have hsup : s.sup ProjectiveTensorTest.tensor (x ⊗ₜ[ℂ] y) ≤ c * ‖x‖ * ‖y‖ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro P hP
    exact (hb P x y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun P _ => hr P) hP)
        (norm_nonneg _)) (norm_nonneg _))
  exact (hD (x ⊗ₜ[ℂ] y)).trans
    ((mul_le_mul_of_nonneg_left hsup D.coe_nonneg).trans_eq (by ring))

section Countable

variable {C : ℕ → Type*} {D : ℕ → Type*}
variable [∀ n, NormedAddCommGroup (C n)] [∀ n, NormedSpace ℂ (C n)]
variable [∀ n, NormedAddCommGroup (D n)] [∀ n, NormedSpace ℂ (D n)]
variable [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]

/-- The projective seminorms on the algebraic tensor of two countable
normed-stage limits are precisely those continuous on all stage pairs. -/
theorem countable_projectiveTensor_stageCriterion
    (i : ∀ n, C n →L[ℂ] E) (j : ∀ n, D n →L[ℂ] F)
    (hexE : ∀ x : E, ∃ n, x ∈ range (i n)) (hexF : ∀ y : F, ∃ n, y ∈ range (j n))
    (hE : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (i n).toLinearMap)) → Continuous p)
    (hF : ∀ p : Seminorm ℂ F, (∀ n, Continuous (p.comp (j n).toLinearMap)) → Continuous p)
    (Q : Seminorm ℂ (E ⊗[ℂ] F)) :
    Continuous[projectiveTensorTopology E F, inferInstance] Q ↔
      ∀ m n, Continuous[projectiveTensorTopology (C m) (D n), inferInstance]
        (Q.comp (TensorProduct.map (i m).toLinearMap (j n).toLinearMap)) := by
  constructor
  · intro h m n
    letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
    letI : TopologicalSpace (C m ⊗[ℂ] D n) := projectiveTensorTopology (C m) (D n)
    exact h.comp (projectiveTensor_map_continuous (i m) (j n))
  · intro h
    have hm (m n : ℕ) :
        ∃ a : ℝ, ∀ (x : C m) (y : D n), Q (i m x ⊗ₜ[ℂ] j n y) ≤ a * ‖x‖ * ‖y‖ := by
      obtain ⟨a, -, ha⟩ := normed_projective_elementary_bound _ (h m n)
      exact ⟨a, fun x y => by
        simpa only [Seminorm.comp_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe] using ha x y⟩
    choose a ha using hm
    obtain ⟨w, v, hw, hv, hdom⟩ := exists_positive_separate_weights a
    apply projective_seminorm_of_weighted_stages i j hexE hexF hE hF w v hw hv Q
    intro m n x y
    exact (ha m n x y).trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hdom m n) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring))

end Countable

end

end Masullo
