import ApproximationNumbers
import NuclearTrace
import Mathlib.Logic.Equiv.Fin.Basic

open Filter Topology Set InnerProductSpace
open scoped InnerProductSpace

namespace Masullo

noncomputable section

universe u

variable {E F : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Schatten membership and norm with the approximation numbers of (C.3.6.2). -/
def IsSchatten (p : ℝ) (A : E →L[ℂ] F) : Prop :=
  IsCompactOperator A ∧ Summable (fun m => approximationNumber m A ^ p)

def schattenNorm (p : ℝ) (A : E →L[ℂ] F) : ℝ :=
  (∑' m, approximationNumber m A ^ p) ^ p⁻¹

private theorem summable_approximationNumber_div_two {f : ℕ → ℝ}
    (hf : Summable f) (hpos : ∀ n, 0 ≤ f n) : Summable (fun n => f (n / 2)) := by
  apply (Nat.divModEquiv 2).symm.summable_iff.mp
  change Summable (fun x : ℕ × Fin 2 => f ((x.1 * 2 + x.2.val) / 2))
  have h : ∀ (x : ℕ × Fin 2), (x.1 * 2 + x.2.val) / 2 = x.1 := by
    rintro ⟨n, j⟩
    have hj := j.isLt
    dsimp
    omega
  simp only [h]
  exact (summable_prod_of_nonneg (fun x => hpos x.1)).mpr
    ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), by simpa using hf.mul_left 2⟩

omit [CompleteSpace E] [CompleteSpace F] in
private theorem approximationNumber_tendsto_zero_of_summable {p : ℝ} (hp : 0 < p)
    {A : E →L[ℂ] F} (hA : Summable (fun m => approximationNumber m A ^ p)) :
    Tendsto (fun m => approximationNumber m A) atTop (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 p⁻¹ (Or.inr (inv_nonneg.mpr hp.le))).tendsto).comp
    hA.tendsto_atTop_zero
  have he (m : ℕ) : (approximationNumber m A ^ p) ^ p⁻¹ = approximationNumber m A := by
    rw [← Real.rpow_mul (approximationNumber_nonneg _ _), mul_inv_cancel₀ hp.ne', Real.rpow_one]
  simpa only [Function.comp_def, he, Real.zero_rpow (inv_ne_zero hp.ne')] using h

omit [CompleteSpace E] [CompleteSpace F] in
private theorem schatten_comp_left {p : ℝ} (hp : 0 ≤ p) {A : E →L[ℂ] F}
    (hA : IsSchatten p A) (C : F →L[ℂ] F) : IsSchatten p (C.comp A) := by
  refine ⟨hA.1.clm_comp C, ?_⟩
  apply (hA.2.mul_left (‖C‖ ^ p)).of_nonneg_of_le (fun _ => Real.rpow_nonneg (approximationNumber_nonneg _ _) _)
  intro m
  rw [← Real.mul_rpow (norm_nonneg _) (approximationNumber_nonneg _ _)]
  exact Real.rpow_le_rpow (approximationNumber_nonneg _ _) (approximationNumber_comp_left_le C A m) hp

omit [CompleteSpace E] [CompleteSpace F] in
private theorem schatten_comp_right {p : ℝ} (hp : 0 ≤ p) {A : E →L[ℂ] F}
    (hA : IsSchatten p A) (B : E →L[ℂ] E) : IsSchatten p (A.comp B) := by
  refine ⟨hA.1.comp_clm B, ?_⟩
  apply (hA.2.mul_right (‖B‖ ^ p)).of_nonneg_of_le (fun _ => Real.rpow_nonneg (approximationNumber_nonneg _ _) _)
  intro m
  rw [← Real.mul_rpow (approximationNumber_nonneg _ _) (norm_nonneg _)]
  exact Real.rpow_le_rpow (approximationNumber_nonneg _ _) (approximationNumber_comp_right_le A B m) hp

omit [CompleteSpace E] [CompleteSpace F] in
private theorem schatten_errors_tendsto {p : ℝ} (hp : 0 < p) {A : E →L[ℂ] F}
    (hA : IsSchatten p A) {ι : Type*} {l : Filter ι} (D : ι → E →L[ℂ] F)
    (hD : Tendsto (fun i => ‖D i‖) l (𝓝 0)) {C : ℝ} (hC : 0 ≤ C)
    (hDC : ∀ i m, approximationNumber m (D i) ≤ C * approximationNumber (m / 2) A) :
    Tendsto (fun i => schattenNorm p (D i)) l (𝓝 0) := by
  have hsm := summable_approximationNumber_div_two hA.2
    (fun n => Real.rpow_nonneg (approximationNumber_nonneg _ _) _)
  have hdom := hsm.mul_left (C ^ p)
  have ht : Tendsto (fun i => ∑' m, approximationNumber m (D i) ^ p) l (𝓝 0) := by
    rw [← show (∑' _ : ℕ, (0 : ℝ)) = 0 from tsum_zero]
    apply tendsto_tsum_of_dominated_convergence hdom
    · intro m
      have hx := squeeze_zero (fun i => approximationNumber_nonneg m (D i))
        (fun i => approximationNumber_le_norm m (D i)) hD
      simpa only [Function.comp_def, Real.zero_rpow hp.ne'] using
        ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp hx)
    · exact Eventually.of_forall fun i m => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (approximationNumber_nonneg _ _) _),
          ← Real.mul_rpow hC (approximationNumber_nonneg _ _)]
        exact Real.rpow_le_rpow (approximationNumber_nonneg _ _) (hDC i m) hp.le
  simpa only [schattenNorm, Function.comp_def, Real.zero_rpow (inv_ne_zero hp.ne')] using
    ((Real.continuousAt_rpow_const 0 p⁻¹ (Or.inr (inv_nonneg.mpr hp.le))).tendsto.comp ht)

private theorem exists_seq_opNorm_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hS : ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖S n‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := S) (fun x => by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (hS x))
    exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩)
  exact ⟨C, (norm_nonneg (S 0)).trans (hC 0), hC⟩

/-- Proposition C.3.6.5. Strong left cutoffs and self-adjoint strong right cutoffs
converge in the Schatten norm, including the joint limit. -/
theorem schatten_strong_composition_convergence {p : ℝ} (hp : 1 ≤ p)
    {A : E →L[ℂ] F} (hA : IsSchatten p A)
    (B : E →L[ℂ] E) (C : F →L[ℂ] F)
    (Bs : ℕ → E →L[ℂ] E) (Cs : ℕ → F →L[ℂ] F)
    (hBs : ∀ x, Tendsto (fun n => Bs n x) atTop (𝓝 (B x)))
    (hCs : ∀ x, Tendsto (fun n => Cs n x) atTop (𝓝 (C x)))
    (hself : ∀ n, IsSelfAdjoint (Bs n)) :
    (∀ j k, IsSchatten p ((Cs j).comp A) ∧ IsSchatten p (A.comp (Bs k)) ∧
      IsSchatten p (((Cs j).comp A).comp (Bs k))) ∧
    IsSchatten p (C.comp A) ∧ IsSchatten p (A.comp B) ∧ IsSchatten p ((C.comp A).comp B) ∧
    Tendsto (fun j => schattenNorm p ((Cs j).comp A - C.comp A)) atTop (𝓝 0) ∧
    Tendsto (fun k => schattenNorm p (A.comp (Bs k) - A.comp B)) atTop (𝓝 0) ∧
    Tendsto (fun (jk : ℕ × ℕ) =>
      schattenNorm p (((Cs jk.1).comp A).comp (Bs jk.2) - (C.comp A).comp B)) atTop (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨MB, hMB, hnormB⟩ := exists_seq_opNorm_bound Bs B hBs
  obtain ⟨MC, hMC, hnormC⟩ := exists_seq_opNorm_bound Cs C hCs
  let L (j : ℕ) := (Cs j).comp A - C.comp A
  let R (k : ℕ) := A.comp (Bs k) - A.comp B
  let J (jk : ℕ × ℕ) := ((Cs jk.1).comp A).comp (Bs jk.2) - (C.comp A).comp B
  have hBself : B.adjoint = B := by
    ext x
    apply ext_inner_left ℂ
    intro y
    have h₁ : Tendsto (fun n => ⟪y, Bs n x⟫_ℂ) atTop (𝓝 ⟪y, B x⟫_ℂ) :=
      ((innerSL ℂ y).continuous.tendsto (B x)).comp (hBs x)
    have h₂ : Tendsto (fun n => ⟪Bs n y, x⟫_ℂ) atTop (𝓝 ⟪B y, x⟫_ℂ) :=
      (continuous_inner.tendsto (B y, x)).comp ((hBs y).prodMk_nhds tendsto_const_nhds)
    have hsame (n : ℕ) : ⟪Bs n y, x⟫_ℂ = ⟪y, Bs n x⟫_ℂ := by
      rw [← (Bs n).adjoint_inner_right, show (Bs n).adjoint = Bs n from (hself n).star_eq]
    simp_rw [hsame] at h₂
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact tendsto_nhds_unique h₂ h₁
  have hAadj : IsCompactOperator A.adjoint := by
    apply isCompactOperator_of_approximationNumber_tendsto_zero
    simp only [approximationNumber_adjoint]
    exact approximationNumber_tendsto_zero_of_summable hp0 hA.2
  have hLnorm : Tendsto (fun j => ‖L j‖) atTop (𝓝 0) := by
    simpa only [L, sub_self, norm_zero] using
      ((tendsto_norm_compact_right A C hA.1 Cs hCs).sub_const (C.comp A)).norm
  have hRnorm : Tendsto (fun k => ‖R k‖) atTop (𝓝 0) := by
    have he (k : ℕ) : ‖R k‖ = ‖(Bs k).comp A.adjoint - B.comp A.adjoint‖ := by
      rw [← ContinuousLinearMap.adjoint.norm_map (R k)]
      simp only [R, map_sub, ContinuousLinearMap.adjoint_comp, hBself]
      rw [show (Bs k).adjoint = Bs k from (hself k).star_eq]
    simpa only [he, sub_self, norm_zero] using
      ((tendsto_norm_compact_right A.adjoint B hAadj Bs hBs).sub_const
        (B.comp A.adjoint)).norm
  have hL (j m : ℕ) : approximationNumber m (L j) ≤ (MC + ‖C‖) * approximationNumber m A := by
    change approximationNumber m ((Cs j).comp A - C.comp A) ≤ _
    rw [← ContinuousLinearMap.sub_comp]
    exact (approximationNumber_comp_left_le (Cs j - C) A m).trans
      (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add (hnormC j) le_rfl))
        (approximationNumber_nonneg _ _))
  have hR (k m : ℕ) : approximationNumber m (R k) ≤ (MB + ‖B‖) * approximationNumber m A := by
    change approximationNumber m (A.comp (Bs k) - A.comp B) ≤ _
    rw [← ContinuousLinearMap.comp_sub, mul_comm]
    exact (approximationNumber_comp_right_le A (Bs k - B) m).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hnormB k) le_rfl))
        (approximationNumber_nonneg _ _))
  have hJ (jk : ℕ × ℕ) : J jk = (L jk.1).comp (Bs jk.2) + C.comp (R jk.2) := by
    ext x
    simp only [J, L, R, ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
    abel
  have hJnorm : Tendsto (fun jk => ‖J jk‖) atTop (𝓝 0) := by
    have hf : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) atTop :=
      tendsto_atTop_atTop.mpr fun n => ⟨(n, 0), fun _ h => h.1⟩
    have hs : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) atTop :=
      tendsto_atTop_atTop.mpr fun n => ⟨(0, n), fun _ h => h.2⟩
    have he := ((hLnorm.comp hf).mul_const MB).add ((hRnorm.comp hs).const_mul ‖C‖)
    have he' : Tendsto (fun jk => ‖L jk.1‖ * MB + ‖C‖ * ‖R jk.2‖)
        (atTop : Filter (ℕ × ℕ)) (𝓝 0) := by
      simpa only [Function.comp_def, zero_mul, mul_zero, add_zero] using he
    refine squeeze_zero (fun _ => norm_nonneg _) (fun jk => ?_) he'
    rw [hJ]
    refine (norm_add_le _ _).trans (add_le_add ?_ (C.opNorm_comp_le (R jk.2)))
    exact ((L jk.1).opNorm_comp_le (Bs jk.2)).trans
      (mul_le_mul_of_nonneg_left (hnormB jk.2) (norm_nonneg _))
  refine ⟨fun j k => ⟨schatten_comp_left hp0.le hA (Cs j),
      schatten_comp_right hp0.le hA (Bs k),
      schatten_comp_right hp0.le (schatten_comp_left hp0.le hA (Cs j)) (Bs k)⟩,
    schatten_comp_left hp0.le hA C, schatten_comp_right hp0.le hA B,
    schatten_comp_right hp0.le (schatten_comp_left hp0.le hA C) B, ?_, ?_, ?_⟩
  · refine schatten_errors_tendsto hp0 hA L hLnorm (add_nonneg hMC (norm_nonneg C)) fun j m => ?_
    exact (hL j m).trans (mul_le_mul_of_nonneg_left
      (approximationNumber_antitone A (Nat.div_le_self _ _)) (add_nonneg hMC (norm_nonneg C)))
  · refine schatten_errors_tendsto hp0 hA R hRnorm (add_nonneg hMB (norm_nonneg B)) fun k m => ?_
    exact (hR k m).trans (mul_le_mul_of_nonneg_left
      (approximationNumber_antitone A (Nat.div_le_self _ _)) (add_nonneg hMB (norm_nonneg B)))
  · let K := (MC + ‖C‖) * MB + ‖C‖ * (MB + ‖B‖)
    refine schatten_errors_tendsto hp0 hA J hJnorm (show 0 ≤ K by
      dsimp [K]; positivity) fun jk m => ?_
    let n := m / 2
    have hnm : n + n ≤ m := by dsimp [n]; omega
    have h₁ : approximationNumber n ((L jk.1).comp (Bs jk.2)) ≤
        (MC + ‖C‖) * approximationNumber n A * MB :=
      (approximationNumber_comp_right_le _ _ n).trans
        (mul_le_mul (hL jk.1 n) (hnormB _) (norm_nonneg _)
          (mul_nonneg (add_nonneg hMC (norm_nonneg _)) (approximationNumber_nonneg _ _)))
    have h₂ : approximationNumber n (C.comp (R jk.2)) ≤
        ‖C‖ * ((MB + ‖B‖) * approximationNumber n A) :=
      (approximationNumber_comp_left_le _ _ n).trans
        (mul_le_mul_of_nonneg_left (hR jk.2 n) (norm_nonneg _))
    calc
      approximationNumber m (J jk) ≤ approximationNumber (n + n) (J jk) :=
        approximationNumber_antitone _ hnm
      _ ≤ approximationNumber n ((L jk.1).comp (Bs jk.2)) +
          approximationNumber n (C.comp (R jk.2)) := by rw [hJ]; exact approximationNumber_add_le _ _ _ _
      _ ≤ K * approximationNumber n A := by
        dsimp [K]
        nlinarith [add_le_add h₁ h₂]

end

end Masullo
