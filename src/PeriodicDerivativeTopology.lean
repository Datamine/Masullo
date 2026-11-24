import PeriodicSmoothTopology
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.ContinuousMap.Compact

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

abbrev PeriodInterval (d : ℝ) := ↥(Icc (0 : ℝ) d)

def periodicDerivativeLM (d : ℝ) (n : ℕ) :
    SmoothPeriodic d →ₗ[ℂ] C(PeriodInterval d, ℂ) where
  toFun f := ⟨fun x => iteratedDeriv n (f : ℝ → ℂ) x,
    (f.property.1.continuous_iteratedDeriv n (by exact_mod_cast le_top)).comp
      continuous_subtype_val⟩
  map_add' f g := by
    ext x
    exact iteratedDeriv_add ((f.property.1.of_le (by exact_mod_cast le_top)).contDiffAt)
      ((g.property.1.of_le (by exact_mod_cast le_top)).contDiffAt)
  map_smul' c f := by
    ext x
    exact iteratedDeriv_const_smul_field c (f : ℝ → ℂ)

def periodicDerivativesLM (d : ℝ) :
    SmoothPeriodic d →ₗ[ℂ] (ℕ → C(PeriodInterval d, ℂ)) :=
  LinearMap.pi (periodicDerivativeLM d)

@[instance_reducible] def periodicDerivativeTopology (d : ℝ) : TopologicalSpace (SmoothPeriodic d) :=
  TopologicalSpace.induced (periodicDerivativesLM d) inferInstance

def periodicDerivativeSeminorms (d : ℝ) :
    SeminormFamily ℂ (SmoothPeriodic d) ((_ : ℕ) × Fin 1) :=
  fun i => (normSeminorm ℂ C(PeriodInterval d, ℂ)).comp (periodicDerivativeLM d i.1)

theorem periodicDerivative_withSeminorms (d : ℝ) :
    WithSeminorms (topology := periodicDerivativeTopology d) (periodicDerivativeSeminorms d) :=
  (periodicDerivativesLM d).withSeminorms_induced <|
    withSeminorms_pi (fun _ : ℕ => norm_withSeminorms ℂ C(PeriodInterval d, ℂ))

private theorem periodic_iteratedDeriv {d : ℝ} {f : ℝ → ℂ} (hf : Periodic f d)
    (n : ℕ) : Periodic (iteratedDeriv n f) d := by
  intro x
  have he : (fun y => f (y + d)) = f := funext hf
  rw [← congrFun (iteratedDeriv_comp_add_const n f d) x, he]

theorem iteratedDeriv_le_periodicDerivativeNorm {d : ℝ} (hd : 0 < d)
    (f : SmoothPeriodic d) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤ ‖periodicDerivativeLM d n f‖ := by
  obtain ⟨m, hm⟩ := exists_integerTranslate_mem_Ico 0 hd x
  have hm' : x + d * (m : ℝ) ∈ Icc 0 d := by simpa using Ico_subset_Icc_self hm
  have he := ((periodic_iteratedDeriv f.property.2 n).int_mul m) x
  rw [mul_comm (m : ℝ) d] at he
  rw [← he]
  exact (periodicDerivativeLM d n f).norm_coe_le_norm ⟨_, hm'⟩

private theorem periodic_chart_derivative_bound (d : ℝ) [Fact (0 < d)] (n : ℕ) :
    ∃ A : ℝ, ∀ f : SmoothPeriodic d,
      ‖periodicDerivativeLM d n f‖ ≤ A * SchwartzMap.seminorm ℂ 0 n (periodicChart d Fact.out f) := by
  classical
  have hs := periodicCutoff_spec d Fact.out
  obtain ⟨s, hsum⟩ := exists_uniform_translate_finset isCompact_Icc
    (isCompact_Icc (a := (-1 : ℝ)) (b := d + 1)) (Fact.out : 0 < d).ne'
  refine ⟨s.card, fun f => ?_⟩
  let g := periodicChart d Fact.out f
  have hg : support g ⊆ Icc (-d) d := fun x hx =>
    hs.2.1 fun hz => hx (by change periodicCutoff d Fact.out x * (f : ℝ → ℂ) x = 0; simp [hz])
  have hP : integerPeriodization d g = (f : ℝ → ℂ) := hs.2.2 _ f.property.2
  apply (ContinuousMap.norm_le _ (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))).mpr
  intro x
  have hx₁ : -1 < (x : ℝ) := by linarith [x.property.1]
  have hx₂ : (x : ℝ) < d + 1 := by linarith [x.property.2]
  have he : (f : ℝ → ℂ) =ᶠ[𝓝 (x : ℝ)] (fun y : ℝ => ∑ m ∈ s, g (y + d * (m : ℝ))) := by
    rw [← hP]
    filter_upwards [Icc_mem_nhds hx₁ hx₂] with y hy
    exact integerPeriodization_finset_eq hg (hsum y hy)
  change ‖iteratedDeriv n (f : ℝ → ℂ) (x : ℝ)‖ ≤
    (s.card : ℝ) * SchwartzMap.seminorm ℂ 0 n g
  rw [he.iteratedDeriv_eq n, iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_comp_add_const]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ m ∈ s, SchwartzMap.seminorm ℂ 0 n g := Finset.sum_le_sum fun m _ => by
        rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g n _
      _ = _ := by simp [nsmul_eq_mul]
  · intro m _
    exact ((g.smooth n).comp (by fun_prop)).contDiffAt

private theorem continuous_periodicDerivativeLM (d : ℝ) [Fact (0 < d)] (n : ℕ) :
    Continuous (periodicDerivativeLM d n) := by
  classical
  have hS := (periodicChart d Fact.out).withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)
  obtain ⟨A, hA⟩ := periodic_chart_derivative_bound d n
  refine WithSeminorms.continuous_of_isBounded hS (norm_withSeminorms ℂ _)
    (periodicDerivativeLM d n) (Seminorm.IsBounded.of_real fun _ => ?_)
  exact ⟨{(0,n)}, A, fun f => by simpa [SeminormFamily.comp_apply] using hA f⟩

set_option maxHeartbeats 350000 in
private theorem continuous_chart_derivativeTopology (d : ℝ) [Fact (0 < d)] :
    @Continuous _ _ (periodicDerivativeTopology d) _ (periodicChart d Fact.out) := by
  classical
  let b := periodicCutoff d Fact.out
  let K := Icc (-d) d
  have hbC : ContDiff ℝ ∞ b := (periodicCutoff_spec d Fact.out).1
  have hb : support b ⊆ K := (periodicCutoff_spec d Fact.out).2.1
  let B := (HasCompactSupport.intro (isCompact_Icc (a := -d) (b := d))
    fun x hx => notMem_support.mp (fun h => hx (hb h))).toSchwartzMap hbC
  refine WithSeminorms.continuous_of_isBounded (periodicDerivative_withSeminorms d)
    (schwartz_withSeminorms ℂ ℝ ℂ) (periodicChart d Fact.out)
    (Seminorm.IsBounded.of_real fun ⟨k, n⟩ => ?_)
  let s : Finset ((_ : ℕ) × Fin 1) := (Finset.range (n + 1)).image (fun j => ⟨j, 0⟩)
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k i B
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  refine ⟨s, C, fun f => ?_⟩
  let p := s.sup (periodicDerivativeSeminorms d)
  apply SchwartzMap.seminorm_le_bound' ℂ _ _ _ (mul_nonneg hC (apply_nonneg _ _))
  intro x
  rw [← Real.norm_eq_abs]
  change ‖x‖ ^ k * ‖iteratedDeriv n (fun y => b y * (f : ℝ → ℂ) y) x‖ ≤ C * p f
  rw [iteratedDeriv_fun_mul ((hbC.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((f.property.1.of_le (by exact_mod_cast le_top)).contDiffAt)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
  have hCp : C * p f =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k i B * p f := by
    unfold C
    rw [Finset.sum_mul]
  rw [Finset.mul_sum, hCp]
  apply Finset.sum_le_sum
  intro i hi
  have hini : n - i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  let j : (_ : ℕ) × Fin 1 := ⟨n - i, 0⟩
  have hj : j ∈ s := Finset.mem_image.mpr ⟨n - i, hini, rfl⟩
  have hle : periodicDerivativeSeminorms d j ≤ p := Finset.le_sup hj
  have hpf : ‖periodicDerivativeLM d (n - i) f‖ ≤ p f := hle f
  have hpv := (iteratedDeriv_le_periodicDerivativeNorm Fact.out f (n - i) x).trans hpf
  have hbv : ‖x‖ ^ k * ‖iteratedDeriv i b x‖ ≤ SchwartzMap.seminorm ℂ k i B := by
    rw [Real.norm_eq_abs]
    exact SchwartzMap.le_seminorm' ℂ k i B x
  simp only [norm_mul, Complex.norm_natCast]
  calc
    _ = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedDeriv i b x‖) *
        ‖iteratedDeriv (n - i) (f : ℝ → ℂ) x‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hbv (Nat.cast_nonneg _)) hpv
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

/-- The localization topology is precisely uniform convergence of all
derivatives on a fundamental interval. -/
theorem smoothPeriodic_topology_eq_derivative (d : ℝ) [Fact (0 < d)] :
    smoothPeriodic_topology d = periodicDerivativeTopology d := by
  apply le_antisymm
  · have h : @Continuous _ _ (smoothPeriodic_topology d) (periodicDerivativeTopology d) id := by
      apply continuous_induced_rng.mpr
      exact continuous_pi fun n => continuous_periodicDerivativeLM d n
    exact continuous_id_iff_le.mp h
  · have h : @Continuous _ _ (periodicDerivativeTopology d) (smoothPeriodic_topology d) id :=
      continuous_induced_rng.mpr (continuous_chart_derivativeTopology d)
    exact continuous_id_iff_le.mp h

end
end Masullo
