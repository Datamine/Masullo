import MellinStrip
import SpectralLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.LocallyFinite

open Filter Function MeasureTheory Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

private theorem entire_nonzero_on_vertical_interval {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h₀ : F 0 ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, F ((y : ℂ) * Complex.I) ≠ 0 := by
  by_contra! hz
  let t : ℝ := (a + b) / 2
  let g (z : ℂ) := F (z * Complex.I)
  have hg : Differentiable ℂ g := hF.comp (differentiable_id.mul_const Complex.I)
  have hcoe : Continuous (fun y : ℝ => (y : ℂ)) := Complex.continuous_ofReal
  have hc : (t : ℂ) ∈ closure ((fun y : ℝ => (y : ℂ)) '' (Ioo a b \ {t})) := by
    apply image_closure_subset_closure_image hcoe
    refine ⟨t, ?_, rfl⟩
    have ht : t ∈ Ioo a b := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
    apply mem_closure_ne_iff_frequently_within.mpr
    have hn : ∀ᶠ y in 𝓝[≠] t, y ∈ Ioo a b :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
    exact hn.frequently
  have hset : (fun y : ℝ => (y : ℂ)) '' (Ioo a b \ {t}) ⊆
      {z : ℂ | g z = (0 : ℂ)} \ {(t : ℂ)} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hz y hy.1, ?_⟩
    intro h
    exact hy.2 (Complex.ofReal_injective (mem_singleton_iff.mp h))
  have hga : AnalyticOnNhd ℂ g univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have he := hga.eqOn_of_preconnected_of_mem_closure
    analyticOnNhd_const isPreconnected_univ (mem_univ (t : ℂ)) (closure_mono hset hc)
  exact h₀ (by simpa [g] using he (mem_univ (0 : ℂ)))

/-- A continuous transform that is nonzero somewhere in every height interval
admits a closed discrete set of heights on which the absolute sum diverges. -/
theorem exists_closedDiscrete_not_summable {g : ℝ → ℝ} (hg : Continuous g)
    (hnz : ∀ n : ℕ, ∃ y ∈ Ioo (n : ℝ) (n + 1), 0 < g y) :
    ∃ Z : Set ℝ, IsClosed Z ∧ IsDiscrete Z ∧
      (∀ y ∈ Z, 0 < g y) ∧ ¬ Summable (fun z : Z => g z.val) := by
  classical
  choose y hy hgy using hnz
  have hopen (n : ℕ) : IsOpen (Ioo (n : ℝ) (n + 1) ∩
      g ⁻¹' Ioi (g (y n) / 2)) := isOpen_Ioo.inter (hg.isOpen_preimage _ isOpen_Ioi)
  have hcontains (n : ℕ) : y n ∈ Ioo (n : ℝ) (n + 1) ∩ g ⁻¹' Ioi (g (y n) / 2) :=
    ⟨hy n, by change g (y n) / 2 < g (y n); linarith [hgy n]⟩
  have hball (n : ℕ) : ∃ r : ℝ, 0 < r ∧ Metric.ball (y n) r ⊆
      Ioo (n : ℝ) (n + 1) ∩ g ⁻¹' Ioi (g (y n) / 2) :=
    Metric.isOpen_iff.mp (hopen n) (y n) (hcontains n)
  choose r hr hball using hball
  have hcounts (n : ℕ) : ∃ k : ℕ, (g (y n) / 2)⁻¹ < k := exists_nat_gt _
  choose k hk using hcounts
  let point (n : ℕ) (j : Fin (k n)) : ℝ := y n + (j.val : ℝ) / ((k n : ℝ) + 1) * r n
  have hp (n : ℕ) (j : Fin (k n)) :
      point n j ∈ Ioo (n : ℝ) (n + 1) ∩ g ⁻¹' Ioi (g (y n) / 2) := by
    apply hball n
    rw [Metric.mem_ball, Real.dist_eq, show point n j - y n =
      (j.val : ℝ) / ((k n : ℝ) + 1) * r n by dsimp [point]; ring, abs_of_nonneg (by positivity [hr n])]
    apply mul_lt_of_lt_one_left (hr n)
    apply (div_lt_one (by positivity : 0 < (k n : ℝ) + 1)).mpr
    exact (Nat.cast_lt.mpr j.isLt).trans (lt_add_one _)
  have hpinj (n : ℕ) : Injective (point n) := by
    intro i j h
    apply Fin.ext
    have he := mul_right_cancel₀ (hr n).ne' (add_left_cancel h)
    exact_mod_cast (div_left_inj' (by positivity : (k n : ℝ) + 1 ≠ 0)).mp he
  let Z := ⋃ n, range (point n)
  have hfinite : LocallyFinite (fun n => range (point n)) := by
    intro x
    refine ⟨Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (x + 1)
    refine (finite_lt_nat N).subset ?_
    intro n hn
    obtain ⟨w, ⟨i, rfl⟩, hw⟩ := hn
    exact Nat.cast_lt.mp (((hp n i).1.1.trans hw).trans hN)
  have hclosed_subset (S : Set ℝ) (hS : S ⊆ Z) : IsClosed S := by
    have he : S = ⋃ n, S ∩ range (point n) := by
      rw [← inter_iUnion, inter_eq_left.mpr hS]
    rw [he]
    exact (hfinite.subset fun n => inter_subset_right).isClosed_iUnion fun n =>
      ((finite_range (point n)).subset inter_subset_right).isClosed
  have hpos (z : Z) : 0 < g z := by
    obtain ⟨n, ⟨i, hi⟩⟩ := mem_iUnion.mp z.property
    have h := (hp n i).2
    change g (y n) / 2 < g (point n i) at h
    rw [hi] at h
    linarith [hgy n]
  refine ⟨Z, hclosed_subset Z (Subset.rfl), isDiscrete_iff_forall_mem_exists_isClosed.mpr
    (fun S hS => ⟨S, hclosed_subset S hS, inter_eq_left.mpr hS⟩), fun z hz => hpos ⟨z, hz⟩, ?_⟩
  let e (i : Σ n, Fin (k n)) : Z := ⟨point i.1 i.2, mem_iUnion.mpr ⟨i.1, mem_range_self _⟩⟩
  have he : Injective e := by
    rintro ⟨n, i⟩ ⟨m, j⟩ h
    have hpEq : point n i = point m j := congrArg Subtype.val h
    have hnm : n = m := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
        exact ((hp n i).1.2.trans_le hcast).not_ge (hpEq ▸ (hp m j).1.1).le
      · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
        exact ((hp m j).1.2.trans_le hcast).not_ge (hpEq.symm ▸ (hp n i).1.1).le
    subst m
    exact congrArg (Sigma.mk n) (hpinj n hpEq)
  intro hs
  have hsum := (summable_sigma_of_nonneg (fun i => (hpos (e i)).le)).mp (hs.comp_injective he)
  have hbound (n : ℕ) : 1 ≤ ∑' i : Fin (k n), g (point n i) := by
    rw [tsum_fintype]
    have hposn : 0 < g (y n) / 2 := by positivity [hgy n]
    have hk' := (inv_lt_iff_one_lt_mul₀ hposn).mp (hk n)
    calc
      1 ≤ (k n : ℝ) * (g (y n) / 2) := by linarith
      _ = ∑ _i : Fin (k n), g (y n) / 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => (show g (y n) / 2 < g (point n i) from (hp n i).2).le
  have hc : Summable (fun _ : ℕ => (1 : ℝ)) :=
    hsum.2.of_nonneg_of_le (fun _ => zero_le_one) hbound
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc.tendsto_atTop_zero)

set_option maxHeartbeats 900000 in
/-- The printed absolute convergence in B.4.4.8 fails already for the
positive-real group, with a single vertical line of characters. -/
theorem mellin_closedDiscrete_absoluteSum_counterexample :
    ∃ p : ℝ → ℂ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      ∃ Z : Set ℝ, IsClosed Z ∧ IsDiscrete Z ∧
        ¬ Summable (fun y : Z => ‖mellin (fun t => p (Real.log t))
          ((y.val : ℂ) * Complex.I)‖) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let p : ℝ → ℂ := fun x => (b x : ℂ)
  let f (t : ℝ) := p (Real.log t)
  have hp : ContDiff ℝ ∞ p := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hpc : HasCompactSupport p := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hw (σ : ℝ) : MellinSchwartzAt f σ := by
    apply mellinSchwartzAt_iff_positive_log.mpr
    let H : ℝ → ℂ := fun x => Real.exp (σ * x) • p x
    have hc : HasCompactSupport H := by
      change HasCompactSupport ((fun x : ℝ => Real.exp (σ * x)) • p)
      exact hpc.smul_left
    have he : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (σ * x)) := by fun_prop
    refine ⟨hc.toSchwartzMap (he.smul hp), funext fun x => ?_⟩
    change H x = _
    simp [H, f, Real.log_exp]
  let F := mellin f
  have hF : Differentiable ℂ F := (mellin_exponential_decay hw).2.1
  have h₀ : F 0 ≠ 0 := by
    change mellin f 0 ≠ 0
    rw [mellin_eq_log_integral]
    simp only [zero_mul, Complex.exp_zero, one_mul, f, Real.log_exp]
    change (∫ x : ℝ, (b x : ℂ)) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      b.hasCompactSupport (fun _ => b.nonneg) (x := 0) (by
        rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
        exact one_ne_zero)).ne'
  have hnz (n : ℕ) : ∃ y ∈ Ioo (n : ℝ) (n + 1), 0 < ‖F ((y : ℂ) * Complex.I)‖ := by
    obtain ⟨y, hy, hn⟩ := entire_nonzero_on_vertical_interval hF h₀
      (a := n) (b := (n : ℝ) + 1) (lt_add_one _)
    exact ⟨y, hy, norm_pos_iff.mpr hn⟩
  have hcont : Continuous (fun y : ℝ => ‖F ((y : ℂ) * Complex.I)‖) :=
    (hF.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).norm
  obtain ⟨Z, hc, hd, _, hsum⟩ := exists_closedDiscrete_not_summable hcont hnz
  exact ⟨p, hp, hpc, Z, hc, hd, hsum⟩


/-- A bounded vertical strip and a dyadic count of order T log T suffice for
absolute Mellin summability on the positive-real factor, with multiplicities. -/
theorem mellin_absoluteSum_of_dyadic_count
    {Shell : ℕ → Type*} [∀ n, Fintype (Shell n)]
    {f : ℝ → ℂ} (hf : ∀ σ : ℝ, MellinSchwartzAt f σ)
    (z : (Σ n, Shell n) → ℂ) (w : (Σ n, Shell n) → ℕ)
    {a b C : ℝ} (hab : a < b) (hstrip : ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b)
    (hlower : ∀ n (i : Shell n), (2 : ℝ) ^ n ≤ max 1 |(z ⟨n, i⟩).im|)
    (hcount : ∀ n, (∑ i : Shell n, (w ⟨n, i⟩ : ℝ)) ≤ C * ((n : ℝ) + 1) * 2 ^ n) :
    Summable (fun i => (w i : ℝ) * ‖mellin f (z i)‖) := by
  obtain ⟨C₀, hC₀, h₀, _⟩ := (mellin_exponential_decay hf).2.2.1 a b hab 0
  obtain ⟨C₂, hC₂, h₂, _⟩ := (mellin_exponential_decay hf).2.2.1 a b hab 2
  have hsum := (dyadic_zero_count_summable (fun i => (z i).im) w hlower hcount).mul_left (C₀ + C₂)
  apply hsum.of_nonneg_of_le (fun _ => by positivity)
  intro i
  have h₁i : ‖mellin f (z i)‖ ≤ C₀ := by
    simpa only [pow_zero, one_mul] using h₀ (z i) (hstrip i).1 (hstrip i).2
  have h₂i : (z i).im ^ 2 * ‖mellin f (z i)‖ ≤ C₂ := by
    simpa only [sq_abs] using h₂ (z i) (hstrip i).1 (hstrip i).2
  have hM : ‖mellin f (z i)‖ ≤ (C₀ + C₂) / (1 + (z i).im ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_add, mul_one, mul_comm ‖mellin f (z i)‖]
    exact add_le_add h₁i h₂i
  calc
    _ ≤ (w i : ℝ) * ((C₀ + C₂) / (1 + (z i).im ^ 2)) :=
      mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg (w i))
    _ = _ := by ring

end
end Masullo
