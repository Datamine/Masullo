import PeriodicFirstSchwartzCurrying

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo
noncomputable section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {L : AddSubgroup X}

/-- Recover the unlocalized jointly smooth function from the equations in the first variable. -/
theorem firstPeriodicSchwartz_exists_periodic (b : PeriodicLocalization L)
    (f : firstPeriodicSchwartz (Y := Y) b) :
    ∃ u : X × Y → ℂ, ContDiff ℝ ∞ u ∧
      (∀ x y (k : L), u (x + k.val, y) = u (x, y)) ∧
      ∀ x y, f.val (x, y) = b.weight x • u (x, y) := by
  let K := L.map (AddMonoidHom.inl X Y)
  let w : X × Y → ℂ := b.weight ∘ Prod.fst
  have hcov (z : X × Y) : ∃ l : K, w (z + l.val) ≠ 0 := by
    obtain ⟨k, hk⟩ := b.cover z.1
    exact ⟨⟨(k.val, 0), ⟨k.val, k.property, rfl⟩⟩, hk⟩
  have he (z : X × Y) (k : K) :
      w (z + k.val) • f.val z = w z • f.val (z + k.val) := by
    obtain ⟨a, ha, hea⟩ := k.property
    have hek : k.val = (a, 0) := hea.symm
    rw [hek]
    rcases z with ⟨x, y⟩
    rw [Prod.mk_add_mk, add_zero]
    exact f.property y x ⟨a, ha⟩
  obtain ⟨u, hu, hp, hf⟩ := exists_periodic_of_localization_equations w
    (b.smooth.comp contDiff_fst) hcov f.val f.val.smooth' he
  refine ⟨u, hu, ?_, fun x y => hf (x,y)⟩
  intro x y k
  simpa only [Prod.mk_add_mk, add_zero] using hp (x, y) ⟨(k.val, 0), ⟨k.val, k.property, rfl⟩⟩

/-- The original mixed seminorm with a weight in the noncompact variable
is bounded by the corresponding joint Schwartz seminorm after localization. -/
theorem euclideanTorus_firstPeriodic_derivative_le {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d) × Y → ℂ)
    (hp : ∀ x y (k : euclideanIntegerLattice d), u (x + k.val, y) = u (x, y))
    (f : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ))
    (hf : ∀ x y, f (x, y) = (euclideanTorusLocalization d).weight x • u (x, y))
    (k n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (y : Y) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n u (x, y)‖ ≤ SchwartzMap.seminorm ℂ k n f := by
  obtain ⟨j, hj⟩ := euclideanTorusLocalization_eventually_one d x
  have hper : iteratedFDeriv ℝ n u (x + j.val, y) = iteratedFDeriv ℝ n u (x, y) := by
    let z := (j.val, (0 : Y))
    have hh : (fun p => u (p + z)) = u := by
      funext z'
      rcases z' with ⟨p, q⟩
      simpa only [z, Prod.mk_add_mk, add_zero] using hp p q j
    simpa only [z, Prod.mk_add_mk, add_zero, iteratedFDeriv_comp_add_right] using
      congrFun (congrArg (iteratedFDeriv ℝ n) hh) (x, y)
  have hloc : (f : EuclideanSpace ℝ (Fin d) × Y → ℂ) =ᶠ[𝓝 (x + j.val, y)] u := by
    have he : ∀ᶠ p in 𝓝 (x + j.val, y),
        (euclideanTorusLocalization d).weight p.1 = 1 := by
      have hc : Tendsto (Prod.fst : EuclideanSpace ℝ (Fin d) × Y → EuclideanSpace ℝ (Fin d))
          (𝓝 (x + j.val, y)) (𝓝 (x + j.val)) := continuous_fst.continuousAt.tendsto
      exact hc.eventually hj
    filter_upwards [he] with p hp
    rcases p with ⟨a, b⟩
    rw [hf, hp, one_smul]
  rw [← hper, ← (hloc.iteratedFDeriv ℝ n).eq_of_nhds]
  calc
    _ ≤ ‖(x + j.val, y)‖ ^ k * ‖iteratedFDeriv ℝ n f (x + j.val, y)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k
    _ ≤ _ := SchwartzMap.le_seminorm ℂ k n f (x + j.val, y)


/-- The Leibniz estimate for a cutoff depending only on the periodic variable. -/
theorem firstPeriodic_localization_weighted_bound (b : PeriodicLocalization L)
    (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u) (k n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h₀ : ∀ i ≤ n, ∀ z, ‖iteratedFDeriv ℝ i u z‖ ≤ M)
    (hk : ∀ i ≤ n, ∀ z, ‖z.2‖ ^ k * ‖iteratedFDeriv ℝ i u z‖ ≤ M)
    (z : X × Y) :
    ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => b.weight p.1 • u p) z‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i (b.compact.toSchwartzMap b.smooth) +
         SchwartzMap.seminorm ℂ 0 i (b.compact.toSchwartzMap b.smooth))) * M := by
  let w : X × Y → ℂ := b.weight ∘ Prod.fst
  let g := b.compact.toSchwartzMap b.smooth
  have hw : ContDiff ℝ ∞ w := b.smooth.comp contDiff_fst
  have hj (i : ℕ) : ‖iteratedFDeriv ℝ i w z‖ ≤ ‖iteratedFDeriv ℝ i g z.1‖ := by
    let F := ContinuousLinearMap.fst ℝ X Y
    have he := F.iteratedFDeriv_comp_right b.smooth z
      (i := i) (WithTop.coe_le_coe.mpr le_top)
    change iteratedFDeriv ℝ i w z = _ at he
    rw [he]
    have hprod : (∏ _ : Fin i, ‖F‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ X Y)
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hprod)
  have hf (i j : ℕ) :
      ‖z.1‖ ^ j * ‖iteratedFDeriv ℝ i w z‖ ≤ SchwartzMap.seminorm ℂ j i g :=
    (mul_le_mul_of_nonneg_left (hj i) (by positivity)).trans
      (SchwartzMap.le_seminorm ℂ j i g z.1)
  have hft (i : ℕ) : ‖iteratedFDeriv ℝ i w z‖ ≤ SchwartzMap.seminorm ℂ 0 i g :=
    (hj i).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g i z.1)
  have hterm (i : ℕ) :
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ i w z‖ * ‖iteratedFDeriv ℝ (n-i) u z‖ ≤
        (SchwartzMap.seminorm ℂ k i g + SchwartzMap.seminorm ℂ 0 i g) * M := by
    rw [Prod.norm_def]
    rcases le_total ‖z.1‖ ‖z.2‖ with h | h
    · rw [max_eq_right h]
      calc
        _ = ‖iteratedFDeriv ℝ i w z‖ * (‖z.2‖ ^ k * ‖iteratedFDeriv ℝ (n-i) u z‖) := by ring
        _ ≤ SchwartzMap.seminorm ℂ 0 i g * M :=
          mul_le_mul (hft i) (hk _ (Nat.sub_le n i) z) (by positivity) (apply_nonneg _ _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (apply_nonneg _ _)) hM
    · rw [max_eq_left h]
      exact (mul_le_mul (hf i k) (h₀ _ (Nat.sub_le n i) z) (norm_nonneg _) (apply_nonneg _ _)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg _ _)) hM)
  change ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => w p • u p) z‖ ≤ _
  calc
    _ ≤ ‖z‖ ^ k * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i w z‖ * ‖iteratedFDeriv ℝ (n-i) u z‖) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_smul_le hw hu z (WithTop.coe_le_coe.mpr le_top)) (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖z‖ ^ k * ‖iteratedFDeriv ℝ i w z‖ * ‖iteratedFDeriv ℝ (n-i) u z‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hterm i) (Nat.cast_nonneg (n.choose i))

/-- The localized Schwartz seminorm is controlled by finitely many joint
derivatives with weights in the noncompact variable only. -/
theorem firstPeriodicSchwartz_seminorm_le (b : PeriodicLocalization L)
    (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u) (f : 𝓢(X × Y, ℂ))
    (hf : ∀ x y, f (x,y) = b.weight x • u (x,y)) (k n : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (h₀ : ∀ i ≤ n, ∀ z, ‖iteratedFDeriv ℝ i u z‖ ≤ M)
    (hk : ∀ i ≤ n, ∀ z, ‖z.2‖ ^ k * ‖iteratedFDeriv ℝ i u z‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n f ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i (b.compact.toSchwartzMap b.smooth) +
         SchwartzMap.seminorm ℂ 0 i (b.compact.toSchwartzMap b.smooth))) * M := by
  apply SchwartzMap.seminorm_le_bound ℂ k n f
    (mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hM)
  intro z
  have he : (f : X × Y → ℂ) = fun p => b.weight p.1 • u p :=
    funext fun p => hf p.1 p.2
  rw [he]
  exact firstPeriodic_localization_weighted_bound b u hu k n hM h₀ hk z

/-- The usual weighted derivative conditions on the unlocalized mixed
space give a joint Schwartz function after multiplying by the cutoff. -/
theorem exists_firstPeriodicSchwartz_of_weighted_bounds (b : PeriodicLocalization L)
    (u : X × Y → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : ∀ x y (k : L), u (x + k.val,y) = u (x,y))
    (hdec : ∀ k n : ℕ, ∃ M : ℝ, ∀ z, ‖z.2‖ ^ k * ‖iteratedFDeriv ℝ n u z‖ ≤ M) :
    ∃ f : firstPeriodicSchwartz (Y := Y) b, ∀ x y, f.val (x,y) = b.weight x • u (x,y) := by
  classical
  let g : X × Y → ℂ := fun z => b.weight z.1 • u z
  have hg : ContDiff ℝ ∞ g := (b.smooth.comp contDiff_fst).smul hu
  have hd (k n : ℕ) : ∃ C : ℝ, ∀ z, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n g z‖ ≤ C := by
    choose B hB using hdec
    let M := ∑ i ∈ Finset.range (n+1), (max (B 0 i) 0 + max (B k i) 0)
    have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => by positivity)
    have hb (i : ℕ) (hi : i ≤ n) : max (B 0 i) 0 + max (B k i) 0 ≤ M :=
      Finset.single_le_sum (f := fun j => max (B 0 j) 0 + max (B k j) 0)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    refine ⟨_, fun z => firstPeriodic_localization_weighted_bound b u hu k n hM
      (fun i hi z => ?_) (fun i hi z => ?_) z⟩
    · have h := (hB 0 i z).trans (le_max_left (B 0 i) (0 : ℝ))
      rw [pow_zero, one_mul] at h
      exact h.trans ((le_add_of_nonneg_right (le_max_right _ _)).trans (hb i hi))
    · exact (hB k i z).trans ((le_max_left _ _).trans
        ((le_add_of_nonneg_left (le_max_right _ _)).trans (hb i hi)))
  refine ⟨⟨⟨g, hg, hd⟩, ?_⟩, fun _ _ => rfl⟩
  intro y x k
  change b.weight (x + k.val) • (b.weight x • u (x,y)) =
    b.weight x • (b.weight (x + k.val) • u (x + k.val,y))
  rw [hp x y k, smul_comm]


end
end Masullo
