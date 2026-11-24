import ModulatedSobolevGroup
import CompactCharacterCompleteness

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

/-- The singleton Sobolev density is the binomial sum of the moment weights. -/
theorem hardySobolevWeight_even_binomial (b x : ℝ) (N : ℕ) :
    hardySobolevWeight b b (2 * (N : ℝ)) x =
      ∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℝ) * (Real.exp (2 * b * x) * (x ^ 2) ^ k) := by
  have hN : (2 * (N : ℝ)) / 2 = (N : ℝ) := by ring
  have hpow : (1 + x ^ 2) ^ N =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (x ^ 2) ^ k := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one, mul_comm]
  rw [hardySobolevWeight, max_self, hN, Real.rpow_natCast, hpow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable {X : Type*} [MeasurableSpace X]

theorem integrable_hardySobolev_sq_iff (μ : Measure X) {l : X → ℝ} (hl : Measurable l)
    (a b s : ℝ) (f : X → ℂ) :
    Integrable (fun x => ‖f x‖ ^ 2) (hardySobolevMeasure μ l a b s) ↔
    Integrable (fun x => hardySobolevWeight a b s (l x) * ‖f x‖ ^ 2) μ := by
  let W x := hardySobolevWeight a b s (l x)
  have hw : Measurable W := (continuous_hardySobolevWeight a b s).measurable.comp hl
  change Integrable _ (μ.withDensity (fun x => ENNReal.ofReal (W x))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hardySobolevWeight_nonneg ..), W, smul_eq_mul]

/-- The squared norms in (9.2.1.19) give the Hilbert norm by a binomial sum.
Every individual logarithmic moment is integrable in the energy formula. -/
theorem hardySobolev_even_norm_sq (μ : Measure X) {l : X → ℝ} (hl : Measurable l)
    (b : ℝ) (N : ℕ) {f : X → ℂ} (hf : MemLp f 2 (hardySobolevMeasure μ l b b (2 * (N : ℝ)))) :
    let moment (k : ℕ) x :=
      ‖f x‖ ^ 2 * (Real.exp (2 * b * l x) * (l x ^ 2) ^ k)
    (∀ k ≤ N, Integrable (moment k) μ) ∧
    ‖hf.toLp f‖ ^ 2 = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * ∫ x, moment k x ∂μ := by
  intro moment
  let W x := hardySobolevWeight b b (2 * (N : ℝ)) (l x)
  let ρ : X → ℝ≥0∞ := fun x => ENNReal.ofReal (W x)
  have hW : Measurable W := (continuous_hardySobolevWeight b b (2 * (N : ℝ))).measurable.comp hl
  have hi := (integrable_hardySobolev_sq_iff μ hl b b (2 * (N : ℝ)) f).mp ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  have he (x : X) : W x * ‖f x‖ ^ 2 =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * moment k x := by
    dsimp [W]
    rw [hardySobolevWeight_even_binomial, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by dsimp [moment]; ring
  have hn (k : ℕ) (x : X) : 0 ≤ moment k x := by
    dsimp [moment]
    positivity
  have hmeas : AEStronglyMeasurable f μ := by
    apply (hf.aestronglyMeasurable).mono_ac
    apply withDensity_absolutelyContinuous' hW.ennreal_ofReal.aemeasurable
    exact Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (by
      dsimp [W, hardySobolevWeight]
      positivity)
  have hm (k : ℕ) (hk : k ≤ N) : Integrable (moment k) μ := by
    apply hi.mono'
    · exact (hmeas.norm.pow 2).mul ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).measurable.comp hl |>.aestronglyMeasurable.mul
        (hl.aestronglyMeasurable.pow 2 |>.pow k))
    · apply Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (hn k x), he]
      refine le_trans ?_ (Finset.single_le_sum (fun j _ =>
        mul_nonneg (by positivity) (hn j x)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
      have hchoose : (1 : ℝ) ≤ N.choose k := by exact_mod_cast Nat.choose_pos hk
      exact le_mul_of_one_le_left (hn k x) hchoose
  refine ⟨hm, ?_⟩
  rw [norm_sq_toLp_two hf]
  change (∫ x, ‖f x‖ ^ 2 ∂μ.withDensity ρ) = _
  rw [integral_withDensity_eq_integral_toReal_smul hW.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hardySobolevWeight_nonneg ..), W, smul_eq_mul]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · exact integral_congr_ae (Eventually.of_forall he)
  · intro k hk
    exact (hm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).const_mul _

section Group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (μ : Measure m.toMonoidHom.ker) [SFinite μ]

/-- The weighted group norm is the binomial combination of the manuscript's
logarithmic moment norms. -/
theorem modulatedSobolevGroup_norm_sq (b : ℝ) (N : ℕ)
    (u : Lp ℂ 2 (modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ)))) :
    let Haar := modulatedLogMeasure m τ hτ μ
    let moment (k : ℕ) g :=
      ‖u g‖ ^ 2 * (Real.exp (2 * b * modulatedLog m g) * (modulatedLog m g ^ 2) ^ k)
    (∀ k ≤ N, Integrable (moment k) Haar) ∧
    ‖u‖ ^ 2 = ∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) * ∫ g, moment k g ∂Haar := by
  intro Haar moment
  generalize he : modulatedSobolevMeasure m τ hτ μ b (2 * (N : ℝ)) = v at u
  rw [modulatedSobolevMeasure_eq_weighted] at he
  subst v
  have h := hardySobolev_even_norm_sq Haar (l := modulatedLog m)
    (continuous_toAdd.comp m.continuous).measurable b N (Lp.memLp u)
  simpa only [Lp.toLp_coeFn] using h

end Group

end
end Masullo
