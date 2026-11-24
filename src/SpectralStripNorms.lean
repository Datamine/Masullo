import OrbitalSobolevNorms
import HardySobolevEvaluation

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1000000

private abbrev density (α s b : ℝ) (m : ℕ) :=
  evaluationDensity (-α) α s m (b : ℂ)

private theorem density_continuous (α s b : ℝ) (m : ℕ) :
    Continuous (density α s b m) := by
  unfold density evaluationDensity
  have hk : Continuous (mellinEvaluationKernel m (b : ℂ)) := by
    unfold mellinEvaluationKernel
    fun_prop
  exact ((stripSobolevAmplitude_continuous (- -α) (-α) (-s)).smul hk).norm.pow 2

private theorem density_nonneg (α s b : ℝ) (m : ℕ) (x : ℝ) :
    0 ≤ density α s b m x := sq_nonneg _

private theorem density_le_at_extremes (α s : ℝ) (m : ℕ) {l b r : ℝ}
    (hl : l ≤ b) (hr : b ≤ r) (x : ℝ) :
    density α s b m x ≤ density α s l m x + density α s r m x := by
  have hpoly : 0 ≤ x ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2) := by
    rw [pow_mul]
    positivity
  by_cases hx : x ≤ 0
  · have hleft : density α s b m x ≤ density α s l m x := by
      simp only [evaluationDensity_eq, Complex.ofReal_re, ite_eq_left hx]
      apply mul_le_mul_of_nonneg_right _ hpoly
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) hx)
    exact hleft.trans (le_add_of_nonneg_right (density_nonneg α s r m x))
  · have hright : density α s b m x ≤ density α s r m x := by
      simp only [evaluationDensity_eq, Complex.ofReal_re, ite_eq_right hx]
      apply mul_le_mul_of_nonneg_right _ hpoly
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (le_of_not_ge hx))
    exact hright.trans (le_add_of_nonneg_left (density_nonneg α s l m x))

private def bandDensity (α s k : ℝ) :=
  (Ioo k (k + 1)).indicator (density α s (-α) 0)

private theorem density_lower_on_band (α s : ℝ) {k b : ℝ} (hk : 1 ≤ k) (hb : -α ≤ b)
    (m : ℕ) (x : ℝ) :
    k ^ (2 * m) * bandDensity α s k x ≤ density α s b m x := by
  unfold bandDensity
  by_cases hx : x ∈ Ioo k (k + 1)
  · have hx₀ : 0 < x := (zero_lt_one.trans_le hk).trans hx.1
    rw [indicator_of_mem hx]
    simp only [evaluationDensity_eq, Complex.ofReal_re, ite_eq_right hx₀.not_ge,
      Nat.mul_zero, pow_zero, one_mul]
    have hp : 0 ≤ (1 + x ^ 2) ^ (-s / 2) := by positivity
    calc
      _ = Real.exp (2 * (-α - α) * x) * (k ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2)) := by ring
      _ ≤ Real.exp (2 * (b - α) * x) * (k ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2)) := by
        have hk' : 0 ≤ k := zero_le_one.trans hk
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg hk' _) hp)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx₀.le)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (zero_le_one.trans hk) hx.1.le _) hp
  · rw [indicator_of_notMem hx, mul_zero]
    exact density_nonneg α s b m x

private theorem bandDensity_integrable (α s k : ℝ) :
    Integrable (bandDensity α s k) :=
  (((density_continuous α s (-α) 0).continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

private theorem density_band_integral_pos (α s k : ℝ) :
    0 < ∫ x, bandDensity α s k x := by
  apply (integral_pos_iff_support_of_nonneg
    (indicator_nonneg (fun y _ => density_nonneg α s (-α) 0 y))
    (bandDensity_integrable α s k)).mpr
  have hs : Ioo k (k + 1) ⊆ support (bandDensity α s k) := by
    intro x hx
    change bandDensity α s k x ≠ 0
    unfold bandDensity
    rw [indicator_of_mem hx]
    unfold density
    rw [evaluationDensity_eq]
    simp only [Nat.mul_zero, pow_zero, one_mul]
    exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)).ne'
  exact (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr (by linarith))).trans_le (measure_mono hs)

private theorem radial_strip_energy_bounded_at_limit {α s b A : ℝ} (m : ℕ)
    (r : ℕ → ℝ) (hlim : Tendsto r atTop (𝓝 b))
    (hi : ∀ n, Integrable (density α s (r n) m))
    (hbound : ∀ n, (∫ x, density α s (r n) m x) ≤ A) :
    Integrable (density α s b m) ∧ (∫ x, density α s b m x) ≤ A := by
  let f (n : ℕ) (x : ℝ) := ENNReal.ofReal (density α s (r n) m x)
  let g (x : ℝ) := ENNReal.ofReal (density α s b m x)
  have hf : ∀ n, Measurable (f n) :=
    fun n => (density_continuous α s (r n) m).measurable.ennreal_ofReal
  have hg (x : ℝ) : Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have hcx : Continuous (fun c : ℝ => ENNReal.ofReal (density α s c m x)) := by
      simp only [density, evaluationDensity_eq, Complex.ofReal_re]
      exact ENNReal.continuous_ofReal.comp
        ((Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const) |>.mul continuous_const)).mul continuous_const)
    exact (hcx.continuousAt (x := b)).tendsto.comp hlim
  have hm : ∀ n, (∫⁻ x, f n x) ≤ ENNReal.ofReal A := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n)
      (Eventually.of_forall (density_nonneg α s (r n) m))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have ht : (∫⁻ x, g x) ≤ ENNReal.ofReal A := by
    calc
      _ = ∫⁻ x, liminf (fun n => f n x) atTop :=
        lintegral_congr fun x => (hg x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, f n x) atTop := lintegral_liminf_le hf
      _ ≤ _ := by
        simpa only [liminf_const] using
          (liminf_le_liminf (Eventually.of_forall hm) :
            liminf (fun n => ∫⁻ x, f n x) atTop ≤ liminf (fun _ => ENNReal.ofReal A) atTop)
  have hi' := (lintegral_ofReal_ne_top_iff_integrable (density_continuous α s b m).aestronglyMeasurable
    (Eventually.of_forall (density_nonneg α s b m))).mp
      ((ht.trans_lt ENNReal.ofReal_lt_top).ne)
  refine ⟨hi', (ENNReal.ofReal_le_ofReal_iff (le_trans
    (integral_nonneg (density_nonneg α s (r 0) m)) (hbound 0))).mp ?_⟩
  rwa [ofReal_integral_eq_lintegral_ofReal hi' (Eventually.of_forall (density_nonneg α s b m))]

private theorem radialStripBounded_parameters {α s A : ℝ} (hs : 0 ≤ s)
    (J : Set (ℝ × ℕ))
    (hJ : ∀ p ∈ J, p.1 ∈ Icc (-α) α ∧ Integrable (density α s p.1 p.2) ∧
      (∫ x, density α s p.1 p.2 x) ≤ A) :
    ∃ (orders : Finset ℕ) (radius : ℕ → ℝ),
      (∀ m ∈ orders, radius m ∈ Icc 0 α ∧
        (radius m < α ∨ (m : ℝ) < (s - 1) / 2)) ∧
      ∀ p ∈ J, p.2 ∈ orders ∧ |p.1| ≤ radius p.2 := by
  let E := ∫ x, bandDensity α s 2 x
  have hE : 0 < E := density_band_integral_pos α s 2
  have hpow : Tendsto (fun m : ℕ => (4 : ℝ) ^ m * E) atTop atTop :=
    Tendsto.atTop_mul_const hE (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpow.eventually_gt_atTop A)
  have horder (p : ℝ × ℕ) (hp : p ∈ J) : p.2 < N := by
    have hlow : (4 : ℝ) ^ p.2 * E ≤ ∫ x, density α s p.1 p.2 x := by
      rw [show (4 : ℝ) ^ p.2 = 2 ^ (2 * p.2) by rw [pow_mul]; norm_num]
      dsimp only [E]
      rw [← integral_const_mul]
      exact integral_mono ((bandDensity_integrable α s 2).const_mul _) (hJ p hp).2.1
        (density_lower_on_band α s (by norm_num : (1 : ℝ) ≤ 2) (hJ p hp).1.1 p.2)
    by_contra! hge
    exact (not_lt_of_ge (hlow.trans (hJ p hp).2.2)) (hN p.2 hge)
  let orders := (Finset.range N).filter (fun m => ∃ b : ℝ, (b, m) ∈ J)
  have hRad (m : ℕ) (hm : m ∈ orders) :
      ∃ r ∈ Icc (0 : ℝ) α, (r < α ∨ (m : ℝ) < (s - 1) / 2) ∧
        ∀ b : ℝ, (b, m) ∈ J → |b| ≤ r := by
    let S := {b : ℝ | b ∈ Icc (-α) α ∧ Integrable (density α s b m) ∧
      (∫ x, density α s b m x) ≤ A}
    have hcl : IsClosed S := IsSeqClosed.isClosed (by
      intro u b hu hb
      change b ∈ Icc (-α) α ∧ Integrable (density α s b m) ∧
        (∫ x, density α s b m x) ≤ A
      exact ⟨isClosed_Icc.isSeqClosed (fun n => (hu n).1) hb,
        radial_strip_energy_bounded_at_limit m u hb (fun n => (hu n).2.1)
          (fun n => (hu n).2.2)⟩)
    have hS : IsCompact S := isCompact_Icc.of_isClosed_subset hcl (fun _ h => h.1)
    obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hm).2
    obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨b, hJ (b, m) hb⟩ continuous_abs.continuousOn
    have hza : |z| ≤ α := abs_le.mpr hz.1
    refine ⟨|z|, ⟨abs_nonneg _, hza⟩, ?_, fun x hx => hmax (hJ (x, m) hx)⟩
    by_cases hlt : |z| < α
    · exact Or.inl hlt
    · right
      have h := (evaluationDensity_integrable_iff (a := -α) (b := α) (z := (z : ℂ))
        (by simpa only [Complex.ofReal_re] using hz.1.1)
        (by simpa only [Complex.ofReal_re] using hz.1.2) hs m).mp hz.2.1
      rcases h with h | h
      · exfalso
        exact hlt (abs_lt.mpr (by simpa only [Complex.ofReal_re] using h))
      · linarith
  let radius (m : ℕ) := if hm : m ∈ orders then (hRad m hm).choose else 0
  have hr (m : ℕ) (hm : m ∈ orders) := (hRad m hm).choose_spec
  refine ⟨orders, radius, fun m hm => ?_, fun p hp => ?_⟩
  · simpa only [radius, dite_eq_left hm] using ⟨(hr m hm).1, (hr m hm).2.1⟩
  · have hm : p.2 ∈ orders := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (horder p hp), ⟨p.1, hp⟩⟩
    refine ⟨hm, ?_⟩
    simpa only [radius, dite_eq_left hm] using (hr p.2 hm).2.2 p.1 hp

variable (F : Type*) [Field F] [NumberField F]

private abbrev ClassGroupType := IdeleClass F
private abbrev radial (g : ClassGroupType F) : ℝ := (ideleClassLogNorm F g).toAdd

/-- The vector in (10.2.2.7) in reciprocal-weight Hilbert coordinates. -/
def spectralStripMoment (χ : PontryaginDual (ClassGroupType F)) (α s : ℝ)
    (z : ℂ) (m : ℕ) (g : ClassGroupType F) : ℂ :=
  stripSobolevAmplitude α (-α) (-s) (radial F g) •
    ((χ g : ℂ) * mellinEvaluationKernel m z (radial F g))

private theorem spectralStripMoment_continuous (χ : PontryaginDual (ClassGroupType F))
    (α s : ℝ) (z : ℂ) (m : ℕ) : Continuous (spectralStripMoment F χ α s z m) := by
  have hc : Continuous (radial F) := ideleClassLogNorm_continuous F
  apply ((stripSobolevAmplitude_continuous α (-α) (-s)).comp hc).smul
  apply (continuous_subtype_val.comp χ.continuous).mul
  exact (show Continuous (mellinEvaluationKernel m z) by unfold mellinEvaluationKernel; fun_prop).comp hc

private theorem spectralStripMoment_norm_sq (χ : PontryaginDual (ClassGroupType F))
    (α s b t : ℝ) (m : ℕ) (g : ClassGroupType F) :
    ‖spectralStripMoment F χ α s ((b : ℂ) + (t : ℂ) * Complex.I) m g‖ ^ 2 =
      density α s b m (radial F g) := by
  have he : ((b : ℂ) + (t : ℂ) * Complex.I).re = b := by simp [Complex.add_re, Complex.mul_re]
  unfold spectralStripMoment density
  calc
    _ = evaluationDensity (-α) α s m ((b : ℂ) + (t : ℂ) * Complex.I) (radial F g) := by
      unfold evaluationDensity
      simp only [norm_smul, norm_mul, Circle.norm_coe, one_mul, neg_neg]
    _ = _ := by rw [evaluationDensity_eq, evaluationDensity_eq, he, Complex.ofReal_re]

local instance spectralStripClassMeasurable : MeasurableSpace (ClassGroupType F) := borel _
local instance spectralStripClassBorel : BorelSpace (ClassGroupType F) := ⟨rfl⟩

variable (μ : Measure (ClassGroupType F)) [μ.IsHaarMeasure]

omit [μ.IsHaarMeasure] in
private theorem spectralStripMoment_memLp_and_energy
    (χ : PontryaginDual (ClassGroupType F)) (α s b t : ℝ) (m : ℕ)
    {c : ℝ≥0} (hc : 0 < c) (hmap : μ.map (radial F) = c • volume)
    (hi : Integrable (density α s b m)) :
    ∃ hLp : MemLp (spectralStripMoment F χ α s ((b : ℂ) + (t : ℂ) * Complex.I) m) 2 μ,
      ‖hLp.toLp _‖ ^ 2 = (c : ℝ) * ∫ x, density α s b m x := by
  have hl : Measurable (radial F) :=
    (show Continuous (radial F) from ideleClassLogNorm_continuous F).measurable
  have hd : AEStronglyMeasurable (density α s b m) (μ.map (radial F)) :=
    (density_continuous α s b m).measurable.aestronglyMeasurable
  have hj : Integrable (density α s b m) (μ.map (radial F)) := by
    rw [hmap]
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mpr hi
  have hk := (integrable_map_measure hd hl.aemeasurable).mp hj
  have hLp : MemLp (spectralStripMoment F χ α s ((b : ℂ) + (t : ℂ) * Complex.I) m) 2 μ :=
    (memLp_two_iff_integrable_sq_norm
    (spectralStripMoment_continuous F χ α s _ m).aestronglyMeasurable).mpr
    (by simpa only [spectralStripMoment_norm_sq, Function.comp_def] using hk)
  refine ⟨hLp, ?_⟩
  rw [norm_sq_toLp_two hLp]
  simp only [spectralStripMoment_norm_sq]
  rw [← integral_map hl.aemeasurable hd, hmap, integral_smul_nnreal_measure]
  rfl

/-- Interior Mellin moments of any order are square integrable. At either
strip endpoint the strict Sobolev cutoff is necessary and sufficient. -/
theorem spectralStripMoment_memLp_iff
    (χ : PontryaginDual (ClassGroupType F)) {α s b : ℝ} (hs : 0 ≤ s)
    (hb : b ∈ Icc (-α) α) (t : ℝ) (m : ℕ) :
    MemLp (spectralStripMoment F χ α s ((b : ℂ) + (t : ℂ) * Complex.I) m) 2 μ ↔
      b ∈ Ioo (-α) α ∨ (m : ℝ) < (s - 1) / 2 := by
  obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
  have hl : Measurable (radial F) :=
    (show Continuous (radial F) from ideleClassLogNorm_continuous F).measurable
  have hd : AEStronglyMeasurable (density α s b m) (μ.map (radial F)) :=
    (density_continuous α s b m).measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm
    (spectralStripMoment_continuous F χ α s _ m).aestronglyMeasurable]
  simp only [spectralStripMoment_norm_sq]
  change Integrable (density α s b m ∘ radial F) μ ↔ _
  rw [← integrable_map_measure hd hl.aemeasurable, hmap]
  have hscale : Integrable (density α s b m) (c • volume) ↔ Integrable (density α s b m) volume :=
    integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top
  rw [hscale]
  have he := evaluationDensity_integrable_iff (z := (b : ℂ))
    (a := -α) (b := α) (by simpa using hb.1) (by simpa using hb.2) hs m
  simpa only [Complex.ofReal_re, mem_Ioo, show 2 * (m : ℝ) + 1 < s ↔
    (m : ℝ) < (s - 1) / 2 by constructor <;> intro h <;> linarith] using he

/-- Any family at a fixed order above the endpoint cutoff loses its uniform
upper norm bound if its abscissae approach either strip boundary. This
applies regardless of the character and the imaginary frequency. -/
theorem spectralStripMoments_unbounded_at_endpoint {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {m : ℕ} (hm : (s - 1) / 2 ≤ (m : ℝ)) (hb : b = -α ∨ b = α)
    (r t : ℕ → ℝ) (χ : ℕ → PontryaginDual (ClassGroupType F))
    (hlim : Tendsto r atTop (𝓝 b)) (hr : ∀ n, r n ∈ Ioo (-α) α) :
    ¬ ∃ C : ℝ, ∀ n,
      ∃ hLp : MemLp (spectralStripMoment F (χ n) α s ((r n : ℂ) + (t n : ℂ) * Complex.I) m)
        2 μ, ‖hLp.toLp _‖ ≤ C := by
  obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
  have hi (n : ℕ) : Integrable (density α s (r n) m) :=
    (evaluationDensity_integrable_iff (a := -α) (b := α) (z := (r n : ℂ))
      (by simpa only [Complex.ofReal_re] using (hr n).1.le)
      (by simpa only [Complex.ofReal_re] using (hr n).2.le) hs m).mpr
      (Or.inl (by simpa only [Complex.ofReal_re, mem_Ioo] using hr n))
  rintro ⟨C, hC⟩
  have hc' : 0 < (c : ℝ) := NNReal.coe_pos.mpr hc
  have hbound (n : ℕ) : (∫ x, density α s (r n) m x) ≤ C ^ 2 / (c : ℝ) := by
    obtain ⟨hLp, hn⟩ := hC n
    obtain ⟨_, he⟩ := spectralStripMoment_memLp_and_energy F μ (χ n) α s
      (r n) (t n) m hc hmap (hi n)
    apply (le_div_iff₀ hc').mpr
    rw [mul_comm, ← he]
    gcongr
  have hI := (radial_strip_energy_bounded_at_limit m r hlim hi hbound).1
  have hb' : b ∈ Icc (-α) α := by rcases hb with (rfl | rfl) <;> constructor <;> linarith
  have h := (evaluationDensity_integrable_iff (a := -α) (b := α) (z := (b : ℂ))
    (by simpa only [Complex.ofReal_re] using hb'.1)
    (by simpa only [Complex.ofReal_re] using hb'.2) hs m).mp hI
  rcases h with h | h
  · simp only [Complex.ofReal_re] at h
    rcases hb with (rfl | rfl) <;> linarith [h.1, h.2]
  · linarith

/-- At exponent three, the first moment is unbounded along this explicit
sequence of interior abscissae approaching the upper edge. -/
theorem spectralStripMoments_first_order_unbounded :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ∃ hLp : MemLp
      (spectralStripMoment F 1 1 3
        (((1 - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) + (n : ℂ) * Complex.I) 1) 2 μ,
      ‖hLp.toLp _‖ ≤ C := by
  let r (n : ℕ) : ℝ := 1 - ((n : ℝ) + 1)⁻¹
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hr : Tendsto r atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  have hb (n : ℕ) : r n ∈ Ioo (-1 : ℝ) 1 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hpos : 0 < (n : ℝ) + 1 := zero_lt_one.trans_le hn
    have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
    exact ⟨by dsimp [r]; linarith, by dsimp [r]; linarith [inv_pos.mpr hpos]⟩
  exact spectralStripMoments_unbounded_at_endpoint F μ (α := 1) (s := 3)
    (by norm_num) (by norm_num) (m := 1) (by norm_num) (Or.inr rfl)
    r (fun n => n) (fun _ => 1) hr hb

/-- One annulus works for the entire collection of chosen orders and radii.
Orders at the strict endpoint threshold may range over the full strip.
Higher orders may range over any closed substrip of the interior. -/
theorem spectralStripMoments_uniform_norm {α s : ℝ} (hs : 1 < s)
    (orders : Finset ℕ) (radius : ℕ → ℝ)
    (hr : ∀ m ∈ orders, radius m ∈ Icc 0 α ∧
      (radius m < α ∨ (m : ℝ) < (s - 1) / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : PontryaginDual (ClassGroupType F)) (m : ℕ),
      m ∈ orders → ∀ b t : ℝ, |b| ≤ radius m →
      ∃ hLp : MemLp (spectralStripMoment F χ α s ((b : ℂ) + (t : ℂ) * Complex.I) m) 2 μ,
        C⁻¹ ≤ ‖hLp.toLp _‖ ∧ ‖hLp.toLp _‖ ≤ C := by
  obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
  let B (m : ℕ) (x : ℝ) := density α s (-(radius m)) m x + density α s (radius m) m x
  let D (x : ℝ) := ∑ m ∈ orders, B m x
  let q := bandDensity α s 1
  have hB (m : ℕ) (hm : m ∈ orders) : Integrable (B m) := by
    obtain ⟨⟨h0, hα⟩, hcond⟩ := hr m hm
    have hpos : Integrable (density α s (radius m) m) := by
      apply (evaluationDensity_integrable_iff (a := -α) (b := α)
        (z := (radius m : ℂ)) (by simp only [Complex.ofReal_re]; linarith)
        (by simpa only [Complex.ofReal_re] using hα) (by linarith) m).mpr
      rcases hcond with h | h
      · exact Or.inl (by simp only [Complex.ofReal_re]; constructor <;> linarith)
      · exact Or.inr (by linarith)
    have hneg : Integrable (density α s (-(radius m)) m) := by
      apply (evaluationDensity_integrable_iff (a := -α) (b := α)
        (z := ((-(radius m)) : ℝ)) (by simp only [Complex.ofReal_re]; linarith)
        (by simp only [Complex.ofReal_re]; linarith) (by linarith) m).mpr
      rcases hcond with h | h
      · exact Or.inl (by simp only [Complex.ofReal_re]; constructor <;> linarith)
      · exact Or.inr (by linarith)
    exact hneg.add hpos
  have hD : Integrable D := integrable_finsetSum _ hB
  have hB₀ (m : ℕ) (x : ℝ) : 0 ≤ B m x :=
    add_nonneg (density_nonneg ..) (density_nonneg ..)
  have hq : Integrable q := bandDensity_integrable α s 1
  let L := Real.sqrt ((c : ℝ) * ∫ x, q x)
  let U := Real.sqrt ((c : ℝ) * ∫ x, D x)
  let C := 1 + U + L⁻¹
  have hc' : 0 < (c : ℝ) := NNReal.coe_pos.mpr hc
  have hL₀ : 0 < (c : ℝ) * ∫ x, q x := mul_pos hc' (density_band_integral_pos α s 1)
  have hL : 0 < L := Real.sqrt_pos_of_pos hL₀
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun χ m hm b t hb => ?_⟩
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  have hDle (x : ℝ) : density α s b m x ≤ D x :=
    (density_le_at_extremes α s m hl hu x).trans
      (Finset.single_le_sum (fun j _ => hB₀ j x) hm)
  have hi : Integrable (density α s b m) :=
    hD.mono' (density_continuous α s b m).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (density_nonneg α s b m x)]
        exact hDle x)
  obtain ⟨hLp, he⟩ := spectralStripMoment_memLp_and_energy F μ χ α s b t m hc hmap hi
  have hl' : -α ≤ b := by linarith [(hr m hm).1.2]
  have hnorm : ‖hLp.toLp _‖ = Real.sqrt ((c : ℝ) * ∫ x, density α s b m x) :=
    (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt he)
  have hlow : L ≤ ‖hLp.toLp _‖ := by
    rw [hnorm]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (integral_mono hq hi (by
        intro x
        simpa only [one_pow, one_mul] using
          (density_lower_on_band α s (k := 1) le_rfl hl' m x))) hc'.le)
  have hupp : ‖hLp.toLp _‖ ≤ U := by
    rw [hnorm]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (integral_mono hi hD hDle) hc'.le)
  refine ⟨hLp, ?_, ?_⟩
  · apply le_trans _ hlow
    exact (inv_le_comm₀ hC hL).mpr (by dsimp [C]; linarith)
  · exact hupp.trans (by dsimp [C]; linarith [inv_pos.mpr hL])

/-- An indexed family in the strip has a finite uniform upper norm bound
exactly when its orders are uniformly bounded and each order above the
endpoint threshold stays a positive distance from both endpoints. -/
theorem spectralStripMoments_uniform_upper_iff {α s : ℝ} (hs : 1 < s)
    {I : Type*} (χ : I → PontryaginDual (ClassGroupType F))
    (b t : I → ℝ) (m : I → ℕ) (hb : ∀ i, b i ∈ Icc (-α) α) :
    (∃ C : ℝ, ∀ i, ∃ hLp : MemLp
      (spectralStripMoment F (χ i) α s ((b i : ℂ) + (t i : ℂ) * Complex.I) (m i)) 2 μ,
      ‖hLp.toLp _‖ ≤ C) ↔
    ∃ (orders : Finset ℕ) (radius : ℕ → ℝ),
      (∀ k ∈ orders, radius k ∈ Icc 0 α ∧
        (radius k < α ∨ (k : ℝ) < (s - 1) / 2)) ∧
      ∀ i, m i ∈ orders ∧ |b i| ≤ radius (m i) := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨c, hc, hmap⟩ := ideleClassLogNorm_map_haar F μ
    have hc' : 0 < (c : ℝ) := NNReal.coe_pos.mpr hc
    let J := range (fun i => (b i, m i))
    have hJ (p : ℝ × ℕ) (hp : p ∈ J) :
        p.1 ∈ Icc (-α) α ∧ Integrable (density α s p.1 p.2) ∧
          (∫ x, density α s p.1 p.2 x) ≤ C ^ 2 / (c : ℝ) := by
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨hLp, hnorm⟩ := hC i
      have hb' := (spectralStripMoment_memLp_iff F μ (χ i)
        (by linarith : (0 : ℝ) ≤ s) (hb i) (t i) (m i)).mp hLp
      have hi : Integrable (density α s (b i) (m i)) := by
        apply (evaluationDensity_integrable_iff (a := -α) (b := α)
          (z := (b i : ℂ)) (by simpa only [Complex.ofReal_re] using (hb i).1)
          (by simpa only [Complex.ofReal_re] using (hb i).2) (by linarith) (m i)).mpr
        rcases hb' with h | h
        · exact Or.inl (by simpa only [mem_Ioo, Complex.ofReal_re] using h)
        · exact Or.inr (by linarith)
      refine ⟨hb i, hi, (le_div_iff₀ hc').mpr ?_⟩
      obtain ⟨_, he⟩ := spectralStripMoment_memLp_and_energy F μ (χ i) α s (b i)
        (t i) (m i) hc hmap hi
      rw [mul_comm, ← he]
      gcongr
    obtain ⟨orders, radius, hr, hsub⟩ := radialStripBounded_parameters (by linarith : (0 : ℝ) ≤ s) J hJ
    exact ⟨orders, radius, hr, fun i => hsub (b i, m i) (mem_range_self i)⟩
  · rintro ⟨orders, radius, hr, hsub⟩
    obtain ⟨C, _, hC⟩ := spectralStripMoments_uniform_norm F μ hs orders radius hr
    refine ⟨C, fun i => ?_⟩
    obtain ⟨hLp, _, hle⟩ := hC (χ i) (m i) (hsub i).1 (b i) (t i) (hsub i).2
    exact ⟨hLp, hle⟩

/-- The actual indices in (10.2.2.4) with the strict endpoint cutoff.
The interior includes every order below the multiplicity. -/
structure SpectralStripIndex
    (B : Set (PontryaginDual (ClassGroupType F)))
    (L : PontryaginDual (ClassGroupType F) → ℂ → ℂ) (a α s : ℝ) where
  character : PontryaginDual (ClassGroupType F)
  character_mem : character ∈ B
  abscissa : ℝ
  height : ℝ
  zero : L character (((a + abscissa : ℝ) : ℂ) + (height : ℂ) * Complex.I) = 0
  order : ℕ
  order_lt : order < analyticOrderNatAt (L character)
    (((a + abscissa : ℝ) : ℂ) + (height : ℂ) * Complex.I)
  abscissa_mem : abscissa ∈ Icc (-α) α
  bounded_jet : abscissa ∈ Ioo (-α) α ∨ (order : ℝ) < (s - 1) / 2

private theorem spectralStripIndex_memLp
    {B : Set (PontryaginDual (ClassGroupType F))}
    {L : PontryaginDual (ClassGroupType F) → ℂ → ℂ} {a α s : ℝ} (hs : 0 ≤ s)
    (j : SpectralStripIndex F B L a α s) :
    MemLp (spectralStripMoment F j.character α s
      ((j.abscissa : ℂ) + (j.height : ℂ) * Complex.I) j.order) 2 μ :=
  (spectralStripMoment_memLp_iff F μ j.character hs j.abscissa_mem
    j.height j.order).mpr j.bounded_jet

/-- The image in the actual reciprocal-weight Hilbert coordinate of all the
admissible orbital vectors on the given spectral strip. -/
def spectralStripFamily (B : Set (PontryaginDual (ClassGroupType F)))
    (L : PontryaginDual (ClassGroupType F) → ℂ → ℂ) (a α s : ℝ) (hs : 0 ≤ s) :
    Set (Lp ℂ 2 μ) :=
  range (fun j : SpectralStripIndex F B L a α s => (spectralStripIndex_memLp F μ hs j).toLp _)

/-- Corrected Proposition 10.2.2.2. The whole spectral family lies in one
positive annulus exactly under the stated control of orders and endpoint
distances. The open-ball conclusion holds exactly for a nonempty family. -/
theorem spectralStripFamily_uniform_norm {α s : ℝ} (hs : 1 < s)
    (B : Set (PontryaginDual (ClassGroupType F)))
    (L : PontryaginDual (ClassGroupType F) → ℂ → ℂ) (a : ℝ) :
    let W := spectralStripFamily F μ B L a α s (by linarith)
    (∃ C : ℝ, 0 < C ∧ W ⊆ {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} ∧
      (¬ W ⊆ Metric.ball 0 C⁻¹ ↔ W.Nonempty)) ↔
    ∃ (orders : Finset ℕ) (radius : ℕ → ℝ),
      (∀ m ∈ orders, radius m ∈ Icc 0 α ∧
        (radius m < α ∨ (m : ℝ) < (s - 1) / 2)) ∧
      ∀ j : SpectralStripIndex F B L a α s, j.order ∈ orders ∧ |j.abscissa| ≤ radius j.order := by
  intro W
  have hs' : 0 ≤ s := by linarith
  let v (j : SpectralStripIndex F B L a α s) := (spectralStripIndex_memLp F μ hs' j).toLp _
  change (∃ C : ℝ, 0 < C ∧ range v ⊆ {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} ∧
    (¬ range v ⊆ Metric.ball 0 C⁻¹ ↔ (range v).Nonempty)) ↔ _
  constructor
  · rintro ⟨C, _, hC, _⟩
    apply (spectralStripMoments_uniform_upper_iff F μ hs
      (fun j : SpectralStripIndex F B L a α s => j.character)
      (fun j => j.abscissa) (fun j => j.height) (fun j => j.order)
      (fun j => j.abscissa_mem)).mp
    exact ⟨C, fun j => ⟨spectralStripIndex_memLp F μ hs' j, (hC (mem_range_self j)).2⟩⟩
  · rintro ⟨orders, radius, hr, hj⟩
    obtain ⟨C, hC, hnorm⟩ := spectralStripMoments_uniform_norm F μ hs orders radius hr
    have hsubset : range v ⊆ {u | C⁻¹ ≤ ‖u‖ ∧ ‖u‖ ≤ C} := by
      rintro u ⟨j, rfl⟩
      obtain ⟨hLp, h⟩ := hnorm j.character j.order (hj j).1 j.abscissa j.height (hj j).2
      exact h
    refine ⟨C, hC, hsubset, ⟨fun h => ?_, ?_⟩⟩
    · obtain ⟨u, hu, _⟩ := not_subset.mp h
      exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩ hball
      have hu' := hball hu
      rw [Metric.mem_ball, dist_zero_right] at hu'
      exact (not_lt.mpr (hsubset hu).1) hu'

end

end Masullo
