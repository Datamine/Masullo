import SLocalThetaSmallNorm
import Mathlib.MeasureTheory.Group.Integral

open Asymptotics Bornology Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Asymptotics NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The large-modulus filter of the S-idele classes. -/
def sLocalLargeNorm : Filter (SIdeleQuotient F S) :=
  comap (sLocalClassModulus F S) atTop

/-- Proposition 2.3.1.2, uniform bound clauses. The exponent-zero case and
every higher degree hold with modulus threshold one. -/
theorem sLocalTheta_largeNorm_class_bounded (B : Set (sLocalBruhatImage F S)) (hB : IsVonNBounded ℂ B)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleQuotient F S, 1 ≤ sLocalClassModulus F S g →
      ‖sLocalTheta F S (sLocalBruhatRestriction F S f.val) g‖ ≤ C * (sLocalClassModulus F S g ^ N)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := sLocalTheta_largeNorm_bounded F S B hB N
  refine ⟨C, hC, fun f hf g hg => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  simp only [sLocalTheta_mk, sLocalClassModulus_mk] at hg ⊢
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans_le hg) _), mul_comm]
  exact hb f hf a hg

private theorem eventually_largeNorm :
    ∀ᶠ g in sLocalLargeNorm F S, 1 ≤ sLocalClassModulus F S g :=
  (show Tendsto (sLocalClassModulus F S) (sLocalLargeNorm F S) atTop from map_comap_le).eventually
    (eventually_ge_atTop 1)

/-- Proposition 2.3.1.2, individual rapid decay on the S-idele classes. -/
theorem sLocalTheta_largeNorm_isBigO (f : sLocalBruhatImage F S) (N : ℕ) :
    (fun g => sLocalTheta F S (sLocalBruhatRestriction F S f.val) g) =O[sLocalLargeNorm F S]
      (fun g => (sLocalClassModulus F S g ^ N)⁻¹) := by
  obtain ⟨C, _, hb⟩ := sLocalTheta_largeNorm_class_bounded F S {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) N
  apply IsBigO.of_bound C
  filter_upwards [eventually_largeNorm F S] with g hg
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (sLocalClassModulus_pos F S g).le _))]
  exact hb f (by simp) g hg

section Homogeneous

variable [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)]

private def homogeneousIntegrand (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : GlobalBruhat F) (g : SIdeleQuotient F S) (k : SLocalThetaNormOne F S) : ℂ :=
  ((ω k : Circle) : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f) (k.val * g)

omit [MeasurableSpace (SLocalThetaNormOne F S)] [BorelSpace (SLocalThetaNormOne F S)] in
private theorem homogeneousIntegrand_continuous (ω : PontryaginDual (SLocalThetaNormOne F S))
    (f : GlobalBruhat F) :
    Continuous (fun p : SIdeleQuotient F S × SLocalThetaNormOne F S =>
      homogeneousIntegrand F S ω f p.1 p.2) := by
  have hk : Continuous (fun p : SIdeleQuotient F S × SLocalThetaNormOne F S => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_subtype_val.comp ω.continuous).comp continuous_snd).mul
    ((sLocalTheta_continuous F S f).comp (hk.mul continuous_fst))

omit [BorelSpace (SLocalThetaNormOne F S)] in
/-- The character integral has a common integrable majorant on each compact
set of parameters. -/
theorem sLocalHomogeneousTheta_compact_majorant (μ : Measure (SLocalThetaNormOne F S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : GlobalBruhat F)
    (K : Set (SIdeleQuotient F S)) (hK : IsCompact K) :
    ∃ M : ℝ, Integrable (fun _ : SLocalThetaNormOne F S => M) μ ∧
      ∀ g ∈ K, ∀ k : SLocalThetaNormOne F S,
        ‖((ω k : Circle) : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f) (k.val * g)‖ ≤ M := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨M, hM⟩ := (hK.prod isCompact_univ).exists_bound_of_continuousOn
    (homogeneousIntegrand_continuous F S ω f).continuousOn
  exact ⟨M, integrable_const _, fun g hg k => hM (g, k) ⟨hg, mem_univ k⟩⟩

/-- The homogeneous theta average is continuous on the actual S-idele classes. -/
theorem sLocalHomogeneousTheta_continuous (μ : Measure (SLocalThetaNormOne F S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : GlobalBruhat F) :
    Continuous (sLocalHomogeneousTheta F S μ ω f) := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  let v := homogeneousIntegrand F S ω f
  have hc := homogeneousIntegrand_continuous F S ω f
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let M := (μ univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hnear : ∀ᶠ g in 𝓝 a, ∀ k : SLocalThetaNormOne F S, ‖v g k - v a k‖ < δ := by
    have hcont : Continuous (fun p : SIdeleQuotient F S × SLocalThetaNormOne F S =>
        ‖v p.1 p.2 - v a p.2‖) :=
      (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).norm
    have hp := IsCompact.eventually_forall_of_forall_eventually
      (isCompact_univ : IsCompact (univ : Set (SLocalThetaNormOne F S))) (x₀ := a)
        (P := fun g k => ‖v g k - v a k‖ < δ) (fun k _ => by
          have ht : Tendsto (fun p : SIdeleQuotient F S × SLocalThetaNormOne F S =>
              ‖v p.1 p.2 - v a p.2‖) (𝓝 (a, k)) (𝓝 0) := by
            have hca : ContinuousAt (fun p => ‖v p.1 p.2 - v a p.2‖) (a, k) :=
              hcont.continuousAt
            change Tendsto _ _ (𝓝 ‖v a k - v a k‖) at hca
            simpa only [sub_self, norm_zero] using hca
          exact ht.eventually (Iio_mem_nhds hδ))
    exact hp.mono fun _ h k => h k (mem_univ k)
  filter_upwards [hnear] with g hg
  have hint (b : SIdeleQuotient F S) : Integrable (v b) μ :=
    sLocalHomogeneousTheta_integrable F S μ ω f b
  change dist (∫ k, v g k ∂μ) (∫ k, v a k ∂μ) < ε
  rw [dist_eq_norm, ← integral_sub (hint g) (hint a)]
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall fun k => (hg k).le)).trans_lt ?_
  change δ * M < ε
  dsimp only [δ]
  calc
    ε / (M + 1) * M = ε * (M / (M + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).mpr (by linarith)) hε
    _ = ε := mul_one _

/-- Left translation of the argument multiplies homogeneous theta by the
inverse character. The left regular action therefore has character `ω`. -/
theorem sLocalHomogeneousTheta_translate (μ : Measure (SLocalThetaNormOne F S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : GlobalBruhat F)
    (k : SLocalThetaNormOne F S) (g : SIdeleQuotient F S) :
    sLocalHomogeneousTheta F S μ ω f (k.val * g) =
      (((ω k : Circle) : ℂ)⁻¹) * sLocalHomogeneousTheta F S μ ω f g := by
  let v := homogeneousIntegrand F S ω f
  change (∫ b, v (k.val * g) b ∂μ) = (((ω k : Circle) : ℂ)⁻¹) * ∫ b, v g b ∂μ
  rw [← integral_mul_left_eq_self (fun b => v (k.val * g) b) k⁻¹, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun b => ?_
  change ((ω (k⁻¹ * b) : Circle) : ℂ) *
    sLocalTheta F S (sLocalBruhatRestriction F S f) ((k.val⁻¹ * b.val) * (k.val * g)) =
      (((ω k : Circle) : ℂ)⁻¹) * (((ω b : Circle) : ℂ) *
        sLocalTheta F S (sLocalBruhatRestriction F S f) (b.val * g))
  have he : (k.val⁻¹ * b.val) * (k.val * g) = b.val * g := by
    calc
      _ = k.val⁻¹ * (b.val * (k.val * g)) := mul_assoc _ _ _
      _ = (k.val⁻¹ * k.val) * (b.val * g) := by rw [mul_left_comm b.val k.val, ← mul_assoc]
      _ = _ := by rw [inv_mul_cancel, one_mul]
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_assoc, he]

omit [BorelSpace (SLocalThetaNormOne F S)] in
/-- Proposition 2.3.1.4, uniform bound clauses. Character averaging preserves
all powers in the rapid-decay estimate below the same large-modulus threshold. -/
theorem sLocalHomogeneousTheta_largeNorm_bounded (μ : Measure (SLocalThetaNormOne F S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (SLocalThetaNormOne F S))
    (B : Set (sLocalBruhatImage F S)) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleQuotient F S, 1 ≤ sLocalClassModulus F S g →
      ‖sLocalHomogeneousTheta F S μ ω f.val g‖ ≤ C * (sLocalClassModulus F S g ^ N)⁻¹ := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨A, hA, hb⟩ := sLocalTheta_largeNorm_class_bounded F S B hB N
  let M := (μ univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨A * (M + 1), by positivity, fun f hf g hg => ?_⟩
  let r := (sLocalClassModulus F S g ^ N)⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr (pow_nonneg (sLocalClassModulus_pos F S g).le _)
  have hpoint (k : SLocalThetaNormOne F S) : ‖homogeneousIntegrand F S ω f.val g k‖ ≤ A * r := by
    unfold homogeneousIntegrand
    rw [norm_mul, Circle.norm_coe, one_mul]
    simpa only [sLocalClassModulus_normOne_mul, r] using
      hb f hf (k.val * g) (by rwa [sLocalClassModulus_normOne_mul])
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hpoint)).trans ?_
  change A * r * M ≤ A * (M + 1) * r
  rw [mul_right_comm A r M, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hr) hA.le

omit [BorelSpace (SLocalThetaNormOne F S)] in
/-- Proposition 2.3.1.4, individual rapid decay of homogeneous theta. -/
theorem sLocalHomogeneousTheta_largeNorm_isBigO (μ : Measure (SLocalThetaNormOne F S))
    [μ.IsHaarMeasure] (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (N : ℕ) :
    (fun g => sLocalHomogeneousTheta F S μ ω f.val g) =O[sLocalLargeNorm F S]
      (fun g => (sLocalClassModulus F S g ^ N)⁻¹) := by
  obtain ⟨C, _, hb⟩ := sLocalHomogeneousTheta_largeNorm_bounded F S μ ω {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) N
  apply IsBigO.of_bound C
  filter_upwards [eventually_largeNorm F S] with g hg
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (sLocalClassModulus_pos F S g).le _))]
  exact hb f (by simp) g hg

end Homogeneous

end

end Masullo
