import SLocalThetaGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Bornology Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Asymptotics NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The real modulus of the S-idele classes. -/
def sLocalClassModulus (g : SIdeleQuotient F S) : ℝ :=
  ((sQuotientNorm F S g).val : ℝ)

@[simp] theorem sLocalClassModulus_mk (g : (SAdeles F S)ˣ) :
    sLocalClassModulus F S (QuotientGroup.mk g) = sLocalIdeleNorm F S g := rfl

theorem sLocalClassModulus_pos (g : SIdeleQuotient F S) : 0 < sLocalClassModulus F S g :=
  NNReal.coe_pos.mpr (Units.zero_lt _)

abbrev SLocalThetaNormOne := (sQuotientNorm F S).ker

theorem sLocalThetaNormOne_compact : CompactSpace (SLocalThetaNormOne F S) := by
  apply isCompact_iff_compactSpace.mp
  exact (sQuotientNorm_proper F S).isCompact_preimage isCompact_singleton

variable [MeasurableSpace (SLocalThetaNormOne F S)]

/-- The homogeneous theta series is the character average over the
norm-one subgroup of the S-idele classes. -/
def sLocalHomogeneousTheta (μ : Measure (SLocalThetaNormOne F S))
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : GlobalBruhat F)
    (g : SIdeleQuotient F S) : ℂ :=
  ∫ k, ((ω k : Circle) : ℂ) *
    sLocalTheta F S (sLocalBruhatRestriction F S f) (k.val * g) ∂μ

theorem sLocalHomogeneousTheta_integrable [BorelSpace (SLocalThetaNormOne F S)]
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : GlobalBruhat F)
    (g : SIdeleQuotient F S) :
    Integrable (fun k => ((ω k : Circle) : ℂ) *
      sLocalTheta F S (sLocalBruhatRestriction F S f) (k.val * g)) μ := by
  letI := sLocalThetaNormOne_compact F S
  have hw := continuous_subtype_val.comp ω.continuous
  have hk : Continuous (fun k : SLocalThetaNormOne F S => k.val * g) :=
    continuous_subtype_val.mul (continuous_const (y := g))
  exact (hw.mul ((sLocalTheta_continuous F S f).comp hk)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace (SLocalThetaNormOne F S)] in
theorem sLocalClassModulus_normOne_mul (k : SLocalThetaNormOne F S) (g : SIdeleQuotient F S) :
    sLocalClassModulus F S (k.val * g) = sLocalClassModulus F S g := by
  unfold sLocalClassModulus
  rw [map_mul, show sQuotientNorm F S k.val = 1 from k.property, one_mul]

private theorem logPower_mul_rpow_tendsto (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun r : ℝ => |Real.log r| ^ d * r ^ ε) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) ε hε).comp hl
  apply h.congr'
  have hp : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have ht : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [hp, ht] with r hr ht'
  change (-Real.log r) ^ (d : ℝ) * Real.exp (-ε * -Real.log r) = _
  rw [Real.rpow_natCast, abs_of_neg (Real.log_neg hr ht'), Real.rpow_def_of_pos hr]
  congr 2
  ring

theorem logPower_mul_rpow_bounded (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → r < 1 →
      |Real.log r| ^ d * r ^ ε ≤ M := by
  have ht := logPower_mul_rpow_tendsto d ε hε
  obtain ⟨δ, hδ, hδmajor⟩ := Metric.nhdsWithin_basis_ball.mem_iff.mp
    (ht.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨max 1 (|Real.log δ| ^ d), (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _),
    fun r hr hr' => ?_⟩
  by_cases h : r < δ
  · exact ((hδmajor ⟨by simpa [Real.dist_eq, abs_of_pos hr] using h, hr⟩).le).trans (le_max_left _ _)
  · have hlog : |Real.log r| ≤ |Real.log δ| := by
      have hd : δ < 1 := (not_lt.mp h).trans_lt hr'
      rw [abs_of_neg (Real.log_neg hr hr'), abs_of_neg (Real.log_neg hδ hd)]
      exact neg_le_neg (Real.log_le_log hδ (not_lt.mp h))
    exact (mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) _) (Real.rpow_le_one hr.le hr'.le hε.le)).trans
      ((pow_le_pow_left₀ (abs_nonneg _) hlog _).trans (le_max_right _ _))

/-- Proposition 2.4.3.1. The weighted ordinary and homogeneous theta
functions are uniformly bounded on bounded families below modulus one. -/
theorem sLocalTheta_smallNorm_bounded (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (B : Set (sLocalBruhatImage F S))
    (hB : IsVonNBounded ℂ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleQuotient F S, sLocalClassModulus F S g < 1 →
      ‖sLocalTheta F S (sLocalBruhatRestriction F S f.val) g‖ * sLocalClassModulus F S g ^ ε ≤ C ∧
      ‖sLocalHomogeneousTheta F S μ ω f.val g‖ * sLocalClassModulus F S g ^ ε ≤ C := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  let d := Fintype.card (InfinitePlace F) + S.card - 1
  obtain ⟨C₁, C₂, hC₁, hC₂, hlog⟩ := sLocalTheta_log_bounded F S B hB
  obtain ⟨D, hD, hd⟩ := logPower_mul_rpow_bounded d ε hε
  let A := C₁ * D + C₂
  have hA : 0 < A := by dsimp [A]; positivity
  have hb (f : sLocalBruhatImage F S) (hf : f ∈ B) (g : SIdeleQuotient F S)
      (hg : sLocalClassModulus F S g < 1) :
      ‖sLocalTheta F S (sLocalBruhatRestriction F S f.val) g‖ * sLocalClassModulus F S g ^ ε ≤ A := by
    have hp := sLocalClassModulus_pos F S g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    let r := sLocalIdeleNorm F S a
    change 0 < r at hp
    change r < 1 at hg
    have h := hlog f hf a hg
    change ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) a‖ * r ^ ε ≤ A
    calc
      _ ≤ (C₁ * |Real.log r| ^ d + C₂) * r ^ ε :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hp.le _)
      _ = C₁ * (|Real.log r| ^ d * r ^ ε) + C₂ * r ^ ε := by ring
      _ ≤ A := add_le_add (mul_le_mul_of_nonneg_left (hd r hp hg) hC₁.le)
        (mul_le_of_le_one_right hC₂.le (Real.rpow_le_one hp.le hg.le hε.le))
  let M := (μ univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  refine ⟨A * (M + 1), by positivity, fun f hf g hg => ⟨(hb f hf g hg).trans ?_, ?_⟩⟩
  · exact le_mul_of_one_le_right hA.le (by linarith)
  · let r := sLocalClassModulus F S g ^ ε
    have hr : 0 < r := Real.rpow_pos_of_pos (sLocalClassModulus_pos F S g) _
    have hpoint (k : SLocalThetaNormOne F S) :
        ‖((ω k : Circle) : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f.val) (k.val * g)‖ ≤ A / r := by
      rw [norm_mul, Circle.norm_coe, one_mul, le_div_iff₀ hr]
      simpa only [sLocalClassModulus_normOne_mul, r] using
        hb f hf (k.val * g) (by rwa [sLocalClassModulus_normOne_mul])
    have hi := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)
    change ‖sLocalHomogeneousTheta F S μ ω f.val g‖ * r ≤ _
    calc
      _ ≤ (A / r * M) * r := mul_le_mul_of_nonneg_right hi hr.le
      _ = A * M := by field_simp
      _ ≤ A * (M + 1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hA.le

/-- Approach to zero through the positive S-idelic modulus. -/
def sLocalSmallNorm : Filter (SIdeleQuotient F S) :=
  comap (sLocalClassModulus F S) (𝓝[>] 0)

/-- Corollary 2.4.3.2. Both weighted theta functions tend to zero at small modulus. -/
theorem sLocalTheta_smallNorm_tendsto (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) (ε : ℝ)
    (hε : 0 < ε) :
    Tendsto (fun g => (sLocalClassModulus F S g ^ ε : ℝ) •
      sLocalTheta F S (sLocalBruhatRestriction F S f.val) g) (sLocalSmallNorm F S) (𝓝 0) ∧
    Tendsto (fun g => (sLocalClassModulus F S g ^ ε : ℝ) •
      sLocalHomogeneousTheta F S μ ω f.val g) (sLocalSmallNorm F S) (𝓝 0) := by
  have he : 0 < ε / 2 := half_pos hε
  obtain ⟨C, hC, hb⟩ := sLocalTheta_smallNorm_bounded F S μ ω {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) (ε / 2) he
  have hm : Tendsto (sLocalClassModulus F S) (sLocalSmallNorm F S) (𝓝[>] 0) :=
    map_comap_le
  have hp : Tendsto (fun g => sLocalClassModulus F S g ^ (ε / 2)) (sLocalSmallNorm F S) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const he.le).tendsto 0).comp (hm.mono_right nhdsWithin_le_nhds)
    simpa only [Real.zero_rpow he.ne', Function.comp_def] using h
  have hbound : ∀ᶠ g in sLocalSmallNorm F S, sLocalClassModulus F S g < 1 :=
    hm.eventually (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))
  have hlim (φ : SIdeleQuotient F S → ℂ)
      (hφ : ∀ g, sLocalClassModulus F S g < 1 →
        ‖φ g‖ * sLocalClassModulus F S g ^ (ε / 2) ≤ C) :
      Tendsto (fun g => (sLocalClassModulus F S g ^ ε : ℝ) • φ g)
        (sLocalSmallNorm F S) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hCpow := hp.const_mul C
    rw [mul_zero] at hCpow
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hCpow
    filter_upwards [hbound] with g hg
    let r := sLocalClassModulus F S g
    have hr := (sLocalClassModulus_pos F S g).le
    have hrpow : r ^ ε = r ^ (ε / 2) * r ^ (ε / 2) := by
      rw [← Real.rpow_add (sLocalClassModulus_pos F S g)]
      congr 1
      ring
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr _), hrpow]
    change r ^ (ε / 2) * r ^ (ε / 2) * ‖φ g‖ ≤ C * r ^ (ε / 2)
    rw [mul_comm _ ‖φ g‖, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hφ g hg) (Real.rpow_nonneg hr _)
  exact ⟨hlim _ (fun g hg => (hb f (by simp) g hg).1),
    hlim _ (fun g hg => (hb f (by simp) g hg).2)⟩

/-- The pointwise big-O assertions of Proposition 2.4.3.1. The bounded-family
version holds up to modulus one, as in the last clause of the proposition. -/
theorem sLocalTheta_smallNorm_isBigO (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) (ε : ℝ)
    (hε : 0 < ε) :
    ((fun g => (sLocalClassModulus F S g ^ ε : ℝ) •
      sLocalTheta F S (sLocalBruhatRestriction F S f.val) g) =O[sLocalSmallNorm F S]
        fun _ => (1 : ℝ)) ∧
    ((fun g => (sLocalClassModulus F S g ^ ε : ℝ) •
      sLocalHomogeneousTheta F S μ ω f.val g) =O[sLocalSmallNorm F S] fun _ => (1 : ℝ)) := by
  obtain ⟨h, hω⟩ := sLocalTheta_smallNorm_tendsto F S μ ω f ε hε
  exact ⟨Asymptotics.isBigO_const_of_tendsto h one_ne_zero,
    Asymptotics.isBigO_const_of_tendsto hω one_ne_zero⟩

end

end Masullo
