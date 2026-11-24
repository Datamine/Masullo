import SLocalMellinDivisor

open Bornology Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Asymptotics NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The homogeneous theta bound of Corollary 7.1.3.3, in the stronger
bounded-family form valid for every number field. -/
theorem sLocalHomogeneousTheta_log_bounded [MeasurableSpace (SLocalThetaNormOne F S)]
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (B : Set (sLocalBruhatImage F S))
    (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : SIdeleQuotient F S,
      sLocalClassModulus F S g < Real.exp (-1) →
      ‖sLocalHomogeneousTheta F S μ ω f.val g‖ ≤
        C * |Real.log (sLocalClassModulus F S g)| ^ (Fintype.card (InfinitePlace F) + S.card - 1) := by
  letI := sLocalThetaNormOne_compact F S
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  let d := Fintype.card (InfinitePlace F) + S.card - 1
  obtain ⟨A, D, hA, hD, hlog⟩ := sLocalTheta_log_bounded F S B hB
  let M := (μ univ).toReal
  refine ⟨(A + D) * (M + 1), mul_pos (add_pos hA hD) (by
    exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one), ?_⟩
  intro f hf g hg
  let L := |Real.log (sLocalClassModulus F S g)| ^ d
  have hlogg : Real.log (sLocalClassModulus F S g) < -1 := by
    simpa only [Real.log_exp] using
      Real.log_lt_log (sLocalClassModulus_pos F S g) hg
  have hL : 1 ≤ L := one_le_pow₀ (by
    rw [abs_of_neg (hlogg.trans (by norm_num))]
    linarith)
  have hpoint (k : SLocalThetaNormOne F S) :
      ‖((ω k : Circle) : ℂ) *
        sLocalTheta F S (sLocalBruhatRestriction F S f.val) (k.val * g)‖ ≤ (A + D) * L := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (k.val * g)
    have hmod : sLocalIdeleNorm F S a = sLocalClassModulus F S g := by
      rw [← sLocalClassModulus_mk, ha, sLocalClassModulus_normOne_mul]
    have hb : ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) a‖ ≤ A * L + D := by
      have h := hlog f hf a (by
        rw [hmod]
        exact hg.trans (Real.exp_lt_one_iff.mpr (by norm_num)))
      simpa only [hmod, L, d] using h
    rw [norm_mul, Circle.norm_coe, one_mul, ← ha]
    change ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) a‖ ≤ (A + D) * L
    calc
      _ ≤ A * L + D := hb
      _ ≤ A * L + D * L := add_le_add_right
        (le_mul_of_one_le_right hD.le hL) _
      _ = _ := (add_mul A D L).symm
  calc
    ‖sLocalHomogeneousTheta F S μ ω f.val g‖ ≤ ((A + D) * L) * M :=
      norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)
    _ ≤ ((A + D) * L) * (M + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg (add_pos hA hD).le (zero_le_one.trans hL))
    _ = (A + D) * (M + 1) * L := by ring

/-- The pointwise small-modulus asymptotic on the actual S-idele quotient. -/
theorem sLocalHomogeneousTheta_log_isBigO [MeasurableSpace (SLocalThetaNormOne F S)]
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) :
    (fun g => sLocalHomogeneousTheta F S μ ω f.val g) =O[sLocalSmallNorm F S]
      (fun g => |Real.log (sLocalClassModulus F S g)| ^ (Fintype.card (InfinitePlace F) + S.card - 1)) := by
  obtain ⟨C, -, h⟩ := sLocalHomogeneousTheta_log_bounded F S μ ω {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f)
  refine Asymptotics.IsBigO.of_bound C ?_
  have hnear : ∀ᶠ g in sLocalSmallNorm F S, sLocalClassModulus F S g < Real.exp (-1) :=
    tendsto_comap.eventually
      (nhdsWithin_le_nhds (Iio_mem_nhds (Real.exp_pos (-1))))
  filter_upwards [hnear] with g hg
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact h f (mem_singleton f) g hg

/-- Corrected Corollary 7.1.3.3 for a number field with one infinite place. -/
theorem sLocalHomogeneousTheta_log_isBigO_one_infinitePlace
    [MeasurableSpace (SLocalThetaNormOne F S)]
    (hInf : Fintype.card (InfinitePlace F) = 1)
    (μ : Measure (SLocalThetaNormOne F S)) [μ.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) :
    (fun g => sLocalHomogeneousTheta F S μ ω f.val g) =O[sLocalSmallNorm F S]
      (fun g => |Real.log (sLocalClassModulus F S g)| ^ S.card) := by
  have hd : Fintype.card (InfinitePlace F) + S.card - 1 = S.card := by omega
  simpa only [hd] using sLocalHomogeneousTheta_log_isBigO F S μ ω f

/-- The printed rule for the lower pole order cannot assign an integer to
every test. For the zero test the continued transform has no pole at all. -/
theorem sLocal_zero_test_no_pole
    [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
    [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
    (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ) [∀ v : S, (μ v).IsHaarMeasure]
    [∀ v : S, SigmaFinite (μ v)]
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (c : ℂ) :
    meromorphicOrderAt (sLocalProductZetaContinued F S μ ω
        (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) 0) c = ⊤ := by
  have hzero : sLocalProductZetaContinued F S μ ω
      (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) 0 =
        fun _ : ℂ => (0 : ℂ) := by
    funext z
    exact (sLocalContinuedMellinEval F S μ ω z).map_zero
  rw [hzero, meromorphicOrderAt_const, ite_eq_left rfl]

end

end Masullo
