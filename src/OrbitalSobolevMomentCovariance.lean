import OrbitalSobolevNorms
import HardySobolevTranslations

open Filter Function MeasureTheory NumberField Set Topology
open scoped InnerProductSpace NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev G := IdeleClass F
private abbrev logNorm (q : G F) : ℝ := (ideleClassLogNorm F q).toAdd
private abbrev amplitude (s : ℝ) (q : G F) :=
  hardySobolevAmplitude 0 0 s (logNorm F q)

local instance orbitalCovarianceMeasurable : MeasurableSpace (G F) := borel _
local instance orbitalCovarianceBorel : BorelSpace (G F) := ⟨rfl⟩
local instance orbitalCovarianceT2 : T2Space (G F) := ideleClasses_hausdorff
local instance orbitalCovarianceLocallyCompact : LocallyCompactSpace (G F) := ideleClasses_locallyCompact
local instance orbitalCovarianceSecondCountable : SecondCountableTopology (G F) := by
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F) := adeles_secondCountable F
  letI : SecondCountableTopology (NumberField.AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := principalIdeles F))

variable (μ : Measure (G F)) [μ.IsHaarMeasure]
variable (s : ℝ) (hs : 0 ≤ s)
variable (χ : PontryaginDual (G F)) (z : ℂ) (hz : z.re = 0)

private abbrev T (g : G F) :=
  hardySobolevMulTranslation μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F) 0 0 s hs g

/-- The character and radial exponential together form the translation
eigenvalue of the order-zero moment. -/
def orbitalMomentPhase (g : G F) : ℂ :=
  (χ g : ℂ) * Complex.exp (z * (logNorm F g : ℂ))

/-- The continuous linear moment functional in the amplitude coordinates. -/
def orbitalSobolevMomentCLM (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2) :
    Lp ℂ 2 μ →L[ℂ] ℂ :=
  let h := ((orbitalSobolevMoment_memLp_iff F μ χ hs hz m).mpr hm).star
  innerSL ℂ (h.toLp (fun q ↦ star (orbitalSobolevMoment F χ s z m q)))

theorem orbitalSobolevMomentCLM_apply (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2)
    (u : Lp ℂ 2 μ) :
    orbitalSobolevMomentCLM F μ s hs χ z hz m hm u =
      ∫ q, u q * orbitalSobolevMoment F χ s z m q ∂μ := by
  let h := ((orbitalSobolevMoment_memLp_iff F μ χ hs hz m).mpr hm).star
  change ⟪h.toLp _, u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with q hq
  rw [RCLike.inner_apply, hq, starRingEnd_apply]
  exact congrArg (u q * ·) (star_star (orbitalSobolevMoment F χ s z m q))

include hs hz in
private theorem orbital_integrable (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2) (u : Lp ℂ 2 μ) :
    Integrable (fun q ↦ u q * orbitalSobolevMoment F χ s z m q) μ := by
  let h := ((orbitalSobolevMoment_memLp_iff F μ χ hs hz m).mpr hm).star
  apply (L2.integrable_inner (𝕜 := ℂ) (h.toLp _) u).congr
  filter_upwards [h.coeFn_toLp] with q hq
  rw [RCLike.inner_apply, hq, starRingEnd_apply]
  exact congrArg (u q * ·) (star_star (orbitalSobolevMoment F χ s z m q))

private theorem amp_eq (q : G F) :
    amplitude F s q = (1 + (logNorm F q)^2) ^ (s / 4) := by
  simp only [amplitude, hardySobolevAmplitude, hardySobolevWeight, mul_zero, zero_mul,
    Real.exp_zero, max_self, one_mul, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

private theorem moment_eq (m : ℕ) (q : G F) :
    orbitalSobolevMoment F χ s z m q =
      (amplitude F s q : ℂ)⁻¹ * orbitalMomentPhase F χ z q * (logNorm F q : ℂ)^m := by
  unfold orbitalSobolevMoment orbitalMomentPhase
  rw [amp_eq, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_inv, ← Real.rpow_neg (by positivity)]
  rw [show -(s / 4) = -s / 4 by ring]

private theorem phase_mul (g q : G F) :
    orbitalMomentPhase F χ z (g * q) = orbitalMomentPhase F χ z g * orbitalMomentPhase F χ z q := by
  have he : logNorm F (g * q) = logNorm F g + logNorm F q := congrArg Multiplicative.toAdd
    (map_mul (ideleClassLogNorm F) g q)
  rw [orbitalMomentPhase, he, Complex.ofReal_add, mul_add, Complex.exp_add, map_mul, Circle.coe_mul]
  unfold orbitalMomentPhase
  ring

private theorem amp_ne_zero (q : G F) : (amplitude F s q : ℂ) ≠ 0 := by
  rw [amp_eq]
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'

private theorem admissible_of_le {j m : ℕ} (hjm : j ≤ m) (hm : (m : ℝ) < (s - 1) / 2) :
    (j : ℝ) < (s - 1) / 2 := lt_of_le_of_lt (by exact_mod_cast hjm) hm

/-- Translating an admissible moment of degree `m` gives the binomial
combination of moments of degrees zero through `m`. -/
theorem orbitalSobolevMomentCLM_translate (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2)
    (g : G F) (u : Lp ℂ 2 μ) :
    orbitalSobolevMomentCLM F μ s hs χ z hz m hm (T F μ s hs g u) =
      orbitalMomentPhase F χ z g *
        ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℕ) : ℂ) *
          (logNorm F g : ℂ) ^ (m-j) * ∫ q, u q * orbitalSobolevMoment F χ s z j q ∂μ := by
  let d : ℂ := logNorm F g
  let M (j : ℕ) (q : G F) := u q * orbitalSobolevMoment F χ s z j q
  let f (q : G F) := T F μ s hs g u q * orbitalSobolevMoment F χ s z m q
  have hT := (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae_eq_comp
    (hardySobolevMulTranslation_ae μ (ideleClassLogNorm F) (ideleClassLogNorm_continuous F)
      0 0 s hs g u)
  rw [orbitalSobolevMomentCLM_apply]
  change (∫ q, f q ∂μ) = orbitalMomentPhase F χ z g *
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) * d ^ (m-j) * ∫ q, M j q ∂μ
  have hsum :
      (∫ q, ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) * d ^ (m-j) * M j q ∂μ) =
        ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) * d ^ (m-j) * ∫ q, M j q ∂μ := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun _ _ ↦ integral_const_mul _ _)
    · intro j hj
      exact (orbital_integrable F μ s hs χ z hz j
        (admissible_of_le s (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hm) u).const_mul _
  rw [← integral_mul_left_eq_self f g, ← hsum, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hT] with q hq
  have ht : logNorm F (g * q) = logNorm F g + logNorm F q :=
    congrArg Multiplicative.toAdd (map_mul (ideleClassLogNorm F) g q)
  change T F μ s hs g u (g * q) =
    ((amplitude F s (g * q) / amplitude F s (g⁻¹ * (g * q)) : ℝ) : ℂ) *
      u (g⁻¹ * (g * q)) at hq
  rw [inv_mul_cancel_left, Complex.ofReal_div] at hq
  dsimp only [f]
  rw [hq, moment_eq, phase_mul, ht, Complex.ofReal_add]
  have hcancel : (amplitude F s (g*q) : ℂ) / (amplitude F s q : ℂ) *
      (amplitude F s (g*q) : ℂ)⁻¹ = (amplitude F s q : ℂ)⁻¹ := by
    field_simp [amp_ne_zero F s (g*q), amp_ne_zero F s q]
  have he : ((amplitude F s (g*q) : ℂ) / (amplitude F s q : ℂ) * u q) *
      ((amplitude F s (g*q) : ℂ)⁻¹ *
        (orbitalMomentPhase F χ z g * orbitalMomentPhase F χ z q) *
        ((logNorm F g : ℂ) + (logNorm F q : ℂ)) ^ m) =
      orbitalMomentPhase F χ z g * ((logNorm F q : ℂ) + d) ^ m *
        (u q * (amplitude F s q : ℂ)⁻¹ * orbitalMomentPhase F χ z q) := by
    calc
      _ = ((amplitude F s (g*q) : ℂ) / (amplitude F s q : ℂ) *
          (amplitude F s (g*q) : ℂ)⁻¹) * (u q *
            (orbitalMomentPhase F χ z g * orbitalMomentPhase F χ z q) *
            ((logNorm F g : ℂ) + (logNorm F q : ℂ)) ^ m) := by ring
      _ = _ := by rw [hcancel, add_comm (logNorm F g : ℂ)]; dsimp [d]; ring
  rw [he, mul_assoc, add_pow, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [M]
  rw [moment_eq]
  ring

private abbrev M (u : Lp ℂ 2 μ) (m : ℕ) :=
  ∫ q, u q * orbitalSobolevMoment F χ s z m q ∂μ

include hz in
/-- One difference preserves the earlier zero moments. When its translation
phase is one, the degree-`m` moment of the difference also vanishes as
soon as all strictly lower moments vanish. -/
theorem orbitalSobolevMoment_difference_zero (g : G F) (u : Lp ℂ 2 μ)
    (m : ℕ) (hm : (m : ℝ) < (s - 1) / 2)
    (hlower : ∀ j < m, M F μ s χ z u j = 0)
    (htop : orbitalMomentPhase F χ z g = 1 ∨ M F μ s χ z u m = 0) :
    M F μ s χ z (u - T F μ s hs g u) m = 0 := by
  let L := orbitalSobolevMomentCLM F μ s hs χ z hz m hm
  have hL : ∀ x, L x = M F μ s χ z x m :=
    orbitalSobolevMomentCLM_apply F μ s hs χ z hz m hm
  have hdiff : L (T F μ s hs g u) = orbitalMomentPhase F χ z g * L u := by
    rw [orbitalSobolevMomentCLM_translate F μ s hs χ z hz m hm g u]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj ↦ by
      change _ * M F μ s χ z u j = 0
      rw [hlower j (Finset.mem_range.mp hj), mul_zero])]
    simp [hL, M]
  rw [← hL, map_sub, hdiff]
  rcases htop with ht | ht
  · rw [ht, one_mul, sub_self]
  · rw [hL u, ht, mul_zero, sub_self]

/-- The order-zero moment is an exact translation eigenfunctional. -/
theorem orbitalSobolevMomentCLM_translate_zero (hm : ((0 : ℕ) : ℝ) < (s - 1) / 2)
    (g : G F) (u : Lp ℂ 2 μ) :
    orbitalSobolevMomentCLM F μ s hs χ z hz 0 hm (T F μ s hs g u) =
      orbitalMomentPhase F χ z g * M F μ s χ z u 0 := by
  rw [orbitalSobolevMomentCLM_translate F μ s hs χ z hz 0 hm g u]
  simp [M]

/-- The first moment acquires the log shift times the zeroth moment. -/
theorem orbitalSobolevMomentCLM_translate_one (hm : ((1 : ℕ) : ℝ) < (s - 1) / 2)
    (g : G F) (u : Lp ℂ 2 μ) :
    orbitalSobolevMomentCLM F μ s hs χ z hz 1 hm (T F μ s hs g u) =
      orbitalMomentPhase F χ z g *
        ((logNorm F g : ℂ) * M F μ s χ z u 0 + M F μ s χ z u 1) := by
  rw [orbitalSobolevMomentCLM_translate F μ s hs χ z hz 1 hm g u]
  simp [M, Finset.sum_range_succ]

include hz in
/-- At a phase hit by just one of two factors, the first moment of their
difference product need not vanish. Its exact value detects the simple root. -/
theorem orbitalSobolevMoment_two_differences_first (g h : G F) (u : Lp ℂ 2 μ)
    (hm : ((1 : ℕ) : ℝ) < (s - 1) / 2) (hg : orbitalMomentPhase F χ z g = 1) :
    let v := u - T F μ s hs h u
    M F μ s χ z (v - T F μ s hs g v) 1 =
      -(logNorm F g : ℂ) * (1 - orbitalMomentPhase F χ z h) * M F μ s χ z u 0 := by
  intro v
  have h0 : ((0 : ℕ) : ℝ) < (s - 1) / 2 := (by norm_num : ((0 : ℕ) : ℝ) < ((1 : ℕ) : ℝ)).trans hm
  let L₀ := orbitalSobolevMomentCLM F μ s hs χ z hz 0 h0
  let L₁ := orbitalSobolevMomentCLM F μ s hs χ z hz 1 hm
  have hL₀ (x) : L₀ x = M F μ s χ z x 0 := orbitalSobolevMomentCLM_apply F μ s hs χ z hz 0 h0 x
  have hL₁ (x) : L₁ x = M F μ s χ z x 1 := orbitalSobolevMomentCLM_apply F μ s hs χ z hz 1 hm x
  have hv : M F μ s χ z v 0 = (1 - orbitalMomentPhase F χ z h) * M F μ s χ z u 0 := by
    rw [← hL₀ v]
    dsimp only [v]
    rw [map_sub, orbitalSobolevMomentCLM_translate_zero F μ s hs χ z hz h0 h u, hL₀ u]
    ring
  rw [← hL₁ (v - T F μ s hs g v), map_sub,
    orbitalSobolevMomentCLM_translate_one F μ s hs χ z hz hm g v, hL₁ v, hg, one_mul, hv]
  ring

end
end Masullo
