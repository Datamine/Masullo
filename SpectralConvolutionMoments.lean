import HardySobolevTranslations
import HardySobolevEvaluation

open Filter Function MeasureTheory Set Topology
open scoped CompactlySupported ENNReal

namespace Masullo

noncomputable section

section Moment

variable {G : Type*} [CommGroup G]

/-- The Haar moment before putting the reciprocal density into its L² vector. -/
def spectralHaarMoment (ℓ : G →* Multiplicative ℝ) (χ : G →* ℂ) (z : ℂ) (n : ℕ) (x : G) : ℂ :=
  χ x * mellinEvaluationKernel n z (ℓ x).toAdd

theorem spectralHaarMoment_mul (ℓ : G →* Multiplicative ℝ) (χ : G →* ℂ) (z : ℂ)
    (n : ℕ) (g x : G) :
    spectralHaarMoment ℓ χ z n (g * x) =
      ∑ j : Fin (n + 1), (n.choose j : ℂ) * spectralHaarMoment ℓ χ z (n - j) g *
        spectralHaarMoment ℓ χ z j x := by
  unfold spectralHaarMoment mellinEvaluationKernel
  have hℓ : (ℓ (g * x)).toAdd = (ℓ x).toAdd + (ℓ g).toAdd := by
    rw [mul_comm, map_mul, toAdd_mul]
  rw [hℓ, Complex.ofReal_add, mul_add, Complex.exp_add, map_mul, add_pow]
  let t (j : ℕ) : ℂ := (n.choose j : ℂ) *
    (χ g * (Complex.exp (z * ((ℓ g).toAdd : ℂ)) * ((ℓ g).toAdd : ℂ) ^ (n - j))) *
    (χ x * (Complex.exp (z * ((ℓ x).toAdd : ℂ)) * ((ℓ x).toAdd : ℂ) ^ j))
  change _ = ∑ j : Fin (n + 1), t j
  rw [Fin.sum_univ_eq_sum_range t]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [t]
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G] [R1Space G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  (ℓ : G →* Multiplicative ℝ) (χ : G →* ℂ) (z : ℂ) (l r s : ℝ)

/-- The physical dual moment in the positive-amplitude Hilbert chart. -/
def spectralChartMoment (n : ℕ) (x : G) : ℂ :=
  spectralHaarMoment ℓ χ z n x / (hardySobolevAmplitude l r s (ℓ x).toAdd : ℂ)

/-- Bilinear pairing with the moment vector in the amplitude chart. -/
def spectralMomentFunctional (n : ℕ)
    (h : MemLp (spectralChartMoment ℓ χ z l r s n) 2 μ) : StrongDual ℂ (Lp ℂ 2 μ) :=
  sobolevBilinearDual μ (h.toLp _)

omit [TopologicalSpace G] [IsTopologicalGroup G] [R1Space G] [BorelSpace G]
  [μ.IsMulLeftInvariant] in
theorem spectralMomentFunctional_apply (n : ℕ)
    (h : MemLp (spectralChartMoment ℓ χ z l r s n) 2 μ) (f : Lp ℂ 2 μ) :
    spectralMomentFunctional μ ℓ χ z l r s n h f =
      ∫ x, f x * spectralChartMoment ℓ χ z l r s n x ∂μ := by
  rw [spectralMomentFunctional, sobolevBilinearDual_apply]
  exact integral_congr_ae (h.coeFn_toLp.mono fun x hx => congrArg (f x * ·) hx)

private theorem hardySobolevAmplitude_ne_zero (x : ℝ) :
    (hardySobolevAmplitude l r s x : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  unfold hardySobolevAmplitude hardySobolevWeight
  exact (Real.sqrt_pos.2 (mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _))).ne'

omit [R1Space G] in
/-- The transpose of translation acts triangularly on the log moments.
All terms are paired in the actual ambient positive-amplitude Hilbert chart. -/
theorem spectralMomentFunctional_translate (hc : Continuous ℓ) (hs : 0 ≤ s)
    (n : ℕ) (h : ∀ j : Fin (n + 1), MemLp (spectralChartMoment ℓ χ z l r s j) 2 μ)
    (g : G) (u : Lp ℂ 2 μ) :
    spectralMomentFunctional μ ℓ χ z l r s n (h (Fin.last n))
        (hardySobolevMulTranslation μ ℓ hc l r s hs g u) =
      ∑ j : Fin (n + 1), (n.choose j : ℂ) * spectralHaarMoment ℓ χ z (n - j) g *
        spectralMomentFunctional μ ℓ χ z l r s j (h j) u := by
  let a (x : G) := (hardySobolevAmplitude l r s (ℓ x).toAdd : ℂ)
  let T := hardySobolevMulTranslation μ ℓ hc l r s hs g
  simp only [spectralMomentFunctional_apply]
  calc
    _ = ∫ x, u x * (spectralHaarMoment ℓ χ z n (g * x) / a x) ∂μ := by
      rw [← integral_mul_left_eq_self (fun x => T u x * spectralChartMoment ℓ χ z l r s n x) g]
      apply integral_congr_ae
      filter_upwards [(measurePreserving_mul_left μ g).quasiMeasurePreserving.ae
        (hardySobolevMulTranslation_ae μ ℓ hc l r s hs g u)] with x hx
      rw [hx, inv_mul_cancel_left, Complex.ofReal_div, spectralChartMoment]
      change (a (g * x) / a x * u x) * (spectralHaarMoment ℓ χ z n (g * x) / a (g * x)) = _
      field_simp [a, hardySobolevAmplitude_ne_zero l r s]
    _ = ∫ x, ∑ j : Fin (n + 1), (n.choose j : ℂ) * spectralHaarMoment ℓ χ z (n - j) g *
        (u x * spectralChartMoment ℓ χ z l r s j x) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [spectralHaarMoment_mul, Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        unfold spectralChartMoment
        dsimp only [a]
        ring
    _ = _ := by
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro j hj
        exact (MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp u) (h j)).const_mul _

variable [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

/-- The scalar entries of the convolution jet matrix are the Mellin moments
of the test, with the binomial coefficient supplied by translation. -/
theorem spectralMomentFunctional_convolution (hc : Continuous ℓ) (hχ : Continuous χ)
    (hs : 0 ≤ s) (φ : C_c(G, ℂ))
    (n : ℕ) (h : ∀ j : Fin (n + 1), MemLp (spectralChartMoment ℓ χ z l r s j) 2 μ)
    (u : Lp ℂ 2 μ) :
    spectralMomentFunctional μ ℓ χ z l r s n (h (Fin.last n))
        (hardySobolevConvolution μ ℓ hc l r s hs φ u) =
      ∑ j : Fin (n + 1), (n.choose j : ℂ) *
        (∫ g, φ g * spectralHaarMoment ℓ χ z (n - j) g ∂μ) *
        spectralMomentFunctional μ ℓ χ z l r s j (h j) u := by
  let L := spectralMomentFunctional μ ℓ χ z l r s n (h (Fin.last n))
  change L (∫ g, φ g • hardySobolevMulTranslation μ ℓ hc l r s hs g u ∂μ) = _
  rw [← L.integral_comp_comm (integrable_hardySobolev_convolution_orbit μ ℓ hc l r s hs φ u)]
  let c (j : Fin (n + 1)) (g : G) := φ g * spectralHaarMoment ℓ χ z (n - j) g
  have hi (j : Fin (n + 1)) : Integrable (c j) μ := by
    have hlog : Continuous (fun x => (ℓ x).toAdd) := continuous_toAdd.comp hc
    have hker : Continuous (mellinEvaluationKernel (n - (j : ℕ)) z) := by
      unfold mellinEvaluationKernel
      fun_prop
    exact (φ.continuous.mul (hχ.mul (hker.comp hlog))).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  calc
    _ = ∫ g, ∑ j : Fin (n + 1), c j g * ((n.choose j : ℂ) *
        spectralMomentFunctional μ ℓ χ z l r s j (h j) u) ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun g => ?_
      change L (φ g • hardySobolevMulTranslation μ ℓ hc l r s hs g u) = _
      rw [map_smul]
      change φ g * L (hardySobolevMulTranslation μ ℓ hc l r s hs g u) = _
      rw [spectralMomentFunctional_translate μ ℓ χ z l r s hc hs n h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [c]
      ring
    _ = _ := by
      rw [integral_finsetSum]
      · simp only [integral_mul_const, c]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · exact fun j _ => (hi j).mul_const _

/-- A vector biorthogonal to the log moments singles out the order-zero
Mellin coefficient on the diagonal of convolution. -/
theorem spectralMomentFunctional_convolution_diagonal
    (hc : Continuous ℓ) (hχ : Continuous χ) (hs : 0 ≤ s) (φ : C_c(G, ℂ))
    (n : ℕ) (h : ∀ j : Fin (n + 1), MemLp (spectralChartMoment ℓ χ z l r s j.val) 2 μ)
    (u : Lp ℂ 2 μ)
    (hdiag : ∀ j : Fin (n + 1), spectralMomentFunctional μ ℓ χ z l r s j.val (h j) u =
      if j = Fin.last n then 1 else 0) :
    spectralMomentFunctional μ ℓ χ z l r s n (h (Fin.last n))
        (hardySobolevConvolution μ ℓ hc l r s hs φ u) =
      ∫ g, φ g * spectralHaarMoment ℓ χ z 0 g ∂μ := by
  rw [spectralMomentFunctional_convolution μ ℓ χ z l r s hc hχ hs φ n h,
    Finset.sum_eq_single (Fin.last n)]
  · rw [hdiag (Fin.last n)]
    simp only [Fin.val_last, Nat.choose_self, Nat.cast_one, Nat.sub_self, ite_true,
      one_mul, mul_one]
  · intro j hj hn
    simp only [hdiag j, hn, ite_false, mul_zero]
  · simp

/-- A homogeneous test makes the image of its convolution lie in the
corresponding translation isotype. -/
theorem hardySobolevConvolution_homogeneous_image (hc : Continuous ℓ) (hs : 0 ≤ s)
    (φ : C_c(G, ℂ)) (k : G) (c : ℂ) (hφ : ∀ g, φ (k⁻¹ * g) = c * φ g)
    (u : Lp ℂ 2 μ) :
    hardySobolevMulTranslation μ ℓ hc l r s hs k
        (hardySobolevConvolution μ ℓ hc l r s hs φ u) =
      c • hardySobolevConvolution μ ℓ hc l r s hs φ u := by
  let T g := hardySobolevMulTranslation μ ℓ hc l r s hs g
  change T k (∫ g, φ g • T g u ∂μ) = c • ∫ g, φ g • T g u ∂μ
  rw [← (T k).integral_comp_comm (integrable_hardySobolev_convolution_orbit μ ℓ hc l r s hs φ u)]
  let p (g : G) := T k (φ g • T g u)
  change (∫ g, p g ∂μ) = c • ∫ g, φ g • T g u ∂μ
  rw [← integral_mul_left_eq_self p k⁻¹, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun g => by
    change T k (φ (k⁻¹ * g) • T (k⁻¹ * g) u) = c • (φ g • T g u)
    rw [map_smul, ← hardySobolevMulTranslation_mul μ ℓ hc l r s hs,
      mul_inv_cancel_left, hφ, mul_smul]

end Moment

section HomogeneousMoment

variable {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]

/-- A Mellin coefficient of a homogeneous test vanishes on every different
character of the norm-one subgroup. -/
theorem spectralHaarMoment_integral_eq_zero_of_homogeneous
    (ℓ : G →* Multiplicative ℝ) (χ : G →* ℂ) (z : ℂ) (n : ℕ)
    (φ : G → ℂ) (k : G) (hℓ : ℓ k = 1) (c : ℂ)
    (hφ : ∀ g, φ (k⁻¹ * g) = c * φ g) (hne : χ k ≠ c) :
    (∫ g, φ g * spectralHaarMoment ℓ χ z n g ∂μ) = 0 := by
  let J := ∫ g, φ g * spectralHaarMoment ℓ χ z n g ∂μ
  have hlog (g : G) : ℓ (k⁻¹ * g) = ℓ g := by simp [hℓ]
  have hχ : χ k * χ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h : χ k * J = c * J := calc
    _ = χ k * ∫ g, φ (k⁻¹ * g) * spectralHaarMoment ℓ χ z n (k⁻¹ * g) ∂μ := by
      congr 1
      exact (integral_mul_left_eq_self (fun g => φ g * spectralHaarMoment ℓ χ z n g) k⁻¹).symm
    _ = _ := by
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun g => by
        simp only [spectralHaarMoment, hlog, hφ, map_mul]
        calc
          _ = (χ k * χ k⁻¹) * (c * (φ g * (χ g * mellinEvaluationKernel n z (ℓ g).toAdd))) := by ring
          _ = _ := by rw [hχ, one_mul]
  exact (mul_eq_zero.mp (show (χ k - c) * J = 0 by rw [sub_mul, h, sub_self])).resolve_left
    (sub_ne_zero.mpr hne)

end HomogeneousMoment

/-- A diagonal calculation descends through a surjective intertwining map. -/
theorem quotient_diagonal_of_ambient {X Y : Type*} (q : X → Y) (hq : Surjective q)
    (A : X → X) (B : Y → Y) (hAB : ∀ x, q (A x) = B (q x))
    (n : ℕ) (L : Fin (n + 1) → X → ℂ) (f : Fin (n + 1) → Y → ℂ)
    (hcompat : ∀ j x, f j (q x) = L j x)
    (c : ℂ) (hdiag : ∀ x,
      (∀ j, L j x = if j = Fin.last n then 1 else 0) → L (Fin.last n) (A x) = c)
    (v : Y) (hv : ∀ j, f j v = if j = Fin.last n then 1 else 0) :
    f (Fin.last n) (B v) = c := by
  obtain ⟨u, rfl⟩ := hq v
  rw [← hAB, hcompat]
  apply hdiag
  intro j
  exact (hcompat j u).symm.trans (hv j)

end

end Masullo
