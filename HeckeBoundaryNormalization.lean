import HeckeBoundaryModelAnalytic

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- The signed cutoff correction is dominated by the actual unweighted
tail of higher prime powers at the real part of the spectral parameter. -/
theorem norm_heckeHigherPrimePowerCrossover_le_tail (c : Place F → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (x : ℝ) {s : ℂ} (hs : 1/2 < s.re) :
    ‖heckeHigherPrimePowerCrossover F c x s‖ ≤
      ∑' j : Place F × ℕ, if j ∉ heckeHigherPrimePowerCutoff F x then
        ‖heckeHigherPrimePowerLog F (fun _ ↦ 1) (s.re : ℂ) j‖ else 0 := by
  let u (j : Place F × ℕ) := if j.1 ∈ heckePrimeNormCutoff F x ∧ j ∉ heckeHigherPrimePowerCutoff F x
    then heckeHigherPrimePowerLog F c s j else 0
  let v (j : Place F × ℕ) := ‖heckeHigherPrimePowerLog F (fun _ ↦ 1) (s.re : ℂ) j‖
  let w (j : Place F × ℕ) := if j ∉ heckeHigherPrimePowerCutoff F x then v j else 0
  have hv : Summable v := summable_norm_heckeHigherPrimePowerLog F _ (by simp)
    (by simpa only [Complex.ofReal_re] using hs)
  have hw : Summable w := hv.of_nonneg_of_le (fun j ↦ by dsimp [w, v]; split <;> positivity)
    (fun j ↦ by dsimp only [w]; split; exact le_rfl; exact norm_nonneg _)
  have hmaj (j : Place F × ℕ) : ‖u j‖ ≤ w j := by
    by_cases hQ : j ∈ heckeHigherPrimePowerCutoff F x
    · simp [u, w, hQ]
    · by_cases hp : j.1 ∈ heckePrimeNormCutoff F x
      · rw [show u j = heckeHigherPrimePowerLog F c s j by simp [u, hp, hQ],
          show w j = v j by simp [w, hQ]]
        have hnorm : 0 < (heckePrimePowerIdeal F (j.1, j.2+1)).absNorm := by
          rw [heckePrimePowerIdeal, map_pow]
          exact pow_pos (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm j.1)) _
        dsimp only [v, heckeHigherPrimePowerLog]
        simp only [norm_mul, norm_div, norm_pow, norm_one, one_pow, Complex.norm_natCast,
          Complex.norm_natCast_cpow_of_pos hnorm, Complex.neg_re, Complex.ofReal_re]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (hc _)) (by positivity)) (Real.rpow_nonneg (by positivity) _)
      · simp [u, w, v, hp, hQ]
  have hu := hw.of_nonneg_of_le (fun j ↦ norm_nonneg (u j)) hmaj
  exact (norm_tsum_le_tsum_norm hu).trans (hu.tsum_le_tsum hmaj hw)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

set_option maxHeartbeats 550000 in
include μ hν in
/-- Corrected B.7.2.4. The explicit norm-twist model is analytic off its
pole, and the normalized products have the indicated uniform expansion. -/
theorem manuscriptFiniteHecke_boundary_normalization (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) (D : Set ℂ) (hD : IsCompact D)
    (hsub : D ⊆ heckeBoundaryDomain F χ t) :
    let q : ℂ := 1 + (t : ℂ) * I
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    let H (x : ℝ) (s : ℂ) := -heckeHigherPrimePowerCrossover F c x s
    let w := heckeBoundaryLogWeight
    ∃ (L : ℂ → ℂ) (R G : ℝ → ℂ → ℂ),
      MeromorphicNFOn L univ ∧ EqOn L (manuscriptFiniteHeckeEuler F χ) {s | 1 < s.re} ∧
      TendstoUniformlyOn (fun x s ↦ heckeReciprocalPartial F c x s * L s) (fun _ ↦ 1) atTop D ∧
      (∀ x ≥ (3 : ℝ), ContinuousOn (R x) D ∧
        ∀ s ∈ D, heckeReciprocalPartial F c x s * L s = Complex.exp (R x s + G x s + H x s)) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ x : ℝ in atTop, ∀ s ∈ D, ‖R x s‖ < 2 * ε / Real.log x) ∧
      (heckeNormOneRestriction F χ ≠ 1 → ∀ x s, G x s = 0) ∧
      (heckeNormOneRestriction F χ = 1 →
        let g (n : ℕ) (s : ℂ) := perronExponentialDifference (n : ℝ) (q - s)
        (∀ x ≥ (3 : ℝ), ∀ s, s.re = 1 → s ≠ q →
          AnalyticAt ℂ (G x) s ∧
          let p := ⌈x⌉₊ - 3
          G x s = -(w p • g (p+2) s) +
            ∑' k, (w (p+k) - w (p+k+1)) • g (p+k+2) s) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ (3 : ℝ),
          let p := ⌈x⌉₊ - 3
          let d (k : ℕ) (s : ℂ) := (w (p+k) - w (p+k+1)) • g (p+k+2) s
          TendstoUniformlyOn (fun N s ↦ ∑ k ∈ Finset.range N, d k s)
            (fun s ↦ ∑' k, d k s) atTop D ∧
          ∀ s ∈ D, ‖G x s‖ ≤ C / Real.log x) ∧
      TendstoUniformlyOn H (fun _ ↦ 0) atTop {s | 1 ≤ s.re} ∧
      ∀ (x : ℝ) (s : ℂ), 1/2 < s.re → ‖H x s‖ ≤
        ∑' j : Place F × ℕ, if j ∉ heckeHigherPrimePowerCutoff F x then
          ‖heckeHigherPrimePowerLog F (fun _ ↦ 1) (s.re : ℂ) j‖ else 0 := by
  intro q c H w
  obtain ⟨L, R, hL, he, hN, hRc, hformula, hRate⟩ :=
    manuscriptFiniteHecke_boundary_normalization_formula F ν η μ hν χ ht D hD hsub
  choose A hAna hEq using exists_analytic_perronBoundaryModel
  let G (x : ℝ) (s : ℂ) :=
    if heckeNormOneRestriction F χ = 1 then A (⌈x⌉₊ - 3) (q-s) else 0
  have hqre : q.re = 1 := by simp [q, Complex.add_re, Complex.mul_re]
  have hcoord (s : ℂ) (hs : s.re = 1) (hne : s ≠ q) :
      (q-s).re = 0 ∧ (q-s).im ≠ 0 := by
    have hr : (q-s).re = 0 := by rw [Complex.sub_re, hqre, hs, sub_self]
    exact ⟨hr, fun h ↦ hne (Complex.ext (by rw [hs, hqre])
      (sub_eq_zero.mp (by simpa only [Complex.sub_im] using h)).symm)⟩
  have hwhen (hω : heckeNormOneRestriction F χ = 1) (x : ℝ) (s : ℂ) (hs : s.re = 1)
      (hne : s ≠ q) :
      let p := ⌈x⌉₊ - 3
      G x s = -(w p • perronExponentialDifference (((p+2 : ℕ) : ℝ)) (q-s)) +
        ∑' k, (w (p+k) - w (p+k+1)) • perronExponentialDifference (((p+k+2 : ℕ) : ℝ)) (q-s) := by
    simp only [G, hω, ite_true]
    exact hEq _ (q-s) (hcoord s hs hne).1.le (sub_ne_zero.mpr (Ne.symm hne))
  have hc : ∀ v, ‖c v‖ ≤ 1 := norm_heckeEulerCoefficient_le_one F χ _
  refine ⟨L, R, G, hL, he, hN, ?_, hRate, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨hRc x hx, fun s hs ↦ ?_⟩
    have heq := (hformula x hx s hs).2
    by_cases hω : heckeNormOneRestriction F χ = 1
    · have hsne := (hsub hs).2.resolve_left (not_not.mpr hω)
      rw [hwhen hω x s (hsub hs).1 hsne, heq]
      simp only [hω, ite_true, H, sub_eq_add_neg]
      rfl
    · rw [heq]
      simp [hω, G, H, c, sub_eq_add_neg]
  · intro hω x s
    simp [G, hω]
  · intro hω g
    constructor
    · intro x _ s hs hne
      refine ⟨?_, hwhen hω x s hs hne⟩
      simp only [G, hω, ite_true]
      exact (hAna _ (q-s) ((hcoord s hs hne).1.trans_lt (by norm_num)) (hcoord s hs hne).2).comp
        (f := fun z : ℂ ↦ q - z) (analyticAt_const.fun_sub analyticAt_id)
    · have hline : D ⊆ {s | s.re = 1} := fun _ hs ↦ (hsub hs).1
      have hDq : q ∉ D := fun h ↦ ((hsub h).2.resolve_left (not_not.mpr hω)) rfl
      obtain ⟨C, hC, hBound⟩ := perronBoundaryModel_uniform_bound hD hqre hDq hline
      refine ⟨C, hC, fun x hx ↦ ?_⟩
      refine ⟨(hBound x hx).1, fun s hs ↦ ?_⟩
      rw [hwhen hω x s (hline hs) ((hsub hs).2.resolve_left (not_not.mpr hω))]
      exact (hBound x hx).2 s hs
  · have h := (heckeHigherPrimePowerCrossover_tendstoUniformlyOn F c hc (a := 1) (by norm_num))
    have hzero : -(fun _ : ℂ ↦ (0 : ℂ)) = fun _ ↦ 0 := funext fun _ ↦ neg_zero
    have hneg : -heckeHigherPrimePowerCrossover F c = H := funext fun _ ↦ funext fun _ ↦ rfl
    simpa only [hzero, hneg] using h.neg
  · intro x s hs
    rw [show H x s = -heckeHigherPrimePowerCrossover F c x s from rfl, norm_neg]
    exact norm_heckeHigherPrimePowerCrossover_le_tail F c hc x hs

end

end Masullo
