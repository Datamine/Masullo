import HeckePerronEdgeEstimates
import HeckePerronError
import GlobalHeckeResidues

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical Interval NumberField Topology

namespace Masullo

noncomputable section

/-- The exponential divided difference with its value at the removable
singularity, expressed in the displacement from the norm-twist pole. -/
def perronExponentialDifference (x : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then (Real.log x : ℂ) else (Complex.exp ((Real.log x : ℂ) * w) - 1) / w

theorem analyticAt_perronExponentialDifference (x : ℝ) (w : ℂ) :
    AnalyticAt ℂ (perronExponentialDifference x) w := by
  let E (z : ℂ) := Complex.exp ((Real.log x : ℂ) * z)
  have hE (z : ℂ) : AnalyticAt ℂ E z := by dsimp [E]; fun_prop
  by_cases h : w = 0
  · subst w
    obtain ⟨R, hR, hEq⟩ := (hE 0).exists_eventuallyEq_sum_add_pow_mul 1
    have he : E =ᶠ[𝓝 (0 : ℂ)] fun z ↦ 1 + z * R z := by
      filter_upwards [hEq] with z hz
      simpa [E, Finset.sum_range_one] using hz
    have hDer : HasDerivAt (fun z ↦ 1 + z * R z) (R 0) 0 := by
      simpa using (((hasDerivAt_id' (0 : ℂ)).mul hR.differentiableAt.hasDerivAt).const_add 1)
    have hDerE : HasDerivAt E (Real.log x : ℂ) 0 := by
      simpa [E] using (((hasDerivAt_id' (0 : ℂ)).const_mul (Real.log x : ℂ)).cexp)
    have h0 : R 0 = (Real.log x : ℂ) := (hDer.congr_of_eventuallyEq he).unique hDerE
    refine hR.congr ?_
    filter_upwards [he] with z hz
    by_cases hz₀ : z = 0
    · simp [hz₀, perronExponentialDifference, h0]
    · rw [perronExponentialDifference, ite_eq_right hz₀]
      change R z = (E z - 1) / z
      rw [hz, add_sub_cancel_left, mul_div_cancel_left₀ _ hz₀]
  · refine ((hE w).fun_sub (analyticAt_const (v := (1 : ℂ))) |>.fun_div analyticAt_id h).congr ?_
    filter_upwards [eventually_ne_nhds h] with z hz
    simp [perronExponentialDifference, E, hz]

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

theorem analyticAt_heckePerronFullSum (c : Place F → ℂ) (x : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun w ↦ heckePerronFullSum F c w x) s := by
  unfold heckePerronFullSum
  apply Finset.analyticAt_fun_sum
  intro j _
  unfold heckePrimePowerTerm
  apply analyticAt_const.fun_mul
  have hn : (((heckePrimePowerIdeal F j).absNorm : ℕ) : ℂ) ≠ 0 := by
    have hp : 0 < (heckePrimePowerIdeal F j).absNorm := by
      rw [heckePrimePowerIdeal, map_pow]
      exact pow_pos (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm j.1)) _
    exact_mod_cast hp.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

/-- The ideal-indexed twisted von Mangoldt function, supported on positive
prime powers. The prime-power presentation is unique. -/
def heckeIdealVonMangoldt (c : Place F → ℂ) (J : Ideal (𝓞 F)) : ℂ :=
  if h : ∃ j, heckePrimePowerIdeal F j = J then
    c h.choose.1 ^ (h.choose.2 + 1) * (Real.log (h.choose.1.asIdeal.absNorm : ℝ) : ℂ)
  else 0

/-- The nonzero ideals whose norms do not exceed the real cutoff. -/
def heckePerronIdealCutoff (x : ℝ) : Finset (Ideal (𝓞 F)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊x⌋₊).toFinset).filter (· ≠ ⊥)

/-- The prime-power polynomial equals the manuscript's sum over nonzero
ideals, with all terms outside the prime-power support equal to zero. -/
theorem heckePerronFullSum_eq_sum_ideals (c : Place F → ℂ) (s : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    heckePerronFullSum F c s x =
      ∑ J ∈ heckePerronIdealCutoff F x, heckeIdealVonMangoldt F c J * (J.absNorm : ℂ) ^ (-s) := by
  let D := (heckePrimePowerNormCutoff F (x + 1)).filter
    (fun j ↦ ((heckePrimePowerIdeal F j).absNorm : ℝ) ≤ x)
  let N (J : Ideal (𝓞 F)) := heckeIdealVonMangoldt F c J * (J.absNorm : ℂ) ^ (-s)
  have hD (j : Place F × ℕ) : j ∈ D ↔ ((heckePrimePowerIdeal F j).absNorm : ℝ) ≤ x := by
    rw [show j ∈ D ↔ _ from Finset.mem_filter, mem_heckePrimePowerNormCutoff]
    exact ⟨And.right, fun h ↦ ⟨h.trans_lt (lt_add_one _), h⟩⟩
  have hCut (J : Ideal (𝓞 F)) : J ∈ heckePerronIdealCutoff F x ↔
      (J.absNorm : ℝ) ≤ x ∧ J ≠ ⊥ := by
    rw [heckePerronIdealCutoff, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact and_congr_left' (Nat.le_floor_iff hx)
  have hterm (j : Place F × ℕ) : N (heckePrimePowerIdeal F j) = heckePrimePowerTerm F c s j := by
    have hj : ∃ k, heckePrimePowerIdeal F k = heckePrimePowerIdeal F j := ⟨j, rfl⟩
    have he : hj.choose = j := heckePrimePowerIdeal_injective F hj.choose_spec
    simp only [N, heckeIdealVonMangoldt, dite_eq_left hj, he, heckePrimePowerTerm]
  change ∑ j ∈ D, heckePrimePowerTerm F c s j = ∑ J ∈ heckePerronIdealCutoff F x, N J
  calc
    _ = ∑ j ∈ D, N (heckePrimePowerIdeal F j) :=
      Finset.sum_congr rfl fun j _ ↦ (hterm j).symm
    _ = ∑ J ∈ D.image (heckePrimePowerIdeal F), N J :=
      (Finset.sum_image (heckePrimePowerIdeal_injective F).injOn).symm
    _ = _ := by
      apply Finset.sum_subset
      · intro J hJ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJ
        refine (hCut _).mpr ⟨(hD _).mp hj, ?_⟩
        apply Ideal.absNorm_eq_zero_iff.not.mp
        rw [heckePrimePowerIdeal, map_pow]
        exact pow_ne_zero _ (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm j.1)).ne'
      · intro J hJ hn
        have he : ¬∃ j, heckePrimePowerIdeal F j = J := by
          rintro ⟨j, rfl⟩
          exact hn (Finset.mem_image.mpr ⟨j, (hD j).mpr ((hCut _).mp hJ).1, rfl⟩)
        simp only [N, heckeIdealVonMangoldt, dite_eq_right he, zero_mul]

/-- The cutoffs used in B.7.1.2, with separation stated pointwise over
the integer lattice. -/
def heckePerronAdmissibleCutoff (b x : ℝ) : Prop :=
  (∃ m : ℤ, x = (m : ℝ)) ∨ ∀ m : ℤ, b ≤ |x - (m : ℝ)|

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

private theorem perronRegularPart_at_eq {A R : ℂ → ℂ} {q : ℂ} {T : ℝ}
    (hT : 0 < T) (hA : AnalyticAt ℂ A q) (hR : AnalyticAt ℂ R q)
    (he : ∀ y ∈ Ioo (0 : ℝ) T, A (q + (y : ℂ) * I) = R (q + (y : ℂ) * I)) :
    A q = R q := by
  have hct : Continuous (fun y : ℝ ↦ q + (y : ℂ) * I) := by fun_prop
  have ht : Tendsto (fun y : ℝ ↦ q + (y : ℂ) * I) (𝓝[>] 0) (𝓝 q) := by
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) (hct.continuousAt (x := 0))
  have he' : (fun y : ℝ ↦ A (q + (y : ℂ) * I)) =ᶠ[𝓝[>] 0] fun y ↦ R (q + (y : ℂ) * I) :=
    Filter.Eventually.mono (Ioo_mem_nhdsGT hT) he
  exact tendsto_nhds_unique (hA.continuousAt.tendsto.comp ht)
    ((hR.continuousAt.tendsto.comp ht).congr' he'.symm)

private theorem perronTwist_model_of_ne {L A : ℂ → ℂ} {s q : ℂ} (x : ℝ) (hs : s ≠ q)
    (ha : -logDeriv L s = A s + 1 / (s - q)) :
    A s + perronExponentialDifference x (q - s) =
      -logDeriv L s + Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s) := by
  rw [perronExponentialDifference, ite_eq_right (sub_ne_zero.mpr (Ne.symm hs)), ha,
    show s - q = -(q - s) by ring, div_neg, sub_div]
  ring

set_option maxHeartbeats 650000 in
include μ hν in
/-- The right-edge approximation and the residue shift, with an analytic
model along the entire one-line, including the coincident-pole value. -/
theorem exists_manuscriptFiniteHecke_perron_model (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∃ A : ℂ → ℂ,
        (∀ s : ℂ, s.re = 1 → AnalyticAt ℂ A s) ∧
        (heckeNormOneRestriction F χ ≠ 1 → ∀ s : ℂ, s.re = 1 → A s = -logDeriv L s) ∧
        (heckeNormOneRestriction F χ = 1 →
          ∀ s : ℂ, s.re = 1 → s ≠ 1 + (t : ℂ) * I →
            -logDeriv L s = A s + 1 / (s - (1 + (t : ℂ) * I))) ∧
        ∀ (K b ε : ℝ), 0 < b → 0 < ε → ∀ᶠ x : ℝ in atTop,
          heckePerronAdmissibleCutoff b x → ∀ s : ℂ, s.re = 1 → |s.im| ≤ K →
          ‖heckePerronFullSum F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) s x -
            (A s + if heckeNormOneRestriction F χ = 1 then
              perronExponentialDifference x (1 + (t : ℂ) * I - s) else 0)‖ < ε := by
  obtain ⟨L, hL, he, hShift⟩ := exists_manuscriptFiniteHecke_perron_shift_eventually F ν η μ hν χ ht
  obtain ⟨B, hB, hPole, hBand⟩ := manuscriptFiniteHecke_perron_band F ν η μ hν χ ht hL he
  obtain ⟨B₁, hB₁, hResidue⟩ := manuscriptFiniteHecke_perron_residues F ν η μ hν χ ht hL he
  let q : ℂ := 1 + (t : ℂ) * I
  have hqre : q.re = 1 := by simp [q, Complex.add_re, Complex.mul_re]
  have honLine (s : ℂ) (hs : s.re = 1)
      (hc : heckeNormOneRestriction F χ ≠ 1 ∨ s ≠ q) : AnalyticAt ℂ L s ∧ L s ≠ 0 := by
    have hlog : 0 < Real.log (B * (|s.im| + 3)) := by
      apply Real.log_pos
      have h := le_mul_of_one_le_left (show 0 ≤ |s.im| + 3 by positivity) hB
      linarith [abs_nonneg s.im]
    apply hBand s (by rw [hs]; norm_num) _ hc
    rw [hs]
    exact sub_le_self _ (div_nonneg finiteHeckeZeroFreeNumerator_pos.le (by positivity))
  have hA : ∃ A : ℂ → ℂ,
      (∀ s : ℂ, s.re = 1 → AnalyticAt ℂ A s) ∧
      (heckeNormOneRestriction F χ ≠ 1 → ∀ s : ℂ, s.re = 1 → A s = -logDeriv L s) ∧
      (heckeNormOneRestriction F χ = 1 → ∀ s : ℂ, s.re = 1 → s ≠ q →
        -logDeriv L s = A s + 1 / (s - q)) := by
    by_cases hω : heckeNormOneRestriction F χ = 1
    · obtain ⟨A, ha, hEq⟩ := exists_analytic_negLogDeriv_simplePole_remainder
        (hL.meromorphicOn q (mem_univ _)) (hPole hω)
        (S := {s | s.re = 1}) (fun s hs hne ↦ honLine s hs (.inr hne))
      exact ⟨A, ha, fun h ↦ (h hω).elim, fun _ ↦ hEq⟩
    · refine ⟨fun s ↦ -logDeriv L s, fun s hs ↦ ?_, fun _ _ _ ↦ rfl, fun h ↦ (hω h).elim⟩
      obtain ⟨ha, hn⟩ := honLine s hs (.inl hω)
      exact analyticAt_neg_logDeriv ha hn
  obtain ⟨A, hA, hAn, hAt⟩ := hA
  refine ⟨L, hL, he, A, hA, hAn, hAt, fun K b ε hb hε ↦ ?_⟩
  let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
  have hRight := heckeContinuation_truncatedPerron_full_eventually F c
    (norm_heckeEulerCoefficient_le_one F χ _) L he (lt_min hb zero_lt_one) (half_pos hε)
  filter_upwards [hRight, hShift K B₁ (ε / 2) hB₁ (half_pos hε)] with x hh hg hx s hs hsim
  obtain ⟨hδ, hδ₁, hκ, hT, hqT, hwidth, hRest⟩ := hg s hs hsim
  let δ := (Real.sqrt (Real.log x))⁻¹
  let κ := (Real.log x)⁻¹
  let T := Real.log x ^ 3
  change 0 < δ at hδ
  change 0 < κ at hκ
  change 0 < T at hT
  let H (w : ℂ) := -logDeriv L (s + w)
  let model := A s + if heckeNormOneRestriction F χ = 1 then
    perronExponentialDifference x (q - s) else 0
  have hModel : rectIntegral (perronContourIntegrand x H) (-δ) κ (-T) T =
      (2 * Real.pi * I) * model := by
    obtain ⟨hn, hp⟩ := hResidue x s hs hδ hδ₁ hκ hT hwidth
    by_cases hω : heckeNormOneRestriction F χ = 1
    · obtain ⟨R, hR, hEq, hres⟩ := hp hω hqT
      have hres' : rectIntegral (perronContourIntegrand x H) (-δ) κ (-T) T =
          (2 * Real.pi * I) * (if q = s then R s + (Real.log x : ℂ)
            else -logDeriv L s + Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s)) := hres
      rw [hres']
      by_cases hqs : q = s
      · subst s
        have hmem (y : ℝ) (hy : y ∈ Ioo 0 T) :
            (y : ℂ) * I ∈ [[-δ, κ]] ×ℂ [[-T, T]] := by
          rw [Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, mem_Icc]
          exact ⟨⟨by linarith, hκ.le⟩, by constructor <;> linarith [hy.1, hy.2]⟩
        have hR0 : AnalyticAt ℂ R q := by
          have h0 : (0 : ℂ) ∈ [[-δ, κ]] ×ℂ [[-T, T]] := by
            rw [Complex.mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
            simp only [Complex.zero_re, Complex.zero_im, mem_Icc]
            exact ⟨⟨neg_nonpos.mpr hδ.le, hκ.le⟩, ⟨neg_nonpos.mpr hT.le, hT.le⟩⟩
          simpa using hR 0 h0
        have hev : A q = R q := perronRegularPart_at_eq hT (hA q hqre) hR0 (fun y hy ↦ by
          have hy₀ : (y : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hy.1.ne') Complex.I_ne_zero
          have hyq : q + (y : ℂ) * I ≠ q := by simpa using hy₀
          have hrey : (q + (y : ℂ) * I).re = 1 := by simp [hqre, Complex.add_re, Complex.mul_re]
          have ha := hAt hω _ hrey hyq
          have hr := hEq ((y : ℂ) * I) (hmem y hy) hyq
          exact add_right_cancel (ha.symm.trans hr))
        simp [model, hω, perronExponentialDifference, hev]
      · simp only [hqs, ite_false, model, hω, ite_true]
        rw [perronTwist_model_of_ne x (Ne.symm hqs) (hAt hω s hs (Ne.symm hqs))]
    · rw [hn hω]
      simp [model, hω, hAn hω s hs]
  have ha := hRest model hModel
  have hh' := hh (perronAdmissibleCutoff_separation hx) s hs
  let J := (∫ y in -T..T, perronContourIntegrand x H ((κ : ℂ) + (y : ℂ) * I)) / (2 * (Real.pi : ℂ))
  have ha' : ‖J - model‖ < ε / 2 := ha
  have hb' : ‖J - heckePerronFullSum F c s x‖ < ε / 2 := by
    simpa only [J, perronContourIntegrand, H, κ, T, mul_div_assoc] using hh'
  change ‖heckePerronFullSum F c s x - model‖ < ε
  refine (norm_sub_le_norm_sub_add_norm_sub _ J _).trans_lt ?_
  rw [norm_sub_rev (heckePerronFullSum F c s x) J]
  linarith

set_option maxHeartbeats 650000 in
include μ hν in
/-- Corrected B.7.1.2. The full prime-power polynomials on the one-line
have analytic remainders tending uniformly to zero on compact sets.
The norm-twist pole gives the oscillatory term away from the pole and
the logarithmic main term at coincidence. -/
theorem manuscriptFiniteHecke_perron_oneLine (χ : PontryaginDual (IdeleClass F))
    {t : ℝ} (ht : HasHeckeHeight F χ t) :
    ∃ (L Z : ℂ → ℂ) (f : ℝ → ℂ → ℂ),
      MeromorphicNFOn L univ ∧ EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      MeromorphicOn Z univ ∧
      (∀ x : ℝ, ∀ s : ℂ, s.re = 1 → AnalyticAt ℂ (f x) s) ∧
      (∀ b > (0 : ℝ), ∀ S : Set ℂ, IsCompact S → S ⊆ {s | s.re = 1} →
        TendstoUniformlyOn f 0 (atTop ⊓ 𝓟 {x | heckePerronAdmissibleCutoff b x}) S) ∧
      let q : ℂ := 1 + (t : ℂ) * I
      let U (s : ℂ) (x : ℝ) :=
        heckePerronFullSum F (heckeEulerCoefficient F χ (chosenFiniteUniformizer F)) s x
      (heckeNormOneRestriction F χ ≠ 1 →
        ∀ x > (1 : ℝ), ∀ s : ℂ, s.re = 1 → U s x = -logDeriv L s + f x s) ∧
      (heckeNormOneRestriction F χ = 1 →
        EqOn Z (dedekindZeta F) {z | 1 < z.re} ∧
        (∀ x > (1 : ℝ), ∀ s : ℂ, s.re = 1 → s ≠ q →
          U s x = -logDeriv Z (s - (t : ℂ) * I) +
            Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s) + f x s) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ‖U q x - (Real.log x : ℂ)‖ ≤ C) := by
  obtain ⟨L, hL, he, A, hA, hAn, hAt, hLim⟩ :=
    exists_manuscriptFiniteHecke_perron_model F ν η μ hν χ ht
  let q : ℂ := 1 + (t : ℂ) * I
  let shift : ℂ := (t : ℂ) * I
  let Z (z : ℂ) := L (z + shift)
  let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
  let P (x : ℝ) (s : ℂ) := A s + if heckeNormOneRestriction F χ = 1 then
    perronExponentialDifference x (q - s) else 0
  let f (x : ℝ) (s : ℂ) := heckePerronFullSum F c s x - P x s
  have hq : q.re = 1 := by simp [q, Complex.add_re, Complex.mul_re]
  have hZ : MeromorphicOn Z univ := fun z _ ↦
    (hL.meromorphicOn (z + shift) (mem_univ _)).comp_analyticAt
      (g := fun w : ℂ ↦ w + shift) (analyticAt_id.fun_add analyticAt_const)
  refine ⟨L, Z, f, hL, he, hZ, ?_, ?_, ?_⟩
  · intro x s hs
    have hP : AnalyticAt ℂ (P x) s := by
      apply (hA s hs).fun_add
      by_cases hω : heckeNormOneRestriction F χ = 1
      · simp only [hω, ite_true]
        exact (analyticAt_perronExponentialDifference x (q - s)).comp
          (f := fun z : ℂ ↦ q - z) (analyticAt_const.fun_sub analyticAt_id)
      · simp only [hω, ite_false]
        exact analyticAt_const
    exact (analyticAt_heckePerronFullSum F c x s).fun_sub hP
  · intro b hb S hS hline
    obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [eventually_inf_principal]
    filter_upwards [hLim K b ε hb hε] with x hx hxb s hs
    have hr : s.re = 1 := hline hs
    have hi : |s.im| ≤ K := by simpa only [Real.norm_eq_abs] using hK s hs
    simpa only [Pi.zero_apply, dist_zero_left, f, P, q] using hx hxb s hr hi
  · dsimp only
    constructor
    · intro hω x _ s hs
      have h := hAn hω s hs
      simp only [f, P, hω, ite_false, add_zero, h]
      ring
    · intro hω
      have heZ : EqOn Z (dedekindZeta F) {z | 1 < z.re} := by
        intro z hz
        have hr : 1 < (z + shift).re := by simpa [shift, Complex.add_re, Complex.mul_re] using hz
        change L (z + shift) = _
        rw [he hr, manuscriptFiniteHeckeEuler_shift F χ ht, hω]
        simpa only [shift, add_sub_cancel_right] using globalFiniteHeckeEuler_trivial_eq_dedekindZeta F hz
      refine ⟨heZ, ?_, ?_⟩
      · intro x _ s hs hsne
        have hZder : logDeriv Z (s - shift) = logDeriv L s := by
          simp only [Z, logDeriv_apply, deriv_comp_add_const, sub_add_cancel]
        have hP : P x s = -logDeriv L s +
            Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s) := by
          simpa only [P, hω, ite_true] using perronTwist_model_of_ne x hsne (hAt hω s hs hsne)
        change heckePerronFullSum F c s x = -logDeriv Z (s - shift) +
          Complex.exp ((Real.log x : ℂ) * (q - s)) / (q - s) + f x s
        rw [hZder, ← hP]
        dsimp only [f]
        ring
      · let C := 1 + ‖A q‖ + Real.log 2
        refine ⟨C, by dsimp [C]; positivity, ?_⟩
        have hN : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
        filter_upwards [hN.eventually (hLim |q.im| 1 1 zero_lt_one zero_lt_one),
          hN.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with x hx hn hx₁
        let n : ℝ := (⌊x⌋₊ : ℕ)
        have hn' : 1 ≤ n := hn
        have hAdm : heckePerronAdmissibleCutoff 1 n := by
          left
          exact ⟨(⌊x⌋₊ : ℤ), by simp [n]⟩
        have hlim : ‖heckePerronFullSum F c q n - (A q + (Real.log n : ℂ))‖ < 1 := by
          simpa only [hω, ite_true, q, sub_self, perronExponentialDifference] using
            hx hAdm q hq le_rfl
        have hflo : n ≤ x := Nat.floor_le (zero_le_one.trans hx₁)
        have hxx : x ≤ 2 * n := by
          have hxx : x < n + 1 := Nat.lt_floor_add_one x
          linarith
        have hlog : 0 ≤ Real.log x - Real.log n :=
          sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hn') hflo)
        have hlog' : Real.log x - Real.log n ≤ Real.log 2 := by
          have hh := Real.log_le_log (zero_lt_one.trans_le hx₁) hxx
          rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hn').ne'] at hh
          linarith
        have hnLog : ‖(Real.log n : ℂ) - (Real.log x : ℂ)‖ ≤ Real.log 2 := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hlog]
          exact hlog'
        change ‖heckePerronFullSum F c q x - (Real.log x : ℂ)‖ ≤ C
        rw [heckePerronFullSum_floor F c q (zero_le_one.trans hx₁)]
        change ‖heckePerronFullSum F c q n - (Real.log x : ℂ)‖ ≤ C
        refine (norm_sub_le_norm_sub_add_norm_sub _ (A q + (Real.log n : ℂ)) _).trans ?_
        have hrest : ‖A q + (Real.log n : ℂ) - (Real.log x : ℂ)‖ ≤ ‖A q‖ + Real.log 2 := by
          rw [add_sub_assoc]
          exact (norm_add_le _ _).trans (add_le_add le_rfl hnLog)
        dsimp only [C]
        linarith

end

end Masullo
