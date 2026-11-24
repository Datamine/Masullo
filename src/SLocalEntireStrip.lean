import SLocalZetaRadialDerivative
import SLocalFlatComponents
import FiniteEulerRecurrence
import Mathlib.Analysis.Complex.PhragmenLindelof

open Bornology Filter Metric Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

/-- Uniform bounds on the vertical boundaries and on horizontal segments
escaping in both directions bound a holomorphic function throughout the strip. -/
private theorem entire_norm_le_of_sparse_strip_boundary {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) {a b C : ℝ} (hab : a < b)
    (hside : ∀ z : ℂ, z.re = a ∨ z.re = b → ‖G z‖ ≤ C)
    (T : ℤ → ℝ) (htop : Tendsto T atTop atTop) (hbot : Tendsto T atBot atBot)
    (hcross : ∀ k : ℤ, ∀ z : ℂ, z.re ∈ Icc a b → z.im = T k → ‖G z‖ ≤ C)
    (z : ℂ) (hz : z.re ∈ Icc a b) : ‖G z‖ ≤ C := by
  obtain ⟨k, hk⟩ := (hbot.eventually (eventually_lt_atBot z.im)).exists
  obtain ⟨j, hj⟩ := (htop.eventually (eventually_gt_atTop z.im)).exists
  let R := Ioo a b ×ℂ Ioo (T k) (T j)
  have hkj : T k < T j := hk.trans hj
  have hR : IsBounded R := (isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)
  have hc : z ∈ closure R := by
    rw [show closure R = Icc a b ×ℂ Icc (T k) (T j) from by
      dsimp only [R]
      rw [Complex.closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hkj.ne]]
    exact ⟨hz, hk.le, hj.le⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le hR hG.diffContOnCl _ hc
  intro w hw
  change w ∈ frontier (Ioo a b ×ℂ Ioo (T k) (T j)) at hw
  rw [Complex.frontier_reProdIm, frontier_Ioo hab, frontier_Ioo hkj,
    closure_Ioo hab.ne, closure_Ioo hkj.ne] at hw
  rcases hw with he | he
  · rcases (show w.im = T k ∨ w.im = T j from by simpa using he.2) with h | h
    · exact hcross k w he.1 h
    · exact hcross j w he.1 h
  · exact hside w (by simpa using he.1)

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev PhaseFamily := ∀ v : S, (v.val.adicCompletion F)ˣ →ₜ* Circle

/-- Recurrent horizontal edges keep the reciprocal of the selected finite Euler denominator bounded. -/
theorem sLocalFiniteZetaDenominator_bounded_inverse_strip_sequence
    (χ : PhaseFamily F S) {a b : ℝ} (hab : a ≤ b) :
    ∃ (C : ℝ) (T : ℤ → ℝ), 0 < C ∧ Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k z, z.re ∈ Icc a b → z.im = T k →
        sLocalFiniteZetaDenominator F S χ z ≠ 0 ∧ ‖(sLocalFiniteZetaDenominator F S χ z)⁻¹‖ ≤ C := by
  let c (v : S) : ℂ := if finiteZetaUnramified F v.val (χ v)
    then (χ v (chosenFiniteUniformizer F v.val) : ℂ) else 0
  let q (v : S) := v.val.asIdeal.absNorm
  have he (z : ℂ) : sLocalFiniteZetaDenominator F S χ z = reciprocalEuler c q z := by
    unfold sLocalFiniteZetaDenominator reciprocalEuler
    apply Finset.prod_congr rfl
    intro v _
    by_cases h : finiteZetaUnramified F v.val (χ v)
    · simp only [c, ite_eq_left h, q, finiteZetaDenominator, finiteZetaRatio, neg_mul,
        mul_comm z (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)]
    · simp only [c, ite_eq_right h, zero_mul, sub_zero]
  obtain ⟨C, T, hC, _, _, _, htop, hbot, hb⟩ := reciprocalEuler_bounded_inverse_strip_sequence
    c q (fun v ↦ NumberField.HeightOneSpectrum.one_lt_absNorm v.val) hab
  refine ⟨C, T, hC, htop, hbot, fun k z hz hi ↦ ?_⟩
  rw [he, ← Complex.re_add_im z, hi]
  exact hb k z.re hz

/-- Every vertical line off the imaginary axis keeps the reciprocal finite Euler denominator bounded. -/
theorem sLocalFiniteZetaDenominator_bounded_inverse_vertical
    (χ : PhaseFamily F S) {a : ℝ} (ha : a ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = a →
      sLocalFiniteZetaDenominator F S χ z ≠ 0 ∧ ‖(sLocalFiniteZetaDenominator F S χ z)⁻¹‖ ≤ C := by
  let L (v : S) := Real.log (v.val.asIdeal.absNorm : ℝ)
  let m (v : S) : ℝ := if finiteZetaUnramified F v.val (χ v) then |1 - Real.exp (-a * L v)| else 1
  have hm (v : S) : 0 < m v := by
    by_cases h : finiteZetaUnramified F v.val (χ v)
    · dsimp only [m]
      rw [ite_eq_left h, abs_pos, sub_ne_zero]
      have hL : 0 < L v := Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
      intro he
      have hzero : -a * L v = 0 := Real.exp_injective (he.symm.trans Real.exp_zero.symm)
      exact (mul_ne_zero (neg_ne_zero.mpr ha) hL.ne') hzero
    · simp [m, h]
  let C := ∏ v : S, (m v)⁻¹
  refine ⟨C, Finset.prod_pos fun v _ ↦ inv_pos.mpr (hm v), fun z hz ↦ ?_⟩
  let d (v : S) := if finiteZetaUnramified F v.val (χ v) then finiteZetaDenominator F v.val (χ v) z else 1
  have hd (v : S) : m v ≤ ‖d v‖ := by
    by_cases h : finiteZetaUnramified F v.val (χ v)
    · have hn : ‖finiteZetaRatio F v.val (χ v) z‖ = Real.exp (-a * L v) := by
        simp only [finiteZetaRatio, L, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
          Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hz]
      simpa only [d, m, ite_eq_left h, finiteZetaDenominator, norm_one, hn] using
        (abs_norm_sub_norm_le (1 : ℂ) (finiteZetaRatio F v.val (χ v) z))
    · simp [d, m, h]
  have hnd (v : S) : d v ≠ 0 := norm_pos_iff.mp ((hm v).trans_le (hd v))
  change (∏ v, d v) ≠ 0 ∧ ‖(∏ v, d v)⁻¹‖ ≤ C
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hnd v), ?_⟩
  rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
  exact Finset.prod_le_prod (fun _ _ ↦ inv_nonneg.mpr (norm_nonneg _))
    (fun v _ ↦ inv_anti₀ (hm v) (hd v))

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

/-- A bound after clearing the finite Euler factors controls an entire
function on a strip crossing the imaginary axis. The recurrent horizontal
edges and both vertical edges have uniformly bounded reciprocal factors. -/
theorem sLocal_entire_bounded_of_finiteCleared
    (χ : PhaseFamily F S) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    {l r T A : ℝ} (hl : l < 0) (hr : 0 < r)
    (hlarge : ∀ z : ℂ, z.re ∈ Icc l r → T < |z.im| →
      ‖sLocalFiniteZetaDenominator F S χ z * H z‖ ≤ A) :
    ∃ M : ℝ, ∀ z : ℂ, z.re ∈ Icc l r → ‖H z‖ ≤ M := by
  let D := sLocalFiniteZetaDenominator F S χ
  obtain ⟨Cl, _, hleft⟩ := sLocalFiniteZetaDenominator_bounded_inverse_vertical F S χ hl.ne
  obtain ⟨Cr, _, hright⟩ := sLocalFiniteZetaDenominator_bounded_inverse_vertical F S χ hr.ne'
  obtain ⟨Ct, τ, _, htop, hbot, hcross⟩ :=
    sLocalFiniteZetaDenominator_bounded_inverse_strip_sequence F S χ (hl.trans hr).le
  have hRect : IsCompact (Icc l r ×ℂ Icc (-T) T) := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    · exact (isBounded_Icc _ _).reProdIm (isBounded_Icc _ _)
  obtain ⟨B, hB⟩ := (hRect.image hH.continuous.norm).bddAbove
  let M := max B (max Cl (max Cr Ct) * A)
  have hbounded (z : ℂ) (hz : z.re ∈ Icc l r) (hd : D z ≠ 0)
      (hinv : ‖(D z)⁻¹‖ ≤ max Cl (max Cr Ct)) : ‖H z‖ ≤ M := by
    by_cases h : T < |z.im|
    · have he : ‖H z‖ = ‖(D z)⁻¹‖ * ‖D z * H z‖ := by
        rw [← norm_mul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      rw [he]
      exact (mul_le_mul hinv (hlarge z hz h) (norm_nonneg _)
        ((norm_nonneg _).trans hinv)).trans (le_max_right _ _)
    · exact (hB (mem_image_of_mem _ ⟨hz, abs_le.mp (not_lt.mp h)⟩)).trans (le_max_left _ _)
  have hside (z : ℂ) (hz : z.re = l ∨ z.re = r) : ‖H z‖ ≤ M := by
    rcases hz with h | h
    · obtain ⟨hd, hb⟩ := hleft z h
      exact hbounded z ⟨h.ge, h.le.trans (hl.trans hr).le⟩ hd (hb.trans (le_max_left _ _))
    · obtain ⟨hd, hb⟩ := hright z h
      exact hbounded z ⟨(hl.trans hr).le.trans h.ge, h.le⟩ hd
        (hb.trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hrow (k : ℤ) (z : ℂ) (hz : z.re ∈ Icc l r) (hi : z.im = τ k) : ‖H z‖ ≤ M := by
    obtain ⟨hd, hb⟩ := hcross k z hz hi
    exact hbounded z hz hd (hb.trans ((le_max_right _ _).trans (le_max_right _ _)))
  exact ⟨M, entire_norm_le_of_sparse_strip_boundary hH (hl.trans hr) hside τ htop hbot hrow⟩

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

set_option maxHeartbeats 1500000 in
include hν in
/-- An entire representative of the S-local Mellin germ has rapid decay
uniformly on every closed vertical strip. -/
theorem sLocal_entire_mem_schwartzBergman
    (ω : PontryaginDual (K F S)) (f : E F S) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G)
    (hmatch : ∀ z : ℂ, Z F S μ ω f =ᶠ[𝓝[≠] z] G) :
    G ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  refine ⟨by simp, hG.differentiableOn, fun a b hab _ n ↦ ?_⟩
  let l := min a (-1)
  let r := max b 1
  let χ := sLocalFiniteZetaPhases F S ω
  let D := sLocalFiniteZetaDenominator F S χ
  let H (z : ℂ) := z ^ n * G z
  have hl : l < 0 := (min_le_right _ _).trans_lt (by norm_num)
  have hr : 0 < r := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_right _ _)
  have hdiff : Differentiable ℂ H := (differentiable_id.pow n).mul hG
  obtain ⟨Cl, hCl, hleft⟩ := sLocalFiniteZetaDenominator_bounded_inverse_vertical F S χ hl.ne
  obtain ⟨Cr, hCr, hright⟩ := sLocalFiniteZetaDenominator_bounded_inverse_vertical F S χ hr.ne'
  obtain ⟨Ct, T, hCt, htop, hbot, hcross⟩ :=
    sLocalFiniteZetaDenominator_bounded_inverse_strip_sequence F S χ (hl.trans hr).le
  obtain ⟨A, hA, hbound⟩ := sLocalProductZeta_finiteCleared_norm_le_on_strip F S μ ω
    ((sLocalRadialDerivative F S)^[n] f) (l - 1) (r + 1)
  let aR := sLocalRealArchParameters F S ω
  let aC := sLocalComplexArchParameters F S ω
  let R : ℝ := 2 + (∑ i, |(aR i).1.im|) + ∑ i, |(aC i).1.im|
  have hRRe (i : {w : InfinitePlace F // w.IsReal}) : 1 + |(aR i).1.im| < R := by
    have h₁ := Finset.single_le_sum (f := fun i ↦ |(aR i).1.im|)
      (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i)
    have h₂ : 0 ≤ ∑ i, |(aC i).1.im| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    dsimp only [R]
    linarith
  have hRIm (i : {w : InfinitePlace F // w.IsComplex}) : 1 + |(aC i).1.im| < R := by
    have h₁ := Finset.single_le_sum (f := fun i ↦ |(aC i).1.im|)
      (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i)
    have h₂ : 0 ≤ ∑ i, |(aR i).1.im| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    dsimp only [R]
    linarith
  have hshift (z α : ℂ) (hα : 1 + |α.im| < R) (hz : R < |z.im|) :
      1 ≤ |(z + α).im| := by
    have ht := abs_add_le (z.im + α.im) (-α.im)
    rw [add_neg_cancel_right, abs_neg] at ht
    rw [Complex.add_im]
    linarith
  have hlarge (z : ℂ) (hz : z.re ∈ Icc l r) (ht : R < |z.im|) (hd : D z ≠ 0) :
      ‖H z‖ ≤ ‖(D z)⁻¹‖ * A := by
    let P (w : ℂ) := D w * ((-w) ^ n * G w)
    have hDcont : Continuous D := continuous_iff_continuousAt.mpr fun w ↦
      (sLocalFiniteZetaDenominator_analytic F S χ w (mem_univ _)).continuousAt
    have hP : Continuous P := hDcont.mul (((continuous_id.neg).pow n).mul hG.continuous)
    have hh : ‖P z‖ ≤ A := by
      refine le_of_tendsto (x := 𝓝[≠] z)
        (hP.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds) ?_
      have hI : ∀ᶠ w : ℂ in 𝓝 z, w.re ∈ Icc (l - 1) (r + 1) := by
        have hi : z.re ∈ Ioo (l - 1) (r + 1) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
        have hnear : ∀ᶠ w : ℂ in 𝓝 z, w.re ∈ Ioo (l - 1) (r + 1) :=
          (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hi
        exact hnear.mono fun _ hw ↦ Ioo_subset_Icc_self hw
      have hH : ∀ᶠ w : ℂ in 𝓝 z, R < |w.im| :=
        (isOpen_lt continuous_const Complex.continuous_im.abs).mem_nhds ht
      have hD : ∀ᶠ w : ℂ in 𝓝 z, D w ≠ 0 :=
        hDcont.continuousAt.eventually_ne hd
      filter_upwards [hI.filter_mono nhdsWithin_le_nhds, hH.filter_mono nhdsWithin_le_nhds,
        hD.filter_mono nhdsWithin_le_nhds,
        sLocalContinuedZeta_iterate_radialDerivative F S μ ν hν ω f n z, hmatch z] with w hw hwH hwD he hEq
      change ‖D w * ((-w) ^ n * G w)‖ ≤ A
      rw [← hEq, ← he]
      exact hbound w hw (fun i ↦ hshift w (aC i).1 (hRIm i) hwH)
        (fun i ↦ hshift w (aR i).1 (hRRe i) hwH) hwD
    have he : (D z)⁻¹ * P z = (-z) ^ n * G z := by
      dsimp only [P]
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    have hval : ‖H z‖ = ‖(D z)⁻¹‖ * ‖P z‖ := by
      rw [← norm_mul, he]
      simp only [H, norm_mul, norm_pow, norm_neg]
    rw [hval]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
  let Rect := Icc l r ×ℂ Icc (-R) R
  have hRect : IsCompact Rect := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    · exact (isBounded_Icc _ _).reProdIm (isBounded_Icc _ _)
  obtain ⟨B, hB⟩ := (hRect.image hdiff.continuous.norm).bddAbove
  let M := max B (max Cl (max Cr Ct) * A)
  have hbounded (z : ℂ) (hz : z.re ∈ Icc l r)
      (hd : D z ≠ 0) (hinv : ‖(D z)⁻¹‖ ≤ max Cl (max Cr Ct)) : ‖H z‖ ≤ M := by
    by_cases h : R < |z.im|
    · exact (hlarge z hz h hd).trans ((mul_le_mul_of_nonneg_right hinv hA).trans (le_max_right _ _))
    · exact (hB (mem_image_of_mem _ ⟨hz, abs_le.mp (not_lt.mp h)⟩)).trans (le_max_left _ _)
  have hv : ∀ z : ℂ, z.re = l ∨ z.re = r → ‖H z‖ ≤ M := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨hd, hb⟩ := hleft z hz
      exact hbounded z ⟨hz.ge, hz.le.trans (hl.trans hr).le⟩ hd (hb.trans (le_max_left _ _))
    · obtain ⟨hd, hb⟩ := hright z hz
      exact hbounded z ⟨(hl.trans hr).le.trans hz.ge, hz.le⟩ hd
        (hb.trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hh : ∀ k : ℤ, ∀ z : ℂ, z.re ∈ Icc l r → z.im = T k → ‖H z‖ ≤ M := by
    intro k z hz hi
    obtain ⟨hd, hb⟩ := hcross k z hz hi
    exact hbounded z hz hd (hb.trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨M, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact entire_norm_le_of_sparse_strip_boundary hdiff (hl.trans hr) hv T htop hbot hh z
    ⟨(min_le_left _ _).trans hz.1, hz.2.trans (le_max_left _ _)⟩

include hν in
/-- Proposition 5.3.4.4, (1) implies (3). The normal form of an entire
S-local Mellin component supplies the original all-exponent theta profile. -/
theorem sLocal_logProfile_mem_of_entire
    (ω : PontryaginDual (K F S)) (f : E F S)
    (hentire : AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) univ) :
    (fun t : ℝ ↦ sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t)) ∈
      logExponentialDecaySubmodule univ := by
  let G := toMeromorphicNFOn (Z F S μ ω f) univ
  have hm : MeromorphicOn (Z F S μ ω f) univ :=
    (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f).meromorphicOn
  have hmatch (z : ℂ) : Z F S μ ω f =ᶠ[𝓝[≠] z] G :=
    (hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).symm
  have hdiff : Differentiable ℂ G := fun z ↦ (hentire z (mem_univ z)).differentiableAt
  have hMem := sLocal_entire_mem_schwartzBergman F S μ ν hν ω f G hdiff hmatch
  apply sLocal_logProfile_mem_of_schwartzBergman F S μ ν hν ω f ⟨G, hMem⟩
  intro z hz
  have hZ : ContinuousAt (Z F S μ ω f) z := by
    apply ((sLocalThetaZeta_analytic F S ν ω f z hz).congr ?_).continuousAt
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact (sLocalContinuedZeta_eq_theta F S μ ν hν ω f hw).symm
  exact tendsto_nhds_unique (hdiff.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hZ.tendsto.mono_left nhdsWithin_le_nhds).congr' (hmatch z))

include hν in
/-- Proposition 5.3.4.4. Entireness of the S-local Mellin component
is equivalent to admitting a flat Schwartz–Bruhat representative. The
equivalent all-exponent profile condition is expressed in logarithmic coordinates. -/
theorem sLocal_entire_iff_flat_and_profile
    (ω : PontryaginDual (K F S)) (f : E F S) :
    let entire := AnalyticOnNhd ℂ (toMeromorphicNFOn (Z F S μ ω f) univ) univ
    let flat := ∃ g : sLocalPolarFreeTestSubspace F S, sLocalMeromorphicZetaComponent F S μ ω f =
      sLocalMeromorphicZetaComponent F S μ ω g.val
    let decay := (fun t : ℝ ↦ sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t)) ∈
      logExponentialDecaySubmodule univ
    (entire ↔ flat) ∧ (flat ↔ decay) := by
  intro entire flat decay
  have h := sLocal_exists_polarFree_meromorphicZeta_iff_logProfile_mem F S μ ν hν ω f
  exact ⟨⟨fun he ↦ h.mpr (sLocal_logProfile_mem_of_entire F S μ ν hν ω f he),
    sLocal_entire_of_meromorphicZeta_eq_polarFree F S μ ω f⟩, h⟩

include hν in
/-- Theorem 7.3.4.1(3). A class in the full finite principal-value image
belongs to the zero-pole kernel exactly when represented by a flat test. -/
theorem sLocalArchPolarKernel_iff_flat_representative (ω : PontryaginDual (K F S))
    (q : sLocalArchPolarImage F S ν ω) :
    q ∈ sLocalArchPolarKernel F S μ ν hν ω ↔
      ∃ g : sLocalPolarFreeTestSubspace F S,
        (sLocalHomogeneousThetaKernel F S ν ω).mkQ g.val = q.val := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  constructor
  · intro h
    obtain ⟨f, hf⟩ := M.mkQ_surjective q.val
    have hentire := (mem_sLocalArchPolarKernel_iff_entire F S μ ν hν ω q f hf).mp h
    obtain ⟨g, hg⟩ := (sLocal_entire_iff_flat_and_profile F S μ ν hν ω f).1.mp hentire
    refine ⟨g, ?_⟩
    rw [← hf]
    change (Submodule.Quotient.mk (p := M) g.val) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq, mem_sLocalHomogeneousThetaKernel_iff,
      sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μ ν hν, map_sub, hg, sub_self]
  · rintro ⟨g, hg⟩
    exact (mem_sLocalArchPolarKernel_iff_entire F S μ ν hν ω q g.val hg).mpr
      (sLocalProductZeta_entire_of_polarFree F S μ ω g.val g.property)

end

end Masullo
