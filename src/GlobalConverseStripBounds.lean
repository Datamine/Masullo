import FiniteHeckeHorizontal
import Mathlib.Analysis.Complex.PhragmenLindelof

open Bornology Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev verticalStrip (a b : ℝ) := Complex.re ⁻¹' Icc a b

/-- The Gaussian-strip step of Theorem 6.3.2.1 can use horizontal edges on
which the outside Euler product has a polynomial lower bound. Rapid decay
of the product with that Euler factor transfers to the undivided holomorphic
coordinate once it has rapid decay on the two vertical edges. -/
theorem rapidStrip_of_sparse_horizontal_lower {L H : ℂ → ℂ} {a b U Y A : ℝ}
    (hab : a < b) (hH : DifferentiableOn ℂ H (verticalStrip a b))
    (hL : ∀ sign : ℝ, |sign| = 1 → ∀ T ≥ U, ∃ t ∈ Ioo T (T + 1),
      ∀ x ∈ Icc a b, |t| ^ (-A) < ‖L ⟨x, sign * t⟩‖)
    (hprod : ∀ m : ℕ, BddAbove
      ((fun z : ℂ ↦ ‖z ^ m * (L z * H z)‖) '' {z ∈ verticalStrip a b | Y ≤ |z.im|}))
    (hside : ∀ n : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re = a ∨ z.re = b → ‖z ^ n * H z‖ ≤ C) :
    ∀ n : ℕ, BddAbove ((fun z : ℂ ↦ ‖z ^ n * H z‖) '' verticalStrip a b) := by
  intro n
  obtain ⟨q, hq⟩ := exists_nat_gt A
  obtain ⟨B, hB⟩ := hprod (n + q)
  obtain ⟨C, hC⟩ := hside n
  refine ⟨max B C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let T := max (max U Y) (|z.im| + 1)
  have hTU : U ≤ T := (le_max_left U Y).trans (le_max_left _ _)
  have hTY : Y ≤ T := (le_max_right U Y).trans (le_max_left _ _)
  have hTz : |z.im| + 1 ≤ T := le_max_right _ _
  have hT₁ : 1 ≤ T := (by linarith [abs_nonneg z.im] : 1 ≤ |z.im| + 1).trans hTz
  obtain ⟨l, hl, hlow⟩ := hL (-1) (by norm_num) T hTU
  obtain ⟨r, hr, hupp⟩ := hL 1 (by norm_num) T hTU
  have hlo : -l < z.im := by linarith [neg_abs_le z.im, hl.1]
  have hhi : z.im < r := by linarith [le_abs_self z.im, hr.1]
  have hedge (sign : ℝ) (hsign : |sign| = 1) (t : ℝ) (ht : T < t)
      (hbound : ∀ x ∈ Icc a b, |t| ^ (-A) < ‖L ⟨x, sign * t⟩‖)
      (w : ℂ) (hw : w.re ∈ Icc a b) (hi : w.im = sign * t) : ‖w ^ n * H w‖ ≤ B := by
    have htpos : 0 < t := zero_lt_one.trans (hT₁.trans_lt ht)
    have hWt : |w.im| = t := by rw [hi, abs_mul, hsign, one_mul, abs_of_pos htpos]
    have hlower : t ^ (-(q : ℝ)) < ‖L w‖ := by
      have hh := hbound w.re hw
      rw [abs_of_pos htpos, ← hi] at hh
      change t ^ (-A) < ‖L w‖ at hh
      exact (Real.rpow_le_rpow_of_exponent_le (hT₁.trans ht.le) (neg_le_neg hq.le)).trans_lt hh
    have hunit : 1 ≤ ‖w‖ ^ q * ‖L w‖ := by
      have hpow : t ^ q ≤ ‖w‖ ^ q :=
        pow_le_pow_left₀ htpos.le (hWt ▸ Complex.abs_im_le_norm w) _
      have hp : (t ^ q)⁻¹ ≤ ‖L w‖ := by
        rw [← Real.rpow_natCast, ← Real.rpow_neg htpos.le]
        exact hlower.le
      calc
        1 = t ^ q * (t ^ q)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ htpos.ne')).symm
        _ ≤ ‖w‖ ^ q * ‖L w‖ := mul_le_mul hpow hp (by positivity) (by positivity)
    have hfast := hB ⟨w, ⟨hw, hWt.symm ▸ hTY.trans ht.le⟩, rfl⟩
    calc
      ‖w ^ n * H w‖ ≤ (‖w‖ ^ q * ‖L w‖) * ‖w ^ n * H w‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hunit
      _ = ‖w ^ (n + q) * (L w * H w)‖ := by simp only [norm_mul, norm_pow, pow_add]; ring
      _ ≤ B := hfast
  let R := Ioo a b ×ℂ Ioo (-l) r
  have hLR : -l < r := hlo.trans hhi
  have hR : IsBounded R := (isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)
  have hcl : closure R = Icc a b ×ℂ Icc (-l) r := by
    dsimp only [R]
    rw [Complex.closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hLR.ne]
  have hzR : z ∈ closure R := hcl ▸ ⟨hz, hlo.le, hhi.le⟩
  have hwide : closure R ⊆ verticalStrip a b := by
    rw [hcl]
    exact fun w hw ↦ hw.1
  have hd : DiffContOnCl ℂ (fun w : ℂ ↦ w ^ n * H w) R :=
    ⟨(differentiableOn_id.pow n).mul (hH.mono (subset_closure.trans hwide)),
      (continuousOn_id.pow n).mul (hH.continuousOn.mono hwide)⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le hR hd _ hzR
  intro w hw
  change w ∈ frontier (Ioo a b ×ℂ Ioo (-l) r) at hw
  rw [Complex.frontier_reProdIm, frontier_Ioo hab, frontier_Ioo hLR,
    closure_Ioo hab.ne, closure_Ioo hLR.ne] at hw
  rcases hw with horizontal | vertical
  · rcases (show w.im = -l ∨ w.im = r from by simpa using horizontal.2) with he | he
    · exact (hedge (-1) (by norm_num) l hl.1 hlow w horizontal.1
        (by simpa using he)).trans (le_max_left _ _)
    · exact (hedge 1 (by norm_num) r hr.1 hupp w horizontal.1
        (by simpa using he)).trans (le_max_left _ _)
  · exact (hC w (by simpa using vertical.1)).trans (le_max_right _ _)

/-- A uniformly nonzero factor at large heights on a vertical line combines
with a bound on the product to control the original coordinate on that line. -/
theorem rapidVerticalBoundary_of_product
    {L H : ℂ → ℂ} {a b x Y T c : ℝ} (hx : x ∈ Icc a b) (hc : 0 < c)
    (hH : ContinuousOn H (verticalStrip a b))
    (hL : ∀ z : ℂ, z.re = x → T ≤ |z.im| → c ≤ ‖L z‖)
    (hprod : ∀ m : ℕ, BddAbove
      ((fun z : ℂ ↦ ‖z ^ m * (L z * H z)‖) '' {z ∈ verticalStrip a b | Y ≤ |z.im|})) :
    ∀ n : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re = x → ‖z ^ n * H z‖ ≤ C := by
  intro n
  obtain ⟨B, hB⟩ := hprod n
  let Y₀ := max Y T
  let edgeSegment := ({x} : Set ℝ) ×ℂ Icc (-Y₀) Y₀
  have hK : IsCompact edgeSegment := isCompact_singleton.reProdIm isCompact_Icc
  have hKsub : edgeSegment ⊆ verticalStrip a b := by
    intro w hw
    have hre : w.re = x := hw.1
    change w.re ∈ Icc a b
    rwa [hre]
  have hcont : ContinuousOn (fun w : ℂ ↦ ‖w ^ n * H w‖) edgeSegment :=
    ((continuousOn_id.pow n).mul (hH.mono hKsub)).norm
  obtain ⟨D, hD⟩ := (hK.image_of_continuousOn hcont).bddAbove
  refine ⟨max (B / c) D, fun w hw ↦ ?_⟩
  by_cases hY : Y₀ ≤ |w.im|
  · apply le_trans _ (le_max_left _ _)
    apply (le_div_iff₀ hc).mpr
    have hcw := hL w hw ((le_max_right _ _).trans hY)
    calc
      ‖w ^ n * H w‖ * c ≤ ‖w ^ n * H w‖ * ‖L w‖ :=
        mul_le_mul_of_nonneg_left hcw (norm_nonneg _)
      _ = ‖w ^ n * (L w * H w)‖ := by simp only [norm_mul]; ring
      _ ≤ B := hB ⟨w, ⟨show w.re ∈ Icc a b by rwa [hw], (le_max_left _ _).trans hY⟩, rfl⟩
  · exact (hD ⟨w, ⟨hw, abs_le.mp (le_of_not_ge hY)⟩, rfl⟩).trans (le_max_right _ _)

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (χ : PontryaginDual (IdeleClass F)) (S : Finset (Place F))
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
/-- The continued Euler product outside any finite set supplies the
horizontal estimates on all rectangles inside the critical strip enlargement. -/
theorem exists_globalConverse_Outside_strip_transfer :
    ∃ (L : ℂ → ℂ) (c : ℝ), 0 < c ∧ MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} ∧
      (∀ y : ℝ, c ≤ ‖L ⟨2, y⟩‖) ∧
      ∀ {a b : ℝ}, a < b → Icc a b ⊆ Icc (-1 : ℝ) 2 →
        ∀ {H : ℂ → ℂ}, DifferentiableOn ℂ H (verticalStrip a b) →
        ∀ Y : ℝ,
        (∀ m : ℕ, BddAbove
          ((fun z : ℂ ↦ ‖z ^ m * (L z * H z)‖) '' {z ∈ verticalStrip a b | Y ≤ |z.im|})) →
        (∀ n : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re = a ∨ z.re = b → ‖z ^ n * H z‖ ≤ C) →
        ∀ n : ℕ, BddAbove ((fun z : ℂ ↦ ‖z ^ n * H z‖) '' verticalStrip a b) := by
  obtain ⟨L, A, U, _, hm, he, _, hLower, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_horizontal_lower_bounds F χ S ν η μ hν
  obtain ⟨M, _, c, hc, _, heM, hcenter, _⟩ :=
    exists_manuscriptFiniteHeckeOutside_polynomial_strips F χ S ν η μ hν
  have hright (y : ℝ) : c ≤ ‖L ⟨2, y⟩‖ := by
    have hz : (⟨2, y⟩ : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      change (1 : ℝ) < 2
      norm_num
    rw [he hz, ← heM hz]
    exact hcenter y
  refine ⟨L, c, hc, hm, he, hright, fun hab hsub H hH Y hprod hside ↦ ?_⟩
  apply rapidStrip_of_sparse_horizontal_lower (L := L) (H := H)
    (A := A) (U := U) (Y := Y) hab hH _ hprod hside
  intro sign hsign T hT
  obtain ⟨t, ht, hbound⟩ := hLower sign hsign T hT
  exact ⟨t, ht, fun x hx ↦ hbound x (hsub hx)⟩

include μ hν in
/-- On a strip ending at real part two, the product estimate provides the
right vertical bound through the absolute Euler product. The left vertical
bound is the only edge bound required as a hypothesis. -/
theorem exists_globalConverse_Outside_strip_transfer_right_two :
    ∃ L : ℂ → ℂ, MeromorphicOn L univ ∧
      EqOn L (manuscriptFiniteHeckeEulerOutside F χ S) {z | 1 < z.re} ∧
      ∀ {a : ℝ}, -1 ≤ a → a < 2 →
        ∀ {H : ℂ → ℂ}, DifferentiableOn ℂ H (verticalStrip a 2) →
        ∀ Y : ℝ,
        (∀ m : ℕ, BddAbove
          ((fun z : ℂ ↦ ‖z ^ m * (L z * H z)‖) '' {z ∈ verticalStrip a 2 | Y ≤ |z.im|})) →
        (∀ n : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re = a → ‖z ^ n * H z‖ ≤ C) →
        ∀ n : ℕ, BddAbove ((fun z : ℂ ↦ ‖z ^ n * H z‖) '' verticalStrip a 2) := by
  obtain ⟨L, c, hc, hMer, he, hcenter, htransfer⟩ :=
    exists_globalConverse_Outside_strip_transfer F χ S ν η μ hν
  refine ⟨L, hMer, he, ?_⟩
  intro a ha hab H hH Y hprod hLeft
  apply htransfer hab (Icc_subset_Icc_left ha) hH Y hprod
  have hRight := rapidVerticalBoundary_of_product (T := 0) (right_mem_Icc.mpr hab.le)
    hc hH.continuousOn (fun w hw _ ↦ by simpa [← hw] using hcenter w.im) hprod
  intro n
  obtain ⟨C, hC⟩ := hLeft n
  obtain ⟨D, hD⟩ := hRight n
  refine ⟨max C D, fun w hw ↦ ?_⟩
  rcases hw with hl | hr
  · exact (hC w hl).trans (le_max_left _ _)
  · exact (hD w hr).trans (le_max_right _ _)

end

end Masullo
