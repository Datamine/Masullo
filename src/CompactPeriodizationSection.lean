import CompactPeriodization
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

open Filter Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

/-- Every real point has a translate in a half-open fundamental interval. -/
theorem exists_integerTranslate_mem_Ico (a : ℝ) {d : ℝ} (hd : 0 < d) (x : ℝ) :
    ∃ n : ℤ, x + d * (n : ℝ) ∈ Ico a (a + d) := by
  refine ⟨-⌊(x - a) / d⌋, ?_⟩
  have h₁ := (le_div_iff₀ hd).mp (Int.floor_le ((x - a) / d))
  have h₂ := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one ((x - a) / d))
  simp only [Int.cast_neg, mul_neg, mem_Ico]
  constructor <;> nlinarith

/-- A strictly longer open interval covers the cyclic quotient. -/
theorem openInterval_covers_integerTranslations {a b d : ℝ} (hd : 0 < d)
    (hab : a + d < b) (x : ℝ) :
    ∃ n : ℤ, x + d * (n : ℝ) ∈ Ioo a b := by
  obtain ⟨n, hn⟩ := exists_integerTranslate_mem_Ico ((a + b - d) / 2) hd x
  exact ⟨n, by constructor <;> linarith [hn.1, hn.2]⟩

/-- For (x) in a compact interval, all terms outside one finite index set
vanish for every test supported in (K). -/
theorem exists_uniform_translate_finset {K I : Set ℝ} (hK : IsCompact K)
    (hI : IsCompact I) {d : ℝ} (hd : d ≠ 0) :
    ∃ s : Finset ℤ, ∀ x ∈ I, ∀ n : ℤ, x + d * (n : ℝ) ∈ K → n ∈ s := by
  classical
  let e := Homeomorph.mulLeft₀ d hd
  have hEmb : IsClosedEmbedding (fun n : ℤ => d * (n : ℝ)) :=
    e.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
  let C := (fun p : ℝ × ℝ => p.1 - p.2) '' (K ×ˢ I)
  have hc : IsCompact C := (hK.prod hI).image (by fun_prop)
  let h := (hEmb.isCompact_preimage hc).finite_of_discrete
  refine ⟨h.toFinset, fun x hx n hn => h.mem_toFinset.mpr ?_⟩
  change d * (n : ℝ) ∈ C
  exact ⟨(x + d * (n : ℝ), x), ⟨hn, hx⟩, by dsimp; ring⟩

theorem integerPeriodization_periodic (d : ℝ) (f : ℝ → ℂ) :
    Periodic (integerPeriodization d f) d := by
  intro x
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => f (x + d * (n : ℝ)))
  have he (n : ℤ) : x + d + d * (n : ℝ) = x + d * ((n + 1 : ℤ) : ℝ) := by
    push_cast
    ring
  simpa [integerPeriodization, Equiv.addRight, he] using h

theorem integerPeriodization_finset_eq {K : Set ℝ} {f : ℝ → ℂ}
    (hf : support f ⊆ K) {d x : ℝ} {s : Finset ℤ}
    (hs : ∀ n : ℤ, x + d * (n : ℝ) ∈ K → n ∈ s) :
    integerPeriodization d f x = ∑ n ∈ s, f (x + d * (n : ℝ)) := by
  apply tsum_eq_sum
  intro n hn
  by_contra hv
  exact hn (hs n (hf hv))

theorem integerPeriodization_contDiff {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ → ℂ} (hf : support f ⊆ K) (hC : ContDiff ℝ ∞ f) {d : ℝ} (hd : d ≠ 0) :
    ContDiff ℝ ∞ (integerPeriodization d f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := exists_uniform_translate_finset hK
    (isCompact_Icc (a := x - 1) (b := x + 1)) hd
  have hS : ContDiff ℝ ∞ (fun y : ℝ => ∑ n ∈ s, f (y + d * (n : ℝ))) :=
    ContDiff.sum fun n _ => hC.comp (by fun_prop)
  apply hS.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (show x - 1 < x by linarith) (show x < x + 1 by linarith)]
    with y hy
  exact integerPeriodization_finset_eq hf (hs y hy)

open scoped Pointwise in
private theorem exists_periodization_cutoff {K : Set ℝ} (hK : IsCompact K) {d : ℝ} (hd : 0 < d)
    (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ support g ⊆ K ∧
      ∀ x, integerPeriodization d g x ≠ 0 := by
  classical
  choose n hn using hcov
  have hball (x : ℝ) := Metric.isOpen_iff.mp isOpen_interior _ (hn x)
  choose r hr hsub using hball
  let bump (x : ℝ) : ContDiffBump (x + d * (n x : ℝ)) :=
    ⟨r x / 2, r x, by linarith [hr x], by linarith [hr x]⟩
  let U (x : ℝ) := {y : ℝ | 0 < bump x (y + d * (n x : ℝ))}
  have hU (x : ℝ) : IsOpen (U x) :=
    isOpen_lt continuous_const ((bump x).continuous.comp (by fun_prop))
  have hxU (x : ℝ) : x ∈ U x :=
    (bump x).pos_of_mem_ball (Metric.mem_ball_self (hr x))
  obtain ⟨s, hs⟩ := (isCompact_Icc (a := 0) (b := d)).elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  let u (y : ℝ) : ℝ := ∑ i ∈ s, bump i y
  let g (y : ℝ) : ℂ := ↑(u y)
  have hC : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp
    (ContDiff.sum fun i _ => (bump i).contDiff)
  have hnonneg (y : ℝ) : 0 ≤ u y := Finset.sum_nonneg fun i _ => (bump i).nonneg
  have hsupport : support g ⊆ K := by
    intro y hy
    by_contra hk
    have hz (i : ℝ) : bump i y = 0 := by
      by_contra hnz
      exact hk (interior_subset (hsub i (by simpa only [(bump i).support_eq] using
        (show y ∈ support (bump i : ℝ → ℝ) from hnz))))
    exact hy (by simp [g, u, hz])
  refine ⟨g, hC, hsupport, ?_⟩
  have hpositive (y : ℝ) (hy : y ∈ Icc 0 d) : ∃ m : ℤ, 0 < u (y + d * (m : ℝ)) := by
    obtain ⟨i, hsi⟩ := mem_iUnion.mp (hs hy)
    obtain ⟨hi, hiy⟩ := mem_iUnion.mp hsi
    exact ⟨n i, lt_of_lt_of_le hiy
      (Finset.single_le_sum (fun j _ => (bump j).nonneg) hi)⟩
  have hnz (y : ℝ) (hy : y ∈ Icc 0 d) : integerPeriodization d g y ≠ 0 := by
    obtain ⟨m, hm⟩ := hpositive y hy
    have hg := compact_integerTranslate_support_finite hK hsupport hd.ne' y
    have hEq : (∑' j : ℤ, u (y + d * (j : ℝ))) =
        ∑ j ∈ hg.toFinset, u (y + d * (j : ℝ)) := by
      apply tsum_eq_sum
      intro j hj
      by_contra hh
      apply hj
      exact hg.mem_toFinset.mpr (by solve_by_elim [Complex.ofReal_ne_zero.mpr])
    have hsum : Summable (fun j : ℤ => u (y + d * (j : ℝ))) := by
      apply summable_of_ne_finset_zero (s := hg.toFinset)
      intro j hj
      by_contra hh
      exact hj (hg.mem_toFinset.mpr (Complex.ofReal_ne_zero.mpr hh))
    have hcs : Complex.ofReal (∑' j : ℤ, u (y + d * (j : ℝ))) =
        integerPeriodization d g y := Complex.ofRealCLM.map_tsum hsum
    rw [← hcs]
    apply Complex.ofReal_ne_zero.mpr
    rw [hEq]
    exact (lt_of_lt_of_le hm (Finset.single_le_sum (f := fun j : ℤ => u (y + d * (j : ℝ))) (fun j _ => hnonneg _)
      (hg.mem_toFinset.mpr (Complex.ofReal_ne_zero.mpr hm.ne')))).ne'
  intro x
  obtain ⟨m, hm⟩ := exists_integerTranslate_mem_Ico 0 hd x
  have hP := (integerPeriodization_periodic d g).int_mul m
  have hrw := hP x
  rw [mul_comm (m : ℝ) d] at hrw
  rw [← hrw]
  exact hnz _ (by simpa using Ico_subset_Icc_self hm)

theorem integerPeriodization_extends_periodic {K : Set ℝ} (hK : IsCompact K) {d : ℝ} (hd : 0 < d)
    (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K) :
    ∃ b : ℝ → ℂ, ContDiff ℝ ∞ b ∧ support b ⊆ K ∧
      ∀ f : ℝ → ℂ, Periodic f d → integerPeriodization d (fun x => b x * f x) = f := by
  obtain ⟨g, hgC, hg, hgnz⟩ := exists_periodization_cutoff hK hd hcov
  let G := integerPeriodization d g
  let b (x : ℝ) := g x / G x
  have hGC := integerPeriodization_contDiff hK hg hgC hd.ne'
  have hGP := integerPeriodization_periodic d g
  have hi : ContDiff ℝ ∞ (fun x => (G x)⁻¹) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hc : ContDiffAt ℂ ∞ (fun z : ℂ => z⁻¹) (G x) := contDiffAt_inv ℂ (hgnz x)
    exact (hc.restrict_scalars ℝ).comp x hGC.contDiffAt
  have hbC : ContDiff ℝ ∞ b := by simpa only [b, div_eq_mul_inv] using hgC.mul hi
  refine ⟨b, hbC, ?_, ?_⟩
  · intro x hx
    apply hg
    exact fun h => hx (by simp [b, h])
  · intro f hf
    funext x
    have he (n : ℤ) : x + d * (n : ℝ) = x + (n : ℝ) * d := by rw [mul_comm d]
    have hs := compact_integerTranslate_summable hK hg hd.ne' x
    calc
      integerPeriodization d (fun x => b x * f x) x =
          ∑' n : ℤ, g (x + d * (n : ℝ)) * (f x / G x) := by
        unfold integerPeriodization
        congr 1
        funext n
        have hG : G (x + (n : ℝ) * d) = G x := (hGP.int_mul n) x
        dsimp only [b]
        rw [he, hG, (hf.int_mul n) x]
        ring
      _ = G x * (f x / G x) := hs.tsum_mul_right _
      _ = f x := by
        have hz : G x ≠ 0 := hgnz x
        field_simp

end
end Masullo
