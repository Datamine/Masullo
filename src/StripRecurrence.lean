import FiniteEulerRecurrence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

open Filter Function MeasureTheory Set
open scoped Topology

namespace Masullo

/-- Positive upper density in the symmetric windows of Definition B.5.3.1.
The positive slope in the measure bound is twice the corresponding lower
bound for the normalized fractions on the chosen windows. -/
def PositiveUpperDensity (E : Set ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ T in atTop, ENNReal.ofReal (c * T) ≤ volume (Icc (-T) T ∩ E)

/-- The density predicate agrees with the positive real limsup in (B.5.3.2). -/
theorem positiveUpperDensity_iff_limsup (E : Set ℝ) : PositiveUpperDensity E ↔
    0 < limsup (fun T : ℝ => (volume (Icc (-T) T ∩ E)).toReal / (2 * T)) atTop := by
  let d (T : ℝ) := (volume (Icc (-T) T ∩ E)).toReal / (2 * T)
  have hfin (T : ℝ) : volume (Icc (-T) T ∩ E) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
  have he : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hub : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) d := by
    refine ⟨1, he.mono fun T hT => ?_⟩
    have hm := ENNReal.toReal_mono (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (μ := volume) (inter_subset_left : Icc (-T) T ∩ E ⊆ Icc (-T) T))
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hm
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).mpr
    linarith
  constructor
  · rintro ⟨c, hc, h⟩
    have hl : ∃ᶠ T in atTop, c / 2 ≤ d T := (h.and_eventually he).mono fun T ⟨ht, hT⟩ => by
      have hm := ENNReal.toReal_mono (hfin T) ht
      rw [ENNReal.toReal_ofReal (by positivity)] at hm
      apply (le_div_iff₀ (by positivity : 0 < 2 * T)).mpr
      linarith
    exact (half_pos hc).trans_le (le_limsup_of_frequently_le hl hub)
  · intro h
    obtain ⟨c, hc, hlim⟩ := exists_between h
    have hcb : (atTop : Filter ℝ).IsCoboundedUnder (· ≤ ·) d :=
      isCoboundedUnder_le_of_eventually_le atTop (x := 0) (he.mono fun T hT =>
        div_nonneg ENNReal.toReal_nonneg (by positivity))
    have hl : ∃ᶠ T in atTop, c < d T := frequently_lt_of_lt_limsup hcb hlim
    refine ⟨2 * c, by positivity, (hl.and_eventually he).mono fun T ⟨ht, hT⟩ => ?_⟩
    have hm := (lt_div_iff₀ (by positivity : 0 < 2 * T)).mp ht
    have hh : 2 * c * T ≤ (volume (Icc (-T) T ∩ E)).toReal := by linarith
    simpa only [ENNReal.ofReal_toReal (hfin T)] using ENNReal.ofReal_le_ofReal hh

def StronglyRecurrentOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ ε > 0, PositiveUpperDensity (recurrenceReturns f K ε)

theorem PositiveUpperDensity.mono {E F : Set ℝ} (h : PositiveUpperDensity E) (hEF : E ⊆ F) :
    PositiveUpperDensity F := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, h.mono fun _ ht => ht.trans (measure_mono (inter_subset_inter_right _ hEF))⟩

/-- Lemma B.5.3.4(1). -/
theorem StronglyRecurrentOn.mono {f : ℂ → ℂ} {K L : Set ℂ} (h : StronglyRecurrentOn f K)
    (hLK : L ⊆ K) : StronglyRecurrentOn f L := fun ε hε =>
  (h ε hε).mono fun _ ⟨b, hb, hh⟩ => ⟨b, hb, fun z hz => hh z (hLK hz)⟩

theorem reciprocalEuler_positiveUpperDensity {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (q : ι → ℕ) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    PositiveUpperDensity (Ici 0 ∩ recurrenceReturns (reciprocalEuler a q) K ε) ∧
    PositiveUpperDensity (Iic 0 ∩ recurrenceReturns (reciprocalEuler a q) K ε) := by
  obtain ⟨c, hc, h⟩ := reciprocalEuler_recurrence a q hK hε
  constructor
  · refine ⟨c, hc, (h.mono fun T ⟨ht, _⟩ => ht.trans (measure_mono ?_)).frequently⟩
    intro t ⟨ht, hret⟩
    exact ⟨⟨by linarith [ht.1, ht.2], ht.2⟩, ht.1, hret⟩
  · refine ⟨c, hc, (h.mono fun T ⟨_, ht⟩ => ht.trans (measure_mono ?_)).frequently⟩
    intro t ⟨ht, hret⟩
    exact ⟨⟨ht.1, by linarith [ht.1, ht.2]⟩, ht.2, hret⟩

private theorem compact_strip_preimage {S K : Set ℂ} (hK : IsCompact K) (hKS : K ⊆ S) :
    IsCompact ((Subtype.val : S → ℂ) ⁻¹' K) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
  exact hK

private theorem compactFamily_transfer {S : Type*} [TopologicalSpace S]
    (H : Set C(S, ℂ)) (hH : IsCompact H) (f : C(S, ℂ))
    (D K : Set S) [CompactSpace D] [CompactSpace K]
    (detects : ∀ g ∈ H, g.restrict D = f.restrict D → g = f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g ∈ H, dist (g.restrict D) (f.restrict D) < δ →
      dist (g.restrict K) (f.restrict K) ≤ ε := by
  let B := H ∩ {g | ε ≤ dist (g.restrict K) (f.restrict K)}
  have hb : IsCompact B := hH.inter_right
    (isClosed_le continuous_const ((ContinuousMap.continuous_restrict K).dist continuous_const))
  by_cases hn : B.Nonempty
  · obtain ⟨g₀, hg₀, hm⟩ := hb.exists_isMinOn hn
      (((ContinuousMap.continuous_restrict D).dist continuous_const).continuousOn)
    let δ := dist (g₀.restrict D) (f.restrict D)
    have hδ : 0 < δ := by
      by_contra! h
      have heq : g₀.restrict D = f.restrict D := dist_le_zero.mp h
      have hg : g₀ = f := detects g₀ hg₀.1 heq
      have ht := hg₀.2
      change ε ≤ dist (g₀.restrict K) (f.restrict K) at ht
      rw [hg, dist_self] at ht
      linarith
    refine ⟨δ, hδ, fun g hg hgd => ?_⟩
    by_contra! h
    exact (not_lt_of_ge (hm (show g ∈ B from ⟨hg, h.le⟩))) hgd
  · refine ⟨1, one_pos, fun g hg _ => ?_⟩
    by_contra! h
    exact hn ⟨g, hg, h.le⟩

/-- A compact analytic hull repairs the disc-to-compact implication of
Lemma B.5.3.4(2). The hull is taken in the compact-open topology, and it
contains the vertical translates restricted to the strip. -/
theorem strongRecurrence_of_disc_of_compact_holomorphic_hull {S : Set ℂ}
    (hconn : IsPreconnected S) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f S)
    (H : Set C(S, ℂ)) (hH : IsCompact H)
    (hhol : ∀ g ∈ H, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F S ∧ ∀ z : S, F z = g z)
    (htrans : ∀ t : ℝ, ∃ g ∈ H, ∀ z : S, g z = f (z + (t : ℂ) * Complex.I))
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hDS : Metric.closedBall z₀ r ⊆ S)
    (hDrec : StronglyRecurrentOn f (Metric.closedBall z₀ r))
    {K : Set ℂ} (hK : IsCompact K) (hKS : K ⊆ S) : StronglyRecurrentOn f K := by
  let D' := (Subtype.val : S → ℂ) ⁻¹' Metric.closedBall z₀ r
  let K' := (Subtype.val : S → ℂ) ⁻¹' K
  letI : CompactSpace D' := isCompact_iff_compactSpace.mp (compact_strip_preimage (isCompact_closedBall _ _) hDS)
  letI : CompactSpace K' := isCompact_iff_compactSpace.mp (compact_strip_preimage hK hKS)
  have hcentre : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  let f₀ : C(S, ℂ) := ⟨fun z => f z, hf.continuousOn.domRestrict⟩
  have hD' : D'.Nonempty := ⟨⟨z₀, hDS hcentre⟩, hcentre⟩
  haveI : Nonempty D' := hD'.to_subtype
  have detects (g : C(S, ℂ)) (hg : g ∈ H) (heq : g.restrict D' = f₀.restrict D') : g = f₀ := by
    obtain ⟨F, hF, hFg⟩ := hhol g hg
    have hev : F =ᶠ[𝓝 z₀] f := by
      filter_upwards [Metric.closedBall_mem_nhds z₀ hr] with z hz
      exact (hFg ⟨z, hDS hz⟩).trans (DFunLike.congr_fun heq ⟨⟨z, hDS hz⟩, hz⟩)
    have he := hF.eqOn_of_preconnected_of_eventuallyEq hf hconn (hDS hcentre) hev
    exact ContinuousMap.ext fun z => (hFg z).symm.trans (he z.property)
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := compactFamily_transfer H hH f₀ D' K' detects (ε := ε / 2) (by linarith)
  apply (hDrec δ hδ).mono
  intro t ht
  obtain ⟨g, hg, hgt⟩ := htrans t
  obtain ⟨b, hb, he⟩ := ht
  have hd : dist (g.restrict D') (f₀.restrict D') ≤ b :=
    (ContinuousMap.dist_le_iff_of_nonempty).mpr fun z => by
      change dist (g z.val) (f z.val.val) ≤ b
      rw [hgt, dist_eq_norm]
      exact he z.val.val z.property
  have hctl := hcontrol g hg (hd.trans_lt hb)
  refine ⟨ε / 2, by linarith, fun z hz => ?_⟩
  let q : K' := ⟨⟨z, hKS hz⟩, hz⟩
  have hx := (ContinuousMap.dist_apply_le_dist (f := g.restrict K') (g := f₀.restrict K') q).trans hctl
  change dist (g q.val) (f z) ≤ ε / 2 at hx
  rwa [hgt, dist_eq_norm] at hx

end Masullo
