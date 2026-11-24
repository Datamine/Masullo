/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
Sources and license are recorded in External/PROVENANCE.md.
-/
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

/-- A group with a regular, σ-finite Haar measure is σ-compact. -/
theorem sigmaCompactSpace_of_sigmaFinite_haar {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [SigmaFinite μ] : SigmaCompactSpace G := by
  let ε (n : ℕ) : ℝ≥0∞ := (↑(n + 1) : ℝ≥0∞)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hex (m n : ℕ) : ∃ K, K ⊆ spanningSets μ m ∧ IsCompact K ∧
      μ (spanningSets μ m \ K) < ε n :=
    (measurableSet_spanningSets μ m).exists_isCompact_sdiff_lt
      (measure_spanningSets_lt_top μ m).ne (by simp [ε])
  choose K _ hK hrem using hex
  let A : Set G := ⋃ p : ℕ × ℕ, K p.1 p.2
  have hA : ∀ᵐ x ∂μ, x ∈ A := by
    have hnull (m : ℕ) : μ (spanningSets μ m \ A) = 0 := by
      refine le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hε fun n ↦ ?_) bot_le
      exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion
        (fun p : ℕ × ℕ ↦ K p.1 p.2) (m, n)))).trans (hrem m n).le
    filter_upwards [ae_all_iff.mpr (fun m ↦ measure_eq_zero_iff_ae_notMem.mp (hnull m))] with x hx
    obtain ⟨m, hm⟩ := iUnion_eq_univ_iff.mp (iUnion_spanningSets μ) x
    by_contra hn
    exact hx m ⟨hm, hn⟩
  let D (p : (ℕ × ℕ) × (ℕ × ℕ)) := K p.1.1 p.1.2 * (K p.2.1 p.2.2)⁻¹
  have hcover : ⋃ p, D p = univ := by
    refine iUnion_eq_univ_iff.mpr fun x ↦ ?_
    obtain ⟨y, hy, hxy⟩ := (hA.and
      ((measurePreserving_mul_left μ x).quasiMeasurePreserving.ae hA)).exists
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact ⟨(i, j), Set.mem_mul.mpr ⟨x * y, hi, y⁻¹, Set.inv_mem_inv.mpr hj, by simp⟩⟩
  exact ⟨hcover ▸ isSigmaCompact_iUnion_of_isCompact D
    (fun p ↦ (hK p.1.1 p.1.2).mul (hK p.2.1 p.2.2).inv)⟩


/-- Complex compactly supported tests integrate against the induced Haar measure by
first integrating over the closed subgroup and then over the quotient. -/
theorem integral_inducedMeasure_complex {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [LocallyCompactSpace B] [T2Space B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [MeasurableSpace C] [BorelSpace C]
    {i : A →* B} {p : B →* C} (h : TopologicalGroup.IsSES i p)
    (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    (f : CompactlySupportedContinuousMap B ℂ) :
    ∫ b, f b ∂(h.inducedMeasure μA μC) = h.integrate μA μC f := by
  have test (L : ℂ →L[ℝ] ℝ) :
      L (∫ b, f b ∂(h.inducedMeasure μA μC)) = L (h.integrate μA μC f) := by
    let ℓ : C(ℂ, ℝ) := ⟨L, L.continuous⟩
    let g := f.compLeft ℓ
    have hg (b : B) : g b = L (f b) :=
      CompactlySupportedContinuousMap.compLeft_apply (g := ℓ) L.map_zero f b
    rw [← L.integral_comp_comm f.integrable, h.integrate_apply,
      ← L.integral_comp_comm (h.pushforward μA f).integrable]
    simp_rw [← hg]
    rw [h.integral_inducedMeasure, h.integrate_apply]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro c
    obtain ⟨b, rfl⟩ := h.isOpenQuotientMap.surjective c
    change h.pushforward μA g (p b) = L (h.pushforward μA f (p b))
    rw [h.pushforward_apply_apply, h.pushforward_apply_apply,
      ← L.integral_comp_comm (h.pullback f b).integrable]
    simp only [h.pullback_def, hg]
  exact Complex.ext (test Complex.reCLM) (test Complex.imCLM)

section Weil

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

local instance : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: (D.1.2.1), p. 747. Integrate over the translate of the subgroup represented
by a quotient point. The representative is chosen by `Quotient.out`. -/
def lcaCosetIntegral (μH : Measure H) (f : G → ℂ) (q : G ⧸ H) : ℂ :=
  ∫ h : H, f (q.out * (h : G)) ∂μH

/-- Paper: (D.1.2.1), p. 747. The coset integral is independent of the representative. -/
theorem lcaCosetIntegral_mk (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G) :
    lcaCosetIntegral H μH f (QuotientGroup.mk x) =
      ∫ h : H, f (x * (h : G)) ∂μH := by
  rw [lcaCosetIntegral]
  set y : G := Quotient.out (QuotientGroup.mk x) with hydef
  have hy : QuotientGroup.mk y = QuotientGroup.mk x := Quotient.out_eq' _
  have hk : y⁻¹ * x ∈ H := QuotientGroup.eq.mp hy
  let k : H := ⟨y⁻¹ * x, hk⟩
  have hxe : x = y * (k : G) := by
    simp [k]
  rw [hxe]
  have hassoc : ∀ h : H, y * (k : G) * (h : G) = y * ((k * h : H) : G) := by
    intro h
    rw [Subgroup.coe_mul, mul_assoc]
  simp_rw [hassoc]
  exact (MeasureTheory.integral_mul_left_eq_self (fun h : H ↦ f (y * (h : G))) k).symm

/-- Integrability of the restriction to a coset is independent of the representative. -/
theorem lcaCosetIntegrable_mk (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G) :
    Integrable (fun h : H => f ((QuotientGroup.mk x : G ⧸ H).out * (h : G))) μH ↔
      Integrable (fun h : H => f (x * (h : G))) μH := by
  let y := (QuotientGroup.mk x : G ⧸ H).out
  have he : QuotientGroup.mk y = (QuotientGroup.mk x : G ⧸ H) := Quotient.out_eq' _
  let k : H := ⟨y⁻¹ * x, QuotientGroup.eq.mp he⟩
  have hx : x = y * (k : G) := by simp [k]
  change Integrable (fun h : H => f (y * (h : G))) μH ↔ _
  conv_rhs => rw [hx]
  simp_rw [mul_assoc, ← Subgroup.coe_mul]
  exact ((measurePreserving_mul_left μH k).integrable_comp_emb
    (MeasurableEquiv.mulLeft k).measurableEmbedding).symm

/-- Paper: Theorem D.1.2.1, p. 747. A regular Haar measure on the quotient
is normalized by Weil's formula on continuous compactly supported test functions. -/
def IsWeilQuotientMeasure (μ : Measure G) (μH : Measure H) (ν : Measure (G ⧸ H)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν

/-- Paper: Theorem D.1.2.1, p. 747. Taking the quotient by the trivial
subgroup, normalized to mass one, recovers the pushforward of the group measure. -/
theorem isWeilQuotientMeasure_bot (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    IsWeilQuotientMeasure (⊥ : Subgroup G) μ Measure.count
      (μ.map (QuotientGroup.mk : G → G ⧸ (⊥ : Subgroup G))) := by
  let : BorelSpace (G ⧸ (⊥ : Subgroup G)) := ⟨rfl⟩
  let e := (QuotientGroup.quotientBot (G := G)).symm
  let h := e.toEquiv.toHomeomorphOfContinuousOpen
    QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe
  refine ⟨e.isHaarMeasure_map μ h.continuous h.symm.continuous, Measure.Regular.map h, ?_⟩
  intro f _
  have hcoset (q : G ⧸ (⊥ : Subgroup G)) :
      lcaCosetIntegral (⊥ : Subgroup G) Measure.count f q = f (h.symm q) := by
    have hout : q.out = h.symm q :=
      h.injective ((Quotient.out_eq' q).trans (h.apply_symm_apply q).symm)
    simp [lcaCosetIntegral, Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G)), hout]
  simp_rw [hcoset]
  change (∫ x, f x ∂μ) = ∫ q, f (h.symm q) ∂(μ.map h)
  simpa only [Homeomorph.toMeasurableEquiv_coe, h.symm_apply_apply] using
    (integral_map_equiv (μ := μ) h.toMeasurableEquiv (fun q ↦ f (h.symm q))).symm

include hH in
/-- Given regular Haar measures on a closed subgroup and its quotient, Weil
integration fixes the ambient regular Haar measure. Adapted from the
multiplicative Tamagawa construction in RiemannMasullo commit f606c45
(Apache-2.0). -/
theorem weilAmbientMeasure_existsUnique (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular] :
    ∃! μ : Measure G, μ.IsHaarMeasure ∧ μ.Regular ∧ IsWeilQuotientMeasure H μ μH ν := by
  letI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let h := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let μ := h.inducedMeasure μH ν
  have hweil : IsWeilQuotientMeasure H μ μH ν := by
    refine ⟨inferInstance, inferInstance, fun f hf => ?_⟩
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    change (∫ x, fc x ∂μ) = _
    rw [integral_inducedMeasure_complex h μH ν fc, h.integrate_apply]
    refine integral_congr_ae (.of_forall fun q => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change h.pushforward μH fc ((QuotientGroup.mk' H) x) = _
    rw [h.pushforward_apply_apply]
    exact (lcaCosetIntegral_mk H μH f x).symm
  refine ⟨μ, ⟨inferInstanceAs (h.inducedMeasure μH ν).IsHaarMeasure,
    inferInstanceAs (h.inducedMeasure μH ν).Regular, hweil⟩, ?_⟩
  rintro μ' ⟨_, hμ'R, hweil'⟩
  letI : μ'.Regular := hμ'R
  letI : μ.Regular := inferInstanceAs (h.inducedMeasure μH ν).Regular
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(G, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  apply Complex.ofReal_injective
  simpa only [fc, ContinuousMap.coe_mk, integral_complex_ofReal] using
    (hweil'.2.2 fc hc).trans (hweil.2.2 fc hc).symm

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]

include hH in
/-- Paper: Theorem D.1.2.1, p. 747. There is a unique quotient Haar measure
satisfying Weil's formula for compactly supported continuous functions. -/
theorem weilQuotientMeasure_existsUnique :
    ∃! ν : Measure (G ⧸ H), IsWeilQuotientMeasure H μ μH ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let h := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let ν₀ : Measure (G ⧸ H) := MeasureTheory.Measure.haar
  let μ₀ := h.inducedMeasure μH ν₀
  let c := Measure.haarScalarFactor μ μ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  have hμ : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul_of_regular μ μ₀
  let ν := c • ν₀
  let hνH : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hc
  have hν : IsWeilQuotientMeasure H μ μH ν := by
    refine ⟨hνH, inferInstance, ?_⟩
    intro f hf
    let f' : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    have hfib (q : G ⧸ H) : h.pushforward μH f' q = lcaCosetIntegral H μH f q := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change h.pushforward μH f' ((QuotientGroup.mk' H) x) = _
      rw [h.pushforward_apply_apply]
      exact (lcaCosetIntegral_mk H μH f x).symm
    change (∫ x, f' x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂(c • ν₀)
    rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_inducedMeasure_complex h μH ν₀ f', h.integrate_apply]
    simp_rw [hfib]
  refine ⟨ν, hν, ?_⟩
  intro ν' hν'
  let : ν'.IsHaarMeasure := hν'.1
  let : ν'.Regular := hν'.2.1
  let d := Measure.haarScalarFactor ν' ν
  have hνeq : ν' = d • ν := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
  obtain ⟨g, hg, hnonneg, hpos⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : C(G, ℂ) := ⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  have hf : HasCompactSupport (f : G → ℂ) := hg.comp_left Complex.ofReal_zero
  have hI : (∫ x, f x ∂μ) ≠ 0 := by
    change (∫ x, (g x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hg hnonneg hpos).ne'
  have hscalar := hν'.2.2 f hf
  rw [hνeq, integral_smul_nnreal_measure, ← hν.2.2 f hf] at hscalar
  have hunit : d = 1 := by
    have he : (1 : ℂ) * (∫ x, f x ∂μ) = ((d : ℝ) : ℂ) * (∫ x, f x ∂μ) := by
      simpa only [one_mul, NNReal.smul_def, Complex.real_smul] using hscalar
    exact_mod_cast (mul_right_cancel₀ hI he).symm
  simpa [hunit] using hνeq

/-- Haar measure on the translate of the subgroup specified by a quotient point. -/
def quotientCosetMeasure (q : G ⧸ H) : Measure G :=
  μH.map (fun h : H => q.out * (h : G))

omit [T2Space G] [LocallyCompactSpace G] [μH.Regular] in
/-- The translated measure is independent of the chosen representative. -/
theorem quotientCosetMeasure_mk (x : G) :
    quotientCosetMeasure H μH (QuotientGroup.mk x) = μH.map (fun h : H => x * (h : G)) := by
  let tr (x : G) (h : H) := x * (h : G)
  have htr (x : G) : Continuous (tr x) := continuous_const.mul continuous_subtype_val
  let y : G := (QuotientGroup.mk x : G ⧸ H).out
  have hy : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk x := Quotient.out_eq' _
  let k : H := ⟨y⁻¹ * x, QuotientGroup.eq.mp hy⟩
  have htr_eq : tr x = tr y ∘ (k * ·) := by
    funext h
    simp [tr, k, ← mul_assoc]
  change μH.map (tr y) = μH.map (tr x)
  rw [htr_eq, ← Measure.map_map (htr y).measurable
    (measurePreserving_mul_left μH k).measurable, (measurePreserving_mul_left μH k).map_eq]

include hH in
/-- The translated subgroup measures form a measurable family. The proof compares
their open-set masses with continuous compact-support fibre integrals. -/
theorem quotientCosetMeasure_measurable [SigmaCompactSpace G] :
    Measurable (quotientCosetMeasure H μH) := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let K := CompactExhaustion.choice G
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let tr (x : G) (h : H) : G := x * (h : G)
  have htr (x : G) : Continuous (tr x) := continuous_const.mul continuous_subtype_val
  let κ : G ⧸ H → Measure G := quotientCosetMeasure H μH
  change Measurable κ
  have hgmeas (g : CompactlySupportedContinuousMap G ℝ) :
      Measurable (fun x ↦ ENNReal.ofReal (g x)) :=
    (ENNReal.continuous_ofReal.comp g.continuous).measurable
  have htest (g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) (q : G ⧸ H) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂κ q) = ENNReal.ofReal (ses.pushforward μH g q) := by
    have hq : (QuotientGroup.mk' H) q.out = q := Quotient.out_eq' q
    have hpush := ses.pushforward_apply_apply μH g q.out
    rw [hq] at hpush
    rw [show κ q = μH.map (tr q.out) from rfl,
      lintegral_map (hgmeas g) (htr q.out).measurable, hpush]
    exact (ofReal_integral_eq_lintegral_ofReal (μ := μH) (ses.pullback g q.out).integrable
      (.of_forall fun h ↦ hg (tr q.out h))).symm

  -- Compactly supported functions approximate the measure of each open fibre from below.
  have hopen {U : Set G} (hU : IsOpen U) : Measurable (fun q ↦ κ q U) := by
    suffices LowerSemicontinuous (fun q ↦ κ q U) from this.measurable
    let F := {g : CompactlySupportedContinuousMap G ℝ //
      tsupport g ⊆ U ∧ ∀ x, g x ∈ Icc 0 1}
    have hsup (q : G ⧸ H) :
        κ q U = ⨆ g : F, ENNReal.ofReal (ses.pushforward μH g.1 q) := by
      rw [show κ q U = μH (tr q.out ⁻¹' U) from
        Measure.map_apply (htr q.out).measurable hU.measurableSet]
      apply le_antisymm
      · refine le_of_forall_lt fun r hr ↦ ?_
        obtain ⟨L, hLU, hL, hrL⟩ := (hU.preimage (htr q.out)).exists_lt_isCompact (μ := μH) hr
        obtain ⟨g, hgL, hgcompact, hgU, hg⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
          (hL.image (htr q.out)) hU (image_subset_iff.mpr hLU)
        let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgcompact⟩
        refine hrL.trans_le (le_iSup_of_le (⟨g', hgU, hg⟩ : F) ?_)
        rw [← htest g' (fun x ↦ (hg x).1), show κ q = μH.map (tr q.out) from rfl,
          lintegral_map (hgmeas g') (htr q.out).measurable, ← lintegral_indicator_one hL.measurableSet]
        apply lintegral_mono
        intro h
        by_cases hh : h ∈ L
        · change L.indicator 1 h ≤ ENNReal.ofReal (g (tr q.out h))
          simp [hh, hgL (mem_image_of_mem _ hh)]
        · simp [hh]
      · refine iSup_le fun g ↦ ?_
        rw [← htest g.1 (fun x ↦ (g.2.2 x).1), show κ q = μH.map (tr q.out) from rfl,
          lintegral_map (hgmeas g.1) (htr q.out).measurable,
          ← lintegral_indicator_one (hU.preimage (htr q.out)).measurableSet]
        apply lintegral_mono
        intro h
        by_cases hh : tr q.out h ∈ U
        · simpa [hh] using ENNReal.ofReal_le_ofReal (g.2.2 (tr q.out h)).2
        · have hz : g.1 (tr q.out h) = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hm ↦ hh (g.2.1 hm))
          simp [hz, hh]
    simp_rw [hsup]
    exact lowerSemicontinuous_iSup fun g ↦
      (ENNReal.continuous_ofReal.comp (ses.pushforward μH g.1).continuous).lowerSemicontinuous

  have hκcompact (q : G ⧸ H) {L : Set G} (hL : IsCompact L) : κ q L < ⊤ := by
    rw [show κ q L = μH (tr q.out ⁻¹' L) from
      Measure.map_apply (htr q.out).measurable hL.measurableSet]
    exact ((Homeomorph.mulLeft q.out).isClosedEmbedding.comp
      ses.isClosedEmbedding).isCompact_preimage hL |>.measure_lt_top

  -- The restrictions to relatively compact open sets are finite on each fibre.
  let U (n : ℕ) := interior (K n)
  have hU : ⋃ n, U n = univ := by
    refine iUnion_eq_univ_iff.mpr fun x ↦ ?_
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, K.subset_interior_succ n hn⟩
  have hrestrict (n : ℕ) : Measurable (fun q ↦ (κ q).restrict (U n)) := by
    let (q : G ⧸ H) : IsFiniteMeasure ((κ q).restrict (U n)) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono interior_subset).trans_lt (hκcompact q (K.isCompact n))⟩
    refine Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
    · intro S hS
      change IsOpen S at hS
      simpa only [Measure.restrict_apply hS.measurableSet] using
        hopen (hS.inter (isOpen_interior : IsOpen (U n)))
    · simpa only [Measure.restrict_apply_univ] using hopen (isOpen_interior : IsOpen (U n))
  refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
  have heq (q : G ⧸ H) : κ q S = ⨆ n, (κ q).restrict (U n) S := by
    have hmono : Monotone (fun n ↦ S ∩ U n) :=
      monotone_const.inter (fun _ _ h ↦ interior_mono (K.subset h))
    simpa only [← inter_iUnion, hU, inter_univ, Measure.restrict_apply hS] using
      hmono.measure_iUnion (μ := κ q)
  simp_rw [heq]
  exact Measurable.iSup fun n ↦ (Measure.measurable_coe hS).comp (hrestrict n)

include hH in
/-- Integrating the translated subgroup measures against the normalized quotient measure
recovers the group measure. -/
theorem weilMeasure_eq_bind [SigmaFinite μ] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) :
    let κ : G ⧸ H → Measure G := fun q ↦ μH.map (fun h : H ↦ q.out * (h : G))
    Measurable κ ∧ ν.bind κ = μ := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : SigmaCompactSpace G := sigmaCompactSpace_of_sigmaFinite_haar μ
  let K := CompactExhaustion.choice G
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let tr (x : G) (h : H) : G := x * (h : G)
  have htr (x : G) : Continuous (tr x) := continuous_const.mul continuous_subtype_val
  let κ : G ⧸ H → Measure G := fun q ↦ μH.map (tr q.out)
  change Measurable κ ∧ ν.bind κ = μ

  have hgmeas (g : CompactlySupportedContinuousMap G ℝ) :
      Measurable (fun x ↦ ENNReal.ofReal (g x)) :=
    (ENNReal.continuous_ofReal.comp g.continuous).measurable
  have htest (g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) (q : G ⧸ H) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂κ q) = ENNReal.ofReal (ses.pushforward μH g q) := by
    have hq : (QuotientGroup.mk' H) q.out = q := Quotient.out_eq' q
    have hpush := ses.pushforward_apply_apply μH g q.out
    rw [hq] at hpush
    rw [show κ q = μH.map (tr q.out) from rfl,
      lintegral_map (hgmeas g) (htr q.out).measurable, hpush]
    exact (ofReal_integral_eq_lintegral_ofReal (μ := μH) (ses.pullback g q.out).integrable
      (.of_forall fun h ↦ hg (tr q.out h))).symm

  have hκ : Measurable κ := quotientCosetMeasure_measurable H hH μH

  let ρ := ν.bind κ
  have htests (g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂ρ) = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    let gℂ : C(G, ℂ) := ⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
    have hgℂ : HasCompactSupport gℂ := g.hasCompactSupport.comp_left Complex.ofReal_zero
    have hcoset (q : G ⧸ H) : lcaCosetIntegral H μH gℂ q = (ses.pushforward μH g q : ℂ) := by
      have hq : (QuotientGroup.mk' H) q.out = q := Quotient.out_eq' q
      rw [← hq, ses.pushforward_apply_apply]
      rw [hq]
      exact integral_complex_ofReal
    have hgPush : ∀ q, 0 ≤ ses.pushforward μH g q := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change 0 ≤ ses.pushforward μH g ((QuotientGroup.mk' H) x)
      rw [ses.pushforward_apply_apply]
      exact integral_nonneg fun h ↦ hg (tr x h)
    have heq : (∫ x, g x ∂μ) = ∫ q, ses.pushforward μH g q ∂ν := by
      have heq := hν.2.2 gℂ hgℂ
      simp_rw [hcoset] at heq
      change (∫ x, (g x : ℂ) ∂μ) = _ at heq
      rw [integral_complex_ofReal, integral_complex_ofReal] at heq
      exact Complex.ofReal_injective heq
    rw [Measure.lintegral_bind hκ.aemeasurable (hgmeas g).aemeasurable]
    simp_rw [htest g hg]
    rw [← ofReal_integral_eq_lintegral_ofReal (ses.pushforward μH g).integrable
      (.of_forall hgPush), ← ofReal_integral_eq_lintegral_ofReal g.integrable (.of_forall hg), heq]

  let : IsFiniteMeasureOnCompacts ρ := ⟨by
    intro L hL
    obtain ⟨g, hgL, hgcompact, -, hg⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hL isOpen_univ (subset_univ L)
    let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgcompact⟩
    calc
      ρ L = ∫⁻ x, L.indicator 1 x ∂ρ := (lintegral_indicator_one hL.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (g' x) ∂ρ := by
        apply lintegral_mono
        intro x
        change L.indicator 1 x ≤ ENNReal.ofReal (g x)
        by_cases hx : x ∈ L
        · simp [hx, hgL hx]
        · simp [hx]
      _ = ∫⁻ x, ENNReal.ofReal (g' x) ∂μ := htests g' (fun x ↦ (hg x).1)
      _ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal g'.integrable (.of_forall fun x ↦ (hg x).1)]
        exact ENNReal.ofReal_lt_top⟩

  have hrepresentative (x : G) : κ (QuotientGroup.mk x) = μH.map (tr x) :=
    quotientCosetMeasure_mk H μH x

  let : ρ.IsMulLeftInvariant := ⟨by
    intro x
    have hx : Measurable (x * · : G → G) := (continuous_const.mul continuous_id).measurable
    have hcov (q : G ⧸ H) : (κ q).map (x * ·) = κ (QuotientGroup.mk x * q) := by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      change (κ (QuotientGroup.mk y)).map (x * ·) =
        κ ((QuotientGroup.mk' H) x * (QuotientGroup.mk' H) y)
      rw [← (QuotientGroup.mk' H).map_mul x y]
      change (κ (QuotientGroup.mk y)).map (x * ·) = κ (QuotientGroup.mk (x * y))
      rw [hrepresentative, hrepresentative, Measure.map_map hx (htr y).measurable]
      simp only [tr, Function.comp_def, mul_assoc]
    change (ν.bind κ).map (x * ·) = ν.bind κ
    ext S hS
    rw [Measure.map_apply hx hS, Measure.bind_apply (hx hS) hκ.aemeasurable,
      Measure.bind_apply hS hκ.aemeasurable]
    have hs (q : G ⧸ H) : κ q ((x * ·) ⁻¹' S) = κ (QuotientGroup.mk x * q) S := by
      rw [← Measure.map_apply hx hS, hcov]
    simp_rw [hs]
    have hshift := measurePreserving_mul_left ν (QuotientGroup.mk x)
    have hmeas : Measurable (fun q : G ⧸ H => κ q S) :=
      (Measure.measurable_coe hS).comp hκ
    rw [← lintegral_map hmeas hshift.measurable, hshift.map_eq]⟩

  -- Uniqueness on relatively compact sets extends along the exhaustion.
  let c := Measure.haarScalarFactor ρ μ
  have hscalar : ρ = c • μ := by
    ext S hS
    have hmono : Monotone (fun n ↦ S ∩ K n) :=
      monotone_const.inter (fun _ _ h ↦ K.subset h)
    have hcover : ⋃ n, S ∩ K n = S := by rw [← inter_iUnion, K.iUnion_eq, inter_univ]
    rw [← hcover, hmono.measure_iUnion, hmono.measure_iUnion]
    congr with n
    exact Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ρ μ
      ((K.isCompact n).closure_of_subset inter_subset_right)
  obtain ⟨g, hgcompact, hg, hgpos⟩ := exists_continuous_nonneg_pos (1 : G)
  let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgcompact⟩
  have hpos : 0 < ∫ x, g' x ∂μ :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hgcompact hg hgpos
  have heq := htests g' hg
  rw [← ofReal_integral_eq_lintegral_ofReal g'.integrable (.of_forall hg),
    ← ofReal_integral_eq_lintegral_ofReal g'.integrable (.of_forall hg), hscalar,
    integral_smul_nnreal_measure] at heq
  have heq' : (c : ℝ) * (∫ x, g' x ∂μ) = ∫ x, g' x ∂μ :=
    (ENNReal.ofReal_eq_ofReal_iff (by positivity) hpos.le).mp heq
  have hc : c = 1 := by
    exact_mod_cast (mul_right_cancel₀ hpos.ne' (heq'.trans (one_mul _).symm))
  exact ⟨hκ, by simpa [hc] using hscalar⟩

include hH in
/-- Paper: Lemma D.1.2.3, p. 747. For a σ-finite group, finiteness of
the iterated integral of the norm implies integrability and Weil's formula. -/
theorem integrable_of_weilNormIntegral [SigmaFinite μ] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {f : G → ℂ} (hf : Measurable f)
    (hfin : (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖₊ ∂μH ∂ν) < (⊤ : ℝ≥0∞)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
  let tr (q : G ⧸ H) (h : H) : G := q.out * (h : G)
  have htr (q : G ⧸ H) : Measurable (tr q) :=
    (continuous_const.mul continuous_subtype_val).measurable
  let κ : G ⧸ H → Measure G := fun q ↦ μH.map (tr q)
  have hκ : Measurable κ ∧ ν.bind κ = μ := weilMeasure_eq_bind H hH μ μH ν hν
  have hfint : Integrable f μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← hκ.2, Measure.lintegral_bind hκ.1.aemeasurable
      hf.enorm.aemeasurable]
    have hnorm (q : G ⧸ H) : (∫⁻ x, ‖f x‖ₑ ∂κ q) = ∫⁻ h : H, ‖f (tr q h)‖ₑ ∂μH :=
      lintegral_map hf.enorm (htr q)
    simp_rw [hnorm, enorm_eq_nnnorm]
    exact hfin
  refine ⟨hfint, ?_⟩
  let kernel : ProbabilityTheory.Kernel (G ⧸ H) G := ⟨κ, hκ.1⟩
  have hcomp := Measure.comp_eq_comp_const_apply (κ := kernel) (μ := ν)
  have hInt : Integrable f ((kernel.comp (ProbabilityTheory.Kernel.const Unit ν)) ()) := by
    rwa [← hcomp, show ν.bind (⇑kernel) = μ from hκ.2]
  calc
    (∫ x, f x ∂μ) = ∫ q, ∫ x, f x ∂κ q ∂ν := by
      rw [← hκ.2, show ν.bind κ = _ from hcomp]
      have heq := ProbabilityTheory.Kernel.integral_comp hInt
      rw [ProbabilityTheory.Kernel.const_apply] at heq
      exact heq
    _ = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
      congr with q
      exact integral_map (htr q).aemeasurable hf.aestronglyMeasurable


include hH in
/-- On sigma-finite groups, a Haar-integrable function is integrable on almost
every represented coset, and its quotient integral recovers the group integral. -/
theorem weilQuotientIntegral_L1_sigmaFinite [SigmaFinite μ] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {f : G → ℂ} (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H => f (q.out * (h : G))) μH) ∧
      Integrable (lcaCosetIntegral H μH f) ν ∧
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
  let tr (q : G ⧸ H) (h : H) : G := q.out * (h : G)
  have htr (q : G ⧸ H) : Measurable (tr q) :=
    (continuous_const.mul continuous_subtype_val).measurable
  let κ : G ⧸ H → Measure G := fun q => μH.map (tr q)
  have hk : Measurable κ ∧ ν.bind κ = μ := weilMeasure_eq_bind H hH μ μH ν hν
  let kernel : ProbabilityTheory.Kernel (G ⧸ H) G := ⟨κ, hk.1⟩
  have hkernel (q : G ⧸ H) : kernel q = κ q := rfl
  have he := Measure.comp_eq_comp_const_apply (κ := kernel) (μ := ν)
  have hcomp : Integrable f ((kernel.comp (ProbabilityTheory.Kernel.const Unit ν)) ()) := by
    rw [← he, show ν.bind (⇑kernel) = μ from hk.2]
    exact hf
  have hF : ∀ᵐ q ∂ν, Integrable f (κ q) := by
    simpa only [ProbabilityTheory.Kernel.const_apply, hkernel] using hcomp.ae_of_comp
  have hEq : (fun q => ∫ x, f x ∂κ q) =ᵐ[ν] lcaCosetIntegral H μH f := by
    filter_upwards [hF] with q hq
    exact integral_map (htr q).aemeasurable hq.aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hF] with q hq
    exact (integrable_map_measure hq.aestronglyMeasurable (htr q).aemeasurable).mp hq
  · apply Integrable.congr _ hEq
    simpa only [ProbabilityTheory.Kernel.const_apply, hkernel] using hcomp.integral_comp
  · rw [← integral_congr_ae hEq, ← hk.2, show ν.bind κ = _ from he]
    simpa only [ProbabilityTheory.Kernel.const_apply, hkernel] using
      ProbabilityTheory.Kernel.integral_comp hcomp

end Weil

/-- For the full subgroup of the additive reals, every fibre of the constant
function one has infinite absolute integral. The only quotient class has positive mass. -/
theorem weil_arbitraryMeasurable_fiber_counterexample :
    (∫⁻ _ : ℝ, (1 : ℝ≥0∞)) = ∞ ∧
      ¬ Integrable (fun _ : ℝ => (1 : ℂ)) volume ∧
      ¬ (∀ᵐ _ ∂(Measure.dirac () : Measure Unit),
        Integrable (fun _ : ℝ => (1 : ℂ)) volume) := by
  have h : ¬ Integrable (fun _ : ℝ => (1 : ℂ)) volume := by
    intro hf
    have hfin := hf.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin
    simpa [Real.volume_univ] using hfin
  exact ⟨by simp [Real.volume_univ], h, fun ha => h ha.exists.choose_spec⟩

end
end Masullo
