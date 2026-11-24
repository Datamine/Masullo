import GlobalHeckeEulerComparison
import SLocalTateProduct

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ComplexConjugate ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S

/-- Absolute convergence gives a bound on the whole closed half-plane
to the right of any fixed real number greater than one. -/
theorem globalFiniteHeckeEuler_bounded_right (ω : PontryaginDual (K F))
    {r : ℝ} (hr : 1 < r) {s : ℂ} (hs : r ≤ s.re) :
    ‖globalFiniteHeckeEuler F ω s‖ ≤ ‖globalFiniteHeckeEuler F 1 (r : ℂ)‖ := by
  let c (ψ : PontryaginDual (K F)) :=
    heckeEulerCoefficient F (normOneEulerCharacter F ψ) (chosenFiniteUniformizer F)
  have hc (ψ : PontryaginDual (K F)) :
      ∀ v, ‖c ψ v‖ ≤ 1 := norm_heckeEulerCoefficient_le_one F _ _
  have hprod (ψ : PontryaginDual (K F)) (z : ℂ) (hz : 1 < z.re) :
      HasProd (heckeEulerFactor F (c ψ) · z) (globalFiniteHeckeEuler F ψ z) :=
    (heckeEulerProduct_hasProdUniformlyOn F (c ψ) (hc ψ) {z} isCompact_singleton
      (by simpa using hz)).hasProd (mem_singleton z)
  have hone (v : Place F) : c 1 v = 1 := by
    have h (g : IdeleClass F) : normOneEulerCharacter F 1 g = 1 := rfl
    have hu : unramifiedFiniteCharacter F (normOneEulerCharacter F 1) v := fun _ _ ↦ h _
    simp only [c, heckeEulerCoefficient, ite_eq_left hu, h, Circle.coe_one]
  have hfactor (v : Place F) :
      ‖heckeEulerFactor F (c ω) v s‖ ≤ ‖heckeEulerFactor F (c 1) v (r : ℂ)‖ := by
    let q : ℝ := v.asIdeal.absNorm
    have hq : 1 < q := by
      dsimp only [q]
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hq₀ := zero_lt_one.trans hq
    let a := q ^ (-r)
    let w := c ω v * (q : ℂ) ^ (-s)
    have ha : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    have hw : ‖w‖ ≤ a := by
      rw [show ‖w‖ = ‖c ω v‖ * q ^ (-s.re) by
        simp only [w, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re]]
      exact (mul_le_of_le_one_left (Real.rpow_nonneg hq₀.le _) (hc ω v)).trans
        (Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hs))
    have hb : 1 - a ≤ ‖1 - w‖ := by
      have h := norm_sub_norm_le (1 : ℂ) w
      rw [norm_one] at h
      linarith
    have hreal : (q : ℂ) ^ (-(r : ℂ)) = (a : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
    change ‖((1 - w)⁻¹ : ℂ)‖ ≤
      ‖(1 - c 1 v * (q : ℂ) ^ (-(r : ℂ)))⁻¹‖
    rw [hone, one_mul, hreal, norm_inv, norm_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_of_nonneg (sub_nonneg.mpr ha.le)]
    exact inv_anti₀ (sub_pos.mpr ha) hb
  apply le_of_tendsto_of_tendsto (hprod ω s (hr.trans_le hs)).norm
    (hprod 1 (r : ℂ) (by simpa using hr)).norm
  refine Eventually.of_forall fun A ↦ ?_
  exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hfactor v)

local instance (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

section LocalBounds

variable (S : Finset (Place F))
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure]

/-- A finite Tate multiplier is bounded on each vertical line with
positive real part, including for ramified phases. -/
theorem finiteTateMultiplier_bounded_vertical
    (χ : ∀ v : S, (v.val.adicCompletion F)ˣ →ₜ* Circle)
    (v : S) (ε : ℂ → ℂ) (hε : IsFiniteTateMultiplier F S μ χ v ε)
    {σ : ℝ} (hσ : 0 < σ) : ∃ C > 0, ∀ z : ℂ, z.re = σ → ‖ε z‖ ≤ C := by
  by_cases hχ : finiteZetaUnramified F v.val (χ v)
  · obtain ⟨a, ha, _, he⟩ := hε.2.2.2.2 hχ
    let d := multiplicity v.val.asIdeal (differentIdeal ℤ (𝓞 F))
    let l := Real.log (v.val.asIdeal.absNorm : ℝ)
    refine ⟨Real.exp ((d : ℝ) * (σ - 1 / 2) * l), Real.exp_pos _, fun z hz ↦ ?_⟩
    rw [he, Complex.norm_exp]
    have hh : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num [Complex.div_ofNat_re]
    simp only [d, l, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      ha, hz, hh, mul_zero, zero_mul, add_zero, sub_zero, le_refl]
  · obtain ⟨g, D, hD, hg⟩ := exists_cleared_finite_reference F S μ (fun w ↦ (χ w)⁻¹) v
    letI : (additiveHaarDifferent F v.val).IsAddHaarMeasure := additiveHaarDifferent_isHaar F v.val
    obtain ⟨f, hf⟩ := finitePlaceFourierTest_tamagawa_surjective F v.val g
    let M := ∫ u : (v.val.adicCompletion F)ˣ,
      ‖f.val u.val * (χ v u : ℂ) * finiteZetaWeight F v.val (σ : ℂ) u‖ ∂μ v
    have hM : 0 ≤ M := integral_nonneg fun _ ↦ norm_nonneg _
    refine ⟨(M + 1) / ‖D‖, div_pos (by linarith) (norm_pos_iff.mpr hD), fun z hz ↦ ?_⟩
    have he := hε.2.2.2.1 f z
    change finiteProductClearedLocal F S μ χ v f z =
      ε z * finiteProductClearedLocal F S μ (fun w ↦ (χ w)⁻¹) v
        (finitePlaceFourierTest F v.val (additiveHaarDifferent F v.val) f) (1 - z) at he
    rw [hf, hg, finiteProductClearedLocal, ite_eq_right hχ,
      ← (finiteZetaContinuation_eq_integral F v.val (μ v) (χ v) f z (hz.symm ▸ hσ)).2] at he
    have hbound : ‖finiteZetaIntegral F v.val (μ v) (χ v) f z‖ ≤ M := by
      unfold finiteZetaIntegral
      apply (norm_integral_le_integral_norm _).trans_eq
      apply integral_congr_ae
      exact Eventually.of_forall fun u ↦ by
        simp [finiteZetaWeight, Complex.norm_exp, Complex.mul_re, hz]
    rw [he, norm_mul] at hbound
    exact (le_div_iff₀ (norm_pos_iff.mpr hD)).mpr (hbound.trans (by linarith))

end LocalBounds

theorem reflect_punctured (c : ℂ) :
    Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] c) (𝓝[≠] (1 - c)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_const.sub continuous_id).continuousAt (x := c)).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change 1 - z ≠ 1 - c
    exact fun h ↦ hz (sub_right_injective h)

private theorem selectedFourier_eq_global_of_different (S : Finset (Place F))
    (hS : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) (f : E F S) :
    (sLocalSelectedFourier F S f).val = GlobalBruhat.fourier F f.val := by
  have ht : sLocalFourierTailVolume F S = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv : ¬ v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h ↦ v.property (hS v.val h)
    simp [differentPrimeMass, multiplicity_eq_zero.mpr hv]
  simp only [sLocalSelectedFourier, ht, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_smul]
  change sLocalBruhatProjection F S (GlobalBruhat.fourier F f.val) =
    GlobalBruhat.fourier F f.val
  exact sLocalBruhatProjection_fixes F S _
    (sLocalFourier_preserves_stage_of_different F S hS f.val f.property)

/-- One conductor stage works for the character, its inverse and the different. -/
theorem exists_globalHeckeTateStage (ω : PontryaginDual (K F)) :
    ∃ S : Finset (Place F), Surjective (sIdeleClassInclusion F S) ∧
      globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) ∧
      globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) ∧
      ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S := by
  obtain ⟨S₀, h₀⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨S₁, h₁⟩ := exists_homogeneousThetaPlaceBase F ω⁻¹
  let D := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  let S := (S₀ ∪ S₁) ∪ D
  obtain ⟨hs, hχ⟩ := h₀ S (Finset.subset_union_left.trans Finset.subset_union_left)
  obtain ⟨_, hχ'⟩ := h₁ S (Finset.subset_union_right.trans Finset.subset_union_left)
  exact ⟨S, hs, hχ, hχ', fun v hv ↦ Finset.mem_union_right _ (by simpa [D] using hv)⟩

local instance tateReflectionIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance tateReflectionIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance tateReflectionNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance tateReflectionNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
variable (ω : PontryaginDual (K F))
variable (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (hω' : globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev phase :=
  sLocalNormOneCharacterOfGlobal F ω S hS hω

private abbrev G (f : E F S) :=
  globalZetaContinued F ν f.val (compactIdeleClassCharacter F ω) 0

include μ hν in
private theorem exists_completed_stage_reference :
    ∃ (r : E F S) (C : ℂ) (B : ℂ) (L : ℂ → ℂ),
      C ≠ 0 ∧ B ≠ 0 ∧
      sLocalEulerNormalizedMellin F S (fun v : S ↦ μ v.val)
        (phase F S hS ω hω) r = (fun _ ↦ C) ∧
      G F S ω ν r = (fun z ↦ B * L z) ∧
      MeromorphicOn L univ ∧
      EqOn L (globalCompletedHeckeEuler F ω S hS hω) {z | 1 < z.re} := by
  obtain ⟨r, C, hC, hN, hfin, _⟩ :=
    exists_globalMellin_order_reference F η ω S hS hω μ ν hν
  obtain ⟨B, hB, he⟩ :=
    globalZetaContinued_reference_eq_completedEuler F ω S hS hω η ν μ hν r C hN (hfin 2)
  let L (z : ℂ) := B⁻¹ * G F S ω ν r z
  have hm := globalZetaContinued_meromorphic F ν r.val (compactIdeleClassCharacter F ω)
    (compactIdeleClassCharacter_unitary F ω) 0
  refine ⟨r, C, B, L, hC, hB, hN, ?_,
    fun z hz ↦ (MeromorphicAt.const _ _).mul (hm z hz), ?_⟩
  · funext z
    dsimp only [L]
    rw [← mul_assoc, mul_inv_cancel₀ hB, one_mul]
  · intro z hz
    dsimp only [L]
    rw [show G F S ω ν r z = B * globalCompletedHeckeEuler F ω S hS hω z from he hz,
      ← mul_assoc, inv_mul_cancel₀ hB, one_mul]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem stage_phase_inv :
    phase F S hS ω⁻¹ hω' = (phase F S hS ω hω)⁻¹ := by
  ext k
  obtain ⟨g, rfl⟩ := globalNormOneToSLocal_surjective F S hS k
  rw [phase, sLocalNormOneCharacterOfGlobal_match]
  change (↑((ω g)⁻¹) : ℂ) = ↑((sLocalNormOneCharacterOfGlobal F ω S hS hω
    (globalNormOneToSLocal F S hS g))⁻¹)
  rw [sLocalNormOneCharacterOfGlobal_match]

private theorem conj_ofReal_cpow_uniform {x : ℝ} (hx : 0 ≤ x) (z : ℂ) :
    conj ((x : ℂ) ^ z) = (x : ℂ) ^ conj z := by
  have h := Complex.conj_cpow (x : ℂ) (conj z) (by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm)
  simpa using h.symm

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem globalFiniteHeckeEuler_inv_conj (z : ℂ) :
    globalFiniteHeckeEuler F ω⁻¹ (conj z) = conj (globalFiniteHeckeEuler F ω z) := by
  let c := normOneEulerCharacter F ω
  have he (x : IdeleClass F) : normOneEulerCharacter F ω⁻¹ x = (c x)⁻¹ := rfl
  have hc (v : Place F) :
      heckeEulerCoefficient F (normOneEulerCharacter F ω⁻¹) (chosenFiniteUniformizer F) v =
        conj (heckeEulerCoefficient F c (chosenFiniteUniformizer F) v) := by
    have hi : unramifiedFiniteCharacter F (normOneEulerCharacter F ω⁻¹) v ↔
        unramifiedFiniteCharacter F c v := by
      unfold unramifiedFiniteCharacter
      simp only [he, inv_eq_one]
    unfold heckeEulerCoefficient
    rw [hi]
    split_ifs
    · rw [he, Circle.coe_inv_eq_conj]
    · exact (map_zero _).symm
  unfold globalFiniteHeckeEuler
  have hconj : IsClosedEmbedding (starRingEnd ℂ : ℂ → ℂ) :=
    Complex.conjCLE.toHomeomorph.isClosedEmbedding
  rw [hconj.map_tprod]
  apply tprod_congr
  intro v
  simp only [heckeEulerFactor, hc, map_inv₀, map_sub, map_one, map_mul]
  have h := conj_ofReal_cpow_uniform (x := (v.asIdeal.absNorm : ℝ)) (Nat.cast_nonneg _) (-z)
  simpa only [Complex.ofReal_natCast, map_neg] using
    congrArg (fun u : ℂ ↦ (1 - conj (heckeEulerCoefficient F c (chosenFiniteUniformizer F) v) * u)⁻¹) h.symm

set_option maxHeartbeats 800000 in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Conjugating the argument and inverting the unitary character conjugates
the completed Euler product, including every archimedean factor. -/
theorem globalCompletedHeckeEuler_inv_conj (z : ℂ) :
    globalCompletedHeckeEuler F ω⁻¹ S hS hω' (conj z) =
      conj (globalCompletedHeckeEuler F ω S hS hω z) := by
  have hτ := stage_phase_inv F S hS ω hω hω'
  have hgR (w : ℂ) : Complex.Gammaℝ (conj w) = conj (Complex.Gammaℝ w) := by
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul,
      ← Complex.Gamma_conj, conj_ofReal_cpow_uniform Real.pi_pos.le]
    simp only [map_div₀, map_neg, map_ofNat]
  have hgC (w : ℂ) : Complex.Gammaℂ (conj w) = conj (Complex.Gammaℂ w) := by
    rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, map_mul, map_mul, ← Complex.Gamma_conj,
      ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, conj_ofReal_cpow_uniform (by positivity)]
    simp only [map_neg, Complex.ofReal_ofNat, map_ofNat]
  change
    (archimedeanNumberFieldZetaDenominator F _ _ (conj z))⁻¹ *
        globalFiniteHeckeEuler F ω⁻¹ (conj z) =
      conj ((archimedeanNumberFieldZetaDenominator F _ _ z)⁻¹ * globalFiniteHeckeEuler F ω z)
  rw [globalFiniteHeckeEuler_inv_conj, map_mul, map_inv₀]
  congr 2
  simp only [archimedeanNumberFieldZetaDenominator, map_mul, map_prod, hτ]
  congr 1
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    let a := sLocalRealArchParameters F S (phase F S hS ω hω) v
    have hi := sLocalRealArchParameters_inv F S (phase F S hS ω hω) v
    have hRe := sLocalRealArchParameters_re F S (phase F S hS ω hω) v
    have hconj : conj a.1 = -a.1 := by
      apply Complex.ext <;> simp [a, hRe]
    simp only [realArchZetaDenominator, hi.1, hi.2, map_inv₀, ← hgR, map_add,
      map_natCast]
    change (Complex.Gammaℝ (conj z + -a.1 + ((a.2 % 2 : ℕ) : ℂ)))⁻¹ =
      (Complex.Gammaℝ (conj z + conj a.1 + ((a.2 % 2 : ℕ) : ℂ)))⁻¹
    rw [hconj]
  · refine Finset.prod_congr rfl fun v _ ↦ ?_
    let j := sLocalComplexArchParameters F S (phase F S hS ω hω) v
    have hi := sLocalComplexArchParameters_inv F S (phase F S hS ω hω) v
    have hRe := sLocalComplexArchParameters_re F S (phase F S hS ω hω) v
    have hconj : conj j.1 = -j.1 := by
      apply Complex.ext <;> simp [j, hRe]
    simp only [complexArchZetaDenominator, hi, Int.natAbs_neg, map_inv₀, ← hgC, map_add,
      map_div₀, map_natCast, map_ofNat]
    change (Complex.Gammaℂ (conj z + -j.1 + (j.2.natAbs : ℂ) / 2))⁻¹ =
      (Complex.Gammaℂ (conj z + conj j.1 + (j.2.natAbs : ℂ) / 2))⁻¹
    rw [hconj]

set_option maxHeartbeats 700000 in
include μ hν in
/-- The completed Euler reflection factor is a nonzero constant times the
actual product of the selected-place Tate multipliers on any stage containing
the different. In particular it is bounded on each positive vertical line. -/
theorem exists_globalCompletedHecke_tateReflection
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    ∃ (L L' ε : ℂ → ℂ),
      MeromorphicOn L univ ∧ MeromorphicOn L' univ ∧
      EqOn L (globalCompletedHeckeEuler F ω S hS hω) {z | 1 < z.re} ∧
      EqOn L' (globalCompletedHeckeEuler F ω⁻¹ S hS hω') {z | 1 < z.re} ∧
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∃ (e : S → ℂ → ℂ) (A : ℂ), A ≠ 0 ∧
        (∀ v, IsFiniteTateMultiplier F S (fun w : S ↦ μ w.val)
          (sLocalFiniteZetaPhases F S (phase F S hS ω hω)) v (e v)) ∧
        ε = fun z ↦ A * sLocalTateEpsilonProduct F S (phase F S hS ω hω) e z) ∧
      (∀ σ : ℝ, 0 < σ → ∃ C > 0, ∀ z : ℂ, z.re = σ → ‖ε z‖ ≤ C) ∧
      ∀ c, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] L * ε := by
  let σ := phase F S hS ω hω
  let τ := phase F S hS ω⁻¹ hω'
  let m (v : S) := μ v.val
  obtain ⟨r, C, B, L, hC, hB, hN, hG, hL, he⟩ :=
    exists_completed_stage_reference F S hS ω hω η ν μ hν
  obtain ⟨r', C', B', L', hC', hB', hN', hG', hL', he'⟩ :=
    exists_completed_stage_reference F S hS ω⁻¹ hω' η ν μ hν
  obtain ⟨e, heT, hP, hPn, _, hFE⟩ := exists_sLocalTateProduct_fourier F S m σ
  let P := sLocalTateEpsilonProduct F S σ e
  let A := (B * C') / (B' * C)
  let ε (z : ℂ) := A * P z
  have hA : A ≠ 0 := div_ne_zero (mul_ne_zero hB hC') (mul_ne_zero hB' hC)
  have hτ : τ = σ⁻¹ := stage_phase_inv F S hS ω hω hω'
  refine ⟨L, L', ε, hL, hL', he, he', analyticOnNhd_const.mul hP,
    fun z ↦ mul_ne_zero hA (hPn z), ⟨e, A, hA, heT, rfl⟩, ?_, ?_⟩
  · intro a ha
    choose u hu hb using fun v : S ↦
      finiteTateMultiplier_bounded_vertical F S m (sLocalFiniteZetaPhases F S σ) v (e v) (heT v) ha
    refine ⟨‖A‖ * ∏ v : S, u v,
      mul_pos (norm_pos_iff.mpr hA) (Finset.prod_pos fun v _ ↦ hu v), fun z hz ↦ ?_⟩
    have hnorm : ‖P z‖ = ∏ v : S, ‖e v z‖ := by
      simp [P, sLocalTateEpsilonProduct, norm_prod, norm_pow]
    rw [show ‖ε z‖ = ‖A‖ * ‖P z‖ from norm_mul _ _, hnorm]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun v _ ↦ norm_nonneg _) (fun v _ ↦ hb v z hz)) (norm_nonneg _)
  · intro c
    let f := sLocalSelectedFourier F S r
    have hf : f.val = GlobalBruhat.fourier F r.val :=
      selectedFourier_eq_global_of_different F S hD r
    have hCross := globalContinuedMellin_cross_normalized F η ω⁻¹ S hS hω' μ ν hν
      f r' (1 - c)
    filter_upwards [(reflect_punctured c).eventually hCross] with z hz
    have hlocal := hFE r z
    change sLocalEulerNormalizedMellin F S m σ r z =
      P z * sLocalEulerNormalizedMellin F S m σ⁻¹ f (1 - z) at hlocal
    rw [show sLocalEulerNormalizedMellin F S m σ r z = C from congrFun hN z, ← hτ] at hlocal
    change G F S ω⁻¹ ν f (1 - z) *
        sLocalEulerNormalizedMellin F S m τ r' (1 - z) =
      G F S ω⁻¹ ν r' (1 - z) * sLocalEulerNormalizedMellin F S m τ f (1 - z) at hz
    have hreflect : G F S ω⁻¹ ν f (1 - z) = G F S ω ν r z := by
      unfold G
      rw [hf]
      exact (globalZetaContinued_compact_functionalEquation F ν r.val ω z).symm
    rw [hreflect, hG, hN', hG'] at hz
    change B * L z * C' = (B' * L' (1 - z)) *
      sLocalEulerNormalizedMellin F S m τ f (1 - z) at hz
    have heq := congrArg (P z * ·) hz
    have heq' : P z * (B * L z * C') = B' * L' (1 - z) * C := by
      calc
        _ = P z * ((B' * L' (1 - z)) * sLocalEulerNormalizedMellin F S m τ f (1 - z)) := heq
        _ = (B' * L' (1 - z)) * (P z * sLocalEulerNormalizedMellin F S m τ f (1 - z)) := by ring
        _ = _ := by rw [← hlocal]
    change L' (1 - z) = L z * (A * P z)
    calc
      _ = (P z * (B * L z * C')) / (B' * C) :=
        (eq_div_iff (mul_ne_zero hB' hC)).mpr (by rw [heq']; ring)
      _ = _ := by dsimp only [A]; ring

/-- The reciprocal archimedean product in the Tate stage. -/
abbrev completedTateReciprocalArch :=
  archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S (phase F S hS ω hω))
    (sLocalComplexArchParameters F S (phase F S hS ω hω))

include μ hν in
/-- The actual finite Euler continuations satisfy the Tate reflection
identity with the Gamma factors cleared, also at exceptional parameters
in the sense of punctured germs. -/
theorem exists_globalFiniteHecke_tateReflection
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    ∃ (f f' ε : ℂ → ℂ),
      MeromorphicOn f univ ∧ MeromorphicOn f' univ ∧
      EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      EqOn f' (globalFiniteHeckeEuler F ω⁻¹) {z | 1 < z.re} ∧
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ σ : ℝ, 0 < σ → ∃ C > 0, ∀ z : ℂ, z.re = σ → ‖ε z‖ ≤ C) ∧
      ∀ c, (fun z ↦ completedTateReciprocalArch F S hS ω hω z * f' (1 - z)) =ᶠ[𝓝[≠] c]
        fun z ↦ f z * completedTateReciprocalArch F S hS ω⁻¹ hω' (1 - z) * ε z := by
  obtain ⟨L, L', ε, hL, hL', he, he', hε, hε₀, _, hbound, hreflect⟩ :=
    exists_globalCompletedHecke_tateReflection F S hS ω hω hω' η ν μ hν hD
  obtain ⟨f, hf, hfe, _⟩ := exists_globalFiniteHeckeContinuation F ω S hS hω η ν μ hν
  obtain ⟨f', hf', hfe', _⟩ := exists_globalFiniteHeckeContinuation F ω⁻¹ S hS hω' η ν μ hν
  refine ⟨f, f', ε, hf, hf', hfe, hfe', hε, hε₀, hbound, fun c ↦ ?_⟩
  have hfg := globalFiniteHeckeContinuation_germ F ω S hS hω hL hf he hfe c
  have hfg' := globalFiniteHeckeContinuation_germ F ω⁻¹ S hS hω' hL' hf' he' hfe' (1 - c)
  filter_upwards [hfg, (reflect_punctured c).eventually hfg', hreflect c] with z hz hz' hr
  let D := completedTateReciprocalArch F S hS ω hω
  let D' := completedTateReciprocalArch F S hS ω⁻¹ hω'
  change D z * f' (1 - z) = f z * D' (1 - z) * ε z
  change f z = D z * L z at hz
  change f' (1 - z) = D' (1 - z) * L' (1 - z) at hz'
  change L' (1 - z) = L z * ε z at hr
  rw [hz, hz', hr]
  ring

set_option maxHeartbeats 650000 in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- On a negative half-integer line, a bound on the local gamma shifts gives
an explicit polynomial bound for the reflected product at every height. -/
theorem completedTateArchRatio_half_integer_uniform (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hR : ∀ v : {v : InfinitePlace F // v.IsReal},
      let a := sLocalRealArchParameters F S (phase F S hS ω hω) v
      ‖a.1 + ((a.2 % 2 : ℕ) : ℂ)‖ ≤ A)
    (hC : ∀ v : {v : InfinitePlace F // v.IsComplex},
      let j := sLocalComplexArchParameters F S (phase F S hS ω hω) v
      ‖j.1 + (j.2.natAbs : ℂ) / 2‖ ≤ A)
    (z : ℂ) (hz : z.re = 1 / 2 - (n : ℝ)) :
    ‖completedTateReciprocalArch F S hS ω hω z *
      (completedTateReciprocalArch F S hS ω⁻¹ hω' (1 - z))⁻¹‖ ≤
        ((‖z‖ + A + (2 * n : ℝ)) / (2 * Real.pi)) ^ (Module.finrank ℚ F * n) := by
  let σ := phase F S hS ω hω
  let τ := phase F S hS ω⁻¹ hω'
  let R := {v : InfinitePlace F // v.IsReal}
  let X := {v : InfinitePlace F // v.IsComplex}
  let a := sLocalRealArchParameters F S σ
  let a' := sLocalRealArchParameters F S τ
  let j := sLocalComplexArchParameters F S σ
  let j' := sLocalComplexArchParameters F S τ
  let w (v : R) : ℂ := (a v).1 + (((a v).2 % 2 : ℕ) : ℂ)
  let u (v : X) : ℂ := (j v).1 + ((j v).2.natAbs : ℂ) / 2
  let B : ℝ := (‖z‖ + A + (2 * n : ℝ)) / (2 * Real.pi)
  let M := Fintype.card R * n + Fintype.card X * (2 * n)
  have hτ : τ = σ⁻¹ := stage_phase_inv F S hS ω hω hω'
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hM : M = Module.finrank ℚ F * n := by
    dsimp only [M, R, X]
    change InfinitePlace.nrRealPlaces F * n + InfinitePlace.nrComplexPlaces F * (2 * n) = _
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank]
    ring
  change _ ≤ B ^ (Module.finrank ℚ F * n)
  rw [← hM]
  have hra (v : R) : (a' v).1 = -(a v).1 ∧ (a' v).2 % 2 = (a v).2 % 2 := by
    dsimp only [a', a]
    rw [hτ]
    exact sLocalRealArchParameters_inv F S σ v
  have hcx (v : X) : j' v = (-(j v).1, -(j v).2) := by
    dsimp only [j', j]
    rw [hτ]
    exact sLocalComplexArchParameters_inv F S σ v
  have hreal_arg (v : R) :
      1 - z + (a' v).1 + (((a' v).2 % 2 : ℕ) : ℂ) =
        conj (z + w v) + (n : ℂ) * 2 := by
    rw [(hra v).1, (hra v).2]
    have har : (a v).1.re = 0 := sLocalRealArchParameters_re F S σ v
    apply Complex.ext
    all_goals
      norm_num [w, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
        Complex.sub_im, Complex.mul_im, har]
      try linarith
  have hcomplex_arg (v : X) :
      1 - z + (j' v).1 + ((j' v).2.natAbs : ℂ) / 2 =
        conj (z + u v) + ((2 * n : ℕ) : ℂ) := by
    rw [hcx v]
    have hcr : (j v).1.re = 0 := sLocalComplexArchParameters_re F S σ v
    have htwo : conj (2 : ℂ) = 2 := map_ofNat _ _
    apply Complex.ext
    all_goals
      norm_num [u, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
        Complex.sub_im, Complex.mul_im, htwo, Complex.div_ofNat_re, Complex.div_ofNat_im, hcr]
      try linarith
  have hbR (v : R) :
      ‖Complex.Gammaℝ (conj (z + w v) + (n : ℂ) * 2) * (Complex.Gammaℝ (z + w v))⁻¹‖ ≤
        B ^ n := by
    apply (norm_gammaReal_reflected_steps_all _ _).trans
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hs : ‖z + w v‖ ≤ ‖z‖ + A :=
      (norm_add_le _ _).trans (add_le_add le_rfl (hR v))
    linarith
  have hbX (v : X) :
      ‖Complex.Gammaℂ (conj (z + u v) + ((2 * n : ℕ) : ℂ)) * (Complex.Gammaℂ (z + u v))⁻¹‖ ≤
        B ^ (2 * n) := by
    apply (norm_gammaComplex_reflected_steps_all _ _).trans
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hs : ‖z + u v‖ ≤ ‖z‖ + A :=
      (norm_add_le _ _).trans (add_le_add le_rfl (hC v))
    push_cast
    linarith
  have hprodR := Finset.prod_le_prod (s := Finset.univ) (fun v _ ↦ norm_nonneg
    (Complex.Gammaℝ (conj (z + w v) + (n : ℂ) * 2) * (Complex.Gammaℝ (z + w v))⁻¹))
    (fun v _ ↦ hbR v)
  have hprodX := Finset.prod_le_prod (s := Finset.univ) (fun v _ ↦ norm_nonneg
    (Complex.Gammaℂ (conj (z + u v) + ((2 * n : ℕ) : ℂ)) * (Complex.Gammaℂ (z + u v))⁻¹))
    (fun v _ ↦ hbX v)
  change ‖archimedeanNumberFieldZetaDenominator F a j z *
    (archimedeanNumberFieldZetaDenominator F a' j' (1 - z))⁻¹‖ ≤ _
  simp only [archimedeanNumberFieldZetaDenominator, realArchZetaDenominator,
    complexArchZetaDenominator, mul_inv, Finset.prod_inv_distrib, inv_inv]
  simp only [← Finset.prod_inv_distrib]
  simp_rw [hreal_arg, hcomplex_arg]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [show ∀ x y : ℂ, x⁻¹ * y = y * x⁻¹ from fun _ _ ↦ mul_comm _ _]
  simp only [add_assoc, norm_mul, norm_prod]
  have hprod := mul_le_mul hprodR hprodX (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    (Finset.prod_nonneg fun _ _ ↦ pow_nonneg hB _)
  simp only [norm_mul] at hprod
  refine hprod.trans_eq ?_
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ]
  simp only [← pow_mul, ← pow_add, M, Nat.mul_comm]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The half-integer reflection bound in the form of a vertical polynomial estimate. -/
theorem completedTateArchRatio_half_integer (n : ℕ) :
    ∃ (C T : ℝ), 0 ≤ C ∧ 0 ≤ T ∧
      ∀ z : ℂ, z.re = 1 / 2 - (n : ℝ) → T ≤ |z.im| →
        ‖completedTateReciprocalArch F S hS ω hω z *
          (completedTateReciprocalArch F S hS ω⁻¹ hω' (1 - z))⁻¹‖ ≤
            C * (1 + ‖z‖) ^ (Module.finrank ℚ F * n) := by
  let σ := phase F S hS ω hω
  let w (v : {v : InfinitePlace F // v.IsReal}) : ℂ :=
    let a := sLocalRealArchParameters F S σ v
    a.1 + ((a.2 % 2 : ℕ) : ℂ)
  let u (v : {v : InfinitePlace F // v.IsComplex}) : ℂ :=
    let j := sLocalComplexArchParameters F S σ v
    j.1 + (j.2.natAbs : ℂ) / 2
  let A := (∑ v, ‖w v‖) + ∑ v, ‖u v‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hR (v) : ‖w v‖ ≤ A := by
    exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg (w i)) (Finset.mem_univ v)).trans
      (le_add_of_nonneg_right (by positivity))
  have hC (v) : ‖u v‖ ≤ A := by
    exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg (u i)) (Finset.mem_univ v)).trans
      (le_add_of_nonneg_left (by positivity))
  let B : ℝ := (1 + A + (2 * n : ℝ)) / (2 * Real.pi)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B ^ (Module.finrank ℚ F * n), 0, pow_nonneg hB _, le_rfl, fun z hz _ ↦ ?_⟩
  refine (completedTateArchRatio_half_integer_uniform F S hS ω hω hω' n A hA hR hC z hz).trans ?_
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  dsimp only [B]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [norm_nonneg z, mul_nonneg hA (norm_nonneg z),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (norm_nonneg z)]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem completedTateArchRatio_negative_half_integer (k : ℕ) :
    ∃ (C T : ℝ) (M : ℕ), 0 ≤ C ∧ 0 ≤ T ∧
      ∀ z : ℂ, z.re = -(k : ℝ) - 1 / 2 → T ≤ |z.im| →
        ‖completedTateReciprocalArch F S hS ω hω z *
          (completedTateReciprocalArch F S hS ω⁻¹ hω' (1 - z))⁻¹‖ ≤
            C * (1 + ‖z‖) ^ M := by
  obtain ⟨C, T, hC, hT, hb⟩ := completedTateArchRatio_half_integer F S hS ω hω hω' (k + 1)
  refine ⟨C, T, Module.finrank ℚ F * (k + 1), hC, hT, fun z hz ht ↦ hb z ?_ ht⟩
  push_cast
  linarith

end

end Masullo
