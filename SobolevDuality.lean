import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.CompactlySupported

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped CompactlySupported ComplexConjugate ENNReal

namespace Masullo

section BilinearDual

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private noncomputable def l2Conjugate : Lp ℂ 2 μ ≃ₗᵢ⋆[ℂ] Lp ℂ 2 μ where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' f g := Lp.ext (by
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_star f, Lp.coeFn_star g,
      Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g)] with x h₀ h₁ h₂ h₃ h₄
    simp only [Pi.star_apply, Pi.add_apply] at h₀ h₁ h₂ h₃ h₄
    rw [h₀, h₃, h₄, h₁, h₂, star_add])
  map_smul' z f := Lp.ext (by
    filter_upwards [Lp.coeFn_star (z • f), Lp.coeFn_star f,
      Lp.coeFn_smul z f, Lp.coeFn_smul (conj z) (star f)] with x h₀ h₁ h₂ h₃
    simp only [Pi.star_apply, Pi.smul_apply] at h₀ h₁ h₂ h₃
    change star (z • f) x = (conj z • star f) x
    rw [h₀, h₂, h₃, h₁, star_smul]
    rfl)
  norm_map' f := by
    change ‖(star f : Lp ℂ 2 μ)‖ = ‖f‖
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star, Lp.norm_def]

/-- The bilinear dual isometry in opposite weighted L² coordinates.
Both coordinates use the base measure and conjugation cancels the
semilinearity of the Hilbert-space Riesz isometry. -/
noncomputable def sobolevBilinearDual : Lp ℂ 2 μ ≃ₗᵢ[ℂ] StrongDual ℂ (Lp ℂ 2 μ) :=
  (l2Conjugate μ).trans (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ))

theorem sobolevBilinearDual_apply (f g : Lp ℂ 2 μ) :
    sobolevBilinearDual μ g f = ∫ x, f x * g x ∂μ := by
  change InnerProductSpace.toDual ℂ (Lp ℂ 2 μ) (star g) f = _
  rw [InnerProductSpace.toDual_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hg
  rw [RCLike.inner_apply, hg]
  simp

end BilinearDual

section WeightedTests

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

/-- The chart on compactly supported tests for the L² weight `‖a‖²`. -/
noncomputable def sobolevWeightedTest (a : C(X, ℂ)) (f : C_c(X, ℂ)) : Lp ℂ 2 μ :=
  ((a.continuous.mul f.continuous).memLp_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.mul_left f.hasCompactSupport)).toLp fun x => a x * f x

theorem sobolevWeightedTest_ae (a : C(X, ℂ)) (f : C_c(X, ℂ)) :
    (sobolevWeightedTest μ a f : X → ℂ) =ᵐ[μ] fun x => a x * f x :=
  MemLp.coeFn_toLp _

theorem sobolevWeightedTest_norm_sq (a : C(X, ℂ)) (f : C_c(X, ℂ)) :
    ‖sobolevWeightedTest μ a f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 * ‖a x‖ ^ 2 ∂μ := by
  let g (x : X) := a x * f x
  have hgc : Continuous g := a.continuous.mul f.continuous
  have hm : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport (HasCompactSupport.mul_left f.hasCompactSupport)
  change ‖hm.toLp g‖ ^ 2 = _
  have hn : ‖hm.toLp g‖ = Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    rw [Lp.norm_toLp, toReal_eLpNorm hm.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable,
      Real.sqrt_eq_rpow]
    norm_num [Real.rpow_natCast, inv_eq_one_div]
  rw [hn, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg ‖g x‖)]
  apply integral_congr_ae
  filter_upwards with x
  simp [g, mul_pow, mul_comm]

end WeightedTests

section Duality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]

set_option maxHeartbeats 600000 in
private theorem exists_compactSupport_lpTwo_approximation {f : X → ℂ} (hf : MemLp f 2 μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → ℂ, Continuous g ∧ MemLp g 2 μ ∧ HasCompactSupport g ∧ eLpNorm (f - g) 2 μ ≤ ε := by
  suffices ∃ g : X → ℂ, eLpNorm (f - g) 2 μ ≤ ε ∧ Continuous g ∧ MemLp g 2 μ ∧ HasCompactSupport g by
    obtain ⟨g, hdist, hcont, hmem, hsupport⟩ := this
    exact ⟨g, hcont, hmem, hsupport, hdist⟩
  refine hf.induction_dense (by norm_num)
    (fun g => Continuous g ∧ MemLp g 2 μ ∧ HasCompactSupport g) ?_ ?_ ?_ hε
  · intro c t ht htμ r hr
    obtain ⟨δ, hδpos, hδ⟩ := exists_Lp_half ℂ μ 2 hr
    have htwo : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    obtain ⟨η, hηpos, hη⟩ := exists_eLpNorm_indicator_le htwo c hδpos.ne'
    have hηne : (η : ℝ≥0∞) ≠ 0 := by exact_mod_cast hηpos.ne'
    obtain ⟨s, hst, hs, hsc, hts⟩ := ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hηne
    have hsμ : μ s ≠ ⊤ := (measure_mono hst).trans_lt htμ |>.ne
    obtain ⟨V, hsV, hV, _, hVs⟩ := hsc.measurableSet.exists_isOpen_sdiff_lt hsμ hηne
    obtain ⟨b, h₁, h₀, hb, hbval⟩ := exists_continuous_one_zero_of_isCompact hs hV.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsV)
    let g : X → ℂ := fun x => b x • c
    have hgc : Continuous g := b.continuous.smul continuous_const
    have hgk : HasCompactSupport g := HasCompactSupport.smul_right hb
    have hgm : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport hgk
    let k : X → ℂ := s.indicator fun _ => c
    let v : X → ℂ := t.indicator fun _ => c
    have hleftPoint (x : X) : ‖(g - k) x‖ ≤ ‖(V \ s).indicator (fun _ => c) x‖ := by
      by_cases hxs : x ∈ s
      · simp [g, k, Pi.sub_apply, hxs, h₁ hxs]
      by_cases hxV : x ∈ V
      · simpa [g, k, Pi.sub_apply, hxs, hxV, norm_smul, Real.norm_of_nonneg (hbval x).1] using
          mul_le_of_le_one_left (norm_nonneg c) (hbval x).2
      · simp [g, k, Pi.sub_apply, hxs, hxV, h₀ (show x ∈ Vᶜ from hxV)]
    have hleft : eLpNorm (g - k) 2 μ ≤ δ := (eLpNorm_mono hleftPoint).trans (hη _ hVs.le)
    have hright : eLpNorm (k - v) 2 μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hst]
      exact hη _ hts.le
    have hk : AEStronglyMeasurable k μ := aestronglyMeasurable_const.indicator hsc.measurableSet
    have hv : AEStronglyMeasurable v μ := aestronglyMeasurable_const.indicator ht
    have hbound := hδ (g - k) (k - v) (hgm.aestronglyMeasurable.sub hk) (hk.sub hv) hleft hright
    exact ⟨g, by simpa [v, sub_add_sub_cancel] using hbound.le, hgc, hgm, hgk⟩
  · rintro g k ⟨hgc, hgm, hgk⟩ ⟨hkc, hkm, hkk⟩
    exact ⟨hgc.add hkc, hgm.add hkm, hgk.add hkk⟩
  · rintro g ⟨_, hgm, _⟩
    exact hgm.aestronglyMeasurable

theorem denseRange_sobolevWeightedTest
    (a : C(X, ℂ)) (ha : ∀ x, a x ≠ 0) : DenseRange (sobolevWeightedTest μ a) := by
  apply Metric.denseRange_iff.mpr
  intro u ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hε' : ENNReal.ofReal (ε / 2) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hhalf)
  let hu := Lp.memLp u
  obtain ⟨g, hgc, hgm, hg, hdist⟩ := exists_compactSupport_lpTwo_approximation μ hu hε'
  let f : C_c(X, ℂ) := ⟨⟨fun x => (a x)⁻¹ * g x, (a.continuous.inv₀ ha).mul hgc⟩,
    HasCompactSupport.mul_left hg⟩
  have hchart : sobolevWeightedTest μ a f = hgm.toLp g := by
    apply Lp.ext
    filter_upwards [sobolevWeightedTest_ae μ a f, hgm.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂]
    change a x * ((a x)⁻¹ * g x) = g x
    rw [← mul_assoc, mul_inv_cancel₀ (ha x), one_mul]
  refine ⟨f, ?_⟩
  rw [hchart, Lp.dist_edist, ← Lp.toLp_coeFn u hu, Lp.edist_toLp_toLp]
  exact (ENNReal.toReal_le_of_le_ofReal hhalf.le hdist).trans_lt (half_lt_self hε)

/-- Lemma 9.1.1.5. Opposite weighted L² coordinates extend the bilinear
integral pairing uniquely from compactly supported continuous tests.
Taking `a = (1 + w²)^(s/4)` gives the manuscript's two Sobolev norms. -/
theorem sobolev_weighted_duality
    (a b : C(X, ℂ)) (hab : ∀ x, a x * b x = 1) :
    let L := Lp ℂ 2 μ
    let p (f g : L) := sobolevBilinearDual μ g f
    Continuous (fun q : L × L => p q.1 q.2) ∧
    (∀ f : L, (∀ g : L, p f g = 0) → f = 0) ∧
    (∀ g : L, (∀ f : L, p f g = 0) → g = 0) ∧
    (∀ f g : C_c(X, ℂ), p (sobolevWeightedTest μ a f) (sobolevWeightedTest μ b g) =
      ∫ x, f x * g x ∂μ) ∧
    (∀ Q : L × L → ℂ, Continuous Q →
      (∀ f g : C_c(X, ℂ), Q (sobolevWeightedTest μ a f, sobolevWeightedTest μ b g) =
        ∫ x, f x * g x ∂μ) → Q = fun q => p q.1 q.2) := by
  let J := sobolevBilinearDual μ
  have hcontinuous : Continuous (fun q : Lp ℂ 2 μ × Lp ℂ 2 μ => J q.2 q.1) :=
    (J.continuous.comp continuous_snd).clm_apply continuous_fst
  have htest (f g : C_c(X, ℂ)) :
      J (sobolevWeightedTest μ b g) (sobolevWeightedTest μ a f) = ∫ x, f x * g x ∂μ := by
    rw [sobolevBilinearDual_apply]
    apply integral_congr_ae
    filter_upwards [sobolevWeightedTest_ae μ a f, sobolevWeightedTest_ae μ b g] with x h₁ h₂
    rw [h₁, h₂, mul_mul_mul_comm, hab x, one_mul]
  refine ⟨hcontinuous, ?_, ?_, htest, ?_⟩
  · intro f hf
    have hz := hf (star f)
    change InnerProductSpace.toDual ℂ (Lp ℂ 2 μ) (star (star f)) f = 0 at hz
    rwa [star_star, InnerProductSpace.toDual_apply_apply, inner_self_eq_zero] at hz
  · intro g hg
    exact J.injective (by ext f; simpa using hg f)
  · intro Q hQ hEq
    have ha x := left_ne_zero_of_mul_eq_one (hab x)
    have hb x := right_ne_zero_of_mul_eq_one (hab x)
    have hd := (denseRange_sobolevWeightedTest μ a ha).prodMap (denseRange_sobolevWeightedTest μ b hb)
    exact hd.equalizer hQ hcontinuous (funext fun ⟨f, g⟩ => (hEq f g).trans (htest f g).symm)

end Duality

section HilbertCompletion

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (μ : Measure (PontryaginDual G)) [μ.IsHaarMeasure] [μ.Regular]

private noncomputable def sobolevSpectralFactor (w : C(PontryaginDual G, ℝ)) (s : ℝ) :
    C(PontryaginDual G, ℂ) where
  toFun x := ((1 + w x ^ 2) ^ (s / 4) : ℝ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((continuous_const.add (w.continuous.pow 2)).rpow_const fun x =>
      Or.inl ((by positivity : 0 < 1 + w x ^ 2)).ne')

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] in
private theorem sobolevSpectralFactor_norm_sq (w : C(PontryaginDual G, ℝ)) (s : ℝ)
    (x : PontryaginDual G) :
    ‖sobolevSpectralFactor w s x‖ ^ 2 = (1 + w x ^ 2) ^ (s / 2) := by
  have hx : 0 < 1 + w x ^ 2 := by positivity
  change ‖(((1 + w x ^ 2) ^ (s / 4) : ℝ) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
    ← Real.rpow_mul_natCast hx.le]
  congr 1
  norm_num
  ring

omit [T2Space G] in
/-- Lemma 9.1.1.2, with the Fourier coordinate as the test variable.
Multiplication by the positive square root of the weight identifies the
weighted Hilbert completion with ordinary (L^2) of the chosen spectral
Haar measure. The compact-open dual of a second-countable group is
second-countable. -/
theorem sobolevHilbertCompletion (w : C(PontryaginDual G, ℝ)) (s : ℝ) :
    ∃ I : C_c(PontryaginDual G, ℂ) →ₗ[ℂ] Lp ℂ 2 μ,
      Injective I ∧ DenseRange I ∧
      (∀ f, ‖I f‖ ^ 2 = ∫ χ, ‖f χ‖ ^ 2 * (1 + w χ ^ 2) ^ (s / 2) ∂μ) ∧
      CompleteSpace (Lp ℂ 2 μ) ∧ (SecondCountableTopology G → SeparableSpace (Lp ℂ 2 μ)) := by
  let a := sobolevSpectralFactor w s
  have ha (x : PontryaginDual G) : a x ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'
  let I : C_c(PontryaginDual G, ℂ) →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := sobolevWeightedTest μ a
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [sobolevWeightedTest_ae μ a (f + g), sobolevWeightedTest_ae μ a f,
          sobolevWeightedTest_ae μ a g, Lp.coeFn_add (sobolevWeightedTest μ a f)
            (sobolevWeightedTest μ a g)] with x hu hv hw hz
        rw [hu, hz, Pi.add_apply, hv, hw]
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [sobolevWeightedTest_ae μ a (c • f), sobolevWeightedTest_ae μ a f,
          Lp.coeFn_smul c (sobolevWeightedTest μ a f)] with x hu hv hw
        rw [hu, RingHom.id_apply, hw, Pi.smul_apply, hv]
        change a x * (c * f x) = c * (a x * f x)
        rw [mul_left_comm] }
  refine ⟨I, ?_, denseRange_sobolevWeightedTest μ a ha, ?_, inferInstance, ?_⟩
  · intro f g hfg
    have hae : (fun x => a x * f x) =ᵐ[μ] fun x => a x * g x := by
      have h := sobolevWeightedTest_ae μ a f
      change sobolevWeightedTest μ a f = sobolevWeightedTest μ a g at hfg
      rw [hfg] at h
      exact h.symm.trans (sobolevWeightedTest_ae μ a g)
    apply CompactlySupportedContinuousMap.ext
    have he := ((a.continuous.mul f.continuous).ae_eq_iff_eq μ (a.continuous.mul g.continuous)).mp hae
    intro x
    exact mul_left_cancel₀ (ha x) (congrFun he x)
  · intro f
    change ‖sobolevWeightedTest μ a f‖ ^ 2 = _
    rw [sobolevWeightedTest_norm_sq]
    exact integral_congr_ae (Eventually.of_forall fun χ =>
      congrArg (‖f χ‖ ^ 2 * ·) (sobolevSpectralFactor_norm_sq w s χ))
  · intro hG
    letI := hG
    haveI : SecondCountableTopology (PontryaginDual G) :=
      (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
    letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
    haveI : SigmaFinite μ := inferInstance
    haveI : SecondCountableTopology (Lp ℂ 2 μ) := inferInstance
    infer_instance

end HilbertCompletion

end Masullo
