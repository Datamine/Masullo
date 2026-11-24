import LocalizedConvolutionNuclear
import CompactBruhatFourierSynthesis
import BruhatCyclicPeriodizationCorollary

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

private theorem summable_compactElementaryCoefficientNorm {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [CompactSpace (ElementaryLCAModel m n r F)] [CompactSpace (Multiplicative (ElementaryLCAModel m n r F))]
    [MeasurableSpace (Multiplicative (ElementaryLCAModel m n r F))]
    [BorelSpace (Multiplicative (ElementaryLCAModel m n r F))]
    (μ : Measure (Multiplicative (ElementaryLCAModel m n r F))) [μ.IsHaarMeasure]
    (f : ElementarySchwartz m n r F) :
    Summable (fun χ : PontryaginDual (Multiplicative (ElementaryLCAModel m n r F)) =>
      ‖elementaryFourierPairing μ χ f‖) := by
  obtain ⟨rfl, rfl⟩ := elementaryLCAModel_compact_dimensions (m := m) (n := n) (r := r) (F := F)
  simpa only [pow_zero, one_mul] using summable_compactElementaryFourierPairing μ f 0

section Compact

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [CompactSpace H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]

/-- Fourier coefficients of a compact Schwartz–Bruhat test are absolutely
summable, including on compact groups with infinitely many stages. -/
theorem summable_compactBruhatCoefficientNorm (μ : Measure H) [μ.IsHaarMeasure]
    (f : BruhatSchwartz H) : Summable (fun χ : PontryaginDual H => ‖compactBruhatFourierCoeff μ χ f‖) := by
  obtain ⟨P, u, rfl⟩ := exists_compactBruhat_wholeStage f
  let A := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor
  letI : CompactSpace (Multiplicative A) := P.coordinates_surjective.compactSpace P.coordinates.continuous
  letI : CompactSpace A := Multiplicative.toAdd.surjective.compactSpace continuous_toAdd
  letI : MeasurableSpace (Multiplicative A) := borel _
  letI : BorelSpace (Multiplicative A) := ⟨rfl⟩
  let ν : Measure (Multiplicative A) := μ.map P.coordinates
  letI : ν.IsHaarMeasure := μ.isHaarMeasure_map_of_isFiniteMeasure P.coordinates.toMonoidHom
    P.coordinates.continuous P.coordinates_surjective
  let t (θ : PontryaginDual (Multiplicative A)) : PontryaginDual H := θ.comp P.coordinates
  have ht : Injective t := by
    intro θ η h
    ext z
    obtain ⟨x, rfl⟩ := P.coordinates_surjective z
    exact congrArg (fun χ : PontryaginDual H => (χ x : ℂ)) h
  have hz (χ : PontryaginDual H) (hχ : χ ∉ range t) :
      ‖compactBruhatFourierCoeff μ χ (P.val.inclusion u)‖ = 0 := by
    have h : ∃ a ∈ P.val.1.kernel, χ a ≠ 1 := by
      by_contra! hh
      obtain ⟨θ, hθ, _⟩ := wholeBruhatStage_character_descends P χ hh
      exact hχ ⟨θ, hθ⟩
    rw [compactBruhatFourierCoeff_eq_zero_off_stage_annihilator μ P u χ h, norm_zero]
  have hs := (summable_compactElementaryCoefficientNorm ν u).mul_left ‖(μ.real univ : ℂ)⁻¹‖
  obtain ⟨c, hc⟩ := hs
  refine ⟨c, (ht.hasSum_iff hz).mp (hc.congr_fun fun θ => ?_)⟩
  change ‖compactBruhatFourierCoeff μ (θ.comp P.coordinates) (P.val.inclusion u)‖ =
    ‖(μ.real univ : ℂ)⁻¹‖ * ‖elementaryFourierPairing ν θ u‖
  rw [compactBruhatFourierCoeff_stage P μ θ u, norm_mul]

private theorem compactBruhatFourierSeries_pointwise (μ : Measure H) [μ.IsHaarMeasure]
    (f : BruhatSchwartz H) (x : H) :
    f.val x = ∑' χ : PontryaginDual H, compactBruhatFourierCoeff μ χ f * star (χ x : ℂ) := by
  let L : BruhatSchwartz H →L[ℂ] ℂ :=
    ⟨{ toFun := fun g => g.val x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
      bruhatSchwartz_continuous_eval x⟩
  have he := ((hasSum_compactBruhatFourierSeries μ f).mapL L).tsum_eq.symm
  refine he.trans ?_
  apply tsum_congr
  intro χ
  change compactBruhatFourierCoeff μ χ f * ((χ⁻¹) x : ℂ) = _
  have hi : (χ⁻¹) x = (χ x)⁻¹ := rfl
  rw [hi, Circle.coe_inv_eq_conj]
  rfl

end Compact

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (μ : Measure G) [μ.IsHaarMeasure]

include m hm hms in
set_option maxHeartbeats 1800000 in
/-- Nuclearity for every compactly supported Schwartz–Bruhat symbol. On the
compact region seen by the weighted kernel, periodization on a sufficiently
large compact cyclic quotient leaves the symbol unchanged. Its absolutely
summable character expansion gives the two Hilbert–Schmidt factors. -/
theorem bruhatCutoffConvolution_traceClass
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {ρ : G → ℂ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (φ : BruhatSchwartz G) (hφc : HasCompactSupport φ.val) :
    let μw := μ.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure μw := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let k := cutoffConvolutionKernel w ρ φ.val
    ∃ (hk : MemLp k 2 (μw.prod μw)) (T : TraceClass (Lp ℂ 2 μw)),
      T.toOperator = kernelIntegralOperator (hk.toLp k) ∧
      T.traceValue = (∫ x, ρ x ∂μ) * φ.val 1 := by
  let L := (tsupport φ.val)⁻¹ * tsupport ρ
  let K := (tsupport ρ * L⁻¹) ∪ tsupport φ.val
  have hL : IsCompact L := hφc.inv.mul hρc
  have hK : IsCompact K := (hρc.mul hL.inv).union hφc
  let ℓ (x : G) : ℝ := (m x).toAdd
  have hℓ : Continuous ℓ := continuous_toAdd.comp m.continuous
  obtain ⟨C, hC⟩ := (hK.image hℓ).isBounded.exists_norm_le
  let D := max C 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hbound (z : G) (hz : z ∈ K) : |ℓ z| ≤ D :=
    (by simpa only [Real.norm_eq_abs] using hC (ℓ z) ⟨z, hz, rfl⟩ : |ℓ z| ≤ C).trans
      (le_max_left _ _)
  obtain ⟨γ, hγ⟩ := hms (Multiplicative.ofAdd (2 * D + 1))
  have hγℓ : ℓ γ = 2 * D + 1 := congrArg Multiplicative.toAdd hγ
  have hγpos : 0 < (m γ).toAdd := by change 0 < ℓ γ; rw [hγℓ]; positivity
  let Q := G ⧸ Subgroup.zpowers γ
  letI : IsClosed ((Subgroup.zpowers γ : Subgroup G) : Set G) :=
    modulatedCyclicSubgroup_isClosed m γ hγpos
  letI : CompactSpace Q := modulatedCyclicQuotient_compact m hm γ hγpos
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  let Haar : Measure Q := Measure.haar
  letI : Haar.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure Q).IsHaarMeasure
  let F := bruhatCyclicPeriodization m hm γ hγpos hms φ
  have hlocal (z : G) (hz : z ∈ K) : F.val (QuotientGroup.mk z) = φ.val z := by
    change (bruhatCyclicPeriodization m hm γ hγpos hms φ).val (QuotientGroup.mk z) = _
    rw [bruhatCyclicPeriodization_apply, bruhatSchwartz_cyclicOrbitSum_apply, tsum_eq_single 0]
    · simp
    · intro n hn
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have h₁ := hbound (γ ^ n * z) (Or.inr hs)
      have h₂ := hbound z hz
      have hlog : ℓ (γ ^ n * z) = (n : ℝ) * (2 * D + 1) + ℓ z := by
        change (m (γ ^ n * z)).toAdd = _
        rw [map_mul, map_zpow, toAdd_mul, toAdd_zpow,
          zsmul_eq_mul, show (m γ).toAdd = 2 * D + 1 from hγℓ]
      rw [hlog] at h₁
      have hn₁ : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h₃ : 2 * D + 1 ≤ |(n : ℝ)| * (2 * D + 1) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hn₁ (show 0 ≤ 2 * D + 1 by positivity)
      have h₄ := abs_sub ((n : ℝ) * (2 * D + 1) + ℓ z) (ℓ z)
      rw [add_sub_cancel_right, abs_mul, abs_of_pos (show 0 < 2 * D + 1 by positivity)] at h₄
      linarith
  let c (χ : PontryaginDual Q) := compactBruhatFourierCoeff Haar χ F
  have hc : Summable (fun χ => ‖c χ‖) := summable_compactBruhatCoefficientNorm Haar F
  let S := support c
  letI : Countable S := by
    apply Set.Countable.to_subtype
    exact hc.countable_support.mono (fun χ hχ => by simpa [S, mem_support, norm_eq_zero] using hχ)
  letI : MeasurableSpace S := ⊤
  letI : MeasurableSingletonClass S := ⟨fun _ => trivial⟩
  let η : Measure S := Measure.count
  letI : SigmaFinite η := inferInstanceAs (SigmaFinite (Measure.count : Measure S))
  letI : MeasureTheory.IsSeparable η := isSeparable_of_sigmaFinite η
  have hcI : Integrable (fun χ : S => c χ.val) η :=
    integrable_count_iff.mpr (hc.subtype _)
  obtain ⟨a, b, ha, hb, hfact⟩ := exists_L2_spectral_factors hcI
  let χ (p : G × S) : ℂ := star (p.2.val (QuotientGroup.mk p.1 : Q) : ℂ)
  have hχ : Measurable χ := measurable_from_prod_countable_left fun θ =>
    (((continuous_subtype_val.comp θ.val.continuous).comp QuotientGroup.continuous_mk).star).measurable
  have hχb (p : G × S) : ‖χ p‖ ≤ 1 := by
    simp only [χ, norm_star, Circle.norm_coe, le_refl]
  refine cutoffConvolution_traceClass_of_spectral_factors μ η hw hpos hρ hρc
    (bruhatSchwartz_continuous φ) hφc χ hχ hχb a b ha hb ?_
  intro x hx y hy
  let z := x * y⁻¹
  have hz : z ∈ K := Or.inl ⟨x, hx, y⁻¹, Set.mem_inv.mpr (by simpa using hy), rfl⟩
  change φ.val z = ∫ θ, χ (x, θ) * star (χ (y, θ)) * (a θ * star (b θ)) ∂η
  rw [← hlocal z hz, compactBruhatFourierSeries_pointwise Haar]
  have hterm (θ : S) : χ (x, θ) * star (χ (y, θ)) * (a θ * star (b θ)) =
      c θ.val * star (θ.val (QuotientGroup.mk z : Q) : ℂ) := by
    rw [hfact θ]
    change star (θ.val (QuotientGroup.mk x : Q) : ℂ) *
        star (star (θ.val (QuotientGroup.mk y : Q) : ℂ)) * c θ.val =
      c θ.val * star (θ.val (QuotientGroup.mk (x * y⁻¹) : Q) : ℂ)
    rw [star_star]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, Circle.coe_mul,
      Circle.coe_inv_eq_conj, star_mul, ← Complex.star_def, star_star]
    ring
  simp_rw [hterm]
  have hi : Integrable (fun θ : S => c θ.val * star (θ.val (QuotientGroup.mk z : Q) : ℂ)) η := by
    apply integrable_count_iff.mpr
    simp only [norm_mul, norm_star, Circle.norm_coe, mul_one]
    exact hc.subtype (· ∈ S)
  rw [integral_countable hi]
  simp only [η, Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  symm
  apply tsum_subtype_eq_of_support_subset (s := S)
    (f := fun χ : PontryaginDual Q => c χ * star (χ (QuotientGroup.mk z : Q) : ℂ))
  intro θ hθ
  show c θ ≠ 0
  intro hzero
  apply hθ
  change c θ * star (θ (QuotientGroup.mk z : Q) : ℂ) = 0
  exact (congrArg (· * star (θ (QuotientGroup.mk z : Q) : ℂ)) hzero).trans (zero_mul _)

include hm hms in
/-- On a compact abscissa base the trace-class realization acts by the
truncated Haar convolution on the actual weighted Hardy–Sobolev classes. -/
theorem bruhatCompactBaseCutoff_traceClass
    (a b s : ℝ) {ρ : G → ℂ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (φ : BruhatSchwartz G) (hφc : HasCompactSupport φ.val) :
    let ν := hardySobolevMeasure μ (modulatedLog m) a b s
    ∃ T : TraceClass (Lp ℂ 2 ν),
      (∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂μ, T.toOperator f x =
        ρ x * ∫ y, φ.val y * f (y⁻¹ * x) ∂μ) ∧
      T.traceValue = (∫ x, ρ x ∂μ) * φ.val 1 := by
  intro ν
  let w (x : G) := hardySobolevWeight a b s (modulatedLog m x)
  have hw : Continuous w := (continuous_hardySobolevWeight a b s).comp
    (continuous_toAdd.comp m.continuous)
  have hp (x : G) : 0 < w x := by
    dsimp [w, hardySobolevWeight]
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos (by positivity) _)
  letI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  obtain ⟨hk, T, hop, htrace⟩ := bruhatCutoffConvolution_traceClass m hm hms μ hw hp hρ hρc φ hφc
  refine ⟨T, ?_, htrace⟩
  intro f
  exact (cutoffConvolutionKernel_apply μ hw hp hρ (bruhatSchwartz_continuous φ) hρc hφc f).mono
    (fun x hx => (congrArg (fun A => A f x) hop).trans hx)

include hm in
/-- The trace asymptotic for a family of smooth compact cutoff convolutions.
The operators exist for the full compactly supported Schwartz–Bruhat class. -/
theorem bruhatCutoffConvolution_trace_asymptotic
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsFiniteMeasure ν]
    {ι : Type*} {l : Filter ι} {Λ ε : ι → ℝ}
    (hΛ : Tendsto Λ l atTop) (hε : Tendsto (fun i => ε i * Λ i) l (𝓝 0))
    (ρ : ι → G → ℝ) (hρ : ∀ i, Continuous (ρ i)) (hρc : ∀ i, HasCompactSupport (ρ i))
    (φ : BruhatSchwartz G) (hφc : HasCompactSupport φ.val)
    {w : G → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (hband : ∀ᶠ i in l, 0 ≤ ε i ∧ (Λ i)⁻¹ + ε i ≤ Λ i - ε i ∧
      (∀ x, 0 ≤ ρ i x ∧ ρ i x ≤ 1) ∧
      (∀ x, modulatedLog m x ∉ Icc (-Real.log (Λ i)) (Real.log (Λ i)) → ρ i x = 0) ∧
      (∀ x, modulatedLog m x ∈ Icc (Real.log ((Λ i)⁻¹ + ε i)) (Real.log (Λ i - ε i)) → ρ i x = 1)) :
    let η := modulatedLogMeasure m τ hτ ν
    letI : η.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
    let ηw := η.withDensity (fun x => ENNReal.ofReal (w x))
    letI : IsLocallyFiniteMeasure ηw := IsLocallyFiniteMeasure.withDensity_ofReal hw
    let K i := cutoffConvolutionKernel w (fun g => (ρ i g : ℂ)) φ.val
    ∃ (hk : ∀ i, MemLp (K i) 2 (ηw.prod ηw)) (T : ι → TraceClass (Lp ℂ 2 ηw)),
      (∀ i, (T i).toOperator = kernelIntegralOperator ((hk i).toLp (K i))) ∧
      (∀ i, (T i).traceValue = (∫ x, (ρ i x : ℂ) ∂η) * φ.val 1) ∧
      Tendsto (fun i => (T i).traceValue -
        (((2 * Real.log (Λ i)) * ν.real univ : ℝ) : ℂ) * φ.val 1) l (𝓝 0) := by
  intro η ηw K
  letI : η.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
  letI : IsLocallyFiniteMeasure ηw := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have h (i : ι) := bruhatCutoffConvolution_traceClass m hm hτ.surjective η hw hpos
    (Complex.continuous_ofReal.comp (hρ i))
    ((hρc i).comp_left (g := Complex.ofReal) Complex.ofReal_zero) φ hφc
  choose hk T hop hval using h
  refine ⟨hk, T, hop, hval, ?_⟩
  exact modulatedCutoff_traceClass_asymptotic m τ hτ ν hΛ hε ρ
    (bruhatSchwartz_continuous φ).continuousAt hw hpos hρ hρc hband T hk (fun i => (hop i).symm)

end Modulated

end
end Masullo
