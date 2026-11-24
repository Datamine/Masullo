import BruhatFractionalTraces

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [hG : SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) [CompactSpace m.toMonoidHom.ker]
  (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

local notation "K" => m.toMonoidHom.ker
local notation "H" => modulatedLogMeasure m τ hτ ν
local notation "W[" a "," b "," s "]" => hardySobolevMeasure H (modulatedLog m) a b s
local notation "E[" I "]" => ModulatedExponentialInductive m I
local notation "dx" => (volume : Measure ℝ)

omit [T2Space G] [LocallyCompactSpace G] hG in
private theorem fractionalGroupMoment_onCoefficient {a b s : ℝ} (U : Set ℝ) (hU : IsOpen U)
    (χ : PontryaginDual K) (f : Lp ℂ 2 W[a,b,s])
    (u : lpTwoRadialSupport ν (stripMeasure a b s) U)
    (hu : (f : G → ℂ) =ᵐ[W[a,b,s]] modulatedIntervalGroupProfile m τ hτ ν a b s u)
    (z : ℂ) (hK : MemLp (U.indicator (mellinEvaluationKernel 0 z)) 2
      (stripMeasure (-a) (-b) (-s))) :
    Integrable (bruhatGroupMellinIntegrand m τ hτ χ f 0 z) H ∧
      bruhatGroupMellinMoment m τ hτ ν χ f 0 z =
        cutoffMellinIntegral (modulatedIntervalCoefficient ν a b s hU χ u).val 0 z := by
  have hAC : H ≪ W[a,b,s] := by
    unfold hardySobolevMeasure
    apply withDensity_absolutelyContinuous'
    · exact (((continuous_hardySobolevWeight a b s).measurable.comp
        (continuous_toAdd.comp m.continuous).measurable).ennreal_ofReal).aemeasurable
    · exact .of_forall fun g =>
        ENNReal.ofReal_ne_zero_iff.mpr (by unfold hardySobolevWeight; positivity)
  have hIntegrand :
      bruhatGroupMellinIntegrand m τ hτ χ (modulatedIntervalGroupProfile m τ hτ ν a b s u) 0 z
        =ᵐ[H] bruhatGroupMellinIntegrand m τ hτ χ f 0 z := by
    filter_upwards [hAC.ae_le hu] with g hg
    unfold bruhatGroupMellinIntegrand
    rw [hg]
  have hGroup := modulatedIntervalMoment_onGroup m τ hτ ν a b s hU χ 0 z hK u
  refine ⟨hGroup.1.congr hIntegrand, (integral_congr_ae hIntegrand.symm).trans (hGroup.2.symm.trans ?_)⟩
  let F (p : K × ℝ) := (χ p.1 : ℂ) * u.val p * mellinEvaluationKernel 0 z p.2
  let v := modulatedIntervalCoefficient ν a b s hU χ u
  obtain ⟨_, hΛ, _⟩ := modulatedInterval_mellinMoment_of_kernel ν a b s hU χ 0 z hK
  change (∫ p, F p ∂ν.prod dx) = _
  rw [integral_prod_symm F (hΛ u).1]
  apply integral_congr_ae
  filter_upwards [modulatedIntervalCoefficient_ae ν a b s hU χ u] with x hx
  change v.val x = _ at hx
  change (∫ k, ((χ k : ℂ) * u.val (k, x)) * mellinEvaluationKernel 0 z x ∂ν) =
    v.val x * mellinEvaluationKernel 0 z x
  rw [integral_mul_const, ← hx]

set_option maxHeartbeats 650000 in
omit [T2Space G] [LocallyCompactSpace G] hG in
/-- The bounded-band term of the analytic diagram has the entire
Paley–Wiener extension and its interval growth factor at every character. -/
theorem fractionalGroup_mellin_band_entire {a b : ℝ} (hab : a ≤ b) (s c : ℝ)
    (χ : PontryaginDual K) (f : Lp ℂ 2 W[a,b,s])
    (hf : ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ Icc c 0 → f g = 0) :
    (∀ z, Integrable (bruhatGroupMellinIntegrand m τ hτ χ f 0 z) H) ∧
      Differentiable ℂ (bruhatGroupMellinMoment m τ hτ ν χ f 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
        ‖bruhatGroupMellinMoment m τ hτ ν χ f 0 z‖ ≤
          C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x)) := by
  have hOpen : ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ Ioo c 0 → f g = 0 := by
    filter_upwards [hf, modulatedCompactInterval_log_ae_ne m τ hτ ν hab s c,
      modulatedCompactInterval_log_ae_ne m τ hτ ν hab s 0] with g h hc h0 ho
    exact h (fun hi => ho ⟨lt_of_le_of_ne hi.1 hc.symm, lt_of_le_of_ne hi.2 h0⟩)
  obtain ⟨u, hu⟩ := exists_modulatedIntervalGroupProfile_ae m τ hτ ν hab f hOpen
  let v := modulatedIntervalCoefficient ν a b s isOpen_Ioo χ u
  have hM (z : ℂ) := fractionalGroupMoment_onCoefficient m τ hτ ν (Ioo c 0) isOpen_Ioo
    χ f u hu z (hardySobolev_bounded_mellinKernel a b s c 0 z)
  have hEq : bruhatGroupMellinMoment m τ hτ ν χ f 0 =
      fun z : ℂ => ∫ x, compactMellinKernel v.val z x := by
    funext z
    simpa only [cutoffMellinIntegral, mellinEvaluationKernel, compactMellinKernel, pow_zero, mul_one]
      using (hM z).2
  refine ⟨fun z => (hM z).1, ?_⟩
  rw [hEq]
  obtain ⟨_, hd, hb⟩ := boundedStripSobolev_mellin_entire_bound a b s c v
  exact ⟨hd, ⟨_, Real.sqrt_nonneg _, hb⟩⟩


section Converse

variable [hMul : ν.IsMulLeftInvariant] [hReg : ν.WeaklyRegular] [hProb : IsProbabilityMeasure ν]

include hG hMul hReg hProb

omit [LocallyCompactSpace G] in
private theorem groupProduct_band_of_coefficients (a b s c : ℝ)
    (u : lpTwoRadialSupport ν (stripMeasure a b s) (Ioi c))
    (h : ∀ χ : PontryaginDual K, (modulatedIntervalCoefficient ν a b s isOpen_Ioi χ u).val ∈
      supportedSobolevCompletion a b s (Ioo c 0)) :
    ∀ᵐ p ∂ν.prod (stripMeasure a b s), p.2 ∉ Ioo c 0 → u.val p = 0 := by
  let ρ := stripMeasure a b s
  let U : Set (K × ℝ) := Prod.snd ⁻¹' (Ioo c 0)ᶜ
  let f := U.indicator (u.val : K × ℝ → ℂ)
  have hf : MemLp f 2 (ν.prod ρ) :=
    (Lp.memLp u.val).indicator (measurableSet_Ioo.compl.preimage measurable_snd)
  let v : PontryaginDual K → Lp ℂ 2 ρ := fun _ => 0
  have hν : ρ ≪ dx := amplitudeMeasure_absolutelyContinuous dx _
  have hv (χ : PontryaginDual K) : (v χ : ℝ → ℂ) =ᵐ[ρ] fun x =>
      ∫ k, star (χ k : ℂ) * f (k, x) ∂ν := by
    have hh := (mem_supportedSobolevCompletion_iff a b s isOpen_Ioo
      (modulatedIntervalCoefficient ν a b s isOpen_Ioi χ⁻¹ u).val).mp (h χ⁻¹)
    filter_upwards [Lp.coeFn_zero ℂ 2 ρ, hν.ae_le hh,
      hν.ae_le (modulatedIntervalCoefficient_ae ν a b s isOpen_Ioi χ⁻¹ u)] with x h0 hx hχ
    change (v χ) x = 0 at h0
    rw [h0]
    by_cases hxU : x ∈ Ioo c 0
    · have hzero : (fun k => star (χ k : ℂ) * f (k, x)) = fun _ => 0 := by
        funext k
        rw [show f (k, x) = 0 from indicator_of_notMem (fun hk : (k, x) ∈ U => hk hxU) _,
          mul_zero]
      rw [hzero, integral_zero]
    · have hEq : (fun k => star (χ k : ℂ) * f (k, x)) =
          fun k => (χ⁻¹ k : ℂ) * u.val (k, x) := by
        funext k
        rw [show f (k, x) = u.val (k, x) from indicator_of_mem (show (k, x) ∈ U from hxU) _]
        exact congrArg (fun z : ℂ => z * u.val (k, x)) (Circle.coe_inv_eq_conj (χ k)).symm
      rw [hEq, ← hχ, hx hxU]
  letI : SecondCountableTopology K := IsInducing.subtypeVal.secondCountableTopology
  have hsum := tsum_sq_character_integral_prod ν hf v hv
  have hint : (∫ p, ‖f p‖ ^ 2 ∂ν.prod ρ) = 0 := by
    have hm : ν.real univ = 1 := by
      rw [Measure.real, hProb.measure_univ, ENNReal.toReal_one]
    rw [hm, one_mul] at hsum
    simpa [v] using hsum.symm
  have hLp := norm_sq_toLp_two hf
  have hLp0 : hf.toLp f = 0 := by
    rw [← norm_eq_zero]
    nlinarith [hLp.trans hint]

  have hzero : f =ᵐ[ν.prod ρ] (0 : K × ℝ → ℂ) :=
    hf.coeFn_toLp.symm.trans (hLp0 ▸ Lp.coeFn_zero ℂ 2 (ν.prod ρ))
  filter_upwards [hzero] with p hp hn
  exact (indicator_of_mem (show p ∈ U from hn) _).symm.trans hp

set_option maxHeartbeats 650000 in
/-- Within the lower-ray completion, the bounded-band term is exactly the
class whose character Mellin transforms admit entire extensions with the
Paley–Wiener interval growth factor. -/
theorem fractionalGroup_mellin_band_iff {a b s c : ℝ}
    (hab : a ≤ b) (hs : 0 ≤ s) (hc : c ≤ 0)
    (f : Lp ℂ 2 W[a,b,s])
    (hf : ∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ Ioi c → f g = 0) :
    (∀ᵐ g ∂W[a,b,s], modulatedLog m g ∉ Icc c 0 → f g = 0) ↔
      ∀ χ : PontryaginDual K, ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
        (∀ z : ℂ, z.re < b → F z = bruhatGroupMellinMoment m τ hτ ν χ f 0 z) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : ℂ, ‖F z‖ ≤ C * Real.sqrt (∫ x in Icc c 0, Real.exp (2 * z.re * x)) := by
  constructor
  · intro h χ
    obtain ⟨_, hD, hB⟩ := fractionalGroup_mellin_band_entire m τ hτ ν hab s c χ f h
    exact ⟨_, hD, fun _ _ => rfl, hB⟩
  · intro h
    obtain ⟨u, hu⟩ := exists_modulatedIntervalGroupProfile_ae m τ hτ ν hab f hf
    have hCoeff (χ : PontryaginDual K) :
        (modulatedIntervalCoefficient ν a b s isOpen_Ioi χ u).val ∈
          supportedSobolevCompletion a b s (Ioo c 0) := by
      obtain ⟨F, hD, hExt, hB⟩ := h χ
      apply (cutoffMellinIntegral_paleyWiener_iff hc hs
        (modulatedIntervalCoefficient ν a b s isOpen_Ioi χ u)).mpr
      refine ⟨F, hD, fun z hz => (hExt z hz).trans ?_, hB⟩
      have hk : MemLp ((Ioi c).indicator (mellinEvaluationKernel 0 z)) 2
          (stripMeasure (-a) (-b) (-s)) :=
        (supportedMellinEvaluation_memLp_iff a b s isOpen_Ioi 0 z).mp
          ((hardySobolev_cutoff_mellinEvaluation_exists_iff hc hz.le hs 0).mpr (Or.inl hz))
      exact (fractionalGroupMoment_onCoefficient m τ hτ ν (Ioi c) isOpen_Ioi χ f u hu z hk).2
    let e := intervalGroupChart m τ hτ
    have hmp : MeasurePreserving e (ν.prod (stripMeasure a b s)) W[a,b,s] := by
      rw [← modulatedInterval_weightedHaar_split m τ hτ ν hab]
      exact intervalGroupChart_preserving m τ hτ ν (stripMeasure a b s)
    have hband := groupProduct_band_of_coefficients m ν a b s c u hCoeff
    filter_upwards [(hmp.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hband, hu] with g hg he hn
    change f g = u.val (e.symm g) at he
    have hlog : modulatedLog m g = (e.symm g).2 := by
      have hh := intervalGroupChart_log m τ hτ (e.symm g)
      change modulatedLog m (e (e.symm g)) = _ at hh
      rwa [e.apply_symm_apply] at hh
    have hOutside : (e.symm g).2 ∉ Ioo c 0 :=
      fun hh => hn (Ioo_subset_Icc_self (hlog.symm ▸ hh))
    exact he.trans (hg hOutside)

end Converse

end
end Masullo
