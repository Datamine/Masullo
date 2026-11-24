import BruhatCyclicIsotypicPeriodization
import BruhatSobolevConvolution
import ModulatedCyclicFourier
import BruhatIsotypeComparison
import ModulatedDecayIsotypes

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1000000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Q" => G ⧸ Subgroup.zpowers γ
local notation "Γ" => Subgroup.zpowers γ

include hm hms in
private theorem integrable_bruhatFourierPairing (μ : Measure G) [μ.IsHaarMeasure]
    (f : BruhatSchwartz G) {w : G → ℂ} (hw : Continuous w) (hn : ∀ x, ‖w x‖ = 1) :
    Integrable (fun x ↦ f.val x * w x) μ := by
  apply (integrable_norm_iff ((bruhatSchwartz_continuous f).mul hw).aestronglyMeasurable).mp
  change Integrable (fun x ↦ ‖f.val x * w x‖) μ
  simp_rw [norm_mul, hn, mul_one]
  simpa [singletonSobolevKernelWeight] using
    bruhatSchwartz_integrable_SobolevKernelWeight μ m hm hms 0 le_rfl f

/-- The unnormalized Haar pairing with a unitary character is continuous
for the full modulated Schwartz–Bruhat topology. -/
def bruhatHaarCharacterPairing (μ : Measure G) [μ.IsHaarMeasure]
    (ξ : PontryaginDual G) : BruhatSchwartz G →L[ℂ] ℂ := by
  let w (x : G) := (ξ x : ℂ)
  have hi (f : BruhatSchwartz G) := integrable_bruhatFourierPairing m hm hms μ f
    (continuous_subtype_val.comp ξ.continuous) (fun x ↦ Circle.norm_coe (ξ x))
  let a : BruhatSchwartz G →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ x, f.val x * w x ∂μ
      map_add' := fun f g ↦ by
        change (∫ x, (f.val x + g.val x) * w x ∂μ) = _
        simp_rw [add_mul]
        exact integral_add (hi f) (hi g)
      map_smul' := fun c f ↦ by
        change (∫ x, (c * f.val x) * w x ∂μ) = c * ∫ x, f.val x * w x ∂μ
        simp_rw [mul_assoc c]
        exact integral_const_mul c _ }
  refine ⟨a, (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G ↦ p.inclusion) a).mpr ?_⟩
  intro p
  change Continuous (a.comp p.inclusion)
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
  intro i
  obtain ⟨q, hq, hbound⟩ := exists_bruhatStage_SobolevKernel_seminorm μ m hm hms 0 le_rfl p
  refine Seminorm.continuous_of_le (q := q) hq fun u ↦ ?_
  change ‖∫ x, p.realize u x * w x ∂μ‖ ≤ q u
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [norm_mul, w, Circle.norm_coe, mul_one]
  simpa [singletonSobolevKernelWeight] using (hbound u).2

@[simp] theorem bruhatHaarCharacterPairing_apply (μ : Measure G) [μ.IsHaarMeasure]
    (ξ : PontryaginDual G) (f : BruhatSchwartz G) :
    bruhatHaarCharacterPairing m hm hms μ ξ f = ∫ x, f.val x * (ξ x : ℂ) ∂μ := rfl

theorem bruhatHaarCharacterPairing_translate (μ : Measure G) [μ.IsHaarMeasure]
    (ξ : PontryaginDual G) (f : BruhatSchwartz G) (a : G) :
    bruhatHaarCharacterPairing m hm hms μ ξ (bruhatSchwartz_translate a f) =
      (ξ a : ℂ) * bruhatHaarCharacterPairing m hm hms μ ξ f := by
  let g (x : G) := (bruhatSchwartz_translate a f).val x * (ξ x : ℂ)
  change (∫ x, g x ∂μ) = _
  rw [← integral_mul_left_eq_self (μ := μ) g a, bruhatHaarCharacterPairing_apply, ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp [g]
  rw [bruhatSchwartz_translate_apply, ← mul_assoc, inv_mul_cancel, one_mul, map_mul, Circle.coe_mul]
  ring

private def cyclicModeIndex : ℤ ≃ Γ :=
  Equiv.ofBijective (fun n ↦ ⟨γ ^ n, Subgroup.zpow_mem_zpowers γ n⟩) (by
    constructor
    · intro i j h
      have hz := congrArg (fun a : Γ ↦ (m a.val).toAdd) h
      change (m (γ ^ i)).toAdd = (m (γ ^ j)).toAdd at hz
      simp only [map_zpow, toAdd_zpow, zsmul_eq_mul] at hz
      exact_mod_cast mul_right_cancel₀ hγ.ne' hz
    · intro a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
      exact ⟨n, Subtype.ext hn⟩)

set_option linter.overlappingInstances false in
/-- The unnormalized group pairing is the unnormalized quotient pairing
after ordinary cyclic periodization with the counting-normalized Weil measure. -/
theorem cyclicFourier_weil_pairing (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [T2Space Q] [LocallyCompactSpace Q]
    (ν : @Measure Q (borel _))
    (hν : IsWeilQuotientMeasure Γ μ Measure.count ν)
    (θ : PontryaginDual Q) (f : BruhatSchwartz G) :
    letI : MeasurableSpace Q := borel _
    (∫ x, f.val x * (θ (QuotientGroup.mk x) : ℂ) ∂μ) =
      ∫ q, (bruhatCyclicPeriodization m hm γ hγ hms f).val q * (θ q : ℂ) ∂ν := by
  letI : MeasurableSpace Q := borel _
  letI : DiscreteTopology Γ := modulatedCyclicSubgroup_discrete m γ hγ
  letI : (Measure.count : Measure Γ).IsHaarMeasure := subgroup_count_isHaarMeasure Γ
  letI : (Measure.count : Measure Γ).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let e := cyclicModeIndex m γ hγ
  letI : Countable Γ := Countable.of_equiv ℤ e
  let F (x : G) := f.val x * (θ (QuotientGroup.mk x) : ℂ)
  have hnorm (x : G) : ‖F x‖ = ‖f.val x‖ := by
    rw [show F x = _ from rfl, norm_mul, Circle.norm_coe, mul_one]
  have hInt : Integrable F μ := integrable_bruhatFourierPairing m hm hms μ f
    (continuous_subtype_val.comp (θ.continuous.comp QuotientGroup.continuous_mk)) (fun _ ↦ Circle.norm_coe _)
  obtain ⟨_, _, hWeil⟩ := weilQuotientIntegral_L1_sigmaFinite Γ
    (modulatedCyclicSubgroup_isClosed m γ hγ) μ Measure.count ν hν hInt
  refine hWeil.trans (integral_congr_ae (.of_forall fun q ↦ ?_))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hs : Summable (fun a : Γ ↦ ‖F (x * a.val)‖) := by
    apply e.summable_iff.mp
    exact (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ f x).congr fun n ↦ by
      change ‖f.val (γ ^ n * x)‖ = ‖F (x * γ ^ n)‖
      rw [hnorm, mul_comm]
  rw [lcaCosetIntegral_mk, integral_countable (integrable_count_iff.mpr hs)]
  simp only [count_real_singleton, one_smul]
  rw [← e.tsum_eq]
  have hterm (n : ℤ) : F (x * (e n).val) = f.val (γ ^ n * x) * (θ (QuotientGroup.mk x) : ℂ) := by
    change f.val (x * γ ^ n) * (θ (QuotientGroup.mk (x * γ ^ n)) : ℂ) = _
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 (Subgroup.zpow_mem_zpowers γ n), mul_one, mul_comm x]
  simp_rw [hterm]
  rw [tsum_mul_right, bruhatCyclicPeriodization_apply m hm γ hγ hms,
    bruhatSchwartz_cyclicOrbitSum_apply]

/-- Compact-kernel Haar averaging multiplies the group pairing with a
character of the selected type by the mass of the kernel Haar measure. -/
theorem bruhatHaarCharacterPairing_kernelAverage (μ : Measure G) [μ.IsHaarMeasure]
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (ρ : Measure m.toMonoidHom.ker) [ρ.IsHaarMeasure]
    (ω : PontryaginDual m.toMonoidHom.ker) (ξ : PontryaginDual G)
    (hξ : ∀ a : m.toMonoidHom.ker, ξ a.val = ω a)
    (f : BruhatSchwartz G) :
    bruhatHaarCharacterPairing m hm hms μ ξ (bruhatSchwartz_kernelAverage m ρ ω hm hms f) =
      (ρ.real univ : ℂ) * bruhatHaarCharacterPairing m hm hms μ ξ f := by
  let K := m.toMonoidHom.ker
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  obtain ⟨A, hA⟩ := exists_bruhatSchwartz_compactAverage K ρ ω
  have he : A f = bruhatSchwartz_kernelAverage m ρ ω hm hms f := by
    apply Subtype.ext
    funext x
    let ev : StrongDual ℂ (BruhatSchwartz G) :=
      ⟨{ toFun := fun u ↦ u.val x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl },
        bruhatSchwartz_continuous_eval x⟩
    change ev (A f) = modulatedKernelAverage m ρ ω f.val x
    refine (hA f ev).2.trans ?_
    apply integral_congr_ae (.of_forall fun k ↦ ?_)
    change (((ω k)⁻¹ : Circle) : ℂ) * (bruhatSchwartz_translate k.val f).val x = _
    rw [bruhatSchwartz_translate_apply]
  rw [← he, (hA f (bruhatHaarCharacterPairing m hm hms μ ξ)).2]
  have hconst (a : K) :
      bruhatHaarCharacterPairing m hm hms μ ξ
        ((((ω a)⁻¹ : Circle) : ℂ) • bruhatSchwartz_translate a.val f) =
      bruhatHaarCharacterPairing m hm hms μ ξ f := by
    rw [map_smul, bruhatHaarCharacterPairing_translate, hξ, smul_eq_mul, ← mul_assoc,
      Circle.coe_inv, inv_mul_cancel₀ (ω a).coe_ne_zero, one_mul]
  simp_rw [hconst]
  rw [integral_const, Complex.real_smul]

set_option linter.overlappingInstances false in
/-- The Haar masses in the pullback formula for Corollary 4.5.1.6.
The quotient coefficient is normalized by the Weil mass. The
homogeneous periodization uses the unnormalized kernel Haar measure. -/
theorem cyclicFourier_homogeneous_weil_pairing (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [T2Space Q] [LocallyCompactSpace Q] [CompactSpace Q]
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (ρ : Measure m.toMonoidHom.ker) [ρ.IsHaarMeasure]
    (ω : PontryaginDual m.toMonoidHom.ker)
    (ν : @Measure Q (borel _))
    (hν : IsWeilQuotientMeasure Γ μ Measure.count ν)
    (θ : PontryaginDual Q)
    (hθ : ∀ a : m.toMonoidHom.ker, θ (QuotientGroup.mk a.val) = ω a)
    (f : ModulatedExponentialInductive m univ) :
    letI : MeasurableSpace Q := borel _
    letI : BorelSpace Q := ⟨rfl⟩
    let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
    let A := modulatedDecay_kernelAverage m ρ ω univ hm hms ⟨0, mem_univ 0⟩
    let B := bruhatCyclicPeriodization m hm γ hγ hms
    (∫ q, (B (J (A f))).val q * (θ q : ℂ) ∂ν) =
      (ρ.real univ : ℂ) * (∫ x, f.val x * (θ (QuotientGroup.mk x) : ℂ) ∂μ) := by
  dsimp only
  letI : MeasurableSpace Q := borel _
  let q : G →ₜ* Q := ⟨QuotientGroup.mk' Γ, QuotientGroup.continuous_mk⟩
  let ξ : PontryaginDual G := θ.comp q
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let A := modulatedDecay_kernelAverage m ρ ω univ hm hms ⟨0, mem_univ 0⟩
  let C := bruhatSchwartz_kernelAverage m ρ ω hm hms
  have hA : J (A f) = C (J f) := by
    apply Subtype.ext
    exact (modulatedDecay_kernelAverage_apply m ρ ω univ hm hms ⟨0, mem_univ 0⟩ f).trans
      (bruhatSchwartz_kernelAverage_apply m ρ ω hm hms (J f)).symm
  exact (cyclicFourier_weil_pairing m hm hms γ hγ μ ν hν θ (J (A f))).symm.trans
    ((congrArg (bruhatHaarCharacterPairing m hm hms μ ξ) hA).trans
      (bruhatHaarCharacterPairing_kernelAverage m hm hms μ ρ ω ξ hθ (J f)))

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- The orbit formula determines the homogeneous periodization operator
and identifies it with ordinary periodization of the compact-kernel average. -/
theorem cyclicFourier_homogeneous_eq_periodize_average
    [T2Space Q] [LocallyCompactSpace Q]
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (ρ : Measure m.toMonoidHom.ker) [ρ.IsHaarMeasure]
    (ω : PontryaginDual m.toMonoidHom.ker)
    (T : ModulatedExponentialInductive m univ →L[ℂ] bruhatCyclicQuotientIsotype m γ ω)
    (hT : ∀ f x, HasSum (fun n : ℤ ↦ ∫ a : m.toMonoidHom.ker, (ω a : ℂ) *
      f.val (a.val * (γ ^ n * x)) ∂ρ) ((T f).val.val (QuotientGroup.mk x)))
    (f : ModulatedExponentialInductive m univ) :
    let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
    let A := modulatedDecay_kernelAverage m ρ ω univ hm hms ⟨0, mem_univ 0⟩
    (T f).val = bruhatCyclicPeriodization m hm γ hγ hms (J (A f)) := by
  dsimp only
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let A := modulatedDecay_kernelAverage m ρ ω univ hm hms ⟨0, mem_univ 0⟩
  apply Subtype.ext
  funext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have he (y : G) : (J (A f)).val y = ∫ a : m.toMonoidHom.ker, (ω a : ℂ) * f.val (a.val * y) ∂ρ := by
    letI : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp
      (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
    change modulatedKernelAverage m ρ ω f.val y = _
    unfold modulatedKernelAverage
    have h := integral_inv_eq_self (fun a : m.toMonoidHom.ker ↦ (ω a : ℂ) * f.val (a.val * y)) ρ
    simpa only [map_inv, Subgroup.coe_inv] using h
  have hS := (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ (J (A f)) x).of_norm.hasSum
  have hT' := (hT f x).congr_fun fun n ↦ he (γ ^ n * x)
  exact (hT'.unique hS).trans
    ((bruhatCyclicPeriodization_apply m hm γ hγ hms (J (A f)) x).trans
      (bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x (J (A f)))).symm

end

end Masullo
