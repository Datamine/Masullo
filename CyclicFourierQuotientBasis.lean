import CompactBruhatFourierIsotypes
import CyclicFourierWeilPairing
import CyclicQuotientBasisTransport

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 8
set_option linter.overlappingInstances false

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Q" => G ⧸ Subgroup.zpowers γ
local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialInductive m univ

theorem modulatedCyclicQuotient_enumerable
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (γ : G) (hγ : 0 < (m γ).toAdd)
    (lift : CircleCharacter m.toMonoidHom.ker → CircleCharacter G)
    (hlift : ∀ η, (lift η).comp (modulatedKernelInclusion m) = η) :
    Nonempty (ℕ ≃ PontryaginDual (G ⧸ Subgroup.zpowers γ)) := by
  obtain ⟨e⟩ := modulatedCyclicIndex_enumerable m hm
  let t : (CircleCharacter m.toMonoidHom.ker × ℤ) → PontryaginDual (G ⧸ Subgroup.zpowers γ) :=
    fun p ↦ modulatedCyclicCharacter m γ hγ (lift p.1) p.2
  exact ⟨e.trans (Equiv.ofBijective t (modulatedCyclicCharacter_bijective m hm τ hτ γ hγ lift hlift))⟩

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem cyclicMode_restrict (χ : CircleCharacter G) (n : ℤ) (a : K) :
    modulatedCyclicCharacter m γ hγ χ n (QuotientGroup.mk a.val) = χ a.val := by
  have ha : m a.val = 1 := a.property
  change χ a.val * Circle.exp (_ * (m a.val).toAdd) = _
  rw [ha, toAdd_one, mul_zero, Circle.exp_zero, mul_one]

variable [hQ : T2Space (G ⧸ Subgroup.zpowers γ)] [hLC : LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
  [hC : CompactSpace (G ⧸ Subgroup.zpowers γ)]
  [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]

/-- Corollary 4.5.1.6 with the Haar scaling in the basis identification.
The raw group integrals are the quotient dual basis. The inverse characters
are obtained using the indicated rescaling of homogeneous periodization. -/
theorem cyclicFourier_quotientBasis
    (hm : IsProperMap m) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ρ : Measure K) [ρ.IsHaarMeasure] (ω : PontryaginDual K)
    (ν : @Measure Q (borel _)) [νHaar : @Measure.IsHaarMeasure Q _ _ (borel _) ν]
    (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)
    (lift : CircleCharacter K → CircleCharacter G)
    (hlift : ∀ η, (lift η).comp (modulatedKernelInclusion m) = η)
    (d : ℕ ≃ ℤ) :
    let V := bruhatCyclicQuotientIsotype m γ ω
    let c := (ν.real univ : ℂ) / (ρ.real univ : ℂ)
    ∃ (T : E →L[ℂ] V) (e : (E ⧸ T.ker) ≃L[ℂ] V)
      (x : ℕ → (E ⧸ T.ker)) (a : ℕ → StrongDual ℂ (E ⧸ T.ker)),
      (∀ f z, HasSum (fun n : ℤ ↦ ∫ k : K, (ω k : ℂ) * f.val (k.val * (γ ^ n * z)) ∂ρ)
        ((T f).val.val (QuotientGroup.mk z))) ∧
      (∀ f, e (T.ker.mkQ f) = c • T f) ∧
      (∀ n, (e (x n)).val = compactBruhatCharacter
        (modulatedCyclicCharacter m γ hγ (lift ω) (d n))⁻¹) ∧
      (∀ n, ∃ f : E, f ∈ modulatedDecayIsotype m ω univ ∧ T.ker.mkQ f = x n ∧
        bruhatCyclicPeriodization m hm γ hγ hτ.surjective
          (modulatedDecay_zeroInclusion m univ (mem_univ 0) f) =
          (ν.real univ : ℂ)⁻¹ • (e (x n)).val) ∧
      (∀ n f, a n (T.ker.mkQ f) =
        ∫ z, f.val z * (modulatedCyclicCharacter m γ hγ (lift ω) (d n) (QuotientGroup.mk z) : ℂ) ∂μ) ∧
      range (T.ker.mkQL.precomp (τ := RingHom.id ℂ) ℂ) =
        {l : StrongDual ℂ E | ∀ f ∈ T.ker, l f = 0} ∧
      IsEmbedding (T.ker.mkQL.precomp (τ := RingHom.id ℂ) ℂ :
        StrongDual ℂ (E ⧸ T.ker) →L[ℂ] StrongDual ℂ E) ∧
      IsSchauderBasis x a ∧ IsAbsolute x a ∧ IsShrinking x a ∧
        IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
  classical
  dsimp only
  letI : MeasurableSpace Q := borel _
  letI : ν.IsHaarMeasure := νHaar
  letI : BorelSpace Q := ⟨rfl⟩
  letI : SecondCountableTopology Q := TopologicalSpace.Quotient.secondCountableTopology QuotientGroup.isOpenMap_coe
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : ContinuousSMul ℂ (BruhatSchwartz Q) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz Q)).continuousSMul
  let V := bruhatCyclicQuotientIsotype m γ ω
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let B := bruhatCyclicPeriodization m hm γ hγ hτ.surjective
  let c := (ν.real univ : ℂ) / (ρ.real univ : ℂ)
  have hρ : (ρ.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  have hνmass : (ν.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  have hc : c ≠ 0 := div_ne_zero hνmass hρ
  obtain ⟨T, _, _, hT, hTiso⟩ := exists_bruhatCyclic_homogeneousPeriodization
    m hm hτ.surjective γ hγ ρ ω univ (mem_univ 0)
  obtain ⟨S, hS⟩ := exists_bruhatCyclic_weighted_isotypeSection m hm hτ.surjective γ hγ ω univ (mem_univ 0)
  let R : V →L[ℂ] E := (ρ.real univ : ℂ)⁻¹ • ((modulatedDecayIsotype m ω univ).subtypeL.comp S)
  have hR : RightInverse R T := by
    intro y
    apply Subtype.ext
    change (T ((ρ.real univ : ℂ)⁻¹ • (S y).val)).val = y.val
    rw [map_smul]
    change (ρ.real univ : ℂ)⁻¹ • (T (S y).val).val = y.val
    rw [hTiso _ (S y).property, hS, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  obtain ⟨e, he⟩ := splitQuotientEquiv_scaled T R hR c hc
  let θ (n : ℕ) : PontryaginDual Q := modulatedCyclicCharacter m γ hγ (lift ω) (d n)
  obtain ⟨hinj, hvec, hzero⟩ := cyclicFourierIsotype_modes m hm γ hγ ω ν τ hτ lift hlift d
  obtain ⟨eAll⟩ := modulatedCyclicQuotient_enumerable m hm τ hτ γ hγ lift hlift
  obtain ⟨P, hP⟩ := exists_cyclicFourierIsotype_projection m hm γ hγ ρ ω hτ.surjective
  obtain ⟨hb, ha, _, hu⟩ := compactBruhatFourier_component_basis ν V P hP eAll θ hinj hvec hzero
  let y (n : ℕ) : V := ⟨compactBruhatCharacter (θ n)⁻¹, hvec n⟩
  let b (n : ℕ) : StrongDual ℂ V := (compactBruhatFourierCoeff ν (θ n)).comp V.subtypeL
  let x (n : ℕ) := e.symm (y n)
  let a (n : ℕ) := (b n).comp e.toContinuousLinearMap
  have hx (n : ℕ) : (e (x n)).val = compactBruhatCharacter (θ n)⁻¹ :=
    congrArg Subtype.val (e.apply_symm_apply (y n))
  have hiso (f : E) (hf : f ∈ modulatedDecayIsotype m ω univ) :
      (e (T.ker.mkQ f)).val = (ν.real univ : ℂ) • B (J f) := by
    rw [he]
    change c • (T f).val = _
    rw [hTiso _ hf, smul_smul, show c * (ρ.real univ : ℂ) = (ν.real univ : ℂ) from div_mul_cancel₀ _ hρ]
  have hrep (n : ℕ) : ∃ f : E, f ∈ modulatedDecayIsotype m ω univ ∧
      T.ker.mkQ f = x n ∧ B (J f) = (ν.real univ : ℂ)⁻¹ • (e (x n)).val := by
    let v := c⁻¹ • y n
    let f := R v
    have hf : f ∈ modulatedDecayIsotype m ω univ :=
      (modulatedDecayIsotype m ω univ).smul_mem _ (S v).property
    have hq : T.ker.mkQ f = x n := by
      apply e.injective
      rw [he, show T f = v from hR v, show e (x n) = y n from e.apply_symm_apply (y n)]
      exact (smul_smul c c⁻¹ (y n)).trans (by rw [mul_inv_cancel₀ hc, one_smul])
    refine ⟨f, hf, hq, ?_⟩
    rw [← hq, hiso _ hf, smul_smul, inv_mul_cancel₀ hνmass, one_smul]
  have hpair (n : ℕ) (f : E) : a n (T.ker.mkQ f) =
      ∫ z, f.val z * (θ n (QuotientGroup.mk z) : ℂ) ∂μ := by
    have hθ (k : K) : θ n (QuotientGroup.mk k.val) = ω k :=
      (cyclicMode_restrict m γ hγ (lift ω) (d n) k).trans (DFunLike.congr_fun (hlift ω) k)
    have hPeriod := cyclicFourier_homogeneous_eq_periodize_average m hm hτ.surjective
      γ hγ ρ ω T hT f
    have hWeil := cyclicFourier_homogeneous_weil_pairing m hm hτ.surjective γ hγ
      μ ρ ω ν hν (θ n) hθ f
    change b n (e (T.ker.mkQ f)) = _
    rw [he, map_smul]
    change c * compactBruhatFourierCoeff ν (θ n) (T f).val = _
    rw [compactBruhatFourierCoeff_apply, hPeriod, hWeil]
    dsimp only [c]
    field_simp [hρ, hνmass]
  exact ⟨T, e, x, a, hT, he, hx, hrep, hpair, quotientDual_strongRange T.ker,
    splitQuotientStrongDual_isEmbedding T R hR, absoluteBasis_pullback_withStrongDual e y b hb ha hu⟩

end

end Masullo
