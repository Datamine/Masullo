import BruhatSupportedHomogeneous
import CyclicFourierQuotientBasis

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 8
set_option linter.overlappingInstances false

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Q" => G ⧸ Subgroup.zpowers γ
local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialInductive m univ

variable [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
  [CompactSpace (G ⧸ Subgroup.zpowers γ)]
  [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]

/-- The supported quotient and the full homogeneous quotient have the same
basis, with the source Haar integrals as coefficient functionals. The
window must meet every log-period orbit in its interior. The section lifts
all basis vectors into tests invariant under every subgroup on which the
fixed norm-one character is trivial. -/
theorem cyclicFourier_supportedQuotientBasis
    (hm : IsProperMap m) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ρ : Measure K) [ρ.IsHaarMeasure] (ω : PontryaginDual K)
    (ν : @Measure Q (borel _)) [νHaar : @Measure.IsHaarMeasure Q _ _ (borel _) ν]
    (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)
    (lift : CircleCharacter K → CircleCharacter G)
    (hlift : ∀ η, (lift η).comp (modulatedKernelInclusion m) = η)
    (d : ℕ ≃ ℤ) (W : Set ℝ) (hW : IsCompact W)
    (hcov : ∀ x : ℝ, ∃ j : ℤ, x + (m γ).toAdd * (j : ℝ) ∈ interior W)
    (L : Subgroup G) (hL : L ≤ K) (hω : ∀ l : L, ω ⟨l.val, hL l.property⟩ = 1) :
    let U := bruhatSupportedInvariant m L ((fun x ↦ (m x).toAdd) ⁻¹' W)
    let V := bruhatCyclicQuotientIsotype m γ ω
    ∃ T : E →L[ℂ] V,
      let T₀ := T.comp U.subtypeL
      ∃ (j : (U ⧸ T₀.ker) ≃L[ℂ] (E ⧸ T.ker))
        (x : ℕ → (U ⧸ T₀.ker)) (a : ℕ → StrongDual ℂ (U ⧸ T₀.ker))
        (b : ℕ → StrongDual ℂ (E ⧸ T.ker)),
        (∀ f z, HasSum (fun n : ℤ ↦ ∫ k : K, (ω k : ℂ) * f.val (k.val * (γ ^ n * z)) ∂ρ)
          ((T f).val.val (QuotientGroup.mk z))) ∧
        (∀ u : U, j (T₀.ker.mkQ u) = T.ker.mkQ u.val) ∧
        (∀ n, ∃ u : U, T₀.ker.mkQ u = x n) ∧
        (∀ n, a n = (b n).comp j.toContinuousLinearMap) ∧
        (∀ n f, b n (T.ker.mkQ f) =
          ∫ z, f.val z * (modulatedCyclicCharacter m γ hγ (lift ω) (d n) (QuotientGroup.mk z) : ℂ) ∂μ) ∧
        range (T.ker.mkQL.precomp (τ := RingHom.id ℂ) ℂ) =
          {l : StrongDual ℂ E | ∀ f ∈ T.ker, l f = 0} ∧
        IsUnconditional b (fun n ↦ strongBidualEvaluation (j (x n))) ∧
        IsSchauderBasis x a ∧ IsAbsolute x a ∧ IsShrinking x a ∧
          IsUnconditional a (fun n ↦ strongBidualEvaluation (x n)) := by
  dsimp only
  letI : MeasurableSpace Q := borel _
  letI : ν.IsHaarMeasure := νHaar
  letI : BorelSpace Q := ⟨rfl⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : ContinuousSMul ℂ (BruhatSchwartz Q) :=
    (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz Q)).continuousSMul
  let U := bruhatSupportedInvariant m L ((fun x ↦ (m x).toAdd) ⁻¹' W)
  let V := bruhatCyclicQuotientIsotype m γ ω
  let c : ℂ := (ν.real univ : ℂ) / (ρ.real univ : ℂ)
  have hρ : (ρ.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  have hνmass : (ν.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  have hc : c ≠ 0 := div_ne_zero hνmass hρ
  obtain ⟨T, e, y, b, hT, he, _, _, hpair, hrange, _, hb, ha, _, hu⟩ :=
    cyclicFourier_quotientBasis m γ hγ hm τ hτ μ ρ ω ν hν lift hlift d
  let T₀ : U →L[ℂ] V := T.comp U.subtypeL
  obtain ⟨S, hS⟩ := exists_bruhatSupportedHomogeneous_section m hm hτ.surjective γ hγ
    ρ ω T hT W hW hcov L hL hω
  obtain ⟨j, hj⟩ := splitQuotientEquiv_restrict T U S hS e c hc he
  let x (n : ℕ) := j.symm (y n)
  let a (n : ℕ) := (b n).comp j.toContinuousLinearMap
  have hrep (n : ℕ) : ∃ u : U, T₀.ker.mkQ u = x n := T₀.ker.mkQ_surjective (x n)
  have hu' : IsUnconditional b (fun n ↦ strongBidualEvaluation (j (x n))) := by
    convert hu using 2
    exact congrArg strongBidualEvaluation (j.apply_symm_apply (y _))
  exact ⟨T, j, x, a, b, hT, hj, hrep, fun _ ↦ rfl, hpair, hrange, hu',
    absoluteBasis_pullback_withStrongDual j y b hb ha hu⟩

end

end Masullo
