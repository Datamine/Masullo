import BruhatStageLogSeminorms
import BruhatSobolevConvolution
import ModulatedLpCoordinates

open Function MeasureTheory Module Set Topology
open scoped ENNReal

namespace Masullo.WholeBruhatStage

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (P : WholeBruhatStage G)
  [MeasurableSpace P.val.2.finiteFactor] [BorelSpace P.val.2.finiteFactor]

/-- All three logarithmic weight families give the inherited topology of the
kernel-invariant Schwartz–Bruhat subspace, using Haar measure on the original group. -/
theorem withSeminorms_fixed_polynomialLp (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    {d : ℕ} (B : Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (γ : Fin d → Multiplicative ℝ →ₜ* G)
    (hγ : ∀ j, P.coordinates.comp (γ j) = elementaryOneParameter (B j))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    let D a (f : P.fixedSubmodule) := bruhatDerivativeWord ((invariantBasisWord a).map γ) f.val
    ∃ M U : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × ℕ),
    ∃ Q : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × Polynomial ℂ),
      WithSeminorms M ∧ WithSeminorms U ∧ WithSeminorms Q ∧
      (∀ a n f, M (a, n) f = lpNorm
        (fun g => ((|modulatedLog m g| : ℝ) : ℂ) ^ n * (D a f).val g) p μ) ∧
      (∀ a n f, U (a, n) f = lpNorm
        (fun g => (1 + ((|modulatedLog m g| : ℝ) : ℂ) ^ n) * (D a f).val g) p μ) ∧
      (∀ a q f, Q (a, q) f = lpNorm
        (fun g => q.eval ((|modulatedLog m g| : ℝ) : ℂ) * (D a f).val g) p μ) := by
  dsimp only
  let D (a : Fin d → ℕ) : P.fixedSubmodule →ₗ[ℂ] BruhatSchwartz G :=
    (bruhatDerivativeWord ((invariantBasisWord a).map γ)).toLinearMap.comp
      P.fixedSubmodule.subtype
  obtain ⟨M, U, Q, hM, hU, hQ, hMU, hMQ⟩ :=
    bruhatSchwartz_polynomialLpSeminorms (E := P.fixedSubmodule) μ m hm hms (p := p) D
  obtain ⟨L, hL, hLnorm⟩ := P.withSeminorms_fixed_logWeightedLp μ m hm B γ hγ p
  have he : M = L := by
    funext i
    rcases i with ⟨a, n⟩
    ext f
    rw [hM, hLnorm]
    rfl
  have hMW : WithSeminorms M := he.symm ▸ hL
  exact ⟨M, U, Q, hMW, hMU.mp hMW, hMQ.mp hMW, hM, hU, hQ⟩

private theorem lpNorm_top_eq_pointwiseSup {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [Nonempty X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℂ} (hf : Continuous f) (hm : MemLp f ⊤ μ) :
    lpNorm f ⊤ μ = ⨆ x, ‖f x‖ := by
  have hclosed : IsClosed {x | ‖f x‖ ≤ lpNorm f ⊤ μ} :=
    isClosed_le hf.norm continuous_const
  have hdense : Dense {x | ‖f x‖ ≤ lpNorm f ⊤ μ} :=
    Measure.dense_of_ae (ae_le_lpNorm_exponent_top hm)
  have hfull := closure_minimal (Subset.rfl) hclosed
  rw [hdense.closure_eq] at hfull
  have hbound x : ‖f x‖ ≤ lpNorm f ⊤ μ := hfull (mem_univ x)
  have hbdd : BddAbove (range fun x => ‖f x‖) := ⟨_, forall_mem_range.mpr hbound⟩
  apply le_antisymm _ (ciSup_le hbound)
  rw [lpNorm_exponent_top_eq_essSup hm]
  exact essSup_le_of_ae_le _ (ae_of_all μ (le_ciSup hbdd))
    (Filter.isCoboundedUnder_le_of_le _ fun x => norm_nonneg (f x))

/-- Pointwise logarithmic suprema give the inherited topology of the
fixed stage when the ambient directional derivatives project to a basis. -/
theorem withSeminorms_fixed_logWeightedSup (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    {d : ℕ} (B : Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (γ : Fin d → Multiplicative ℝ →ₜ* G)
    (hγ : ∀ j, P.coordinates.comp (γ j) = elementaryOneParameter (B j)) :
    ∃ U : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × ℕ), WithSeminorms U ∧
      ∀ a n f, U (a, n) f = ⨆ g, ‖(1 + ((|modulatedLog m g| : ℝ) : ℂ) ^ n) *
        (bruhatDerivativeWord ((invariantBasisWord a).map γ) f.val).val g‖ := by
  letI : Fact (1 ≤ (⊤ : ℝ≥0∞)) := ⟨le_top⟩
  obtain ⟨_, U, _, _, hU, _, _, hUnorm, _⟩ :=
    P.withSeminorms_fixed_polynomialLp μ m hm hms B γ hγ ⊤
  refine ⟨U, hU, fun a n f => ?_⟩
  rw [hUnorm]
  let u := bruhatDerivativeWord ((invariantBasisWord a).map γ) f.val
  have hlog := continuous_toAdd.comp m.continuous
  apply lpNorm_top_eq_pointwiseSup μ
  · exact (continuous_const.add ((Complex.continuous_ofReal.comp hlog.abs).pow n)).mul
      (bruhatSchwartz_continuous u)
  · have hzero := bruhatSchwartz_logPower_memLp μ m hm hms (p := ⊤) le_top 0 u
    have hn := bruhatSchwartz_logPower_memLp μ m hm hms (p := ⊤) le_top n u
    refine (hzero.add hn).ae_eq (ae_of_all μ fun g => ?_)
    simp only [Pi.add_apply, pow_zero, one_mul, add_mul, u]

/-- The weighted profile of an ambient Bruhat derivative has the finite
integral with the printed radial factor in the Haar normalization of a section. -/
theorem lpNorm_logWeighted_positiveRadial
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsFiniteMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : p ≠ ⊤) (n : ℕ) (u : BruhatSchwartz G) :
    lpNorm (fun g => (1 + ((|modulatedLog m g| : ℝ) : ℂ) ^ n) * u.val g) p
        (modulatedLogMeasure m τ hτ ν) =
      (∫ t in Ioi (0 : ℝ), t⁻¹ * ∫ k,
        ‖(1 + ((|Real.log t| : ℝ) : ℂ) ^ n) *
          u.val (τ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^ p.toReal ∂ν) ^
        (1 / p.toReal) := by
  let μ := modulatedLogMeasure m τ hτ ν
  letI : μ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ν
  let F (g : G) := (1 + ((|modulatedLog m g| : ℝ) : ℂ) ^ n) * u.val g
  have hlog := continuous_toAdd.comp m.continuous
  have hF : Continuous F := (continuous_const.add ((Complex.continuous_ofReal.comp
    hlog.abs).pow n)).mul (bruhatSchwartz_continuous u)
  have hzero := bruhatSchwartz_logPower_memLp μ m hm hτ.surjective hp 0 u
  have hn := bruhatSchwartz_logPower_memLp μ m hm hτ.surjective hp n u
  have hmem : MemLp F p μ := (hzero.add hn).ae_eq (ae_of_all μ fun g => by
    simp only [F, Pi.add_apply, pow_zero, one_mul, add_mul])
  change lpNorm F p μ = _
  rw [lpNorm_modulatedLogMeasure_positiveRadial m τ hτ ν (zero_lt_one.trans_le hp).ne'
    hfin hF hmem]
  apply congrArg (fun y : ℝ => y ^ (1 / p.toReal))
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  apply congrArg (t⁻¹ * ·)
  apply integral_congr_ae
  refine ae_of_all _ fun k => ?_
  have hmod : modulatedLog m (τ (Multiplicative.ofAdd (Real.log t)) * k.val) =
      Real.log t := by
    rw [modulatedLog, map_mul, hτ _, show m k.val = 1 from k.property, mul_one]
    rfl
  simp only [F, hmod]

end Masullo.WholeBruhatStage
