import SLocalMellinCompact
import Mathlib.Analysis.Meromorphic.NormalForm

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev ArchTests := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FiniteTests := locallyConstantTests (∀ v : S, v.val.adicCompletion F)
private abbrev Characters := PontryaginDual (SLocalThetaNormOne F S)

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]

/-- The entire reciprocal of the S-local Euler product, including the
archimedean Gamma factors on the given character component. -/
def sLocalEulerDenominator (ω : Characters F S) (z : ℂ) : ℂ :=
  archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z *
    sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω) z

/-- The S-local Euler product as a meromorphic function. -/
def sLocalEulerFactor (ω : Characters F S) (z : ℂ) : ℂ :=
  (sLocalEulerDenominator F S ω z)⁻¹

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
theorem sLocalEulerDenominator_analytic (ω : Characters F S) (c : ℂ) :
    AnalyticAt ℂ (sLocalEulerDenominator F S ω) c :=
  (archimedeanNumberFieldZetaDenominator_analytic F _ _ c).mul
    (sLocalFiniteZetaDenominator_analytic F S (sLocalFiniteZetaPhases F S ω) c trivial)

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
theorem sLocalEulerDenominator_ne_zero_of_pos (ω : Characters F S) {z : ℂ}
    (hz : 0 < z.re) : sLocalEulerDenominator F S ω z ≠ 0 := by
  apply mul_ne_zero _ (sLocalFiniteZetaDenominator_ne_zero_of_pos F S _ z hz)
  apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
  · exact fun i => by simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  · exact fun i => by simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
theorem sLocalEulerFactor_meromorphic (ω : Characters F S) : Meromorphic (sLocalEulerFactor F S ω) :=
  fun c => (sLocalEulerDenominator_analytic F S ω c).meromorphicAt.inv

private theorem entire_eventually_ne_zero {D : ℂ → ℂ} (hD : ∀ c, AnalyticAt ℂ D c)
    (hOne : D 1 ≠ 0) (c : ℂ) : ∀ᶠ z in 𝓝[≠] c, D z ≠ 0 := by
  have hM : MeromorphicOn D univ := fun z _ => (hD z).meromorphicAt
  have h₁ : meromorphicOrderAt D 1 = 0 := by
    rw [(hD 1).meromorphicOrderAt_eq, (hD 1).analyticOrderAt_eq_zero.mpr hOne]
    rfl
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hD c).meromorphicAt).mp
  exact hM.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 1) (mem_univ c)
    (by simp [h₁])

variable (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

private abbrev Z (ω : Characters F S) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

private theorem Z_pure (ω : Characters F S) (φ : ArchTests F) (ψ : FiniteTests F S) (z : ℂ) :
    Z F S μ ω (sLocalBruhatPure F S φ ψ) z =
      sLocalFiniteZetaContinued F S μ (sLocalFiniteZetaPhases F S ω) z ψ *
        archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
          (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z φ := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  change archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z
    (sLocalFiniteZetaSchwartzTest F S μ (sLocalFiniteZetaPhases F S ω) z
      (sLocalBruhatPure F S φ ψ)) = _
  rw [sLocalFiniteZetaSchwartzTest, sLocalBruhatContractFinite_pure, map_smul]
  rfl

/-- The reciprocal Euler product clears the poles of the full S-local
continued integral, including at coincident poles of several places. -/
theorem sLocalEulerDenominator_mul_zeta_analyticGerm
    (ω : Characters F S) (f : E F S) (c : ℂ) :
    ∃ N : ℂ → ℂ, AnalyticAt ℂ N c ∧
      (fun z => sLocalEulerDenominator F S ω z * Z F S μ ω f z) =ᶠ[𝓝[≠] c] N := by
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  let a := sLocalRealArchParameters F S ω
  let j := sLocalComplexArchParameters F S ω
  let χ := sLocalFiniteZetaPhases F S ω
  let D := sLocalEulerDenominator F S ω
  have hp : f ∈ Submodule.span ℂ {g : E F S |
      ∃ (φ : ArchTests F) (ψ : FiniteTests F S), sLocalBruhatPure F S φ ψ = g} := by
    rw [sLocalBruhatPure_span]
    trivial
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨φ, ψ, rfl⟩ := hg
    obtain ⟨G, hG, he⟩ :=
      (archimedeanNumberFieldZeta_denominator_analyticOperatorGerm F a j c).apply_exists_analytic φ
    let P := fun z => sLocalFiniteZetaCleared F S μ χ z ψ
    have hP : AnalyticAt ℂ P c := sLocalFiniteZetaCleared_analytic F S μ χ ψ c trivial
    have hne := entire_eventually_ne_zero
      (fun z => sLocalFiniteZetaDenominator_analytic F S χ z trivial)
      (sLocalFiniteZetaDenominator_ne_zero_of_pos F S χ 1 (by norm_num)) c
    refine ⟨fun z => G z * P z, hG.mul hP, ?_⟩
    filter_upwards [he, hne] with z hz hne
    have hfinite : sLocalFiniteZetaDenominator F S χ z *
        sLocalFiniteZetaContinued F S μ χ z ψ = P z := by
      change _ * ((sLocalFiniteZetaDenominator F S χ z)⁻¹ * P z) = _
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [Z_pure]
    change (archimedeanNumberFieldZetaDenominator F a j z *
        sLocalFiniteZetaDenominator F S χ z) * (sLocalFiniteZetaContinued F S μ χ z ψ *
          archimedeanNumberFieldZeta F complexTamagawaAngularMeasure a j z φ) = G z * P z
    rw [← hfinite, ← hz]
    simp only [smul_apply, smul_eq_mul]
    ring
  | zero =>
    exact ⟨0, analyticAt_const, .of_forall fun z => by simp [Z, sLocalProductZetaContinued]⟩
  | add f g _ _ hf hg =>
    obtain ⟨A, hA, ha⟩ := hf
    obtain ⟨B, hB, hb⟩ := hg
    refine ⟨fun z => A z + B z, hA.add hB, ?_⟩
    filter_upwards [ha, hb] with z h₁ h₂
    rw [← h₁, ← h₂]
    simp only [Z, sLocalProductZetaContinued, map_add, mul_add]
  | smul b f _ hf =>
    obtain ⟨A, hA, ha⟩ := hf
    refine ⟨fun z => b * A z, analyticAt_const.mul hA, ?_⟩
    filter_upwards [ha] with z h
    rw [← h]
    simp only [Z, sLocalProductZetaContinued, map_smul, smul_eq_mul]
    ring

/-- The pole order of the continued zeta transform is at most the pole order
of the S-local Euler product, with all local multiplicities retained. -/
theorem sLocalZeta_poleOrder_le_euler (ω : Characters F S) (f : E F S) (c : ℂ) :
    meromorphicOrderAt (sLocalEulerFactor F S ω) c ≤ meromorphicOrderAt (Z F S μ ω f) c := by
  obtain ⟨N, hN, h⟩ := sLocalEulerDenominator_mul_zeta_analyticGerm F S μ ω f c
  have hn := entire_eventually_ne_zero (sLocalEulerDenominator_analytic F S ω)
    (sLocalEulerDenominator_ne_zero_of_pos F S ω (z := 1) (by norm_num)) c
  have he : Z F S μ ω f =ᶠ[𝓝[≠] c] fun z => N z * sLocalEulerFactor F S ω z := by
    filter_upwards [h, hn] with z hz hn
    change _ = N z * (sLocalEulerDenominator F S ω z)⁻¹
    rw [← hz, mul_comm (sLocalEulerDenominator F S ω z), mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [meromorphicOrderAt_congr he]
  change _ ≤ meromorphicOrderAt (N * sLocalEulerFactor F S ω) c
  rw [meromorphicOrderAt_mul hN.meromorphicAt (sLocalEulerFactor_meromorphic F S ω c)]
  exact le_add_of_nonneg_left hN.meromorphicOrderAt_nonneg

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
/-- The denominator vanishes exactly at the poles of the S-local Euler product. -/
theorem sLocalEulerFactor_order_lt_zero_iff (ω : Characters F S) (c : ℂ) :
    meromorphicOrderAt (sLocalEulerFactor F S ω) c < 0 ↔
      sLocalEulerDenominator F S ω c = 0 := by
  let D := sLocalEulerDenominator F S ω
  have hD := sLocalEulerDenominator_analytic F S ω c
  have hne := entire_eventually_ne_zero (sLocalEulerDenominator_analytic F S ω)
    (sLocalEulerDenominator_ne_zero_of_pos F S ω (z := 1) (by norm_num)) c
  have ho := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hD.meromorphicAt).2 hne
  have ha : analyticOrderAt D c ≠ ⊤ := by
    intro ht
    apply ho
    rw [hD.meromorphicOrderAt_eq, ht, ENat.map_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ha
  have hc : D c = 0 ↔ n ≠ 0 := by
    rw [← hD.analyticOrderAt_ne_zero, ← hn]
    simp
  change meromorphicOrderAt D⁻¹ c < 0 ↔ D c = 0
  rw [meromorphicOrderAt_inv, hD.meromorphicOrderAt_eq, ← hn, ENat.map_natCast, hc]
  change ((-(n : ℤ)) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) ↔ n ≠ 0
  have hi : -(n : ℤ) < 0 ↔ n ≠ 0 := by omega
  exact WithTop.coe_lt_coe.trans hi

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
/-- The compact-convergence domain is precisely the complement of the
pole support of the S-local Euler product. -/
theorem sLocalMellinRegularSet_iff_noEulerPole (ω : Characters F S) (c : ℂ) :
    c ∈ sLocalMellinRegularSet F S ω ↔ 0 ≤ meromorphicOrderAt (sLocalEulerFactor F S ω) c := by
  rw [← not_lt, sLocalEulerFactor_order_lt_zero_iff, sLocalMellinRegularSet_iff_euler]
  unfold sLocalEulerDenominator archimedeanNumberFieldZetaDenominator
  simp only [mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies,
    realArchZetaDenominator, complexArchZetaDenominator, ne_eq, inv_eq_zero, and_assoc]

/-- After multiplying by the reciprocal Euler product, passing to
meromorphic normal form gives an entire function. -/
theorem sLocalEulerDenominator_mul_zeta_entire
    (ω : Characters F S) (f : E F S) :
    let C z := sLocalEulerDenominator F S ω z * Z F S μ ω f z
    AnalyticOnNhd ℂ (toMeromorphicNFOn C univ) univ := by
  intro C c hc
  have hM : MeromorphicOn C univ := fun z _ =>
    (sLocalEulerDenominator_analytic F S ω z).meromorphicAt.mul
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ f z)
  have hNF := meromorphicNFOn_toMeromorphicNFOn C univ hc
  apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hM hc]
  exact ((hM c hc).meromorphicOrderAt_nonneg_iff).mpr
    (sLocalEulerDenominator_mul_zeta_analyticGerm F S μ ω f c)

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ] in
/-- An entire nonvanishing epsilon factor times the reflected Euler ratio
has the same negative divisor as the original Euler factor. -/
theorem sLocalEulerRatio_negativeDivisor
    (ω ω' : Characters F S) {ε : ℂ → ℂ} (hε : ∀ z, AnalyticAt ℂ ε z)
    (hε₀ : ∀ z, ε z ≠ 0) (c : ℂ) :
    min (meromorphicOrderAt (fun z => ε z * sLocalEulerFactor F S ω z *
        sLocalEulerDenominator F S ω' (1 - z)) c) 0 =
      min (meromorphicOrderAt (sLocalEulerFactor F S ω) c) 0 := by
  let L := sLocalEulerFactor F S ω
  let N (z : ℂ) := ε z * sLocalEulerDenominator F S ω' (1 - z)
  have hN : AnalyticAt ℂ N c := (hε c).mul
    ((sLocalEulerDenominator_analytic F S ω' (1 - c)).comp
      (f := fun z : ℂ => 1 - z) (x := c) (analyticAt_const.sub analyticAt_id))
  have hEq : (fun z => ε z * L z * sLocalEulerDenominator F S ω' (1 - z)) = L * N := by
    funext z
    change ε z * L z * sLocalEulerDenominator F S ω' (1 - z) = L z * N z
    dsimp only [N]
    ac_rfl
  change min (meromorphicOrderAt (fun z => ε z * L z * sLocalEulerDenominator F S ω' (1 - z)) c) 0 =
    min (meromorphicOrderAt L c) 0
  rw [hEq]
  by_cases hpos : 0 < c.re
  · have hL : AnalyticAt ℂ L c := (sLocalEulerDenominator_analytic F S ω c).inv
      (sLocalEulerDenominator_ne_zero_of_pos F S ω hpos)
    rw [min_eq_right (hL.mul hN).meromorphicOrderAt_nonneg,
      min_eq_right hL.meromorphicOrderAt_nonneg]
  · have hdual : 0 < (1 - c).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hN₀ : N c ≠ 0 := mul_ne_zero (hε₀ c) (sLocalEulerDenominator_ne_zero_of_pos F S ω' hdual)
    rw [mul_comm L N, meromorphicOrderAt_mul_of_ne_zero hN hN₀]

include μ in
/-- Restriction of the continued transform to any compact subset of the
complement of the Euler pole divisor is continuous in the uniform norm. -/
def sLocalMellinOnEulerRegularCompact (K : Set (Characters F S × ℂ)) (hK : IsCompact K)
    (hreg : ∀ x ∈ K, 0 ≤ meromorphicOrderAt (sLocalEulerFactor F S x.1) x.2) :
    E F S →L[ℂ] C(K, ℂ) :=
  sLocalMellinOnCompact F S μ K hK
    (fun x hx => (sLocalMellinRegularSet_iff_noEulerPole F S x.1 x.2).mpr (hreg x hx))

@[simp] theorem sLocalMellinOnEulerRegularCompact_apply (K : Set (Characters F S × ℂ))
    (hK : IsCompact K) (hreg : ∀ x ∈ K, 0 ≤ meromorphicOrderAt (sLocalEulerFactor F S x.1) x.2)
    (f : E F S) (x : K) :
    sLocalMellinOnEulerRegularCompact F S μ K hK hreg f x = Z F S μ x.val.1 f x.val.2 :=
  sLocalMellinOnCompact_apply F S μ K hK _ f x

/-- Evaluation of the continued S-local Mellin family on the test space. -/
def sLocalContinuedMellinEval (ω : Characters F S) (z : ℂ) : E F S →L[ℂ] ℂ :=
  (archimedeanNumberFieldZeta F complexTamagawaAngularMeasure
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) z).comp
      (sLocalFiniteZetaSchwartzTest F S μ (sLocalFiniteZetaPhases F S ω) z)

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

/-- Dilation covariance as an identity of continuous linear operators, for
every parameter outside the Euler pole divisor. -/
theorem sLocalContinuedMellinEval_leftTranslate (ω : Characters F S) (g : (SAdeles F S)ˣ)
    {z : ℂ} (hz : 0 ≤ meromorphicOrderAt (sLocalEulerFactor F S ω) z) :
    (sLocalContinuedMellinEval F S μ ω z).comp (sLocalBruhatLeftTranslate F S g) =
      sLocalZetaWeight F S ω z (QuotientGroup.mk g) • sLocalContinuedMellinEval F S μ ω z := by
  apply ContinuousLinearMap.ext
  intro f
  change Z F S μ ω (sLocalBruhatLeftTranslate F S g f) z =
    sLocalZetaWeight F S ω z (QuotientGroup.mk g) * Z F S μ ω f z
  exact sLocalProductZetaContinued_leftTranslate F S μ ω g f
    ((sLocalMellinRegularSet_iff_noEulerPole F S ω z).mpr hz)


end
end Masullo
