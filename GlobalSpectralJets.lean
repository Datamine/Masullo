import GlobalCoprimeAmbient
import CyclicMellinMoments
import SLocalThetaDualGeneration
import RealSchwartzTaylorDual

open Bornology Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev B := SchwartzBergman (univ : Set ℝ)
set_option maxHeartbeats 1500000

/-- The normalized jets of an entire divisor contained in a fixed strip
span a strongly dense subspace of the dual of its Bergman quotient. -/
theorem bergmanDivisor_normalizedJets_span_dense (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (a b : ℝ) (hstrip : ∀ z : ℂ, 0 < analyticOrderAt g z → z.re ∈ Icc a b) :
    let D := bergmanDivisorSubmodule g
    let I := {i : {z : ℂ // z.re ∈ Icc a b} × ℕ //
      (i.2 : ℕ∞) < analyticOrderAt g i.1}
    ∀ J : I → StrongDual ℂ (B ⧸ D),
      (∀ i f, J i (D.mkQ f) = bergmanNormalizedJet i.val.1 i.val.2 f) →
      Dense (Submodule.span ℂ (range J) : Set (StrongDual ℂ (B ⧸ D))) := by
  intro D I J hJ
  let Q := B ⧸ D
  have hF := schwartzBergman_frechet (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
  letI : IsTopologicalAddGroup B := hF.choose
  letI : PolynormableSpace ℂ B := hF.choose_spec.1
  have hN : NuclearLocallyConvex.{0,0} B := nuclearLocallyConvex_of_equiv entireLogMellin
    (positiveRealExponentialDecay_nuclear univ univ_nonempty)
  have hD : IsClosed (D : Set B) := bergmanDivisorSubmodule_isClosed hg
  letI : IsClosed (D : Set B) := hD
  have hFQ := isFrechetTVS_closedQuotient hF D hD
  have hNQ := nuclearLocallyConvex_quotient hN D hD
  letI : IsTopologicalAddGroup Q := hFQ.choose
  letI : PolynormableSpace ℂ Q := hFQ.choose_spec.1
  letI : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  letI : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Q := hFQ.choose_spec.2.2
  letI : T2Space Q := hNQ.1
  letI : ContinuousSMul ℂ Q := (PolynormableSpace.withSeminorms ℂ Q).continuousSMul
  letI : BarrelledSpace ℂ Q := isFrechetTVS_barrelled hFQ
  obtain ⟨e, he⟩ := strongBidual_equiv_of_nuclear hNQ
  have hv (x : Q) : x ∈ (⊥ : Submodule ℂ Q) ↔ ∀ i, J i x = 0 := by
    rw [Submodule.mem_bot]
    exact (bergmanDivisor_normalizedJets_separate g a b hstrip J hJ x).symm
  have hc := strongDual_closure_span_eq_annihilator e he J ⊥ hv
  intro x
  rw [hc]
  intro y hy
  have hz : y = 0 := by simpa only [Submodule.mem_bot] using hy
  rw [hz, map_zero]

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev Test := (GlobalBruhat.polarEvaluation F).ker
private abbrev X := (Test F).map (globalIdelicZetaComponentKernel F η ω).mkQ
private abbrev G (r : GlobalBruhat F) := globalHeckeClearedZeta F ν ω r
private abbrev Z (r : GlobalBruhat F) := globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0
private abbrev H := GlobalCoprimeDecay F ω

include μ hν in
/-- Every pole-cleared minimal Hecke reference has order zero outside
the closed critical strip. -/
theorem globalHeckeClearedZeta_order_zero_off_strip (r : GlobalBruhat F)
    (hmin : ∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (Z F ν ω r) z ≤ meromorphicOrderAt (Z F ν ω f) z)
    (z : ℂ) (hz : z.re < 0 ∨ 1 < z.re) :
    analyticOrderAt (G F ν ω r) z = 0 := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F ω
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨r', L, _, _, hL, hout, _, _⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  have hr' : meromorphicOrderAt (Z F ν ω r') z = 0 := (hL z).symm.trans (hout z hz)
  have h₀ : z ≠ 0 := by rintro rfl; norm_num at hz
  have h₁ : z ≠ 1 := by rintro rfl; norm_num at hz
  have hp : globalHeckePoleFactor F ω z ≠ 0 := by
    by_cases hw : ω = 1
    · simpa only [globalHeckePoleFactor, ite_eq_left hw] using
        mul_ne_zero h₀ (sub_ne_zero.mpr h₁.symm)
    · rw [globalHeckePoleFactor, ite_eq_right hw]
      exact one_ne_zero
  have hP := globalHeckePoleFactor_analytic F ω z
  have hPo : meromorphicOrderAt (globalHeckePoleFactor F ω) z = 0 := by
    rw [hP.meromorphicOrderAt_eq, hP.analyticOrderAt_eq_zero.mpr hp]
    rfl
  have hG : meromorphicOrderAt (G F ν ω r) z ≤ meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) z := by
    rw [globalHeckeClearedZeta_meromorphicOrder, hPo, zero_add, meromorphicOrderAt_const,
      ite_eq_right one_ne_zero, ← hr']
    exact hmin r' z
  have hGa := globalHeckeClearedZeta_analytic F ν ω r z
  have hne : analyticOrderAt (G F ν ω r) z ≠ ⊤ := by
    intro ht
    rw [hGa.meromorphicOrderAt_eq, ht] at hG
    simp [meromorphicOrderAt_const] at hG
  exact le_antisymm (by
    have h := analyticOrder_le_of_meromorphicOrder_le hGa
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z) hne hG
    rw [(analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z).analyticOrderAt_eq_zero.mpr
      one_ne_zero] at h
    exact h) bot_le

/-- Spectral derivative indices, restricted to the critical strip. -/
abbrev GlobalSpectralJetIndices (r : GlobalBruhat F) :=
  {i : {z : ℂ // z.re ∈ Icc (0 : ℝ) 1} × ℕ //
    (i.2 : ℕ∞) < analyticOrderAt (G F ν ω r) i.1}

include μ hν in
/-- The critical-strip jet system on the actual homogeneous theta quotient,
with its quotient topology and the logarithmic Mellin moment formula.
The jets are normalized by the derivative factorial. -/
theorem exists_globalSpectral_nativeJets :
    ∃ (r : GlobalBruhat F) (M : H F ω ≃L[ℂ] B)
      (j : X F η ω →L[ℂ] H F ω),
      let R := j.toLinearMap.range
      let I := GlobalSpectralJetIndices F ν ω r
      ∃ J : I → StrongDual ℂ (H F ω ⧸ R),
        IsClosedEmbedding j ∧
        (∀ f : Test F, ∀ g, (j (globalPolarFreeTestClass F η ω f)).val.val g =
          adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val g) ∧
        (∀ z : ℂ, 0 < analyticOrderAt (G F ν ω r) z → z.re ∈ Icc (0 : ℝ) 1) ∧
        Equicontinuous (fun i (u : H F ω ⧸ R) ↦ J i u) ∧
        IsVonNBounded ℂ (range J) ∧
        (∀ i, ∃ x, ∀ k, J k x = if k = i then 1 else 0) ∧
        Dense (Submodule.span ℂ (range J) : Set (StrongDual ℂ (H F ω ⧸ R))) ∧
        ∀ i u, J i (R.mkQ u) =
          ((i.val.2.factorial : ℕ) : ℂ)⁻¹ *
            ∫ t : ℝ, Complex.exp ((i.val.1 : ℂ) * (t : ℂ)) *
              ((t : ℂ) ^ i.val.2 * (entireLogMellin.symm (M u)).val t) := by
  classical
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  obtain ⟨M, j, q, hj, hjval, _, hq⟩ :=
    exists_globalSpectral_thetaMellinQuotient F ω ν η μ hν r hr hmin
  let D := bergmanDivisorSubmodule (G F ν ω r)
  let I := GlobalSpectralJetIndices F ν ω r
  let R := j.toLinearMap.range
  have hfinite := globalHeckeClearedZeta_order_ne_top F ν ω r hr
  obtain ⟨J, hJ, hc, hb, hd⟩ := bergmanDivisor_quotientJets_biorthogonal (G F ν ω r)
    (globalHeckeBergmanRepresentative F ν ω r)
    (globalHeckeBergmanRepresentative_order F ν ω r) hfinite 0 1 zero_le_one
  let T := strongDualPrecompEquiv q
  have hstrip (z : ℂ) (hz : 0 < analyticOrderAt (G F ν ω r) z) : z.re ∈ Icc (0 : ℝ) 1 := by
    by_contra h
    have hout : z.re < 0 ∨ 1 < z.re := by
      simpa only [mem_Icc, not_and_or, not_le] using h
    rw [globalHeckeClearedZeta_order_zero_off_strip F ν η μ hν ω r hmin z hout] at hz
    exact lt_irrefl _ hz
  refine ⟨r, M, j, fun i : I ↦ T (J i), hj, hjval, hstrip, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have h := Metric.equicontinuousAt_iff_right.mp (hc (q u)) ε hε
    exact q.continuous.continuousAt h
  · have he : range (fun i : I ↦ T (J i)) = T '' range J := range_comp T J
    rw [he]
    exact hb.image T.toContinuousLinearMap
  · intro i
    obtain ⟨x, hx⟩ := hd i
    refine ⟨q.symm x, fun k ↦ ?_⟩
    change J k (q (q.symm x)) = _
    rw [q.apply_symm_apply, hx]
  · have hdense := bergmanDivisor_normalizedJets_span_dense (G F ν ω r)
      (fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt) 0 1 hstrip J hJ
    have he : range (fun i : I ↦ T (J i)) = T '' range J := range_comp T J
    rw [he]
    change Dense (Submodule.span ℂ (T.toLinearMap '' range J) : Set (StrongDual ℂ (H F ω ⧸ R)))
    rw [← Submodule.map_span T.toLinearMap, Submodule.map_coe]
    exact T.surjective.denseRange.dense_image T.continuous hdense
  · intro i u
    change J i (q (R.mkQ u)) = _
    rw [hq, hJ, bergmanNormalizedJet_apply]
    have hm := entireLogMellin_iteratedDeriv_eq_moment (entireLogMellin.symm (M u))
      (i.val.1 : ℂ) i.val.2
    rw [entireLogMellin.apply_symm_apply] at hm
    rw [hm]

#print axioms bergmanDivisor_normalizedJets_span_dense
#print axioms globalHeckeClearedZeta_order_zero_off_strip
#print axioms exists_globalSpectral_nativeJets

end

end Masullo
