import EntireJetDirectSum
import GlobalSpectralHeckeOrders

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000

private abbrev B := SchwartzBergman (univ : Set ℝ)

@[reducible] local instance : TopologicalSpace (StrongDual ℂ CompactOpenEntire) :=
  ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := CompactOpenEntire) (F := ℂ)

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F

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
private abbrev H := GlobalCoprimeDecay F ω
private abbrev G (r : GlobalBruhat F) := globalHeckeClearedZeta F ν ω r

/-- A native Mellin quotient with a divisor model admits the translated
compact-open annihilator and the corresponding biorthogonal moment system. -/
theorem exists_shiftedDivisor_jetSystem (g₀ : ℂ → ℂ) (hg₀ : Differentiable ℂ g₀)
    (b₀ : B) (hb₀ : ∀ z, analyticOrderAt b₀.val z = analyticOrderAt g₀ z)
    (hfinite₀ : ∀ z, analyticOrderAt g₀ z ≠ ⊤)
    (hstrip₀ : ∀ z : ℂ, 0 < analyticOrderAt g₀ z → z.re ∈ Icc (0 : ℝ) 1)
    (M : H F ω ≃L[ℂ] B) (R : Submodule ℂ (H F ω))
    (q : (H F ω ⧸ R) ≃L[ℂ] (B ⧸ bergmanDivisorSubmodule g₀))
    (hq : ∀ u, q (R.mkQ u) = (bergmanDivisorSubmodule g₀).mkQ (M u))
    (a : ℝ) :
    let d := (a : ℂ) * Complex.I
    let g := shiftedCompactOpenGenerator g₀ hg₀ a
    let I := JetIndex g
    let A := compactOpenEntireAnnihilator g.val
    letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
    ∃ (e : (I →₀ ℂ) ≃L[ℂ] A) (U : A →L[ℂ] StrongDual ℂ (H F ω ⧸ R)),
      let J (i : I) := U (e (Finsupp.single i 1))
      let Jn (i : I) := (i.val.2.factorial : ℂ)⁻¹ • J i
      (∀ i : I, (e (Finsupp.single i 1)).val = compactOpenEntireJet i.val.1 i.val.2) ∧
      Injective U ∧ DenseRange U ∧
      (∀ l : A, ∀ u, U l (R.mkQ u) = l.val (bergmanToCompactOpenEntire
        (schwartzBergmanEntireShift d (M u)))) ∧
      (∀ i u, J i (R.mkQ u) =
        ∫ t : ℝ, Complex.exp ((i.val.1 + d) * (t : ℂ)) *
          ((t : ℂ) ^ i.val.2 * (entireLogMellin.symm (M u)).val t)) ∧
      (∀ i : I, ∃ x, ∀ k, J k x = if k = i then 1 else 0) ∧
      Equicontinuous (fun i (x : H F ω ⧸ R) ↦ Jn i x) ∧ IsVonNBounded ℂ (range Jn) := by
  classical
  let d := (a : ℂ) * Complex.I
  let g := shiftedCompactOpenGenerator g₀ hg₀ a
  let I := JetIndex g
  let A := compactOpenEntireAnnihilator g.val
  let D := bergmanDivisorSubmodule g.val
  have hg : Differentiable ℂ (g.val : ℂ → ℂ) := g.property
  have horder (z : ℂ) : analyticOrderAt (g.val : ℂ → ℂ) z = analyticOrderAt g₀ (z + d) :=
    analyticOrderAt_translate_entire hg₀ d z
  have hfinite (z : ℂ) : analyticOrderAt (g.val : ℂ → ℂ) z ≠ ⊤ :=
    horder z ▸ hfinite₀ (z + d)
  have hstrip (z : ℂ) (hz : 0 < analyticOrderAt (g.val : ℂ → ℂ) z) : z.re ∈ Icc (0 : ℝ) 1 := by
    rw [horder] at hz
    have hd : d.re = 0 := by simp [d, Complex.mul_re]
    simpa only [Complex.add_re, hd, add_zero] using hstrip₀ (z + d) hz
  let b := schwartzBergmanEntireShift d b₀
  have hb (z : ℂ) : analyticOrderAt b.val z = analyticOrderAt (g.val : ℂ → ℂ) z := by
    rw [horder, schwartzBergmanEntireShift_analyticOrderAt, hb₀]
  obtain ⟨e, he⟩ := compactOpenEntireAnnihilator_finiteSupportEquiv_of_bergman g hfinite b hb
  obtain ⟨shift, hshift⟩ := exists_bergmanDivisorQuotient_shift hg₀ d
  let Q : (H F ω ⧸ R) ≃L[ℂ] (B ⧸ D) := q.trans shift
  have hQ (u : H F ω) : Q (R.mkQ u) = D.mkQ (schwartzBergmanEntireShift d (M u)) := by
    change shift (q (R.mkQ u)) = _
    rw [hq, hshift]
    rfl
  obtain ⟨U₀, hUi, hUd, hU₀⟩ := exists_compactOpenEntire_restriction g.val hg 0 1 zero_le_one hstrip
  let T := strongDualPrecompEquiv Q
  let U := T.toContinuousLinearMap.comp U₀
  let J (i : I) := U (e (Finsupp.single i 1))
  let Jn (i : I) := (i.val.2.factorial : ℂ)⁻¹ • J i
  have hU (l : A) (u : H F ω) : U l (R.mkQ u) =
      l.val (bergmanToCompactOpenEntire (schwartzBergmanEntireShift d (M u))) := by
    change U₀ l (Q (R.mkQ u)) = _
    rw [hQ, hU₀]
  have hJ (i : I) (u : H F ω) : J i (R.mkQ u) =
      iteratedDeriv i.val.2 (schwartzBergmanEntireShift d (M u)).val i.val.1 := by
    rw [show J i = U (e (Finsupp.single i 1)) from rfl, hU, he, compactOpenEntireJet_apply]
    exact congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv i.val.2 f i.val.1)
      (funext (bergmanToCompactOpenEntire_apply _))
  have hm (i : I) (u : H F ω) : J i (R.mkQ u) =
      ∫ t : ℝ, Complex.exp ((i.val.1 + d) * (t : ℂ)) *
        ((t : ℂ) ^ i.val.2 * (entireLogMellin.symm (M u)).val t) := by
    rw [hJ]
    have hS : (schwartzBergmanEntireShift d (M u)).val = (M u).val ∘ (· + d) :=
      funext (schwartzBergmanEntireShift_apply d (M u))
    have hderiv : iteratedDeriv i.val.2 ((M u).val ∘ (· + d)) i.val.1 =
        iteratedDeriv i.val.2 (M u).val (i.val.1 + d) :=
      congrFun (iteratedDeriv_comp_add_const i.val.2 (M u).val d) i.val.1
    have hm' := entireLogMellin_iteratedDeriv_eq_moment (entireLogMellin.symm (M u))
      (i.val.1 + d) i.val.2
    rw [entireLogMellin.apply_symm_apply] at hm'
    exact (congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv i.val.2 f i.val.1) hS).trans (hderiv.trans hm')

  let k (i : I) : {p : {z : ℂ // z.re ∈ Icc (0 : ℝ) 1} × ℕ //
      (p.2 : ℕ∞) < analyticOrderAt (g.val : ℂ → ℂ) p.1} :=
    ⟨(⟨i.val.1, hstrip _ (bot_le.trans_lt i.property)⟩, i.val.2), i.property⟩
  have hk : Injective k := fun i j h ↦ Subtype.ext (congrArg (fun p ↦ (p.val.1.val, p.val.2)) h)
  obtain ⟨N, hN, hNc, hNb, hNi⟩ := bergmanDivisor_quotientJets_biorthogonal g.val b hb hfinite 0 1 zero_le_one
  have hJn (i : I) : Jn i = T (N (k i)) := by
    ext x
    obtain ⟨u, rfl⟩ := R.mkQ_surjective x
    change (i.val.2.factorial : ℂ)⁻¹ * J i (R.mkQ u) = N (k i) (Q (R.mkQ u))
    rw [hJ, hQ, hN, bergmanNormalizedJet_apply]
  refine ⟨e, U, he, T.injective.comp hUi,
    T.surjective.denseRange.comp hUd T.continuous, hU, hm, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := hNi (k i)
    let c : ℂ := (i.val.2.factorial : ℂ)⁻¹
    refine ⟨c • Q.symm x, fun l ↦ ?_⟩
    have heval := congrArg (fun L : StrongDual ℂ (H F ω ⧸ R) ↦ L (Q.symm x)) (hJn l)
    change (l.val.2.factorial : ℂ)⁻¹ * J l (Q.symm x) = N (k l) (Q (Q.symm x)) at heval
    rw [Q.apply_symm_apply, hx] at heval
    simp only [hk.eq_iff] at heval
    rw [map_smul, smul_eq_mul]
    by_cases hl : l = i
    · subst l
      simpa only [ite_true, c] using heval
    · rw [ite_eq_right hl] at heval ⊢
      have hzero := (mul_eq_zero.mp heval).resolve_left
        (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      rw [hzero, mul_zero]
  · intro u
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have h := Metric.equicontinuousAt_iff_right.mp (hNc (Q u)) ε hε
    filter_upwards [Q.continuous.continuousAt h] with v hv i
    change dist (Jn i u) (Jn i v) < ε
    rw [hJn i]
    exact hv (k i)
  · have hrange : range Jn ⊆ T '' range N := by
      rintro _ ⟨i, rfl⟩
      exact ⟨N (k i), mem_range_self _, (hJn i).symm⟩
    exact IsVonNBounded.subset hrange (hNb.image T.toContinuousLinearMap)

include μ hν in
/-- Corrected Theorem 7.1.4.2 in each imaginary norm-frequency chart.
The annihilator is the locally convex direct sum of the jet coordinates,
and restriction to the actual quotient has dense image. -/
theorem exists_globalSpectral_shiftedBiorthogonal (a : ℝ) :
    ∃ (r : GlobalBruhat F) (M : H F ω ≃L[ℂ] B)
      (j : X F η ω →L[ℂ] H F ω),
      let d := (a : ℂ) * Complex.I
      let g := spectralShiftedGenerator F ν ω r a
      let I := JetIndex g
      let A := compactOpenEntireAnnihilator g.val
      let R := j.toLinearMap.range
      letI : TopologicalSpace (I →₀ ℂ) := finestLocallyConvexTopology _
      ∃ (e : (I →₀ ℂ) ≃L[ℂ] A) (U : A →L[ℂ] StrongDual ℂ (H F ω ⧸ R)),
        let J (i : I) := U (e (Finsupp.single i 1))
        let Jn (i : I) := (i.val.2.factorial : ℂ)⁻¹ • J i
        (∀ f : GlobalBruhat F, ∀ z,
          meromorphicOrderAt (globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0) z ≤
          meromorphicOrderAt (globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0) z) ∧
        IsClosedEmbedding j ∧
        (∀ f : Test F, ∀ q, (j (globalPolarFreeTestClass F η ω f)).val.val q =
          adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val q) ∧
        (∀ i : I, (e (Finsupp.single i 1)).val = compactOpenEntireJet i.val.1 i.val.2) ∧
        Injective U ∧ DenseRange U ∧
        (∀ l : A, ∀ u, U l (R.mkQ u) = l.val (bergmanToCompactOpenEntire
          (schwartzBergmanEntireShift d (M u)))) ∧
        (∀ i u, J i (R.mkQ u) =
          ∫ t : ℝ, Complex.exp ((i.val.1 + d) * (t : ℂ)) *
            ((t : ℂ) ^ i.val.2 * (entireLogMellin.symm (M u)).val t)) ∧
        (∀ i : I, ∃ x, ∀ k, J k x = if k = i then 1 else 0) ∧
        Equicontinuous (fun i (x : H F ω ⧸ R) ↦ Jn i x) ∧ IsVonNBounded ℂ (range Jn) := by
  classical
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  obtain ⟨M, j, q, hj, hjval, _, hq⟩ :=
    exists_globalSpectral_thetaMellinQuotient F ω ν η μ hν r hr hmin
  let g₀ := G F ν ω r
  have hg₀ : Differentiable ℂ g₀ := fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  have hstrip (z : ℂ) (hz : 0 < analyticOrderAt g₀ z) : z.re ∈ Icc (0 : ℝ) 1 := by
    by_contra he
    have hout : z.re < 0 ∨ 1 < z.re := by simpa only [mem_Icc, not_and_or, not_le] using he
    rw [globalHeckeClearedZeta_order_zero_off_strip F ν η μ hν ω r hmin z hout] at hz
    exact lt_irrefl _ hz
  obtain ⟨e, U, h⟩ := exists_shiftedDivisor_jetSystem F ω g₀ hg₀
    (globalHeckeBergmanRepresentative F ν ω r) (globalHeckeBergmanRepresentative_order F ν ω r)
    (globalHeckeClearedZeta_order_ne_top F ν ω r hr) hstrip M j.toLinearMap.range q hq a
  exact ⟨r, M, j, e, U, hmin, hj, hjval, h⟩

#print axioms exists_shiftedDivisor_jetSystem
#print axioms exists_globalSpectral_shiftedBiorthogonal

end

end Masullo
