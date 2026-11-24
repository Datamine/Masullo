import GlobalOrbitalDivisor

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 1600000

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


private abbrev P := finiteHeckeOmissionMultiplier F (normOneEulerCharacter F ω)

/-- The orbital generator in the shifted norm-frequency chart. -/
def orbitalShiftedGenerator (r : GlobalBruhat F) (W : Finset (Place F)) (a : ℝ) :
    CompactOpenEntire :=
  shiftedCompactOpenGenerator (globalOrbitalGenerator F ν ω r W)
    (fun z ↦ ((finiteHeckeOmissionMultiplier_analytic F (normOneEulerCharacter F ω) W z).mul
      (globalHeckeClearedZeta_analytic F ν ω r z)).differentiableAt) a

include μ hν in
/-- Corrected Theorem 7.1.4.3 for the actual principal-value theta quotient.
The locally convex direct sum has one block at each distinct zero, with
the total multiplicity of the selected Euler factors at a common zero. -/
theorem exists_globalOrbital_shiftedBiorthogonal (W : Finset (Place F)) (a : ℝ) :
    ∃ (r : GlobalBruhat F) (M : H F ω ≃L[ℂ] B)
      (j : X F η ω →L[ℂ] H F ω),
      let d := (a : ℂ) * Complex.I
      let g := orbitalShiftedGenerator F ν ω r W a
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
          adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F (globalWeilPrincipalValues F W f.val)).val q) ∧
        (∀ z, analyticOrderAt (g.val : ℂ → ℂ) z =
          ((W.filter fun v ↦ P F ω {v} (z + d) = 0).card : ℕ∞) +
            analyticOrderAt (G F ν ω r) (z + d)) ∧
        (∀ z, (∃ v ∈ W, P F ω {v} (z + d) = 0) →
          analyticOrderAt (G F ν ω r) (z + d) = 0) ∧
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
  obtain ⟨M, j, q, hj, hjval, hq⟩ :=
    exists_globalOrbital_thetaMellinQuotient F ω ν η μ hν r hr hmin W
  obtain ⟨hg, hf, hs, b, hb⟩ := exists_globalOrbital_divisorData F ν η μ hν ω r hr hmin W
  let g := globalOrbitalGenerator F ν ω r W
  obtain ⟨e, U, h⟩ := exists_shiftedDivisor_jetSystem F ω g hg b hb hf hs M j.toLinearMap.range q hq a
  refine ⟨r, M, j, e, U, hmin, hj, hjval, ?_, ?_, h⟩
  · intro z
    change analyticOrderAt (fun w ↦ g (w + (a : ℂ) * Complex.I)) z = _
    rw [analyticOrderAt_translate_entire hg]
    exact globalOrbitalGenerator_order F ν ω r W _
  · rintro z ⟨v, _, hv⟩
    let w := z + (a : ℂ) * Complex.I
    have hw : w.re = 0 :=
      finiteHeckeOmissionMultiplier_zero_line F (normOneEulerCharacter F ω) {v} w hv
    exact (globalHeckeClearedZeta_analytic F ν ω r w).analyticOrderAt_eq_zero.mpr
      (globalHeckeClearedZeta_ne_zero_zero_line_of_min F η ν μ hν ω r hmin w hw)

#print axioms exists_globalOrbital_shiftedBiorthogonal

end

end Masullo
