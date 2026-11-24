import IdelicWeilLogProfile
import HeckeExplicitFormula

open Filter Function IsDedekindDomain MeasureTheory MeromorphicOn NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance weilCharNormOneCompact : CompactSpace (K F) := normOneIdeleClass_compact F
local instance weilCharNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilCharNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilCharIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance weilCharIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance weilCharCompletionMeasurable (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance weilCharCompletionBorel (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance weilCharClassMeasurable : MeasurableSpace (IdeleClass F) := borel _
local instance weilCharClassBorel : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance weilCharClassLocallyCompact : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance weilCharClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff

variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Charts := ∀ ω : PontryaginDual (K F), CompletedHeckeChart F ω
private abbrev χ₀ (ω : PontryaginDual (K F)) := heckeOrdinateCharacter F ω 0

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem χ₀_height (ω : PontryaginDual (K F)) : HasHeckeHeight F (χ₀ F ω) 0 := by
  simpa only [neg_zero] using heckeOrdinateCharacter_hasHeight F ω 0

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem χ₀_unramified (E : Charts F) (ω : PontryaginDual (K F)) :
    globalNormOneCharacter F (heckeNormOneRestriction F (χ₀ F ω)) ∈
      (sUnramified F (E ω).stage : Set (QuasiCharacter (IdeleClass F))) := by
  rw [heckeNormOneRestriction_ordinateCharacter]
  exact (E ω).unramified

set_option maxHeartbeats 550000 in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The completed Euler function of the manuscript at height zero has the
same divisor as the chart used to enumerate the idelic zeros. -/
theorem completedHeckeChart_divisor_eq_manuscript (E : Charts F) (ω : PontryaginDual (K F))
    (L : ℂ → ℂ) (hL : MeromorphicOn L univ)
    (he : EqOn L (manuscriptCompletedHeckeEuler F (χ₀ F ω) (E ω).stage
      (E ω).surj (χ₀_unramified F E ω) 0) {z | 1 < z.re}) (z : ℂ) :
    divisor L univ z = completedHeckeZeroOrder F E ω z := by
  let C := E ω
  let d : ℂ := (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F
  have hd : d ≠ 0 := pow_ne_zero _ (inv_ne_zero (by norm_num))
  let L' : ℂ → ℂ := (fun _ => d) * C.continuation
  have hL' : MeromorphicOn L' univ := fun z hz =>
    (MeromorphicAt.const d z).mul (C.meromorphic z hz)
  have he' : EqOn L' (manuscriptCompletedHeckeEuler F (χ₀ F ω) C.stage C.surj
      (χ₀_unramified F E ω) 0) {z | 1 < z.re} := by
    intro s hs
    have hχ : heckeNormOneRestriction F (χ₀ F ω) = ω :=
      heckeNormOneRestriction_ordinateCharacter F ω 0
    have hP (ψ : PontryaginDual (K F)) (hψ : ψ = ω)
        (hU : globalNormOneCharacter F ψ ∈ (sUnramified F C.stage : Set (QuasiCharacter (IdeleClass F)))) :
        C.continuation s = globalCompletedHeckeEuler F ψ C.stage C.surj hU s := by
      subst ψ
      exact C.agrees hs
    rw [manuscriptCompletedHeckeEuler_shift F _ _ _ _ _ (χ₀_height F ω)]
    change d * C.continuation s = d * globalCompletedHeckeEuler F
      (heckeNormOneRestriction F (χ₀ F ω)) C.stage C.surj (χ₀_unramified F E ω)
      (s - ((0 : ℝ) : ℂ) * Complex.I)
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    exact congrArg (d * ·) (hP _ hχ _)
  have hord := meromorphicOrderAt_congr (globalHeckeContinuation_unique_germ hL hL' he he' z)
  unfold completedHeckeZeroOrder
  rw [MeromorphicOn.divisor_apply hL (mem_univ _),
    MeromorphicOn.divisor_apply C.meromorphic (mem_univ _), hord]
  change (meromorphicOrderAt ((fun _ : ℂ => d) * C.continuation) z).untop₀ =
    (meromorphicOrderAt C.continuation z).untop₀
  rw [meromorphicOrderAt_mul (MeromorphicAt.const _ _) (C.meromorphic _ (mem_univ _)),
    meromorphicOrderAt_const, ite_eq_right hd, zero_add]

private theorem hasSum_endpoint_poles (Φ : ℂ → ℂ) (b : Prop) [Decidable b] :
    HasSum (fun z : ℂ => ((if b ∧ (z = 0 ∨ z = 1) then (1 : ℤ) else 0) : ℂ) * Φ z)
      (if b then Φ 0 + Φ 1 else 0) := by
  by_cases hb : b
  · rw [ite_eq_left hb]
    refine ((hasSum_ite_eq (0 : ℂ) (Φ 0)).add (hasSum_ite_eq (1 : ℂ) (Φ 1))).congr_fun ?_
    intro z
    by_cases h0 : z = 0
    · subst z
      simp [hb]
    by_cases h1 : z = 1
    · subst z
      simp [hb]
    · simp [h0, h1]
  · simp [hb, hasSum_zero]

/-- Removing the two endpoint poles leaves the sum over the positive
divisor weights, indexed by their actual support. -/
private theorem hasSum_positive_divisor (d : ℂ → ℤ) (Φ : ℂ → ℂ) (b : Prop) [Decidable b]
    (hd : ∀ z, d z = max (d z) 0 - (if b ∧ (z = 0 ∨ z = 1) then (1 : ℤ) else 0))
    {a : ℂ} (ha : HasSum (fun z => (d z : ℂ) * Φ z) a) :
    HasSum (fun z : {z : ℂ // 0 < d z} => ((d z.val).toNat : ℂ) * Φ z.val)
      (a + if b then Φ 0 + Φ 1 else 0) := by
  let P (z : ℂ) := if b ∧ (z = 0 ∨ z = 1) then (1 : ℤ) else 0
  let D : Set ℂ := {z | 0 < d z}
  let Q (z : ℂ) := ((d z).toNat : ℂ) * Φ z
  have hEq (z : ℂ) : (d z : ℂ) * Φ z + (P z : ℂ) * Φ z = Q z := by
    rw [← add_mul, ← Int.cast_add, show d z + P z = max (d z) 0 by
      have hh := hd z
      change d z = max (d z) 0 - P z at hh
      omega]
    have hmax : ((d z).toNat : ℤ) = max (d z) 0 := by omega
    simp only [Q, ← hmax, Int.cast_natCast]
  have hp : HasSum (fun z => (P z : ℂ) * Φ z) (if b then Φ 0 + Φ 1 else 0) :=
    (hasSum_endpoint_poles Φ b).congr_fun (fun z => by
      by_cases hz : b ∧ (z = 0 ∨ z = 1) <;> simp [P, hz])
  have hsum : HasSum Q (a + if b then Φ 0 + Φ 1 else 0) :=
    (ha.add hp).congr_fun (fun z => (hEq z).symm)
  have he : D.indicator Q = Q := by
    funext z
    by_cases hz : z ∈ D
    · exact indicator_of_mem hz Q
    · have hz' : (d z).toNat = 0 := by
        change ¬ 0 < d z at hz
        omega
      rw [indicator_of_notMem hz, show Q z = 0 by simp [Q, hz']]
  exact hasSum_subtype_iff_indicator.mpr (he.symm ▸ hsum)

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

private abbrev componentSample (g : PositiveRealExponentialDecay (univ : Set ℝ)) (z : ℂ) :=
  mellin (g.val ∘ Real.log) (z - 1 / 2)

set_option maxHeartbeats 1050000 in
include μ hν in
/-- On each norm-one component, the actual idelic zero terms sum to the
characterwise conductor, prime-power and gamma terms with its two pole samples. -/
theorem idelicWeil_component_hasSum (E : Charts F) (ω : PontryaginDual (K F))
    (f : BruhatCompactTest (IdeleClass F)) :
    ∃ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
      (hu : globalNormOneCharacter F (heckeNormOneRestriction F (χ₀ F ω)⁻¹) ∈
        (sUnramified F U : Set (QuasiCharacter (IdeleClass F)))),
      let g := idelicWeilCenteredTest F ν ω f
      Summable (fun j => ‖heckeCenteredPrimeTerm F (χ₀ F ω) g j‖) ∧
      HasSum (fun z : {z : ℂ // 0 < completedHeckeZeroOrder F E ω z} =>
        completedHeckeZeroDistribution F ν E (-1 / 2) ⟨ω, z⟩ f)
        ((Real.log (heckeDiscriminantConductor F (χ₀ F ω)) : ℂ) * g.val 0 -
          (∑' j, heckeCenteredPrimeTerm F (χ₀ F ω) g j) +
          heckeCenteredArchTerm F (χ₀ F ω) (E ω).stage (E ω).surj (χ₀_unramified F E ω) U hU hu 0 g +
          (if ω = 1 then componentSample g 0 + componentSample g 1 else 0)) := by
  let g := idelicWeilCenteredTest F ν ω f
  let d := completedHeckeZeroOrder F E ω
  obtain ⟨L, U, hU, hu, hL, he, hw, _, hAbs, hsum⟩ :=
    manuscriptCompletedHecke_explicitFormula F (χ₀ F ω) (E ω).stage (E ω).surj
      (χ₀_unramified F E ω) ν η μ hν (χ₀_height F ω) g
  have hD (z : ℂ) : divisor L univ z = d z :=
    completedHeckeChart_divisor_eq_manuscript F E ω L hL.meromorphicOn he z
  have hW (z : ℂ) : d z = max (d z) 0 - (if ω = 1 ∧ (z = 0 ∨ z = 1) then (1 : ℤ) else 0) := by
    simpa only [hD, heckeNormOneRestriction_ordinateCharacter, Complex.ofReal_zero, zero_mul, add_zero]
      using hw z
  refine ⟨U, hU, hu, hAbs, ?_⟩
  have hsum' := hsum.congr_fun (fun z => congrArg (fun m : ℤ => (m : ℂ) * componentSample g z) (hD z).symm)
  refine (hasSum_positive_divisor d (componentSample g) (ω = 1) hW hsum').congr_fun ?_
  intro z
  let p : CompletedHeckeZeros F E := ⟨ω, z⟩
  have ht := completedHeckeZeroDistribution_apply_centered F ν E p (-1 / 2) f
  have hr : ((-1 / 2 : ℝ) : ℂ) = -1 / 2 := by (push_cast; norm_num)
  rw [hr] at ht
  change completedHeckeZeroDistribution F ν E (-1 / 2) p f =
    ((d z.val).toNat : ℂ) * mellin (g.val ∘ Real.log) (z.val + (-1 / 2)) at ht
  rw [show z.val + (-1 / 2 : ℂ) = z.val - 1 / 2 by ring] at ht
  exact ht

set_option maxHeartbeats 1350000 in
include μ hν in
/-- Summing the characterwise conductor, prime-power and gamma combination
reproduces the normalized spectral sum minus the global pole terms.
This groups the absolutely convergent zero family by its norm-one components. -/
theorem idelicWeil_characterGeometry_hasSum (E : Charts F)
    (f : BruhatCompactTest (IdeleClass F)) :
    ∃ A : PontryaginDual (K F) → ℂ,
      (∀ ω, ∃ (U : Finset (Place F)) (hU : Surjective (sIdeleClassInclusion F U))
        (hu : globalNormOneCharacter F (heckeNormOneRestriction F (χ₀ F ω)⁻¹) ∈
          (sUnramified F U : Set (QuasiCharacter (IdeleClass F)))),
        let g := idelicWeilCenteredTest F ν ω f
        A ω = (ν.real univ : ℂ)⁻¹ *
          ((Real.log (heckeDiscriminantConductor F (χ₀ F ω)) : ℂ) * g.val 0 -
            (∑' j, heckeCenteredPrimeTerm F (χ₀ F ω) g j) +
            heckeCenteredArchTerm F (χ₀ F ω) (E ω).stage (E ω).surj (χ₀_unramified F E ω) U hU hu 0 g)) ∧
      HasSum A ((ν.real univ : ℂ)⁻¹ *
        (∑' p : CompletedHeckeZeros F E, completedHeckeZeroDistribution F ν E (-1 / 2) p f) -
          idelicWeilPolarDual F ν f) := by
  choose U hU hu hC using fun ω => idelicWeil_component_hasSum F ν η μ hν E ω f
  let g (ω : PontryaginDual (K F)) := idelicWeilCenteredTest F ν ω f
  let d (ω : PontryaginDual (K F)) : ℂ :=
    (Real.log (heckeDiscriminantConductor F (χ₀ F ω)) : ℂ) * (g ω).val 0 -
      (∑' j, heckeCenteredPrimeTerm F (χ₀ F ω) (g ω) j) +
      heckeCenteredArchTerm F (χ₀ F ω) (E ω).stage (E ω).surj (χ₀_unramified F E ω)
        (U ω) (hU ω) (hu ω) 0 (g ω)
  let P (ω : PontryaginDual (K F)) : ℂ :=
    if ω = 1 then componentSample (g ω) 0 + componentSample (g ω) 1 else 0
  let v (p : CompletedHeckeZeros F E) := completedHeckeZeroDistribution F ν E (-1 / 2) p f
  have hnorm : Summable (fun p : CompletedHeckeZeros F E => ‖v p‖) := by
    have h := completedHeckeZeros_mellin_summable F ν η μ hν E f (-1 / 2) univ
    have hs : Summable (fun p : (univ : Set (CompletedHeckeZeros F E)) => ‖v p.val‖) := by
      refine h.congr ?_
      intro p
      change _ = ‖completedHeckeZeroDistribution F ν E (-1 / 2) p.val f‖
      rw [completedHeckeZeroDistribution_apply, norm_mul, Complex.norm_natCast]
    exact summable_subtype_iff_indicator.mp hs |>.congr (fun p => indicator_of_mem (mem_univ p) _)
  have hsum : HasSum v (∑' p, v p) := hnorm.of_norm.hasSum
  let Z (ω : PontryaginDual (K F)) := {z : ℂ // 0 < completedHeckeZeroOrder F E ω z}
  have hSigma : HasSum (fun p : Σ ω, Z ω => v p) (∑' p, v p) := hsum
  have hGrouped : HasSum (fun ω => d ω + P ω) (∑' p, v p) :=
    hSigma.sigma (fun ω => (hC ω).2)
  have hP : HasSum P (componentSample (g 1) 0 + componentSample (g 1) 1) := by
    have hp : HasSum P (P 1) := hasSum_single 1 (fun v hv => by simp [P, hv])
    simpa only [P, ite_eq_left rfl] using hp
  have hd : HasSum d ((∑' p, v p) - (componentSample (g 1) 0 + componentSample (g 1) 1)) :=
    (hGrouped.sub hP).congr_fun (fun ω => (add_sub_cancel_right (d ω) (P ω)).symm)
  let c : ℂ := (ν.real univ : ℂ)⁻¹
  refine ⟨fun ω => c * d ω, fun ω => ⟨U ω, hU ω, hu ω, rfl⟩, ?_⟩
  have hEq : c * (componentSample (g 1) 0 + componentSample (g 1) 1) =
      idelicWeilPolarDual F ν f := by
    rw [idelicWeilPolarDual_apply_centered]
    simp only [componentSample, zero_sub, neg_div, g, c,
      show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
  rw [← hEq, ← mul_sub]
  exact hd.mul_left c

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The logarithmic contact coefficient splits into the field
discriminant and the finite sum of local conductor exponents. -/
theorem heckeDiscriminantConductor_log_eq_local (χ : PontryaginDual (IdeleClass F)) :
    Real.log (heckeDiscriminantConductor F χ) =
      Real.log ((discr F).natAbs : ℝ) +
        ∑' v : Place F, (heckeConductorExponent F χ v : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
  let n := heckeConductorExponent F χ
  let S := (heckeConductorExponent_finiteSupport F χ).toFinset
  have hzero (v : Place F) (hv : v ∉ S) : n v = 0 := by
    exact Function.notMem_support.mp (fun h => hv ((Set.Finite.mem_toFinset _).mpr h))
  have hideal : heckeConductorIdeal F χ = ∏ v ∈ S, v.asIdeal ^ n v := by
    unfold heckeConductorIdeal
    apply finprod_eq_finsetProd_of_mulSupport_subset
    intro v hv
    by_contra h
    exact hv (by simp [hzero v h, n])
  have hprod : ((heckeConductorIdeal F χ).absNorm : ℝ) =
      ∏ v ∈ S, (v.asIdeal.absNorm : ℝ) ^ n v := by
    rw [hideal]
    simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hq (v : Place F) : (v.asIdeal.absNorm : ℝ) ≠ 0 := by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (zero_lt_one.trans h).ne'
  have hdisc : ((discr F).natAbs : ℝ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F)
  rw [heckeDiscriminantConductor, Nat.cast_mul, hprod,
    Real.log_mul hdisc (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hq v)),
    Real.log_prod (fun v _ => pow_ne_zero _ (hq v))]
  simp_rw [Real.log_pow]
  rw [tsum_eq_sum (s := S)]
  intro v hv
  change (n v : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) = 0
  rw [hzero v hv, Nat.cast_zero, zero_mul]

end
end Masullo
