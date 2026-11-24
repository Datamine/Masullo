import DedekindEulerProduct
import HeckeEulerNonvanishing
import GlobalHeckeGaussianReference
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

open Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- The trivial finite Hecke product is the Dedekind zeta series. -/
theorem globalFiniteHeckeEuler_trivial_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    globalFiniteHeckeEuler F 1 s = dedekindZeta F s := by
  unfold globalFiniteHeckeEuler
  apply HasProd.tprod_eq
  apply (dedekindZeta_hasProd F hs).congr_fun
  intro v
  have hunit (g : IdeleClass F) : normOneEulerCharacter F 1 g = 1 := rfl
  have hunramified : unramifiedFiniteCharacter F (normOneEulerCharacter F 1) v :=
    fun u _ ↦ hunit _
  simp [heckeEulerFactor, heckeEulerCoefficient, hunramified, hunit]

variable (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F 1 ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev Γtriv (s : ℂ) :=
  Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
    Complex.Gammaℂ s ^ InfinitePlace.nrComplexPlaces F

/-- The canonical completed product uses the full Deligne gamma factor at
each complex place. -/
theorem globalCompletedHeckeEuler_trivial_eq_dedekindZeta {s : ℂ} (h : 1 < s.re) :
    globalCompletedHeckeEuler F 1 S hs hu s = Γtriv F s * dedekindZeta F s := by
  let A := sLocalNormOneCharacterOfGlobal F 1 S hs hu
  let D := archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S A) (sLocalComplexArchParameters F S A)
  change (D s)⁻¹ * globalFiniteHeckeEuler F 1 s = _
  rw [globalFiniteHeckeEuler_trivial_eq_dedekindZeta F h]
  have hA : A = 1 := sLocalNormOneCharacterOfGlobal_trivial F S hs hu
  have hD : (D s)⁻¹ = Γtriv F s := by
    dsimp only [D, archimedeanNumberFieldZetaDenominator]
    rw [hA, mul_inv_rev, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    simp only [realArchZetaDenominator, complexArchZetaDenominator, inv_inv,
      sLocalComplexArchParameters_one, sLocalRealArchParameters_one, Int.natAbs_zero,
      Nat.cast_zero, zero_div, add_zero, Finset.prod_const, Finset.card_univ, Γtriv, mul_comm]
  rw [hD]

private theorem Γtriv_continuousAt_one :
    ContinuousAt (Γtriv F) (1 : ℂ) := by
  have hR : ContinuousAt Complex.Gammaℝ (1 : ℂ) := by
    have h := Complex.differentiable_Gammaℝ_inv.differentiableAt (x := (1 : ℂ))
    have hc := (h.inv (inv_ne_zero (by simp [Complex.Gammaℝ_one]))).continuousAt
    change ContinuousAt (fun s : ℂ ↦ ((Complex.Gammaℝ s)⁻¹)⁻¹) 1 at hc
    simpa only [inv_inv] using hc
  have hC : ContinuousAt Complex.Gammaℂ (1 : ℂ) := by
    have h := Complex.differentiable_Gammaℂ_inv.differentiableAt (x := (1 : ℂ))
    have hn : Complex.Gammaℂ 1 ≠ 0 := by
      simp [Complex.Gammaℂ_one, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    have hc := (h.inv (inv_ne_zero hn)).continuousAt
    change ContinuousAt (fun s : ℂ ↦ ((Complex.Gammaℂ s)⁻¹)⁻¹) 1 at hc
    simpa only [inv_inv] using hc
  exact (hR.pow _).mul (hC.pow _)

private theorem tendsto_real_punctured_one :
    Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    change (r : ℂ) ≠ 1
    exact_mod_cast (show r ≠ 1 from (show 1 < r from hr).ne')

private theorem trivial_gamma_mul_dedekind_right_limit :
    Tendsto (fun r : ℝ ↦ ((r : ℂ) - 1) * (Γtriv F r * dedekindZeta F r))
      (𝓝[>] (1 : ℝ)) (𝓝 (Γtriv F 1 * (dedekindZeta_residue F : ℂ))) := by
  have hζ := tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have hγ := (Γtriv_continuousAt_one F).tendsto.comp
    (tendsto_real_punctured_one.mono_right nhdsWithin_le_nhds)
  apply (hγ.mul hζ).congr'
  exact Eventually.of_forall fun r ↦ by dsimp only [Function.comp_apply]; ring

/-- The real-axis residue limit for the completed trivial zeta function
with full complex gamma factors. -/
theorem completedDedekindZeta_right_residue_one :
    Tendsto (fun r : ℝ ↦ ((r : ℂ) - 1) *
      ((Complex.Gammaℝ r ^ InfinitePlace.nrRealPlaces F *
        Complex.Gammaℂ r ^ InfinitePlace.nrComplexPlaces F) * dedekindZeta F r))
      (𝓝[>] (1 : ℝ)) (𝓝 ((1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ))) := by
  simpa only [Γtriv, Complex.Gammaℝ_one, Complex.Gammaℂ_one, one_pow, one_mul] using
    trivial_gamma_mul_dedekind_right_limit F

/-- The residue at one of the canonical completed trivial Euler product.
Its complex-place normalization contributes one factor of π⁻¹ per place. -/
theorem globalCompletedHecke_trivial_residue_one {L : ℂ → ℂ}
    (hm : MeromorphicAt L 1) (hp : meromorphicOrderAt L 1 = (-1 : ℤ))
    (he : EqOn L (globalCompletedHeckeEuler F 1 S hs hu) {z | 1 < z.re}) :
    Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ))
      (𝓝 ((1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ))) := by
  let c := Γtriv F 1 * (dedekindZeta_residue F : ℂ)
  let P (z : ℂ) := (z - 1) * L z
  have hright : Tendsto (fun r : ℝ ↦ P r) (𝓝[>] (1 : ℝ)) (𝓝 c) := by
    apply (trivial_gamma_mul_dedekind_right_limit F).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hre : (r : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hr
    dsimp only [P]
    rw [he hre, globalCompletedHeckeEuler_trivial_eq_dedekindZeta F S hs hu hre]
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) 1 := by fun_prop
  have horder : meromorphicOrderAt P 1 = 0 := by
    rw [show P = (fun z : ℂ ↦ z - 1) * L from rfl, meromorphicOrderAt_mul ha.meromorphicAt hm, hp]
    have ho : meromorphicOrderAt (fun z : ℂ ↦ z - 1) 1 = (1 : ℤ) := by
      apply (meromorphicOrderAt_eq_int_iff ha.meromorphicAt).mpr
      exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, .of_forall (by simp)⟩
    rw [ho]
    decide
  obtain ⟨d, _, hd⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero (ha.meromorphicAt.mul hm) horder
  have hd' : d = c := tendsto_nhds_unique (hd.comp tendsto_real_punctured_one) hright
  rw [hd'] at hd
  change Tendsto P (𝓝[≠] (1 : ℂ)) (𝓝 c) at hd
  simpa only [P, c, Γtriv, Complex.Gammaℝ_one, Complex.Gammaℂ_one, one_pow, one_mul] using hd

/-- The actual displayed Euler product (3.2.1.2) for the trivial character.
Equation (3.2.1.5) uses half of Deligne's gamma factor at each complex place. -/
def manuscriptTrivialHeckeEuler (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
    (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F * globalFiniteHeckeEuler F 1 s

theorem manuscriptTrivialHeckeEuler_eq_scaled {s : ℂ} (h : 1 < s.re) :
    manuscriptTrivialHeckeEuler F s =
      (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F * globalCompletedHeckeEuler F 1 S hs hu s := by
  rw [manuscriptTrivialHeckeEuler, globalCompletedHeckeEuler_trivial_eq_dedekindZeta F S hs hu h,
    globalFiniteHeckeEuler_trivial_eq_dedekindZeta F h, div_pow, div_eq_mul_inv, ← inv_pow]
  ring

/-- The class number formula gives the right-hand residue limit for the
Euler product with exactly the gamma normalization in the manuscript. -/
theorem manuscriptTrivialHeckeEuler_right_residue_one :
    Tendsto (fun r : ℝ ↦ ((r : ℂ) - 1) * manuscriptTrivialHeckeEuler F r)
      (𝓝[>] (1 : ℝ)) (𝓝 (((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ))) := by
  let a := (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F
  have h := (trivial_gamma_mul_dedekind_right_limit F).const_mul a
  have hc : a * (Γtriv F 1 * (dedekindZeta_residue F : ℂ)) =
      ((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ) := by
    simp only [a, Γtriv, Complex.Gammaℝ_one, Complex.Gammaℂ_one, one_pow, one_mul, one_div]
    rw [← mul_assoc, ← mul_pow, ← mul_inv]
  rw [hc] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hs' : 1 < (r : ℂ).re := by simpa using hr
  rw [manuscriptTrivialHeckeEuler, globalFiniteHeckeEuler_trivial_eq_dedekindZeta F hs',
    div_pow, div_eq_mul_inv, ← inv_pow]
  dsimp only [a]
  ring

/-- Scaling a canonical continuation to the manuscript's Euler product
gives the corrected punctured residue at one. -/
theorem manuscriptTrivialHeckeEuler_continuation_residue_one {L : ℂ → ℂ}
    (hm : MeromorphicAt L 1) (hp : meromorphicOrderAt L 1 = (-1 : ℤ))
    (he : EqOn L (globalCompletedHeckeEuler F 1 S hs hu) {z | 1 < z.re}) :
    let Lₚ : ℂ → ℂ := fun z ↦ (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F * L z
    EqOn Lₚ (manuscriptTrivialHeckeEuler F) {z | 1 < z.re} ∧
      Tendsto (fun z : ℂ ↦ (z - 1) * Lₚ z) (𝓝[≠] (1 : ℂ))
        (𝓝 (((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
          (dedekindZeta_residue F : ℂ))) := by
  intro Lₚ
  let a := (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · change a * L z = _
    rw [he hz, manuscriptTrivialHeckeEuler_eq_scaled F S hs hu hz]
  have ht := (globalCompletedHecke_trivial_residue_one F S hs hu hm hp he).const_mul a
  have hc : a * ((1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
      (dedekindZeta_residue F : ℂ)) =
      ((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ) := by
    simp only [a, one_div]
    rw [← mul_assoc, ← mul_pow, ← mul_inv]
  rw [hc] at ht
  apply ht.congr'
  exact Eventually.of_forall fun z ↦ by dsimp only [Lₚ, a]; ring

/-- A field of fourth roots of unity refutes the printed residue at one.
Its different has norm four and it has one complex place. -/
theorem manuscriptTrivialHeckeEuler_residue_one_printed_false :
    let K := CyclotomicField 4 ℚ
    ¬ Tendsto (fun r : ℝ ↦ ((r : ℂ) - 1) * manuscriptTrivialHeckeEuler K r)
      (𝓝[>] (1 : ℝ))
      (𝓝 ((dedekindZeta_residue K /
        Real.sqrt ((differentIdeal ℤ (𝓞 K)).absNorm : ℝ) : ℝ) : ℂ)) := by
  let K := CyclotomicField 4 ℚ
  change ¬ Tendsto (fun r : ℝ ↦ ((r : ℂ) - 1) * manuscriptTrivialHeckeEuler K r)
    (𝓝[>] (1 : ℝ)) (𝓝 ((dedekindZeta_residue K /
      Real.sqrt ((differentIdeal ℤ (𝓞 K)).absNorm : ℝ) : ℝ) : ℂ))
  intro hp
  letI : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  letI hcyclo : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  have hplaces : InfinitePlace.nrComplexPlaces K = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 4 K]
    decide
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclotomicExtension {2 ^ 2} ℚ K := hcyclo
  have hd : discr K = -4 := by
    have h := IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K
    norm_num at h
    exact h
  have habs : (differentIdeal ℤ (𝓞 K)).absNorm = 4 := by
    rw [absNorm_differentIdeal K, hd]
    decide
  have hsqrt : Real.sqrt ((differentIdeal ℤ (𝓞 K)).absNorm : ℝ) = 2 := by
    rw [habs]
    norm_num
  have he := tendsto_nhds_unique (manuscriptTrivialHeckeEuler_right_residue_one K) hp
  rw [hplaces, pow_one, hsqrt, Complex.ofReal_div] at he
  push_cast at he
  have hm : (dedekindZeta_residue K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)
  have hc : (2 * (Real.pi : ℂ))⁻¹ = (2 : ℂ)⁻¹ :=
    mul_right_cancel₀ hm (by simpa [div_eq_mul_inv, mul_comm] using he)
  have hr := congrArg Complex.re (congrArg Inv.inv hc)
  norm_num [Complex.mul_re] at hr
  linarith [Real.pi_gt_three]

/-- No continuation of the displayed product in the fourth cyclotomic field
can have the manuscript's stated residue at one. -/
theorem manuscriptTrivialHeckeEuler_continuation_printed_false
    {L : ℂ → ℂ}
    (he : EqOn L (manuscriptTrivialHeckeEuler (CyclotomicField 4 ℚ)) {z | 1 < z.re}) :
    let K := CyclotomicField 4 ℚ
    ¬ Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ))
      (𝓝 ((dedekindZeta_residue K /
        Real.sqrt ((differentIdeal ℤ (𝓞 K)).absNorm : ℝ) : ℝ) : ℂ)) := by
  intro K h
  apply manuscriptTrivialHeckeEuler_residue_one_printed_false
  apply (h.comp tendsto_real_punctured_one).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hs : (r : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hr
  simp only [Function.comp_apply, he hs]

private abbrev K := normOneIdeleClass F
local instance heckeResiduesIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance heckeResiduesIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩
local instance heckeResiduesNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance heckeResiduesNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include hν in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A trivial Euler reference with the same scalar in its idelic integral
and its Fourier value at zero fixes the numerical norm-one Haar mass. -/
theorem normOneHaar_mass_of_trivialEuler_reference
    (f : GlobalBruhat F) (d : ℂ) (hd : d ≠ 0)
    (hzero : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 =
      d * (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F)
    (hEuler : ∀ r : ℝ, 1 < r →
      idelicZetaIntegral F η (GlobalBruhat.algebraicEquiv F f).val
        (compactIdeleClassCharacter F 1) r =
        d * ((Complex.Gammaℝ r ^ InfinitePlace.nrRealPlaces F *
          Complex.Gammaℂ r ^ InfinitePlace.nrComplexPlaces F) * dedekindZeta F r)) :
    ν.real univ = dedekindZeta_residue F := by
  let χ := compactIdeleClassCharacter F (1 : PontryaginDual (K F))
  let a := (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F
  have ha : a ≠ 0 := pow_ne_zero _
    (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hχ : χ = 1 := by
    ext q
    change (Circle.toUnits ((1 : PontryaginDual (K F)) (ideleClassNormOnePart F q)) : ℂ) = 1
    rw [PontryaginDual.one_apply, map_one]
    rfl
  have hcont (r : ℝ) (hr : 1 < r) :
      globalZetaContinued F ν f χ 0 r =
        idelicZetaIntegral F η (GlobalBruhat.algebraicEquiv F f).val χ r := by
    apply globalZetaContinued_eq_idelic F η ν hν f χ (compactIdeleClassCharacter_unitary F 1)
    · simp
    · intro t
      simp [hχ]
    · simpa only [Complex.ofReal_re] using hr
  have hL := (globalZetaContinued_trivial_residues F ν f).2.comp (tendsto_real_punctured_one)
  change Tendsto (fun r : ℝ => ((r : ℂ) - 1) * globalZetaContinued F ν f χ 0 r)
    (𝓝[>] (1 : ℝ)) (𝓝 ((ν.real univ : ℂ) *
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0)) at hL
  have hR : Tendsto (fun r : ℝ => ((r : ℂ) - 1) * globalZetaContinued F ν f χ 0 r)
      (𝓝[>] (1 : ℝ)) (𝓝 (d * (a * (dedekindZeta_residue F : ℂ)))) := by
    refine ((completedDedekindZeta_right_residue_one F).const_mul d).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hcont r hr, hEuler r hr]
    ring
  have he := tendsto_nhds_unique hL hR
  rw [hzero] at he
  have hc : (ν.real univ : ℂ) = (dedekindZeta_residue F : ℂ) := by
    apply mul_right_cancel₀ (mul_ne_zero hd ha)
    linear_combination he
  exact_mod_cast hc

include μ hν in
private theorem globalCompletedHecke_trivial_residue_pair_of_reference
    (r : GlobalBruhat F) {L : ℂ → ℂ} {B : ℂ} (hB : B ≠ 0)
    (hscale : globalZetaContinued F ν r (compactIdeleClassCharacter F 1) 0 = fun z ↦ B * L z)
    (hm : MeromorphicOn L univ)
    (he : EqOn L (globalCompletedHeckeEuler F 1 S hs hu) {z | 1 < z.re}) :
      let u := (GlobalBruhat.algebraicEquiv F r).val 0
      let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F r)).val 0
      let c := (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ)
      v ≠ 0 ∧
        Tendsto (fun z : ℂ ↦ z * L z) (𝓝[≠] (0 : ℂ)) (𝓝 (-(c * (u / v)))) ∧
        Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 c) := by
  let G := globalZetaContinued F ν r (compactIdeleClassCharacter F 1) 0
  let u := (GlobalBruhat.algebraicEquiv F r).val 0
  let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F r)).val 0
  let c := (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F * (dedekindZeta_residue F : ℂ)
  let m : ℂ := (ν.real univ : ℂ)
  have hscale' (z : ℂ) : G z = B * L z := congrFun hscale z
  have hscaled (z : ℂ) : L z = B⁻¹ * G z := by
    rw [hscale', ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
  obtain ⟨L₀, hm₀, he₀, _, hp⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F 1 S hs hu η ν μ hν
  have horder : meromorphicOrderAt L 1 = (-1 : ℤ) :=
    (meromorphicOrderAt_congr
      (globalCompletedHeckeContinuation_unique_germ F 1 S hs hu hm hm₀ he he₀ 1)).trans
      (hp rfl).2.1
  have h₁ : Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 c) :=
    globalCompletedHecke_trivial_residue_one F S hs hu (hm 1 (mem_univ _)) horder he
  have hres := globalZetaContinued_trivial_residues F ν r
  have he₁ : Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 (B⁻¹ * (m * v))) := by
    apply (hres.2.const_mul B⁻¹).congr'
    refine Eventually.of_forall fun z ↦ ?_
    change B⁻¹ * ((z - 1) * G z) = (z - 1) * L z
    rw [hscaled]
    ring
  have hnorm := tendsto_nhds_unique he₁ h₁
  have hc : c ≠ 0 := mul_ne_zero
    (pow_ne_zero _ (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  have hv : v ≠ 0 := fun hv ↦ hc (by rw [← hnorm, hv, mul_zero, mul_zero])
  refine ⟨hv, ?_, h₁⟩
  have he₀ : -(c * (u / v)) = B⁻¹ * (-(m * u)) := by
    rw [← hnorm]
    field_simp [hv]
  rw [he₀]
  apply (hres.1.const_mul B⁻¹).congr'
  refine Eventually.of_forall fun z ↦ ?_
  change B⁻¹ * (z * G z) = z * L z
  rw [hscaled]
  ring

include μ hν in
/-- The residue at one fixes the scale of the actual adelic Euler reference.
The residue at zero then differs from its negative by the ratio of the
reference test and its Fourier transform evaluated at the origin. -/
theorem exists_globalCompletedHecke_trivial_residue_pair :
    ∃ (r : GlobalBruhat F) (L : ℂ → ℂ), MeromorphicOn L univ ∧
      EqOn L (globalCompletedHeckeEuler F 1 S hs hu) {z | 1 < z.re} ∧
      let u := (GlobalBruhat.algebraicEquiv F r).val 0
      let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F r)).val 0
      let c := (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ)
      v ≠ 0 ∧
        Tendsto (fun z : ℂ ↦ z * L z) (𝓝[≠] (0 : ℂ)) (𝓝 (-(c * (u / v)))) ∧
        Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 c) := by
  obtain ⟨r, L, he, hm, _, _, ⟨B, hB, hscale⟩, _⟩ :=
    exists_globalCompletedHeckeContinuation F 1 S hs hu η ν μ hν
  exact ⟨r, L, hm, he,
    globalCompletedHecke_trivial_residue_pair_of_reference F S hs hu η ν μ hν r hB hscale hm he⟩

include μ hν in
/-- The explicit adelic reference gives the residue pair of the canonical
completed trivial Euler product, with the different in the residue at zero. -/
theorem exists_globalCompletedHecke_trivial_exact_residues :
    ∃ L : ℂ → ℂ, MeromorphicOn L univ ∧
      EqOn L (globalCompletedHeckeEuler F 1 S hs hu) {z | 1 < z.re} ∧
      let d : ℝ := Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
      let c : ℂ := (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ)
      Tendsto (fun z : ℂ ↦ z * L z) (𝓝[≠] (0 : ℂ)) (𝓝 (-((d : ℂ) * c))) ∧
        Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 c) := by
  obtain ⟨r, C, hC, hN, hzero, hfourier⟩ :=
    exists_trivialEuler_reference_origin_ratio F S (fun v ↦ μ v.val)
  have hn : sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
      (sLocalNormOneCharacterOfGlobal F 1 S hs hu) r = fun _ ↦ C := by
    rw [sLocalNormOneCharacterOfGlobal_trivial]
    exact hN
  have hfinite := globalMellin_reference_order_ne_top F η 1 S hs hu μ ν hν r C hC hn 2
  obtain ⟨B, hB, hE⟩ := globalZetaContinued_reference_eq_completedEuler
    F 1 S hs hu η ν μ hν r C hn hfinite
  let G := globalZetaContinued F ν r.val (compactIdeleClassCharacter F 1) 0
  let L (z : ℂ) := B⁻¹ * G z
  have hG := globalZetaContinued_meromorphic F ν r.val (compactIdeleClassCharacter F 1)
    (compactIdeleClassCharacter_unitary F 1) 0
  have hL : MeromorphicOn L univ := fun z hz ↦ (MeromorphicAt.const B⁻¹ z).mul (hG z hz)
  have he : EqOn L (globalCompletedHeckeEuler F 1 S hs hu) {z | 1 < z.re} := fun z hz ↦ by
    change B⁻¹ * G z = _
    rw [show G z = B * globalCompletedHeckeEuler F 1 S hs hu z from hE hz,
      ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
  have hscale : G = fun z ↦ B * L z := by
    funext z
    dsimp only [L]
    rw [← mul_assoc, mul_inv_cancel₀ hB, one_mul]
  obtain ⟨_, h₀, h₁⟩ :=
    globalCompletedHecke_trivial_residue_pair_of_reference F S hs hu η ν μ hν
      r.val hB hscale hL he
  let d := Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
  have hd : (NNReal.sqrt ‖discr F‖₊ : ℝ) = d := by
    change (NNReal.sqrt ‖discr F‖₊ : ℝ) =
      Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs, absNorm_differentIdeal F,
      Nat.cast_natAbs, Int.cast_abs]
  have hd₀ : d ≠ 0 := by
    have hn : (0 : ℝ) < ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ) := by
      rw [absNorm_differentIdeal F]
      exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero F)
    exact (Real.sqrt_pos_of_pos hn).ne'
  let u := GlobalBruhat.evaluation F 0 r.val
  let v := GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F r.val)
  have hv : v = (d : ℂ)⁻¹ * u := by
    change GlobalBruhat.evaluation F 0 (GlobalBruhat.fourier F r.val) = _
    rw [hfourier, ENNReal.toReal_inv, ENNReal.coe_toReal, hd, Complex.ofReal_inv]
  have hu₀ : u ≠ 0 := by
    change GlobalBruhat.evaluation F 0 r.val ≠ 0
    rw [hzero]
    exact pow_ne_zero _ (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hquot : u / v = (d : ℂ) := by
    rw [hv]
    field_simp [hu₀, Complex.ofReal_ne_zero.mpr hd₀]
  refine ⟨L, hL, he, ?_, h₁⟩
  change Tendsto (fun z : ℂ ↦ z * L z) (𝓝[≠] (0 : ℂ))
    (𝓝 (-((d : ℂ) * ((1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
      (dedekindZeta_residue F : ℂ)))))
  change Tendsto (fun z : ℂ ↦ z * L z) (𝓝[≠] (0 : ℂ))
    (𝓝 (-(((1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
      (dedekindZeta_residue F : ℂ)) * (u / v)))) at h₀
  rw [hquot, mul_comm (((1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F *
    (dedekindZeta_residue F : ℂ)))] at h₀
  exact h₀

include μ hν in
/-- The corrected residue pair for the Euler product displayed in the paper.
The volume in (A.3.2.1) is the Dedekind zeta residue. -/
theorem exists_manuscriptTrivialHeckeEuler_exact_residues :
    ∃ L : ℂ → ℂ, MeromorphicOn L univ ∧
      EqOn L (manuscriptTrivialHeckeEuler F) {z | 1 < z.re} ∧
      let d : ℝ := Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
      let c : ℂ := ((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
        (dedekindZeta_residue F : ℂ)
      Tendsto (fun z : ℂ ↦ z * L z) (𝓝[≠] (0 : ℂ)) (𝓝 (-((d : ℂ) * c))) ∧
        Tendsto (fun z : ℂ ↦ (z - 1) * L z) (𝓝[≠] (1 : ℂ)) (𝓝 c) := by
  obtain ⟨S, hS⟩ := exists_homogeneousThetaPlaceBase F (1 : PontryaginDual (K F))
  obtain ⟨hs, hu⟩ := hS S Subset.rfl
  obtain ⟨L, hL, he, h₀, h₁⟩ := exists_globalCompletedHecke_trivial_exact_residues
    F S hs hu η ν μ hν
  let a := (2 : ℂ)⁻¹ ^ InfinitePlace.nrComplexPlaces F
  let Lₚ (z : ℂ) := a * L z
  let c := ((2 * (Real.pi : ℂ))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
    (dedekindZeta_residue F : ℂ)
  let d := Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ)
  let c₁ := (1 / (Real.pi : ℂ)) ^ InfinitePlace.nrComplexPlaces F * (dedekindZeta_residue F : ℂ)
  have hc : a * c₁ = c := by
    simp only [a, c, c₁, one_div]
    rw [← mul_assoc, ← mul_pow, ← mul_inv]
  refine ⟨Lₚ, fun z hz ↦ (MeromorphicAt.const a z).mul (hL z hz), ?_, ?_, ?_⟩
  · intro z hz
    simp only [Lₚ, he hz, manuscriptTrivialHeckeEuler_eq_scaled F S hs hu hz, a]
  · have h := h₀.const_mul a
    change Tendsto (fun z ↦ a * (z * L z)) (𝓝[≠] (0 : ℂ)) (𝓝 (a * (-((d : ℂ) * c₁)))) at h
    rw [show a * (-((d : ℂ) * c₁)) = -((d : ℂ) * c) by rw [← hc]; ring] at h
    apply h.congr'
    exact Eventually.of_forall fun z ↦ by dsimp only [Lₚ]; ring
  · have h := h₁.const_mul a
    change Tendsto (fun z ↦ a * ((z - 1) * L z)) (𝓝[≠] (1 : ℂ)) (𝓝 (a * c₁)) at h
    rw [hc] at h
    apply h.congr'
    exact Eventually.of_forall fun z ↦ by dsimp only [Lₚ]; ring

end

end Masullo
