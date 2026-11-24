import SLocalArchRangeComparison
import SLocalEulerReference
import SchwartzDilationContinuity
import CompactGroupAveraging
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)

private theorem continuous_sLocalArchNormalizedDilation (c : ℂ) (f : Arch F) :
    Continuous (fun t : ℝ ↦ sLocalArchNormalizedDilation F c t f) := by
  let d : ℝ := Module.finrank ℚ F
  let E := mixedEmbedding.mixedSpace F
  let A (t : ℝ) : E ≃L[ℝ] E :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.exp (t / d)) (Real.exp_pos _).ne')
  have hA : Continuous (fun t ↦ (A t).toContinuousLinearMap) := by
    change Continuous (fun t : ℝ ↦ Real.exp (t / d) • ContinuousLinearMap.id ℝ E)
    fun_prop
  have hAi : Continuous (fun t ↦ (A t).symm.toContinuousLinearMap) := by
    change Continuous (fun t : ℝ ↦ (Real.exp (t / d))⁻¹ • ContinuousLinearMap.id ℝ E)
    exact ((Real.continuous_exp.comp (continuous_id.div_const d)).inv₀
      (fun _ ↦ (Real.exp_pos _).ne')).smul continuous_const
  exact (by fun_prop : Continuous (fun t : ℝ ↦ Complex.exp (c * (t : ℂ)))).smul
    (continuous_schwartz_linearPullback A hA hAi f)

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S
private abbrev L (v : S) := v.val.adicCompletion F
private abbrev FiniteTests := locallyConstantTests (∀ v : S, L F S v)

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable

/-- Integrating normalized dilations on a compact interval divides the
difference of the two endpoint multipliers by the spectral displacement.
The finite slice of the actual S-local test is preserved. -/
theorem exists_sLocalArch_dividedExponentialMultiply (ω : PontryaginDual (K F S))
    (c : ℂ) (b : ℝ) (hb : 0 ≤ b) (f : Arch F) (ψ : FiniteTests F S) :
    ∃ g : Arch F, ∀ w : ℂ,
      Z F S μ ω (sLocalBruhatPure F S g ψ) =ᶠ[𝓝[≠] w]
        fun z ↦ ((1 - Complex.exp ((c - z) * (b : ℂ))) / (z - c)) *
            Z F S μ ω (sLocalBruhatPure F S f ψ) z := by
  let I := Icc (0 : ℝ) b
  let ρ : Measure I := volume.comap Subtype.val
  letI : IsFiniteMeasure ρ := ⟨by
    change (volume.comap (Subtype.val : I → ℝ)) univ < ∞
    rw [Measure.comap_apply _ Subtype.val_injective
      (MeasurableEmbedding.subtype_coe (s := I) measurableSet_Icc).measurableSet_image'
      _ MeasurableSet.univ, image_univ, Subtype.range_coe]
    exact isCompact_Icc.measure_lt_top⟩
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompleteSpace (Arch F) := completeSpace_schwartzMap
  let A (t : I) := sLocalArchNormalizedDilation F c t.val f
  have hA : Continuous A := (continuous_sLocalArchNormalizedDilation F c f).comp continuous_subtype_val
  have hAc : HasCompactSupport A :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport A) (subset_univ _)
  obtain ⟨g, hg⟩ := exists_positivePettisIntegral_of_hasCompactSupport ρ hA hAc
  refine ⟨g, fun w ↦ ?_⟩
  let D : Set ℂ := {z | max 0 c.re < z.re}
  let H (z : ℂ) := (1 - Complex.exp ((c - z) * (b : ℂ))) / (z - c)
  have hH : Meromorphic H := fun z ↦
    (analyticAt_const.sub (((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp)).meromorphicAt.div
      (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hD : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hDne : D.Nonempty := ⟨((max 0 c.re + 1 : ℝ) : ℂ), by
    change max 0 c.re < ((max 0 c.re + 1 : ℝ) : ℂ).re
    simp⟩
  refine boundedPoleMellinSpace_unique_germs hD hDne
    (sLocalProductZetaContinued_meromorphic F S μ ω _ _ _)
    (fun z ↦ (hH z).mul (sLocalProductZetaContinued_meromorphic F S μ ω _ _ _ z)) ?_ w
  intro z hz
  have hpos : 0 < z.re := (le_max_left _ _).trans_lt hz
  have hne : z ≠ c := fun h ↦ (lt_irrefl c.re) (h ▸ (le_max_right 0 c.re).trans_lt hz)
  letI : TopologicalSpace (FiniteTests F S) := finestLocallyConvexTopology _
  letI : IsTopologicalAddGroup (FiniteTests F S) := (finest_withSeminorms _).topologicalAddGroup
  let p : Arch F →L[ℂ] E F S :=
    ⟨(sLocalBruhatPure F S).flip ψ, ((continuous_inductiveTensor_lift_iff
      (sLocalBruhatPure F S)).mp (sLocalBruhatPure_lift_continuous F S)).1 ψ⟩
  let ℓ : StrongDual ℂ (Arch F) := (sLocalContinuedMellinEval F S μ ω z).comp p
  have he (t : ℝ) :
      Z F S μ ω (sLocalBruhatPure F S (sLocalArchNormalizedDilation F c t f) ψ) z =
        Complex.exp ((c - z) * (t : ℂ)) * Z F S μ ω (sLocalBruhatPure F S f ψ) z := by
    let f₁ := sLocalBruhatPure F S (sLocalArchNormalizedDilation F c t f) ψ
    let f₂ := sLocalBruhatPure F S f ψ
    have h (x : E F S) : ContinuousAt (Z F S μ ω x) z := by
      have hreg : z ∈ sLocalMellinRegularSet F S ω :=
        (sLocalMellinRegularSet_iff_noEulerPole F S ω z).mpr
          (le_of_not_gt (fun h ↦ sLocalEulerDenominator_ne_zero_of_pos F S ω hpos
            ((sLocalEulerFactor_order_lt_zero_iff F S ω z).mp h)))
      exact ((sLocalProductZetaContinued_continuousOn_regular F S μ ω x).continuousAt
        ((sLocalMellinRegularSet_isOpen F S ω).mem_nhds hreg))
    have hw : ContinuousAt (fun u : ℂ ↦ Complex.exp ((c - u) * (t : ℂ))) z := by
      fun_prop
    exact (((h f₁).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hw.mul (h f₂))).mp
      (sLocalArchNormalizedDilation_germ F S μ ω c t f ψ z)).eq_of_nhds
  change Z F S μ ω (sLocalBruhatPure F S g ψ) z = H z * _
  have hP := (hg ℓ).2
  change Z F S μ ω (sLocalBruhatPure F S g ψ) z = ∫ t : I, ℓ (A t) ∂ρ at hP
  rw [hP]
  change (∫ t : I, ℓ (A t) ∂(volume.comap Subtype.val)) = _
  calc
    _ = ∫ t : I, Complex.exp ((c - z) * (t.val : ℂ)) *
        Z F S μ ω (sLocalBruhatPure F S f ψ) z ∂(volume.comap Subtype.val) := by
      exact integral_congr_ae (.of_forall fun t ↦ he t.val)
    _ = (∫ t in Icc (0 : ℝ) b, Complex.exp ((c - z) * (t : ℂ))) *
        Z F S μ ω (sLocalBruhatPure F S f ψ) z := by
      rw [integral_subtype_comap (s := I) measurableSet_Icc
        (fun t : ℝ ↦ Complex.exp ((c - z) * (t : ℂ)) *
          Z F S μ ω (sLocalBruhatPure F S f ψ) z), integral_mul_const]
    _ = H z * Z F S μ ω (sLocalBruhatPure F S f ψ) z := by
      congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb,
        integral_exp_mul_complex (sub_ne_zero.mpr (Ne.symm hne))]
      dsimp only [H]
      rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ← neg_sub z c, div_neg, ← neg_div, neg_sub]

private theorem exists_sLocalArch_eulerFactorMultiply (ω : PontryaginDual (K F S)) (v : S)
    (c : ℂ) (f : Arch F) (ψ : FiniteTests F S) :
    let P := finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v)
    ∃ g : Arch F, ∀ w : ℂ,
      Z F S μ ω (sLocalBruhatPure F S g ψ) =ᶠ[𝓝[≠] w]
        fun z ↦ (P z / (z - c) ^ (if P c = 0 then 1 else 0 : ℕ)) *
          Z F S μ ω (sLocalBruhatPure F S f ψ) z := by
  let χ := sLocalFiniteZetaPhases F S ω v
  let P := finiteZetaWeilMultiplier F v.val χ
  let b : ℝ := Real.log (v.val.asIdeal.absNorm : ℝ)
  let a : ℂ := (χ (chosenFiniteUniformizer F v.val) : ℂ)
  have hform (hχ : finiteZetaUnramified F v.val χ) (z : ℂ) :
      P z = 1 - a * Complex.exp (-z * (b : ℂ)) := by
    simp only [P, finiteZetaWeilMultiplier, ite_eq_left hχ, finiteZetaRatio, a, b]
  by_cases hχ : finiteZetaUnramified F v.val χ
  · by_cases hc : P c = 0
    · have hb : 0 ≤ b := Real.log_nonneg (by
        exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).le)
      obtain ⟨g, hg⟩ := exists_sLocalArch_dividedExponentialMultiply F S μ ω c b hb f ψ
      refine ⟨g, fun w ↦ ?_⟩
      refine (hg w).trans (.of_forall fun z ↦ ?_)
      have ha : a * Complex.exp (-c * (b : ℂ)) = 1 := by
        rw [hform hχ] at hc
        exact (sub_eq_zero.mp hc).symm
      have he : a * Complex.exp (-z * (b : ℂ)) = Complex.exp ((c - z) * (b : ℂ)) := by
        calc
          _ = (a * Complex.exp (-c * (b : ℂ))) * Complex.exp ((c - z) * (b : ℂ)) := by
            rw [mul_assoc, ← Complex.exp_add]
            congr 2
            ring
          _ = _ := by rw [ha, one_mul]
      change _ = (P z / (z - c) ^ (if P c = 0 then 1 else 0 : ℕ)) * _
      rw [ite_eq_left hc, pow_one, hform hχ, he]
    · let g := sLocalArchNormalizedDilation F 0 b f
      refine ⟨f - a • g, fun w ↦ ?_⟩
      filter_upwards [sLocalArchNormalizedDilation_germ F S μ ω 0 b f ψ w] with z hz
      let ℓ := sLocalContinuedMellinEval F S μ ω z
      let A := (sLocalBruhatPure F S).flip ψ
      change ℓ (A (f - a • g)) = (P z / (z - c) ^ (if P c = 0 then 1 else 0 : ℕ)) * ℓ (A f)
      change ℓ (A g) = Complex.exp ((0 - z) * (b : ℂ)) * ℓ (A f) at hz
      rw [map_sub, map_smul, map_sub, map_smul, smul_eq_mul, hz, hform hχ,
        ite_eq_right hc, pow_zero, div_one, zero_sub]
      ring
  · have hP (z : ℂ) : P z = 1 := by simp [P, finiteZetaWeilMultiplier, hχ]
    refine ⟨f, fun w ↦ .of_forall fun z ↦ ?_⟩
    change _ = (P z / (z - c) ^ (if P c = 0 then 1 else 0 : ℕ)) * _
    simp [hP]

/-- Apply all selected finite denominators without canceling their zeros at the
chosen center. The archimedean test changes within its original Schwartz space. -/
theorem exists_sLocalArch_eulerProductMultiply (ω : PontryaginDual (K F S)) (T : Finset S)
    (c : ℂ) (f : Arch F) (ψ : FiniteTests F S) :
    ∃ g : Arch F, ∀ w : ℂ,
      Z F S μ ω (sLocalBruhatPure F S g ψ) =ᶠ[𝓝[≠] w] fun z ↦
        (sLocalSelectedEulerMultiplier F S ω T z /
          (z - c) ^ sLocalSelectedFinitePoleCount F S ω T c) *
          Z F S μ ω (sLocalBruhatPure F S f ψ) z := by
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨f, fun w ↦ .of_forall fun z ↦ by
        simp [sLocalSelectedEulerMultiplier, sLocalSelectedFinitePoleCount]⟩
  | @insert v T hv ih =>
      obtain ⟨g, hg⟩ := ih
      obtain ⟨g', hg'⟩ := exists_sLocalArch_eulerFactorMultiply F S μ ω v c g ψ
      refine ⟨g', fun w ↦ ?_⟩
      let P := finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F S ω v)
      filter_upwards [hg' w, hg w] with z hz hzg
      change _ = (P z / (z - c) ^ (if P c = 0 then 1 else 0 : ℕ)) * _ at hz
      have hprod : sLocalSelectedEulerMultiplier F S ω (insert v T) z =
          P z * sLocalSelectedEulerMultiplier F S ω T z := by
        simp [sLocalSelectedEulerMultiplier, hv, P]
      have hcount : sLocalSelectedFinitePoleCount F S ω (insert v T) c =
          (if P c = 0 then 1 else 0) + sLocalSelectedFinitePoleCount F S ω T c := by
        classical
        by_cases hp : P c = 0
        · simp [sLocalSelectedFinitePoleCount, P, Finset.filter_insert, hp, hv, Nat.add_comm]
        · simp [sLocalSelectedFinitePoleCount, P, Finset.filter_insert, hp]
      rw [hz, hzg, hprod, hcount, pow_add, ← mul_assoc, div_mul_div_comm]


/-- A test attains the full multiplicity at the specified center and has
only archimedean multiplicities at every other center. -/
theorem exists_sLocalOrbital_fullOrder_archBoundElsewhere (ω : PontryaginDual (K F S)) (c : ℂ) :
    ∃ f : E F S,
      meromorphicOrderAt (Z F S μ ω f) c = (((-(sLocalPoleCount F S ω c : ℤ)) : ℤ) : WithTop ℤ) ∧
      ∀ w ≠ c, meromorphicOrderAt (Z F S μ ω f) w =
        (((-(sLocalArchPoleCount F S ω w : ℤ)) : ℤ) : WithTop ℤ) := by
  obtain ⟨φ, ψ, C, hC, hN⟩ := exists_sLocalEulerNormalizedMellin_pure_constant F S μ ω
  obtain ⟨g, hg⟩ := exists_sLocalArch_eulerProductMultiply F S μ ω Finset.univ c φ ψ
  let x := sLocalBruhatPure F S φ ψ
  let y := sLocalBruhatPure F S g ψ
  let D := sLocalEulerDenominator F S ω
  let P := sLocalSelectedEulerMultiplier F S ω Finset.univ
  let m := sLocalSelectedFinitePoleCount F S ω Finset.univ c
  let Q (z : ℂ) := (z - c) ^ m
  have hcount (w : ℂ) : sLocalSelectedFinitePoleCount F S ω Finset.univ w =
      (sLocalFinitePolesAt F S ω w).card := rfl
  have hmul (w : ℂ) : meromorphicOrderAt (Z F S μ ω y) w =
      meromorphicOrderAt P w - meromorphicOrderAt Q w +
        (((-(sLocalPoleCount F S ω w : ℤ)) : ℤ) : WithTop ℤ) := by
    let n := sLocalPoleCount F S ω w
    have hD : AnalyticAt ℂ D w := sLocalEulerDenominator_analytic F S ω w
    have hX : MeromorphicAt (Z F S μ ω x) w :=
      sLocalProductZetaContinued_meromorphic F S μ ω _ _ x w
    obtain ⟨U, hU, hU₀, he, _⟩ := sLocalEulerDenominator_exists_leadingFactor F S ω w
    have hd : meromorphicOrderAt D w = (n : WithTop ℤ) := by
      rw [hD.meromorphicOrderAt_eq, hD.analyticOrderAt_eq_natCast.mpr ⟨U, hU, hU₀, he⟩,
        ENat.map_natCast]
      rfl
    have hE := meromorphicOrderAt_congr (sLocalEulerNormalizedMellin_eq_germ F S μ ω x w)
    change meromorphicOrderAt (sLocalEulerNormalizedMellin F S μ ω x) w =
      meromorphicOrderAt (D * Z F S μ ω x) w at hE
    rw [hN, meromorphicOrderAt_const, ite_eq_right hC,
      meromorphicOrderAt_mul hD.meromorphicAt hX, hd] at hE
    have hx : meromorphicOrderAt (Z F S μ ω x) w = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
      apply WithTop.add_left_cancel (WithTop.natCast_ne_top n)
      rw [← hE]
      change (0 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) + ((-(n : ℤ) : ℤ) : WithTop ℤ)
      simp only [← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
    have hp : MeromorphicAt P w := by
      change MeromorphicAt (sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω)) w
      exact (sLocalFiniteZetaDenominator_analytic F S _ w (mem_univ _)).meromorphicAt
    have hq : MeromorphicAt Q w := ((analyticAt_id.sub analyticAt_const).pow _).meromorphicAt
    rw [meromorphicOrderAt_congr (hg w)]
    change meromorphicOrderAt ((P / Q) * Z F S μ ω x) w = _
    rw [meromorphicOrderAt_mul (hp.div hq) hX, meromorphicOrderAt_div hp hq, hx]
  refine ⟨y, ?_, fun w hw ↦ ?_⟩
  · have hq : meromorphicOrderAt Q c = (m : WithTop ℤ) :=
      meromorphicOrderAt_pow_id_sub_const (x := c) (n := m)
    rw [hmul, sLocalSelectedEulerMultiplier_order, hq]
    change ((m : ℤ) : WithTop ℤ) - ((m : ℤ) : WithTop ℤ) + _ = _
    simp
  · have hqa : AnalyticAt ℂ Q w := (analyticAt_id.sub analyticAt_const).pow m
    have hq : meromorphicOrderAt Q w = 0 := by
      rw [hqa.meromorphicOrderAt_eq, hqa.analyticOrderAt_eq_zero.mpr
        (pow_ne_zero _ (sub_ne_zero.mpr hw))]
      rfl
    rw [hmul, sLocalSelectedEulerMultiplier_order, hq, sub_zero, hcount]
    let a := sLocalArchPoleCount F S ω w
    let k := (sLocalFinitePolesAt F S ω w).card
    change ((k : ℤ) : WithTop ℤ) + ((-((a + k : ℕ) : ℤ) : ℤ) : WithTop ℤ) =
      ((-(a : ℤ) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add, WithTop.coe_eq_coe]
    push_cast
    omega


attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

private abbrev Isolated (ω : PontryaginDual (K F S)) (c : ℂ) (f : E F S) :=
  ∀ w ≠ c, 0 ≤ meromorphicOrderAt (Z F S μ ω f) w

include hν in
/-- The full Euler pole order can be attained by an actual test whose
continued transform has no poles at any other center. -/
theorem exists_sLocalOrbital_isolated_fullOrder (ω : PontryaginDual (K F S)) (c : ℂ)
    (hc : 0 < sLocalPoleCount F S ω c) :
    ∃ f : E F S, Isolated F S μ ω c f ∧ meromorphicOrderAt (Z F S μ ω f) c =
      (((-(sLocalPoleCount F S ω c : ℤ)) : ℤ) : WithTop ℤ) := by
  obtain ⟨f, hf, hf'⟩ := exists_sLocalOrbital_fullOrder_archBoundElsewhere F S μ ω c
  let a (i : SLocalArchPoleIndex F S ω) :=
    if i.val.1 = c then 0 else sLocalLaurentCoeff F S μ ω i.val.1 i.val.2 f
  obtain ⟨g, hg, h⟩ := exists_sLocalArchFixedFiniteSimultaneousInterpolation F S μ ω
  obtain ⟨φ, hφ⟩ := h a
  let b := sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let q : sLocalArchPolarImage F S ν ω :=
    ⟨M.mkQ b, b, Submodule.subset_span ⟨φ, g, fun v _ ↦ hg v, rfl⟩, rfl⟩
  have hb (w : ℂ) (k : ℕ) (hk : sLocalArchPoleCount F S ω w < k) :
      sLocalLaurentCoeff F S μ ω w k b = 0 :=
    sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω hk q
  refine ⟨f - b, fun w hw ↦ ?_, ?_⟩
  · have hzero : ∀ k > 0, sLocalLaurentCoeff F S μ ω w k (f - b) = 0 := by
      intro k hk
      rw [map_sub]
      by_cases hka : k ≤ sLocalArchPoleCount F S ω w
      · exact sub_eq_zero.mpr (by simpa [a, hw] using (hφ ⟨(w, k), hk, hka⟩).symm)
      · rw [hb w k (lt_of_not_ge hka), sub_zero]
        exact (sLocalLaurentCoeff_vanish_iff F S μ ω w _ f).mpr
          (le_of_eq (hf' w hw).symm) k (lt_of_not_ge hka)
    simpa using (sLocalLaurentCoeff_vanish_iff F S μ ω w 0 (f - b)).mp hzero
  · have hb0 : 0 ≤ meromorphicOrderAt (Z F S μ ω b) c := by
      have hzero : ∀ k > 0, sLocalLaurentCoeff F S μ ω c k b = 0 := by
        intro k hk
        by_cases hka : k ≤ sLocalArchPoleCount F S ω c
        · simpa [a] using hφ ⟨(c, k), hk, hka⟩
        · exact hb c k (lt_of_not_ge hka)
      simpa using (sLocalLaurentCoeff_vanish_iff F S μ ω c 0 b).mp hzero
    have hsub : Z F S μ ω (f - b) = Z F S μ ω f + -(Z F S μ ω b) := by
      funext z
      change (sLocalContinuedMellinEval F S μ ω z) (f - b) =
        (sLocalContinuedMellinEval F S μ ω z) f + -(sLocalContinuedMellinEval F S μ ω z) b
      rw [map_sub, sub_eq_add_neg]
    rw [hsub, ← hf]
    apply meromorphicOrderAt_add_eq_left_of_lt
    · exact (sLocalProductZetaContinued_meromorphic F S μ ω _ _ b c).neg
    · rw [← meromorphicOrderAt_neg, hf]
      refine lt_of_lt_of_le ?_ hb0
      exact WithTop.coe_lt_coe.mpr (by omega)


include hν in
private theorem sLocalOrbital_shiftedDerivative_germ (ω : PontryaginDual (K F S))
    (c : ℂ) (f : E F S) (w : ℂ) :
    Z F S μ ω (c • f + sLocalRadialDerivative F S f) =ᶠ[𝓝[≠] w]
      fun z ↦ (c - z) * Z F S μ ω f z := by
  filter_upwards [sLocalContinuedZeta_iterate_radialDerivative F S μ ν hν ω f 1 w] with z hz
  let A := sLocalContinuedMellinEval F S μ ω z
  change A (sLocalRadialDerivative F S f) = (-z) ^ 1 * A f at hz
  change A (c • f + sLocalRadialDerivative F S f) = (c - z) * A f
  rw [map_add, map_smul, smul_eq_mul, hz, pow_one]
  ring

include hν in
theorem exists_sLocalOrbital_isolated_order (ω : PontryaginDual (K F S)) (c : ℂ)
    (n : ℕ) (hn : n ≤ sLocalPoleCount F S ω c) (hpos : 0 < n) :
    ∃ f : E F S, Isolated F S μ ω c f ∧
      meromorphicOrderAt (Z F S μ ω f) c = (((-(n : ℤ)) : ℤ) : WithTop ℤ) := by
  obtain ⟨f, hf, ho⟩ := exists_sLocalOrbital_isolated_fullOrder F S μ ν hν ω c (hpos.trans_le hn)
  let m := sLocalPoleCount F S ω c
  have hstep (d : ℕ) : ∃ g : E F S, Isolated F S μ ω c g ∧
      meromorphicOrderAt (Z F S μ ω g) c = (((d : ℤ) - m : ℤ) : WithTop ℤ) := by
    induction d with
    | zero =>
      exact ⟨f, hf, by simpa [m] using ho⟩
    | succ d ih =>
      obtain ⟨g, hg, he⟩ := ih
      let p := c • g + sLocalRadialDerivative F S g
      have hG : Meromorphic (Z F S μ ω g) :=
        sLocalProductZetaContinued_meromorphic F S μ ω _ _ g
      have hA (w : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ c - z) w :=
        analyticAt_const.sub analyticAt_id
      refine ⟨p, fun w hw ↦ ?_, ?_⟩
      · rw [meromorphicOrderAt_congr (sLocalOrbital_shiftedDerivative_germ F S μ ν hν ω c g w)]
        change 0 ≤ meromorphicOrderAt ((fun z : ℂ ↦ c - z) * Z F S μ ω g) w
        rw [meromorphicOrderAt_mul (hA w).meromorphicAt (hG w)]
        exact add_nonneg (hA w).meromorphicOrderAt_nonneg (hg w hw)
      · have hP : meromorphicOrderAt (fun z : ℂ ↦ c - z) c = 1 := by
          rw [show (fun z : ℂ ↦ c - z) = -(fun z : ℂ ↦ z - c) by
            funext z
            exact (neg_sub z c).symm, ← meromorphicOrderAt_neg]
          exact meromorphicOrderAt_id_sub_const (𝕜 := ℂ) (x := c)
        rw [meromorphicOrderAt_congr (sLocalOrbital_shiftedDerivative_germ F S μ ν hν ω c g c)]
        change meromorphicOrderAt ((fun z : ℂ ↦ c - z) * Z F S μ ω g) c = _
        rw [meromorphicOrderAt_mul (hA c).meromorphicAt (hG c), hP, he]
        change ((1 : ℤ) : WithTop ℤ) + (((d : ℤ) - m : ℤ) : WithTop ℤ) = _
        rw [← WithTop.coe_add, WithTop.coe_eq_coe]
        push_cast
        omega
  obtain ⟨g, hg, he⟩ := hstep (m - n)
  have hnm : n ≤ m := hn
  refine ⟨g, hg, he.trans ?_⟩
  congr 1
  omega


include hν in
/-- Every finite Laurent block at one center is realized exactly, with
every other principal part zero. -/
theorem exists_sLocalOrbital_singleBlock (ω : PontryaginDual (K F S)) (c : ℂ)
    (n : ℕ) (hn : n ≤ sLocalPoleCount F S ω c) (a : ℕ → ℂ) :
    ∃ f : E F S, ∀ (w : ℂ) (k : ℕ), 0 < k →
      sLocalLaurentCoeff F S μ ω w k f = if w = c ∧ k ≤ n then a k else 0 := by
  induction n generalizing a with
  | zero =>
    exact ⟨0, fun w k hk ↦ by simp [Nat.not_le_of_lt hk]⟩
  | succ n ih =>
    obtain ⟨u, hu, ho⟩ := exists_sLocalOrbital_isolated_order F S μ ν hν ω c (n+1) hn
      (Nat.succ_pos n)
    let B (w : ℂ) (k : ℕ) := sLocalLaurentCoeff F S μ ω w k
    let β := B c (n+1) u
    have hβ : β ≠ 0 := sLocalLaurentCoeff_ne_zero_of_exact_order F S μ ω u c (n+1)
      (Nat.succ_pos n) ho
    let b := a (n+1) / β
    obtain ⟨g, hg⟩ := ih (Nat.le_trans (Nat.le_succ _) hn) (fun k ↦ a k - b * B c k u)
    refine ⟨g + b • u, fun w k hk ↦ ?_⟩
    change B w k (g + b • u) = _
    rw [map_add, map_smul, smul_eq_mul]
    have hgk : B w k g = if w = c ∧ k ≤ n then a k - b * B c k u else 0 := hg w k hk
    rw [hgk]
    by_cases hw : w = c
    · subst w
      by_cases hkn : k ≤ n
      · simp [hkn, Nat.le_succ_of_le hkn]
      · by_cases he : k = n+1
        · subst k
          simp only [true_and, Nat.not_succ_le_self, ite_false, le_refl, ite_true, zero_add]
          exact div_mul_cancel₀ _ hβ
        · have hlt : n+1 < k := by omega
          have hzu : B c k u = 0 :=
            (sLocalLaurentCoeff_vanish_iff F S μ ω c (n+1) u).mpr (le_of_eq ho.symm) k hlt
          simp [hkn, Nat.not_le_of_lt hlt, hzu]
    · have hzu : B w k u = 0 := (sLocalLaurentCoeff_vanish_iff F S μ ω w 0 u).mpr
        (by simpa using hu w hw) k hk
      simp [hw, hzu]


/-- The finite band of Laurent coefficients removed by selected finite
principal values. -/
def SLocalOrbitalIndex (ω : PontryaginDual (K F S)) (W : Finset S) :=
  {i : ℂ × ℕ // sLocalPoleCount F S ω i.1 - sLocalSelectedFinitePoleCount F S ω W i.1 < i.2 ∧
    i.2 ≤ sLocalPoleCount F S ω i.1}

include hν in
/-- Corrected Theorem 7.3.1.2. The selection is finite-place, as in the
definition of the principal-value operator. The band starts just above
the remaining, rather than the removed, pole order. -/
theorem sLocalOrbitalPrincipalValues_biorthogonal (ω : PontryaginDual (K F S)) (W : Finset S) :
    let H := SLocalHomogeneousThetaQuotient F S ν ω
    let M := sLocalHomogeneousThetaKernel F S ν ω
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let I := SLocalOrbitalIndex F S ω W
    let A (i : I) := sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2
    IsClosed (R : Set H) ∧
      (∀ q : H, q ∈ R ↔ ∀ i, A i q = 0) ∧
      closure (Submodule.span ℂ (range A) : Set (StrongDual ℂ H)) =
        {ℓ | ∀ q ∈ R, ℓ q = 0} ∧
      ∃ u : I → H ⧸ R,
        (∀ i j (q : H), R.mkQ q = u j → A i q = if i = j then 1 else 0) ∧
        ∀ (a b : I → ℂ) (ℓ : StrongDual ℂ H),
          HasSum (fun i ↦ a i • A i) ℓ → HasSum (fun i ↦ b i • A i) ℓ → a = b := by
  let H := SLocalHomogeneousThetaQuotient F S ν ω
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let I := SLocalOrbitalIndex F S ω W
  let d := sLocalPoleCount F S ω
  let m (c : ℂ) := d c - sLocalSelectedFinitePoleCount F S ω W c
  let A (i : I) := sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2
  let B (i : {i : ℂ × ℕ // m i.1 < i.2}) := sLocalThetaLaurentCoeff F S μ ν hν ω i.val.1 i.val.2
  have hR : R = sLocalThetaPoleBound F S μ ν hν ω m :=
    sLocalFiniteNonzeroTestSubspace_map_eq_selected_poleBound F S μ ν hν ω W
  have hK : ∀ q : H, q ∈ R ↔ ∀ i, A i q = 0 := by
    intro q
    rw [hR, ← sLocalThetaRemovedLaurentCoefficients_ker F S μ ν hν ω m]
    change (sLocalThetaRemovedLaurentCoefficients F S μ ν hν ω m q = 0) ↔ _
    exact ⟨fun h i ↦ congrFun h i, fun h ↦ funext h⟩
  have hspan : Submodule.span ℂ (range A) = Submodule.span ℂ (range B) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨⟨i.val, i.property.1⟩, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i.val.2 ≤ d i.val.1
      · exact Submodule.subset_span ⟨⟨i.val, i.property, hi⟩, rfl⟩
      · have hz : B i = 0 := by
          apply ContinuousLinearMap.ext
          intro q
          obtain ⟨f, rfl⟩ := M.mkQ_surjective q
          change sLocalLaurentCoeff F S μ ω i.val.1 i.val.2 f = 0
          have hbound := sLocalZeta_poleOrder_le_euler F S μ ω f i.val.1
          rw [sLocalEulerFactor_order F S ω i.val.1, sLocalAllowedPoleOrder_eq_count F S ω i.val.1] at hbound
          exact (sLocalLaurentCoeff_vanish_iff F S μ ω i.val.1 (d i.val.1) f).mpr hbound
            i.val.2 (lt_of_not_ge hi)
        rw [hz]
        exact Submodule.zero_mem _
  have hcl : closure (Submodule.span ℂ (range A) : Set (StrongDual ℂ H)) =
      {ℓ | ∀ q ∈ R, ℓ q = 0} := by
    rw [hspan, hR]
    exact sLocalThetaPoleBound_strongClosure F S μ ν hν ω m
  have hwitness (j : I) : ∃ f : E F S, ∀ i : I,
      A i (M.mkQ f) = if i = j then 1 else 0 := by
    obtain ⟨f, hf⟩ := exists_sLocalOrbital_singleBlock F S μ ν hν ω j.val.1 (d j.val.1)
      le_rfl (fun k ↦ if k = j.val.2 then 1 else 0)
    refine ⟨f, fun i ↦ ?_⟩
    change sLocalLaurentCoeff F S μ ω i.val.1 i.val.2 f = _
    rw [hf i.val.1 i.val.2 (Nat.zero_le _ |>.trans_lt i.property.1)]
    by_cases h : i = j
    · subst i
      have hle : j.val.2 ≤ d j.val.1 := j.property.2
      simp [hle]
    · have he : ¬ (i.val.1 = j.val.1 ∧ i.val.2 = j.val.2) :=
        fun h' ↦ h (Subtype.ext (Prod.ext h'.1 h'.2))
      by_cases hc : i.val.1 = j.val.1
      · have hk : i.val.2 ≠ j.val.2 := fun he' ↦ he ⟨hc, he'⟩
        simp [hk, h]
      · simp [hc, h]
  choose f hf using hwitness
  let u (j : I) := R.mkQ (M.mkQ (f j))
  have hu (i j : I) (q : H) (hq : R.mkQ q = u j) : A i q = if i = j then 1 else 0 := by
    have hmem : q - M.mkQ (f j) ∈ R := (Submodule.Quotient.eq R).mp hq
    have hz := (hK _).mp hmem i
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans (hf j i)
  refine ⟨sLocalFiniteNonzeroTestSubspace_map_isClosed F S μ ν hν ω W, hK, hcl, u, hu, ?_⟩
  intro a b ℓ ha hb
  funext j
  let x := M.mkQ (f j)
  let ev : StrongDual ℂ H →L[ℂ] ℂ :=
    ⟨{ toFun := fun L ↦ L x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl },
      continuous_eval_const x⟩
  have evalSum (v : I → ℂ) (hv : HasSum (fun i ↦ v i • A i) ℓ) : v j = ev ℓ := by
    have h' : HasSum (fun i ↦ ev (v i • A i)) (ev ℓ) := hv.map ev ev.continuous
    have he (i : I) : ev (v i • A i) = if i = j then v j else 0 := by
      change v i * A i (M.mkQ (f j)) = _
      rw [hf j i]
      by_cases hi : i = j
      · simp [hi]
      · simp [hi]
    simp only [he] at h'
    exact (hasSum_ite_eq j (v j)).unique h'
  exact (evalSum a ha).trans (evalSum b hb).symm


end

end Masullo
