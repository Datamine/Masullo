import SLocalRadialLift
import SLocalZetaVerticalSchwartz
import SLocalMeromorphicKernels
import SLocalFlatTestMellin

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev Q := SIdeleQuotient F S
private abbrev U := (SAdeles F S)ˣ
private abbrev E := sLocalBruhatImage F S
private abbrev P := sLocalPolarFreeTestSubspace F S
private abbrev L (v : S) := v.val.adicCompletion F

/-- The canonical norm section in the logarithmic coordinate, on S-idele classes. -/
def sLocalLogNormRay (t : ℝ) : Q F S :=
  QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))

private theorem split_apply (t : ℝ) (k : K F S) :
    sLocalZetaSplit F S (t, k) = sLocalLogNormRay F S t * k.val := rfl

private theorem ray_zero : sLocalLogNormRay F S 0 = 1 := by
  change QuotientGroup.mk' (sUnitImage F S) (sLocalExpSection F S 1) = 1
  rw [map_one, map_one]

private theorem weight_ne_zero (ω : PontryaginDual (K F S)) (z : ℂ) (q : Q F S) :
    sLocalZetaWeight F S ω z q ≠ 0 := by
  unfold sLocalZetaWeight
  exact mul_ne_zero (Complex.exp_ne_zero _) (Circle.coe_ne_zero _)

private def weightCharacter (ω : PontryaginDual (K F S)) (z : ℂ) : Q F S →ₜ* ℂˣ where
  toFun q := Units.mk0 (sLocalZetaWeight F S ω z q) (weight_ne_zero F S ω z q)
  map_one' := by
    apply Units.ext
    change sLocalZetaWeight F S ω z 1 = 1
    have h : sLocalZetaSplit F S (0, 1) = 1 := by
      rw [split_apply, ray_zero]
      exact one_mul (1 : Q F S)
    rw [← h, sLocalZetaWeight_split, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      map_one, Circle.coe_one, mul_one]
  map_mul' q r := Units.ext (sLocalZetaWeight_mul F S ω z q r)
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr (sLocalZetaWeight_continuous F S ω z)

/-- Extend a character of the norm-one group so that it is trivial on the
canonical logarithmic norm section. -/
def sLocalNormOnePhase (ω : PontryaginDual (K F S)) : Q F S →ₜ* ℂˣ :=
  weightCharacter F S ω 0

@[simp] theorem sLocalNormOnePhase_normOne (ω : PontryaginDual (K F S)) (k : K F S) :
    (sLocalNormOnePhase F S ω k.val : ℂ) = (ω k : ℂ) := by
  have he : sLocalZetaSplit F S (0, k) = k.val := by
    rw [split_apply, ray_zero]
    exact one_mul (k.val : Q F S)
  change sLocalZetaWeight F S ω 0 k.val = _
  rw [← he, sLocalZetaWeight_split, zero_mul, Complex.exp_zero, one_mul]

private theorem sLocalNormOnePhase_ray (ω : PontryaginDual (K F S)) (t : ℝ) :
    (sLocalNormOnePhase F S ω (sLocalLogNormRay F S t) : ℂ) = 1 := by
  have he : sLocalZetaSplit F S (t, 1) = sLocalLogNormRay F S t := by rw [split_apply]; exact mul_one _
  change sLocalZetaWeight F S ω 0 (sLocalLogNormRay F S t) = 1
  rw [← he, sLocalZetaWeight_split, zero_mul, Complex.exp_zero, map_one, Circle.coe_one, mul_one]

private theorem sLocalTheta_twist (χ : Q F S →ₜ* ℂˣ) (f g : E F S)
    (h : ∀ u : U F S, sLocalBruhatRestriction F S g.val u.val =
      (χ (QuotientGroup.mk u) : ℂ) * sLocalBruhatRestriction F S f.val u.val)
    (q : Q F S) :
    sLocalTheta F S (sLocalBruhatRestriction F S g.val) q =
      (χ q : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f.val) q := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [sLocalTheta_mk, sLocalThetaOnIdeles, ← tsum_mul_left]
  apply tsum_congr
  intro v
  let a := sUnitOrbitEquiv F S v
  rw [← sUnitOrbitEquiv_val F S v]
  change sLocalBruhatRestriction F S g.val (a.val * u).val = _
  have ha : (QuotientGroup.mk a.val : Q F S) = 1 := (QuotientGroup.eq_one_iff _).mpr a.property
  rw [h, QuotientGroup.mk_mul, ha]
  rw [one_mul (QuotientGroup.mk u : Q F S)]
  rfl

section Profiles

variable [MeasurableSpace (K F S)] [BorelSpace (K F S)]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

omit [BorelSpace (K F S)] [ν.IsHaarMeasure] in
private theorem sLocalHomogeneousTheta_inversePhase (ω : PontryaginDual (K F S))
    (f g : E F S) (h : ∀ u : U F S, sLocalBruhatRestriction F S g.val u.val =
      ((sLocalNormOnePhase F S ω)⁻¹ (QuotientGroup.mk u) : ℂ) * sLocalBruhatRestriction F S f.val u.val)
    (q : Q F S) :
    sLocalHomogeneousTheta F S ν ω g.val q =
      ((sLocalNormOnePhase F S ω q : ℂ)⁻¹) * sLocalHomogeneousTheta F S ν 1 f.val q := by
  let c := sLocalNormOnePhase F S ω
  unfold sLocalHomogeneousTheta
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun k ↦ by
    change (ω k : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S g.val)
      (k.val * q) = (c q : ℂ)⁻¹ * (1 * sLocalTheta F S (sLocalBruhatRestriction F S f.val) (k.val * q))
    rw [sLocalTheta_twist F S c⁻¹ f g h]
    have he : ((c⁻¹ (k.val * q) : ℂˣ) : ℂ) =
        (ω k : ℂ)⁻¹ * (c q : ℂ)⁻¹ := by
      rw [map_mul]
      change ((c k.val : ℂˣ)⁻¹ : ℂ) * ((c q : ℂˣ)⁻¹ : ℂ) = _
      exact congrArg (fun z : ℂ ↦ z⁻¹ * (c q : ℂ)⁻¹) (sLocalNormOnePhase_normOne F S ω k)
    rw [he]
    change (ω k : ℂ) * (((ω k : ℂ)⁻¹ * (c q : ℂ)⁻¹) * _) = (c q : ℂ)⁻¹ * (1 * _)
    rw [one_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero (ω k)), one_mul]

/-- The realization of all-exponent radial profiles extends to any
prescribed unitary component, with the correct norm-one covariance. -/
theorem exists_sLocalHomogeneousTheta_polarFreeCLM_fixedSupport (ω : PontryaginDual (K F S)) :
    ∃ L : PositiveRealExponentialDecay univ →L[ℂ] P F S,
      (∀ φ (t : ℝ), sLocalHomogeneousTheta F S ν ω (L φ).val.val (sLocalLogNormRay F S t) = φ.val t) ∧
      ∀ a b : ℝ, ∃ C : Set (SAdeles F S), IsCompact C ∧
        ∀ f, support f.val ⊆ Icc a b →
          tsupport (sLocalBruhatRestriction F S (L f).val.val) ⊆ C := by
  obtain ⟨L, hL, hSupport, _⟩ := exists_sLocalHomogeneousTheta_trivial_polarFreeCLM_fixedSupport F S ν
  let χ := (sLocalNormOnePhase F S ω)⁻¹
  obtain ⟨M, hM⟩ := exists_sLocalPolarFree_zeroExtendedClassQuasiCharacter_mulEquiv F S χ
  refine ⟨M.toContinuousLinearMap.comp L, fun φ t ↦ ?_, fun a b ↦ ?_⟩
  · let f := L φ
    have hPhase (u : U F S) : sLocalBruhatRestriction F S (M f).val.val u.val =
        (χ (QuotientGroup.mk u) : ℂ) * sLocalBruhatRestriction F S f.val.val u.val := by
      rw [hM, dite_eq_left u.isUnit]
      have hu : u.isUnit.unit = u := Units.ext u.isUnit.unit_spec
      rw [hu]
    change sLocalHomogeneousTheta F S ν ω (M f).val.val (sLocalLogNormRay F S t) = _
    rw [sLocalHomogeneousTheta_inversePhase F S ν ω f.val (M f).val hPhase,
      sLocalNormOnePhase_ray, inv_one, one_mul, hL]
    change φ.val (Real.log (sLocalIdeleNorm F S (sLocalExpSection F S (Multiplicative.ofAdd t)))) = _
    rw [sLocalIdeleNorm_expSection, Real.log_exp]
  · obtain ⟨C, hC, hLC⟩ := hSupport a b
    refine ⟨C, hC, fun f hf ↦ ?_⟩
    apply Subset.trans (closure_mono ?_) (hLC f hf)
    intro x hx
    change sLocalBruhatRestriction F S (M (L f)).val.val x ≠ 0 at hx
    rw [hM] at hx
    by_cases h : IsUnit x
    · rw [dite_eq_left h, mul_ne_zero_iff] at hx
      exact hx.2
    · rw [dite_eq_right h] at hx
      exact (hx rfl).elim

theorem exists_sLocalHomogeneousTheta_polarFreeCLM (ω : PontryaginDual (K F S)) :
    ∃ L : PositiveRealExponentialDecay univ →L[ℂ] P F S,
      ∀ φ (t : ℝ), sLocalHomogeneousTheta F S ν ω (L φ).val.val (sLocalLogNormRay F S t) = φ.val t := by
  obtain ⟨L, hL, _⟩ := exists_sLocalHomogeneousTheta_polarFreeCLM_fixedSupport F S ν ω
  exact ⟨L, hL⟩

theorem exists_sLocalHomogeneousTheta_polarFree_of_profile (ω : PontryaginDual (K F S))
    (φ : PositiveRealExponentialDecay univ) :
    ∃ g : P F S, ∀ t : ℝ, sLocalHomogeneousTheta F S ν ω g.val.val (sLocalLogNormRay F S t) = φ.val t := by
  obtain ⟨L, hL⟩ := exists_sLocalHomogeneousTheta_polarFreeCLM F S ν ω
  exact ⟨L φ, hL φ⟩

/-- The all-exponent decay condition gives an actual flat representative
in the same homogeneous theta class. -/
theorem exists_sLocalPolarFree_of_logProfile_mem (ω : PontryaginDual (K F S)) (f : E F S)
    (hf : (fun t : ℝ ↦ sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t)) ∈
      logExponentialDecaySubmodule univ) :
    ∃ g : P F S, sLocalHomogeneousTheta F S ν ω f.val =
      sLocalHomogeneousTheta F S ν ω g.val.val := by
  let φ : PositiveRealExponentialDecay univ := ⟨_, hf⟩
  obtain ⟨g, hg⟩ := exists_sLocalHomogeneousTheta_polarFree_of_profile F S ν ω φ
  refine ⟨g, funext fun q ↦ ?_⟩
  obtain ⟨⟨t, k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
  rw [split_apply, show sLocalLogNormRay F S t * k.val = k.val * sLocalLogNormRay F S t from mul_comm (sLocalLogNormRay F S t) (k.val : Q F S),
    sLocalHomogeneousTheta_translate, sLocalHomogeneousTheta_translate, hg]

omit [MeasurableSpace (K F S)] [BorelSpace (K F S)] in
private theorem normWeight_split (z : ℂ) (t : ℝ) (k : K F S) :
    (weightCharacter F S 1 z (k.val * sLocalLogNormRay F S t) : ℂ) = Complex.exp (z * t) := by
  change sLocalZetaWeight F S 1 z (k.val * sLocalLogNormRay F S t) = _
  rw [mul_comm (k.val : Q F S) (sLocalLogNormRay F S t), ← split_apply, sLocalZetaWeight_split]
  change Complex.exp (z * (t : ℂ)) * 1 = _
  exact mul_one _

omit [BorelSpace (K F S)] [ν.IsHaarMeasure] in
private theorem sLocalHomogeneousTheta_normWeight (ω : PontryaginDual (K F S))
    (z : ℂ) (f g : E F S) (h : ∀ u : U F S, sLocalBruhatRestriction F S g.val u.val =
      (weightCharacter F S 1 z (QuotientGroup.mk u) : ℂ) * sLocalBruhatRestriction F S f.val u.val)
    (t : ℝ) :
    sLocalHomogeneousTheta F S ν ω g.val (sLocalLogNormRay F S t) =
      Complex.exp (z * t) * sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t) := by
  unfold sLocalHomogeneousTheta
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun k ↦ by
    change (ω k : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S g.val) (k.val * sLocalLogNormRay F S t) =
      Complex.exp (z * t) * ((ω k : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f.val)
        (k.val * sLocalLogNormRay F S t))
    rw [sLocalTheta_twist F S (weightCharacter F S 1 z) f g h, normWeight_split F S,
      mul_left_comm]

/-- Flat tests have all-exponent logarithmic Schwartz decay on every
unitary component. -/
theorem sLocalPolarFree_logProfile_mem (ω : PontryaginDual (K F S)) (f : P F S) :
    (fun t : ℝ ↦ sLocalHomogeneousTheta F S ν ω f.val.val (sLocalLogNormRay F S t)) ∈
      logExponentialDecaySubmodule univ := by
  apply (Submodule.mem_iInf _).2
  intro a
  let z : ℂ := ((a : ℝ) - 1 : ℝ)
  obtain ⟨M, hM⟩ := exists_sLocalPolarFree_classQuasiCharacter_mulEquiv F S (weightCharacter F S 1 z)
  obtain ⟨g, hg⟩ := exists_sLocalRadialSchwartz F S ν ω (M f).val 1 zero_lt_one
  refine ⟨g, funext fun t ↦ ?_⟩
  change g t = (Real.exp ((a : ℝ) * t) : ℂ) *
    sLocalHomogeneousTheta F S ν ω f.val.val (sLocalLogNormRay F S t)
  have hgt : g t = Complex.exp ((1 : ℝ) * (t : ℂ)) *
      sLocalHomogeneousTheta F S ν ω (M f).val.val (sLocalLogNormRay F S t) := hg t
  rw [hgt, sLocalHomogeneousTheta_normWeight F S ν ω z f.val (M f).val (hM f) t, ← mul_assoc,
    ← Complex.exp_add, Complex.ofReal_exp]
  congr 2
  push_cast [z]
  ring

end Profiles

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hν : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)) Measure.count
    (sLocalClassHaar F S ν))

include hν in
private theorem homogeneousTheta_eq_iff_meromorphicZeta_eq (ω : PontryaginDual (K F S)) (f g : E F S) :
    sLocalHomogeneousTheta F S ν ω f.val = sLocalHomogeneousTheta F S ν ω g.val ↔
      sLocalMeromorphicZetaComponent F S μ ω f = sLocalMeromorphicZetaComponent F S μ ω g := by
  rw [← sub_eq_zero (a := sLocalMeromorphicZetaComponent F S μ ω f), ← map_sub,
    ← sLocalHomogeneousTheta_zero_iff_meromorphicZeta F S μ ν hν]
  -- Show that averaging the difference gives the difference of the averages.
  have h (q : Q F S) : sLocalHomogeneousTheta F S ν ω (f - g).val q =
      sLocalHomogeneousTheta F S ν ω f.val q - sLocalHomogeneousTheta F S ν ω g.val q := by
    unfold sLocalHomogeneousTheta
    rw [← integral_sub (sLocalHomogeneousTheta_integrable F S ν ω f.val q)
      (sLocalHomogeneousTheta_integrable F S ν ω g.val q)]
    apply integral_congr_ae
    exact .of_forall fun k ↦ by
      let u := (k.val * q).out
      have he (v : E F S) : sLocalTheta F S (sLocalBruhatRestriction F S v.val) (k.val * q) =
          sLocalThetaEval F S u v.val := by
        conv_lhs => rw [← Quotient.out_eq' (k.val * q), sLocalTheta_mk]
        rfl
      change (ω k : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S (f - g).val) (k.val * q) =
        (ω k : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S f.val) (k.val * q) -
          (ω k : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S g.val) (k.val * q)
      rw [he, he, he, Submodule.coe_sub, map_sub, mul_sub]
  simp only [h, sub_eq_zero, funext_iff]

include hν in
/-- Proposition 5.3.4.4, equivalence of (2) and (3). A flat test represents
the continued Mellin component precisely when its logarithmic theta
profile has Schwartz decay at every real exponential weight. -/
theorem sLocal_exists_polarFree_meromorphicZeta_iff_logProfile_mem
    (ω : PontryaginDual (K F S)) (f : E F S) :
    (∃ g : P F S, sLocalMeromorphicZetaComponent F S μ ω f =
      sLocalMeromorphicZetaComponent F S μ ω g.val) ↔
    (fun t : ℝ ↦ sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t)) ∈
      logExponentialDecaySubmodule univ := by
  constructor
  · rintro ⟨g, hg⟩
    rw [(homogeneousTheta_eq_iff_meromorphicZeta_eq F S μ ν hν ω f g.val).2 hg]
    exact sLocalPolarFree_logProfile_mem F S ν ω g
  · intro hf
    obtain ⟨g, hg⟩ := exists_sLocalPolarFree_of_logProfile_mem F S ν ω f hf
    exact ⟨g, (homogeneousTheta_eq_iff_meromorphicZeta_eq F S μ ν hν ω f g.val).1 hg⟩

private abbrev continued (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Proposition 5.3.4.4, (2) implies (1), with equality in the space of
meromorphic functions. -/
theorem sLocal_entire_of_meromorphicZeta_eq_polarFree (ω : PontryaginDual (K F S)) (f : E F S)
    (hf : ∃ g : P F S, sLocalMeromorphicZetaComponent F S μ ω f =
      sLocalMeromorphicZetaComponent F S μ ω g.val) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (continued F S μ ω f) univ) univ := by
  obtain ⟨g, hg⟩ := hf
  apply sLocalProductZeta_entire_of_flat_representative F S μ ω f
  refine ⟨g.val, g.property, ?_⟩
  change zeroMeromorphicGerms.mkQ ⟨continued F S μ ω f,
    sLocalProductZetaContinued_meromorphic F S μ ω _ _ f⟩ =
    zeroMeromorphicGerms.mkQ ⟨continued F S μ ω g.val,
      sLocalProductZetaContinued_meromorphic F S μ ω _ _ g.val⟩ at hg
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hg
  change ∀ c : ℂ, (fun z ↦ continued F S μ ω f z - continued F S μ ω g.val z)
    =ᶠ[𝓝[≠] c] 0 at hg
  intro c
  filter_upwards [hg c] with z hz
  exact sub_eq_zero.mp hz

private theorem mellin_logProfile (φ : ℝ → ℂ) (z : ℂ) :
    mellin (fun t ↦ φ (Real.log t)) z = ∫ t : ℝ, Complex.exp (z * (t : ℂ)) * φ t := by
  unfold mellin
  rw [← Real.range_exp, ← image_univ, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn, Measure.restrict_univ]
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  simp only [Real.log_exp, abs_of_pos (Real.exp_pos t), Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add]
  norm_cast
  congr 2
  ring

include hν in
/-- Every whole-plane Schwartz–Bergman transform is realized on the
positive half-plane by a flat test in the prescribed S-local component. -/
theorem exists_sLocalPolarFree_zeta_eq_schwartzBergmanCLM (ω : PontryaginDual (K F S)) :
    ∃ L : SchwartzBergman (univ : Set ℝ) →L[ℂ] P F S, ∀ G, EqOn
      (sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
        (sLocalComplexArchParameters F S ω) (L G).val) G.val {z | 0 < z.re} := by
  let e := positiveRealFourierMellin (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
  obtain ⟨L, hL⟩ := exists_sLocalHomogeneousTheta_polarFreeCLM F S ν ω
  refine ⟨L.comp e.symm.toContinuousLinearMap, fun G z hz ↦ ?_⟩
  let φ := e.symm G
  let f := L φ
  change sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f.val z = G.val z
  have hz' : 0 < z.re := hz
  have he := (sLocalContinuedZeta_eq_theta F S μ ν hν ω f.val hz').trans
    (sLocalThetaZeta_integrable_eq_radial F S ν ω f.val z hz').2
  change sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f.val z = _ at he
  rw [he, sLocalRadialMellin]
  have hm : G.val z = mellin (fun t ↦ φ.val (Real.log t)) z := by
    rw [← show e φ = G from e.apply_symm_apply G]
    exact positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty φ z
      (mem_univ _)
  rw [hm, mellin_logProfile]
  exact integral_congr_ae (.of_forall fun t ↦ congrArg (Complex.exp (z * (t : ℂ)) * ·) (hL φ t))

include hν in
theorem exists_sLocalPolarFree_zeta_eq_schwartzBergman
    (ω : PontryaginDual (K F S)) (G : SchwartzBergman (univ : Set ℝ)) :
    ∃ f : P F S, EqOn
      (sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
        (sLocalComplexArchParameters F S ω) f.val) G.val {z | 0 < z.re} := by
  obtain ⟨L, hL⟩ := exists_sLocalPolarFree_zeta_eq_schwartzBergmanCLM F S μ ν hν ω
  exact ⟨L G, hL G⟩

include hν in
/-- If the continuation lies in the whole-plane Schwartz–Bergman space,
the actual logarithmic theta profile has all-exponent decay. -/
theorem sLocal_logProfile_mem_of_schwartzBergman
    (ω : PontryaginDual (K F S)) (f : E F S)
    (G : SchwartzBergman (univ : Set ℝ))
    (hG : EqOn G.val
      (sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
        (sLocalComplexArchParameters F S ω) f) {z | 0 < z.re}) :
    (fun t : ℝ ↦ sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t)) ∈
      logExponentialDecaySubmodule univ := by
  let I := Ioi (0 : ℝ)
  let e := positiveRealFourierMellin (univ : Set ℝ) isOpen_univ
    ordConnected_univ univ_nonempty
  let φ := e.symm G
  let Θ (t : ℝ) := sLocalHomogeneousTheta F S ν ω f.val (sLocalLogNormRay F S t)
  have hΘ : Θ ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).2
    intro a
    obtain ⟨u, hu⟩ := exists_sLocalRadialSchwartz F S ν ω f a a.property
    refine ⟨u, funext fun t ↦ ?_⟩
    change u t = (Real.exp ((a : ℝ) * t) : ℂ) * Θ t
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
    exact hu t
  have hφ : φ.val ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).2
    intro a
    exact (Submodule.mem_iInf _).mp φ.property ⟨a.val, mem_univ _⟩
  let eI := positiveRealFourierMellin I isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  have he : (⟨Θ, hΘ⟩ : PositiveRealExponentialDecay I) = ⟨φ.val, hφ⟩ := by
    apply eI.injective
    apply Subtype.ext
    funext z
    by_cases hz : 0 < z.re
    · rw [show (eI ⟨Θ, hΘ⟩).val z = mellin (fun t ↦ Θ (Real.log t)) z from
        positiveRealFourierMellin_apply I isOpen_Ioi ordConnected_Ioi nonempty_Ioi _ _ hz,
        show (eI ⟨φ.val, hφ⟩).val z = mellin (fun t ↦ φ.val (Real.log t)) z from
          positiveRealFourierMellin_apply I isOpen_Ioi ordConnected_Ioi nonempty_Ioi _ _ hz,
        ← positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty φ z
          (mem_univ _)]
      change mellin (fun t ↦ Θ (Real.log t)) z = (e φ).val z
      rw [show e φ = G from e.apply_symm_apply G, hG hz, mellin_logProfile]
      exact ((sLocalContinuedZeta_eq_theta F S μ ν hν ω f hz).trans
        (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2).symm
    · exact ((eI ⟨Θ, hΘ⟩).property.1 hz).trans ((eI ⟨φ.val, hφ⟩).property.1 hz).symm
  have ht : Θ = φ.val := congrArg Subtype.val he
  change Θ ∈ logExponentialDecaySubmodule univ
  rw [ht]
  exact φ.property

include hν in
/-- Proposition 5.3.4.4 reduces the construction of a flat representative
to a whole-plane Schwartz–Bergman bound on the continued Mellin component. -/
theorem sLocal_exists_polarFree_meromorphicZeta_of_schwartzBergman
    (ω : PontryaginDual (K F S)) (f : E F S)
    (G : SchwartzBergman (univ : Set ℝ))
    (hG : EqOn G.val
      (sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
        (sLocalComplexArchParameters F S ω) f) {z | 0 < z.re}) :
    ∃ g : P F S, sLocalMeromorphicZetaComponent F S μ ω f =
      sLocalMeromorphicZetaComponent F S μ ω g.val :=
  (sLocal_exists_polarFree_meromorphicZeta_iff_logProfile_mem F S μ ν hν ω f).mpr
    (sLocal_logProfile_mem_of_schwartzBergman F S μ ν hν ω f G hG)

end

end Masullo
