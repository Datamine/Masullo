import AdelicThetaDecay
import AdelicFourierDerivative
import IdelicZeta
import SLocalThetaMellin
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter Function MeasureTheory NumberField Set Topology
open scoped ENNReal NNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Q := IdeleClass F
private abbrev G := Idele F
private abbrev H := principalIdeles F

local instance : MeasurableSpace (G F) := borel _
local instance : BorelSpace (G F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Q F) := borel _
local instance : BorelSpace (Q F) := ⟨rfl⟩

/-- The idele class group in logarithmic-modulus and compact norm-one coordinates. -/
def ideleClassLogCoordinates : ℝ × K F ≃ₜ Q F where
  toFun p := (ideleClassSplitHomeomorph F).symm (p.2, Multiplicative.ofAdd p.1)
  invFun q := ((ideleClassLogNorm F q).toAdd, ideleClassNormOnePart F q)
  left_inv p := by
    change (((ideleClassSplitHomeomorph F) ((ideleClassSplitHomeomorph F).symm
      (p.2, Multiplicative.ofAdd p.1))).2.toAdd, ((ideleClassSplitHomeomorph F)
      ((ideleClassSplitHomeomorph F).symm (p.2, Multiplicative.ofAdd p.1))).1) = p
    rw [Homeomorph.apply_symm_apply]
    rfl
  right_inv q := (ideleClassSplitHomeomorph F).symm_apply_apply q
  continuous_toFun := (ideleClassSplitHomeomorph F).symm.continuous.comp
    (continuous_snd.prodMk (continuous_ofAdd.comp continuous_fst))
  continuous_invFun := (continuous_toAdd.comp (ideleClassLogNorm_continuous F)).prodMk
    ((ideleClassSplitHomeomorph F).continuous.fst)

theorem log_norm_coordinates (p : ℝ × K F) :
    Real.log (ideleClassNorm F (ideleClassLogCoordinates F p)) = p.1 := by
  exact congrArg Prod.fst ((ideleClassLogCoordinates F).symm_apply_apply p)

/-- The class measure obtained from norm-one Haar and Lebesgue measure
in the logarithmic-modulus coordinate. -/
def globalClassMeasure (ν : Measure (K F)) : Measure (Q F) :=
  (volume.prod ν).map (ideleClassLogCoordinates F)

/-- The logarithmic product measure is Haar on the full idele class group. -/
theorem globalClassMeasure_isHaar (ν : Measure (K F)) [ν.IsHaarMeasure] :
    (globalClassMeasure F ν).IsHaarMeasure := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := ideleClassLogCoordinates F
  let μ : Measure (ℝ × K F) := volume.prod ν
  have hμ : IsFiniteMeasureOnCompacts (μ.map e) := Measure.IsFiniteMeasureOnCompacts.map μ e
  have hpos : (μ.map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  change (μ.map e).IsHaarMeasure
  refine {
    lt_top_of_isCompact := hμ.lt_top_of_isCompact
    open_pos := hpos.open_pos
    map_mul_left_eq_self := ?_ }
  intro g
  let p := e.symm g
  let A : ℝ × K F → ℝ × K F := Prod.map (p.1 + ·) (p.2 * ·)
  have hf : Measurable ((p.1 + ·) : ℝ → ℝ) := measurable_const.add measurable_id
  have hg : Measurable ((p.2 * ·) : K F → K F) :=
    (continuous_const.mul continuous_id).measurable
  have hmap : Measure.map A μ = μ := by
    change Measure.map (Prod.map _ _) (volume.prod ν) = _
    rw [← Measure.map_prod_map volume ν hf hg, map_add_left_eq_self, map_mul_left_eq_self]
  have hcomp : (g * ·) ∘ e = e ∘ A := by
    funext y
    change g * e y = e (A y)
    rw [← e.apply_symm_apply g]
    change (p.2.val * ideleClassExpSection F (Multiplicative.ofAdd p.1)) *
        (y.2.val * ideleClassExpSection F (Multiplicative.ofAdd y.1)) =
      (p.2.val * y.2.val) * ideleClassExpSection F (Multiplicative.ofAdd (p.1 + y.1))
    rw [show Multiplicative.ofAdd (p.1 + y.1) =
      Multiplicative.ofAdd p.1 * Multiplicative.ofAdd y.1 from rfl, map_mul]
    exact mul_mul_mul_comm p.2.val (ideleClassExpSection F (Multiplicative.ofAdd p.1))
      y.2.val (ideleClassExpSection F (Multiplicative.ofAdd y.1))
  have hmul : Measurable ((g * ·) : Q F → Q F) :=
    ((continuous_const (y := g)).mul continuous_id).measurable
  change Measure.map (g * ·) (μ.map e) = μ.map e
  rw [Measure.map_map hmul e.continuous.measurable, hcomp,
    ← Measure.map_map e.continuous.measurable (hf.prodMap hg), hmap]

private theorem log_envelope_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    (C c : ℝ) (hc : 0 < c) :
    Integrable (fun q : Q F => C * Real.exp (-c * |Real.log (ideleClassNorm F q)|))
      (globalClassMeasure F ν) := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  let e := ideleClassLogCoordinates F
  apply (e.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).mpr
  change Integrable (fun p : ℝ × K F => C * Real.exp (-c * |Real.log (ideleClassNorm F (e p))|))
    (volume.prod ν)
  simp only [e, log_norm_coordinates]
  exact ((integrable_exp_abs_envelope c hc).const_mul C).comp_fst (ν := ν)

private theorem weighted_absolute_theta_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun q : Q F =>
      ideleClassNorm F q ^ σ * adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q)
      (globalClassMeasure F ν) := by
  let u := GlobalBruhat.algebraicEquiv F f
  obtain ⟨C, c, _, hc, hb⟩ := adelicTheta_zeta_strip_majorant F f σ σ hσ le_rfl
  have hpow : Continuous (fun q : Q F => ideleClassNorm F q ^ σ) :=
    (ideleClassNorm_continuous F).rpow_const (fun q => Or.inl (ideleClassNorm_pos F q).ne')
  have hcont := hpow.mul (adelicThetaAbs_continuous F u.property)
  refine (log_envelope_integrable F ν C c hc).mono' hcont.aestronglyMeasurable ?_
  refine Eventually.of_forall fun q => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (ideleClassNorm_pos F q).le _)
    (by
      obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
      rw [adelicThetaAbs_mk]
      exact tsum_nonneg fun _ => norm_nonneg _))]
  exact hb q σ le_rfl le_rfl

local instance : LocallyCompactSpace (G F) := ideles_locallyCompact
local instance : T2Space (G F) := ideles_hausdorff

local instance : SecondCountableTopology (G F) := by
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance : DiscreteTopology (H F) := principalIdeles_discrete (F := F)
local instance : Countable (H F) := countable_of_Lindelof_of_discrete
local instance : (Measure.count : Measure (H F)).IsHaarMeasure := subgroup_count_isHaarMeasure _
local instance : (Measure.count : Measure (H F)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- Every multiplicative Haar measure gives a compatible class normalization
with counting measure on the principal ideles and Lebesgue log modulus. -/
theorem globalClassMeasure_exists_weil (μ : Measure (G F)) [μ.IsHaarMeasure] :
    ∃ ν : Measure (K F), ν.IsHaarMeasure ∧
      IsWeilQuotientMeasure (H F) μ Measure.count (globalClassMeasure F ν) := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  letI : IsClosed (H F : Set (G F)) := principalIdeles_closed
  letI : LocallyCompactSpace (Q F) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := H F)).locallyCompactSpace
  letI : T1Space (Q F) := QuotientGroup.t1Space_iff.mpr principalIdeles_closed
  letI : SecondCountableTopology (Q F) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI := normOneIdeleClass_compact F
  let ν₀ : Measure (K F) := Measure.haar
  letI : ν₀.IsHaarMeasure := inferInstance
  let ρ := globalClassMeasure F ν₀
  letI : ρ.IsHaarMeasure := globalClassMeasure_isHaar F ν₀
  letI : ρ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  obtain ⟨η, hη, _⟩ := weilQuotientMeasure_existsUnique (H F) principalIdeles_closed μ Measure.count
  letI := hη.1
  letI := hη.2.1
  let c := Measure.haarScalarFactor η ρ
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure η ρ).ne'
  have heq : η = c • ρ := Measure.isMulLeftInvariant_eq_smul_of_regular η ρ
  refine ⟨c • ν₀, Measure.IsHaarMeasure.nnreal_smul ν₀ hc, ?_⟩
  have hmap : globalClassMeasure F (c • ν₀) = c • ρ := by
    unfold globalClassMeasure ρ
    rw [Measure.prod_smul_right, Measure.map_smul]
    rfl
  rw [hmap, ← heq]
  exact hη

private def principalFiberEquiv : Fˣ ≃ H F :=
  Equiv.ofBijective (fun t => ⟨principalIdele F t, t, rfl⟩) ⟨
    fun _ _ h => principalIdele_injective F (congrArg Subtype.val h),
    fun ⟨_, t, ht⟩ => ⟨t, Subtype.ext ht⟩⟩

private theorem idelicZeta_principal_summand (u : Adeles F → ℂ) (c : IdeleQuasiCharacter F)
    (g : G F) (t : Fˣ) :
    u (g * (principalFiberEquiv F t).val).val *
        (c (ideleClassMap F (g * (principalFiberEquiv F t).val)) : ℂ) =
      thetaSummand F u g t * (c (ideleClassMap F g) : ℂ) := by
  let e := principalFiberEquiv F
  let q := ideleClassMap F
  have ht : q (e t).val = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (e t).property
  rw [map_mul q, ht, congrArg c (mul_one (q g))]
  exact congrArg (fun a : Adeles F => u a * (c (q g) : ℂ))
    (mul_comm g.val (principalIdele F t).val)

private theorem idelicZeta_principal_summable (u : Adeles F → ℂ)
    (hu : u ∈ bruhatSubmodule F) (c : IdeleQuasiCharacter F) (g : G F) :
    Summable (fun h : H F => ‖u (g * h.val).val *
      (c (ideleClassMap F (g * h.val)) : ℂ)‖) := by
  apply (principalFiberEquiv F).summable_iff.mp
  refine ((adelicThetaNorm_summable F hu g).mul_right ‖(c (ideleClassMap F g) : ℂ)‖).congr
    fun t => ?_
  change ‖thetaSummand F u g t‖ * ‖(c (ideleClassMap F g) : ℂ)‖ =
    ‖u (g * (principalFiberEquiv F t).val).val *
      (c (ideleClassMap F (g * (principalFiberEquiv F t).val)) : ℂ)‖
  rw [idelicZeta_principal_summand F u c g t, norm_mul]

/-- The fibre sum is absolutely convergent on every principal-idele coset
at any quasi-character. This identity does not require global integrability. -/
theorem idelicZeta_cosetIntegral_eq_theta (u : Adeles F → ℂ) (hu : u ∈ bruhatSubmodule F)
    (c : IdeleQuasiCharacter F) :
    lcaCosetIntegral (H F) Measure.count (fun g : G F => u g.val * (c (ideleClassMap F g) : ℂ)) =
      fun q : Q F => adelicTheta F u q * (c q : ℂ) := by
  funext q
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
  change lcaCosetIntegral (H F) Measure.count
    (fun a : G F => u a.val * (c (ideleClassMap F a) : ℂ)) (QuotientGroup.mk g) =
      adelicTheta F u (ideleClassMap F g) * (c (ideleClassMap F g) : ℂ)
  rw [lcaCosetIntegral_mk, integral_countable
    (integrable_count_iff.mpr (idelicZeta_principal_summable F u hu c g))]
  simp only [count_real_singleton, one_smul]
  rw [← (principalFiberEquiv F).tsum_eq]
  simp_rw [idelicZeta_principal_summand F u c g, tsum_mul_right]
  rfl

/-- The idelic zeta integral converges absolutely on `Re s > 1` and
unfolds to the theta integral with the compatible Weil quotient measure. -/
theorem idelicZeta_integrable_eq_theta (μ : Measure (G F)) [μ.IsHaarMeasure]
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (H F) μ Measure.count (globalClassMeasure F ν))
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ)
    (hs : 1 < s.re) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    Integrable (fun g : G F => u g.val * (ideleNormTwist F χ s (ideleClassMap F g) : ℂ)) μ ∧
      idelicZetaIntegral F μ u χ s = thetaZetaIntegral F (globalClassMeasure F ν) u χ s := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let u := GlobalBruhat.algebraicEquiv F f
  let q := ideleClassMap F
  let c (g : Q F) := (ideleNormTwist F χ s g : ℂ)
  let w (g : G F) := u.val g.val * c (q g)
  have hc : Continuous c := Units.continuous_val.comp (map_continuous (ideleNormTwist F χ s))
  have hw : Continuous w := ((bruhat_continuous F u.property).comp Units.continuous_val).mul
    (hc.comp (ideleClassMap_continuous F))
  let e := principalFiberEquiv F
  have hf (g : G F) (t : Fˣ) : w (g * (e t).val) = thetaSummand F u.val g t * c (q g) :=
    idelicZeta_principal_summand F u.val (ideleNormTwist F χ s) g t
  have hfiber (g : G F) : Summable (fun h : H F => ‖w (g * h.val)‖) :=
    idelicZeta_principal_summable F u.val u.property (ideleNormTwist F χ s) g
  have horbit (g : G F) : (∑' h : H F, ‖w (g * h.val)‖) =
      ideleClassNorm F (q g) ^ s.re * adelicThetaAbs F u.val (q g) := by
    rw [← e.tsum_eq]
    simp only [hf, norm_mul, tsum_mul_right, c, norm_ideleNormTwist F χ hχ]
    exact mul_comm _ _
  have h := weighted_absolute_theta_integrable F ν f s.re hs
  have hfin : (∫⁻ y : Q F, ∫⁻ h : H F, ‖w (y.out * h.val)‖₊ ∂Measure.count
      ∂globalClassMeasure F ν) < ⊤ := by
    have he (y : Q F) : (∫⁻ h : H F, ‖w (y.out * h.val)‖₊ ∂Measure.count) =
        ENNReal.ofReal (ideleClassNorm F y ^ s.re * adelicThetaAbs F u.val y) := by
      rw [lintegral_count]
      simp_rw [← enorm_eq_nnnorm, ← ofReal_norm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hfiber y.out), horbit]
      have hy : q y.out = y := Quotient.out_eq' y
      rw [hy]
    simp_rw [he]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt h.hasFiniteIntegral
  obtain ⟨hInt, hEq⟩ := integrable_of_weilNormIntegral (H F) principalIdeles_closed
    μ Measure.count (globalClassMeasure F ν) hν hw.measurable hfin
  refine ⟨hInt, hEq.trans ?_⟩
  change (∫ q, lcaCosetIntegral (H F) Measure.count
    (fun g : G F => u.val g.val * (ideleNormTwist F χ s (ideleClassMap F g) : ℂ)) q
      ∂globalClassMeasure F ν) = _
  rw [idelicZeta_cosetIntegral_eq_theta F u.val u.property]
  rfl


/-- Absolute convergence in the classical half-plane for any Haar measure
on the ideles. -/
theorem idelicZeta_integrable (μ : Measure (G F)) [μ.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ)
    (hs : 1 < s.re) :
    Integrable (fun g : G F => (GlobalBruhat.algebraicEquiv F f).val g.val *
      (ideleNormTwist F χ s (ideleClassMap F g) : ℂ)) μ := by
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  letI := hν
  exact (idelicZeta_integrable_eq_theta F μ ν hW f χ hχ s hs).1


private theorem log_moment_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    Integrable (fun q : Q F =>
      |Real.log (ideleClassNorm F q)| * (C * Real.exp (-c * |Real.log (ideleClassNorm F q)|)))
      (globalClassMeasure F ν) := by
  let d := c / 2
  have hd : 0 < d := half_pos hc
  have hl : Continuous (fun q : Q F => Real.log (ideleClassNorm F q)) :=
    continuous_fst.comp (ideleClassLogCoordinates F).symm.continuous
  refine (log_envelope_integrable F ν (C / d) d hd).mono' ?_ ?_
  · exact (hl.abs.mul (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_const (y := -c)).mul hl.abs)))).aestronglyMeasurable
  refine Eventually.of_forall fun q => ?_
  let t := |Real.log (ideleClassNorm F q)|
  have ht : 0 ≤ t := abs_nonneg _
  change ‖t * (C * Real.exp (-c * t))‖ ≤ C / d * Real.exp (-d * t)
  rw [Real.norm_of_nonneg (by positivity)]
  have hte : t ≤ Real.exp (d * t) / d :=
    (le_div_iff₀ hd).mpr (by
      have he := Real.add_one_le_exp (d * t)
      linarith)
  calc
    _ ≤ (Real.exp (d * t) / d) * (C * Real.exp (-c * t)) :=
      mul_le_mul_of_nonneg_right hte (by positivity)
    _ = C / d * (Real.exp (d * t) * Real.exp (-c * t)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      dsimp [d]
      ring

/-- The class zeta integral is holomorphic on the absolute convergence half-plane. -/
theorem thetaZetaIntegral_analytic (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    AnalyticOnNhd ℂ (fun z => thetaZetaIntegral F (globalClassMeasure F ν)
      (GlobalBruhat.algebraicEquiv F f).val χ z) {z : ℂ | 1 < z.re} := by
  have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ ho
  intro z hz
  let u := GlobalBruhat.algebraicEquiv F f
  let l (q : Q F) := Real.log (ideleClassNorm F q)
  have hl : Continuous l := continuous_fst.comp (ideleClassLogCoordinates F).symm.continuous
  let θ := adelicTheta F u.val
  have hθ := adelicTheta_continuous F (bruhat_theta_continuous_and_invariant u.property).1
  let k (w : ℂ) (q : Q F) := θ q * ((χ q : ℂ) * Complex.exp (w * (l q : ℂ)))
  have hk (w : ℂ) : Continuous (k w) :=
    hθ.mul ((Units.continuous_val.comp (map_continuous χ)).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp hl)).cexp)
  have hb (w : ℂ) (q : Q F) : ‖k w q‖ ≤ ideleClassNorm F q ^ w.re * adelicThetaAbs F u.val q := by
    change ‖θ q * (ideleNormTwist F χ w q : ℂ)‖ ≤ _
    rw [norm_mul, norm_ideleNormTwist F χ hχ, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_adelicTheta_le_abs F u.property q)
      (Real.rpow_nonneg (ideleClassNorm_pos F q).le _)
  have hz' : 1 < z.re := hz
  have hi : Integrable (k z) (globalClassMeasure F ν) :=
    (weighted_absolute_theta_integrable F ν f z.re hz').mono'
      (hk z).aestronglyMeasurable (Eventually.of_forall (hb z))
  let a := (1 + z.re) / 2
  let b := z.re + 1
  have ha : 1 < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  obtain ⟨C, c, hC, hc, hmaj⟩ := adelicTheta_zeta_strip_majorant F f a b ha hab
  have hn : Complex.re ⁻¹' Ioo a b ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  have hd (w : ℂ) (q : Q F) : HasDerivAt (fun s => k s q) ((l q : ℂ) * k w q) w := by
    simpa only [k, id_eq, one_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((((hasDerivAt_id w).mul_const (l q : ℂ)).cexp.const_mul (χ q : ℂ)).const_mul (θ q))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := k) (F' := fun w q => (l q : ℂ) * k w q)
    (bound := fun q => |l q| * (C * Real.exp (-c * |l q|))) hn
    (Eventually.of_forall fun w => (hk w).aestronglyMeasurable)
    hi ((Complex.continuous_ofReal.comp hl).mul (hk z)).aestronglyMeasurable
    (Eventually.of_forall fun q w hw => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hb w q).trans (hmaj q w.re hw.1.le hw.2.le)) (abs_nonneg _))
    (log_moment_integrable F ν C c hC hc)
    (Eventually.of_forall fun q w _ => hd w q)
  exact h.2.differentiableAt.differentiableWithinAt

/-- The actual global idelic zeta integral is holomorphic for `Re s > 1`. -/
theorem idelicZetaIntegral_analytic (μ : Measure (G F)) [μ.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    AnalyticOnNhd ℂ (fun z => idelicZetaIntegral F μ
      (GlobalBruhat.algebraicEquiv F f).val χ z) {z : ℂ | 1 < z.re} := by
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  letI := hν
  have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ ho
  exact (thetaZetaIntegral_analytic F ν f χ hχ).differentiableOn.congr
    (fun z hz => (idelicZeta_integrable_eq_theta F μ ν hW f χ hχ z hz).2)


/-- Lemma 3.2.2.3 in unitary-twist coordinates. The idelic Mellin integral
is a continuous linear functional of the test in the final Schwartz-slice topology. -/
def idelicZetaCLM (μ : Measure (G F)) [μ.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) (hs : 1 < s.re) :
    GlobalBruhat F →L[ℂ] ℂ := by
  let u := GlobalBruhat.algebraicEquiv F
  let w (g : G F) := (ideleNormTwist F χ s (ideleClassMap F g) : ℂ)
  let Z (f : GlobalBruhat F) (g : G F) := (u f).val g.val * w g
  have hI (f : GlobalBruhat F) : Integrable (Z f) μ := idelicZeta_integrable F μ f χ hχ s hs
  let L : GlobalBruhat F →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ g, Z f g ∂μ
      map_add' := fun f g => by
        change (∫ a, Z (f + g) a ∂μ) = (∫ a, Z f a ∂μ) + ∫ a, Z g a ∂μ
        have he : Z (f + g) = fun a => Z f a + Z g a := by
          funext a
          simp only [Z, map_add, Submodule.coe_add, Pi.add_apply, add_mul]
        rw [he, integral_add (hI f) (hI g)]
      map_smul' := fun c f => by
        change (∫ a, Z (c • f) a ∂μ) = c • ∫ a, Z f a ∂μ
        have he : Z (c • f) = fun a => c • Z f a := by
          funext a
          simp only [Z, map_smul, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [he, integral_smul] }
  refine ⟨L, ?_⟩
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  letI : ν.IsHaarMeasure := hν
  obtain ⟨p, c, hp, hc, hbound⟩ := adelicTheta_zeta_strip_seminorm F s.re s.re hs le_rfl
  let E (q : Q F) := Real.exp (-c * |Real.log (ideleClassNorm F q)|)
  have hE : Integrable E (globalClassMeasure F ν) := by
    simpa only [one_mul] using log_envelope_integrable F ν 1 c hc
  let C : ℝ≥0 := ⟨∫ q, E q ∂globalClassMeasure F ν, integral_nonneg (fun q => Real.exp_nonneg _)⟩
  have hb (f : GlobalBruhat F) : ‖L f‖ ≤ C * p f := by
    have hEq := (idelicZeta_integrable_eq_theta F μ ν hW f χ hχ s hs).2
    change L f = (∫ q, adelicTheta F (u f).val q * (ideleNormTwist F χ s q : ℂ)
      ∂globalClassMeasure F ν) at hEq
    rw [hEq]
    refine (norm_integral_le_of_norm_le (hE.const_mul (p f)) (.of_forall fun q => ?_)).trans_eq ?_
    · rw [norm_mul, norm_ideleNormTwist F χ hχ, mul_comm]
      exact (mul_le_mul_of_nonneg_left (norm_adelicTheta_le_abs F (u f).property q)
        (Real.rpow_nonneg (ideleClassNorm_pos F q).le _)).trans (hbound f q s.re le_rfl le_rfl)
    · rw [integral_const_mul]
      exact mul_comm _ _
  have hn : Continuous ((normSeminorm ℂ ℂ).comp L) :=
    Seminorm.continuous_of_le (q := C • p) (continuous_const.mul hp) hb
  apply continuous_of_continuousAt_zero L
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact hn.tendsto' _ _ (map_zero _)

@[simp] theorem idelicZetaCLM_apply (μ : Measure (G F)) [μ.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) (hs : 1 < s.re)
    (f : GlobalBruhat F) :
    idelicZetaCLM F μ χ hχ s hs f =
      idelicZetaIntegral F μ (GlobalBruhat.algebraicEquiv F f).val χ s := rfl

/-- Lemma 3.2.2.3 for any quasi-character in the half-plane of absolute
convergence. Its real exponent is the exponent of its absolute value. -/
theorem globalQuasiCharacter_zeta_continuous (μ : Measure (G F)) [μ.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) {σ : ℝ} (hσ : 1 < σ)
    (hχ : ∀ q, ‖(χ q : ℂ)‖ = ideleClassNorm F q ^ σ) :
    Continuous (fun f : GlobalBruhat F =>
      ∫ g : G F, (GlobalBruhat.algebraicEquiv F f).val g.val * (χ (ideleClassMap F g) : ℂ) ∂μ) := by
  let ψ := ideleNormTwist F χ (-(σ : ℂ))
  have hψ : IsUnitary F ψ := by
    intro q
    have hm := ideleClassNorm_pos F q
    change ‖(χ q : ℂ) * ideleNormPower F (-(σ : ℂ)) q‖ = 1
    rw [norm_mul, hχ, ideleNormPower, Complex.norm_exp, Real.rpow_def_of_pos hm]
    rw [← Real.exp_add]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [mul_comm (Real.log _) σ, add_neg_cancel, Real.exp_zero]
  have he (q : Q F) : (ideleNormTwist F ψ (σ : ℂ) q : ℂ) = (χ q : ℂ) := by
    change ((χ q : ℂ) * ideleNormPower F (-(σ : ℂ)) q) * ideleNormPower F (σ : ℂ) q = _
    rw [mul_assoc]
    unfold ideleNormPower
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
  have hs : 1 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  apply (idelicZetaCLM F μ ψ hψ (σ : ℂ) hs).continuous.congr
  intro f
  simp only [idelicZetaCLM_apply, idelicZetaIntegral, he]


private theorem norm_mul_ideleTwist_integrable_majorant
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (q : X → Q F) (v : X → ℂ)
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) {a b : ℝ}
    (ha : Integrable (fun x => v x * (ideleNormTwist F χ (a : ℂ) (q x) : ℂ)) μ)
    (hb : Integrable (fun x => v x * (ideleNormTwist F χ (b : ℂ) (q x) : ℂ)) μ) :
    ∃ M : X → ℝ, Integrable M μ ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ∀ x, ‖v x * (ideleNormTwist F χ z (q x) : ℂ)‖ ≤ M x := by
  let m (z : ℂ) (x : X) := ‖v x * (ideleNormTwist F χ z (q x) : ℂ)‖
  refine ⟨fun x => m a x + m b x, ha.norm.add hb.norm, fun z hza hzb x => ?_⟩
  change m z x ≤ m a x + m b x
  have hm (w : ℂ) :
      m w x = ‖v x‖ * ideleClassNorm F (q x) ^ w.re := by
    dsimp only [m]
    rw [norm_mul, norm_ideleNormTwist F χ hχ]
  rcases le_total (ideleClassNorm F (q x)) 1 with h | h
  · refine (show m z x ≤ m a x by
      rw [hm, hm, Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (ideleClassNorm_pos F (q x)) h hza) (norm_nonneg _)).trans
          (le_add_of_nonneg_right (norm_nonneg _))
  · refine (show m z x ≤ m b x by
      rw [hm, hm, Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h hzb) (norm_nonneg _)).trans
          (le_add_of_nonneg_left (norm_nonneg _))

theorem uniformIntegral_logTruncation
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (l : X → ℝ) (hl : Measurable l)
    (k : ℂ → X → ℂ) {U : Set ℂ}
    (hI : ∀ z ∈ U, Integrable (k z) μ) {M : X → ℝ} (hM : Integrable M μ)
    (hbound : ∀ z ∈ U, ∀ x, ‖k z x‖ ≤ M x) :
    TendstoUniformlyOn (fun (R : ℝ) (z : ℂ) => ∫ x in l ⁻¹' Icc (-Real.log R) (Real.log R),
      k z x ∂μ) (fun z => ∫ x, k z x ∂μ) atTop U := by
  let J (R : ℝ) := l ⁻¹' Icc (-Real.log R) (Real.log R)
  have hcover : AECover μ atTop J := by
    refine ⟨.of_forall fun x => ?_, fun _ => hl measurableSet_Icc⟩
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop |l x|] with R hR
    exact ⟨by linarith [neg_le_abs (l x)], (le_abs_self (l x)).trans hR⟩
  have htail : Tendsto (fun R => ∫ x in (J R)ᶜ, M x ∂μ) atTop (𝓝 0) := by
    have he (R : ℝ) : (∫ x in (J R)ᶜ, M x ∂μ) = (∫ x, M x ∂μ) - ∫ x in J R, M x ∂μ := by
      rw [← integral_add_compl (hcover.measurableSet R) hM, add_sub_cancel_left]
    simp_rw [he]
    have hc : Tendsto (fun _ : ℝ => ∫ x, M x ∂μ) atTop (𝓝 (∫ x, M x ∂μ)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hc.sub (hcover.integral_tendsto_of_countably_generated hM)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [htail.eventually (Iio_mem_nhds hε)] with R hR z hz
  change dist (∫ x, k z x ∂μ) (∫ x in J R, k z x ∂μ) < ε
  rw [dist_eq_norm, ← integral_add_compl (hcover.measurableSet R) (hI z hz), add_sub_cancel_left]
  exact (norm_integral_le_of_norm_le hM.integrableOn (.of_forall (hbound z hz))).trans_lt hR

/-- The idelic modulus truncations in Remark 3.2.2.2 converge uniformly on
each closed strip in the half-plane of absolute convergence. The cutoff
radius tends to infinity through real values, so any diverging sequence is allowed. -/
theorem idelicZetaIntegral_truncation (μ : Measure (G F)) [μ.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    TendstoUniformlyOn (fun (R : ℝ) (z : ℂ) =>
      ∫ g in (fun g : G F => Real.log (ideleNorm F g)) ⁻¹' Icc (-Real.log R) (Real.log R),
        u g.val * (ideleNormTwist F χ z (ideleClassMap F g) : ℂ) ∂μ)
      (idelicZetaIntegral F μ u χ) atTop (Complex.re ⁻¹' Icc a b) := by
  let u := (GlobalBruhat.algebraicEquiv F f).val
  have hl : Measurable (fun g : G F => Real.log (ideleNorm F g)) :=
    Real.measurable_log.comp (ideleNorm_continuous F).measurable
  have hi (z : ℂ) (hz : 1 < z.re) := idelicZeta_integrable F μ f χ hχ z hz
  obtain ⟨M, hM, hbound⟩ := norm_mul_ideleTwist_integrable_majorant F (ideleClassMap F)
    (fun g => u g.val) χ hχ (hi a (by simpa using ha)) (hi b (by simpa using ha.trans_le hab))
  exact uniformIntegral_logTruncation _ hl _
    (fun z hz => hi z (ha.trans_le hz.1)) hM (fun z hz => hbound z hz.1 hz.2)

/-- A common integrable envelope for the two strip edges gives uniform
truncation throughout the strip. -/
theorem thetaZetaIntegral_truncation_of_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (a b : ℝ) (hab : a ≤ b)
    (hi : ∀ z : ℂ, z ∈ Complex.re ⁻¹' Icc a b →
      Integrable (fun q => adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q *
        (ideleNormTwist F χ z q : ℂ)) (globalClassMeasure F ν)) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    TendstoUniformlyOn (fun (R : ℝ) (z : ℂ) =>
      ∫ q in (fun q : Q F => Real.log (ideleClassNorm F q)) ⁻¹' Icc (-Real.log R) (Real.log R),
        adelicTheta F u q * (ideleNormTwist F χ z q : ℂ) ∂globalClassMeasure F ν)
      (thetaZetaIntegral F (globalClassMeasure F ν) u χ) atTop (Complex.re ⁻¹' Icc a b) := by
  let u := GlobalBruhat.algebraicEquiv F f
  have hl : Measurable (fun q : Q F => Real.log (ideleClassNorm F q)) :=
    Real.measurable_log.comp (ideleClassNorm_continuous F).measurable
  obtain ⟨M, hM, hbound⟩ := norm_mul_ideleTwist_integrable_majorant F id (adelicTheta F u.val)
    χ hχ (hi a (by simpa using hab)) (hi b (by simpa using hab))
  exact uniformIntegral_logTruncation _ hl _
    hi hM (fun z hz => hbound z hz.1 hz.2)

/-- The ordinary complex class integrand is absolutely integrable on the
initial half-plane, with the product Haar normalization. -/
theorem thetaZetaIntegral_integrable (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (z : ℂ) (hz : 1 < z.re) :
    Integrable (fun q => adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q *
      (ideleNormTwist F χ z q : ℂ)) (globalClassMeasure F ν) := by
  let u := GlobalBruhat.algebraicEquiv F f
  have hv := adelicTheta_continuous F (bruhat_theta_continuous_and_invariant u.property).1
  refine (weighted_absolute_theta_integrable F ν f z.re hz).mono'
    (hv.mul (Units.continuous_val.comp (map_continuous (ideleNormTwist F χ z)))).aestronglyMeasurable
    (.of_forall fun q => ?_)
  rw [norm_mul, norm_ideleNormTwist F χ hχ, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_adelicTheta_le_abs F u.property q)
    (Real.rpow_nonneg (ideleClassNorm_pos F q).le _)

/-- Class theta integrals converge uniformly under the same modulus
truncations and strip hypotheses. -/
theorem thetaZetaIntegral_truncation (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    TendstoUniformlyOn (fun (R : ℝ) (z : ℂ) =>
      ∫ q in (fun q : Q F => Real.log (ideleClassNorm F q)) ⁻¹' Icc (-Real.log R) (Real.log R),
        adelicTheta F u q * (ideleNormTwist F χ z q : ℂ) ∂globalClassMeasure F ν)
      (thetaZetaIntegral F (globalClassMeasure F ν) u χ) atTop (Complex.re ⁻¹' Icc a b) := by
  exact thetaZetaIntegral_truncation_of_integrable F ν f χ hχ a b hab
    (fun z hz => thetaZetaIntegral_integrable F ν f χ hχ z (ha.trans_le hz.1))


/-- Applying the normalized Riemann–Roch identity twice recovers both the
zero evaluation and the theta series. These are the involution identities
needed for the continued global zeta functional equation. -/
theorem adelicTheta_fourier_fourier (f : GlobalBruhat F) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    let w := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F
      (GlobalBruhat.fourier F f))).val
    w 0 = u 0 ∧ adelicTheta F w = adelicTheta F u := by
  let u := GlobalBruhat.algebraicEquiv F f
  let f' := GlobalBruhat.fourier F f
  let v := GlobalBruhat.algebraicEquiv F f'
  let f'' := GlobalBruhat.fourier F f'
  let w := GlobalBruhat.algebraicEquiv F f''
  have h₁ (q : Q F) : adelicTheta F u.val q =
      (ideleClassNorm F q)⁻¹ • adelicTheta F v.val q⁻¹ +
        (ideleClassNorm F q)⁻¹ • v.val 0 - u.val 0 := by
    simpa only [v, f', GlobalBruhat.fourier_apply] using
      congrFun (adelicTheta_riemannRoch F u.property).2 q
  have h₂ (q : Q F) : adelicTheta F v.val q =
      (ideleClassNorm F q)⁻¹ • adelicTheta F w.val q⁻¹ +
        (ideleClassNorm F q)⁻¹ • w.val 0 - v.val 0 := by
    simpa only [w, f'', GlobalBruhat.fourier_apply] using
      congrFun (adelicTheta_riemannRoch F v.property).2 q
  have hdiff (q : Q F) : adelicTheta F u.val q - adelicTheta F w.val q = w.val 0 - u.val 0 := by
    rw [h₁, h₂ q⁻¹, map_inv]
    have hq : (q⁻¹ : Q F)⁻¹ = q := inv_inv q
    simp only [hq, inv_inv, smul_sub, smul_add, smul_smul,
      inv_mul_cancel₀ (ideleClassNorm_pos F q).ne', one_smul]
    abel
  let r (t : ℝ) := ideleClassExpSection F (Multiplicative.ofAdd t)
  have ht (a : GlobalBruhat F) : Tendsto (fun t : ℝ =>
      adelicTheta F (GlobalBruhat.algebraicEquiv F a).val (r t)) atTop (𝓝 0) := by
    obtain ⟨C, _, hC⟩ := (adelicTheta_decay F a 1).2
    have hlim : Tendsto (fun t : ℝ => C * Real.exp (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hr : ideleClassNorm F (r t) = Real.exp t := ideleClassNorm_expSection F _
    simpa only [hr, pow_one, ← Real.exp_neg] using
      (hC (r t)).1 (hr ▸ (Real.one_le_exp_iff.mpr ht))
  have hzero : w.val 0 - u.val 0 = 0 := by
    have hc : Tendsto (fun _ : ℝ => w.val 0 - u.val 0) atTop (𝓝 (0 : ℂ)) := by
      have hh := (ht f).sub (ht f'')
      rw [sub_zero] at hh
      exact hh.congr' (Eventually.of_forall fun t => hdiff (r t))
    exact tendsto_nhds_unique tendsto_const_nhds hc
  exact ⟨sub_eq_zero.mp hzero, funext fun q => (sub_eq_zero.mp ((hdiff q).trans hzero)).symm⟩


/-- The part of the theta Mellin integral with class modulus at least one. -/
def thetaZetaUpper (ν : Measure (K F)) (f : GlobalBruhat F)
    (χ : IdeleQuasiCharacter F) (z : ℂ) : ℂ :=
  ∫ q in {q : Q F | 1 ≤ ideleClassNorm F q},
    adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q * (ideleNormTwist F χ z q : ℂ)
    ∂globalClassMeasure F ν

private theorem thetaZetaUpper_integrand_bound
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (b : ℝ) :
    ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
      ∀ (f : GlobalBruhat F) (w : ℂ), w.re ≤ b → ∀ q : Q F, 1 ≤ ideleClassNorm F q →
        ‖adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q * (ideleNormTwist F χ w q : ℂ)‖ ≤
          p f * Real.exp (-1 * |Real.log (ideleClassNorm F q)|) := by
  let l (q : Q F) := Real.log (ideleClassNorm F q)
  let n := max 2 (b + 1)
  have hn : 1 < n := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨p, hpC, hp⟩ := adelicTheta_power_seminorm F n hn
  refine ⟨p, hpC, fun f w hw q hq => ?_⟩
  let u := GlobalBruhat.algebraicEquiv F f
  let θ := adelicTheta F u.val
  have hq' : 1 ≤ ideleClassNorm F q := hq
  have hlog : 0 ≤ l q := Real.log_nonneg hq'
  have hr : ideleClassNorm F q ^ w.re ≤
      Real.exp (-1 * l q) * ideleClassNorm F q ^ n := by
    rw [Real.rpow_def_of_pos (ideleClassNorm_pos F q),
      Real.rpow_def_of_pos (ideleClassNorm_pos F q), ← Real.exp_add, Real.exp_le_exp]
    have hs : w.re ≤ -1 + n := by linarith [le_max_right (2 : ℝ) (b + 1)]
    nlinarith [mul_le_mul_of_nonneg_left hs hlog]
  change ‖θ q * (ideleNormTwist F χ w q : ℂ)‖ ≤ _
  rw [norm_mul, norm_ideleNormTwist F χ hχ, abs_of_nonneg hlog, mul_comm (p f),
    mul_comm ‖θ q‖]
  calc
    _ ≤ (Real.exp (-1 * l q) * ideleClassNorm F q ^ n) *
        adelicThetaAbs F u.val q :=
      mul_le_mul hr (norm_adelicTheta_le_abs F u.property q) (norm_nonneg _) (by positivity)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hp f q) (Real.exp_nonneg _)

/-- A continuous seminorm controls the upper theta Mellin integral uniformly
on each region where the real part is bounded above. -/
theorem thetaZetaUpper_seminorm_bound (ν : Measure (K F)) [ν.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (b : ℝ) :
    ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
      ∀ (f : GlobalBruhat F) (z : ℂ), z.re ≤ b → ‖thetaZetaUpper F ν f χ z‖ ≤ p f := by
  let E (q : Q F) := Real.exp (-1 * |Real.log (ideleClassNorm F q)|)
  let S := {q : Q F | 1 ≤ ideleClassNorm F q}
  have hS : MeasurableSet S := measurableSet_Ici.preimage (ideleClassNorm_continuous F).measurable
  have hi : Integrable E (globalClassMeasure F ν) := by
    simpa only [one_mul] using log_envelope_integrable F ν 1 1 one_pos
  let C : ℝ≥0 := ⟨∫ q in S, E q ∂globalClassMeasure F ν, integral_nonneg (fun _ => Real.exp_nonneg _)⟩
  obtain ⟨p, hp, hbound⟩ := thetaZetaUpper_integrand_bound F χ hχ b
  refine ⟨C • p, continuous_const.mul hp, fun f z hz => ?_⟩
  refine (norm_integral_le_of_norm_le (hi.integrableOn.const_mul (p f)) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem hS] with q hq
    exact hbound f z hz q hq
  · rw [integral_const_mul]
    exact mul_comm _ _

/-- The upper theta Mellin integral is absolutely convergent at every
parameter and is entire. Its bound on a strip uses one continuous test
seminorm and an exponential envelope in the logarithmic coordinate. -/
theorem thetaZetaUpper_integrable_analytic (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) :
    (∀ s : ℂ, IntegrableOn (fun q => adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q *
      (ideleNormTwist F χ s q : ℂ)) {q : Q F | 1 ≤ ideleClassNorm F q} (globalClassMeasure F ν)) ∧
    AnalyticOnNhd ℂ (thetaZetaUpper F ν f χ) univ := by
  let u := GlobalBruhat.algebraicEquiv F f
  let S := {q : Q F | 1 ≤ ideleClassNorm F q}
  let μ := globalClassMeasure F ν
  let l (q : Q F) := Real.log (ideleClassNorm F q)
  let θ := adelicTheta F u.val
  let k (w : ℂ) (q : Q F) := θ q * ((χ q : ℂ) * Complex.exp (w * (l q : ℂ)))
  have hS : MeasurableSet S := measurableSet_Ici.preimage (ideleClassNorm_continuous F).measurable
  have hl : Continuous l := continuous_fst.comp (ideleClassLogCoordinates F).symm.continuous
  have hθ := adelicTheta_continuous F (bruhat_theta_continuous_and_invariant u.property).1
  have hk (w : ℂ) : Continuous (k w) :=
    hθ.mul ((Units.continuous_val.comp (map_continuous χ)).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp hl)).cexp)
  have hb (b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ≤ b → ∀ q ∈ S,
      ‖k w q‖ ≤ C * Real.exp (-1 * |l q|) := by
    obtain ⟨p, _, hp⟩ := thetaZetaUpper_integrand_bound F χ hχ b
    exact ⟨p f, apply_nonneg p f, hp f⟩
  have hI (w : ℂ) : Integrable (k w) (μ.restrict S) := by
    obtain ⟨C, _, hb'⟩ := hb w.re
    refine (log_envelope_integrable F ν C 1 one_pos).integrableOn.mono'
      (hk w).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := μ) hS] with q hq
    exact hb' w le_rfl q hq
  refine ⟨hI, DifferentiableOn.analyticOnNhd ?_ isOpen_univ⟩
  intro z _
  change DifferentiableWithinAt ℂ (fun w => ∫ q, k w q ∂μ.restrict S) univ z
  have hneigh : Complex.re ⁻¹' Iio (z.re + 1) ∈ 𝓝 z :=
    (isOpen_Iio.preimage Complex.continuous_re).mem_nhds (by simp)
  obtain ⟨C, hC, hbound⟩ := hb (z.re + 1)
  have hd (w : ℂ) (q : Q F) : HasDerivAt (fun s => k s q) ((l q : ℂ) * k w q) w := by
    simpa only [k, id_eq, one_mul, mul_assoc, mul_left_comm, mul_comm] using
      ((((hasDerivAt_id w).mul_const (l q : ℂ)).cexp.const_mul (χ q : ℂ)).const_mul (θ q))
  have he : Integrable (fun q => |l q| * (C * Real.exp (-1 * |l q|))) (μ.restrict S) :=
    (log_moment_integrable F ν C 1 hC one_pos).integrableOn
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := k) (F' := fun w q => (l q : ℂ) * k w q) hneigh
    (.of_forall fun w => (hk w).aestronglyMeasurable) (hI z)
    ((Complex.continuous_ofReal.comp hl).mul (hk z)).aestronglyMeasurable
    ((ae_restrict_mem (μ := μ) hS).mono fun q hq w hw => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound w hw.le q hq) (abs_nonneg _))
    he (.of_forall fun q w _ => hd w q)
  exact hh.2.differentiableAt.differentiableWithinAt


/-- The ordinary class integral in 3.2.2.1(2)(b) can fail to converge
absolutely even on a nontrivial unitary component. At exponent one, any
nonzero Fourier evaluation at zero forces divergence for every unitary
character. Compact-character cancellation only applies after averaging. -/
theorem thetaZetaIntegral_not_integrable_on_one_line (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ)
    (s : ℂ) (hs : s.re = 1)
    (hf : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 ≠ 0) :
    ¬ Integrable (fun q : Q F => adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q *
      (ideleNormTwist F χ s q : ℂ)) (globalClassMeasure F ν) := by
  let u := GlobalBruhat.algebraicEquiv F f
  let v := GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)
  let θ := adelicTheta F u.val
  let μ := globalClassMeasure F ν
  let k (q : Q F) := θ q * (ideleNormTwist F χ s q : ℂ)
  obtain ⟨C, hC, hsmall⟩ := (adelicTheta_decay F f 0).2
  let D := C + ‖u.val 0‖
  have hD : 0 < D := add_pos_of_pos_of_nonneg hC (norm_nonneg _)
  let d := min 1 (‖v.val 0‖ / (2 * D))
  have hd : 0 < d := lt_min one_pos (div_pos (norm_pos_iff.mpr hf) (by positivity))
  let T : Set (Q F) := {q | Real.log (ideleClassNorm F q) < Real.log d}
  have hT : MeasurableSet T :=
    measurableSet_Iio.preimage (Real.measurable_log.comp (ideleClassNorm_continuous F).measurable)
  have hmT : μ T = ⊤ := by
    letI := normOneIdeleClass_compact F
    letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
    let e := ideleClassLogCoordinates F
    change ((volume.prod ν).map e) T = _
    rw [Measure.map_apply e.continuous.measurable hT]
    have hpre : e ⁻¹' T = Iio (Real.log d) ×ˢ (univ : Set (K F)) := by
      ext p
      change (Real.log (ideleClassNorm F (e p)) < Real.log d) ↔
        p.1 < Real.log d ∧ p.2 ∈ (univ : Set (K F))
      simp only [e, log_norm_coordinates, mem_univ, and_true]
    rw [hpre, Measure.prod_prod, Real.volume_Iio, ENNReal.top_mul]
    exact (isOpen_univ.measure_pos ν univ_nonempty).ne'
  have hbound (q : Q F) (hq : q ∈ T) : ‖v.val 0‖ / 2 ≤ ‖k q‖ := by
    let m := ideleClassNorm F q
    have hm : 0 < m := ideleClassNorm_pos F q
    have hmd : m < d := (Real.log_lt_log_iff hm hd).1 hq
    have hm1 : m ≤ 1 := hmd.le.trans (min_le_left _ _)
    let R := θ q - m⁻¹ • v.val 0 + u.val 0
    have hR : ‖R‖ ≤ C := by simpa only [pow_zero, mul_one] using (hsmall q).2.1 hm1
    have hR' : m • θ q - v.val 0 = m • R - m • u.val 0 := by
      dsimp only [R]
      rw [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hm.ne', one_smul, add_sub_cancel_right]
    have he : ‖m • θ q - v.val 0‖ ≤ m * D := by
      rw [hR']
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hm.le, ← mul_add]
      exact mul_le_mul_of_nonneg_left (add_le_add_left hR _) hm.le
    have hz : ‖v.val 0‖ ≤ ‖m • θ q‖ + m * D := by
      calc
        ‖v.val 0‖ = ‖m • θ q - (m • θ q - v.val 0)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := (norm_sub_le _ _).trans (add_le_add_right he _)
    have hsmall' : m * D ≤ ‖v.val 0‖ / 2 := by
      have hh := (le_div_iff₀ (show 0 < 2 * D by positivity)).mp
        (hmd.le.trans (min_le_right (1 : ℝ) (‖v.val 0‖ / (2 * D))))
      linarith
    have hk : ‖k q‖ = ‖m • θ q‖ := by
      rw [show k q = θ q * (ideleNormTwist F χ s q : ℂ) from rfl, norm_mul,
        norm_ideleNormTwist F χ hχ, hs, Real.rpow_one, norm_smul, Real.norm_of_nonneg hm.le, mul_comm]
    linarith
  intro hi
  have hconst : IntegrableOn (fun _ : Q F => ‖v.val 0‖ / 2) T μ := by
    apply (hi.norm.integrableOn (s := T)).mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem (μ := μ) hT] with q hq
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖v.val 0‖ / 2)]
    exact hbound q hq
  rcases (integrableOn_const_iff (C := ‖v.val 0‖ / 2)).mp hconst with hz | hfin
  · exact (div_pos (norm_pos_iff.mpr hf) (by norm_num)).ne' (enorm_eq_zero.mp hz)
  · exact hfin.ne hmT


/-- The divergence has actual Schwartz–Bruhat witnesses on every unitary
component at exponent one, even with the original zero term set to zero. -/
theorem exists_thetaZetaIntegral_not_integrable_on_one_line
    (ν : Measure (K F)) [ν.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) (hs : s.re = 1) :
    ∃ f : GlobalBruhat F, (GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 1 ∧
      ¬ Integrable (fun q : Q F => adelicTheta F (GlobalBruhat.algebraicEquiv F f).val q *
        (ideleNormTwist F χ s q : ℂ)) (globalClassMeasure F ν) := by
  obtain ⟨f, hf⟩ := GlobalBruhat.polarEvaluation_surjective F (0, 1)
  have h₀ : (GlobalBruhat.algebraicEquiv F f).val 0 = 0 := congrArg Prod.fst hf
  have h₁ : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 1 :=
    congrArg Prod.snd hf
  exact ⟨f, h₀, h₁, thetaZetaIntegral_not_integrable_on_one_line F ν f χ hχ s hs
    (h₁ ▸ one_ne_zero)⟩


/-- The boundary obstruction for the ordinary class integral transfers to
the idelic Lebesgue integral by Weil integration. This applies to every
multiplicative Haar normalization and every unitary twist. -/
theorem exists_idelicZetaIntegral_not_integrable_on_one_line (μ : Measure (G F)) [μ.IsHaarMeasure]
    (χ : IdeleQuasiCharacter F) (hχ : IsUnitary F χ) (s : ℂ) (hs : s.re = 1) :
    ∃ f : GlobalBruhat F, (GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
      ¬ Integrable (fun g : G F => (GlobalBruhat.algebraicEquiv F f).val g.val *
        (ideleNormTwist F χ s (ideleClassMap F g) : ℂ)) μ := by
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  obtain ⟨ν, hν, hW⟩ := globalClassMeasure_exists_weil F μ
  letI := hν
  obtain ⟨f, h₀, _, hdiv⟩ := exists_thetaZetaIntegral_not_integrable_on_one_line F ν χ hχ s hs
  refine ⟨f, h₀, fun hI => hdiv ?_⟩
  have hJ := (weilQuotientIntegral_L1_sigmaFinite (H F) principalIdeles_closed μ Measure.count
    (globalClassMeasure F ν) hW hI).2.1
  rw [idelicZeta_cosetIntegral_eq_theta F _ (GlobalBruhat.algebraicEquiv F f).property] at hJ
  exact hJ

/-- Counterexample to Proposition 3.4.2.1 at a point of its set (L_A) on
the trivial norm-one component. The imaginary part can be any real number. -/
theorem printed_global_idelic_boundary_convergence_fails
    (μ : Measure (G F)) [μ.IsHaarMeasure] (y : ℝ) :
    ∃ f : GlobalBruhat F, ¬ Integrable
      (fun g : G F => (GlobalBruhat.algebraicEquiv F f).val g.val *
        ideleNormPower F (1 + (y : ℂ) * Complex.I) (ideleClassMap F g)) μ := by
  have hχ : IsUnitary F (1 : IdeleQuasiCharacter F) := fun _ => by simp
  have hs : (1 + (y : ℂ) * Complex.I).re = 1 := by simp
  obtain ⟨f, _, hi⟩ := exists_idelicZetaIntegral_not_integrable_on_one_line F μ 1 hχ _ hs
  have he (q : Q F) :
      (ideleNormTwist F 1 (1 + (y : ℂ) * Complex.I) q : ℂ) =
        ideleNormPower F (1 + (y : ℂ) * Complex.I) q := by
    change (((1 : IdeleQuasiCharacter F) q : ℂ) * _) = _
    simp
  exact ⟨f, by simpa only [he] using hi⟩

end

end Masullo
