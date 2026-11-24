/-
The stage integrability and orbit integral arguments adapt RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at 1d8742feacca560ae3a2beedfb0e743b1efd8bfe
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import BruhatSchwartz
import BruhatFirstOrderSymbols
import ElementarySchwartzHaar
import WeilSigmaCompactLocalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Haar on the open upper subgroup pushes forward to Haar on the elementary
coordinate group, since the structural quotient has compact kernel. -/
theorem BruhatSchwartzStage.coordinates_map_addHaar (p : BruhatSchwartzStage G)
    [MeasurableSpace p.2.finiteFactor] [BorelSpace p.2.finiteFactor] :
    ((μ.comap p.1.upper.val.subtype).map
      (fun x => (p.1.stageCoordinates p.2 x).toAdd)).IsAddHaarMeasure := by
  let H := p.1.upper.val
  let K := p.1.kernel.comap H.subtype
  let E := ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
  have ho := p.1.upper.property.1
  have hK : IsCompact (K : Set H) := by
    apply (H.isClosed_of_isOpen ho).isClosedEmbedding_subtypeVal.isCompact_preimage
      (K := (p.1.kernel : Set G))
    rw [← lcaDualAnnihilator_annihilator p.1.kernel p.1.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ p.1.annihilator_open
  let q : H →ₜ* p.1.StageQuotient := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  have hq : IsProperMap q :=
    LCAStructuralPair.proper_of_open_surjective_compact_kernel q
      (QuotientGroup.mk'_surjective K) QuotientGroup.isOpenMap_coe (by simpa [q] using hK)
  have hp : IsProperMap (p.1.stageCoordinates p.2) := p.2.equiv.toHomeomorph.isProperMap.comp hq
  let ν := μ.comap H.subtype
  letI : ν.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul)
    μ (f := H.subtype) ho.isOpenEmbedding_subtypeVal
  letI : BorelSpace ((Fin p.2.latticeRank → ℤ) × p.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace ((Fin p.2.torusDim → AddCircle (1 : ℝ)) ×
      (Fin p.2.latticeRank → ℤ) × p.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace E := Prod.borelSpace
  letI mE : MeasurableSpace (Multiplicative E) := (inferInstance : MeasurableSpace E)
  letI : BorelSpace (Multiplicative E) := (inferInstance : BorelSpace E)
  letI : T2Space (Multiplicative E) := (inferInstance : T2Space E)
  let ρ : Measure (Multiplicative E) := ν.map (p.1.stageCoordinates p.2)
  letI : ρ.IsHaarMeasure := Measure.isHaarMeasure_map ν
    (p.1.stageCoordinates p.2).toMonoidHom hp.continuous
    (p.2.equiv.surjective.comp (QuotientGroup.mk'_surjective K))
    (isProperMap_iff_tendsto_cocompact.mp hp).2
  exact
    { lt_top_of_isCompact := fun {_} h => IsCompact.measure_lt_top (μ := ρ) h
      map_add_left_eq_self := fun x => map_mul_left_eq_self ρ (Multiplicative.ofAdd x)
      open_pos := fun s hs hn => Measure.IsOpenPosMeasure.open_pos (μ := ρ) s hs hn }

/-- All realized Schwartz–Bruhat stage functions are Haar-integrable. -/
theorem BruhatSchwartzStage.integrable (p : BruhatSchwartzStage G) (f : p.Space) :
    Integrable (p.realize f) μ := by
  letI : MeasurableSpace p.2.finiteFactor := borel _
  letI : BorelSpace p.2.finiteFactor := ⟨rfl⟩
  let H := p.1.upper.val
  let E := ElementaryLCAModel p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
  let e (x : H) : E := (p.1.stageCoordinates p.2 x).toAdd
  let ν := μ.comap H.subtype
  let τ := ν.map e
  letI : τ.IsAddHaarMeasure := p.coordinates_map_addHaar μ
  letI : BorelSpace ((Fin p.2.latticeRank → ℤ) × p.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace ((Fin p.2.torusDim → AddCircle (1 : ℝ)) ×
      (Fin p.2.latticeRank → ℤ) × p.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace E := Prod.borelSpace
  have hf : Integrable f.val τ := by
    apply memLp_one_iff_integrable.mp
    have h := elementarySchwartz_weightedOperator_memLp_haar τ 1 [(1, [])] [(1, [])] f
    have he : (elementarySchwartz_weightedOperator [(1, [])] [(1, [])] f : E → ℂ) = f.val := by
      funext x
      simp [elementarySchwartz_weightedOperator_apply, elementaryDualWord, elementaryOrbitWord]
    exact he ▸ h
  have he : Continuous e := (p.1.stageCoordinates p.2).continuous
  have hcomp : Integrable (fun x : H => f (e x)) ν :=
    hf.comp_measurable he.measurable
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := (H : Set G))
  · rw [integrableOn_iff_comap_subtypeVal p.1.upper.property.1.measurableSet]
    exact hcomp.congr (.of_forall fun x => (p.1.realizeSchwartz_apply_of_mem p.2 f x).symm)
  · exact p.1.realizeSchwartz_apply_of_not_mem p.2 f

theorem bruhatSchwartz_integrable (f : BruhatSchwartz G) : Integrable f.val μ := by
  obtain ⟨p, u, hu⟩ := f.property
  rw [← hu]
  exact p.integrable μ u

omit [MeasurableSpace G] [BorelSpace G] in
set_option maxHeartbeats 800000 in
/-- The realization of a stage is invariant under its structural kernel. -/
theorem BruhatSchwartzStage.realize_mul_kernel (p : BruhatSchwartzStage G) (f : p.Space)
    (x : G) (k : p.1.kernel) : p.realize f (x * k.val) = p.realize f x := by
  have hk := p.1.kernel_le k.property
  by_cases hx : x ∈ p.1.upper.val
  · let y : p.1.upper.val := ⟨x, hx⟩
    let z : p.1.upper.val := ⟨k.val, hk⟩
    change p.realize f (y * z).val = p.realize f y.val
    rw [p.1.realizeSchwartz_apply_of_mem, p.1.realizeSchwartz_apply_of_mem, map_mul]
    have hz : p.1.stageCoordinates p.2 z = 1 := by
      change p.2.equiv (QuotientGroup.mk z) = 1
      rw [(QuotientGroup.eq_one_iff z).mpr k.property, map_one]
    rw [hz, mul_one]
  · rw [p.1.realizeSchwartz_apply_of_not_mem p.2 f _ hx,
      p.1.realizeSchwartz_apply_of_not_mem p.2 f _
        (fun h => hx ((p.1.upper.val.mul_mem_cancel_right hk).mp h))]

set_option maxHeartbeats 800000 in
/-- The Fourier transform of a realized stage is supported in the dual
upper subgroup and invariant under the dual kernel. These facts use only the
integrable physical test; no integrability on the dual is needed. -/
theorem BruhatSchwartzStage.fourier_support_invariant (p : BruhatSchwartzStage G) (f : p.Space) :
    support (lcaFourier μ (p.realize f)) ⊆ lcaAnnihilator p.1.kernel ∧
      ∀ (ψ : lcaAnnihilator p.1.upper.val) χ,
        lcaFourier μ (p.realize f) (χ * ψ.val) = lcaFourier μ (p.realize f) χ := by
  constructor
  · intro χ hχ
    apply (mem_lcaAnnihilator_iff _ χ).mpr
    intro k
    have hl := lcaFourier_translate μ (p.realize f) k.val χ
    rw [show (fun x => p.realize f (k.val * x)) = p.realize f from
      funext fun x => (congrArg (p.realize f) (mul_comm k.val x)).trans
        (p.realize_mul_kernel f x k)] at hl
    apply Circle.ext
    change (χ k.val : ℂ) = (1 : ℂ)
    exact mul_right_cancel₀ hχ (hl.symm.trans (one_mul _).symm)
  · intro ψ χ
    apply integral_congr_ae
    exact .of_forall fun x => by
      by_cases hx : x ∈ p.1.upper.val
      · have hψ := (mem_lcaAnnihilator_iff _ ψ.val).mp ψ.property ⟨x, hx⟩
        change p.realize f x * star (((χ x * ψ.val x : Circle) : ℂ)) =
          p.realize f x * star (χ x : ℂ)
        change ψ.val x = 1 at hψ
        rw [hψ, mul_one]
      · simp [p.1.realizeSchwartz_apply_of_not_mem p.2 f x hx]

variable [μ.Regular]

/-- A continuous integrable derivative along a one-parameter subgroup
has integral zero when the original function is integrable. -/
private theorem integral_orbit_derivative_zero (a : Multiplicative ℝ →ₜ* G)
    {f v : G → ℂ} (hf : Integrable f μ) (hv : Integrable v μ) (hvc : Continuous v)
    (hd : ∀ x : G, HasDerivAt (fun t : ℝ => f (x * a (Multiplicative.ofAdd t))) (v x) 0) :
    ∫ x, v x ∂μ = 0 := by
  obtain ⟨J, hJo, hJσ, hvs⟩ := exists_open_sigmaCompact_subgroup_of_integrable μ hv
  let b (t : ℝ) := a (Multiplicative.ofAdd t)
  have hb : Continuous b := a.continuous.comp continuous_ofAdd
  have hmem (t : ℝ) : b t ∈ J := by
    have hpre := isPreconnected_range hb
    exact hpre.subset_isClopen ⟨J.isClosed_of_isOpen hJo, hJo⟩
      ⟨1, ⟨0, map_one a⟩, J.one_mem⟩ (mem_range_self t)
  have htime (x : G) (t : ℝ) : HasDerivAt
      (fun s => f (x * b s)) (v (x * b t)) t := by
    have h : HasDerivAt (fun s : ℝ => f (x * b t * b s)) (v (x * b t)) (t - t) :=
      sub_self t ▸ hd (x * b t)
    have he : (fun s => f (x * b t * b (s - t))) = (fun s => f (x * b s)) := by
      funext s
      have hb' : b t * b (s - t) = b s := by
        change a (Multiplicative.ofAdd t) * a (Multiplicative.ofAdd (s - t)) = _
        rw [← map_mul, ← ofAdd_add, add_sub_cancel]
      rw [mul_assoc, hb']
    rw [← he]
    exact h.comp_sub_const t t
  let k (t : ℝ) (x : G) := v (x * b t)
  have hFTC (x : G) : (∫ t in (0 : ℝ)..1, k t x) = f (x * b 1) - f x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => htime x t)
      ((hvc.comp (continuous_const.mul hb)).intervalIntegrable (μ := volume) 0 1)
    simpa only [k, b, ofAdd_zero, map_one, mul_one] using h
  let S : Set G := J
  letI : SigmaFinite (μ.restrict S) := sigmaFinite_restrict_of_isSigmaCompact μ hJσ
  have hk0 (t : ℝ) (x : G) (hx : x ∉ S) : k t x = 0 :=
    notMem_support.mp fun hm => hx ((J.mul_mem_cancel_right (hmem t)).mp (hvs hm))
  have hrow (t : ℝ) : (∫ x in S, k t x ∂μ) = ∫ x, v x ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hk0 t)).trans (integral_mul_right_eq_self v (b t))
  have hnorm (t : ℝ) : (∫ x in S, ‖k t x‖ ∂μ) = ∫ x, ‖v x‖ ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hk0 t x hx, norm_zero])).trans ?_
    exact integral_mul_right_eq_self (fun x => ‖v x‖) (b t)
  have hkc : Continuous (Function.uncurry k) := hvc.comp (continuous_snd.mul (hb.comp continuous_fst))
  letI : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
  have hint : Integrable (Function.uncurry k)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod (μ.restrict S)) := by
    refine (integrable_prod_iff hkc.aestronglyMeasurable).mpr ⟨.of_forall fun t =>
      ((measurePreserving_mul_right μ (b t)).integrable_comp_of_integrable hv).restrict, ?_⟩
    simpa only [Function.uncurry_apply_pair, hnorm] using
      (integrable_const (μ := volume.restrict (uIoc (0 : ℝ) 1)) (∫ x, ‖v x‖ ∂μ))
  have he := intervalIntegral_integral_swap hint
  simp_rw [hrow, hFTC] at he
  have hzero (x : G) (hx : x ∉ S) : f (x * b 1) - f x = 0 := by
    rw [← hFTC]
    simp only [fun t => hk0 t x hx, intervalIntegral.integral_zero]
  have hf1 : Integrable (fun x => f (x * b 1)) μ :=
    (measurePreserving_mul_right μ (b 1)).integrable_comp_of_integrable hf
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_sub hf1 hf,
    integral_mul_right_eq_self, sub_self] at he
  simpa using he

/-- Fourier differentiation for each generating first-order operator.
The symbol is the derivative at the identity of the character itself. -/
theorem lcaFourier_bruhatDerivative (a : Multiplicative ℝ →ₜ* G)
    (f : BruhatSchwartz G) (χ : PontryaginDual G) :
    lcaFourier μ (bruhatSchwartz_derivative a f).val χ =
      bruhatOrbitDeriv a (fun x => (χ x : ℂ)) 1 * lcaFourier μ f.val χ := by
  let g := bruhatSchwartz_derivative a f
  let c := bruhatOrbitDeriv a (fun x => (χ x : ℂ)) 1
  let u : BruhatSchwartz G := g - c • f
  let w (x : G) := f.val x * star (χ x : ℂ)
  let v (x : G) := u.val x * star (χ x : ℂ)
  have hcont : Continuous v :=
    (bruhatSchwartz_continuous u).mul (continuous_subtype_val.comp χ.continuous).star
  have hchar : HasDerivAt (fun t : ℝ => (χ (a (Multiplicative.ofAdd t)) : ℂ)) c 0 := by
    have h := (bruhatOrbitDeriv_regular a _ (s := 0) (pontryaginDual_mem_bruhatSmooth χ 1)).2 (1 : G)
    simpa only [one_mul] using h
  have hstar : HasDerivAt (fun t : ℝ => star (χ (a (Multiplicative.ofAdd t)) : ℂ)) (-c) 0 := by
    have h := HasDerivAt.comp_const_sub (0 : ℝ) (0 : ℝ)
      (show HasDerivAt _ c (0 - 0) by simpa only [sub_zero] using hchar)
    simpa only [zero_sub, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj, Complex.star_def] using h
  have hd (x : G) : HasDerivAt (fun t : ℝ => w (x * a (Multiplicative.ofAdd t))) (v x) 0 := by
    have hx := (bruhatOrbitDeriv_regular a _ (s := 0) (bruhatSchwartz_le_smooth f.property 1)).2 x
    have h := hx.fun_mul (hstar.const_mul (star (χ x : ℂ)))
    have hfun : (fun t : ℝ => w (x * a (Multiplicative.ofAdd t))) =
        fun t => f.val (x * a (Multiplicative.ofAdd t)) *
          (star (χ x : ℂ) * star (χ (a (Multiplicative.ofAdd t)) : ℂ)) := by
      funext t
      simp only [w, map_mul, Circle.coe_mul, star_mul]
      ring
    have hval : v x = bruhatOrbitDeriv a f.val x *
        (star (χ x : ℂ) * star (χ (a (Multiplicative.ofAdd (0 : ℝ))) : ℂ)) +
        f.val (x * a (Multiplicative.ofAdd (0 : ℝ))) * (star (χ x : ℂ) * -c) := by
      change (g.val x - c * f.val x) * star (χ x : ℂ) = _
      simp only [ofAdd_zero, map_one, mul_one, Circle.coe_one, star_one]
      change (bruhatOrbitDeriv a f.val x - c * f.val x) * star (χ x : ℂ) = _
      ring
    rw [hfun, hval]
    exact h
  have hf := integrable_fourierIntegrand μ (bruhatSchwartz_integrable μ f) χ
  have hg := integrable_fourierIntegrand μ (bruhatSchwartz_integrable μ g) χ
  have hv := integrable_fourierIntegrand μ (bruhatSchwartz_integrable μ u) χ
  have hz := integral_orbit_derivative_zero μ a hf hv hcont hd
  change (∫ x, (g.val x - c * f.val x) * star (χ x : ℂ) ∂μ) = 0 at hz
  simp only [sub_mul, mul_assoc] at hz
  rw [integral_sub hg (hf.const_mul c), integral_const_mul] at hz
  exact sub_eq_zero.mp hz

/-- The algebra of invariant differential operators on smooth Bruhat functions. -/
def bruhatDiffAlgebra (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    Subalgebra ℂ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Algebra.adjoin ℂ (range (bruhatFirstOrder (G := G)))

omit [MeasurableSpace G] [BorelSpace G] in
private def smoothCharacter (χ : PontryaginDual G) : bruhatSmoothSubmodule (G := G) :=
  ⟨fun x => (χ x : ℂ), pontryaginDual_mem_bruhatSmooth χ⟩

omit [MeasurableSpace G] [BorelSpace G] in
/-- The invariant differential symbol is the value of the differentiated
character at the identity. -/
def bruhatDiffSymbol (D : bruhatDiffAlgebra G) (χ : PontryaginDual G) : ℂ :=
  (D.val (smoothCharacter χ)).val 1

/-- The Fourier integral is linear on the full space of Schwartz–Bruhat tests. -/
def bruhatFourierLinear : BruhatSchwartz G →ₗ[ℂ] (PontryaginDual G → ℂ) where
  toFun f := lcaFourier μ f.val
  map_add' f g := by
    funext χ
    change (∫ x, (f.val x + g.val x) * star (χ x : ℂ) ∂μ) = _
    simp only [add_mul, Pi.add_apply]
    exact integral_add (integrable_fourierIntegrand μ (bruhatSchwartz_integrable μ f) χ)
      (integrable_fourierIntegrand μ (bruhatSchwartz_integrable μ g) χ)
  map_smul' c f := by
    funext χ
    change (∫ x, (c * f.val x) * star (χ x : ℂ) ∂μ) = c * lcaFourier μ f.val χ
    simp only [mul_assoc, integral_const_mul, lcaFourier]

/-- Lemma D.1.6.19(1). Every invariant differential operator restricts
continuously to Schwartz–Bruhat functions, and its Fourier transform is
multiplication by the operator's symbol. -/
theorem lcaFourier_bruhatDiff (D : bruhatDiffAlgebra G) :
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
      (∀ f, Submodule.inclusion bruhatSchwartz_le_smooth (T f) =
        D.val (Submodule.inclusion bruhatSchwartz_le_smooth f)) ∧
      ∀ f χ, lcaFourier μ (T f).val χ = bruhatDiffSymbol D χ * lcaFourier μ f.val χ := by
  let i := Submodule.inclusion (bruhatSchwartz_le_smooth (G := G))
  let B := bruhatFourierLinear μ
  have hD : ∃ p : PontryaginDual G → ℂ,
      (∀ χ, D.val (smoothCharacter χ) = p χ • smoothCharacter χ) ∧
      ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
        (∀ f, i (T f) = D.val (i f)) ∧ ∀ f χ, B (T f) χ = p χ * B f χ := by
    refine Algebra.adjoin_induction (p := fun L _ => ∃ p : PontryaginDual G → ℂ,
      (∀ χ, L (smoothCharacter χ) = p χ • smoothCharacter χ) ∧
      ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
        (∀ f, i (T f) = L (i f)) ∧ ∀ f χ, B (T f) χ = p χ * B f χ) ?_ ?_ ?_ ?_ D.property
    · rintro _ ⟨a, rfl⟩
      refine ⟨fun χ => bruhatOrbitDeriv a (fun x => (χ x : ℂ)) 1, ?_,
        bruhatSchwartz_derivative a, bruhatSchwartz_derivative_eq_firstOrder a,
        lcaFourier_bruhatDerivative μ a⟩
      intro χ
      apply Subtype.ext
      funext x
      change bruhatOrbitDeriv a (fun y => (χ y : ℂ)) x =
        bruhatOrbitDeriv a (fun y => (χ y : ℂ)) 1 * (χ x : ℂ)
      simp only [bruhatOrbitDeriv, one_mul, map_mul, Circle.coe_mul, deriv_const_mul_field]
      exact mul_comm _ _
    · intro c
      refine ⟨fun _ => c, fun _ => rfl, c • ContinuousLinearMap.id ℂ _, ?_, ?_⟩
      · intro f
        exact i.map_smul c f
      · intro f χ
        change B (c • f) χ = c * B f χ
        rw [B.map_smul]
        rfl
    · rintro L M _ _ ⟨p, hp, T, hT, hTp⟩ ⟨q, hq, U, hU, hUq⟩
      refine ⟨p + q, ?_, T + U, ?_, ?_⟩
      · intro χ
        change L (smoothCharacter χ) + M (smoothCharacter χ) = (p χ + q χ) • smoothCharacter χ
        rw [hp, hq, add_smul]
      · intro f
        change i (T f + U f) = L (i f) + M (i f)
        rw [i.map_add, hT, hU]
      · intro f χ
        change B (T f + U f) χ = (p χ + q χ) * B f χ
        rw [B.map_add]
        change B (T f) χ + B (U f) χ = _
        rw [hTp, hUq, add_mul]
    · rintro L M _ _ ⟨p, hp, T, hT, hTp⟩ ⟨q, hq, U, hU, hUq⟩
      refine ⟨p * q, ?_, T.comp U, ?_, ?_⟩
      · intro χ
        change L (M (smoothCharacter χ)) = (p χ * q χ) • smoothCharacter χ
        rw [hq, map_smul, hp, smul_smul, mul_comm]
      · intro f
        change i (T (U f)) = L (M (i f))
        rw [hT, hU]
      · intro f χ
        change B (T (U f)) χ = (p χ * q χ) * B f χ
        rw [hTp, hUq, mul_assoc]
  obtain ⟨p, hp, T, hT, hTp⟩ := hD
  refine ⟨T, hT, fun f χ => ?_⟩
  have hsym : bruhatDiffSymbol D χ = p χ := by
    unfold bruhatDiffSymbol
    rw [hp]
    change p χ * (χ 1 : ℂ) = p χ
    simp
  rw [hsym]
  exact hTp f χ

/-- Multiplying the transform by a continuous real frequency is induced
by a rescaled directional derivative on the physical test space. -/
theorem exists_bruhatFourier_frequency (ρ : PontryaginDual G →ₜ* Multiplicative ℝ) :
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
      ∀ f χ, lcaFourier μ (T f).val χ = ((ρ χ).toAdd : ℂ) * lcaFourier μ f.val χ := by
  let r : continuousRealHomSubmodule (PontryaginDual G) :=
    ⟨fun χ => (ρ χ).toAdd, continuous_toAdd.comp ρ.continuous,
      fun _ _ => congrArg Multiplicative.toAdd (map_mul ρ _ _)⟩
  obtain ⟨σ, hσ⟩ := bruhatFirstOrder_frequency (G := G)
  let D := σ.symm r
  obtain ⟨a, ha⟩ := bruhatFirstOrderReal_represent D
  let z : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hz : z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨z⁻¹ • bruhatSchwartz_derivative a, fun f χ => ?_⟩
  have hpair (t : ℝ) : χ (a (Multiplicative.ofAdd t)) =
      Circle.exp ((2 * Real.pi * (ρ χ).toAdd) * t) := by
    have h := hσ a D ha χ t
    rw [show σ D = r from σ.apply_symm_apply r] at h
    simpa only [r, mul_assoc] using h.symm
  have hslope := characterSlope_unique a χ (2 * Real.pi * (ρ χ).toAdd) hpair
  have hsymbol := (directionalDeriv_character_symbol [a] χ).2.1
  change bruhatOrbitDeriv a (fun x => (χ x : ℂ)) 1 =
    (((characterSlope a χ).toAdd : ℝ) : ℂ) * Complex.I * 1 at hsymbol
  rw [hslope, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_one] at hsymbol
  let B := bruhatFourierLinear μ
  change B (z⁻¹ • bruhatSchwartz_derivative a f) χ = _
  rw [B.map_smul]
  change z⁻¹ * lcaFourier μ (bruhatSchwartz_derivative a f).val χ = _
  rw [lcaFourier_bruhatDerivative, hsymbol]
  have hmul : 2 * (Real.pi : ℂ) * ((ρ χ).toAdd : ℂ) * Complex.I =
      z * ((ρ χ).toAdd : ℂ) := by dsimp [z]; ring
  rw [hmul, ← mul_assoc z⁻¹, ← mul_assoc z⁻¹, inv_mul_cancel₀ hz, one_mul]

/-- Polynomial frequency weights on the transform come from continuous
invariant differential operators on the physical Schwartz–Bruhat space. -/
theorem exists_bruhatFourier_polynomial {ι : Type*} (ρ : ι → PontryaginDual G →ₜ* Multiplicative ℝ)
    (P : MvPolynomial ι ℂ) :
    ∃ T : BruhatSchwartz G →L[ℂ] BruhatSchwartz G,
      ∀ f χ, lcaFourier μ (T f).val χ =
        MvPolynomial.eval (fun i => ((ρ i χ).toAdd : ℂ)) P * lcaFourier μ f.val χ := by
  classical
  let B := bruhatFourierLinear μ
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨c • ContinuousLinearMap.id ℂ _, fun f χ => ?_⟩
    change B (c • f) χ = _
    rw [B.map_smul, MvPolynomial.eval_C]
    rfl
  | add P Q hP hQ =>
    obtain ⟨T, hT⟩ := hP
    obtain ⟨U, hU⟩ := hQ
    refine ⟨T + U, fun f χ => ?_⟩
    change B (T f + U f) χ = _
    rw [B.map_add, MvPolynomial.eval_add, add_mul]
    change lcaFourier μ (T f).val χ + lcaFourier μ (U f).val χ = _
    rw [hT f χ, hU f χ]
  | mul_X P i hP =>
    obtain ⟨T, hT⟩ := hP
    obtain ⟨U, hU⟩ := exists_bruhatFourier_frequency μ (ρ i)
    refine ⟨U.comp T, fun f χ => ?_⟩
    change lcaFourier μ (U (T f)).val χ = _
    rw [hU, hT, MvPolynomial.eval_mul, MvPolynomial.eval_X, mul_left_comm, mul_assoc]

end
end Masullo
