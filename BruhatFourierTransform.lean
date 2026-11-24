import BruhatFourierSmooth
import BruhatStageEvaluation
import BruhatEquivPullback
import StructuralFourierProjectors

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [μ.Regular] in
set_option maxHeartbeats 1200000 in
private theorem stage_integral_norm_seminorm (p : BruhatSchwartzStage G) :
    ∃ q : Seminorm ℂ p.Space, Continuous q ∧ ∀ s, q s = ∫ x, ‖p.realize s x‖ ∂μ := by
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
  obtain ⟨q, hq, heq⟩ := elementarySchwartz_withSeminorms_weightedOperatorLp_haar τ 1
  let i : List (ℂ × List (Multiplicative ℝ →ₜ* Multiplicative E)) ×
      List (ℂ × List (Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative E))) :=
    ([(1, [])], [(1, [])])
  refine ⟨q i, hq.continuous_seminorm i, fun s => ?_⟩
  have htest : (elementarySchwartz_weightedOperator i.1 i.2 s : E → ℂ) = s.val := by
    funext y
    simp [i, elementarySchwartz_weightedOperator_apply, elementaryDualWord, elementaryOrbitWord]
  have hs : Integrable s.val τ := by
    apply memLp_one_iff_integrable.mp
    exact htest ▸ elementarySchwartz_weightedOperator_memLp_haar τ 1 i.1 i.2 s
  have he : Continuous e := (p.1.stageCoordinates p.2).continuous
  rw [heq, htest, lpNorm_one_eq_integral_norm hs.aestronglyMeasurable,
    integral_map he.measurable.aemeasurable hs.norm.aestronglyMeasurable]
  have hsub : (∫ x : H, ‖s.val (e x)‖ ∂ν) = ∫ x in (H : Set G), ‖p.realize s x‖ ∂μ := by
    rw [← integral_subtype_comap p.1.upper.property.1.measurableSet]
    apply integral_congr_ae
    exact .of_forall fun x => congrArg norm (p.1.realizeSchwartz_apply_of_mem p.2 s x).symm
  refine hsub.trans (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_)
  rw [p.1.realizeSchwartz_apply_of_not_mem p.2 s x hx, norm_zero]

omit [μ.Regular] in
set_option maxHeartbeats 900000 in
/-- Pairing a Schwartz–Bruhat function with a fixed character is continuous
in the Schwartz–Bruhat topology. -/
theorem bruhatFourier_evaluation_continuous (χ : PontryaginDual G) :
    Continuous (fun f : BruhatSchwartz G => lcaFourier μ f.val χ) := by
  let B := (LinearMap.proj χ).comp (bruhatFourierLinear μ)
  change Continuous B
  apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage G => p.inclusion) B).mpr
  intro p
  obtain ⟨q, hq, heq⟩ := stage_integral_norm_seminorm μ p
  let T := B.comp p.inclusion
  change Continuous T
  apply continuous_of_continuousAt_zero T
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun f => norm_nonneg _) (fun f => ?_) (map_zero q ▸ hq.tendsto 0)
  change ‖lcaFourier μ (p.realize f) χ‖ ≤ q f
  rw [heq]
  exact norm_lcaFourier_le_integral_norm μ _ χ

set_option maxHeartbeats 2600000 in
/-- The Fourier integral acts continuously on the full locally convex
Schwartz–Bruhat spaces, using the actual structural-stage topology. -/
theorem exists_bruhatFourier_continuousLinear :
    ∃ F : BruhatSchwartz G →L[ℂ] BruhatSchwartz (PontryaginDual G),
      ∀ f χ, (F f).val χ = lcaFourier μ f.val χ := by
  let A (χ : PontryaginDual G) : BruhatSchwartz G →L[ℂ] ℂ :=
    ⟨(LinearMap.proj χ).comp (bruhatFourierLinear μ), bruhatFourier_evaluation_continuous μ χ⟩
  have hA (p : BruhatSchwartzStage G) :
      ∃ (p' : BruhatSchwartzStage (PontryaginDual G)) (B : p.Space →L[ℂ] p'.Space),
        ∀ s χ, p'.realize (B s) χ = A χ (p.inclusion s) := by
    obtain ⟨e⟩ := p.1.dual.quotient_elementary
    let p' : BruhatSchwartzStage (PontryaginDual G) := ⟨p.1.dual, e⟩
    let a (χ : PontryaginDual G) : p.Space →L[ℂ] ℂ := (A χ).comp p.inclusionCLM
    let r : PontryaginDual G → PontryaginDual G := id
    have hr (s : p.Space) : ∃ t : p'.Space, ∀ χ, p'.realize t (r χ) = a χ s := by
      obtain ⟨t, ht⟩ := p.exists_fourier_realize μ e s
      exact ⟨t, fun χ => congrFun ht χ⟩
    have h := bruhatStage_exists_clm_of_evaluation (G := G) (H := PontryaginDual G)
      (X := PontryaginDual G) p p' r Function.surjective_id a hr
    obtain ⟨B, hB⟩ := h
    exact ⟨p', B, hB⟩
  exact bruhatSchwartz_exists_clm_of_stage_evaluation (H := PontryaginDual G)
    id Function.surjective_id A hA

set_option maxHeartbeats 1400000 in
/-- Lemma D.1.6.19(2). Fourier transformation is a continuous linear
isomorphism of the actual Schwartz–Bruhat spaces, with the integral
formula on every test. -/
theorem exists_bruhatFourier_equiv :
    ∃ F : BruhatSchwartz G ≃L[ℂ] BruhatSchwartz (PontryaginDual G),
      ∀ f χ, (F f).val χ = lcaFourier μ f.val χ := by
  obtain ⟨F, hF⟩ := exists_bruhatFourier_continuousLinear μ
  letI : MeasurableSpace (PontryaginDual G) := borel _
  letI : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μ
  letI : ν.IsHaarMeasure := hν.1
  letI : ν.Regular := hν.2.1
  obtain ⟨U, hU⟩ := exists_bruhatFourier_continuousLinear ν
  obtain ⟨b, hb⟩ := pontryaginDual_bidual (G := G)
  let inv : G ≃ₜ* G :=
    { toFun := Inv.inv
      invFun := Inv.inv
      left_inv := inv_inv
      right_inv := inv_inv
      map_mul' := mul_inv
      continuous_toFun := continuous_inv
      continuous_invFun := continuous_inv }
  let e := inv.trans b
  obtain ⟨T, hT⟩ := exists_bruhatSchwartz_pullback_continuousLinear e
  let S := T.comp U
  have hS (g : BruhatSchwartz (PontryaginDual G)) (x : G) :
      (S g).val x = ∫ χ, g.val χ * (χ x : ℂ) ∂ν := by
    change (T (U g)).val x = _
    rw [hT, hU]
    apply integral_congr_ae
    exact .of_forall fun χ => by
      change g.val χ * star (b (x⁻¹) χ : ℂ) = _
      rw [hb, map_inv, Circle.coe_inv_eq_conj, Complex.star_def, starRingEnd_self_apply]
  have hSF (f : BruhatSchwartz G) : S (F f) = f := by
    have hf := bruhatSchwartz_integrable μ f
    have hu : Integrable (lcaFourier μ f.val) ν :=
      (bruhatSchwartz_integrable ν (F f)).congr (.of_forall (hF f))
    obtain ⟨g, hg, hg'⟩ := lcaFourier_plancherel_inversion μ ν hν hf hu
    have he : (g : G → ℂ) = f.val :=
      Measure.eq_of_ae_eq hg g.continuous (bruhatSchwartz_continuous f)
    apply Subtype.ext
    funext x
    rw [hS, ← he, hg']
    apply integral_congr_ae
    exact .of_forall fun χ => congrArg (· * (χ x : ℂ)) (hF f χ)
  have hS0 (g : BruhatSchwartz (PontryaginDual G)) (hg : S g = 0) : g = 0 := by
    have hz (ξ : PontryaginDual (PontryaginDual G)) : lcaFourier ν g.val ξ = 0 := by
      obtain ⟨x, rfl⟩ := e.surjective ξ
      have h := congrArg (fun f : BruhatSchwartz G => f.val x) hg
      change (T (U g)).val x = 0 at h
      rwa [hT, hU] at h
    have hae := ae_eq_zero_of_lcaFourier_eq_zero ν (bruhatSchwartz_integrable ν g) hz
    exact Subtype.ext (Measure.eq_of_ae_eq hae (bruhatSchwartz_continuous g) continuous_const)
  have hFS (g : BruhatSchwartz (PontryaginDual G)) : F (S g) = g := by
    apply sub_eq_zero.mp
    apply hS0
    rw [map_sub, hSF, sub_self]
  exact ⟨ContinuousLinearEquiv.equivOfInverse F S hSF hFS, hF⟩

/-- Corrected D.1.6.19(3) on all Schwartz–Bruhat tests. The normalized
structural averages intertwine, and the inverse formula includes the cutoff
of the original test to the open upper subgroup. -/
theorem bruhatFourier_structuralProjector
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (P : LCAStructuralPair G)
    (η : Measure P.kernel) [η.IsHaarMeasure] [IsProbabilityMeasure η] [η.Regular]
    (θ : Measure (lcaAnnihilator P.upper.val)) [θ.IsHaarMeasure]
    [IsProbabilityMeasure θ] [θ.Regular]
    (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)
    (f : BruhatSchwartz G) :
    let g := (P.upper.val : Set G).indicator (fun x => ∫ k : P.kernel, f.val (x * k.val) ∂η)
    lcaFourier μ g =
      (lcaAnnihilator P.kernel : Set (PontryaginDual G)).indicator
        (fun χ => ∫ ψ : lcaAnnihilator P.upper.val, lcaFourier μ f.val (χ * ψ.val) ∂θ) ∧
    ∀ x, g x = ∫ χ in (lcaAnnihilator P.kernel : Set (PontryaginDual G)),
      lcaFourier μ ((P.upper.val : Set G).indicator f.val) χ * (χ x : ℂ) ∂ν := by
  letI : ν.IsHaarMeasure := hν.1
  obtain ⟨F, hF⟩ := exists_bruhatFourier_continuousLinear μ
  have hf := bruhatSchwartz_integrable μ f
  have hfc := bruhatSchwartz_continuous f
  have hi : Integrable (lcaFourier μ f.val) ν :=
    (bruhatSchwartz_integrable ν (F f)).congr (.of_forall (hF f))
  exact ⟨(lcaFourier_structuralProjector μ P η θ hf hfc).2.2,
    structuralProjector_inverseFourier μ P η θ ν hν hf hfc hi⟩

end
end Masullo
