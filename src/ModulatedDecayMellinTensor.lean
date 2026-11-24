import CompletedInductiveTensorEquiv
import ModulatedDecayMellinProduct
import ModulatedDecayMellinEvaluation
import ModulatedDecayMellinInjectivity
import MellinBergman

set_option Elab.async false
set_option maxHeartbeats 1500000

open Function MeasureTheory Set Topology
open scoped TensorProduct

namespace Masullo
noncomputable section

section AngularFourier

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]

/-- Fourier transformation followed by inversion of the dual character
has the sign convention of the Fourier–Mellin integral. -/
theorem exists_bruhatFourier_inverted_equiv (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular] :
    ∃ F : BruhatSchwartz H ≃L[ℂ] BruhatSchwartz (PontryaginDual H),
      ∀ a ω, (F a).val ω = lcaFourier ν a.val ω⁻¹ := by
  let D := PontryaginDual H
  let e : D ≃ₜ* D :=
    { toFun := Inv.inv
      invFun := Inv.inv
      left_inv := inv_inv
      right_inv := inv_inv
      map_mul' := mul_inv
      continuous_toFun := continuous_inv
      continuous_invFun := continuous_inv }
  obtain ⟨U, hU⟩ := exists_bruhatFourier_equiv ν
  obtain ⟨J, hJ⟩ := exists_bruhatSchwartz_pullback_continuousLinear e
  have hJJ : J.comp J = ContinuousLinearMap.id ℂ (BruhatSchwartz D) := by
    ext a : 1
    apply Subtype.ext
    funext ω
    change (J (J a)).val ω = a.val ω
    rw [hJ, hJ]
    exact congrArg a.val (inv_inv ω)
  let V := ContinuousLinearEquiv.equivOfInverse' J J hJJ hJJ
  exact ⟨U.trans V, fun a ω => (hJ (U a) ω).trans (hU a ω⁻¹)⟩

end AngularFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [LocallyCompactSpace m.toMonoidHom.ker]

/-- The tensor product of the angular Fourier and radial Mellin equivalences
computes the Haar integral on the entire completed tensor. -/
theorem exists_decayMellin_completedTensorEquiv_of_multiplication
    (hm : IsProperMap m)
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsHaarMeasure] [IsFiniteMeasure ν]
    (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty)
    (L : (inductiveTensorModuleStructure (BruhatSchwartz K) (PositiveRealExponentialDecay I)).Completed
      ≃L[ℂ] ModulatedExponentialInductive m I)
    (hL : ∀ (a : BruhatSchwartz K) (r : PositiveRealExponentialDecay I) (g : G),
      (L ((inductiveTensorModuleStructure (BruhatSchwartz K) (PositiveRealExponentialDecay I)).incl
        (a ⊗ₜ[ℂ] r))).val g =
        a.val (modulatedKernelProjection m τ hτ g) * r.val (modulatedLog m g)) :
    let B := BruhatSchwartz (PontryaginDual K)
    let Q := SchwartzBergman I
    let P := inductiveTensorModuleStructure B Q
    ∃ F : BruhatSchwartz K ≃L[ℂ] B,
      (∀ a ω, (F a).val ω = lcaFourier ν a.val ω⁻¹) ∧
      ∃ (c : ℝ) (_ : 0 < c) (T : ModulatedExponentialInductive m I ≃L[ℂ] P.Completed),
        (∀ a r, T (L ((inductiveTensorModuleStructure (BruhatSchwartz K) (PositiveRealExponentialDecay I)).incl
          (a ⊗ₜ[ℂ] r))) = P.incl (F a ⊗ₜ[ℂ] positiveRealFourierMellin I hI hInt hne r)) ∧
        ∃ V : PontryaginDual K → {z : ℂ // z.re ∈ I} → P.Completed →L[ℂ] ℂ,
          (∀ ω z b q, V ω z (P.incl (b ⊗ₜ[ℂ] q)) = b.val ω * q.val z.val) ∧
          (∀ ω z f, decayMellinEvaluation μ m (ω.comp (modulatedKernelProjection m τ hτ)) z.val z.property f =
            c • V ω z (T f)) ∧
          Injective (fun w ω z => V ω z w) := by
  dsimp only
  let A := BruhatSchwartz K
  let R := PositiveRealExponentialDecay I
  let B := BruhatSchwartz (PontryaginDual K)
  let Q := SchwartzBergman I
  let D := inductiveTensorModuleStructure A R
  let P := inductiveTensorModuleStructure B Q
  letI : IsTopologicalAddGroup A := (PolynormableSpace.withSeminorms ℂ A).topologicalAddGroup
  letI : IsTopologicalAddGroup R := (PolynormableSpace.withSeminorms ℂ R).topologicalAddGroup
  letI : IsTopologicalAddGroup B := (PolynormableSpace.withSeminorms ℂ B).topologicalAddGroup
  letI : IsTopologicalAddGroup Q := (schwartzBergman_frechet I hI hInt hne).1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  obtain ⟨F, hF⟩ := exists_bruhatFourier_inverted_equiv ν
  let M := positiveRealFourierMellin I hI hInt hne
  let W : D.Completed ≃L[ℂ] P.Completed := completedInductiveTensor_congr F M
  let T : ModulatedExponentialInductive m I ≃L[ℂ] P.Completed := L.symm.trans W
  obtain ⟨c, hc, hp⟩ := decayMellin_fourier_mul_mellin_haar m τ hτ μ ν
  have hEval (ω : PontryaginDual K) (z : ℂ) (hz : z.re ∈ I) :
      ∃ V : P.Completed →L[ℂ] ℂ,
        (∀ b q, V (P.incl (b ⊗ₜ[ℂ] q)) = b.val ω * q.val z) ∧
        ∀ f, decayMellinEvaluation μ m (ω.comp (modulatedKernelProjection m τ hτ)) z hz f =
          c • V (T f) := by
    let v : B →L[ℂ] ℂ :=
      ⟨{ toFun := fun b => b.val ω, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
        bruhatSchwartz_continuous_eval ω⟩
    obtain ⟨u, hu⟩ := exists_schwartzBergman_jetEvaluation hI hInt z hz 0
    obtain ⟨V, hV⟩ := exists_completedInductiveTensor_pair v u
    have hV' (b : B) (q : Q) : V (P.incl (b ⊗ₜ[ℂ] q)) = b.val ω * q.val z := by
      simpa only [v, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mk', hu,
        iteratedDeriv_zero] using hV b q
    refine ⟨V, hV', ?_⟩
    let χ := ω.comp (modulatedKernelProjection m τ hτ)
    let E : ModulatedExponentialInductive m I →L[ℂ] ℂ :=
      ⟨decayMellinEvaluation μ m χ z hz, continuous_decayMellinEvaluation m μ χ z hz⟩
    have he : E.comp L.toContinuousLinearMap = c • (V.comp W.toContinuousLinearMap) := by
      apply D.continuousLinearMap_ext_on_tmul
      intro a r
      change (∫ g, decayMellinIntegrand m χ (L (D.incl (a ⊗ₜ[ℂ] r))) z g ∂μ) =
        c • V (W (D.incl (a ⊗ₜ[ℂ] r)))
      rw [completedInductiveTensor_congr_tmul, hV', hF, positiveRealFourierMellin_apply I hI hInt hne r z hz]
      exact hp (L (D.incl (a ⊗ₜ[ℂ] r))) a.val r.val ω z hne (hL a r)
    intro f
    have hf := DFunLike.congr_fun he (L.symm f)
    change E (L (L.symm f)) = c • V (W (L.symm f)) at hf
    rw [L.apply_symm_apply] at hf
    exact hf
  let V (ω : PontryaginDual K) (z : {z : ℂ // z.re ∈ I}) := (hEval ω z.val z.property).choose
  refine ⟨F, hF, c, hc, T, ?_, V, fun ω z => (hEval ω z.val z.property).choose_spec.1,
    fun ω z => (hEval ω z.val z.property).choose_spec.2, ?_⟩
  · intro a r
    change W (L.symm (L (D.incl (a ⊗ₜ[ℂ] r)))) = _
    rw [L.symm_apply_apply]
    exact completedInductiveTensor_congr_tmul F M a r
  · intro x y hxy
    obtain ⟨a, ha⟩ := hne
    apply T.symm.injective
    apply sub_eq_zero.mp
    apply decayMellinEvaluation_eq_zero_of_verticalLine m τ hτ hm μ ⟨a, ha⟩
    intro ω t
    let z : {z : ℂ // z.re ∈ I} := ⟨⟨a, t⟩, ha⟩
    let E := decayMellinEvaluation μ m (ω.comp (modulatedKernelProjection m τ hτ)) z.val z.property
    have hx : E (T.symm x) = c • V ω z x := by
      rw [show E (T.symm x) = c • V ω z (T (T.symm x)) from (hEval ω z.val z.property).choose_spec.2 _]
      rw [T.apply_symm_apply]
    have hy : E (T.symm y) = c • V ω z y := by
      rw [show E (T.symm y) = c • V ω z (T (T.symm y)) from (hEval ω z.val z.property).choose_spec.2 _]
      rw [T.apply_symm_apply]
    change E (T.symm x - T.symm y) = 0
    have hVxy : V ω z x = V ω z y := congrFun (congrFun hxy ω) z
    rw [map_sub, hx, hy, hVxy, sub_self]

end
end Masullo
