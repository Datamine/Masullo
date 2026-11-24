/-
The dual quotient pairing adapts RiemannMasullo AppD_SchwartzBruhat/Sec1c.lean
at 1d8742feacca560ae3a2beedfb0e743b1efd8bfe (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import BruhatFourierDerivative
import Mathlib.Algebra.Category.Grp.Injective

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Characters on the annihilator of the physical kernel descend to the
physical stage, and this restriction is constant on the dual kernel cosets. -/
theorem LCAStructuralPair.dualStagePairing (P : LCAStructuralPair G) :
    ∃ d : P.dual.StageQuotient →ₜ* PontryaginDual P.StageQuotient,
      ∀ (χ : P.dual.upper.val) (x : P.upper.val),
        d (QuotientGroup.mk χ) (QuotientGroup.mk x) = χ.val x.val := by
  let J := P.upper.val
  let N := P.kernel.comap J.subtype
  let H := P.dual.upper.val
  let M := P.dual.kernel.comap H.subtype
  letI : LocallyCompactSpace J := P.upper.property.1.locallyCompactSpace
  let r := PontryaginDual.map (⟨J.subtype, continuous_subtype_val⟩ : J →ₜ* G)
  have hres (χ : H) : r χ.val ∈ lcaAnnihilator N :=
    (mem_lcaAnnihilator_iff _ _).mpr fun x =>
      (mem_lcaAnnihilator_iff P.kernel χ.val).mp χ.property ⟨x.val.val, x.property⟩
  let R : H →ₜ* lcaAnnihilator N :=
    ⟨(r.toMonoidHom.comp H.subtype).codRestrict _ hres,
      (r.continuous.comp continuous_subtype_val).subtype_mk hres⟩
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator N
    (P.kernel_closed.preimage continuous_subtype_val)
  let t : H →ₜ* PontryaginDual P.StageQuotient := (e.symm : _ →ₜ* _).comp R
  have ht (χ : H) (x : J) : t χ (QuotientGroup.mk x) = χ.val x.val := by
    rw [← he]
    change (e (e.symm (R χ))).val x = _
    rw [e.apply_symm_apply]
    rfl
  have hk : M ≤ t.toMonoidHom.ker := by
    intro χ hχ
    change χ.val ∈ lcaAnnihilator J at hχ
    apply PontryaginDual.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact (ht χ x).trans ((mem_lcaAnnihilator_iff J χ.val).mp hχ x)
  let d := QuotientGroup.lift M t.toMonoidHom hk
  have hd : Continuous d := (QuotientGroup.isQuotientMap_mk M).continuous_iff.mpr t.continuous
  exact ⟨⟨d, hd⟩, ht⟩

private theorem extend_real_frequency_open {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (J : Subgroup A) (hJ : IsOpen (J : Set A))
    (ρ : J →ₜ* Multiplicative ℝ) :
    ∃ τ : A →ₜ* Multiplicative ℝ, ∀ x : J, τ x.val = ρ x := by
  obtain ⟨L, hL⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    J.subtype.toAdditive (show Injective J.subtype.toAdditive from Subtype.val_injective)
    ρ.toMonoidHom.toAdditiveLeft
  let τ := L.toMultiplicativeRight
  have he (x : J) : τ x.val = ρ x := DFunLike.congr_fun hL (Additive.ofMul x)
  have hc : Continuous τ := by
    apply continuous_of_continuousAt_one
    have hn : Filter.map Subtype.val (𝓝 (1 : J)) = 𝓝 (1 : A) :=
      hJ.isOpenEmbedding_subtypeVal.map_nhds_eq 1
    rw [ContinuousAt, map_one, ← hn, tendsto_map'_iff]
    have ht : Tendsto ρ (𝓝 (1 : J)) (𝓝 1) := ρ.continuous.tendsto' 1 1 (map_one ρ)
    exact ht.congr (fun x => (he x).symm)
  exact ⟨⟨τ, hc⟩, he⟩

omit [IsTopologicalGroup G] [T2Space G] in
/-- A one-parameter subgroup of the dual is an exponential with a continuous
real frequency on the physical group. -/
theorem exists_frequency_dualDirection (a : Multiplicative ℝ →ₜ* PontryaginDual G) :
    ∃ ρ : G →ₜ* Multiplicative ℝ, ∀ t : ℝ, ∀ x : G,
      a (Multiplicative.ofAdd t) x = Circle.exp ((ρ x).toAdd * t) := by
  let b := pontryaginBidualEval (G := G)
  let c : PontryaginDual (PontryaginDual G) →ₜ* Multiplicative ℝ :=
    ⟨characterSlope a, characterSlope_continuous a⟩
  exact ⟨c.comp b, fun t x => characterSlope_eq_exp a (b x) t⟩

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-- The Fourier transform on the dual upper subgroup is the Fourier pairing
on the physical open subgroup, evaluated through the two stage quotients. -/
theorem BruhatSchwartzStage.fourier_quotientIntegral
    (p : BruhatSchwartzStage G) (s : p.Space)
    (d : p.1.dual.StageQuotient →ₜ* PontryaginDual p.1.StageQuotient)
    (hd : ∀ (χ : p.1.dual.upper.val) (x : p.1.upper.val),
      d (QuotientGroup.mk χ) (QuotientGroup.mk x) = χ.val x.val)
    (χ : p.1.dual.upper.val) :
    lcaFourier μ (p.realize s) χ.val =
      ∫ x : p.1.upper.val, s (p.1.stageCoordinates p.2 x).toAdd *
        star (d (QuotientGroup.mk χ) (QuotientGroup.mk x) : ℂ) ∂μ.comap p.1.upper.val.subtype := by
  let f (x : G) := p.realize s x * star (χ.val x : ℂ)
  change (∫ x, f x ∂μ) = _
  have hzero (x : G) (hx : x ∉ (p.1.upper.val : Set G)) : f x = 0 := by
    simp [f, p.1.realizeSchwartz_apply_of_not_mem p.2 s x hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← integral_subtype_comap p.1.upper.property.1.measurableSet f]
  apply integral_congr_ae
  exact .of_forall fun x => by
    change p.realize s x.val * star (χ.val x.val : ℂ) = _
    rw [p.1.realizeSchwartz_apply_of_mem p.2 s x]
    exact congrArg (fun z : Circle => s (p.1.stageCoordinates p.2 x).toAdd * star (z : ℂ))
      (hd χ x).symm

variable [μ.IsHaarMeasure] [μ.Regular]

set_option maxHeartbeats 800000 in
/-- Every polynomial in the real and lattice coordinates of the dual stage
bounds a weighted Fourier integral of a physical stage test. -/
theorem BruhatSchwartzStage.fourier_polynomial_bound (p : BruhatSchwartzStage G)
    (d : ElementaryLCAPresentation p.1.dual.StageQuotient) (s : p.Space)
    (P : MvPolynomial (Fin d.realDim ⊕ Fin d.latticeRank) ℂ) :
    ∃ C : ℝ, ∀ χ : p.1.dual.upper.val,
      let y := (p.1.dual.stageCoordinates d χ).toAdd
      ‖MvPolynomial.eval (Sum.elim (fun i => (y.1 i : ℂ))
        (fun i => ((y.2.2.1 i : ℤ) : ℂ))) P * lcaFourier μ (p.realize s) χ.val‖ ≤ C := by
  let H := p.1.dual.upper.val
  let y (χ : H) := (p.1.dual.stageCoordinates d χ).toAdd
  have hy : Continuous y := (p.1.dual.stageCoordinates d).continuous
  have hya (χ ψ : H) : y (χ * ψ) = y χ + y ψ :=
    congrArg Multiplicative.toAdd (map_mul (p.1.dual.stageCoordinates d) χ ψ)
  let r (i : Fin d.realDim ⊕ Fin d.latticeRank) (χ : H) : ℝ :=
    Sum.elim (fun j => (y χ).1 j) (fun j => ((y χ).2.2.1 j : ℝ)) i
  have hr (i) : Continuous (r i) := by
    cases i with
    | inl j => exact (PiLp.continuous_apply 2 _ j).comp hy.fst
    | inr j =>
      exact (continuous_of_discreteTopology : Continuous (fun a : ℤ => (a : ℝ))).comp
        ((continuous_apply j).comp hy.snd.snd.fst)
  have hra (i) (χ ψ : H) : r i (χ * ψ) = r i χ + r i ψ := by
    cases i <;> simp [r, hya]
  let ρ (i) : H →ₜ* Multiplicative ℝ :=
    { toFun := fun χ => Multiplicative.ofAdd (r i χ)
      map_one' := by
        have h := hra i 1 1
        rw [one_mul] at h
        have hzero : r i 1 = 0 := by linarith
        exact congrArg Multiplicative.ofAdd hzero
      map_mul' := fun χ ψ => congrArg Multiplicative.ofAdd (hra i χ ψ)
      continuous_toFun := continuous_ofAdd.comp (hr i) }
  choose τ hτ using fun i => extend_real_frequency_open H p.1.dual.upper.property.1 (ρ i)
  obtain ⟨A, hA⟩ := exists_bruhatFourier_polynomial μ τ P
  let u := A (p.inclusion s)
  refine ⟨∫ x, ‖u.val x‖ ∂μ, fun χ => ?_⟩
  have he (i : Fin d.realDim ⊕ Fin d.latticeRank) :
      ((τ i χ.val).toAdd : ℂ) =
        Sum.elim (fun i => ((y χ).1 i : ℂ)) (fun i => (((y χ).2.2.1 i : ℤ) : ℂ)) i := by
    rw [hτ]
    change (r i χ : ℂ) = _
    cases i <;> simp [r]
  have hf := hA (p.inclusion s) χ.val
  rw [show (fun i => ((τ i χ.val).toAdd : ℂ)) = _ from funext he] at hf
  exact (congrArg norm hf.symm).le.trans (norm_lcaFourier_le_integral_norm μ u.val χ.val)

end
end Masullo
