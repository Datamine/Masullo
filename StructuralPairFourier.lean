import LCAFourierInversion

open Filter Function MeasureTheory Set Topology
open scoped ZeroAtInfty

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (ν : Measure (PontryaginDual G))

/-- Invariance under a closed subgroup is equivalent to Fourier support in its
annihilator. Inversion is applied to the continuous representative. -/
theorem lcaFourier_support_iff_invariant (hν : IsLCAPlancherelMeasure μ ν)
    (H : Subgroup G) {f : G → ℂ} (hc : Continuous f) (hf : Integrable f μ)
    (hF : Integrable (lcaFourier μ f) ν) :
    Function.support (lcaFourier μ f) ⊆ lcaAnnihilator H ↔
      ∀ h : H, ∀ x : G, f (h.val * x) = f x := by
  obtain ⟨F, hFf, hformula⟩ := lcaFourier_plancherel_inversion μ ν hν hf hF
  have hEq : (F : G → ℂ) = f := Measure.eq_of_ae_eq hFf F.continuous hc
  rw [hEq] at hformula
  constructor
  · intro hSupport h x
    rw [hformula, hformula x]
    apply integral_congr_ae
    exact .of_forall fun χ ↦ by
      by_cases hχ : lcaFourier μ f χ = 0
      · simp [hχ]
      · have hone : χ h.val = 1 :=
          (mem_lcaAnnihilator_iff H χ).mp (hSupport hχ) h
        change lcaFourier μ f χ * (χ (h.val * x) : ℂ) = _
        rw [map_mul, hone, one_mul]
  · intro hInv χ hχ
    apply (mem_lcaAnnihilator_iff H χ).mpr
    intro h
    have htr := lcaFourier_translate μ f h.val χ
    rw [show (fun x ↦ f (h.val * x)) = f from funext (hInv h)] at htr
    apply Subtype.ext
    change (χ h.val : ℂ) = (1 : ℂ)
    exact mul_right_cancel₀ hχ (htr.symm.trans (one_mul _).symm)

/-- Support in a closed subgroup is equivalent to invariance of the Fourier
transform under translation by the annihilator. -/
theorem lcaFourier_invariant_iff_support (hν : IsLCAPlancherelMeasure μ ν)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) {f : G → ℂ}
    (hc : Continuous f) (hf : Integrable f μ) (hF : Integrable (lcaFourier μ f) ν) :
    (∀ ψ : lcaAnnihilator H, ∀ χ : PontryaginDual G,
      lcaFourier μ f (ψ.val * χ) = lcaFourier μ f χ) ↔
      Function.support f ⊆ H := by
  constructor
  · intro hInv x hx
    obtain ⟨F, hFf, hformula⟩ := lcaFourier_plancherel_inversion μ ν hν hf hF
    have hEq : (F : G → ℂ) = f := Measure.eq_of_ae_eq hFf F.continuous hc
    rw [hEq] at hformula
    letI : ν.IsHaarMeasure := hν.1
    rw [← lcaDualAnnihilator_annihilator H hH]
    apply (mem_lcaDualAnnihilator_iff (lcaAnnihilator H) x).mpr
    intro ψ
    have hmul : (ψ.val x : ℂ) * f x = f x := calc
      _ = ∫ χ, lcaFourier μ f (ψ.val * χ) * ((ψ.val * χ) x : ℂ) ∂ν := by
        rw [hformula, ← integral_const_mul]
        apply integral_congr_ae
        exact .of_forall fun χ ↦ by
          change (ψ.val x : ℂ) * (lcaFourier μ f χ * (χ x : ℂ)) =
            lcaFourier μ f (ψ.val * χ) * ((ψ.val * χ) x : ℂ)
          rw [hInv ψ χ]
          change (ψ.val x : ℂ) * (lcaFourier μ f χ * (χ x : ℂ)) =
            lcaFourier μ f χ * ((ψ.val x * χ x : Circle) : ℂ)
          rw [Circle.coe_mul]
          ring
      _ = ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν :=
        integral_mul_left_eq_self (μ := ν)
          (fun χ : PontryaginDual G ↦ lcaFourier μ f χ * (χ x : ℂ)) ψ.val
      _ = _ := (hformula x).symm
    apply Subtype.ext
    change (ψ.val x : ℂ) = (1 : ℂ)
    exact mul_right_cancel₀ hx (hmul.trans (one_mul _).symm)
  · intro hSupport ψ χ
    unfold lcaFourier
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      by_cases hx : f x = 0
      · simp [hx]
      · have hψx := (mem_lcaAnnihilator_iff H ψ.val).mp ψ.property ⟨x, hSupport hx⟩
        change f x * star (((ψ.val x * χ x : Circle) : ℂ)) = _
        change ψ.val x = 1 at hψx
        rw [hψx, one_mul]

/-- Corrected D.1.5.2(3). A test with integrable Fourier transform has a unique
continuous representative, on which both support–invariance comparisons hold. -/
theorem lcaFourier_structural_representative (hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (hF : Integrable (lcaFourier μ f) ν) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] f ∧ lcaFourier μ F = lcaFourier μ f ∧
      (∀ H : Subgroup G, Function.support (lcaFourier μ f) ⊆ lcaAnnihilator H ↔
        ∀ h : H, ∀ x : G, F (h.val * x) = F x) ∧
      (∀ H : Subgroup G, IsClosed (H : Set G) →
        ((∀ ψ : lcaAnnihilator H, ∀ χ : PontryaginDual G,
          lcaFourier μ f (ψ.val * χ) = lcaFourier μ f χ) ↔ Function.support F ⊆ H)) ∧
      (∀ F' : C₀(G, ℂ), (F' : G → ℂ) =ᵐ[μ] f → F' = F) := by
  obtain ⟨F, hEq, _⟩ := lcaFourier_plancherel_inversion μ ν hν hf hF
  have hL : lcaFourier μ F = lcaFourier μ f := by
    funext χ
    exact integral_congr_ae (hEq.mono fun x hx ↦
      congrArg (fun z : ℂ ↦ z * star (χ x : ℂ)) hx)
  have hInt : Integrable (F : G → ℂ) μ := hf.congr hEq.symm
  have hTransform : Integrable (lcaFourier μ F) ν := hL.symm ▸ hF
  refine ⟨F, hEq, hL, ?_, ?_, ?_⟩
  · intro H
    rw [← hL]
    exact lcaFourier_support_iff_invariant μ ν hν H F.continuous hInt hTransform
  · intro H hH
    rw [← hL]
    exact lcaFourier_invariant_iff_support μ ν hν H hH F.continuous hInt hTransform
  · intro F' hF'
    exact DFunLike.coe_injective (Measure.eq_of_ae_eq (hF'.trans hEq.symm)
      F'.continuous F.continuous)

end
end Masullo
