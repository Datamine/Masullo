import WeilOpenSubgroup
import LCAFourierInversion

open Filter Function MeasureTheory Set Topology
open scoped ENNReal ZeroAtInfty

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]

local instance quotientMeasurableSpace : MeasurableSpace (G ⧸ H) := borel _
local instance quotientBorelSpace : BorelSpace (G ⧸ H) := ⟨rfl⟩

variable (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ μH ν)

include hH hν

/-- The Fourier integral of the Weil average is the restriction of the ambient
Fourier integral to characters trivial on the subgroup. -/
theorem weilQuotient_fourier {f : G → ℂ} (hf : Integrable f μ) :
    let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    ∀ χ : PontryaginDual (G ⧸ H),
      lcaFourier ν (lcaCosetIntegral H μH f) χ = lcaFourier μ f (PontryaginDual.map q χ) := by
  intro q χ
  let g (x : G) := f x * star (χ (q x) : ℂ)
  have hg : Integrable g μ := integrable_fourierIntegrand μ hf (PontryaginDual.map q χ)
  have h := (weilQuotientIntegral_L1 H hH μ μH ν hν hg).2.2
  change (∫ y, lcaCosetIntegral H μH f y * star (χ y : ℂ) ∂ν) = ∫ x, g x ∂μ
  rw [h]
  apply integral_congr_ae
  exact .of_forall fun y ↦ by
    change lcaCosetIntegral H μH f y * star (χ y : ℂ) = lcaCosetIntegral H μH g y
    rw [lcaCosetIntegral, ← integral_mul_const]
    change (∫ z : H, f (y.out * (z : G)) * star (χ y : ℂ) ∂μH) =
      ∫ z : H, g (y.out * (z : G)) ∂μH
    apply integral_congr_ae
    exact .of_forall fun z ↦ by
      have hq : q (y.out * (z : G)) = y := by
        change QuotientGroup.mk (y.out * (z : G)) = y
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (z : G)).2 z.property,
          mul_one]
        exact Quotient.out_eq' y
      change _ = f (y.out * (z : G)) * star (χ (q (y.out * (z : G))) : ℂ)
      rw [hq]

/-- A quotient-null set pulls back to a null set for each finite-measure
restriction of Haar measure on the ambient group. -/
theorem weilQuotient_ae_restrict {p : (G ⧸ H) → Prop} (hp : ∀ᵐ q ∂ν, p q)
    {A : Set G} (hA : MeasurableSet A) (hAf : μ A ≠ ⊤) :
    ∀ᵐ x ∂μ.restrict A, p (QuotientGroup.mk x) := by
  obtain ⟨S, hS, hmS, h0S⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  let q : G → G ⧸ H := QuotientGroup.mk
  let B := q ⁻¹' S ∩ A
  have hq : Measurable q := QuotientGroup.continuous_mk.measurable
  have hB : MeasurableSet B := (hq hmS).inter hA
  have hBf : μ B ≠ ⊤ := ne_top_of_le_ne_top hAf (measure_mono inter_subset_right)
  let f : G → ℂ := B.indicator (fun _ ↦ 1)
  have hf : Integrable f μ := memLp_one_iff_integrable.mp
    (memLp_indicator_const (μ := μ) 1 hB (1 : ℂ) (.inr hBf))
  have hf0 : ∀ᵐ y ∂ν, lcaCosetIntegral H μH f y = 0 := by
    filter_upwards [show ∀ᵐ y ∂ν, y ∉ S from ae_iff.mpr (by simpa using h0S)] with y hy
    unfold lcaCosetIntegral
    rw [show (fun z : H ↦ f (y.out * (z : G))) = 0 from funext fun z ↦ by
      have hk : q (y.out * (z : G)) = y := by
        change QuotientGroup.mk (y.out * (z : G)) = y
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (z : G)).2 z.property,
          mul_one]
        exact Quotient.out_eq' y
      exact indicator_of_notMem (fun he ↦ hy (hk ▸ (show q (y.out * (z : G)) ∈ S from he.1))) _]
    exact integral_zero _ _
  have he := (weilQuotientIntegral_L1 H hH μ μH ν hν hf).2.2.trans
    ((integral_congr_ae hf0).trans (integral_zero _ _))
  change ∫ x, B.indicator (fun _ ↦ (1 : ℂ)) x ∂μ = 0 at he
  rw [integral_indicator hB, setIntegral_const, Complex.real_smul, mul_one,
    Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff] at he
  have h0B := he.resolve_right hBf
  apply ae_iff.mpr
  refine measure_mono_null (show {x | ¬ p (q x)} ⊆ q ⁻¹' S from fun x hx ↦ hS hx) ?_
  rw [Measure.restrict_apply (hq hmS)]
  exact h0B

/-- Inner regularity on all Borel sets upgrades the local pullback
of quotient-almost-everywhere statements to the entire ambient measure. -/
theorem weilQuotient_ae [μ.InnerRegular] {p : (G ⧸ H) → Prop} (hp : ∀ᵐ q ∂ν, p q) :
    ∀ᵐ x ∂μ, p (QuotientGroup.mk x) := by
  obtain ⟨S, hS, hmS, h0S⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  let q : G → G ⧸ H := QuotientGroup.mk
  have hq : Measurable q := QuotientGroup.continuous_mk.measurable
  apply ae_iff.mpr
  refine measure_mono_null (show {x | ¬ p (q x)} ⊆ q ⁻¹' S from fun x hx ↦ hS hx) ?_
  rw [(hq hmS).measure_eq_iSup_isCompact μ]
  refine le_antisymm (iSup_le fun K ↦ iSup_le fun hKS ↦ iSup_le fun hK ↦ ?_) bot_le
  have hOutside : ∀ᵐ y ∂ν, y ∉ S := ae_iff.mpr (by simpa using h0S)
  have h := weilQuotient_ae_restrict H hH μ μH ν hν hOutside
    hK.isClosed.measurableSet (hK.measure_lt_top (μ := μ)).ne
  have h0 : μ.restrict K (q ⁻¹' S) = 0 := by
    have hz := ae_iff.mp h
    have hs : {x : G | ¬ (QuotientGroup.mk x : G ⧸ H) ∉ S} = q ⁻¹' S := by
      ext x
      change (¬ ¬ (QuotientGroup.mk x : G ⧸ H) ∈ S) ↔ (QuotientGroup.mk x : G ⧸ H) ∈ S
      exact not_not
    exact hs ▸ hz
  rw [Measure.restrict_apply (hq hmS), inter_eq_right.mpr hKS] at h0
  exact h0.le

local instance dualQuotientMeasurableSpace : MeasurableSpace (PontryaginDual (G ⧸ H)) :=
  borel _
local instance dualQuotientBorelSpace : BorelSpace (PontryaginDual (G ⧸ H)) := ⟨rfl⟩

/-- Poisson summation on the quotient, with the global almost-everywhere form
on the quotient and the ambient form on finite-measure restrictions. -/
theorem weilQuotient_poisson
    (νDual : Measure (PontryaginDual (G ⧸ H))) (hνDual : IsLCAPlancherelMeasure ν νDual)
    {f : G → ℂ} (hf : Integrable f μ) :
    let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    let u : PontryaginDual (G ⧸ H) → ℂ := fun χ ↦ lcaFourier μ f (PontryaginDual.map q χ)
    Integrable (lcaCosetIntegral H μH f) ν ∧
    (∃ F : C₀(PontryaginDual (G ⧸ H), ℂ), ∀ χ, F χ = u χ) ∧
    (Integrable u νDual →
      ∃ P : C₀(G ⧸ H, ℂ),
        (P : G ⧸ H → ℂ) =ᵐ[ν] lcaCosetIntegral H μH f ∧
        (∀ x : G, P (q x) = ∫ χ, u χ * (χ (q x) : ℂ) ∂νDual) ∧
        (∀ A : Set G, MeasurableSet A → μ A ≠ ⊤ →
          ∀ᵐ x ∂μ.restrict A, (∫ h : H, f (x * (h : G)) ∂μH) = P (q x)) ∧
        (Continuous (fun x : G ↦ ∫ h : H, f (x * (h : G)) ∂μH) →
          ∀ x : G, (∫ h : H, f (x * (h : G)) ∂μH) = P (q x))) := by
  intro q u
  letI : IsClosed (H : Set G) := hH
  letI : ν.IsHaarMeasure := hν.1
  letI : ν.Regular := hν.2.1
  letI : νDual.IsHaarMeasure := hνDual.1
  letI : νDual.Regular := hνDual.2.1
  have hq (x : G) : q x = QuotientGroup.mk x := rfl
  have hAvg := (weilQuotientIntegral_L1 H hH μ μH ν hν hf).2.1
  have hu : lcaFourier ν (lcaCosetIntegral H μH f) = u :=
    funext (weilQuotient_fourier H hH μ μH ν hν hf)
  have hC : ∃ F : C₀(PontryaginDual (G ⧸ H), ℂ), ∀ χ, F χ = u χ := by
    rw [← hu]
    exact lcaFourier_zeroAtInfty ν hAvg
  refine ⟨hAvg, hC, fun hInt ↦ ?_⟩
  obtain ⟨U, hU, -⟩ := lcaFourier_unitary ν νDual hνDual
  obtain ⟨P, hP, hPval⟩ := lcaFourier_inversion_L1 ν νDual U hU hAvg (hu.symm ▸ hInt)
  refine ⟨P, hP, fun x ↦ ?_, ?_, ?_⟩
  · rw [hPval, hu]
  · intro A hA hAf
    filter_upwards [weilQuotient_ae_restrict H hH μ μH ν hν hP hA hAf] with x hx
    rw [← lcaCosetIntegral_mk H μH f x, hq]
    exact hx.symm
  · intro h
    have hAvgC : Continuous (lcaCosetIntegral H μH f) := by
      apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
      exact h.congr (fun x ↦ (lcaCosetIntegral_mk H μH f x).symm)
    have hEq := Measure.eq_of_ae_eq hP P.continuous hAvgC
    intro x
    rw [← lcaCosetIntegral_mk H μH f x, hq]
    exact (congrFun hEq _).symm

local instance annihilatorMeasurableSpace : MeasurableSpace (lcaAnnihilator H) := borel _
local instance annihilatorBorelSpace : BorelSpace (lcaAnnihilator H) := ⟨rfl⟩

/-- D.1.2.7 in the manuscript's annihilator coordinates. The Haar measure on
the annihilator is transported from the prescribed quotient Plancherel measure. -/
theorem weilQuotient_poisson_annihilator
    (νDual : Measure (PontryaginDual (G ⧸ H))) (hνDual : IsLCAPlancherelMeasure ν νDual)
    {f : G → ℂ} (hf : Integrable f μ) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H,
      let νA := Measure.map e νDual
      νA.IsHaarMeasure ∧ νA.Regular ∧
      (∀ χ x, (e χ).val x = χ (QuotientGroup.mk x)) ∧
      (∃ Z : C₀(lcaAnnihilator H, ℂ), ∀ χ, Z χ = lcaFourier μ f χ.val) ∧
      (Integrable (fun χ : lcaAnnihilator H ↦ lcaFourier μ f χ.val) νA →
        ∃ P : C₀(G ⧸ H, ℂ),
          (P : G ⧸ H → ℂ) =ᵐ[ν] lcaCosetIntegral H μH f ∧
          (∀ x : G, P (QuotientGroup.mk x) =
            ∫ χ : lcaAnnihilator H, lcaFourier μ f χ.val * (χ.val x : ℂ) ∂νA) ∧
          (∀ A : Set G, MeasurableSet A → μ A ≠ ⊤ →
            ∀ᵐ x ∂μ.restrict A, (∫ h : H, f (x * (h : G)) ∂μH) = P (QuotientGroup.mk x)) ∧
          (Continuous (fun x : G ↦ ∫ h : H, f (x * (h : G)) ∂μH) →
            ∀ x : G, (∫ h : H, f (x * (h : G)) ∂μH) = P (QuotientGroup.mk x))) := by
  letI : IsClosed (H : Set G) := hH
  letI : νDual.IsHaarMeasure := hνDual.1
  letI : νDual.Regular := hνDual.2.1
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator H hH
  let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  let u (χ : PontryaginDual (G ⧸ H)) := lcaFourier μ f (PontryaginDual.map q χ)
  have hχ (χ : PontryaginDual (G ⧸ H)) : (e χ).val = PontryaginDual.map q χ :=
    PontryaginDual.ext (he χ)
  obtain ⟨-, ⟨F, hF⟩, hPoisson⟩ := weilQuotient_poisson H hH μ μH ν hν νDual hνDual hf
  let Z := F.comp e.symm.toHomeomorph.toCocompactMap
  refine ⟨e, e.isHaarMeasure_map νDual, Measure.Regular.map e.toHomeomorph, he, ⟨Z, ?_⟩, ?_⟩
  · intro χ
    change F (e.symm χ) = lcaFourier μ f χ.val
    rw [hF]
    change lcaFourier μ f (PontryaginDual.map q (e.symm χ)) = _
    rw [← hχ, e.apply_symm_apply]
  · intro h
    have hInt : Integrable u νDual := by
      have hi := (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv _).mp h
      refine hi.congr (.of_forall fun χ ↦ ?_)
      change lcaFourier μ f (e χ).val = lcaFourier μ f (PontryaginDual.map q χ)
      rw [hχ]
    obtain ⟨P, hP, hVal, hAE, hC⟩ := hPoisson hInt
    refine ⟨P, hP, fun x ↦ ?_, hAE, hC⟩
    change P (q x) = _
    rw [hVal]
    change (∫ χ, u χ * (χ (q x) : ℂ) ∂νDual) =
      ∫ χ : lcaAnnihilator H, lcaFourier μ f χ.val * (χ.val x : ℂ)
        ∂Measure.map e.toHomeomorph.toMeasurableEquiv νDual
    rw [integral_map_equiv e.toHomeomorph.toMeasurableEquiv]
    apply integral_congr_ae
    exact .of_forall fun χ ↦ by
      change u χ * (χ (q x) : ℂ) = lcaFourier μ f (e χ).val * ((e χ).val x : ℂ)
      rw [he, hχ]
      rfl

omit hH hν in
/-- In an uncountable discrete extension of the real group, outer-regular
ambient Haar measure gives the inverse image of a singleton infinite mass. -/
theorem outerRegular_haar_uncountable_slice {D : Type*} [CommGroup D]
    [TopologicalSpace D] [DiscreteTopology D] [Uncountable D]
    [MeasurableSpace (D × Multiplicative ℝ)] [BorelSpace (D × Multiplicative ℝ)]
    (m : Measure (D × Multiplicative ℝ)) [m.IsHaarMeasure] [m.OuterRegular] :
    m (univ ×ˢ ({1} : Set (Multiplicative ℝ))) = ⊤ := by
  by_contra h
  obtain ⟨U, hUsub, hU, hUfin⟩ :=
    (univ ×ˢ ({1} : Set (Multiplicative ℝ))).exists_isOpen_lt_of_lt (μ := m) ⊤ (lt_top_iff_ne_top.mpr h)
  letI : IsFiniteMeasure (m.restrict U) := isFiniteMeasure_restrict.mpr hUfin.ne
  let A (d : D) : Set (D × Multiplicative ℝ) := U ∩ ({d} : Set D) ×ˢ univ
  have hOpen (d : D) : IsOpen (A d) := hU.inter ((isOpen_discrete {d}).prod isOpen_univ)
  have hNonempty (d : D) : (A d).Nonempty :=
    ⟨(d, 1), hUsub ⟨mem_univ _, mem_singleton _⟩, mem_singleton _, mem_univ _⟩
  have hDisj : Pairwise (Disjoint on A) := by
    intro d e hde
    exact disjoint_left.mpr fun x hx hy =>
      hde ((mem_singleton_iff.mp hx.2.1).symm.trans (mem_singleton_iff.mp hy.2.1))
  have hCount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := m.restrict U)
    (fun d ↦ (hOpen d).measurableSet) hDisj
  have hAll : {d | 0 < m.restrict U (A d)} = (univ : Set D) := by
    apply eq_univ_of_forall
    intro d
    change 0 < m.restrict U (A d)
    rw [Measure.restrict_apply (hOpen d).measurableSet, inter_eq_left.mpr inter_subset_left]
    exact (hOpen d).measure_pos m (hNonempty d)
  rw [hAll, countable_univ_iff] at hCount
  exact not_countable hCount

end
end Masullo
