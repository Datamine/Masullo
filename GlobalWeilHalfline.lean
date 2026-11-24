import RadialWeilHalfline
import UnramifiedOrbitalQuotient

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped SchwartzMap NumberField

namespace Masullo
noncomputable section

private abbrev S := 𝓢(ℝ, ℂ)
variable (F : Type*) [Field F] [NumberField F]
private abbrev Q := IdeleClass F
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance globalHalflineQMeasure : MeasurableSpace (Q F) := borel _
local instance globalHalflineQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance globalHalflineQT2 : T2Space (Q F) := ideleClasses_hausdorff
local instance globalHalflineQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance globalHalflineQSecondCountable : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance globalHalflineKMeasure : MeasurableSpace (K F) := borel _
local instance globalHalflineKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance globalHalflineKCompact : CompactSpace (K F) := normOneIdeleClass_compact F

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (s : ℝ) (hs : 0 ≤ s)
local instance globalHalflineSplitHaar : (globalClassMeasure F ν).IsHaarMeasure :=
  globalClassMeasure_isHaar F ν

set_option maxHeartbeats 1200000 in
private theorem cutoff_globalWeil_range_closure_split
    (A : Finset (Place F)) (ω : PontryaginDual (K F))
    (ρ : Q F → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₁ : ∀ q, ρ q ≤ 1) (a : ℝ)
    (hSupp : ∀ q, (ideleClassLogNorm F q).toAdd < a → ρ q = 0) :
    let μ := globalClassMeasure F ν
    let H := globalOrbitalSobolevIsotype F μ s hs ω
    let P := globalWeilIsotypeProduct F μ s hs A ω
    let M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := cutoffOperator ρ hρ hρ₀ hρ₁
    closure (range fun u : H ↦ M (P u).val) = closure (range fun u : H ↦ M u.val) := by
  intro μ H P M
  let J := globalZeroLineSchwartzIsotype F ν s ω⁻¹
  let X := closure (range fun u : H ↦ M (P u).val)
  obtain ⟨ds, hd, hModel, _⟩ := exists_globalZeroLineWeil_shiftModel F ν s hs A ω
  have hCut (f g : S) (h : Set.EqOn f g (Ici a)) : M (J f) = M (J g) := by
    apply Lp.ext
    filter_upwards [cutoffOperator_ae ρ hρ hρ₀ hρ₁ (J f), cutoffOperator_ae ρ hρ hρ₀ hρ₁ (J g),
      globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ f,
      globalZeroLineSchwartzIsotype_ae_formula F ν s ω⁻¹ g] with q hf hg hf' hg'
    rw [hf,hg]
    by_cases hq : a ≤ (ideleClassLogNorm F q).toAdd
    · rw [hf',hg',h hq]
    · rw [hSupp q (lt_of_not_ge hq), Complex.ofReal_zero, zero_mul, zero_mul]
  have hCompact (f : S) (hf : HasCompactSupport f) : M (J f) ∈ X := by
    obtain ⟨g, _, hg⟩ := radialWeilDifferenceProduct_surjOn_halfline ds hd a f hf
    apply subset_closure
    refine ⟨globalWeilSchwartzTest F s hs ν ω g, ?_⟩
    have hm := hModel g
    change (P (globalWeilSchwartzTest F s hs ν ω g)).val = J (radialWeilDifferenceProduct ds g) at hm
    change M (P (globalWeilSchwartzTest F s hs ν ω g)).val = M (J f)
    rw [hm]
    exact hCut _ _ hg
  have hAll : MapsTo M (range J) X := by
    rintro _ ⟨f,rfl⟩
    have hconv := ((M.comp J).continuous.continuousAt.tendsto.comp (truncateSchwartz_tendsto f))
    exact isClosed_closure.mem_of_tendsto hconv
      (Eventually.of_forall fun n ↦ hCompact _ (truncateSchwartz_hasCompactSupport n f))
  apply le_antisymm
  · apply closure_mono
    rintro _ ⟨u,rfl⟩
    exact ⟨P u,rfl⟩
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨u,rfl⟩
    have hu := globalZeroLineSchwartzIsotype_dense_in_ambient F ν s hs ω u.val u.property.2
    exact (closure_minimal hAll (isClosed_closure.preimage M.continuous)) hu

variable (μ : Measure (Q F)) [μ.IsHaarMeasure]

set_option maxHeartbeats 1400000 in
/-- Cutting off below any fixed log modulus makes the closure of every finite
Weil-product image coincide with the cutoff closure of the full isotype. -/
theorem cutoff_globalWeil_range_closure
    (A : Finset (Place F)) (ω : PontryaginDual (K F))
    (ρ : Q F → ℝ) (hρ : Measurable ρ)
    (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₁ : ∀ q, ρ q ≤ 1) (a : ℝ)
    (hSupp : ∀ q, (ideleClassLogNorm F q).toAdd < a → ρ q = 0) :
    let H := globalOrbitalSobolevIsotype F μ s hs ω
    let P := globalWeilIsotypeProduct F μ s hs A ω
    let M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := cutoffOperator ρ hρ hρ₀ hρ₁
    closure (range fun u : H ↦ M (P u).val) = closure (range fun u : H ↦ M u.val) := by
  obtain ⟨η,hη,h⟩ := exists_globalClassMeasure_of_haar F μ
  letI : η.IsHaarMeasure := hη
  have go (σ : Measure (Q F)) [σ.IsHaarMeasure] (he : globalClassMeasure F η = σ) :
      let H := globalOrbitalSobolevIsotype F σ s hs ω
      let P := globalWeilIsotypeProduct F σ s hs A ω
      let M : Lp ℂ 2 σ →L[ℂ] Lp ℂ 2 σ := cutoffOperator ρ hρ hρ₀ hρ₁
      closure (range fun u : H ↦ M (P u).val) = closure (range fun u : H ↦ M u.val) := by
    subst σ
    exact cutoff_globalWeil_range_closure_split F η s hs A ω ρ hρ hρ₀ hρ₁ a hSupp
  exact go μ h

set_option maxHeartbeats 1400000 in
/-- An indicator supported on a measurable set invariant under the compact
norm-one group has closed image on the completed orbital isotype. -/
theorem isClosed_globalOrbitalIsotype_cutoff_range
    (ω : PontryaginDual (K F)) (U : Set (Q F)) (hU : MeasurableSet U)
    (hInv : ∀ (k : K F) (q : Q F), k.val⁻¹ * q ∈ U ↔ q ∈ U)
    (h₀ : ∀ q, 0 ≤ U.indicator (fun _ ↦ (1 : ℝ)) q)
    (h₁ : ∀ q, U.indicator (fun _ ↦ (1 : ℝ)) q ≤ 1) :
    let H := globalOrbitalSobolevIsotype F μ s hs ω
    let M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
      cutoffOperator _ (measurable_const.indicator hU) h₀ h₁
    IsClosed (range fun u : H ↦ M u.val) := by
  intro H M
  let L := Lp ℂ 2 μ
  let ρ := U.indicator (fun _ ↦ (1 : ℝ))
  let V := globalAmbientSobolevIsotype F ω μ 0 0 s hs
  let T (g : Q F) := hardySobolevMulTranslation μ (ideleClassLogNorm F)
    (ideleClassLogNorm_continuous F) 0 0 s hs g
  have hρ : Measurable ρ := measurable_const.indicator hU
  have hM (u : L) : (M u : Q F → ℂ) =ᵐ[μ] fun q ↦ (ρ q : ℂ) * u q :=
    cutoffOperator_ae ρ hρ h₀ h₁ u
  have hidem (u : L) : M (M u) = M u := by
    apply Lp.ext
    filter_upwards [hM u, hM (M u)] with q hq hqq
    rw [hqq,hq]
    by_cases h : q ∈ U <;> simp [ρ,h]
  have hcomm (k : K F) (u : L) : T k.val (M u) = M (T k.val u) := by
    let g : Q F := k.val
    let hshift := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving
    have ht (x : L) := hardySobolevMulTranslation_ae μ (ideleClassLogNorm F)
      (ideleClassLogNorm_continuous F) 0 0 s hs g x
    apply Lp.ext
    filter_upwards [ht (M u), hM (T g u), ht u, hshift.ae_eq_comp (hM u)] with q h₁q h₂q h₃q h₄q
    have he : ρ (g⁻¹ * q) = ρ q := by
      by_cases hq : q ∈ U
      · have hgq : g⁻¹ * q ∈ U := (hInv k q).mpr hq
        simp [ρ,hq,hgq]
      · have hgq : g⁻¹ * q ∉ U := fun h ↦ hq ((hInv k q).mp h)
        simp [ρ,hq,hgq]
    change M u (g⁻¹ * q) = (ρ (g⁻¹ * q) : ℂ) * u (g⁻¹ * q) at h₄q
    rw [h₁q,h₂q,h₃q,h₄q,he]
    ring
  have hRange : range (fun u : H ↦ M u.val) = (V : Set L) ∩ {u | M u = u} := by
    ext u
    constructor
    · rintro ⟨x,rfl⟩
      refine ⟨(mem_thetaCharacterSubspace _ _ _).mpr ?_,hidem _⟩
      intro k
      have hx := (mem_thetaCharacterSubspace _ _ _).mp x.property.2 k
      change T k.val (M x.val) = (ω k : ℂ) • M x.val
      rw [hcomm,hx,map_smul]
    · rintro ⟨hu,hfix⟩
      exact ⟨⟨u,globalThetaSobolevMap_zeroLine_dense_of_haar F μ s hs u,hu⟩,hfix⟩
  rw [hRange]
  exact (globalAmbientSobolevIsotype_isClosed F ω μ 0 0 s hs).inter
    (isClosed_eq M.continuous continuous_id)

omit [ν.IsHaarMeasure] in
set_option maxHeartbeats 1300000 in
/-- Both cutoffs used in §11.1.2 give the same closed image for each finite
unramified Weil product as for the full isotype. The parameter `b` is absent
for the positive cutoff and is `Λ` for the two-sided cutoff. -/
theorem cutoff_globalPrincipalValues_range_closure_eq_cutoff_range
    (A : Finset (Place F)) (ω : PontryaginDual (K F))
    (hA : ∀ v ∈ A, ω.comp (globalSobolevFiniteUnitInclusion F v) = 1)
    (Λ : ℝ) (hΛ : 0 < Λ) (b : Option ℝ) :
    let U : Set ℝ := Ici (Λ⁻¹) ∩ b.elim univ Iic
    let ρ : Q F → ℝ := ((ideleClassNorm F) ⁻¹' U).indicator (fun _ ↦ 1)
    ∃ (hρ : Measurable ρ) (hρ₀ : ∀ q, 0 ≤ ρ q) (hρ₁ : ∀ q, ρ q ≤ 1),
      let H := globalOrbitalSobolevIsotype F μ s hs ω
      let M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := cutoffOperator ρ hρ hρ₀ hρ₁
      closure (range fun u : H ↦ M (globalIsotypicPrincipalValues F μ s hs ω A u).val) =
        range (fun u : H ↦ M u.val) := by
  intro U ρ
  have hU : MeasurableSet U := by
    cases b with
    | none => exact measurableSet_Ici.inter MeasurableSet.univ
    | some y => exact measurableSet_Ici.inter measurableSet_Iic
  have hρ : Measurable ρ :=
    measurable_const.indicator ((ideleClassNorm_continuous F).measurable hU)
  have hρ₀ (q : Q F) : 0 ≤ ρ q := by
    by_cases hq : q ∈ (ideleClassNorm F) ⁻¹' U <;> simp [ρ, hq]
  have hρ₁ (q : Q F) : ρ q ≤ 1 := by
    by_cases hq : q ∈ (ideleClassNorm F) ⁻¹' U <;> simp [ρ, hq]
  refine ⟨hρ,hρ₀,hρ₁,?_⟩
  have hSupp (q : Q F) (hq : (ideleClassLogNorm F q).toAdd < Real.log (Λ⁻¹)) : ρ q = 0 := by
    change Real.log (ideleClassNorm F q) < Real.log (Λ⁻¹) at hq
    have hlt := (Real.log_lt_log_iff (ideleClassNorm_pos F q) (inv_pos.mpr hΛ)).mp hq
    apply indicator_of_notMem
    exact fun h ↦ hlt.not_ge ((show ideleClassNorm F q ∈ U from h).1)
  have hLeft := cutoff_globalWeil_range_closure F s hs μ A ω ρ hρ hρ₀ hρ₁ (Real.log Λ⁻¹) hSupp
  have hInv (k : K F) (q : Q F) :
      k.val⁻¹ * q ∈ ideleClassNorm F ⁻¹' U ↔ q ∈ ideleClassNorm F ⁻¹' U := by
    change ideleClassNorm F (k.val⁻¹ * q) ∈ U ↔ ideleClassNorm F q ∈ U
    rw [map_mul, map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, one_mul]
  have hClosed := isClosed_globalOrbitalIsotype_cutoff_range F s hs μ ω
    (ideleClassNorm F ⁻¹' U) ((ideleClassNorm_continuous F).measurable hU) hInv hρ₀ hρ₁
  dsimp only at hLeft hClosed
  rw [globalWeilIsotypeProduct_eq_unramified F μ s hs A ω hA, hClosed.closure_eq] at hLeft
  exact hLeft

end
end Masullo
