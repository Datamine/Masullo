import IdelicWeilFinite
import BruhatCompactTestTopology
import BruhatFourierDerivative
import FiniteFlatQuasiCharacter
import IdelicCutoffKernel

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
local notation "Place" => HeightOneSpectrum (𝓞 F)
private abbrev U := IntegralUnitFamily F

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

private def integralUnitFamilyClassHom : U F →ₜ* IdeleClass F :=
  { toFun := integralUnitFamilyClass F
    map_one' := integralUnitFamilyClass_one F
    map_mul' := integralUnitFamilyClass_mul F
    continuous_toFun := integralUnitFamilyClass_continuous F }

private theorem integralUnitFamily_unit_nhds_basis (v : Place) :
    (𝓝 (1 : principalIntegralUnits F v)).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {u : principalIntegralUnits F v | ‖u.val.val - 1‖ < ε}) := by
  let j : principalIntegralUnits F v → v.adicCompletion F := fun u => u.val.val
  have hj : IsInducing j :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isInducing.comp IsInducing.subtypeVal
  rw [hj.nhds_eq_comap]
  have he (r : ℝ) : j ⁻¹' Metric.ball 1 r =
      {u : principalIntegralUnits F v | ‖u.val.val - 1‖ < r} := by
    ext u
    exact Iff.trans (Metric.mem_ball) (by rw [dist_eq_norm]; rfl)
  simpa only [show j 1 = 1 from rfl, he] using
    (Metric.nhds_basis_ball (x := (1 : v.adicCompletion F))).comap j

/-- A unitary character of the product of integral finite units has open kernel. -/
theorem integralUnitFamily_character_ker_open (χ : PontryaginDual (U F)) :
    IsOpen (χ.toMonoidHom.ker : Set (U F)) := by
  let V : Set (U F) := {u | ‖(χ u : ℂ) - 1‖ < 1 / 2}
  have hχ : Continuous (fun u : U F => (χ u : ℂ)) :=
    continuous_subtype_val.comp χ.continuous
  have hV : V ∈ 𝓝 (1 : U F) :=
    (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds
      (by change ‖(χ 1 : ℂ) - 1‖ < 1 / 2; simp)
  rw [nhds_pi] at hV
  have hBasis := Filter.hasBasis_pi (fun v : Place => integralUnitFamily_unit_nhds_basis F v)
  obtain ⟨⟨S, r⟩, ⟨hS, hr⟩, hs⟩ := hBasis.mem_iff.mp hV
  let ε (v : Place) := min (r v) 1
  have hε (v : Place) (hv : v ∈ S) : 0 < ε v := lt_min (hr v hv) zero_lt_one
  apply χ.toMonoidHom.ker.isOpen_of_mem_nhds (g := 1)
  rw [nhds_pi]
  apply hBasis.mem_iff.mpr
  refine ⟨⟨S, ε⟩, ⟨hS, hε⟩, ?_⟩
  intro u hu
  change χ u = 1
  apply Circle.coe_injective
  apply complex_eq_one_of_powers_near_one
  intro n
  have hpow : u ^ n ∈ V := hs fun v hv => by
    have huv : ‖(u v).val.val - 1‖ < ε v := hu v hv
    change ‖((u ^ n) v).val.val - 1‖ < r v
    rw [Pi.pow_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact (ultrametric_norm_pow_sub_one_lt (hε v hv) (min_le_right _ _) huv n).trans_le (min_le_left _ _)
  change ‖(χ (u ^ n) : ℂ) - 1‖ < 1 / 2 at hpow
  simpa only [map_pow, Circle.coe_pow] using hpow

set_option maxHeartbeats 1100000 in
/-- A closed subgroup of the idele classes with compactly generated
annihilator pulls back to an open subgroup of the integral finite units. -/
theorem integralUnitFamily_preimage_open_of_compact_annihilator
    (H : Subgroup (IdeleClass F)) (hH : IsClosed (H : Set (IdeleClass F)))
    (hgen : IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F) H)) :
    IsOpen ((H.comap (integralUnitFamilyClassHom F).toMonoidHom : Subgroup (U F)) : Set (U F)) := by
  letI (v : Place) : CompactSpace (principalIntegralUnits F v) := principalIntegralUnits_compactSpace F v
  let J := lcaAnnihilator (G := IdeleClass F) H
  obtain ⟨A, _, hA, hgenA⟩ := hgen
  let ι := integralUnitFamilyClassHom F
  let R : J → PontryaginDual (U F) := fun χ => PontryaginDual.map ι χ.val
  let T := R '' A
  have hR : Continuous R := (PontryaginDual.map ι).continuous.comp continuous_subtype_val
  letI : DiscreteTopology (PontryaginDual (U F)) :=
    (compactSpace_iff_discretePontryaginDual (G := U F)).mp inferInstance
  have hT : T.Finite := (hA.image hR).finite_of_discrete
  have hEq : (H.comap ι.toMonoidHom : Set (U F)) =
      ⋂ θ ∈ T, (θ.toMonoidHom.ker : Set (U F)) := by
    ext u
    simp only [SetLike.mem_coe, Subgroup.mem_comap, mem_iInter, MonoidHom.mem_ker]
    change ι u ∈ H ↔ ∀ θ ∈ T, θ u = 1
    rw [← lcaDualAnnihilator_annihilator (G := IdeleClass F) H hH, mem_lcaDualAnnihilator_iff]
    constructor
    · intro hu θ hθ
      obtain ⟨χ, _, rfl⟩ := hθ
      exact hu χ
    · intro hu χ
      let e : J →* Circle :=
        { toFun := fun ψ => ψ.val (ι u)
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have he : A ⊆ e.ker := fun ψ hψ => hu (R ψ) ⟨ψ, hψ, rfl⟩
      have hall : (⊤ : Subgroup J) ≤ e.ker :=
        hgenA ▸ (Subgroup.closure_le e.ker).mpr he
      exact hall (Subgroup.mem_top χ)
  change IsOpen (H.comap ι.toMonoidHom : Set (U F))
  rw [hEq]
  exact hT.isOpen_biInter fun θ _ => integralUnitFamily_character_ker_open F θ

set_option maxHeartbeats 1100000 in
/-- Every compact-test stage is fixed by one open subgroup of the product
of finite integral units. -/
theorem bruhatCompactTest_stage_finite_invariance (i : BruhatCompactTestIndex (IdeleClass F)) :
    ∃ H : Subgroup (U F), IsOpen (H : Set (U F)) ∧
      ∀ (u : i.Space) g a, a ∈ H →
        (i.inclusion u).val.val (g * integralUnitFamilyClass F a) =
          (i.inclusion u).val.val g := by
  let P := i.1.1
  let ι := integralUnitFamilyClassHom F
  refine ⟨P.kernel.comap ι.toMonoidHom,
    integralUnitFamily_preimage_open_of_compact_annihilator F P.kernel P.kernel_closed
      P.annihilator_compactlyGenerated, ?_⟩
  intro u g a ha
  have ha' : integralUnitFamilyClass F a ∈ P.kernel := ha
  exact i.1.realize_mul_kernel u.val g ⟨_, ha'⟩

/-- A bounded family has one compact support and one open finite-unit level
of invariance. -/
theorem bruhatCompactTest_common_finite_stage (B : Set (BruhatCompactTest (IdeleClass F)))
    (hB : IsVonNBounded ℂ B) :
    ∃ (C : Set (IdeleClass F)) (H : Subgroup (U F)), IsCompact C ∧ IsOpen (H : Set (U F)) ∧
      ∀ f ∈ B, tsupport f.val.val ⊆ C ∧
        ∀ g a, a ∈ H → f.val.val (g * integralUnitFamilyClass F a) = f.val.val g := by
  obtain ⟨i, A, _, hA⟩ :=
    bruhatCompactTest_bounded_stage (CompactExhaustion.choice (IdeleClass F)) B hB
  obtain ⟨H, hH, hInv⟩ := bruhatCompactTest_stage_finite_invariance F i
  refine ⟨i.2.val, H, i.2.property, hH, fun f hf => ?_⟩
  rw [← hA] at hf
  obtain ⟨u, _, rfl⟩ := hf
  refine ⟨closure_minimal ?_ i.2.property.isClosed, hInv u⟩
  intro x hx
  contrapose! hx
  exact Function.notMem_support.mpr (u.property x hx)

/-- Every compact idelic Bruhat test is locally constant in the finite directions. -/
theorem bruhatCompactTest_locallyConstantAtFinite (f : BruhatCompactTest (IdeleClass F)) :
    IdelicTestLocallyConstantAtFinite F f.val.val := by
  obtain ⟨p, u, hu⟩ := f.val.property
  let i : BruhatCompactTestIndex (IdeleClass F) := (p, ⟨tsupport f.val.val, f.property⟩)
  let w : i.Space := ⟨u, fun g hg =>
    (congrFun hu g).trans (image_eq_zero_of_notMem_tsupport hg)⟩
  obtain ⟨H, hH, h⟩ := bruhatCompactTest_stage_finite_invariance F i
  have he : (i.inclusion w).val.val = f.val.val := hu
  exact idelicTestLocallyConstantAtFinite_of_open_invariance F _ H hH (he ▸ h w)

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
/-- The finite-place terms have uniformly finite support on bounded families
in the compact Bruhat test topology. -/
theorem bruhatCompactTest_finiteWeil_uniformly_zero (B : Set (BruhatCompactTest (IdeleClass F)))
    (hB : IsVonNBounded ℂ B) :
    ∀ᶠ v : Place in cofinite, ∀ f ∈ B,
      finitePlaceIdelicWeilTerm F μ f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f) v = 0 := by
  obtain ⟨C, H, hC, hH, hInv⟩ := bruhatCompactTest_common_finite_stage F B hB
  filter_upwards [finitePlaceIdelicWeilTerm_uniformly_zero F μ C hC H hH] with v hv f hf
  exact hv f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f) (hInv f hf).1 (hInv f hf).2

omit [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure] in
/-- The finite-place partial sums stabilize at the full sum uniformly on
each bounded set of compact Bruhat tests. -/
theorem bruhatCompactTest_finiteWeil_partialSums_eventually_eq
    (B : Set (BruhatCompactTest (IdeleClass F))) (hB : IsVonNBounded ℂ B) :
    let t (f : BruhatCompactTest (IdeleClass F)) :=
      finitePlaceIdelicWeilTerm F μ f.val.val f.property (bruhatCompactTest_locallyConstantAtFinite F f)
    ∀ᶠ s : Finset Place in atTop, ∀ f ∈ B, (∑ v ∈ s, t f v) = ∑' v, t f v := by
  dsimp only
  let E := eventually_cofinite.mp (bruhatCompactTest_finiteWeil_uniformly_zero F μ B hB)
  filter_upwards [eventually_ge_atTop E.toFinset] with s hs f hf
  symm
  apply tsum_eq_sum
  intro v hv
  have hn : v ∉ E.toFinset := fun he => hv (hs he)
  rw [Set.Finite.mem_toFinset] at hn
  exact not_not.mp hn f hf

end
end Masullo
