import DiagonalQuotientTrace
import OrbitalShellCounterexample
import PrimaryOrbitalTraceKernel
import PrintedOrbitalIndentation

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField Pointwise

namespace Masullo

noncomputable section

section Transversal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) [DiscreteTopology H]

private abbrev q := (QuotientGroup.mk : G → G ⧸ H)
local instance orbitalShellQuotMeas : MeasurableSpace (G ⧸ H) := borel _
local instance orbitalShellQuotBorel : BorelSpace (G ⧸ H) := ⟨rfl⟩

/-- An open set meeting all cosets of a discrete subgroup contains a Borel transversal. -/
theorem quotient_borel_transversal_subset_open {B : Set G} (hB : IsOpen B)
    (hcover : ∀ z : G ⧸ H, ∃ x ∈ B, q H x = z) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ B ∧ BijOn (q H) D univ := by
  have hs : IsOpen ({1} : Set H) := isOpen_discrete _
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp hs
  have hV1 : (1 : G) ∈ V := by
    change (1 : H) ∈ Subtype.val ⁻¹' V
    rw [hV]
    simp
  obtain ⟨U₀, hU₀, hdiv⟩ := exists_nhds_split_inv (hVo.mem_nhds hV1)
  obtain ⟨U, hUsub, hUo, hU1⟩ := mem_nhds_iff.mp hU₀
  have hi : InjOn (q H) U := by
    intro a ha b hb hab
    have hp : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have hv : a⁻¹ * b ∈ V := by
      simpa only [div_eq_mul_inv, mul_comm] using hdiv b (hUsub hb) a (hUsub ha)
    have hone : (⟨a⁻¹ * b, hp⟩ : H) ∈ ({1} : Set H) := by
      rw [← hV]
      exact hv
    have hval := congrArg Subtype.val (mem_singleton_iff.mp hone)
    exact inv_mul_eq_one.mp hval
  have hlocal : IsLocalHomeomorph (q H) := by
    apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
    intro x
    have hx : x ∈ x • U := ⟨1, hU1, mul_one x⟩
    have ho := hUo.smul x
    refine ⟨x • U, ho.mem_nhds hx, .of_continuous_injective_isOpenMap
      (QuotientGroup.continuous_mk.comp continuous_subtype_val) ?_ ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩ hab
      apply Subtype.ext
      change QuotientGroup.mk (s := H) (x * a) = QuotientGroup.mk (x * b) at hab
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at hab
      exact congrArg (x * ·) (hi ha hb (mul_left_cancel hab))
    · exact QuotientGroup.isOpenMap_coe.comp ho.isOpenEmbedding_subtypeVal.isOpenMap
  let f : B → G ⧸ H := q H ∘ Subtype.val
  have hEmb : IsOpenEmbedding (Subtype.val : B → G) := hB.isOpenEmbedding_subtypeVal
  have hsurj : Surjective f := fun z => by
    obtain ⟨x, hx, he⟩ := hcover z
    exact ⟨⟨x, hx⟩, he⟩
  obtain ⟨E, hE, _, hEi, hEs⟩ := borel_section_extend (hlocal.comp hEmb.isLocalHomeomorph)
    hsurj ∅ MeasurableSet.empty (injOn_empty f)
  refine ⟨Subtype.val '' E, hEmb.measurableEmbedding.measurableSet_image' hE, ?_,
    mapsTo_univ _ _, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact congrArg Subtype.val (hEi ha hb hab)
  · rw [SurjOn, ← image_comp]
    exact hEs.ge

end Transversal

variable (F : Type*) [Field F] [NumberField F]
private abbrev G := Idele F
private abbrev H := principalIdeles F
private abbrev Q := IdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance orbitalShellGMeas : MeasurableSpace (G F) := borel _
local instance orbitalShellGBorel : BorelSpace (G F) := ⟨rfl⟩
local instance orbitalShellGT2 : T2Space (G F) := ideles_hausdorff
local instance orbitalShellGLC : LocallyCompactSpace (G F) := ideles_locallyCompact
local instance orbitalShellGSC : SecondCountableTopology (G F) := by
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
local instance orbitalShellQMeas : MeasurableSpace (Q F) := borel _
local instance orbitalShellQBorel : BorelSpace (Q F) := ⟨rfl⟩
local instance orbitalShellQLC : LocallyCompactSpace (Q F) := ideleClasses_locallyCompact
local instance orbitalShellQSC : SecondCountableTopology (Q F) := ideleClass_secondCountable F
local instance orbitalShellHDiscrete : DiscreteTopology (H F) := principalIdeles_discrete
local instance orbitalShellHCountable : Countable (H F) := countable_of_Lindelof_of_discrete
local instance orbitalShellHCountHaar : (Measure.count : Measure (H F)).IsHaarMeasure :=
  subgroup_count_isHaarMeasure _
local instance orbitalShellHCountRegular : (Measure.count : Measure (H F)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- If the indentation is supported in the initial S-idelic block, multiplying
by any difference of divisorial indicators outside S kills the kernel. -/
theorem orbitalNormalizedShell_eq_zero (S A B : Finset (Place F))
    (hA : Disjoint A S) (hB : Disjoint B S) (u : C(G F, ℝ))
    (hu : tsupport u ⊆ sIdeleBlock F S)
    {x y : G F} (hx : x ∈ sIdeleBlock F S) :
    (orbitalDivisorialIndicator F B y - orbitalDivisorialIndicator F A y) *
      diagonalIndentation (H F) u x y = 0 := by
  by_cases hy : y ∈ sIdeleBlock F S
  · have hz := (sIdeleBlock_mem_iff F S y).mp hy
    have ha : orbitalDivisorialIndicator F A y = 1 :=
      indicator_of_mem (show y ∈ {g | ∀ v ∈ A, ideleOrder F g v = 0} from
        fun v hv => hz v (Finset.disjoint_left.mp hA hv)) _
    have hb : orbitalDivisorialIndicator F B y = 1 :=
      indicator_of_mem (show y ∈ {g | ∀ v ∈ B, ideleOrder F g v = 0} from
        fun v hv => hz v (Finset.disjoint_left.mp hB hv)) _
    rw [ha, hb, sub_self, zero_mul]
  · rw [diagonalIndentation_eq_zero (H F) u (sIdeleBlock F S) hu hx hy, mul_zero]

/-- A normalized S-local indentation can preserve the full quotient trace while
killing every divisorial shell outside the initial place set. -/
theorem exists_orbitalNormalizedShell (S : Finset (Place F))
    (hS : Surjective (sIdeleClassInclusion F S)) (ν : Measure (Q F))
    [IsFiniteMeasureOnCompacts ν] :
    ∃ (u : C(G F, ℝ)) (η : Measure (G F)),
      (∀ x, 0 ≤ u x) ∧ tsupport u ⊆ sIdeleBlock F S ∧
      (∀ L : Set (Q F), IsCompact L → IsCompact (tsupport u ∩ (ideleClassMap F) ⁻¹' L)) ∧
      (∀ x, Integrable (fun h : H F => u ((h : G F)⁻¹ * x)) Measure.count ∧
        (∫ h : H F, u ((h : G F)⁻¹ * x) ∂Measure.count) = 1) ∧
      η.map (ideleClassMap F) = ν ∧
      (∀ w : Q F → ℂ, Integrable w ν →
        (∫ x, ∫ h : H F, (diagonalIndentation (H F) u x ((h : G F)⁻¹ * x) : ℂ) *
          w (ideleClassMap F x) ∂Measure.count ∂η) = ∫ c, w c ∂ν) ∧
      ∀ A B : Finset (Place F), Disjoint A S → Disjoint B S →
        ∀ᵐ x ∂η, ∀ y : G F,
          (orbitalDivisorialIndicator F B y - orbitalDivisorialIndicator F A y) *
            diagonalIndentation (H F) u x y = 0 := by
  have hcover (z : Q F) : ∃ x ∈ sIdeleBlock F S, ideleClassMap F x = z := by
    obtain ⟨b, hb⟩ := hS z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨g.val, g.property, hb⟩
  obtain ⟨u, hpos, hsupp, hp, hn⟩ := exists_quotientIndentation_supported (H F)
    principalIdeles_closed Measure.count (sIdeleBlock_open F S) hcover
  obtain ⟨D, hD, hDS, hDt⟩ := quotient_borel_transversal_subset_open (H F)
    (sIdeleBlock_open F S) hcover
  let μ := quotientLiftedMeasure (H F) Measure.count ν
  letI : IsFiniteMeasureOnCompacts μ :=
    quotientLiftedMeasure_finiteOnCompacts (H F) principalIdeles_closed Measure.count ν
  letI : SigmaFinite μ := inferInstance
  let η := μ.restrict D
  have hη : η.map (ideleClassMap F) = ν :=
    quotientLiftedMeasure_transversal (H F) principalIdeles_closed ν hD hDt
  refine ⟨u, η, hpos, hsupp, hp, hn, hη, ?_, ?_⟩
  · intro w hw
    exact (diagonalIndentation_trace_integral (H F) principalIdeles_closed u hp hpos
      (fun x => (hn x).2) η ν hη w hw).2.1
  · intro A B hA hB
    filter_upwards [ae_restrict_mem hD (μ := μ)] with x hx y
    exact orbitalNormalizedShell_eq_zero F S A B hA hB u hsupp (hDS hx)

private abbrev K := normOneIdeleClass F
local instance orbitalShellKMeas : MeasurableSpace (K F) := borel _
local instance orbitalShellKBorel : BorelSpace (K F) := ⟨rfl⟩
local instance orbitalShellKCompact : CompactSpace (K F) := normOneIdeleClass_compact F
local instance orbitalShellClassHaar (ν : Measure (K F)) [ν.IsHaarMeasure] :
    (globalClassMeasure F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν

/-- At the half shift the radial bump contributes a strictly positive one-place trace. -/
theorem exists_orbitalHalfShift_nonzero_sample (ν : Measure (K F)) [ν.IsHaarMeasure]
    (v : Place F) :
    ∃ φ : BruhatCompactTest (Q F),
      (∀ g : Q F, g ∈ tsupport φ.val.val → 1 < ideleClassNorm F g) ∧
      (∑' n : ℤ, orbitalPlacePoissonSample F ν 1 φ v (-1/2) n) ≠ 0 := by
  obtain ⟨φ, hs, hinv, hsample⟩ := exists_orbitalShell_single_sample F v
  refine ⟨φ, hs, ?_⟩
  have hconst (n : ℤ) : (fun k : K F ↦ φ.val.val (globalUniformizerClass F v ^ (-n) * k.val) *
      ((1 : PontryaginDual (Q F)) k.val : ℂ)) =
      fun _ ↦ if -n = -1 then (1 : ℂ) else 0 := by
    funext k
    rw [mul_comm (globalUniformizerClass F v ^ (-n)) k.val, hinv, hsample]
    simp
  unfold orbitalPlacePoissonSample
  simp_rw [hconst]
  rw [tsum_eq_single (1 : ℤ)]
  · simp only [ite_true, integral_const, Complex.real_smul, mul_one, Int.cast_one]
    apply mul_ne_zero (mul_ne_zero _ _) _
    · exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    · exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    · apply Complex.ofReal_ne_zero.mpr
      exact (ENNReal.toReal_pos (isOpen_univ.measure_pos ν univ_nonempty).ne'
        (measure_ne_top ν _)).ne'
  · intro n hn
    have hne : -n ≠ -1 := fun h ↦ hn (neg_injective h)
    simp [hne]

/-- Even with the actual primary orbital kernel, the total normalized diagonal
can be nonzero while a one-place shell outside the initial block vanishes. -/
theorem orbitalNormalizedShell_counterexample (S : Finset (Place F))
    (hS : Surjective (sIdeleClassInclusion F S)) (ν : Measure (K F)) [ν.IsHaarMeasure]
    {p : ℕ} (hp : p.Prime) (v : Place F) (hv : v ∉ S)
    (hpv : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)})
    (s : ℝ) (hs : 0 ≤ s) (hDegree : 2 * (Module.finrank ℚ F : ℝ) ≤ s) (hs' : 1 < s) :
    let μ := globalClassMeasure F ν
    ∃ (φ : BruhatCompactTest (Q F)) (k : Lp ℂ 2 (μ.prod μ)) (d : Q F → ℂ)
      (u : C(G F, ℝ)) (η : Measure (G F)),
      (∀ g : Q F, g ∈ tsupport φ.val.val → 1 < ideleClassNorm F g) ∧
      kernelIntegralOperator k = primaryOrbitalKernelOperator F ν s hs {v} 1
        (orbitalShiftedBruhatTest F (-1/2) φ) ∧
      Integrable d μ ∧
      (∀ x, (∫ h : H F, u ((h : G F)⁻¹ * x) ∂Measure.count) = 1) ∧
      η.map (ideleClassMap F) = μ ∧
      (∫ x, ∫ h : H F, (diagonalIndentation (H F) u x ((h : G F)⁻¹ * x) : ℂ) *
          d (ideleClassMap F x) ∂Measure.count ∂η) = ∫ c, d c ∂μ ∧
      (∫ c, d c ∂μ) ≠ 0 ∧
      (∀ (U : ℕ → Set (Q F)), DoublingSequence μ U → CofinalAtOne U →
        IsCompact (closure (U 0)) → ∀ C : ℝ≥0, 0 < C →
        (∀ n, μ (U n * (U n)⁻¹) < C * μ (U n)) →
        ∀ᵐ x ∂μ, Tendsto (fun n ↦ translatedAverage (μ.prod μ) (U n ×ˢ U n)
          (k : Q F × Q F → ℂ) (x,x)) atTop (𝓝 (d x))) ∧
      ∀ᵐ x ∂η, ∀ y : G F,
        (orbitalDivisorialIndicator F {v} y - orbitalDivisorialIndicator F ∅ y) *
          diagonalIndentation (H F) u x y = 0 := by
  intro μ
  letI : μ.IsHaarMeasure := globalClassMeasure_isHaar F ν
  obtain ⟨φ, hsupport, hnonzero⟩ := exists_orbitalHalfShift_nonzero_sample F ν v
  have hone : ∀ w ∈ ({v} : Finset (Place F)), unramifiedFiniteCharacter F 1 w := by
    intro w hw a ha
    simp
  obtain ⟨k, d, hk, _, hd, hsum, hdiag⟩ := exists_primaryOrbitalPoissonKernel F ν s hs {v} 1 hp
    (fun w hw ↦ Finset.mem_singleton.mp hw ▸ hpv) hDegree hs' hone (-1/2) φ
  obtain ⟨u, η, _, _, _, hn, hη, htotal, hshell⟩ := exists_orbitalNormalizedShell F S hS μ
  refine ⟨φ, k, d, u, η, hsupport, hk, hd, fun x ↦ (hn x).2, hη, htotal d hd, ?_, hdiag, ?_⟩
  · change (∫ c, d c ∂(globalClassMeasure F ν)) ≠ 0
    rw [hsum, Finset.sum_singleton]
    exact hnonzero
  · exact hshell ∅ {v} (Finset.disjoint_empty_left _) (by simpa using hv)

end
end Masullo
