import SLocalFourierTail
import GlobalMellinPadding
import SLocalMellinCompact
import SchwartzCyclicMoment

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F

variable (S T : Finset (Place F))

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Z (A : Finset (Place F)) (ω : PontryaginDual (SLocalThetaNormOne F A))
    (f : E F A) :=
  sLocalProductZetaContinued F A (fun v ↦ μ v.val) ω
    (sLocalRealArchParameters F A ω) (sLocalComplexArchParameters F A ω) f

/-- The Mellin multiplier from the base-stage compressed Fourier integral
to the enlarged-stage integral. The numerator accounts for the changed
codifferent tails and the denominator for the inserted local factors. -/
def sLocalFourierPaddingMultiplier (ω : PontryaginDual (SLocalThetaNormOne F T)) (z : ℂ) : ℂ :=
  (sLocalZetaWeight F T ω z (QuotientGroup.mk (sLocalFourierTransitionIdele F S T)) *
    sLocalMellinPaddingHaarMass F μ S T) /
      sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ω) z

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem paddingDenominator_ne_zero
    (ω : PontryaginDual (SLocalThetaNormOne F T)) {z : ℂ} (hz : 0 < z.re) :
    sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ω) z ≠ 0 := by
  unfold sLocalMellinPaddingDenominator
  exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
    finiteZetaDenominator_ne_zero_of_pos F v.val.val (sLocalFiniteZetaPhases F T ω v.val) z hz

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem sLocalFourierPaddingMultiplier_analytic_ne_zero
    (ω : PontryaginDual (SLocalThetaNormOne F T)) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (sLocalFourierPaddingMultiplier F S T μ ω) z ∧
      sLocalFourierPaddingMultiplier F S T μ ω z ≠ 0 := by
  have hD := paddingDenominator_ne_zero F S T ω hz
  have hAnalytic := Finset.analyticAt_fun_prod Finset.univ (fun (v : {v : T // v.val ∉ S}) _ ↦
    finiteZetaDenominator_analytic F v.val.val (sLocalFiniteZetaPhases F T ω v.val) z)
  unfold sLocalFourierPaddingMultiplier
  constructor
  · unfold sLocalZetaWeight
    exact ((((analyticAt_id.mul analyticAt_const).cexp).mul analyticAt_const).mul
      analyticAt_const).div hAnalytic hD
  · apply div_ne_zero _ hD
    unfold sLocalZetaWeight
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Circle.coe_ne_zero _))
      (sLocalMellinPaddingHaarMass_ne_zero F μ)

/-- Padding commutes with the compressed Fourier–Mellin transform up to
the stated analytic multiplier on the positive half-plane. -/
theorem sLocalProductZetaContinued_fourier_padding_right
    (hST : S ⊆ T) (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S)) (ht : Surjective (sIdeleClassInclusion F T))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    let ωS := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let ωT := sLocalNormOneCharacterOfGlobal F ω T ht huT
    Z F μ T ωT (sLocalFourierCompression F T (sLocalBruhatTransition F hST f)) z =
      sLocalFourierPaddingMultiplier F S T μ ωT z *
        Z F μ S ωS (sLocalFourierCompression F S f) z := by
  intro ωS ωT
  let g := sLocalFourierCompression F S f
  let u := sLocalFourierTransitionIdele F S T
  let D := sLocalMellinPaddingDenominator F S (sLocalFiniteZetaPhases F T ωT) z
  let H := sLocalMellinPaddingHaarMass F μ S T
  let w := sLocalZetaWeight F T ωT z (QuotientGroup.mk u)
  have hpad : D * Z F μ T ωT (sLocalBruhatTransition F hST g) z =
      H * Z F μ S ωS g z :=
    sLocalProductZetaContinued_global_pad_right F ω S hs hu μ hST ht huT g z hz
  have hD := paddingDenominator_ne_zero F S T ωT hz
  have hCov : Z F μ T ωT (sLocalBruhatLeftTranslate F T u (sLocalBruhatTransition F hST g)) z =
      w * Z F μ T ωT (sLocalBruhatTransition F hST g) z :=
    sLocalProductZetaContinued_leftTranslate_right F T (fun v ↦ μ v.val) ωT u _ hz
  rw [sLocalFourierCompression_transition F S hST]
  change Z F μ T ωT (sLocalBruhatLeftTranslate F T u (sLocalBruhatTransition F hST g)) z = _
  rw [hCov]
  change w * Z F μ T ωT (sLocalBruhatTransition F hST g) z =
    (w * H / D) * Z F μ S ωS g z
  have h := (eq_div_iff hD).mpr ((mul_comm _ D).trans hpad)
  rw [h]
  ring

private theorem continuedZeta_analytic_right (A : Finset (Place F))
    (ω : PontryaginDual (SLocalThetaNormOne F A)) (f : E F A) (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ (Z F μ A ω f) z := by
  let η := sLocalZetaProductMeasure F A (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : η.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F A (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  apply (sLocalIdelicZeta_analytic F A η ω f z hz).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  exact ((sLocalIdelicZeta_meromorphic_continuation F A (fun v ↦ μ v.val) ω f).2 hw).symm

/-- The padding multiplier is an analytic unit at every reflected jet
center. Thus the base-stage and enlarged-stage Fourier jets have exactly
the same vanishing filtration on an inserted test. -/
theorem sLocalFourierPadding_reflected_jets_vanish_iff
    (hST : S ⊆ T) (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S)) (ht : Surjective (sIdeleClassInclusion F T))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (huT : globalNormOneCharacter F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : E F S) (c : ℂ) (hc : c.re = 0) (n : ℕ) :
    let ωS := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let ωT := sLocalNormOneCharacterOfGlobal F ω T ht huT
    (∀ k < n, iteratedDeriv k (fun z ↦
      Z F μ T ωT (sLocalFourierCompression F T (sLocalBruhatTransition F hST f)) (1-z)) c = 0) ↔
    (∀ k < n, iteratedDeriv k (fun z ↦
      Z F μ S ωS (sLocalFourierCompression F S f) (1-z)) c = 0) := by
  intro ωS ωT
  let g := sLocalFourierCompression F S f
  let h := sLocalFourierCompression F T (sLocalBruhatTransition F hST f)
  let ρ (z : ℂ) := 1-z
  let LS := Z F μ S ωS g ∘ ρ
  let LT := Z F μ T ωT h ∘ ρ
  let U := sLocalFourierPaddingMultiplier F S T μ ωT ∘ ρ
  have hw : 0 < (ρ c).re := by simp [ρ, hc]
  have hρ : AnalyticAt ℂ ρ c := analyticAt_const.sub analyticAt_id
  have hS : AnalyticAt ℂ LS c := (continuedZeta_analytic_right F μ S ωS g _ hw).comp hρ
  have hT : AnalyticAt ℂ LT c := (continuedZeta_analytic_right F μ T ωT h _ hw).comp hρ
  obtain ⟨hU₀, hUne⟩ := sLocalFourierPaddingMultiplier_analytic_ne_zero F S T μ ωT hw
  have hU : AnalyticAt ℂ U c := hU₀.comp hρ
  have hOpen : IsOpen {z | 0 < (ρ z).re} :=
    (isOpen_lt continuous_const Complex.continuous_re).preimage
      (continuous_const.sub continuous_id)
  have he : LT =ᶠ[𝓝 c] U * LS := by
    filter_upwards [hOpen.mem_nhds hw] with z hz
    exact sLocalProductZetaContinued_fourier_padding_right F S T μ hST ω hs ht hu huT f (ρ z) hz
  have hOrder := meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)
  have hUnitOrder : meromorphicOrderAt U c = 0 := by
    rw [hU.meromorphicOrderAt_eq, hU.analyticOrderAt_eq_zero.mpr hUne]
    rfl
  rw [meromorphicOrderAt_mul hU.meromorphicAt hS.meromorphicAt, hUnitOrder, zero_add,
    hT.meromorphicOrderAt_eq, hS.meromorphicOrderAt_eq] at hOrder
  change (∀ k < n, iteratedDeriv k LT c = 0) ↔ (∀ k < n, iteratedDeriv k LS c = 0)
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hT,
    ← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hS]
  have hm : analyticOrderAt LT c = analyticOrderAt LS c :=
    WithTop.map_injective (Nat.cast_injective (R := ℤ)) hOrder
  rw [hm]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The scalar compact section has the actual selected local Euler
denominators as its Mellin divisor, with coincident zeros counted once
for each selected place. -/
theorem exists_sLocalCompactMellinRepresentative
    (ω : PontryaginDual (SLocalThetaNormOne F T)) (W : Finset T) :
    ∃ (a b : ℝ) (A : PositiveRealExponentialDecay univ →L[ℂ] PositiveRealExponentialDecay univ),
      (∀ f, support (A f).val ⊆ Icc a b) ∧
      ∀ f, ∃ g : PositiveRealExponentialDecay univ, ∀ z : ℂ,
        (entireLogMellin f).val z - (entireLogMellin (A f)).val z =
          (∏ v ∈ W, finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F T ω v) z) *
            (entireLogMellin g).val z := by
  let generator (v : T) : ℝ × Circle :=
    (Real.log (v.val.asIdeal.absNorm : ℝ),
      sLocalFiniteZetaPhases F T ω v (chosenFiniteUniformizer F v.val))
  let gs := W.toList.map generator
  have hg : ∀ g ∈ gs, 0 < g.1 := by
    intro g hg
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hg
    apply Real.log_pos
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
  obtain ⟨A, hA, hDiff⟩ := exists_logDecayCyclicDifferenceProduct_compactMellinRepresentative gs hg
  refine ⟨_, _, A, hA, fun f ↦ ?_⟩
  obtain ⟨g, h⟩ := hDiff f
  refine ⟨g, fun z ↦ (h z).trans ?_⟩
  congr 1
  dsimp only [gs]
  rw [List.map_map, Finset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro v _
  simp only [Function.comp_apply, generator, finiteZetaDenominator, finiteZetaRatio]
  congr 4
  ring

omit [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- A single logarithmic interval suffices to preserve all Taylor jets
through the actual selected Weil multiplicities. -/
theorem exists_sLocalCompactMellinRepresentative_selectedJets
    (ω : PontryaginDual (SLocalThetaNormOne F T)) (W : Finset T)
    (hW : ∀ v ∈ W, finiteZetaUnramified F v.val (sLocalFiniteZetaPhases F T ω v)) :
    ∃ (a b : ℝ) (A : PositiveRealExponentialDecay univ →L[ℂ] PositiveRealExponentialDecay univ),
      (∀ f, support (A f).val ⊆ Icc a b) ∧
      ∀ f c, ∀ k < sLocalSelectedFinitePoleCount F T ω W c,
        iteratedDeriv k (entireLogMellin (A f)).val c =
          iteratedDeriv k (entireLogMellin f).val c := by
  obtain ⟨a, b, A, hA, hDiff⟩ := exists_sLocalCompactMellinRepresentative F T ω W
  refine ⟨a, b, A, hA, fun f c k hk ↦ ?_⟩
  let P := sLocalSelectedEulerMultiplier F T ω W
  let Q := (entireLogMellin f).val - (entireLogMellin (A f)).val
  have hP : AnalyticAt ℂ P c := by
    unfold P sLocalSelectedEulerMultiplier
    apply Finset.analyticAt_fun_prod
    intro v hv
    have heq : finiteZetaWeilMultiplier F v.val (sLocalFiniteZetaPhases F T ω v) =
        finiteZetaDenominator F v.val (sLocalFiniteZetaPhases F T ω v) := by
      funext z
      simp only [finiteZetaWeilMultiplier, ite_eq_left (hW v hv), finiteZetaDenominator]
    rw [heq]
    exact finiteZetaDenominator_analytic F v.val (sLocalFiniteZetaPhases F T ω v) c
  have hEntire (u : PositiveRealExponentialDecay (univ : Set ℝ)) :
      AnalyticAt ℂ (entireLogMellin u).val c := by
    apply Differentiable.analyticAt
    have he := (entireLogMellin u).property.2.1
    simpa only [preimage_univ, differentiableOn_univ] using he
  have hQ : AnalyticAt ℂ Q c := (hEntire f).sub (hEntire (A f))
  obtain ⟨g, hg⟩ := hDiff f
  have he : Q = P * (entireLogMellin g).val := by
    funext z
    refine (hg z).trans ?_
    congr 1
    unfold P sLocalSelectedEulerMultiplier
    apply Finset.prod_congr rfl
    intro v hv
    simp only [finiteZetaWeilMultiplier, ite_eq_left (hW v hv), finiteZetaDenominator]
  have ho : (sLocalSelectedFinitePoleCount F T ω W c : WithTop ℤ) ≤ meromorphicOrderAt Q c := by
    rw [he, meromorphicOrderAt_mul hP.meromorphicAt (hEntire g).meromorphicAt,
      sLocalSelectedEulerMultiplier_order F T ω W c]
    exact le_add_of_nonneg_right (hEntire g).meromorphicOrderAt_nonneg
  have ho' : (sLocalSelectedFinitePoleCount F T ω W c : ℕ∞) ≤ analyticOrderAt Q c := by
    rw [hQ.meromorphicOrderAt_eq] at ho
    cases h : analyticOrderAt Q c with
    | top => simp
    | coe n =>
      rw [h, ENat.map_natCast] at ho
      exact_mod_cast ho
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQ).mp ho' k hk
  change iteratedDeriv k ((entireLogMellin f).val - (entireLogMellin (A f)).val) c = 0 at hz
  rw [iteratedDeriv_sub (hEntire f).contDiffAt (hEntire (A f)).contDiffAt, sub_eq_zero] at hz
  exact hz.symm

end

end Masullo
