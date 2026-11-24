import SLocalBruhatProjections
import AdelicFourierClosure
import FiniteLocalAdditiveFourier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ContDiff NumberField RestrictedProduct SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev A := Adeles F
private abbrev FinA := FiniteAdeleRing (𝓞 F) F

/-- Integral finite adeles supported on the places outside the selected set. -/
def sLocalIntegralAdditiveTail (S : Finset (Place F)) : Set (FinA F) :=
  {u | (∀ v ∈ S, u v = 0) ∧ ∀ v, u v ∈ v.adicCompletionIntegers F}

private def tailPart (S : Finset (Place F)) (u : FinA F) : FinA F :=
  finiteCoordinateSplit F S (0, ((finiteCoordinateSplit F S).symm u).2)

private theorem tailPart_apply (S : Finset (Place F)) (u : FinA F) (v : Place F) :
    tailPart F S u v = if v ∈ S then 0 else u v := by
  classical
  by_cases h : v ∈ S
  · rw [tailPart, finiteCoordinateSplit_apply, dite_eq_left h, ite_eq_left h]
    rfl
  · rw [tailPart, finiteCoordinateSplit_apply, dite_eq_right h, ite_eq_right h]
    have hu := congrArg (fun x : FinA F => x v) ((finiteCoordinateSplit F S).apply_symm_apply u)
    rwa [finiteCoordinateSplit_apply, dite_eq_right h] at hu

private theorem tailPart_mem (S : Finset (Place F)) {u : FinA F}
    (hu : ∀ v ∉ S, u v ∈ v.adicCompletionIntegers F) :
    tailPart F S u ∈ sLocalIntegralAdditiveTail F S := by
  constructor
  · intro v hv
    simp only [tailPart_apply, ite_eq_left hv]
  · intro v
    by_cases hv : v ∈ S
    · rw [tailPart_apply, ite_eq_left hv]
      exact zero_mem _
    · simpa only [tailPart_apply, ite_eq_right hv] using hu v hv

private theorem tail_mul_swap (S : Finset (Place F)) (x y : FinA F) :
    tailPart F S x * y = x * tailPart F S y := by
  apply RestrictedProduct.ext
  intro v
  change tailPart F S x v * y v = x v * tailPart F S y v
  by_cases hv : v ∈ S <;> simp only [tailPart_apply, hv, ite_true, ite_false, zero_mul, mul_zero]

private theorem sLocalBruhatPad_add_tailPart (S : Finset (Place F)) (a : A F) :
    sLocalBruhatPad F S (sAdelesProjection F S a) +
      finiteAdelicTranslation F (tailPart F S a.2) = a := by
  apply Prod.ext
  · exact add_zero a.1
  · apply RestrictedProduct.ext
    intro v
    change (sLocalBruhatPad F S (sAdelesProjection F S a)).2 v + tailPart F S a.2 v = a.2 v
    have hp : (sLocalBruhatPad F S (sAdelesProjection F S a)).2 v =
        if v ∈ S then a.2 v else 0 := by
      change (finiteCoordinateSplit F S ((sAdelesProjection F S a).2, 0)) v = _
      rw [finiteCoordinateSplit_apply]
      split <;> rfl
    rw [hp, tailPart_apply]
    by_cases hv : v ∈ S <;> simp [hv]

/-- An embedded S-local test is supported on the integral tail and invariant
under its additive translations. These two conditions characterize the stage. -/
theorem sLocalBruhatImage_iff_support_tail_invariant (S : Finset (Place F)) (f : GlobalBruhat F) :
    f ∈ sLocalBruhatImage F S ↔
      (∀ a : A F, (∃ v ∉ S, a.2 v ∉ v.adicCompletionIntegers F) →
        GlobalBruhat.evaluation F a f = 0) ∧
      (∀ u ∈ sLocalIntegralAdditiveTail F S, ∀ a : A F,
        GlobalBruhat.evaluation F (a + finiteAdelicTranslation F u) f =
          GlobalBruhat.evaluation F a f) := by
  have hproj (u : FinA F) (hu : ∀ v ∈ S, u v = 0) (a : A F) :
      sAdelesProjection F S (a + finiteAdelicTranslation F u) = sAdelesProjection F S a := by
    apply Prod.ext
    · exact add_zero a.1
    · funext v
      change a.2 v.val + u v.val = a.2 v.val
      rw [hu _ v.property, add_zero]
  constructor
  · intro hf
    let x : sLocalBruhatImage F S := ⟨f, hf⟩
    refine ⟨fun a ha => ?_, fun u hu a => ?_⟩
    · change GlobalBruhat.evaluation F a x.val = 0
      rw [sLocalBruhatRestriction_reconstruct, ite_eq_right (by
        obtain ⟨v, hv, hn⟩ := ha
        exact fun h => hn (h v hv)), mul_zero]
    · change GlobalBruhat.evaluation F (a + finiteAdelicTranslation F u) x.val = _
      have hi (v : Place F) : a.2 v + u v ∈ v.adicCompletionIntegers F ↔
          a.2 v ∈ v.adicCompletionIntegers F := by
        constructor
        · intro h
          simpa only [add_sub_cancel_right] using sub_mem h (hu.2 v)
        · exact fun h => add_mem h (hu.2 v)
      simp only [sLocalBruhatRestriction_reconstruct, hproj u hu.1 a]
      change _ * (if ∀ v ∉ S, a.2 v + u v ∈ v.adicCompletionIntegers F then _ else _) = _
      simp only [hi]
      exact (sLocalBruhatRestriction_reconstruct F S x a).symm
  · rintro ⟨hs, ht⟩
    let p := sLocalBruhatCorestrict F S f
    have he : p.val = f := by
      apply (GlobalBruhat.algebraicEquiv F).injective
      apply Subtype.ext
      funext a
      change GlobalBruhat.evaluation F a p.val = GlobalBruhat.evaluation F a f
      rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatCorestrict_restrict]
      by_cases hi : ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F
      · rw [ite_eq_left hi, mul_one]
        change GlobalBruhat.evaluation F (sLocalBruhatPad F S (sAdelesProjection F S a)) f = _
        let u := tailPart F S a.2
        have hu := tailPart_mem F S hi
        exact (ht u hu _).symm.trans
          (congrArg (fun b => GlobalBruhat.evaluation F b f) (sLocalBruhatPad_add_tailPart F S a))
      · rw [ite_eq_right hi, mul_zero]
        push Not at hi
        exact (hs a hi).symm
    exact he ▸ p.property

private abbrev FinitePhase (u : FinA F) :=
  standardAdelicCharacter F (finiteAdelicTranslation F u)

/-- The global transform of an S-local test has the same value as its
S-local restriction on the omitted codifferent lattices, and vanishes
away from those lattices. -/
theorem sLocalFourier_codifferent_reconstruct (S : Finset (Place F))
    (f : sLocalBruhatImage F S) (b : A F) :
    GlobalBruhat.evaluation F b (GlobalBruhat.fourier F f.val) =
      sLocalBruhatRestriction F S (GlobalBruhat.fourier F f.val) (sAdelesProjection F S b) *
        (if ∀ v ∉ S, b.2 v ∈ finitePlaceIntegerAnnihilator F v then 1 else 0) := by
  letI : MeasurableSpace (A F) := borel _
  letI : BorelSpace (A F) := ⟨rfl⟩
  let y := tailPart F S b.2
  let b₀ := sLocalBruhatPad F S (sAdelesProjection F S b)
  let u := (GlobalBruhat.algebraicEquiv F f.val).val
  obtain ⟨hs, ht⟩ := (sLocalBruhatImage_iff_support_tail_invariant F S f.val).mp f.property
  have hy :
      (∀ x ∈ finiteIntegralAdeles F, FinitePhase F (x * y) = 0) ↔
        ∀ v ∉ S, b.2 v ∈ finitePlaceIntegerAnnihilator F v := by
    rw [finiteIntegralAdeles_annihilator_iff]
    constructor
    · intro h v hv
      simpa only [y, tailPart_apply, ite_eq_right hv] using h v
    · intro h v
      change tailPart F S b.2 v ∈ finitePlaceIntegerAnnihilator F v
      rw [tailPart_apply]
      by_cases hv : v ∈ S
      · rw [ite_eq_left hv]
        intro x hx
        simp
      · rw [ite_eq_right hv]
        exact h v hv
  by_cases hb : ∀ v ∉ S, b.2 v ∈ finitePlaceIntegerAnnihilator F v
  · rw [ite_eq_left hb, mul_one]
    change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f.val)).val b =
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f.val)).val b₀
    rw [GlobalBruhat.fourier_apply, adelicFourierIntegral]
    apply integral_congr_ae
    refine Eventually.of_forall fun a ↦ ?_
    by_cases ha : ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers F
    · have hx : tailPart F S a.2 ∈ finiteIntegralAdeles F :=
        (mem_finiteIntegralAdeles_iff F _).mpr (tailPart_mem F S ha).2
      have htail : FinitePhase F (a.2 * y) = 0 := by
        rw [show a.2 * y = tailPart F S a.2 * b.2 from (tail_mul_swap F S a.2 b.2).symm]
        have he : tailPart F S a.2 * b.2 = tailPart F S a.2 * y := by
          apply RestrictedProduct.ext
          intro v
          change tailPart F S a.2 v * b.2 v = tailPart F S a.2 v * tailPart F S b.2 v
          by_cases hv : v ∈ S <;> simp [tailPart_apply, hv]
        rw [he]
        exact hy.mpr hb _ hx
      have he : a * b = a * b₀ + finiteAdelicTranslation F (a.2 * y) := by
        rw [← sLocalBruhatPad_add_tailPart F S b, mul_add]
        congr 1
        exact Prod.ext (mul_zero _) rfl
      change u a * ((standardAdelicCharacter F (a * b)).toMul : ℂ) =
        u a * ((standardAdelicCharacter F (a * b₀)).toMul : ℂ)
      have hc : standardAdelicCharacter F (finiteAdelicTranslation F (a.2 * y)) = 0 := htail
      rw [he, map_add, hc, add_zero]
    · push Not at ha
      change u a * _ = u a * _
      rw [show u a = 0 from hs a ha, zero_mul, zero_mul]
  · rw [ite_eq_right hb, mul_zero]
    have hn := mt hy.mp hb
    push Not at hn
    obtain ⟨x, hx, hn⟩ := hn
    let v := tailPart F S x
    have hv := tailPart_mem F S (fun w _ ↦ (mem_finiteIntegralAdeles_iff F x).mp hx w)
    have he : finiteAdelicTranslation F v * b = finiteAdelicTranslation F (x * y) := by
      apply Prod.ext
      · exact zero_mul _
      · exact tail_mul_swap F S x b.2
    change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f.val)).val b = 0
    rw [GlobalBruhat.fourier_apply]
    exact adelicFourier_eq_zero_of_finite_translation F v (ht v hv) b (he ▸ hn)

private theorem integral_of_finite_annihilator {y : FinA F}
    (hy : ∀ x ∈ finiteIntegralAdeles F, FinitePhase F (x * y) = 0)
    (v : Place F) (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    y v ∈ v.adicCompletionIntegers F := by
  have h := (finiteIntegralAdeles_annihilator_iff F y).mp hy v
  rwa [finitePlaceIntegerAnnihilator_eq_integerRing_of_not_dvd F v hv] at h

/-- The frequencies annihilating the integral finite adeles are integral
away from the prime divisors of the different. -/
theorem exists_finset_integral_outside_finite_annihilator :
    ∃ S : Finset (Place F), ∀ y : FinA F,
      (∀ x ∈ finiteIntegralAdeles F, FinitePhase F (x * y) = 0) →
      ∀ v ∉ S, y v ∈ v.adicCompletionIntegers F := by
  let D := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  refine ⟨D, fun y hy v hv ↦ integral_of_finite_annihilator F hy v ?_⟩
  simpa [D] using hv

/-- The global Fourier transform preserves the S-local test space when
S contains the prime divisors of the different. -/
theorem sLocalFourier_preserves_stage_of_different
    (S : Finset (Place F))
    (hS : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : GlobalBruhat F) (hf : f ∈ sLocalBruhatImage F S) :
    GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S := by
  obtain ⟨hs, ht⟩ := (sLocalBruhatImage_iff_support_tail_invariant F S f).mp hf
  apply (sLocalBruhatImage_iff_support_tail_invariant F S _).mpr
  let v := (GlobalBruhat.algebraicEquiv F f).val
  constructor
  · rintro y ⟨w, hw, hnon⟩
    have hcontrast : ¬ (∀ x ∈ finiteIntegralAdeles F, FinitePhase F (x * tailPart F S y.2) = 0) := by
      intro h
      have h' := integral_of_finite_annihilator F h w (fun b => hw (hS w b))
      rw [tailPart_apply, ite_eq_right hw] at h'
      exact hnon h'
    push Not at hcontrast
    obtain ⟨x, hx, hc⟩ := hcontrast
    let u := tailPart F S x
    have hu := tailPart_mem F S (fun w _ => (mem_finiteIntegralAdeles_iff F x).mp hx w)
    have hχ : standardAdelicCharacter F (finiteAdelicTranslation F u * y) ≠ 0 := by
      have he : finiteAdelicTranslation F u * y = finiteAdelicTranslation F (u * y.2) := by
        apply Prod.ext
        · exact zero_mul y.1
        · rfl
      rw [he, tail_mul_swap F S x y.2]
      exact hc
    change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val y = _
    rw [GlobalBruhat.fourier_apply]
    exact adelicFourier_eq_zero_of_finite_translation F u (ht u hu) y hχ
  · intro u hu y
    change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
      (y + finiteAdelicTranslation F u) = (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val y
    simp only [GlobalBruhat.fourier_apply, adelicFourierIntegral]
    apply integral_congr_ae
    refine .of_forall fun x => ?_
    by_cases hi : ∀ w ∉ S, x.2 w ∈ w.adicCompletionIntegers F
    · have hu' : x.2 * u ∈ sLocalIntegralAdditiveTail F S := by
        constructor
        · intro w hw
          change x.2 w * u w = 0
          rw [hu.1 w hw, mul_zero]
        · intro w
          change x.2 w * u w ∈ w.adicCompletionIntegers F
          by_cases hw : w ∈ S
          · rw [hu.1 w hw, mul_zero]
            exact zero_mem _
          · exact mul_mem (hi w hw) (hu.2 w)
      have he : x * finiteAdelicTranslation F u = finiteAdelicTranslation F (x.2 * u) := by
        apply Prod.ext
        · exact mul_zero x.1
        · rfl
      change v x * ((standardAdelicCharacter F (x * (y + finiteAdelicTranslation F u))).toMul : ℂ) =
        v x * ((standardAdelicCharacter F (x * y)).toMul : ℂ)
      have hχ : standardAdelicCharacter F (finiteAdelicTranslation F (x.2 * u)) = 0 :=
        standardAdelicCharacter_finite_integral F
          ((mem_finiteIntegralAdeles_iff F _).mpr hu'.2)
      rw [mul_add, map_add, he, hχ, add_zero]
    · push Not at hi
      have hx : v x = 0 := hs x hi
      change v x * _ = v x * _
      rw [hx, zero_mul, zero_mul]

/-- A stage omitting a prime of the different contains a test whose global
Fourier transform has a nonzero value at a nonintegral omitted coordinate. -/
theorem sLocalFourier_stage_counterexample (S : Finset (Place F)) (w : Place F)
    (hw : w ∉ S) (hd : w.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    ∃ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∉ sLocalBruhatImage F S := by
  obtain ⟨y, hy, hnon⟩ := finitePlaceIntegerAnnihilator_exists_nonintegral F w hd
  let ξ := finitePlaceAdditiveInsert F w y
  let I : Set (FinA F) := finiteIntegralAdeles F
  have hIo : IsOpen I := by
    change IsOpen {a : FinA F | a ∈ finiteIntegralAdeles F}
    simp_rw [mem_finiteIntegralAdeles_iff]
    exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  letI : T2Space (FinA F) :=
    inferInstanceAs (T2Space (Πʳ v : Place F, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let ψ₀ := compactOpenIndicator (X := FinA F) ⟨I, isCompact_finiteIntegralAdeles F, hIo⟩
  let ψ : FiniteBruhat F := ⟨⟨ψ₀.val, ψ₀.property.1⟩, ψ₀.property.2⟩
  obtain ⟨u, _, huC, huD, huB, hu₀⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := univ) (x := (0 : mixedEmbedding.mixedSpace F))
      univ_mem
  let v (z : mixedEmbedding.mixedSpace F) : ℂ := u z
  let φ := (huC.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp huD)
  let f := GlobalBruhat.pure F ψ φ
  let g := bruhatTensor F φ ψ
  have hg (a : A F) : g a = v (mixedArch a) * I.indicator (fun _ ↦ (1 : ℂ)) a.2 := rfl
  have hzero (a : A F) (ha : a.2 ∉ I) : g a = 0 := by
    rw [hg, indicator_of_notMem ha, mul_zero]
  have hgmem : g ∈ bruhatSubmodule F := bruhatTensor_mem F φ ψ
  refine ⟨f, (sLocalBruhatImage_iff_support_tail_invariant F S f).mpr ⟨?_, ?_⟩, ?_⟩
  · rintro a ⟨w', _, hw'⟩
    exact hzero a (fun ha ↦ hw' ((mem_finiteIntegralAdeles_iff F a.2).mp ha w'))
  · intro b hb a
    have hb' : b ∈ finiteIntegralAdeles F := (mem_finiteIntegralAdeles_iff F b).mpr hb.2
    have he : (a + finiteAdelicTranslation F b).2 ∈ I ↔ a.2 ∈ I := by
      change a.2 + b ∈ finiteIntegralAdeles F ↔ a.2 ∈ finiteIntegralAdeles F
      exact (finiteIntegralAdeles F).toAddSubgroup.add_mem_cancel_right hb'
    change g (a + finiteAdelicTranslation F b) = g a
    rw [hg, hg]
    have harch : mixedArch (a + finiteAdelicTranslation F b) = mixedArch a := by
      change (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a.1 + 0) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1
      rw [add_zero]
    rw [harch]
    by_cases ha : a.2 ∈ I
    · rw [indicator_of_mem ha, indicator_of_mem (he.mpr ha)]
    · rw [indicator_of_notMem ha, indicator_of_notMem (mt he.mp ha)]
  · intro hmem
    letI : MeasurableSpace (A F) := borel _
    letI : BorelSpace (A F) := ⟨rfl⟩
    have hout : ξ.2 w ∉ (w.adicCompletionIntegers F : Set (w.adicCompletion F)) := by
      simpa only [ξ, finitePlaceAdditiveInsert_finite_apply_self] using hnon
    have hs := ((sLocalBruhatImage_iff_support_tail_invariant F S _).mp hmem).1 ξ
      ⟨w, hw, hout⟩
    change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val ξ = 0 at hs
    rw [GlobalBruhat.fourier_apply, adelicFourierIntegral] at hs
    let μ := adelicHaarUnitDomain F
    have hInt : Integrable g μ := by
      have h := bruhat_dilate_integrable F hgmem (1 : Idele F)
      change Integrable (fun a : A F ↦ g (1 * a)) μ at h
      simpa only [one_mul] using h
    have hEq : (∫ a, g a *
        ((standardAdelicCharacter F (a * ξ)).toMul : ℂ) ∂μ) = ∫ a, g a ∂μ := by
      apply integral_congr_ae (ae_of_all _ ?_)
      intro a
      by_cases ha : a.2 ∈ I
      · have hmul : a * ξ = finitePlaceAdditiveInsert F w (a.2 w * y) :=
          Prod.ext (mul_zero _) (finitePlaceAdditiveInsert_finite_mul F w a.2 y)
        have hn := hy (a.2 w) ((mem_finiteIntegralAdeles_iff F a.2).mp ha w)
        change standardAdelicCharacter F (finitePlaceAdditiveInsert F w (a.2 w * y)) = 0 at hn
        rw [hmul, hn]
        simp
      · rw [hzero a ha, zero_mul]
    change (∫ a, g a * ((standardAdelicCharacter F (a * ξ)).toMul : ℂ) ∂μ) = 0 at hs
    rw [hEq] at hs
    have hre : 0 < ∫ a, (g a).re ∂μ := by
      apply (integral_pos_iff_support_of_nonneg (f := fun a ↦ (g a).re) ?_ (hInt.re)).mpr
      · have hopen : IsOpen (Function.support (fun a ↦ (g a).re)) :=
          (isClosed_eq (Complex.continuous_re.comp (bruhat_continuous F hgmem)) continuous_const).isOpen_compl
        letI : μ.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
        apply hopen.measure_pos μ
        refine ⟨0, ?_⟩
        have hz : (0 : FinA F) ∈ I := (finiteIntegralAdeles F).zero_mem
        simp [Function.mem_support, hg, v, hu₀, show (0 : A F).2 ∈ I from hz]
      · intro a
        change 0 ≤ (g a).re
        by_cases ha : a.2 ∈ I
        · simpa [hg, indicator_of_mem ha, v] using (huB (mem_range_self (mixedArch a))).1
        · rw [hzero a ha, Complex.zero_re]
    have he := integral_re hInt
    change (∫ a, (g a).re ∂μ) = (∫ a, g a ∂μ).re at he
    rw [hs, Complex.zero_re] at he
    exact hre.ne' he

/-- The global Fourier operator preserves a stage exactly when the stage
includes every prime divisor of the different. -/
theorem sLocalFourier_preserves_stage_iff (S : Finset (Place F)) :
    (∀ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S) ↔
      ∀ w : Place F, w.asIdeal ∣ differentIdeal ℤ (𝓞 F) → w ∈ S := by
  refine ⟨fun h w hd ↦ ?_, sLocalFourier_preserves_stage_of_different F S⟩
  by_contra hw
  obtain ⟨f, hf, hn⟩ := sLocalFourier_stage_counterexample F S w hw hd
  exact hn (h f hf)

/-- For any number field of degree greater than one, the stage with only
archimedean places fails to be preserved by global Fourier. -/
theorem sLocalFourier_empty_stage_counterexample (hF : 1 < Module.finrank ℚ F) :
    ∃ f ∈ sLocalBruhatImage F ∅, GlobalBruhat.fourier F f ∉ sLocalBruhatImage F ∅ := by
  have hJ : differentIdeal ℤ (𝓞 F) ≠ ⊤ := by
    intro h
    have hn := NumberField.absNorm_differentIdeal F (𝓞 F)
    rw [h, Ideal.absNorm_top] at hn
    have he : |discr F| = 1 := by
      rw [← Int.natCast_natAbs, ← hn]
      rfl
    have hg := abs_discr_gt_two hF
    rw [he] at hg
    omega
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hJ
  let w : Place F := ⟨P, hP.isPrime, fun h ↦ differentIdeal_ne_bot (le_bot_iff.mp (h ▸ hle))⟩
  exact sLocalFourier_stage_counterexample F ∅ w (Finset.notMem_empty _) (Ideal.dvd_iff_le.mpr hle)

/-- A finite exceptional set suffices for the global Fourier transform
to preserve every larger S-local stage of Schwartz–Bruhat tests. -/
theorem exists_finset_sLocalFourier_preserves_stages :
    ∃ S₀ : Finset (Place F), ∀ S : Finset (Place F), S₀ ⊆ S →
      ∀ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S := by
  let D := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  refine ⟨D, fun S hS ↦ sLocalFourier_preserves_stage_of_different F S (fun v hv ↦ hS ?_)⟩
  simpa [D] using hv

/-- Fourier restricted to a stage preserved by the global transform. -/
def sLocalStageFourier (S : Finset (Place F))
    (hS : ∀ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S) :
    sLocalBruhatImage F S →L[ℂ] sLocalBruhatImage F S := by
  let T := (GlobalBruhat.fourier F).comp (sLocalBruhatImage F S).subtypeL
  exact ⟨T.toLinearMap.codRestrict _ (fun f => hS f.val f.property), T.continuous.subtype_mk _⟩

@[simp] theorem sLocalStageFourier_val (S : Finset (Place F))
    (hS : ∀ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S)
    (f : sLocalBruhatImage F S) :
    (sLocalStageFourier F S hS f).val = GlobalBruhat.fourier F f.val := rfl

/-- The restricted Fourier operators commute with all inclusions between
preserved stages. -/
theorem sLocalStageFourier_transition {S T : Finset (Place F)} (hST : S ⊆ T)
    (hS : ∀ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S)
    (hT : ∀ f ∈ sLocalBruhatImage F T, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F T) :
    (sLocalStageFourier F T hT).comp (sLocalBruhatTransition F hST) =
      (sLocalBruhatTransition F hST).comp (sLocalStageFourier F S hS) := by
  apply ContinuousLinearMap.ext
  intro f
  exact Subtype.ext rfl


end
end Masullo
