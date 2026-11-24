import GlobalHeckeDivisor
import HeckeEulerProducts

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev E := sLocalBruhatImage F

/-- The unitary extension to all idele classes using the norm-one part. -/
def normOneEulerCharacter (ω : PontryaginDual (K F)) : PontryaginDual (IdeleClass F) where
  toMonoidHom := ω.toMonoidHom.comp ((MonoidHom.fst _ _).comp (ideleClassSplit F).toMonoidHom)
  continuous_toFun := ω.continuous.comp (continuous_fst.comp (ideleClassSplitHomeomorph F).continuous)

variable (ω : PontryaginDual (K F))

private abbrev P := normOneEulerCharacter F ω
private abbrev χ := globalNormOneCharacter F ω
private abbrev b := heckeEulerCoefficient F (P F ω) (chosenFiniteUniformizer F)
private abbrev euler := heckeEulerFactor F (b F ω)

private theorem integralUnits_iff_norm (v : Place F) (u : (v.adicCompletion F)ˣ) :
    u ∈ finitePlaceIntegralUnits F v ↔ ‖(u : v.adicCompletion F)‖ = 1 := by
  let x : v.adicCompletion F := u.val
  have hi (z : v.adicCompletion F) : z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff.symm
  change (x ∈ v.adicCompletionIntegers F ∧ u.inv ∈ v.adicCompletionIntegers F) ↔ ‖x‖ = 1
  rw [hi, hi, show u.inv = x⁻¹ from Units.val_inv_eq_inv_val u, norm_inv]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr (Units.ne_zero u)
  constructor
  · rintro ⟨h₁, h₂⟩
    apply le_antisymm h₁
    exact (inv_le_one_iff₀.mp h₂).resolve_left hx.not_ge
  · rintro h
    simp [h]

variable (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : χ F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev A := sLocalNormOneCharacterOfGlobal F ω S hs hu
private abbrev phase := sLocalFiniteZetaPhases F S (A F ω S hs hu)

private theorem local_unramified_iff (v : S) :
    finiteZetaUnramified F v.val (phase F ω S hs hu v) ↔
      unramifiedFiniteCharacter F (P F ω) v.val := by
  constructor
  · intro h u hu
    apply Subtype.ext
    exact (sLocalFiniteZetaPhases_of_global F S ω hs _ v u).symm.trans
      (congrArg Subtype.val (h u ((integralUnits_iff_norm F v.val u).mpr hu)))
  · intro h u hu
    apply Subtype.ext
    exact (sLocalFiniteZetaPhases_of_global F S ω hs _ v u).trans
      (congrArg Subtype.val (h u ((integralUnits_iff_norm F v.val u).mp hu)))

private theorem local_denominator_eq (v : S) (h : finiteZetaUnramified F v.val
    (phase F ω S hs hu v)) (z : ℂ) :
    finiteZetaDenominator F v.val (phase F ω S hs hu v) z = (euler F ω v.val z)⁻¹ := by
  have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v.val)).ne'
  have hlog : Complex.log (v.val.asIdeal.absNorm : ℂ) =
      (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)]
  simp only [euler, heckeEulerFactor, inv_inv, b, heckeEulerCoefficient,
    ite_eq_left ((local_unramified_iff F ω S hs hu v).mp h)]
  rw [finiteZetaDenominator, finiteZetaRatio,
    sLocalFiniteZetaPhases_of_global F S ω hs hu v, Complex.cpow_def_of_ne_zero hq, hlog,
    mul_comm (-z)]
  rfl

/-- At each selected place the Weil principal-value multiplier is the
reciprocal local Hecke factor in the canonical global character chart. -/
theorem sLocalFiniteWeilMultiplier_eq_heckeFactor_inv (v : S) (z : ℂ) :
    finiteZetaWeilMultiplier F v.val (phase F ω S hs hu v) z = (euler F ω v.val z)⁻¹ := by
  by_cases h : finiteZetaUnramified F v.val (phase F ω S hs hu v)
  · rw [finiteZetaWeilMultiplier, ite_eq_left h]
    exact local_denominator_eq F ω S hs hu v h z
  · have he := mt (local_unramified_iff F ω S hs hu v).mpr h
    simp only [finiteZetaWeilMultiplier, ite_eq_right h, euler, heckeEulerFactor, inv_inv, b,
      heckeEulerCoefficient, ite_eq_right he, zero_mul, sub_zero]

/-- The selected finite Tate denominators equal the reciprocal selected
Hecke product in the same global character chart. -/
theorem sLocalFiniteZetaDenominator_eq_heckeProduct (z : ℂ) :
    sLocalFiniteZetaDenominator F S (phase F ω S hs hu) z =
      (∏ v ∈ S, euler F ω v z)⁻¹ := by
  unfold sLocalFiniteZetaDenominator
  rw [← Finset.prod_inv_distrib, Finset.prod_subtype S (fun _ ↦ Iff.rfl)]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : finiteZetaUnramified F v.val (phase F ω S hs hu v)
  · rw [ite_eq_left h, local_denominator_eq F ω S hs hu v h]
  · have he := mt (local_unramified_iff F ω S hs hu v).mpr h
    simp only [ite_eq_right h, euler, heckeEulerFactor, inv_inv, b, heckeEulerCoefficient,
      ite_eq_right he, zero_mul, sub_zero]

include hu in
private theorem padding_denominator_eq {T : Finset (Place F)}
    (ht : Surjective (sIdeleClassInclusion F T))
    (huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) (z : ℂ) :
    sLocalMellinPaddingDenominator F S (phase F ω T ht huT) z =
      (∏ v ∈ T \ S, euler F ω v z)⁻¹ := by
  unfold sLocalMellinPaddingDenominator
  rw [← Finset.prod_inv_distrib]
  let e : {v : T // v.val ∉ S} ≃ (↑(T \ S) : Set (Place F)) :=
    { toFun := fun v => ⟨v.val.val, Finset.mem_sdiff.mpr ⟨v.val.property, v.property⟩⟩
      invFun := fun v => ⟨⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩,
        (Finset.mem_sdiff.mp v.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Finset.prod_subtype (T \ S) (fun _ ↦ Iff.rfl)]
  apply Fintype.prod_equiv e
  intro v
  exact local_denominator_eq F ω T ht huT v.val
    (sLocalFiniteZetaPhases_global_unramified_new F S ω hu ht huT v.val v.property) z

include hu in
/-- The Euler denominator gained by padding is the inverse product of
the Hecke factors at the newly selected places. -/
theorem sLocalMellinPaddingDenominator_eq_heckeProduct {T : Finset (Place F)}
    (ht : Surjective (sIdeleClassInclusion F T))
    (huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) (z : ℂ) :
    sLocalMellinPaddingDenominator F S (phase F ω T ht huT) z =
      (∏ v ∈ T \ S, euler F ω v z)⁻¹ :=
  padding_denominator_eq F ω S hu ht huT z

private abbrev archDenominator :=
  archimedeanNumberFieldZetaDenominator F
    (sLocalRealArchParameters F S (A F ω S hs hu))
    (sLocalComplexArchParameters F S (A F ω S hs hu))

/-- The finite Euler product for the canonical unitary extension of the
norm-one character. Its defining product converges in the right half-plane. -/
def globalFiniteHeckeEuler (z : ℂ) : ℂ := ∏' v, euler F ω v z

/-- The completed Euler product with the canonical norm-one extension and
the archimedean factors of the same local Mellin chart. -/
def globalCompletedHeckeEuler (z : ℂ) : ℂ :=
  (archDenominator F ω S hs hu z)⁻¹ * ∏' v, euler F ω v z

private theorem globalHecke_archDenominator_ne_zero {z : ℂ} (hz : 0 < z.re) :
    archDenominator F ω S hs hu z ≠ 0 := by
  apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
  · intro v
    simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  · intro v
    simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz

theorem globalCompletedHeckeEuler_ne_zero {z : ℂ} (hz : 1 < z.re) :
    globalCompletedHeckeEuler F ω S hs hu z ≠ 0 :=
  mul_ne_zero (inv_ne_zero (globalHecke_archDenominator_ne_zero F ω S hs hu (zero_lt_one.trans hz)))
    (heckeEulerProduct_ne_zero F _ (norm_heckeEulerCoefficient_le_one F _ _) hz)

private theorem archDenominator_stage_eq
    (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
    (huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) :
    archDenominator F ω S hs hu = archDenominator F ω T ht huT := by
  obtain ⟨hR, hC⟩ := sLocalArchZetaDenominators_eq_of_weight F S (A F ω S hs hu)
    (A F ω T ht huT) (fun a ↦ (sLocalZetaWeight_global_arch_eq F S ω hs hu T ht huT a 0).symm)
  funext z
  unfold archDenominator archimedeanNumberFieldZetaDenominator
  simp_rw [hR, hC]

/-- The completed product is independent of the conductor stage used to read
the archimedean parameters. -/
theorem globalCompletedHeckeEuler_stage_eq
    (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
    (huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) :
    globalCompletedHeckeEuler F ω S hs hu = globalCompletedHeckeEuler F ω T ht huT := by
  unfold globalCompletedHeckeEuler
  rw [archDenominator_stage_eq F ω S hs hu T ht huT]

theorem globalHeckeContinuation_unique_germ {L L' P : ℂ → ℂ}
    (hL : MeromorphicOn L univ) (hL' : MeromorphicOn L' univ)
    (h : EqOn L P {z | 1 < z.re}) (h' : EqOn L' P {z | 1 < z.re}) (c : ℂ) :
    L =ᶠ[𝓝[≠] c] L' := by
  have hm : MeromorphicOn (L - L') univ := hL.sub hL'
  have ht : meromorphicOrderAt (L - L') (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
    change L z - L' z = 0
    rw [h hz, h' hz, sub_self]
  have hc : meromorphicOrderAt (L - L') c = ⊤ := by
    by_contra hc
    have hall := (hm.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).mp
      ⟨c, mem_univ c, hc⟩
    exact hall 2 (mem_univ _) ht
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hc] with z hz
  exact sub_eq_zero.mp hz

/-- Two meromorphic continuations of the completed product have the same
germ at every center and hence the same orders. -/
theorem globalCompletedHeckeContinuation_unique_germ {L L' : ℂ → ℂ}
    (hL : MeromorphicOn L univ) (hL' : MeromorphicOn L' univ)
    (h : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (h' : EqOn L' (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re}) (c : ℂ) :
    L =ᶠ[𝓝[≠] c] L' :=
  globalHeckeContinuation_unique_germ hL hL' h h' c

private theorem globalHecke_archDenominator_analytic (z : ℂ) :
    AnalyticAt ℂ (archDenominator F ω S hs hu) z :=
  archimedeanNumberFieldZetaDenominator_analytic _ _ _ z

private theorem finiteHeckeContinuation_properties {L : ℂ → ℂ}
    (hL : MeromorphicOn L univ)
    (hEq : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re}) :
    let D := archDenominator F ω S hs hu
    MeromorphicOn (D * L) univ ∧
      EqOn (D * L) (globalFiniteHeckeEuler F ω) {z | 1 < z.re} := by
  intro D
  refine ⟨fun z hz ↦ ((globalHecke_archDenominator_analytic F ω S hs hu z).meromorphicAt.mul
    (hL z hz)), ?_⟩
  intro z hz
  change D z * L z = ∏' v, euler F ω v z
  rw [hEq hz, globalCompletedHeckeEuler, ← mul_assoc,
    mul_inv_cancel₀ (globalHecke_archDenominator_ne_zero F ω S hs hu (zero_lt_one.trans hz)),
    one_mul]

/-- Every finite Euler continuation agrees as a meromorphic germ with the
completed continuation multiplied by the reciprocal archimedean factor. -/
theorem globalFiniteHeckeContinuation_germ {L f : ℂ → ℂ}
    (hL : MeromorphicOn L univ) (hf : MeromorphicOn f univ)
    (hL₁ : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (hf₁ : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re}) (z : ℂ) :
    f =ᶠ[𝓝[≠] z] archDenominator F ω S hs hu * L := by
  obtain ⟨hm, he⟩ := finiteHeckeContinuation_properties F ω S hs hu hL hL₁
  exact globalHeckeContinuation_unique_germ hf hm hf₁ he z

/-- The orders of the finite and completed Euler continuations agree on the
positive half-plane, including on its internal line of real part one. -/
theorem globalFiniteHeckeContinuation_order_of_re_pos {L f : ℂ → ℂ}
    (hL : MeromorphicOn L univ) (hf : MeromorphicOn f univ)
    (hL₁ : EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re})
    (hf₁ : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re}) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt f z = meromorphicOrderAt L z := by
  rw [meromorphicOrderAt_congr (globalFiniteHeckeContinuation_germ F ω S hs hu hL hf hL₁ hf₁ z)]
  exact meromorphicOrderAt_mul_of_ne_zero (globalHecke_archDenominator_analytic F ω S hs hu z)
    (globalHecke_archDenominator_ne_zero F ω S hs hu hz)

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance (T : Finset (Place F)) : MeasurableSpace (SAdeles F T)ˣ := borel _
local instance (T : Finset (Place F)) : BorelSpace (SAdeles F T)ˣ := ⟨rfl⟩

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev L (T : Finset (Place F)) (t : Surjective (sIdeleClassInclusion F T))
    (u : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F)))) (f : E F T) :=
  sLocalProductZetaContinued F T (fun v ↦ μ v.val) (A F ω T t u)
    (sLocalRealArchParameters F T (A F ω T t u))
    (sLocalComplexArchParameters F T (A F ω T t u)) f

private abbrev N (f : E F S) :=
  sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) (A F ω S hs hu) f

/-- Padding a finite-stage numerator multiplies it by precisely the
integral-unit Haar masses of the added places. -/
theorem sLocalEulerNormalizedMellin_global_pad
    {T : Finset (Place F)} (hST : S ⊆ T) (ht : Surjective (sIdeleClassInclusion F T))
    (huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (f : E F S) (c : ℂ) :
    N F ω T ht huT μ (sLocalBruhatTransition F hST f) c =
      sLocalMellinPaddingHaarMass F μ S T * N F ω S hs hu μ f c := by
  let S₁ := A F ω S hs hu
  let T₁ := A F ω T ht huT
  let fT := sLocalBruhatTransition F hST f
  let D := sLocalMellinPaddingDenominator F S (phase F ω T ht huT)
  let M := sLocalMellinPaddingHaarMass F μ S T
  have hD (z : ℂ) :
      sLocalEulerDenominator F T T₁ z = sLocalEulerDenominator F S S₁ z * D z := by
    change archDenominator F ω T ht huT z *
        sLocalFiniteZetaDenominator F T (phase F ω T ht huT) z =
      archDenominator F ω S hs hu z * sLocalFiniteZetaDenominator F S (phase F ω S hs hu) z * D z
    rw [← congrFun (archDenominator_stage_eq F ω S hs hu T ht huT) z,
      sLocalFiniteZetaDenominator_eq_heckeProduct F ω T ht huT z,
      sLocalFiniteZetaDenominator_eq_heckeProduct F ω S hs hu z,
      show D z = _ from padding_denominator_eq F ω S hu ht huT z, ← Finset.prod_sdiff hST, mul_inv]
    ring
  have ha := (sLocalEulerNormalizedMellin_entire F T (fun v ↦ μ v.val) T₁ fT c trivial).continuousAt
  have hb : ContinuousAt (fun z => M * N F ω S hs hu μ f z) c := continuousAt_const.mul
    (sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val) S₁ f c trivial).continuousAt
  apply ((ha.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hb).mp ?_).eq_of_nhds
  filter_upwards [sLocalEulerNormalizedMellin_eq_germ F T (fun v ↦ μ v.val) T₁ fT c,
    sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) S₁ f c,
    sLocalProductZetaContinued_global_pad F S ω hs hu μ hST ht huT f c] with z hT hS hp
  change N F ω T ht huT μ fT z = sLocalEulerDenominator F T T₁ z * L F ω μ T ht huT fT z at hT
  change N F ω S hs hu μ f z = sLocalEulerDenominator F S S₁ z * L F ω μ S hs hu f z at hS
  change D z * L F ω μ T ht huT fT z = M * L F ω μ S hs hu f z at hp
  change N F ω T ht huT μ fT z = M * N F ω S hs hu μ f z
  rw [hT, hS, hD, mul_assoc, hp, mul_left_comm]

private theorem reference_local_eq (r : E F S) (C : ℂ)
    (hN : N F ω S hs hu μ r = fun _ ↦ C) (z : ℂ) (hz : 0 < z.re) :
    L F ω μ S hs hu r z =
      C * ((archDenominator F ω S hs hu z)⁻¹ * ∏ v ∈ S, euler F ω v z) := by
  let D := sLocalEulerDenominator F S (A F ω S hs hu)
  have he := sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) (A F ω S hs hu) r z
  change N F ω S hs hu μ r =ᶠ[𝓝[≠] z] D * L F ω μ S hs hu r at he
  rw [hN] at he
  have hD := (sLocalEulerDenominator_analytic F S (A F ω S hs hu) z).continuousAt
  have hL := sLocalProductZetaContinued_continuousAt_pos F μ S (A F ω S hs hu) r z hz
  have heq : C = D z * L F ω μ S hs hu r z :=
    ((continuousAt_const.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hD.mul hL)).mp he).eq_of_nhds
  have hd := sLocalEulerDenominator_ne_zero_of_pos F S (A F ω S hs hu) hz
  calc
    L F ω μ S hs hu r z = C * (D z)⁻¹ := by
      rw [heq, mul_comm (D z), mul_assoc, mul_inv_cancel₀ hd, mul_one]
    _ = _ := by
      change C * (archDenominator F ω S hs hu z *
        sLocalFiniteZetaDenominator F S (phase F ω S hs hu) z)⁻¹ = _
      rw [sLocalFiniteZetaDenominator_eq_heckeProduct F ω S hs hu z, mul_inv, inv_inv]

private abbrev G (f : GlobalBruhat F) :=
  globalZetaContinued F ν f (compactIdeleClassCharacter F ω) 0

private abbrev Q (T : Finset (Place F)) (z : ℂ) :=
  (archDenominator F ω S hs hu z)⁻¹ * ∏ v ∈ T, euler F ω v z

private theorem reference_block_eq {T : Finset (Place F)} (hST : S ⊆ T)
    (ht : Surjective (sIdeleClassInclusion F T))
    (huT : χ F ω ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
    (r : E F S) (C : ℂ) (hN : N F ω S hs hu μ r = fun _ ↦ C) :
    ∃ B : ℂ, ∀ z : ℂ, 1 < z.re →
      (∫ g in (sIdeleBlock F T : Set (Idele F)), globalMellinIntegrand F ω r.val z g ∂η) =
        B * Q F ω S hs hu T z := by
  let ρ := sLocalZetaProductMeasure F T (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  letI : ρ.IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F T (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F)
  let rT := sLocalBruhatTransition F hST r
  obtain ⟨R, hR⟩ := globalMellin_block_integral_eq_smul F η ω T ht huT ρ
  let M := sLocalMellinPaddingHaarMass F μ S T
  refine ⟨(R : ℂ) * M * C, fun z hz => ?_⟩
  have hp := zero_lt_one.trans hz
  let D := sLocalMellinPaddingDenominator F S (phase F ω T ht huT)
  have hd : D z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦
    finiteZetaDenominator_ne_zero_of_pos F v.val.val (phase F ω T ht huT v.val) z hp
  have he := sLocalProductZetaContinued_global_pad_right F ω S hs hu μ hST ht huT r z hp
  change D z * L F ω μ T ht huT rT z = M * L F ω μ S hs hu r z at he
  have hn := congrArg ((D z)⁻¹ * ·) he
  rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul] at hn
  have hf := hR rT z
  change (∫ g in (sIdeleBlock F T : Set (Idele F)), globalMellinIntegrand F ω r.val z g ∂η) =
    R • sLocalIdelicZetaIntegral F T ρ (A F ω T ht huT) rT z at hf
  rw [hf, ← (sLocalIdelicZeta_meromorphic_continuation F T (fun v ↦ μ v.val)
    (A F ω T ht huT) rT).2 hp, Complex.real_smul]
  change (R : ℂ) * L F ω μ T ht huT rT z = _
  rw [hn, reference_local_eq F ω S hs hu μ r C hN z hp,
    show D z = _ from padding_denominator_eq F ω S hu ht huT z, inv_inv]
  unfold Q
  rw [← Finset.prod_sdiff hST]
  ring

variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include hν in
/-- The continuation of a constant-normalized Euler reference is a nonzero
scalar multiple of the completed Euler product on its convergence half-plane. -/
theorem globalZetaContinued_reference_eq_completedEuler
    (r : E F S) (C : ℂ) (hN : N F ω S hs hu μ r = fun _ ↦ C)
    (hfinite : meromorphicOrderAt (G F ω ν r.val) (2 : ℂ) ≠ ⊤) :
    ∃ B : ℂ, B ≠ 0 ∧ EqOn (G F ω ν r.val)
      (fun z => B * globalCompletedHeckeEuler F ω S hs hu z) {z | 1 < z.re} := by
  obtain ⟨T, hm, hST, ht, hcofinal, hcover⟩ := exists_ideleBlock_tower F S
  have huT (n : ℕ) : χ F ω ∈ (sUnramified F (T n) : Set (QuasiCharacter (IdeleClass F))) :=
    (mem_sUnramified_iff F (T n) _).mpr fun v hv u ↦
      (mem_sUnramified_iff F S _).mp hu v (fun h ↦ hv (hST n h)) u
  let B (n : ℕ) (z : ℂ) :=
    ∫ g in (sIdeleBlock F (T n) : Set (Idele F)), globalMellinIntegrand F ω r.val z g ∂η
  have hB (z : ℂ) (hz : 1 < z.re) :
      Tendsto (fun n ↦ B n z) atTop (𝓝 (G F ω ν r.val z)) := by
    have hint : Integrable (globalMellinIntegrand F ω r.val z) η :=
      idelicZeta_integrable F η r.val _ (compactIdeleClassCharacter_unitary F ω) z hz
    have hmono : Monotone (fun n ↦ (sIdeleBlock F (T n) : Set (Idele F))) :=
      fun m n h x hx ↦ (sIdeleTransition F (hm h) ⟨x, hx⟩).property
    have h := tendsto_setIntegral_of_monotone
      (fun n ↦ (sIdeleBlock_open F (T n)).measurableSet) hmono hint.integrableOn
    rw [hcover, Measure.restrict_univ] at h
    have he := globalZetaContinued_eq_idelic F η ν hν r.val (compactIdeleClassCharacter F ω)
      (compactIdeleClassCharacter_unitary F ω) (κ := 0) Complex.zero_re (fun t ↦ by simp) z hz
    change G F ω ν r.val z = _ at he
    rw [he]
    exact h
  let H := globalCompletedHeckeEuler F ω S hs hu
  have hQ (z : ℂ) (hz : 1 < z.re) :
      Tendsto (fun n ↦ Q F ω S hs hu (T n) z) atTop (𝓝 (H z)) := by
    have hp := (heckeEulerProduct_hasProdUniformlyOn F (b F ω)
      (norm_heckeEulerCoefficient_le_one F _ _) {z} isCompact_singleton
      (fun s hs ↦ (mem_singleton_iff.mp hs).symm ▸ hz)).hasProd (mem_singleton z)
    exact tendsto_const_nhds.mul ((show Tendsto
      (fun U : Finset (Place F) ↦ ∏ v ∈ U, euler F ω v z) atTop
      (𝓝 (∏' v, euler F ω v z)) from hp).comp hcofinal)
  have hcross (z w : ℂ) (hz : 1 < z.re) (hw : 1 < w.re) :
      G F ω ν r.val z * H w = G F ω ν r.val w * H z := by
    have he (n : ℕ) :
        B n z * Q F ω S hs hu (T n) w = B n w * Q F ω S hs hu (T n) z := by
      obtain ⟨K, hK⟩ := reference_block_eq F ω S hs hu η μ (hST n) (ht n) (huT n) r C hN
      change ∀ z, 1 < z.re → B n z = K * Q F ω S hs hu (T n) z at hK
      rw [hK z hz, hK w hw]
      ring
    exact tendsto_nhds_unique ((hB z hz).mul (hQ w hw))
      (((hB w hw).mul (hQ z hz)).congr' (.of_forall fun n ↦ (he n).symm))
  have htwo : 1 < (2 : ℂ).re := by norm_num
  have hH := globalCompletedHeckeEuler_ne_zero F ω S hs hu htwo
  have hG : G F ω ν r.val (2 : ℂ) ≠ 0 := by
    intro h
    apply hfinite
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hu₂ : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds htwo
    filter_upwards [hu₂.filter_mono nhdsWithin_le_nhds] with z hz
    have he := hcross z 2 hz htwo
    rw [h, zero_mul] at he
    exact (mul_eq_zero.mp he).resolve_right hH
  refine ⟨G F ω ν r.val 2 / H 2, div_ne_zero hG hH, fun z hz ↦ ?_⟩
  have he := hcross z 2 hz htwo
  change G F ω ν r.val z = G F ω ν r.val 2 / H 2 * H z
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hH).mpr he

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem continuedZeta_meromorphic (f : GlobalBruhat F) :
    MeromorphicOn (G F ω ν f) univ :=
  globalZetaContinued_meromorphic F ν f _ (compactIdeleClassCharacter_unitary F ω) 0

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem continuedZeta_order_zero_on_right (f : GlobalBruhat F) {z : ℂ}
    (hz : 1 < z.re) (h : G F ω ν f z ≠ 0) :
    meromorphicOrderAt (G F ω ν f) z = 0 := by
  have h₀ : z ≠ 0 := fun he => by norm_num [he] at hz
  have h₁ : z ≠ 1 := fun he => by norm_num [he] at hz
  have ha : AnalyticAt ℂ (G F ω ν f) z := globalZetaContinued_analyticAt F ν f _
    (compactIdeleClassCharacter_unitary F ω) 0 z (by simpa using h₀)
    (by simpa using sub_ne_zero.mpr h₁)
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr h]
  rfl

private theorem entire_normalized_transform {f L : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hL : MeromorphicOn L univ)
    (hfinite : ∀ z, meromorphicOrderAt L z ≠ ⊤)
    (hle : ∀ z, meromorphicOrderAt L z ≤ meromorphicOrderAt f z) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h univ ∧
      ∀ z, f =ᶠ[𝓝[≠] z] L * h := by
  have hm : MeromorphicOn (f / L) univ := hf.div hL
  let U := toMeromorphicNFOn (f / L) univ
  refine ⟨U, ?_, ?_⟩
  · intro z hz
    apply (meromorphicNFOn_toMeromorphicNFOn (f / L) univ hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm hz,
      meromorphicOrderAt_div (hf z hz) (hL z hz)]
    have h := hle z
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite z)
    rw [← hn] at h ⊢
    cases hm : meromorphicOrderAt f z with
    | top => simp
    | coe m =>
      rw [hm] at h
      exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (WithTop.coe_le_coe.mp h))
  · intro z
    have hn := (hL z trivial).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun he => hfinite z (meromorphicOrderAt_eq_top_iff.mpr he))
    filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z), hn] with s hs hs'
    change U s = f s / L s at hs
    change f s = L s * U s
    rw [hs, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hs', mul_one]

include μ hν in
/-- The completed product has a meromorphic continuation whose divisor is
the stage-independent minimum. Every continued global zeta transform
factors through it with an entire scalar quotient. -/
theorem exists_globalCompletedHeckeContinuation :
    ∃ (r : GlobalBruhat F) (L : ℂ → ℂ),
      EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      MeromorphicOn L univ ∧
      (∀ z, meromorphicOrderAt L z = meromorphicOrderAt (G F ω ν r) z) ∧
      (∀ z : ℂ, z.re < 0 ∨ 1 < z.re → meromorphicOrderAt L z = 0) ∧
      (∃ B : ℂ, B ≠ 0 ∧ G F ω ν r = fun z => B * L z) ∧
      ∀ f : GlobalBruhat F, ∃ U : ℂ → ℂ, AnalyticOnNhd ℂ U univ ∧
        ∀ z, G F ω ν f =ᶠ[𝓝[≠] z] L * U := by
  obtain ⟨r, C, hC, hN, hfinite, _⟩ :=
    exists_globalMellin_order_reference F η ω S hs hu μ ν hν
  have hmin := globalHeckeOrderReference_min F η ν ω μ S hs hu hν r C hC hN
  obtain ⟨B, hB, he⟩ := globalZetaContinued_reference_eq_completedEuler
    F ω S hs hu η ν μ hν r C hN (hfinite 2)
  let L := (fun _ : ℂ => B⁻¹) * G F ω ν r.val
  have hr := continuedZeta_meromorphic F ω ν r.val
  have hL : MeromorphicOn L univ := fun z hz => (MeromorphicAt.const B⁻¹ z).mul (hr z hz)
  have horder (z : ℂ) : meromorphicOrderAt L z = meromorphicOrderAt (G F ω ν r.val) z := by
    change meromorphicOrderAt ((fun _ : ℂ => B⁻¹) * G F ω ν r.val) z = _
    rw [meromorphicOrderAt_mul (MeromorphicAt.const B⁻¹ z) (hr z trivial),
      meromorphicOrderAt_const, ite_eq_right (inv_ne_zero hB), zero_add]
  refine ⟨r.val, L, ?_, hL, horder, ?_, ?_, fun f => ?_⟩
  · intro z hz
    change B⁻¹ * G F ω ν r.val z = _
    rw [he hz, ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
  · intro z hz
    rw [horder]
    rcases hz with hl | hr'
    · obtain ⟨T, hT⟩ := exists_homogeneousThetaPlaceBase F ω⁻¹
      obtain ⟨ht, huT⟩ := hT T Subset.rfl
      obtain ⟨q, D, hD, hM, hqfinite, _⟩ :=
        exists_globalMellin_order_reference F η ω⁻¹ T ht huT μ ν hν
      have hqmin := globalHeckeOrderReference_min F η ν ω⁻¹ μ T ht huT hν q D hD hM
      obtain ⟨A, hA, hEq⟩ := globalZetaContinued_reference_eq_completedEuler
        F ω⁻¹ T ht huT η ν μ hν q D hM (hqfinite 2)
      have hz' : 1 < (1 - z).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      have hn : G F ω⁻¹ ν q.val (1-z) ≠ 0 := by
        rw [hEq (show 1-z ∈ {z : ℂ | 1 < z.re} from hz')]
        exact mul_ne_zero hA (globalCompletedHeckeEuler_ne_zero F ω⁻¹ T ht huT hz')
      exact (globalHeckeOrderReference_reflect F ν ω r.val q.val hmin hqmin z).trans
        (continuedZeta_order_zero_on_right F ω⁻¹ ν q.val hz' hn)
    · apply continuedZeta_order_zero_on_right F ω ν r.val hr'
      rw [he (show z ∈ {z : ℂ | 1 < z.re} from hr')]
      exact mul_ne_zero hB (globalCompletedHeckeEuler_ne_zero F ω S hs hu hr')
  · refine ⟨B, hB, funext fun z => ?_⟩
    change G F ω ν r.val z = B * (B⁻¹ * G F ω ν r.val z)
    rw [← mul_assoc, mul_inv_cancel₀ hB, one_mul]
  · exact entire_normalized_transform (continuedZeta_meromorphic F ω ν f) hL
      (fun z => horder z ▸ hfinite z) (fun z => horder z ▸ hmin f z)

include μ hν in
/-- A meromorphic continuation of the finite Euler product exists on the
whole plane. In the open left half-plane its exact divisor is the divisor
of the reciprocal archimedean factor. -/
theorem exists_globalFiniteHeckeContinuation :
    ∃ f : ℂ → ℂ,
      MeromorphicOn f univ ∧ EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      ∀ z : ℂ, z.re < 0 →
        meromorphicOrderAt f z = meromorphicOrderAt (archDenominator F ω S hs hu) z := by
  obtain ⟨r, L, he, hm, _, hout, _, _⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  let D := archDenominator F ω S hs hu
  obtain ⟨hf, hf₁⟩ := finiteHeckeContinuation_properties F ω S hs hu hm he
  refine ⟨D * L, hf, hf₁, fun z hz ↦ ?_⟩
  rw [meromorphicOrderAt_mul (globalHecke_archDenominator_analytic F ω S hs hu z).meromorphicAt
    (hm z (mem_univ z)), hout z (Or.inl hz), add_zero]

omit [ν.IsHaarMeasure]
  [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem completedReference_min_of_entire_factor {L : ℂ → ℂ} (r : GlobalBruhat F)
    (hL : MeromorphicOn L univ)
    (horder : ∀ z, meromorphicOrderAt L z = meromorphicOrderAt (G F ω ν r) z)
    (hfactor : ∀ f : GlobalBruhat F, ∃ U : ℂ → ℂ, AnalyticOnNhd ℂ U univ ∧
      ∀ z, G F ω ν f =ᶠ[𝓝[≠] z] L * U) :
    ∀ f : GlobalBruhat F, ∀ z, meromorphicOrderAt (G F ω ν r) z ≤
      meromorphicOrderAt (G F ω ν f) z := by
  intro f z
  obtain ⟨U, hU, he⟩ := hfactor f
  have ha := hU z (mem_univ z)
  rw [← horder z, meromorphicOrderAt_congr (he z),
    meromorphicOrderAt_mul (hL z (mem_univ z)) ha.meromorphicAt]
  exact le_add_of_nonneg_right ha.meromorphicOrderAt_nonneg

include μ hν in
/-- The canonical completed Euler continuation is entire on a nontrivial
norm-one component. On the trivial component it has exactly the two simple
poles at zero and one. -/
theorem exists_globalCompletedHecke_analytic_or_simple_poles :
    ∃ L : ℂ → ℂ,
      MeromorphicOn L univ ∧ EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      (ω ≠ 1 → AnalyticOnNhd ℂ L univ) ∧
      (ω = 1 → meromorphicOrderAt L 0 = (-1 : ℤ) ∧
        meromorphicOrderAt L 1 = (-1 : ℤ) ∧
        ∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ L z) := by
  obtain ⟨r, L, he, hm, ho, _, ⟨B, hB, hsB⟩, hfactor⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  have hmin := completedReference_min_of_entire_factor F ω ν r hm ho hfactor
  have hscale : L = fun z ↦ B⁻¹ * G F ω ν r z := by
    funext z
    rw [hsB, ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
  have hregular (z : ℂ) (h : AnalyticAt ℂ (G F ω ν r) z) : AnalyticAt ℂ L z := by
    rw [hscale]
    exact analyticAt_const.mul h
  refine ⟨L, hm, he, ?_, ?_⟩
  · intro hω z hz
    apply hregular
    exact globalZetaContinued_entire_of_polar_zero F ν r (compactIdeleClassCharacter F ω)
      (compactIdeleClassCharacter_unitary F ω) 0
      (Or.inl (by rw [compactIdeleClassCharacter_integral, ite_eq_right hω])) z hz
  · intro hω
    subst ω
    obtain ⟨h₀, h₁⟩ := trivial_reference_regularized_nonzero F ν r hmin
    rw [globalHeckeClearedZeta_trivial_zero, neg_ne_zero] at h₀
    rw [globalHeckeClearedZeta_trivial_one, neg_ne_zero] at h₁
    have h := globalZetaContinued_pole_order F ν r
      (compactIdeleClassCharacter F 1) (compactIdeleClassCharacter_unitary F 1) 0
    refine ⟨?_, ?_, fun z hz₀ hz₁ ↦ hregular z ?_⟩
    · rw [ho]
      simpa only [compactIdeleClassCharacter_integral, ite_true, ite_eq_right h₀, neg_zero] using h.1
    · rw [ho]
      simpa only [compactIdeleClassCharacter_integral, ite_true, ite_eq_right h₁, sub_zero] using h.2
    · exact globalZetaContinued_analyticAt F ν r (compactIdeleClassCharacter F 1)
        (compactIdeleClassCharacter_unitary F 1) 0 z (by simpa using hz₀)
        (by simpa using sub_ne_zero.mpr hz₁)

include μ hν in
/-- The completed unitary Euler products for a character and its inverse
have meromorphic continuations related by reflection and a nowhere-zero
entire factor. The equation holds as a germ at every point. -/
theorem exists_globalCompletedHecke_functionalEquation :
    ∃ (T : Finset (Place F)) (ht : Surjective (sIdeleClassInclusion F T))
      (huT : χ F ω⁻¹ ∈ (sUnramified F T : Set (QuasiCharacter (IdeleClass F))))
      (L L' ε : ℂ → ℂ),
      MeromorphicOn L univ ∧ MeromorphicOn L' univ ∧
      EqOn L (globalCompletedHeckeEuler F ω S hs hu) {z | 1 < z.re} ∧
      EqOn L' (globalCompletedHeckeEuler F ω⁻¹ T ht huT) {z | 1 < z.re} ∧
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      ∀ c, (fun z ↦ L' (1 - z)) =ᶠ[𝓝[≠] c] L * ε := by
  obtain ⟨T, hT⟩ := exists_homogeneousThetaPlaceBase F ω⁻¹
  obtain ⟨ht, huT⟩ := hT T Subset.rfl
  obtain ⟨r, L, hEq, hL, horder, hout, _, hfactor⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  obtain ⟨r', L', hEq', hL', horder', _, _, hfactor'⟩ :=
    exists_globalCompletedHeckeContinuation F ω⁻¹ T ht huT η ν μ hν
  have hr := completedReference_min_of_entire_factor F ω ν r hL horder hfactor
  have hr' := completedReference_min_of_entire_factor F ω⁻¹ ν r' hL' horder' hfactor'
  let R (z : ℂ) := L' (1 - z)
  have ha (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := analyticAt_const.sub analyticAt_id
  have hm : MeromorphicOn R univ := fun z _ ↦
    (hL' (1 - z) (mem_univ _)).comp_analyticAt (g := fun w : ℂ ↦ 1 - w) (ha z)
  have ho (z : ℂ) : meromorphicOrderAt R z = meromorphicOrderAt L z := by
    change meromorphicOrderAt (L' ∘ fun w : ℂ ↦ 1 - w) z = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (ha z) (by simp), horder', horder]
    exact (globalHeckeOrderReference_reflect F ν ω r r' hr hr' z).symm
  have hfinite (z : ℂ) : meromorphicOrderAt L z ≠ ⊤ := by
    have h₂ : meromorphicOrderAt L (2 : ℂ) = 0 :=
      hout 2 (Or.inr (by norm_num))
    exact ((hL.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).mp
      ⟨2, mem_univ _, by rw [h₂]; exact WithTop.zero_ne_top⟩) z (mem_univ z)
  obtain ⟨ε, hε, he⟩ := entire_normalized_transform hm hL hfinite (fun z ↦ (ho z).ge)
  refine ⟨T, ht, huT, L, L', ε, hL, hL', hEq, hEq', hε, ?_, he⟩
  intro z
  have hz := hε z (mem_univ z)
  have hsum : meromorphicOrderAt L z + meromorphicOrderAt ε z =
      meromorphicOrderAt L z + 0 := by
    calc
      _ = meromorphicOrderAt (L * ε) z :=
        (meromorphicOrderAt_mul (hL z (mem_univ z)) hz.meromorphicAt).symm
      _ = meromorphicOrderAt R z := (meromorphicOrderAt_congr (he z)).symm
      _ = _ := (ho z).trans (add_zero _).symm
  exact hz.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    (WithTop.add_left_cancel (hfinite z) hsum)


end

end Masullo
