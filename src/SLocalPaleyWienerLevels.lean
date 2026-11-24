import SLocalPaleyWienerDensity
import SLocalPaleyWienerBoxTransition

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev P := HeightOneSpectrum (𝓞 F)
private abbrev E := sLocalBruhatImage F

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable (T : Finset (P F))
variable (ν : Measure (SLocalThetaNormOne F T)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (SLocalThetaNormOne F T))

private abbrev M := sLocalHomogeneousThetaKernel F T ν ω
private abbrev Q := SLocalHomogeneousThetaQuotient F T ν ω

/-- The continuous left action on the homogeneous theta quotient. -/
def sLocalHomogeneousThetaTranslate (c : SIdeleQuotient F T) : Q F T ν ω →L[ℂ] Q F T ν ω :=
  (sLocalThetaToComponent F T ν ω).comp
    ((sLocalThetaTranslate F T c).comp (sLocalThetaComponent_isotypicSection F T ν ω).choose)

theorem continuous_sLocalHomogeneousThetaTranslate :
    Continuous (fun p : SIdeleQuotient F T × Q F T ν ω ↦
      sLocalHomogeneousThetaTranslate F T ν ω p.1 p.2) :=
  (sLocalThetaToComponent F T ν ω).continuous.comp <| (continuous_sLocalThetaTranslate F T).comp
    (continuous_fst.prodMk ((sLocalThetaComponent_isotypicSection F T ν ω).choose.continuous.comp
      continuous_snd))

def sLocalHomogeneousThetaEvalLinear (q : SIdeleQuotient F T) : E F T →ₗ[ℂ] ℂ where
  toFun f := sLocalHomogeneousTheta F T ν ω f.val q
  map_add' f g := by
    unfold sLocalHomogeneousTheta
    rw [← integral_add (sLocalHomogeneousTheta_integrable F T ν ω f.val q)
      (sLocalHomogeneousTheta_integrable F T ν ω g.val q)]
    apply integral_congr_ae (.of_forall fun k ↦ ?_)
    change (ω k : ℂ) * sLocalThetaOperator F T (f+g) (k.val*q) =
      (ω k : ℂ) * sLocalThetaOperator F T f (k.val*q) +
        (ω k : ℂ) * sLocalThetaOperator F T g (k.val*q)
    rw [map_add, Pi.add_apply, mul_add]
  map_smul' a f := by
    unfold sLocalHomogeneousTheta
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    apply integral_congr_ae (.of_forall fun k ↦ ?_)
    change (ω k : ℂ) * sLocalThetaOperator F T (a • f) (k.val*q) =
      a * ((ω k : ℂ) * sLocalThetaOperator F T f (k.val*q))
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

private theorem sLocalHomogeneousTheta_mkQ_eq_iff (f g : E F T) :
    (M F T ν ω).mkQ f = (M F T ν ω).mkQ g ↔
      ∀ q, sLocalHomogeneousTheta F T ν ω f.val q = sLocalHomogeneousTheta F T ν ω g.val q := by
  change (Submodule.Quotient.mk f : Q F T ν ω) = Submodule.Quotient.mk g ↔ _
  rw [Submodule.Quotient.eq (M F T ν ω), mem_sLocalHomogeneousThetaKernel_iff]
  apply forall_congr'
  intro q
  let L := sLocalHomogeneousThetaEvalLinear F T ν ω q
  change L (f-g) = 0 ↔ L f = L g
  rw [map_sub, sub_eq_zero]

/-- On a nontrivial S-local homogeneous component the image of the common
polar kernel is the whole quotient, without a class group hypothesis. -/
theorem sLocalPolarFree_image_eq_top_of_ne_one (hω : ω ≠ 1) :
    let P := ((GlobalBruhat.polarEvaluation F).comp (E F T).subtypeL).ker
    P.map (M F T ν ω).mkQ = ⊤ := by
  intro P
  obtain ⟨k, hk⟩ : ∃ k : SLocalThetaNormOne F T, ω k ≠ 1 := by
    by_contra! h
    apply hω
    ext k
    exact congrArg Subtype.val (h k)
  let c : ℂ := (ω k : Circle)
  have hc : c - 1 ≠ 0 := fun e => hk (Circle.coe_injective (by simpa [c] using sub_eq_zero.mp e))
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective k.val
  have hnorm : sLocalIdeleNorm F T u = 1 := by
    rw [← sLocalClassModulus_mk, hu]
    have hk₀ : sQuotientNorm F T k.val = 1 := k.property
    simp [sLocalClassModulus, hk₀]
  apply top_unique
  intro q _
  obtain ⟨f, rfl⟩ := (M F T ν ω).mkQ_surjective q
  let t := sLocalBruhatLeftTranslate F T u f
  let g := (c - 1)⁻¹ • (t - f)
  have ht : GlobalBruhat.polarEvaluation F t.val = GlobalBruhat.polarEvaluation F f.val := by
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.leftTranslate F (sLocalEmbed F T u).val f.val) = _
    rw [polarEvaluation_leftTranslate, show ideleNorm F (sLocalEmbed F T u).val = 1 from hnorm, one_smul]
  have hg : g ∈ P := by
    change GlobalBruhat.polarEvaluation F ((c - 1)⁻¹ • (t.val - f.val)) = 0
    rw [map_smul, map_sub, ht, sub_self, smul_zero]
  refine Submodule.mem_map.mpr ⟨g, hg, (sLocalHomogeneousTheta_mkQ_eq_iff F T ν ω _ _).2 ?_⟩
  intro x
  let L := sLocalHomogeneousThetaEvalLinear F T ν ω x
  change L ((c - 1)⁻¹ • (t - f)) = L f
  have he : L t = c * L f := sLocalHomogeneousTheta_leftTranslate_normOne F T ν ω k u hu f x
  rw [map_smul, map_sub, he, smul_eq_mul, ← sub_one_mul, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

theorem sLocalHomogeneousThetaTranslate_mkQ
    (u : (SAdeles F T)ˣ) (f : E F T) :
    sLocalHomogeneousThetaTranslate F T ν ω (QuotientGroup.mk u) ((M F T ν ω).mkQ f) =
      (M F T ν ω).mkQ (sLocalBruhatLeftTranslate F T u f) := by
  let N := (sLocalThetaOperator F T).ker
  let j := (sLocalThetaComponent_isotypicSection F T ν ω).choose
  obtain ⟨g,hg⟩ := N.mkQ_surjective (j ((M F T ν ω).mkQ f))
  have he : (M F T ν ω).mkQ g = (M F T ν ω).mkQ f := by
    change sLocalThetaToComponent F T ν ω (N.mkQ g) = _
    rw [hg]
    exact (sLocalThetaComponent_isotypicSection F T ν ω).choose_spec.1 _
  unfold sLocalHomogeneousThetaTranslate
  simp only [ContinuousLinearMap.comp_apply]
  change sLocalThetaToComponent F T ν ω (sLocalThetaTranslate F T (QuotientGroup.mk u)
    (j ((M F T ν ω).mkQ f))) = _
  rw [← hg]
  change (M F T ν ω).mkQ (sLocalBruhatLeftTranslate F T u g) = _
  apply (sLocalHomogeneousTheta_mkQ_eq_iff F T ν ω _ _).mpr
  intro q
  rw [sLocalHomogeneousTheta_translate_test, sLocalHomogeneousTheta_translate_test]
  exact (sLocalHomogeneousTheta_mkQ_eq_iff F T ν ω _ _).mp he _

theorem sLocalHomogeneousThetaTranslate_one (x : Q F T ν ω) :
    sLocalHomogeneousThetaTranslate F T ν ω 1 x = x := by
  obtain ⟨f,rfl⟩ := (M F T ν ω).mkQ_surjective x
  have he : (QuotientGroup.mk (1 : (SAdeles F T)ˣ) : SIdeleQuotient F T) = 1 :=
    map_one (QuotientGroup.mk' (sUnitImage F T))
  rw [← he, sLocalHomogeneousThetaTranslate_mkQ]
  apply (sLocalHomogeneousTheta_mkQ_eq_iff F T ν ω _ _).mpr
  intro q
  rw [sLocalHomogeneousTheta_translate_test, he, inv_one]
  exact congrArg (sLocalHomogeneousTheta F T ν ω f.val) (one_mul q)

theorem sLocalHomogeneousThetaTranslate_mul
    (c d : SIdeleQuotient F T) (x : Q F T ν ω) :
    sLocalHomogeneousThetaTranslate F T ν ω (c*d) x =
      sLocalHomogeneousThetaTranslate F T ν ω c (sLocalHomogeneousThetaTranslate F T ν ω d x) := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨v,rfl⟩ := QuotientGroup.mk_surjective d
  obtain ⟨f,rfl⟩ := (M F T ν ω).mkQ_surjective x
  let p := QuotientGroup.mk' (sUnitImage F T)
  have h : p (u*v) = p u * p v := map_mul p u v
  change sLocalHomogeneousThetaTranslate F T ν ω (p u * p v) ((M F T ν ω).mkQ f) = _
  rw [← h]
  change sLocalHomogeneousThetaTranslate F T ν ω (QuotientGroup.mk (u*v)) ((M F T ν ω).mkQ f) = _
  rw [sLocalHomogeneousThetaTranslate_mkQ (F := F) T ν ω (u*v) f,
    sLocalHomogeneousThetaTranslate_mkQ (F := F) T ν ω v f,
    sLocalHomogeneousThetaTranslate_mkQ (F := F) T ν ω u (sLocalBruhatLeftTranslate F T v f)]
  apply (sLocalHomogeneousTheta_mkQ_eq_iff F T ν ω _ _).mpr
  intro q
  rw [sLocalHomogeneousTheta_translate_test, sLocalHomogeneousTheta_translate_test,
    sLocalHomogeneousTheta_translate_test]
  have he : (p (u*v))⁻¹ * q = (p v)⁻¹ * ((p u)⁻¹ * q) :=
    (congrArg (fun a : SIdeleQuotient F T ↦ a⁻¹ * q) h).trans
      ((congrArg (fun a : SIdeleQuotient F T ↦ a*q) (mul_inv_rev (p u) (p v))).trans
        (mul_assoc (p v)⁻¹ (p u)⁻¹ q))
  exact congrArg (sLocalHomogeneousTheta F T ν ω f.val) he

/-- The moment constraint for the zero-moment levels. -/
def sLocalPaleyWienerMomentKernel : Submodule ℂ (E F T) :=
  ((GlobalBruhat.polarEvaluation F).toLinearMap.comp (E F T).subtype).ker

/-- Closed homogeneous level associated with a Fourier region and a linear
constraint on test representatives. The two manuscript levels use the full
test submodule and the kernel of the evaluation moments. -/
def sLocalPaleyWienerThetaLevel {S : Finset (P F)} (hST : S ⊆ T)
    (K : Set (SAdeles F S)) (D : Submodule ℂ (E F T)) : Submodule ℂ (Q F T ν ω) :=
  (((sLocalPaleyWienerStageTests F S hST K) ⊓ D).map (M F T ν ω).mkQ).topologicalClosure

theorem sLocalPaleyWienerThetaLevel_mono {S : Finset (P F)} (hST : S ⊆ T)
    (D : Submodule ℂ (E F T)) : Monotone (fun K ↦ sLocalPaleyWienerThetaLevel F T ν ω hST K D) := by
  intro K L h
  apply Submodule.topologicalClosure_mono
  exact Submodule.map_mono (inf_le_inf (sLocalPaleyWienerStageTests_mono F S hST h) le_rfl)

theorem sLocalPaleyWienerThetaLevel_translate {S : Finset (P F)}
    (hST : S ⊆ T) (K L : Set (SAdeles F S))
    (D : Submodule ℂ (E F T)) (hD : D = ⊤ ∨ D = sLocalPaleyWienerMomentKernel F T)
    (c : SIdeleQuotient F T)
    (hlevel : ∀ f ∈ sLocalPaleyWienerStageTests F S hST K,
      ∃ g ∈ sLocalPaleyWienerStageTests F S hST L,
        (GlobalBruhat.polarEvaluation F f.val = 0 → GlobalBruhat.polarEvaluation F g.val = 0) ∧
        ∀ q, sLocalHomogeneousTheta F T ν ω g.val q = sLocalHomogeneousTheta F T ν ω f.val (c⁻¹ * q)) :
    MapsTo (sLocalHomogeneousThetaTranslate F T ν ω c)
      (sLocalPaleyWienerThetaLevel F T ν ω hST K D)
      (sLocalPaleyWienerThetaLevel F T ν ω hST L D) := by
  let A := (((sLocalPaleyWienerStageTests F S hST K) ⊓ D).map (M F T ν ω).mkQ : Set (Q F T ν ω))
  let B := (((sLocalPaleyWienerStageTests F S hST L) ⊓ D).map (M F T ν ω).mkQ : Set (Q F T ν ω))
  have hA : MapsTo (sLocalHomogeneousThetaTranslate F T ν ω c) A B := by
    intro x hx
    obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨g,hg,hm,he⟩ := hlevel f hf.1
    have hmem : g ∈ D := by
      rcases hD with rfl | rfl
      · trivial
      · exact hm hf.2
    refine Submodule.mem_map.mpr ⟨g,⟨hg,hmem⟩,?_⟩
    obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective c
    rw [sLocalHomogeneousThetaTranslate_mkQ]
    apply (sLocalHomogeneousTheta_mkQ_eq_iff F T ν ω _ _).mpr
    intro q
    rw [sLocalHomogeneousTheta_translate_test]
    exact he q
  exact hA.closure (sLocalHomogeneousThetaTranslate F T ν ω c).continuous


theorem sLocalAbsolutePaleyWienerThetaLevel_translate {S : Finset (P F)} (hST : S ⊆ T)
    (X : ℝ) (D : Submodule ℂ (E F T)) (hD : D = ⊤ ∨ D = sLocalPaleyWienerMomentKernel F T)
    (c : SIdeleQuotient F T) (hc : 1 ≤ sLocalClassModulus F T c) :
    let A := sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) D
    MapsTo (sLocalHomogeneousThetaTranslate F T ν ω c) A A :=
  sLocalPaleyWienerThetaLevel_translate F T ν ω hST _ _ D hD c
    (fun f hf ↦ sLocalAbsolutePaleyWiener_translate F S ν ω hST X f hf c hc)

theorem sLocalInvariantPaleyWienerThetaLevel_translate {S : Finset (P F)} (hST : S ⊆ T)
    (Y : ℝ) (D : Submodule ℂ (E F T)) (hD : D = ⊤ ∨ D = sLocalPaleyWienerMomentKernel F T)
    (c : SIdeleQuotient F T) (hc : 1 ≤ sLocalClassModulus F T c) :
    let A := sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerRegion F S Y) D
    MapsTo (sLocalHomogeneousThetaTranslate F T ν ω c) A A :=
  sLocalPaleyWienerThetaLevel_translate F T ν ω hST _ _ D hD c
    (fun f hf ↦ sLocalInvariantPaleyWiener_translate F S ν ω hST Y f hf c hc)

theorem sLocalAbsolutePaleyWienerThetaLevel_le_enlargedBox {S : Finset (P F)}
    (hST : S ⊆ T) {X Y : ℝ} (hXY : X ≤ Y) (D : Submodule ℂ (E F T)) :
    sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) D ≤
      sLocalPaleyWienerThetaLevel F T ν ω (show T ⊆ T from le_rfl)
        (sLocalPaleyWienerBox F T (max Y (sLocalFourierTailRadius F S T))) D := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.map_mono
  apply inf_le_inf _ le_rfl
  intro f hf
  exact Submodule.mem_map.mpr
    ⟨f, sLocalAbsolutePaleyWienerStageTests_le_enlargedBox F S hST hXY hf, rfl⟩

theorem sLocalAbsolutePaleyWienerThetaLevel_le_invariant {S : Finset (P F)}
    (hST : S ⊆ T) {X : ℝ} (hX : 0 ≤ X) (D : Submodule ℂ (E F T)) :
    sLocalPaleyWienerThetaLevel F T ν ω hST (sLocalPaleyWienerBox F S X) D ≤
      sLocalPaleyWienerThetaLevel F T ν ω hST
        (sLocalPaleyWienerRegion F S (X ^ (Fintype.card (InfinitePlace F) + S.card))) D :=
  Submodule.topologicalClosure_mono (Submodule.map_mono (inf_le_inf
    (sLocalAbsolutePaleyWienerStageTests_le_invariant F S hST hX) le_rfl))

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩

omit [ν.IsHaarMeasure] in
/-- Uniform support for the absolute levels. The upper bound applies to
the local Fourier theta function, and the lower bound applies to the
global theta function of each zero-moment test. -/
theorem sLocalAbsolutePaleyWienerTheta_support {S : Finset (P F)}
    (hST : S ⊆ T) {X : ℝ} (hX : 0 < X)
    (νG : Measure (normOneIdeleClass F)) (ωG : PontryaginDual (normOneIdeleClass F)) :
    ∃ B > (0 : ℝ), ∀ f ∈ sLocalPaleyWienerStageTests F S hST (sLocalPaleyWienerBox F S X),
      (tsupport (sLocalHomogeneousTheta F T ν ω (sLocalFourierCompression F T f).val) ⊆
        {q | sLocalClassModulus F T q ≤ B}) ∧
      (GlobalBruhat.polarEvaluation F f.val = 0 →
        tsupport (adelicHomogeneousTheta F νG ωG (fun x ↦ GlobalBruhat.evaluation F x f.val)) ⊆
          {q | B⁻¹ ≤ ideleClassNorm F q}) := by
  let Y := X ^ (Fintype.card (InfinitePlace F) + S.card)
  refine ⟨ideleNorm F (sLocalCodifferentTailIdele F S) * Y,
    mul_pos (ideleNorm_pos F _) (pow_pos hX _), ?_⟩
  intro f hf
  have h := sLocalAbsolutePaleyWienerStageTests_le_invariant F S hST hX.le hf
  exact ⟨sLocalPaleyWienerStageTests_fourierSupport F S ν ω hST f h,
    sLocalPaleyWienerStageTests_globalSupport F S νG ωG hST f (pow_pos hX _) h⟩

/-- Density of the closed levels in the full homogeneous quotient and in
the image of the two-moment kernel, respectively. -/
theorem sLocalPaleyWienerThetaLevel_sequentialDensity {S : Finset (P F)}
    (hST : S ⊆ T) (hs : Surjective (sIdeleClassInclusion F S))
    (ωG : PontryaginDual (normOneIdeleClass F))
    (hu : globalNormOneCharacter F ωG ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
    (D : Submodule ℂ (E F T)) (hD : D = ⊤ ∨ D = sLocalPaleyWienerMomentKernel F T) :
    let ωT := sLocalNormOneCharacterOfGlobal F ωG T
      (sIdeleClassInclusion_surjective_mono F hST hs) (sUnramified_mono F hST hu)
    ∀ region ∈ ({sLocalPaleyWienerBox F S, sLocalPaleyWienerRegion F S} : Set (ℝ → Set (SAdeles F S))),
    ∀ x ∈ D.map (M F T ν ωT).mkQ, ∃ g : ℕ → Q F T ν ωT,
      (∀ n, ∃ X > 0, g n ∈ sLocalPaleyWienerThetaLevel F T ν ωT hST (region X) D) ∧
      Tendsto g atTop (𝓝 x) := by
  dsimp only
  intro region hregion x hx
  obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hx
  let ωT := sLocalNormOneCharacterOfGlobal F ωG T
    (sIdeleClassInclusion_surjective_mono F hST hs) (sUnramified_mono F hST hu)
  obtain ⟨g,hg,hlim⟩ :=
    sLocalPaleyWiener_sequentialDensity_of_unramified F S hST hs ωG hu η νG hν ν f region hregion
  refine ⟨fun n ↦ (M F T ν ωT).mkQ (g n), ?_,hlim⟩
  intro n
  obtain ⟨⟨X,hX,hXmem⟩,hm⟩ := hg n
  have hmem : g n ∈ D := by
    rcases hD with rfl | rfl
    · trivial
    · exact hm hf
  exact ⟨X,hX, subset_closure (Submodule.mem_map.mpr ⟨g n,⟨hXmem,hmem⟩,rfl⟩)⟩

end

end Masullo
