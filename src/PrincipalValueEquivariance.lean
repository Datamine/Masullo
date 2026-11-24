import SLocalPrincipalRangeGlobal
import ThetaTranslationContinuity
import CompactGroupAveraging

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Coord (S : Finset (Place F)) := (v : S) → v.val.adicCompletion F
private abbrev Test (S : Finset (Place F)) := locallyConstantTests (Coord F S)
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S

private theorem sLocalRestriction_ext {S : Finset (Place F)} {f g : E F S}
    (h : ∀ x, sLocalBruhatRestriction F S f.val x = sLocalBruhatRestriction F S g.val x) : f = g := by
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x f.val = GlobalBruhat.evaluation F x g.val
  rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatRestriction_reconstruct, h]

private theorem sLocalBruhatLeftTranslate_pure (S : Finset (Place F)) (g : (SAdeles F S)ˣ)
    (φ : Arch F) (ψ : Test F S) :
    sLocalBruhatLeftTranslate F S g (sLocalBruhatPure F S φ ψ) =
      sLocalBruhatPure F S
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archDilation F (sLocalEmbed F S g).val) φ)
        (locallyConstantTestTranslate _ (MulEquiv.prodUnits g).2 ψ) := by
  apply sLocalRestriction_ext F
  intro x
  rw [sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict]
  have hp : sAdelesProjection F S ((sLocalEmbed F S g).val⁻¹).val = g.inv := by
    rw [← Subgroup.coe_inv, ← map_inv]
    exact sLocalEmbed_project F S g⁻¹
  have ha : mixedArch (F := F) ((sLocalEmbed F S g).val⁻¹).val =
      InfiniteAdeleRing.ringEquiv_mixedSpace F g.inv.1 := by
    calc
      _ = InfiniteAdeleRing.ringEquiv_mixedSpace F
          (sAdelesProjection F S ((sLocalEmbed F S g).val⁻¹).val).1 := rfl
      _ = _ := congrArg (fun u : SAdeles F S ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F u.1) hp
  change φ (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.inv.1 * x.1)) * ψ.val (g.inv.2 * x.2) =
    φ (mixedArch (F := F) ((sLocalEmbed F S g).val⁻¹).val *
      InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * ψ.val (g.inv.2 * x.2)
  rw [ha, map_mul]

/-- A principal value in one finite coordinate commutes with every
S-local idele translation on Schwartz–Bruhat tests. -/
theorem sLocalWeilPrincipalValue_translate (S : Finset (Place F)) (v : S)
    (g : (SAdeles F S)ˣ) :
    Commute (sLocalWeilPrincipalValue F S v) (sLocalBruhatLeftTranslate F S g) := by
  apply ContinuousLinearMap.ext
  intro f
  letI : TopologicalSpace (Test F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] Test F S) := inductiveTensorTopology _ _
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    change sLocalBruhatFiniteMap F S _ (sLocalBruhatLeftTranslate F S g (sLocalBruhatPure F S φ ψ)) =
      sLocalBruhatLeftTranslate F S g (sLocalBruhatFiniteMap F S _ (sLocalBruhatPure F S φ ψ))
    rw [sLocalBruhatLeftTranslate_pure, sLocalBruhatFiniteMap_pure, sLocalBruhatFiniteMap_pure,
      sLocalBruhatLeftTranslate_pure,
      sLocalCoordinateMap_translate F S v (weilPrincipalValue F v) (MulEquiv.prodUnits g).2
        (weilPrincipalValue_commute F v)]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem sLocalWeilPrincipalValues_translate (S : Finset (Place F)) (T : Finset S)
    (g : (SAdeles F S)ˣ) :
    Commute (sLocalWeilPrincipalValues F S T) (sLocalBruhatLeftTranslate F S g) := by
  unfold sLocalWeilPrincipalValues
  refine Finset.noncommProd_induction T (sLocalWeilPrincipalValue F S) _
    (fun L : E F S →L[ℂ] E F S => Commute L (sLocalBruhatLeftTranslate F S g)) ?_ ?_ ?_
  · exact fun _ _ ha hb => Commute.mul_left ha hb
  · exact Commute.one_left _
  · exact fun v _ => sLocalWeilPrincipalValue_translate F S v g

/-- Choose one finite stage that contains the test, the operator's
places, and every nonunit component of the translating idele. -/
theorem globalWeilPrincipalValues_translate (T : Finset (Place F)) (g : Idele F) :
    Commute (globalWeilPrincipalValues F T) (GlobalBruhat.leftTranslate F g) := by
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨A, a, ha⟩ := globalBruhat_exhausted F f
  obtain ⟨B, hg⟩ := sIdeleBlock_cover F g
  let S := A ∪ (B ∪ T)
  let b : sIdeleBlock F S := ⟨g, sIdeleBlock_mono F
    (Finset.subset_union_left.trans Finset.subset_union_right : B ⊆ S) hg⟩
  let x := sLocalBruhatTransition F (show A ⊆ S from Finset.subset_union_left) a
  let U : Finset S := Finset.univ.filter fun v ↦ v.val ∈ T
  have hU : U.map ⟨Subtype.val, Subtype.val_injective⟩ = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro hv
      have hvS : v ∈ S := Finset.mem_union_right A (Finset.mem_union_right B hv)
      exact Finset.mem_map.mpr ⟨⟨v, hvS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  let c := (sBlockUnitProduct F S b).1
  let L := sLocalBruhatLeftTranslate F S c
  let P := sLocalWeilPrincipalValues F S U
  have hL (y : E F S) : GlobalBruhat.leftTranslate F g y.val = (L y).val :=
    bruhatTranslate_block_eq F S b y
  have hP (y : E F S) : globalWeilPrincipalValues F T y.val = (P y).val := by
    rw [← hU]
    exact globalWeilPrincipalValues_stage F S U y
  have hx : x.val = f := ha
  change globalWeilPrincipalValues F T (GlobalBruhat.leftTranslate F g f) =
    GlobalBruhat.leftTranslate F g (globalWeilPrincipalValues F T f)
  rw [← hx, hL x, hP x, hP (L x), hL (P x)]
  exact congrArg Subtype.val (DFunLike.congr_fun (sLocalWeilPrincipalValues_translate F S U c).eq x)

theorem sLocalWeilPrincipalValuesQuotient_translate (S : Finset (Place F)) (T : Finset S)
    (P : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S)
    (hP : ∀ f : E F S,
      P ((sLocalThetaOperator F S).ker.mkQ f) =
        (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S T f))
    (c : SIdeleQuotient F S) : Commute P (sLocalThetaTranslate F S c) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := (sLocalThetaOperator F S).ker.mkQ_surjective y
  let Q := (sLocalThetaOperator F S).ker.mkQ
  let L := sLocalBruhatLeftTranslate F S g
  let V := sLocalWeilPrincipalValues F S T
  change P (Q (L f)) = sLocalThetaTranslateIdeles F S g (P (Q f))
  rw [hP (L f), hP f]
  change Q (V (L f)) = Q (L (V f))
  exact congrArg Q (DFunLike.congr_fun (sLocalWeilPrincipalValues_translate F S T g).eq f)

theorem globalWeilPrincipalValuesQuotient_translate (T : Finset (Place F))
    (c : IdeleClass F) : Commute (globalWeilPrincipalValuesQuotient F T) (globalThetaTranslate F c) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := (globalThetaOperator F).ker.mkQ_surjective y
  let Q := (globalThetaOperator F).ker.mkQ
  let L := GlobalBruhat.leftTranslate F g
  let P := globalWeilPrincipalValues F T
  change Q (P (L f)) = Q (L (P f))
  exact congrArg Q (DFunLike.congr_fun (globalWeilPrincipalValues_translate F T g).eq f)

/-- Equivariance preserves the actual norm-one character isotypes of the
global ordinary theta quotient. -/
theorem globalWeilPrincipalValuesQuotient_isotype (T : Finset (Place F))
    (ω : PontryaginDual (normOneIdeleClass F)) (q : GlobalThetaQuotient F)
    (hq : ∀ c : normOneIdeleClass F, globalThetaTranslate F c.val q = (↑(ω c) : ℂ) • q)
    (c : normOneIdeleClass F) :
    globalThetaTranslate F c.val (globalWeilPrincipalValuesQuotient F T q) =
      (↑(ω c) : ℂ) • globalWeilPrincipalValuesQuotient F T q := by
  have he := DFunLike.congr_fun (globalWeilPrincipalValuesQuotient_translate F T c.val).eq q
  change globalWeilPrincipalValuesQuotient F T (globalThetaTranslate F c.val q) =
    globalThetaTranslate F c.val (globalWeilPrincipalValuesQuotient F T q) at he
  rw [hq c, map_smul] at he
  exact he.symm

/-- Equivariance likewise preserves every S-local ordinary theta isotype. -/
theorem sLocalWeilPrincipalValuesQuotient_isotype (S : Finset (Place F)) (T : Finset S)
    (P : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S)
    (hP : ∀ f : E F S,
      P ((sLocalThetaOperator F S).ker.mkQ f) =
        (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S T f))
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (q : SLocalThetaQuotient F S)
    (hq : ∀ c : SLocalThetaNormOne F S, sLocalThetaTranslate F S c.val q = (↑(ω c) : ℂ) • q)
    (c : SLocalThetaNormOne F S) :
    sLocalThetaTranslate F S c.val (P q) = (↑(ω c) : ℂ) • P q := by
  have he := DFunLike.congr_fun (sLocalWeilPrincipalValuesQuotient_translate F S T P hP c.val).eq q
  change P (sLocalThetaTranslate F S c.val q) = sLocalThetaTranslate F S c.val (P q) at he
  rw [hq c, map_smul] at he
  exact he.symm

/-- The injective descended operator also reflects the character
condition, so it cannot move a vector into a new isotype. -/
theorem globalWeilPrincipalValuesQuotient_isotype_iff (T : Finset (Place F))
    (ω : PontryaginDual (normOneIdeleClass F)) (q : GlobalThetaQuotient F) :
    (∀ c : normOneIdeleClass F, globalThetaTranslate F c.val (globalWeilPrincipalValuesQuotient F T q) =
      (↑(ω c) : ℂ) • globalWeilPrincipalValuesQuotient F T q) ↔
    ∀ c : normOneIdeleClass F, globalThetaTranslate F c.val q = (↑(ω c) : ℂ) • q := by
  refine ⟨?_, globalWeilPrincipalValuesQuotient_isotype F T ω q⟩
  intro h c
  apply globalWeilPrincipalValuesQuotient_injective F T
  have he := DFunLike.congr_fun (globalWeilPrincipalValuesQuotient_translate F T c.val).eq q
  exact he.trans ((h c).trans (map_smul _ _ _).symm)

theorem sLocalWeilPrincipalValuesQuotient_isotype_iff (S : Finset (Place F)) (T : Finset S)
    (P : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S)
    (hP : ∀ f : E F S,
      P ((sLocalThetaOperator F S).ker.mkQ f) =
        (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S T f))
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (q : SLocalThetaQuotient F S) :
    (∀ c : SLocalThetaNormOne F S, sLocalThetaTranslate F S c.val (P q) = (↑(ω c) : ℂ) • P q) ↔
    ∀ c : SLocalThetaNormOne F S, sLocalThetaTranslate F S c.val q = (↑(ω c) : ℂ) • q := by
  obtain ⟨Q, ⟨hQ, hQmk⟩, _⟩ := existsUnique_sLocalWeilPrincipalValuesQuotient F S T
  have heq : P = Q := by
    ext y
    obtain ⟨f, rfl⟩ := (sLocalThetaOperator F S).ker.mkQ_surjective y
    exact (hP f).trans (hQmk f).symm
  have hi : Injective P := heq.symm ▸ hQ
  refine ⟨?_, sLocalWeilPrincipalValuesQuotient_isotype F S T P hP ω q⟩
  intro h c
  apply hi
  have he := DFunLike.congr_fun (sLocalWeilPrincipalValuesQuotient_translate F S T P hP c.val).eq q
  exact he.trans ((h c).trans (map_smul _ _ _).symm)

private theorem pettisAverage_commutes {K E : Type*} [MeasurableSpace K]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [T2Space E] [PolynormableSpace ℂ E]
    (ν : Measure K) (d : K → ℂ) (ρ : K → E →L[ℂ] E)
    (P A : E →L[ℂ] E) (hP : ∀ k x, P (ρ k x) = ρ k (P x))
    (hA : ∀ x, HasPositivePettisIntegral ν (fun k ↦ d k • ρ k x) (A x)) (x : E) :
    P (A x) = A (P x) := by
  symm
  apply positivePettis_integral_unique (hA (P x))
  intro ℓ
  have h := hA x (ℓ.comp P)
  simpa only [ContinuousLinearMap.comp_apply, map_smul, hP, Function.comp_def] using h

/-- Principal values commute with every global theta character average
represented by the Pettis integral of the weighted norm-one action. -/
theorem globalWeilPrincipalValuesQuotient_average (T : Finset (Place F))
    [MeasurableSpace (normOneIdeleClass F)] (ν : Measure (normOneIdeleClass F))
    (ω : PontryaginDual (normOneIdeleClass F))
    (A : GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F)
    (hA : ∀ q, HasPositivePettisIntegral ν
      (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • globalThetaTranslate F k.val q) (A q))
    (q : GlobalThetaQuotient F) :
    globalWeilPrincipalValuesQuotient F T (A q) = A (globalWeilPrincipalValuesQuotient F T q) := by
  letI : UniformSpace (GlobalThetaQuotient F) := IsTopologicalAddGroup.rightUniformSpace _
  letI : T2Space (GlobalThetaQuotient F) := globalThetaQuotient_t2Space F
  letI : PolynormableSpace ℂ (GlobalThetaQuotient F) :=
    polynormableSpace_complex_quotient (globalThetaOperator F).ker
  let P := globalWeilPrincipalValuesQuotient F T
  exact pettisAverage_commutes ν (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ))
    (fun k ↦ globalThetaTranslate F k.val) P A
    (fun k x ↦ DFunLike.congr_fun (globalWeilPrincipalValuesQuotient_translate F T k.val).eq x) hA q

/-- The S-local principal values commute with the corresponding Pettis
character average on the ordinary local theta quotient. -/
theorem sLocalWeilPrincipalValuesQuotient_average
    (S : Finset (Place F)) (T : Finset S)
    [MeasurableSpace (SLocalThetaNormOne F S)] (ν : Measure (SLocalThetaNormOne F S))
    (ω : PontryaginDual (SLocalThetaNormOne F S))
    (P A : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S)
    (hP : ∀ f : E F S,
      P ((sLocalThetaOperator F S).ker.mkQ f) =
        (sLocalThetaOperator F S).ker.mkQ (sLocalWeilPrincipalValues F S T f))
    (hA : ∀ q, HasPositivePettisIntegral ν
      (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ) • sLocalThetaTranslate F S k.val q) (A q))
    (q : SLocalThetaQuotient F S) : P (A q) = A (P q) := by
  letI : UniformSpace (SLocalThetaQuotient F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : T2Space (SLocalThetaQuotient F S) := sLocalThetaQuotient_t2Space F S
  letI : PolynormableSpace ℂ (SLocalThetaQuotient F S) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
  exact pettisAverage_commutes ν (fun k ↦ (((ω k)⁻¹ : Circle) : ℂ))
    (fun k ↦ sLocalThetaTranslate F S k.val) P A
    (fun k x ↦ DFunLike.congr_fun (sLocalWeilPrincipalValuesQuotient_translate F S T P hP k.val).eq x) hA q

end

end Masullo
