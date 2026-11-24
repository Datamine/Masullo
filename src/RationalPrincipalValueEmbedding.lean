import PrincipalValueSpectralClosure
import SLocalMultiplicativeTamagawa

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev Place (F : Type*) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)

section FiniteSupport

variable (F : Type*) [Field F] [NumberField F] (S : Finset (Place F))
private abbrev K := SLocalThetaNormOne F S
private abbrev Q := SLocalThetaQuotient F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

/-- A theta class fixed by an open subgroup of the compact norm-one class
group has only finitely many nonzero character components. -/
theorem sLocalTheta_finite_components_of_open_fixed
    (ν : Measure (K F S)) [ν.IsHaarMeasure]
    (q : Q F S) (J : Subgroup (K F S)) (hJ : IsOpen (J : Set (K F S)))
    (hq : ∀ k ∈ J, sLocalNormOneAction F S k q = q) :
    ∃ A : Finset (PontryaginDual (K F S)),
      ∀ ω ∉ A, sLocalThetaToComponent F S ν ω q = 0 := by
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  letI : J.Normal := ⟨fun x hx g ↦ by
    have he : g * x * g⁻¹ = x := by
      apply Subtype.ext
      change g.val * x.val * g.val⁻¹ = x.val
      rw [mul_comm g.val x.val, mul_assoc, mul_inv_cancel, mul_one]
    rwa [he]⟩
  letI : DiscreteTopology (K F S ⧸ J) := QuotientGroup.discreteTopology hJ
  let D := {ω : PontryaginDual (K F S) // ∀ k ∈ J, ω k = 1}
  let lift (ω : D) : PontryaginDual (K F S ⧸ J) :=
    ⟨QuotientGroup.lift J ω.val.toMonoidHom ω.property, continuous_of_discreteTopology⟩
  have hl : Injective lift := by
    intro ω τ h
    apply Subtype.ext
    apply DFunLike.ext
    intro k
    exact DFunLike.congr_fun h (QuotientGroup.mk k)
  letI : Finite D := Finite.of_injective lift hl
  letI : Fintype D := Fintype.ofFinite D
  refine ⟨(Finset.univ : Finset D).image (fun ω : D ↦ ω.val), fun ω hω ↦ ?_⟩
  have hnot : ¬ ∀ k ∈ J, ω k = 1 := fun h ↦ hω (Finset.mem_image.mpr ⟨⟨ω,h⟩,Finset.mem_univ _,rfl⟩)
  push Not at hnot
  obtain ⟨k,hk,hne⟩ := hnot
  apply sLocalThetaToComponent_eq_zero_of_eigenvalue_ne F S ν ω q k 1
  · intro he
    exact hne (Subtype.ext (he.trans Circle.coe_one.symm))
  · rw [one_smul, hq k hk]

end FiniteSupport

section Rational

variable (S : Finset (Place ℚ))

private abbrev KRat := SLocalThetaNormOne ℚ S
private abbrev IRat := (SAdeles ℚ S)ˣ
private abbrev QRat := SLocalThetaQuotient ℚ S
private abbrev HType := ∀ j : S, Subgroup (j.val.adicCompletion ℚ)ˣ

private def realCoordinate (a : (InfiniteAdeleRing ℚ)ˣ) : ℝ :=
  InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.val Rat.infinitePlace)

private theorem realCoordinate_continuous : Continuous realCoordinate :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    ((continuous_apply Rat.infinitePlace).comp Units.continuous_val)

private theorem realCoordinate_pos_norm_one {a : (InfiniteAdeleRing ℚ)ˣ}
    (ha : 0 < realCoordinate a) (hn : ‖a.val Rat.infinitePlace‖ = 1) : a = 1 := by
  let e := InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have he : ‖e (a.val Rat.infinitePlace)‖ = ‖a.val Rat.infinitePlace‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
      (map_zero e) _
  change 0 < e (a.val Rat.infinitePlace) at ha
  rw [Real.norm_eq_abs, abs_of_pos ha, hn] at he
  have hv : a.val Rat.infinitePlace = 1 := e.injective (he.trans (map_one e).symm)
  apply Units.ext
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  exact hv

private def thetaStabilizer (q : QRat S) : Subgroup (KRat S) where
  carrier := {k | sLocalNormOneAction ℚ S k q = q}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change sLocalNormOneAction ℚ S a q = q at ha
    change sLocalNormOneAction ℚ S b q = q at hb
    change sLocalNormOneAction ℚ S (a*b) q = q
    rw [map_mul]
    change sLocalNormOneAction ℚ S a (sLocalNormOneAction ℚ S b q) = q
    rw [hb,ha]
  inv_mem' := by
    intro a ha
    change sLocalNormOneAction ℚ S a q = q at ha
    change sLocalNormOneAction ℚ S a⁻¹ q = q
    have he := congrArg (sLocalNormOneAction ℚ S a⁻¹) ha
    change (sLocalNormOneAction ℚ S a⁻¹ * sLocalNormOneAction ℚ S a) q = _ at he
    rw [← map_mul, inv_mul_cancel, map_one] at he
    exact he.symm

/-- At a rational angular level the stabilizer of an ordinary theta class
contains an open neighborhood in the norm-one class group. -/
private theorem rationalSLocalTheta_stabilizer_isOpen (H : HType S)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion ℚ)ˣ))
    (hU : ∀ j (u : H j), ‖u.val.val‖ = 1)
    (q : QRat S) (hq : q ∈ sLocalThetaInvariantTestSpan ℚ S H) :
    IsOpen (thetaStabilizer S q : Set (KRat S)) := by
  let e := sLocalZetaIdeleCoordinates ℚ S
  let π := QuotientGroup.mk' (sUnitImage ℚ S)
  let U : Set (IRat S) := e ⁻¹' ({a | 0 < realCoordinate a} ×ˢ Set.pi univ (fun j ↦ (H j : Set _)))
  have hUopen : IsOpen U := ((isOpen_lt continuous_const realCoordinate_continuous).prod
    (isOpen_set_pi (finite_univ) fun j _ ↦ hH j)).preimage e.continuous
  have h1 : (1 : IRat S) ∈ U := by
    change e 1 ∈ {a | 0 < realCoordinate a} ×ˢ Set.pi univ (fun j ↦ (H j : Set _))
    rw [map_one e]
    refine ⟨?_, fun j _ ↦ (H j).one_mem⟩
    change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace 1
    rw [map_one]
    exact zero_lt_one
  let V : Set (KRat S) := Subtype.val ⁻¹' (π '' U)
  have hV : IsOpen V :=
    (QuotientGroup.isOpenMap_coe (N := sUnitImage ℚ S) U hUopen).preimage continuous_subtype_val
  have hV1 : (1 : KRat S) ∈ V := ⟨1,h1,map_one π⟩
  apply (thetaStabilizer S q).isOpen_of_mem_nhds (Filter.mem_of_superset (hV.mem_nhds hV1) ?_)
  rintro k ⟨d,hd,hk⟩
  let p := e d
  have hpos : 0 < realCoordinate p.1 := hd.1
  let b (j : S) : H j := ⟨p.2 j, hd.2 j (mem_univ _)⟩
  have hnorm : sLocalIdeleNorm ℚ S d = 1 := by
    rw [← sLocalClassModulus_mk ℚ S d]
    change sLocalClassModulus ℚ S (π d) = 1
    rw [hk]
    change ((sQuotientNorm ℚ S k.val).val : ℝ) = 1
    rw [show sQuotientNorm ℚ S k.val = 1 from k.property]
    rfl
  have harch : ‖p.1.val Rat.infinitePlace‖ = 1 := by
    rw [← e.symm_apply_apply d, sLocalZetaIdeleCoordinates_norm,
      Fintype.prod_subsingleton _ Rat.infinitePlace, Rat.isReal_infinitePlace.mult_eq_one, pow_one] at hnorm
    change ‖p.1.val Rat.infinitePlace‖ * ∏ j : S, ‖(p.2 j).val‖ = 1 at hnorm
    simpa only [show ∀ j, ‖(p.2 j).val‖ = 1 from fun j ↦ hU j (b j),
      Finset.prod_const_one, mul_one] using hnorm
  have harch' : p.1 = 1 := realCoordinate_pos_norm_one hpos harch
  have hd' : d = angularLocalIdele ℚ S H b := by
    calc
      d = e.symm p := (e.symm_apply_apply d).symm
      _ = e.symm (1,p.2) := congrArg e.symm (Prod.ext harch' rfl)
      _ = angularLocalIdele ℚ S H b := Units.ext rfl
  change sLocalThetaTranslate ℚ S k.val q = q
  rw [← hk, hd']
  exact sLocalThetaInvariantTestSpan_fixed ℚ S H q hq b

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

local instance (v : Place ℚ) : MeasurableSpace (v.adicCompletion ℚ) := borel _
local instance (v : Place ℚ) : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
local instance (v : Place ℚ) : MeasurableSpace (v.adicCompletion ℚ)ˣ := borel _
local instance (v : Place ℚ) : BorelSpace (v.adicCompletion ℚ)ˣ := ⟨rfl⟩
local instance : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ := borel _
local instance : BorelSpace (InfiniteAdeleRing ℚ)ˣ := ⟨rfl⟩

/-- Every ordinary rational S-local theta class has finite norm-one character support. -/
theorem rationalSLocalTheta_finite_components (ν : Measure (KRat S)) [ν.IsHaarMeasure]
    (q : QRat S) : ∃ A : Finset (PontryaginDual (KRat S)),
      ∀ ω ∉ A, sLocalThetaToComponent ℚ S ν ω q = 0 := by
  obtain ⟨H,hH,hn,_,hcover,_⟩ := sLocalTheta_exists_angularStages ℚ S
  obtain ⟨n,hqn⟩ := hcover q
  exact sLocalTheta_finite_components_of_open_fixed ℚ S ν q
    (thetaStabilizer S q) (rationalSLocalTheta_stabilizer_isOpen S (H n) (hH n) (hn n) q hqn)
    (fun _ hk ↦ hk)

/-- For the rational field the principal-value product is a closed
topological embedding of the actual ordinary S-local theta quotient. -/
theorem rationalSLocalThetaPrincipalValues_closedEmbedding (W : Finset S) :
    IsClosedEmbedding (sLocalThetaPrincipalValues ℚ S W) := by
  let P := sLocalThetaPrincipalValues ℚ S W
  let μ (v : S) := finitePlaceMultiplicativeTamagawa ℚ v.val
  letI (v : S) : (μ v).IsHaarMeasure := finitePlaceMultiplicativeTamagawa_isHaar ℚ v.val
  letI (v : S) : LocallyCompactSpace (v.val.adicCompletion ℚ)ˣ := by
    letI := finitePlace_locallyCompact ℚ v.val
    exact IsOpenUnits.isOpenEmbedding_unitsVal.locallyCompactSpace
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion ℚ)ˣ := by
    letI := finitePlace_secondCountable ℚ v.val
    exact IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.secondCountableTopology
  letI (v : S) : SigmaFinite (μ v) := inferInstance
  obtain ⟨ν,hν,hw⟩ := sLocalMultiplicativeTamagawa_exists_weil ℚ S
  letI : ν.IsHaarMeasure := hν
  letI : SecondCountableTopology (IRat S) := sLocalIdeles_secondCountable ℚ S
  letI : SecondCountableTopology (SIdeleQuotient ℚ S) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.secondCountableTopology
      QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  letI : T1Space (SIdeleQuotient ℚ S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed ℚ S)
  letI : SecondCountableTopology (KRat S) := IsInducing.subtypeVal.secondCountableTopology
  letI : CompactSpace (KRat S) := sLocalThetaNormOne_compact ℚ S
  letI : ν.WeaklyRegular :=
    (Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν).weaklyRegular
  have hclosed : IsClosed (range P) := by
    apply isClosed_of_closure_subset
    intro q hq
    obtain ⟨A,hA⟩ := rationalSLocalTheta_finite_components S ν q
    have hc := (sLocalTheta_mem_closure_principalRange_iff_components ℚ S ν μ hw W q).mp hq
    exact sLocalTheta_mem_principalRange_of_finite_components ℚ S ν W q A hA fun ω _ ↦ hc ω
  apply (sLocalThetaPrincipalValues_closedEmbedding_iff_angular ℚ S W).mpr
  intro H _ _
  exact hclosed.preimage (sLocalThetaInvariantTestSpan ℚ S H).subtypeL.continuous

/-- For the rational field the principal-value product is a closed
topological embedding of the actual ordinary global theta quotient. -/
theorem rationalGlobalThetaPrincipalValues_closedEmbedding (W : Finset (Place ℚ)) :
    IsClosedEmbedding (globalWeilPrincipalValuesQuotient ℚ W) := by
  apply (globalThetaPrincipalValues_closedEmbedding_iff ℚ W).mpr
  intro T _
  exact rationalSLocalThetaPrincipalValues_closedEmbedding T _

end Rational
end
end Masullo
