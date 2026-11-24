import SLocalAdditive
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

private abbrev Place (F : Type*) [Field F] [NumberField F] := HeightOneSpectrum (𝓞 F)
private abbrev FinAdeles (F : Type*) [Field F] [NumberField F] := FiniteAdeleRing (𝓞 F) F

private def infinitePlaceUnder (w : InfinitePlace L) : InfinitePlace K :=
  w.comap (algebraMap K L)

private def archWithAbsMap (w : InfinitePlace L) :
    WithAbs (infinitePlaceUnder K L w).1 →+* WithAbs w.1 :=
  (WithAbs.equiv w.1).symm.toRingHom.comp
    ((algebraMap K L).comp (WithAbs.equiv (infinitePlaceUnder K L w).1).toRingHom)

omit [NumberField K] [NumberField L] in
private theorem archWithAbsMap_continuous (w : InfinitePlace L) :
    Continuous (archWithAbsMap K L w) := by
  apply Isometry.continuous
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change w (algebraMap K L ((WithAbs.equiv _ ) x)) = infinitePlaceUnder K L w ((WithAbs.equiv _) x)
  exact (InfinitePlace.comap_apply w (algebraMap K L) _).symm

def archCompletionMap (w : InfinitePlace L) :
    (infinitePlaceUnder K L w).Completion →+* w.Completion :=
  (InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (archWithAbsMap K L w) (archWithAbsMap_continuous K L w)).comp
      (InfinitePlace.Completion.equiv (infinitePlaceUnder K L w)).toRingHom)

omit [NumberField K] [NumberField L] in
theorem archCompletionMap_continuous (w : InfinitePlace L) : Continuous (archCompletionMap K L w) :=
  (InfinitePlace.Completion.isometryEquivCompletion w).symm.continuous.comp
    ((UniformSpace.Completion.continuous_map.comp
      (InfinitePlace.Completion.isometryEquivCompletion (infinitePlaceUnder K L w)).continuous))

omit [NumberField K] [NumberField L] in
theorem archCompletionMap_diagonal (w : InfinitePlace L) (a : K) :
    archCompletionMap K L w (algebraMap K _ a) = algebraMap L _ (algebraMap K L a) := by
  apply InfinitePlace.Completion.ext
  exact UniformSpace.Completion.mapRingHom_coe (archWithAbsMap_continuous K L w) _

private abbrev finitePlaceUnder (w : Place L) : Place K :=
  w.under (𝓞 K)

private instance finitePlace_liesOver (w : Place L) :
    w.asIdeal.LiesOver (finitePlaceUnder K L w).asIdeal := ⟨rfl⟩

private theorem finitePlaceUnder_cofinite :
    Tendsto (finitePlaceUnder K L) cofinite cofinite := by
  apply Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
    (fun _ _ _ _ h => HeightOneSpectrum.ext_iff.mpr h)).subset ?_
  intro w hw
  have hw' : finitePlaceUnder K L w = v := mem_singleton_iff.mp hw
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw').symm⟩⟩

private def finiteWithValMap (w : Place L) :
    WithVal ((finitePlaceUnder K L w).valuation K) →+* WithVal (w.valuation L) :=
  algebraMap _ _

private theorem finiteWithValMap_continuous (w : Place L) :
    Continuous (finiteWithValMap K L w) :=
  (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) (L := L)
    (finitePlaceUnder K L w) w).continuous

def finiteCompletionMap (w : Place L) :
    (finitePlaceUnder K L w).adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (finiteWithValMap K L w) (finiteWithValMap_continuous K L w)).comp
      (HeightOneSpectrum.adicCompletion.equiv K (finitePlaceUnder K L w)).toRingHom)

theorem finiteCompletionMap_continuous (w : Place L) : Continuous (finiteCompletionMap K L w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K (finitePlaceUnder K L w)))

theorem finiteCompletionMap_diagonal (w : Place L) (a : K) :
    finiteCompletionMap K L w (algebraMap K _ a) = algebraMap L _ (algebraMap K L a) := by
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe (finiteWithValMap_continuous K L w) _

private theorem valuation_finiteCompletion_coe {F : Type*} [Field F] [NumberField F]
    (v : Place F) (a : F) :
    Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a := by
  change Valued.v ((algebraMap F (v.adicCompletion F) a).toCompletion) = _
  change Valued.v ((↑((WithVal.equiv (v.valuation F)).symm a) : (v.valuation F).Completion)) = _
  rw [Valued.valuedCompletion_apply]
  rfl

theorem finiteCompletionMap_integral (w : Place L) :
    MapsTo (finiteCompletionMap K L w)
      ((finitePlaceUnder K L w).adicCompletionIntegers K)
      (w.adicCompletionIntegers L) := by
  let v := finitePlaceUnder K L w
  let A : Set (v.adicCompletion K) := v.adicCompletionIntegers K
  let B : Set (w.adicCompletion L) := w.adicCompletionIntegers L
  let m := finiteCompletionMap K L w
  let D := Set.range (algebraMap K (v.adicCompletion K))
  have hA : IsOpen A := Valued.isOpen_valuationSubring _
  have hB : IsClosed B := Valued.isClosed_valuationSubring _
  have hD : closure D = univ := (v.denseRange_algebraMap K).closure_range
  have hs : A ∩ D ⊆ m ⁻¹' B := by
    rintro _ ⟨ha, a, rfl⟩
    change algebraMap K (v.adicCompletion K) a ∈ v.adicCompletionIntegers K at ha
    change finiteCompletionMap K L w (algebraMap K _ a) ∈ w.adicCompletionIntegers L
    rw [finiteCompletionMap_diagonal, HeightOneSpectrum.mem_adicCompletionIntegers,
      valuation_finiteCompletion_coe, ← HeightOneSpectrum.valuation_liesOver (K := K) (L := L) v w]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valuation_finiteCompletion_coe] at ha
    exact pow_le_one₀ zero_le ha
  have hc := hA.inter_closure (t := D)
  rw [hD, inter_univ] at hc
  exact hc.trans (closure_minimal hs (hB.preimage (finiteCompletionMap_continuous K L w)))

def finiteAdelesExtension : FinAdeles K →+* FinAdeles L :=
  RestrictedProduct.mapAlongRingHom (fun v : Place K => v.adicCompletion K)
    (fun w : Place L => w.adicCompletion L) (finitePlaceUnder K L) (finitePlaceUnder_cofinite K L)
    (finiteCompletionMap K L) (.of_forall (finiteCompletionMap_integral K L))

theorem finiteAdelesExtension_continuous : Continuous (finiteAdelesExtension K L) :=
  RestrictedProduct.mapAlong_continuous _ _ (finitePlaceUnder K L) (finitePlaceUnder_cofinite K L)
    (fun w => finiteCompletionMap K L w) (.of_forall (finiteCompletionMap_integral K L))
    (finiteCompletionMap_continuous K L)

def infiniteAdelesExtension : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w => (archCompletionMap K L w).comp (Pi.evalRingHom _ (infinitePlaceUnder K L w))

omit [NumberField K] [NumberField L] in
theorem infiniteAdelesExtension_continuous : Continuous (infiniteAdelesExtension K L) :=
  continuous_pi fun w => (archCompletionMap_continuous K L w).comp (continuous_apply _)

def adelesExtension : Adeles K →+* Adeles L :=
  RingHom.prodMap (infiniteAdelesExtension K L) (finiteAdelesExtension K L)

theorem adelesExtension_continuous : Continuous (adelesExtension K L) :=
  (infiniteAdelesExtension_continuous K L).prodMap (finiteAdelesExtension_continuous K L)

theorem adelesExtension_diagonal (a : K) :
    adelesExtension K L (algebraMap K (Adeles K) a) = algebraMap L (Adeles L) (algebraMap K L a) := by
  apply Prod.ext
  · exact funext fun w => archCompletionMap_diagonal K L w a
  · ext w
    exact congrArg (HeightOneSpectrum.adicCompletion.toCompletion) (finiteCompletionMap_diagonal K L w a)

private def archCompletionTransport {v w : InfinitePlace K} (h : v = w) :
    v.Completion → w.Completion :=
  h ▸ id

private def finiteCompletionTransport {v w : Place K} (h : v = w) :
    v.adicCompletion K → w.adicCompletion K :=
  h ▸ id

omit [NumberField K] in
private theorem archCompletionTransport_continuous {v w : InfinitePlace K} (h : v = w) :
    Continuous (archCompletionTransport K h) := by
  subst w
  exact continuous_id

private theorem finiteCompletionTransport_continuous {v w : Place K} (h : v = w) :
    Continuous (finiteCompletionTransport K h) := by
  subst w
  exact continuous_id

omit [NumberField K] in
private theorem archCompletionTransport_diagonal {v w : InfinitePlace K} (h : v = w) (a : K) :
    archCompletionTransport K h (algebraMap K _ a) = algebraMap K _ a := by
  subst w
  rfl

private theorem finiteCompletionTransport_diagonal {v w : Place K} (h : v = w) (a : K) :
    finiteCompletionTransport K h (algebraMap K _ a) = algebraMap K _ a := by
  subst w
  rfl

omit [NumberField K] in
private theorem archCompletionTransport_apply {v w : InfinitePlace K} (h : v = w)
    (a : InfiniteAdeleRing K) : archCompletionTransport K h (a v) = a w := by
  subst w
  rfl

private theorem finiteCompletionTransport_apply {v w : Place K} (h : v = w)
    (a : FinAdeles K) : finiteCompletionTransport K h (a v) = a w := by
  subst w
  rfl

omit [NumberField K] in
private theorem archCompletion_dense (v : InfinitePlace K) :
    DenseRange (algebraMap K v.Completion) :=
  (InfinitePlace.Completion.denseRange_coe v).comp
    (WithAbs.equiv v.1).symm.surjective.denseRange (InfinitePlace.Completion.continuous_coe v)

omit [NumberField K] in
private theorem archUnder_id (w : InfinitePlace K) : infinitePlaceUnder K K w = w :=
  InfinitePlace.comap_id w

private theorem finiteUnder_id (w : Place K) : finitePlaceUnder K K w = w := by
  apply HeightOneSpectrum.ext
  exact Ideal.comap_id w.asIdeal

theorem adelesExtension_id : adelesExtension K K = RingHom.id (Adeles K) := by
  ext a
  apply Prod.ext
  · funext w
    let v := infinitePlaceUnder K K w
    have he : (archCompletionMap K K w : v.Completion → w.Completion) =
        archCompletionTransport K (archUnder_id K w) :=
      (archCompletion_dense K v).equalizer (archCompletionMap_continuous K K w)
        (archCompletionTransport_continuous K _) (by
          funext x
          exact (archCompletionMap_diagonal K K w x).trans (archCompletionTransport_diagonal K _ x).symm)
    exact (congrFun he (a.1 v)).trans (archCompletionTransport_apply K (archUnder_id K w) a.1)
  · apply RestrictedProduct.ext
    intro w
    let v := finitePlaceUnder K K w
    have he : (finiteCompletionMap K K w : v.adicCompletion K → w.adicCompletion K) =
        finiteCompletionTransport K (finiteUnder_id K w) :=
      (v.denseRange_algebraMap K).equalizer (finiteCompletionMap_continuous K K w)
        (finiteCompletionTransport_continuous K _) (by
          funext x
          exact (finiteCompletionMap_diagonal K K w x).trans (finiteCompletionTransport_diagonal K _ x).symm)
    exact (congrFun he (a.2 v)).trans (finiteCompletionTransport_apply K (finiteUnder_id K w) a.2)

section Tower

variable (M : Type*) [Field M] [NumberField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
private theorem archUnder_trans (w : InfinitePlace M) :
    infinitePlaceUnder K L (infinitePlaceUnder L M w) = infinitePlaceUnder K M w := by
  simp only [infinitePlaceUnder, ← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq K L M]

private theorem finiteUnder_trans (w : Place M) :
    finitePlaceUnder K L (finitePlaceUnder L M w) = finitePlaceUnder K M w := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) w.asIdeal

theorem adelesExtension_comp :
    (adelesExtension L M).comp (adelesExtension K L) = adelesExtension K M := by
  ext a
  apply Prod.ext
  · funext w
    let v := infinitePlaceUnder L M w
    let u := infinitePlaceUnder K L v
    let f : u.Completion → w.Completion :=
      archCompletionMap L M w ∘ archCompletionMap K L v
    let g : u.Completion → w.Completion :=
      archCompletionMap K M w ∘ archCompletionTransport K (archUnder_trans K L M w)
    have he : f = g := (archCompletion_dense K u).equalizer
      ((archCompletionMap_continuous L M w).comp (archCompletionMap_continuous K L v))
      ((archCompletionMap_continuous K M w).comp (archCompletionTransport_continuous K _)) (by
        funext x
        change archCompletionMap L M w (archCompletionMap K L v (algebraMap K _ x)) =
          archCompletionMap K M w (archCompletionTransport K (archUnder_trans K L M w) (algebraMap K _ x))
        rw [archCompletionMap_diagonal, archCompletionMap_diagonal, archCompletionTransport_diagonal,
          archCompletionMap_diagonal, IsScalarTower.algebraMap_apply K L M])
    exact (congrFun he (a.1 u)).trans
      (congrArg (archCompletionMap K M w) (archCompletionTransport_apply K (archUnder_trans K L M w) a.1))
  · apply RestrictedProduct.ext
    intro w
    let v := finitePlaceUnder L M w
    let u := finitePlaceUnder K L v
    let f : u.adicCompletion K → w.adicCompletion M :=
      finiteCompletionMap L M w ∘ finiteCompletionMap K L v
    let g : u.adicCompletion K → w.adicCompletion M :=
      finiteCompletionMap K M w ∘ finiteCompletionTransport K (finiteUnder_trans K L M w)
    have he : f = g := (u.denseRange_algebraMap K).equalizer
      ((finiteCompletionMap_continuous L M w).comp (finiteCompletionMap_continuous K L v))
      ((finiteCompletionMap_continuous K M w).comp (finiteCompletionTransport_continuous K _)) (by
        funext x
        change finiteCompletionMap L M w (finiteCompletionMap K L v (algebraMap K _ x)) =
          finiteCompletionMap K M w (finiteCompletionTransport K (finiteUnder_trans K L M w) (algebraMap K _ x))
        rw [finiteCompletionMap_diagonal, finiteCompletionMap_diagonal, finiteCompletionTransport_diagonal,
          finiteCompletionMap_diagonal, IsScalarTower.algebraMap_apply K L M])
    exact (congrFun he (a.2 u)).trans
      (congrArg (finiteCompletionMap K M w) (finiteCompletionTransport_apply K (finiteUnder_trans K L M w) a.2))

end Tower

private abbrev AddPrincipals (F : Type*) [Field F] [NumberField F] :=
  NumberField.AdeleRing.principalSubgroup (𝓞 F) F

theorem principalAdeles_strict [TopologicalSpace K] [DiscreteTopology K] :
    IsClosedEmbedding (algebraMap K (Adeles K)) := by
  let P := AddPrincipals K
  letI : DiscreteTopology P := principalAdeles_discrete
  let j (x : K) : P := ⟨algebraMap K (Adeles K) x, ⟨x, rfl⟩⟩
  have hj : IsClosedEmbedding j := IsClosedEmbedding.of_continuous_injective_isClosedMap
    continuous_of_discreteTopology
    (fun _ _ e => NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val e))
    (fun _ _ => isClosed_discrete _)
  exact (principalAdeles_closed (F := K)).isClosedEmbedding_subtypeVal.comp hj

def adeleClassesExtension : GlobalAddClass K →+ GlobalAddClass L :=
  QuotientAddGroup.map (AddPrincipals K) (AddPrincipals L) (adelesExtension K L).toAddMonoidHom (by
    rintro a ⟨x, rfl⟩
    exact ⟨algebraMap K L x, (adelesExtension_diagonal K L x).symm⟩)

theorem adeleClassesExtension_continuous : Continuous (adeleClassesExtension K L) :=
  QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (QuotientAddGroup.continuous_mk.comp (adelesExtension_continuous K L))

def idelesExtension : Idele K →* Idele L := Units.map (adelesExtension K L)

theorem idelesExtension_continuous : Continuous (idelesExtension K L) :=
  (adelesExtension_continuous K L).units_map (adelesExtension K L).toMonoidHom

theorem idelesExtension_diagonal (x : Kˣ) :
    idelesExtension K L (principalIdele K x) = principalIdele L (Units.map (algebraMap K L) x) :=
  Units.ext (adelesExtension_diagonal K L x.val)

theorem principalIdeles_strict [TopologicalSpace Kˣ] [DiscreteTopology Kˣ] :
    IsClosedEmbedding (principalIdele K) := by
  let P := principalIdeles K
  letI : DiscreteTopology P := principalIdeles_discrete
  let j (x : Kˣ) : P := ⟨principalIdele K x, ⟨x, rfl⟩⟩
  have hj : IsClosedEmbedding j := IsClosedEmbedding.of_continuous_injective_isClosedMap
    continuous_of_discreteTopology (fun _ _ e => principalIdele_injective K (congrArg Subtype.val e))
    (fun _ _ => isClosed_discrete _)
  exact (principalIdeles_closed (F := K)).isClosedEmbedding_subtypeVal.comp hj

private theorem ideleClassMap_principal (x : Lˣ) :
    ideleClassMap L (principalIdele L x) = 1 :=
  (QuotientGroup.eq_one_iff (principalIdele L x)).mpr ⟨x, rfl⟩

def ideleClassesExtension : IdeleClass K →* IdeleClass L := by
  let f : Idele K →* IdeleClass L := (ideleClassMap L).comp (idelesExtension K L)
  have h : principalIdeles K ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    change ideleClassMap L (idelesExtension K L (principalIdele K x)) = 1
    calc
      _ = ideleClassMap L (principalIdele L (Units.map (algebraMap K L) x)) :=
        congrArg (ideleClassMap L) (idelesExtension_diagonal K L x)
      _ = 1 := ideleClassMap_principal L _
  exact QuotientGroup.lift (principalIdeles K) f h

theorem ideleClassesExtension_continuous : Continuous (ideleClassesExtension K L) :=
  QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    ((ideleClassMap_continuous L).comp (idelesExtension_continuous K L))

def integralAdelesBlockExtension :
    globalIntegralBlock K ∅ →+ globalIntegralBlock L ∅ :=
  ((adelesExtension K L).toAddMonoidHom.comp (globalIntegralBlock K ∅).subtype).codRestrict _ (by
    intro a w _
    exact finiteCompletionMap_integral K L w (a.property (finitePlaceUnder K L w) (Finset.notMem_empty _)))

def integralAdelesClassesExtension :
    SBlockClass K ∅ →+ SBlockClass L ∅ :=
  QuotientAddGroup.map (sIntegersGlobal K ∅).range (sIntegersGlobal L ∅).range
    (integralAdelesBlockExtension K L) (by
      rintro a ⟨x, rfl⟩
      have hx (w : Place L) : (algebraMap L (FinAdeles L) (algebraMap K L x.val)) w ∈
          w.adicCompletionIntegers L := by
        change (algebraMap L (w.adicCompletion L) (algebraMap K L x.val)) ∈ _
        rw [← finiteCompletionMap_diagonal K L w x.val]
        exact finiteCompletionMap_integral K L w (x.property (finitePlaceUnder K L w) (Finset.notMem_empty _))
      refine ⟨⟨algebraMap K L x.val, fun w _ => hx w⟩, Subtype.ext ?_⟩
      exact (adelesExtension_diagonal K L x.val).symm)

theorem integralAdelesClassesExtension_natural :
    sBlockClass_homeomorph L ∅ ∘ integralAdelesClassesExtension K L =
      adeleClassesExtension K L ∘ sBlockClass_homeomorph K ∅ := by
  funext x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

theorem integralAdelesClassesExtension_continuous :
    Continuous (integralAdelesClassesExtension K L) := by
  apply ((sBlockClass_homeomorph L ∅).toHomeomorph.isEmbedding.continuous_iff).mpr
  change Continuous (sBlockClass_homeomorph L ∅ ∘ integralAdelesClassesExtension K L)
  rw [integralAdelesClassesExtension_natural K L]
  exact (adeleClassesExtension_continuous K L).comp (sBlockClass_homeomorph K ∅).continuous_toFun

/-- The S-integer ring with no finite places inverted is the ring of integers. -/
def sIntegerRing_empty_equiv : (𝓞 K) ≃+* sIntegerRing K ∅ := by
  let f : (𝓞 K) →+* sIntegerRing K ∅ :=
    (algebraMap (𝓞 K) K).codRestrict _ fun x v _ =>
      HeightOneSpectrum.coe_algebraMap_mem (𝓞 K) K v x
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact (IsFractionRing.injective (𝓞 K) K) (congrArg (fun a : sIntegerRing K ∅ => a.val) h)
  · intro x
    obtain ⟨y, hy⟩ := (diagonal_finiteAdeles_integral_iff x.val).mp
      (fun v => x.property v (Finset.notMem_empty _))
    exact ⟨y, Subtype.ext hy⟩

theorem principalAdeles_strict_sequence [TopologicalSpace K] [DiscreteTopology K] :
    IsClosedEmbedding (algebraMap K (Adeles K)) ∧
      IsOpenQuotientMap (QuotientAddGroup.mk : Adeles K → GlobalAddClass K) ∧
      (∀ a : Adeles K, (QuotientAddGroup.mk a : GlobalAddClass K) = 0 ↔
        a ∈ Set.range (algebraMap K (Adeles K))) ∧
      CompactSpace (GlobalAddClass K) ∧ T2Space (GlobalAddClass K) ∧
      ∀ n : ℕ, n ≠ 0 → Bijective (fun a : GlobalAddClass K => n • a) :=
  ⟨principalAdeles_strict K, QuotientAddGroup.isOpenQuotientMap_mk,
    fun a => QuotientAddGroup.eq_zero_iff a, principalAdeles_quotient_compact,
    principalAdeles_quotient_hausdorff, principalAdeles_quotient_uniquelyDivisible⟩

theorem principalIdeles_strict_sequence [TopologicalSpace Kˣ] [DiscreteTopology Kˣ] :
    IsClosedEmbedding (principalIdele K) ∧ IsOpenQuotientMap (ideleClassMap K) ∧
      (∀ a : Idele K, ideleClassMap K a = 1 ↔ a ∈ Set.range (principalIdele K)) ∧
      LocallyCompactSpace (IdeleClass K) ∧ T2Space (IdeleClass K) ∧
      Continuous (ideleClassNorm K) ∧ Set.range (ideleClassNorm K) = Ioi 0 ∧
      Continuous (ideleClassExpSection K) ∧
      ∀ x : Multiplicative ℝ, ideleClassNorm K (ideleClassExpSection K x) =
        Real.exp x.toAdd :=
  ⟨principalIdeles_strict K, QuotientGroup.isOpenQuotientMap_mk,
    fun a => QuotientGroup.eq_one_iff a, ideleClasses_locallyCompact (F := K),
    ideleClasses_hausdorff (F := K), ideleClassNorm_continuous K, ideleClassNorm_range K,
    ideleClassExpSection_continuous K, ideleClassNorm_expSection K⟩

section Tower

variable (M : Type*) [Field M] [NumberField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem idelesExtension_comp :
    (idelesExtension L M).comp (idelesExtension K L) = idelesExtension K M := by
  apply DFunLike.ext
  intro a
  apply Units.ext
  exact DFunLike.congr_fun (adelesExtension_comp K L M) a.val

theorem adeleClassesExtension_comp :
    (adeleClassesExtension L M).comp (adeleClassesExtension K L) = adeleClassesExtension K M := by
  apply DFunLike.ext
  intro a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact congrArg (QuotientAddGroup.mk : Adeles M → GlobalAddClass M)
    (DFunLike.congr_fun (adelesExtension_comp K L M) b)

theorem ideleClassesExtension_comp :
    (ideleClassesExtension L M).comp (ideleClassesExtension K L) = ideleClassesExtension K M := by
  apply DFunLike.ext
  intro a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
  exact congrArg (ideleClassMap M) (DFunLike.congr_fun (idelesExtension_comp K L M) b)

theorem integralAdelesClassesExtension_comp :
    (integralAdelesClassesExtension L M).comp (integralAdelesClassesExtension K L) =
      integralAdelesClassesExtension K M := by
  apply DFunLike.ext
  intro a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact congrArg (QuotientAddGroup.mk : globalIntegralBlock M ∅ → SBlockClass M ∅)
    (Subtype.ext (DFunLike.congr_fun (adelesExtension_comp K L M) b.val))

end Tower

theorem idelesExtension_id :
    idelesExtension K K = MonoidHom.id (Idele K) := by
  apply DFunLike.ext
  intro a
  exact Units.ext (DFunLike.congr_fun (adelesExtension_id K) a.val)

theorem adeleClassesExtension_id :
    adeleClassesExtension K K = AddMonoidHom.id (GlobalAddClass K) := by
  apply DFunLike.ext
  intro a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact congrArg (QuotientAddGroup.mk : Adeles K → GlobalAddClass K)
    (DFunLike.congr_fun (adelesExtension_id K) b)

theorem ideleClassesExtension_id :
    ideleClassesExtension K K = MonoidHom.id (IdeleClass K) := by
  apply DFunLike.ext
  intro a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
  exact congrArg (ideleClassMap K) (DFunLike.congr_fun (idelesExtension_id K) b)

theorem integralAdelesClassesExtension_id :
    integralAdelesClassesExtension K K = AddMonoidHom.id (SBlockClass K ∅) := by
  apply DFunLike.ext
  intro a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact congrArg (QuotientAddGroup.mk : globalIntegralBlock K ∅ → SBlockClass K ∅)
    (Subtype.ext (DFunLike.congr_fun (adelesExtension_id K) b.val))

end

end Masullo
