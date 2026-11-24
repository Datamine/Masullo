import SLocalAdditive
import IdeleIdealClasses

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

/-- The subring whose units are the global ideles integral off S. -/
def globalIntegralSubring (S : Finset (Place F)) : Subring (Adeles F) where
  __ := globalIntegralBlock F S
  one_mem' := fun _ _ => one_mem _
  mul_mem' ha hb v hv := mul_mem (ha v hv) (hb v hv)

def sIdeleBlock (S : Finset (Place F)) : Subgroup (Idele F) :=
  (globalIntegralSubring F S).toSubmonoid.units

theorem sIdeleBlock_open (S : Finset (Place F)) : IsOpen (sIdeleBlock F S : Set (Idele F)) :=
  Submonoid.isOpen_units (U := (globalIntegralSubring F S).toSubmonoid) (globalIntegralBlock_open F S)

theorem sIdeleBlock_mem_iff (S : Finset (Place F)) (a : Idele F) :
    a ∈ sIdeleBlock F S ↔ ∀ v ∉ S, ideleOrder F a v = 0 := by
  constructor
  · intro h v hv
    apply (ideleOrder_eq_zero_iff F a v).mpr
    have hn := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h.1 v hv)
    have hi := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h.2 v hv)
    have he := congrArg (fun x : Adeles F => x.2 v) a.val_inv
    change a.val.2 v * a.inv.2 v = 1 at he
    have hb : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by rw [← map_mul, he, map_one]
    exact le_antisymm hn (hb.symm.trans_le (mul_le_of_le_one_right zero_le hi))
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr
        ((ideleOrder_eq_zero_iff F a v).mp (h v hv)).le
    · intro v hv
      have he := congrArg (fun x : Adeles F => x.2 v) a.val_inv
      change a.val.2 v * a.inv.2 v = 1 at he
      have hb : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by rw [← map_mul, he, map_one]
      rw [(ideleOrder_eq_zero_iff F a v).mp (h v hv), one_mul] at hb
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr hb.le

private def sAdelicSubringProduct (S : Finset (Place F)) :
    globalIntegralSubring F S ≃ₜ* SAdeles F S × SIntegralTail F S where
  __ := (globalIntegralBlockHomeomorph F S).toHomeomorph
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul (sAdelesProjection F S) a.val b.val
    · funext v
      apply Subtype.ext
      rfl

private def sBlockUnitsEquiv (S : Finset (Place F)) :
    sIdeleBlock F S ≃ₜ* (globalIntegralSubring F S)ˣ where
  __ := (globalIntegralSubring F S).toSubmonoid.unitsEquivUnitsType
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    exact ⟨(Units.continuous_val.comp continuous_subtype_val).subtype_mk _,
      (Units.continuous_coe_inv.comp continuous_subtype_val).subtype_mk _⟩
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Units.continuous_iff.mpr
      ⟨continuous_subtype_val.comp Units.continuous_val,
        continuous_subtype_val.comp Units.continuous_coe_inv⟩

/-- The S-ideles with the integral tail carry the open subgroup topology. -/
def sIdeleBlockHomeomorph (S : Finset (Place F)) :
    sIdeleBlock F S ≃ₜ* (SAdeles F S × SIntegralTail F S)ˣ :=
  (sBlockUnitsEquiv F S).trans (Units.mapContinuousMulEquiv (sAdelicSubringProduct F S))

def sIdeleInsertion (S : Finset (Place F)) : (SAdeles F S × SIntegralTail F S)ˣ →* Idele F :=
  (sIdeleBlock F S).subtype.comp (sIdeleBlockHomeomorph F S).symm.toMonoidHom

theorem sIdeleInsertion_openEmbedding (S : Finset (Place F)) :
    IsOpenEmbedding (sIdeleInsertion F S) :=
  (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal.comp
    (sIdeleBlockHomeomorph F S).symm.toHomeomorph.isOpenEmbedding

theorem sIdeleBlock_locallyCompact_hausdorff (S : Finset (Place F)) :
    LocallyCompactSpace (sIdeleBlock F S) ∧ T2Space (sIdeleBlock F S) := by
  letI := ideles_locallyCompact (F := F)
  letI := ideles_hausdorff (F := F)
  exact ⟨(sIdeleBlock_open F S).locallyCompactSpace, inferInstance⟩

/-- The principal elements in the S-block are the S-units. -/
def sUnitToField (S : Finset (Place F)) : (sIntegerRing F S)ˣ →* Fˣ :=
  Units.map (sIntegerRing F S).subtype

theorem principalIdele_mem_sBlock (S : Finset (Place F)) (t : Fˣ) :
    principalIdele F t ∈ sIdeleBlock F S ↔
      ∃ u : (sIntegerRing F S)ˣ, sUnitToField F S u = t := by
  constructor
  · intro h
    let u : (sIntegerRing F S)ˣ :=
      ⟨⟨t.val, h.1⟩, ⟨t.inv, h.2⟩, Subtype.ext t.val_inv, Subtype.ext t.inv_val⟩
    exact ⟨u, Units.ext rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.property, u.inv.property⟩

def sPrincipal (S : Finset (Place F)) : (sIntegerRing F S)ˣ →* sIdeleBlock F S :=
  ((principalIdele F).comp (sUnitToField F S)).codRestrict (sIdeleBlock F S)
    (fun u => (principalIdele_mem_sBlock F S _).mpr ⟨u, rfl⟩)

theorem sIdeleInsertion_equivariant (S : Finset (Place F))
    (u : (sIntegerRing F S)ˣ) (a : (SAdeles F S × SIntegralTail F S)ˣ) :
    sIdeleInsertion F S ((sIdeleBlockHomeomorph F S (sPrincipal F S u)) * a) =
      principalIdele F (sUnitToField F S u) * sIdeleInsertion F S a := by
  have h : sIdeleInsertion F S (sIdeleBlockHomeomorph F S (sPrincipal F S u)) =
      principalIdele F (sUnitToField F S u) :=
    congrArg (fun x : sIdeleBlock F S => x.val)
      ((sIdeleBlockHomeomorph F S).symm_apply_apply (sPrincipal F S u))
  rw [map_mul, h]

private theorem continuous_discrete_leftTranslation {U H : Type*} [TopologicalSpace U]
    [DiscreteTopology U] [TopologicalSpace H] [Mul H] [ContinuousMul H] (f : U → H) :
    Continuous (fun ua : U × H => f ua.1 * ua.2) :=
  (continuous_of_discreteTopology.comp continuous_fst).mul continuous_snd

theorem sIdeleInsertion_action_continuous (S : Finset (Place F))
    [TopologicalSpace (sIntegerRing F S)ˣ] [DiscreteTopology (sIntegerRing F S)ˣ] :
    Continuous (fun ua : (sIntegerRing F S)ˣ × (SAdeles F S × SIntegralTail F S)ˣ =>
      sIdeleBlockHomeomorph F S (sPrincipal F S ua.1) * ua.2) ∧
    Continuous (fun ua : (sIntegerRing F S)ˣ × Idele F =>
      principalIdele F (sUnitToField F S ua.1) * ua.2) := by
  have hg := continuous_discrete_leftTranslation
    (fun u : (sIntegerRing F S)ˣ => principalIdele F (sUnitToField F S u))
  refine ⟨(sIdeleInsertion_openEmbedding F S).isEmbedding.continuous_iff.mpr ?_, hg⟩
  convert hg.comp (continuous_fst.prodMk
    ((sIdeleInsertion_openEmbedding F S).continuous.comp continuous_snd)) using 1
  funext ua
  exact sIdeleInsertion_equivariant F S ua.1 ua.2


theorem sIdeleBlock_mono {S T : Finset (Place F)} (h : S ⊆ T) :
    sIdeleBlock F S ≤ sIdeleBlock F T := by
  intro a ha
  refine (sIdeleBlock_mem_iff F T a).mpr fun v hv =>
    (sIdeleBlock_mem_iff F S a).mp ha v (fun hv' => hv (h hv'))

theorem sIdeleBlock_cover (a : Idele F) : ∃ S, a ∈ sIdeleBlock F S := by
  refine ⟨(ideleOrder_finite_support F a).toFinset, (sIdeleBlock_mem_iff F _ a).mpr ?_⟩
  intro v hv
  by_contra h
  exact hv ((ideleOrder_finite_support F a).mem_toFinset.mpr h)

def sIdeleTransition {S T : Finset (Place F)} (h : S ⊆ T) :
    sIdeleBlock F S →* sIdeleBlock F T :=
  Subgroup.inclusion (sIdeleBlock_mono F h)

theorem sIdeleTransition_continuous {S T : Finset (Place F)} (h : S ⊆ T) :
    Continuous (sIdeleTransition F h) := continuous_subtype_val.subtype_mk _

/-- The global ideles are the topological direct limit of the open
S-blocks. This is its universal property for continuous homomorphisms. -/
theorem sIdeleBlock_directLimit {H : Type*} [Monoid H] [TopologicalSpace H]
    (f : ∀ S, sIdeleBlock F S →ₜ* H)
    (hf : ∀ S T (h : S ⊆ T) (a : sIdeleBlock F S),
      f T (sIdeleTransition F h a) = f S a) :
    ∃! g : Idele F →ₜ* H, ∀ S (a : sIdeleBlock F S), g a.val = f S a := by
  choose I hI using sIdeleBlock_cover F
  let g (a : Idele F) := f (I a) ⟨a, hI a⟩
  have hg (S : Finset (Place F)) (a : sIdeleBlock F S) : g a.val = f S a := by
    let T := I a.val ∪ S
    have h₁ := hf (I a.val) T (Finset.subset_union_left (s₁ := I a.val) (s₂ := S)) ⟨a.val, hI a.val⟩
    have h₂ := hf S T (Finset.subset_union_right (s₁ := I a.val) (s₂ := S)) a
    exact h₁.symm.trans h₂
  have hcont : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro a
    let S := I a
    let b : sIdeleBlock F S := ⟨a, hI a⟩
    have hb : Continuous (fun x : sIdeleBlock F S => g x.val) := by
      have he : (fun x : sIdeleBlock F S => g x.val) = f S := funext (hg S)
      rw [he]
      exact (f S).continuous
    exact ((continuousWithinAt_iff_continuousAt_domRestrict g b.property).mpr
      hb.continuousAt).continuousAt ((sIdeleBlock_open F S).mem_nhds b.property)
  let G : Idele F →ₜ* H :=
    { toFun := g
      continuous_toFun := hcont
      map_one' := (hg ∅ 1).trans (map_one (f ∅))
      map_mul' a b := by
        let S := I a ∪ I b
        let a' : sIdeleBlock F S :=
          sIdeleTransition F (Finset.subset_union_left (s₁ := I a) (s₂ := I b)) ⟨a, hI a⟩
        let b' : sIdeleBlock F S :=
          sIdeleTransition F (Finset.subset_union_right (s₁ := I a) (s₂ := I b)) ⟨b, hI b⟩
        change g (a' * b').val = g a'.val * g b'.val
        rw [hg S (a' * b'), map_mul, hg S a', hg S b'] }
  exact ⟨G, hg, fun g' hg' => DFunLike.ext _ _ fun a => hg' (I a) ⟨a, hI a⟩⟩

/-- The S-idele class group, including the integral finite tail. -/
abbrev SIdeleClass (S : Finset (Place F)) := sIdeleBlock F S ⧸ (sPrincipal F S).range

private def sBlockToClasses (S : Finset (Place F)) : sIdeleBlock F S →* IdeleClass F :=
  (ideleClassMap F).comp (sIdeleBlock F S).subtype

private theorem sBlockToClasses_ker (S : Finset (Place F)) :
    (sBlockToClasses F S).ker = (sPrincipal F S).range := by
  ext a
  change QuotientGroup.mk a.val = (1 : IdeleClass F) ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨t, ht⟩
    have h : principalIdele F t ∈ sIdeleBlock F S := ht.symm ▸ a.property
    obtain ⟨u, hu⟩ := (principalIdele_mem_sBlock F S t).mp h
    exact ⟨u, Subtype.ext (congrArg (principalIdele F) hu |>.trans ht)⟩
  · rintro ⟨u, hu⟩
    exact ⟨sUnitToField F S u, congrArg Subtype.val hu⟩

def sIdeleClassInclusion (S : Finset (Place F)) : SIdeleClass F S →* IdeleClass F :=
  QuotientGroup.lift _ (sBlockToClasses F S) (sBlockToClasses_ker F S).ge

theorem sIdeleClassInclusion_openEmbedding (S : Finset (Place F)) :
    IsOpenEmbedding (sIdeleClassInclusion F S) := by
  let p := sBlockToClasses F S
  let f := sIdeleClassInclusion F S
  let q := QuotientGroup.mk' (sPrincipal F S).range
  have he : f ∘ q = p := rfl
  have hc : Continuous f := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    (he.symm ▸ ((ideleClassMap_continuous F).comp
      (continuous_subtype_val : Continuous (Subtype.val : sIdeleBlock F S → Idele F))))
  have ho : IsOpenMap f := IsOpenMap.of_comp QuotientGroup.continuous_mk
    QuotientGroup.mk_surjective (he.symm ▸ QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp
      (sIdeleBlock_open F S).isOpenEmbedding_subtypeVal.isOpenMap)
  have hi : Injective f := by
    rw [injective_iff_map_eq_one]
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← sBlockToClasses_ker]
    exact hc
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho

theorem sIdeleClassInclusion_range (S : Finset (Place F)) :
    (sIdeleClassInclusion F S).range = (sIdeleBlock F S).map (ideleClassMap F) := by
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨QuotientGroup.mk (⟨a, ha⟩ : sIdeleBlock F S), rfl⟩

theorem sIdeleClassInclusion_unique (S : Finset (Place F)) (f : SIdeleClass F S →* IdeleClass F)
    (hf : ∀ a : sIdeleBlock F S, f (QuotientGroup.mk a) = ideleClassMap F a.val) :
    f = sIdeleClassInclusion F S := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  exact hf a


/-- The classes of divisors supported on S are the classes killed when
the primes in S are inverted. -/
def sInvertedIdealClasses (S : Finset (Place F)) : Subgroup (ClassGroup (𝓞 F)) :=
  (sIdeleBlock F S).map (ideleIdealClass F)

def divisorClassMap :
    Multiplicative (Place F →₀ ℤ) →* ClassGroup (𝓞 F) :=
  (ClassGroup.mk F).comp (divisorFractionalIdeal F)

theorem sInvertedIdealClasses_divisors (S : Finset (Place F)) (c : ClassGroup (𝓞 F)) :
    c ∈ sInvertedIdealClasses F S ↔
      ∃ d : Place F →₀ ℤ, d.support ⊆ S ∧ divisorClassMap F (Multiplicative.ofAdd d) = c := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Multiplicative.toAdd (ideleDivisor F a), ?_, rfl⟩
    intro v hv
    by_contra hns
    exact (Finsupp.mem_support_iff.mp hv) ((sIdeleBlock_mem_iff F S a).mp ha v hns)
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨a, ha⟩ := ideleDivisor_surjective F (Multiplicative.ofAdd d)
    have he (v : Place F) : ideleOrder F a v = d v :=
      congrArg (fun x : Multiplicative (Place F →₀ ℤ) => (Multiplicative.toAdd x) v) ha
    refine ⟨a, (sIdeleBlock_mem_iff F S a).mpr ?_, ?_⟩
    · intro v hv
      rw [he, Finsupp.notMem_support_iff.mp (fun h => hv (hd h))]
    · change divisorClassMap F (ideleDivisor F a) = _
      rw [ha]

/-- Divisor presentation of the S-local ideal-class group. -/
abbrev SPicardGroup (S : Finset (Place F)) :=
  ClassGroup (𝓞 F) ⧸ sInvertedIdealClasses F S

private theorem ideleIdealClass_principal_one (t : Fˣ) :
    ideleIdealClass F (principalIdele F t) = 1 :=
  (ideleIdealClass_ker_iff F _).mpr ⟨t, 1, by simp⟩

def sLocalizedIdeleClassMap (S : Finset (Place F)) : IdeleClass F →* SPicardGroup F S :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (sInvertedIdealClasses F S)).comp (ideleIdealClass F))
    (by
      rintro _ ⟨t, rfl⟩
      change QuotientGroup.mk' (sInvertedIdealClasses F S) (ideleIdealClass F (principalIdele F t)) = 1
      rw [ideleIdealClass_principal_one, map_one])

theorem sLocalizedIdeleClassMap_surjective (S : Finset (Place F)) :
    Surjective (sLocalizedIdeleClassMap F S) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, ha⟩ := ideleIdealClass_surjective F c
  refine ⟨ideleClassMap F a, ?_⟩
  exact congrArg (QuotientGroup.mk' (sInvertedIdealClasses F S)) ha

theorem sLocalizedIdeleClassMap_ker (S : Finset (Place F)) :
    (sLocalizedIdeleClassMap F S).ker = (sIdeleClassInclusion F S).range := by
  rw [sIdeleClassInclusion_range]
  ext c
  obtain ⟨a, rfl⟩ := ideleClassMap_surjective F c
  change QuotientGroup.mk (ideleIdealClass F a) = (1 : SPicardGroup F S) ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨x, hx, hxa⟩
    have he : x⁻¹ * a ∈ (ideleIdealClass F).ker := by
      change ideleIdealClass F (x⁻¹ * a) = 1
      rw [map_mul, map_inv, hxa, inv_mul_cancel]
    obtain ⟨t, b, hb⟩ := (ideleIdealClass_ker_iff F (x⁻¹ * a)).mp he
    obtain ⟨hb₁, hb₂⟩ := (ideleDivisor_ker_iff F b.val).mp b.property
    have hbS : b.val ∈ sIdeleBlock F S := ⟨fun v _ => hb₁ v, fun v _ => hb₂ v⟩
    refine ⟨x * b.val, (sIdeleBlock F S).mul_mem hx hbS, ?_⟩
    have ha : a = x * (principalIdele F t * b.val) := by rw [← hb, mul_inv_cancel_left]
    have ht : ideleClassMap F (principalIdele F t) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩
    have hqa := congrArg (ideleClassMap F) ha
    rw [map_mul, map_mul, ht] at hqa
    calc
      ideleClassMap F (x * b.val) = ideleClassMap F x * ideleClassMap F b.val :=
        map_mul (ideleClassMap F) x b.val
      _ = ideleClassMap F x * (1 * ideleClassMap F b.val) :=
        congrArg (fun y => ideleClassMap F x * y) (one_mul (ideleClassMap F b.val)).symm
      _ = ideleClassMap F a := hqa.symm
  · rintro ⟨x, hx, he⟩
    have hb : x⁻¹ * a ∈ principalIdeles F := by
      apply (QuotientGroup.eq_one_iff _).mp
      change ideleClassMap F (x⁻¹ * a) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    obtain ⟨t, ht⟩ := hb
    have ht' : ideleIdealClass F (x⁻¹ * a) = 1 := ht ▸ ideleIdealClass_principal_one F t
    rw [map_mul, map_inv, inv_mul_eq_one] at ht'
    exact ⟨x, hx, ht'⟩

theorem sIdeleClass_finiteCokernel (S : Finset (Place F)) :
    Finite (SPicardGroup F S) :=
  Finite.of_surjective _ QuotientGroup.mk_surjective

instance sIdeleClassRange_normal (S : Finset (Place F)) :
    (sIdeleClassInclusion F S).range.Normal := by
  rw [← sLocalizedIdeleClassMap_ker]
  infer_instance

def sIdeleClass_cokernelEquiv (S : Finset (Place F)) :
    (IdeleClass F ⧸ (sIdeleClassInclusion F S).range) ≃* SPicardGroup F S :=
  (QuotientGroup.quotientMulEquivOfEq (sLocalizedIdeleClassMap_ker F S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (sLocalizedIdeleClassMap_surjective F S))

private theorem sIdeleClass_range_open (S : Finset (Place F)) :
    IsOpen ((sIdeleClassInclusion F S).range : Set (IdeleClass F)) :=
  (sIdeleClassInclusion_openEmbedding F S).isOpen_range

theorem sIdeleClass_identityComponent (S : Finset (Place F)) :
    sIdeleClassInclusion F S '' connectedComponent 1 =
      connectedComponent (1 : IdeleClass F) := by
  let f := sIdeleClassInclusion F S
  let R := Set.range (sIdeleClassInclusion F S)
  let e := (sIdeleClassInclusion_openEmbedding F S).isEmbedding.toHomeomorph
  have hmem : (1 : IdeleClass F) ∈ R := ⟨1, map_one f⟩
  have h₁ : e 1 = ⟨1, hmem⟩ := Subtype.ext (map_one f)
  have hc : IsClopen R := ⟨f.range.isClosed_of_isOpen (sIdeleClass_range_open F S),
    sIdeleClass_range_open F S⟩
  have he : e '' connectedComponent 1 = connectedComponent (e 1) := by
    simpa only [connectedComponentIn_univ, image_univ, e.surjective.range_eq] using
      (e.image_connectedComponentIn (s := (univ : Set (SIdeleClass F S))) (x := 1) (mem_univ _))
  change (fun x : SIdeleClass F S => (e x).val) '' connectedComponent 1 = _
  rw [show (fun x : SIdeleClass F S => (e x).val) = Subtype.val ∘ e from rfl,
    image_comp, he, h₁]
  exact (connectedComponentIn_eq_image hmem).symm.trans (hc.connectedComponentIn_eq hmem)

/-- A finite set of places suffices to meet every ideal class, and all
larger S-blocks give the whole global idele class group. -/
theorem sIdeleClass_eventually_surjective :
    ∃ S : Finset (Place F), ∀ T : Finset (Place F), S ⊆ T →
      Surjective (sIdeleClassInclusion F T) := by
  letI : Fintype (ClassGroup (𝓞 F)) := Fintype.ofFinite _
  choose a ha using ideleIdealClass_surjective F
  choose S hS using sIdeleBlock_cover F
  let B := Finset.univ.biUnion fun c : ClassGroup (𝓞 F) => S (a c)
  refine ⟨B, fun T hBT y => ?_⟩
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F y
  let c := ideleIdealClass F g
  have hSa : S (a c) ⊆ B := Finset.subset_biUnion_of_mem (s := Finset.univ) (fun c => S (a c))
    (Finset.mem_univ c)
  have hac : a c ∈ sIdeleBlock F T := sIdeleBlock_mono F (hSa.trans hBT) (hS (a c))
  have hy : ideleClassMap F g ∈ (sLocalizedIdeleClassMap F T).ker := by
    change QuotientGroup.mk c = (1 : SPicardGroup F T)
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨a c, hac, ha c⟩
  rw [sLocalizedIdeleClassMap_ker] at hy
  exact hy

end

end Masullo
