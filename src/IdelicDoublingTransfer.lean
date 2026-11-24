import IdelicDoubling
import ProfiniteDoubling
import NormOneExact
import SLocalFundamentalDomain
import SUnitRank

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
abbrev SFiniteAdeles (S : Finset (Place F)) := (v : S) → v.val.adicCompletion F

private def sFiniteIntegerRing (S : Finset (Place F)) : Subring (SFiniteAdeles F S) where
  carrier := {a | ∀ v : S, a v ∈ v.val.adicCompletionIntegers F}
  zero_mem' _v := zero_mem _
  one_mem' _v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  neg_mem' ha v := neg_mem (ha v)
  mul_mem' ha hb v := mul_mem (ha v) (hb v)

def sFiniteIntegralUnits (S : Finset (Place F)) : Subgroup (SFiniteAdeles F S)ˣ :=
  (sFiniteIntegerRing F S).toSubmonoid.units

theorem sFiniteIntegralUnits_open (S : Finset (Place F)) :
    IsOpen (sFiniteIntegralUnits F S : Set (SFiniteAdeles F S)ˣ) := by
  apply Submonoid.isOpen_units
  have e : (sFiniteIntegerRing F S : Set (SFiniteAdeles F S)) =
      Set.univ.pi (fun v : S => (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))) := by
    ext a
    simp [sFiniteIntegerRing, Set.mem_pi]
  change IsOpen (sFiniteIntegerRing F S : Set (SFiniteAdeles F S))
  rw [e]
  exact isOpen_set_pi finite_univ (fun v _ => Valued.isOpen_valuationSubring _)

private def sLocalUnitCoordinates (S : Finset (Place F)) :
    (SAdeles F S)ˣ ≃ₜ* InfiniteIdeles F × (SFiniteAdeles F S)ˣ where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := Homeomorph.prodUnits.continuous
  continuous_invFun := Homeomorph.prodUnits.symm.continuous

private theorem sLocalNorm_of_integral (S : Finset (Place F)) (a : (SAdeles F S)ˣ)
    (ha : (sLocalUnitCoordinates F S a).2 ∈ sFiniteIntegralUnits F S) :
    sLocalIdeleNorm F S a = ‖(sLocalUnitCoordinates F S a).1.val‖ := by
  let b := (sLocalEmbed F S a).val
  have hi : b ∈ (ideleDivisor F).ker := by
    change ideleDivisor F b = 1
    apply Finsupp.ext
    intro v
    by_cases hv : v ∈ S
    · have h₁ : b.val.2 v ∈ v.adicCompletionIntegers F := by
        rw [show b.val.2 v = a.val.2 ⟨v, hv⟩ from sLocalEmbed_finite F S a ⟨v, hv⟩]
        exact ha.1 ⟨v, hv⟩
      have h₂ : b.inv.2 v ∈ v.adicCompletionIntegers F := by
        have hh := sLocalEmbed_finite F S a⁻¹ ⟨v, hv⟩
        rw [map_inv] at hh
        rw [show b.inv.2 v = a.inv.2 ⟨v, hv⟩ from hh]
        exact ha.2 ⟨v, hv⟩
      have h₁' := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp h₁
      have h₂' := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp h₂
      have hEq : Valued.v (b.val.2 v) * Valued.v (b.inv.2 v) = 1 := by
        rw [← map_mul]
        exact (congrArg Valued.v (congrArg (fun d : Adeles F => d.2 v) b.val_inv)).trans (map_one _)
      exact (ideleOrder_eq_zero_iff F b v).mpr
        (le_antisymm h₁' (hEq.symm.trans_le (mul_le_of_le_one_right zero_le h₂')))
    · exact (sIdeleBlock_mem_iff F S b).mp (sLocalEmbed F S a).property v hv
  change ideleNorm F b = _
  rw [ideleNorm_eq_arch_of_finite_integral F b hi]
  change ‖b.val.1‖ = ‖a.val.1‖
  rw [show b.val.1 = a.val.1 from sLocalEmbed_arch F S a]

private def sLocalIntegralBlock (S : Finset (Place F)) : Subgroup (SLocalNormOne F S) :=
  (sFiniteIntegralUnits F S).comap ((MonoidHom.snd _ _).comp
    ((sLocalUnitCoordinates F S).toMonoidHom.comp (sLocalIdeleNorm F S).ker.subtype))

private theorem sLocalIntegralBlock_open (S : Finset (Place F)) :
    IsOpen (sLocalIntegralBlock F S : Set (SLocalNormOne F S)) :=
  (sFiniteIntegralUnits_open F S).preimage
    (continuous_snd.comp ((sLocalUnitCoordinates F S).continuous.comp continuous_subtype_val))

private def sLocalIntegralProduct (S : Finset (Place F)) :
    sLocalIntegralBlock F S ≃ₜ* archNormOne F × sFiniteIntegralUnits F S where
  toFun x :=
    let z := sLocalUnitCoordinates F S x.val.val
    (⟨z.1, (archNormOne_iff F _).mpr ((sLocalNorm_of_integral F S x.val.val x.property).symm.trans x.val.property)⟩,
      ⟨z.2, x.property⟩)
  invFun p := by
    let x := (sLocalUnitCoordinates F S).symm (p.1.val, p.2.val)
    have he := (sLocalUnitCoordinates F S).apply_symm_apply (p.1.val, p.2.val)
    have hx : (sLocalUnitCoordinates F S x).2 ∈ sFiniteIntegralUnits F S := by
      change (sLocalUnitCoordinates F S ((sLocalUnitCoordinates F S).symm _)).2 ∈ _
      rw [he]
      exact p.2.property
    have hn : sLocalIdeleNorm F S x = 1 := by
      rw [sLocalNorm_of_integral F S x hx]
      change ‖(sLocalUnitCoordinates F S ((sLocalUnitCoordinates F S).symm _)).1.val‖ = 1
      rw [he]
      exact (archNormOne_iff F _).mp p.1.property
    exact ⟨⟨x, hn⟩, hx⟩
  left_inv x := Subtype.ext (Subtype.ext ((sLocalUnitCoordinates F S).symm_apply_apply x.val.val))
  right_inv p :=
    let he := (sLocalUnitCoordinates F S).apply_symm_apply (p.1.val, p.2.val)
    Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  map_mul' x y :=
    let he := map_mul (sLocalUnitCoordinates F S) x.val.val y.val.val
    Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  continuous_toFun := by
    have hc := (sLocalUnitCoordinates F S).continuous.comp
      ((continuous_subtype_val : Continuous ((↑) : SLocalNormOne F S → (SAdeles F S)ˣ)).comp
        (continuous_subtype_val : Continuous ((↑) : sLocalIntegralBlock F S → SLocalNormOne F S)))
    exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)
  continuous_invFun :=
    (((sLocalUnitCoordinates F S).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _).subtype_mk _

/-- The product of the Archimedean norm-one group and the local integral
finite units is an open subgroup of the pure S-local norm-one group. -/
def sLocalIntegralEmbed (S : Finset (Place F)) :
    archNormOne F × sFiniteIntegralUnits F S →* SLocalNormOne F S :=
  (sLocalIntegralBlock F S).subtype.comp (sLocalIntegralProduct F S).symm.toMonoidHom

theorem sLocalIntegralEmbed_open (S : Finset (Place F)) :
    IsOpenEmbedding (sLocalIntegralEmbed F S) :=
  (sLocalIntegralBlock_open F S).isOpenEmbedding_subtypeVal.comp
    (sLocalIntegralProduct F S).symm.toHomeomorph.isOpenEmbedding

/-- The genuine quotient at modulus one for the pure S-local group. -/
abbrev SLocalNormOneClass (S : Finset (Place F)) :=
  SLocalNormOne F S ⧸ (sPrincipalLocalNormOne F S).range

def sLocalNormOneQuotient (S : Finset (Place F)) : SLocalNormOne F S →* SLocalNormOneClass F S :=
  QuotientGroup.mk' (sPrincipalLocalNormOne F S).range

theorem sLocalNormOneQuotient_open (S : Finset (Place F)) :
    IsOpenQuotientMap (sLocalNormOneQuotient F S) := QuotientGroup.isOpenQuotientMap_mk

/-- The repaired A.5.2.14. A bound on adjacent finite indices suffices for
the local norm-one basis and its quotient, for any Haar normalizations. -/
theorem sLocalNormOneDoubling (S : Finset (Place F)) {c : ℝ} (hc : 0 < c)
    (K : ℕ → Subgroup (sFiniteIntegralUnits F S))
    (hKc : ∀ k, IsCompact (K k : Set (sFiniteIntegralUnits F S)))
    (hKo : ∀ k, IsOpen (K k : Set (sFiniteIntegralUnits F S)))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set (sFiniteIntegralUnits F S))))
    (hidx : ∃ N : ℕ, ∀ k, (K (k + 1)).relIndex (K k) ≤ N) :
    let W := fun k => sLocalIntegralEmbed F S '' (archDoublingBox F c k ×ˢ (K k : Set (sFiniteIntegralUnits F S)))
    OpenTranslateBasis W ∧ OpenTranslateBasis (fun k => sLocalNormOneQuotient F S '' W k) := by
  have hA : OpenTranslateBasis (archDoublingBox F c) :=
    groupBox_translateBasis (archBoxHom F) (archBoxHom_continuous F) (archBoxHom_open F) hc
  have hB := compactOpen_subgroup_translateBasis K hKc hKo hdec hcof hidx
  have h := (hA.prod hB).image (sLocalIntegralEmbed F S)
    (sLocalIntegralEmbed_open F S).continuous (sLocalIntegralEmbed_open F S).isOpenMap
  exact ⟨h, h.image _ (sLocalNormOneQuotient_open F S).continuous (sLocalNormOneQuotient_open F S).isOpenMap⟩


section PositiveNorm

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

private def positiveNormLog (N : G →* ℝ) (hp : ∀ a, 0 < N a) : G →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd (Real.log (N a))
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul N, Real.log_mul (hp a).ne' (hp b).ne']
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem positiveNormLog_ker (N : G →* ℝ) (hp : ∀ a, 0 < N a) :
    (positiveNormLog N hp).ker = N.ker := by
  ext a
  change Real.log (N a) = 0 ↔ N a = 1
  constructor
  · intro ha
    have h := congrArg Real.exp ha
    rwa [Real.exp_log (hp a), Real.exp_zero] at h
  · intro ha
    rw [ha, Real.log_one]

private def positiveNormLogSplit (N : G →* ℝ) (hp : ∀ a, 0 < N a) (hN : Continuous N)
    (τ : Multiplicative ℝ →* G) (hτ : Continuous τ)
    (hs : ∀ t, N (τ t) = Real.exp t.toAdd) :
    (Multiplicative ℝ × N.ker) ≃ₜ* G := by
  let L := positiveNormLog N hp
  have hL : Continuous L := continuous_ofAdd.comp (hN.log (fun a => (hp a).ne'))
  have hLt (t : Multiplicative ℝ) : L (τ t) = t := by
    change Multiplicative.ofAdd (Real.log (N (τ t))) = t
    rw [hs, Real.log_exp]
    rfl
  have hker : L.ker = N.ker := positiveNormLog_ker N hp
  have ha (a : G) : a / τ (L a) ∈ N.ker := by
    rw [← hker]
    change L (a / τ (L a)) = 1
    rw [map_div, hLt, div_self']
  exact
    { toFun := fun p => τ p.1 * p.2.val
      invFun := fun a => (L a, ⟨a / τ (L a), ha a⟩)
      left_inv := fun p => by
        have hp' : L p.2.val = 1 := show p.2.val ∈ L.ker from hker.symm ▸ p.2.property
        apply Prod.ext
        · change L (τ p.1 * p.2.val) = p.1
          rw [map_mul, hLt, hp', mul_one]
        · apply Subtype.ext
          change τ p.1 * p.2.val / τ (L (τ p.1 * p.2.val)) = p.2.val
          rw [map_mul, hLt, hp', mul_one, mul_comm (τ p.1), mul_div_cancel_right]
      right_inv := fun a => by
        change τ (L a) * (a / τ (L a)) = a
        rw [mul_comm, div_mul_cancel]
      map_mul' := fun p q => by
        change τ (p.1 * q.1) * (p.2.val * q.2.val) =
          (τ p.1 * p.2.val) * (τ q.1 * q.2.val)
        rw [map_mul, mul_mul_mul_comm]
      continuous_toFun := (hτ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := hL.prodMk
        ((continuous_id.div' (hτ.comp hL)).subtype_mk _) }

/-- A positive norm radius, recorded in the logarithm of the modulus. -/
def modulusBox (c : ℝ) (k : ℕ) : Set (Multiplicative ℝ) :=
  {t | |t.toAdd| < boxRadius c k}

theorem modulusBox_translateBasis {c : ℝ} (hc : 0 < c) : OpenTranslateBasis (modulusBox c) := by
  let p : Multiplicative (Unit → ℝ) →* Multiplicative ℝ :=
    { toFun := fun t => Multiplicative.ofAdd (t.toAdd ())
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hp : Continuous p := continuous_ofAdd.comp ((continuous_apply ()).comp continuous_toAdd)
  have ho : IsOpenMap p := isOpenMap_ofAdd.comp ((isOpenMap_eval ()).comp isOpenMap_toAdd)
  have h (k : ℕ) : modulusBox c k = groupBox p (boxRadius c k) := by
    ext t
    constructor
    · intro ht
      exact ⟨fun _ => t.toAdd, by
        rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (boxRadius_pos hc k)]
        exact fun _ => ht, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (boxRadius_pos hc k)] at hz
      exact hz ()
  rw [funext h]
  exact groupBox_translateBasis p hp ho hc

/-- Extend a norm-one basis to the full group using a chosen norm section.
The positive modulus interval is symmetric under inversion. -/
theorem openTranslateBasis_norm_split (N : G →* ℝ) (hp : ∀ a, 0 < N a) (hN : Continuous N)
    (τ : Multiplicative ℝ →* G) (hτ : Continuous τ)
    (hs : ∀ t, N (τ t) = Real.exp t.toAdd) {U : ℕ → Set N.ker}
    (hU : OpenTranslateBasis U) {c : ℝ} (hc : 0 < c) :
    OpenTranslateBasis (fun k => {a : G | ∃ t ∈ modulusBox c k, ∃ b ∈ U k, a = τ t * b.val}) := by
  let e := positiveNormLogSplit N hp hN τ hτ hs
  have h := ((modulusBox_translateBasis hc).prod hU).image e.toMonoidHom e.continuous
    e.toHomeomorph.isOpenMap
  convert h using 1
  funext k
  ext a
  constructor
  · rintro ⟨t, ht, b, hb, rfl⟩
    exact ⟨(t, b), ⟨ht, hb⟩, rfl⟩
  · rintro ⟨⟨t, b⟩, ⟨ht, hb⟩, rfl⟩
    exact ⟨t, ht, b, hb, rfl⟩

end PositiveNorm

private theorem sLocalEmbed_continuous (S : Finset (Place F)) :
    Continuous (sLocalEmbed F S) :=
  (sBlockUnitProduct F S).symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem sLocalIdeleNorm_continuous (S : Finset (Place F)) : Continuous (sLocalIdeleNorm F S) :=
  (ideleNorm_continuous F).comp (continuous_subtype_val.comp (sLocalEmbed_continuous F S))

theorem sLocalIdeleNorm_positive (S : Finset (Place F)) (b : (SAdeles F S)ˣ) :
    0 < sLocalIdeleNorm F S b :=
  ideleNorm_pos F (sLocalEmbed F S b).val

/-- The actual principal S-unit inclusion and the quotient of pure S-ideles. -/
def sLocalPrincipal (S : Finset (Place F)) : (sIntegerRing F S)ˣ →* (SAdeles F S)ˣ :=
  (sLocalIdeleNorm F S).ker.subtype.comp (sPrincipalLocalNormOne F S)

abbrev SLocalIdeleClass (S : Finset (Place F)) := (SAdeles F S)ˣ ⧸ (sLocalPrincipal F S).range

def sLocalIdeleClassQuotient (S : Finset (Place F)) : (SAdeles F S)ˣ →* SLocalIdeleClass F S :=
  QuotientGroup.mk' (sLocalPrincipal F S).range

/-- The repaired A.5.2.15. Extend the actual S-local norm-one boxes by an
arbitrary continuous modulus section and pass to the quotient. -/
theorem sLocalFullDoubling (S : Finset (Place F))
    (τ : Multiplicative ℝ →* (SAdeles F S)ˣ) (hτ : Continuous τ)
    (hτnorm : ∀ t, sLocalIdeleNorm F S (τ t) = Real.exp t.toAdd)
    {U : ℕ → Set (SLocalNormOne F S)} (hU : OpenTranslateBasis U)
    {c : ℝ} (hc : 0 < c) :
    let W := fun k => {a : (SAdeles F S)ˣ | ∃ t ∈ modulusBox c k, ∃ b ∈ U k, a = τ t * b.val}
    OpenTranslateBasis W ∧ OpenTranslateBasis (fun k => sLocalIdeleClassQuotient F S '' W k) := by
  have h := openTranslateBasis_norm_split (sLocalIdeleNorm F S) (sLocalIdeleNorm_positive F S)
    (sLocalIdeleNorm_continuous F S) τ hτ hτnorm hU hc
  have hq : IsOpenQuotientMap (sLocalIdeleClassQuotient F S) := QuotientGroup.isOpenQuotientMap_mk
  exact ⟨h, h.image _ hq.continuous hq.isOpenMap⟩


def normOneIntegralEmbedInS (S : Finset (Place F)) :
    archNormOne F × IntegralFiniteUnits F →* sBlockInNormOne F S :=
  (normOneIntegralEmbedHom F).codRestrict _ (fun p => by
    apply (sIdeleBlock_mem_iff F S _).mpr
    intro v hv
    exact congrArg (fun d : Multiplicative (Place F →₀ ℤ) => d.toAdd v)
      (normOneIntegralEmbed_divisor F p))

private theorem normOneIntegralEmbedInS_open (S : Finset (Place F)) :
    IsOpenEmbedding (normOneIntegralEmbedInS F S) := by
  let m := normOneIntegralEmbedInS F S
  let e := normOneIntegralEmbedHom F
  have he : IsOpenEmbedding e := normOneIntegralEmbed_open F
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (he.continuous.subtype_mk _)
    (fun _ _ h => he.injective (congrArg (fun a : sBlockInNormOne F S => a.val) h)) ?_
  intro V hV
  have heq : m '' V = Subtype.val ⁻¹' (e '' V) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨b, hb, Subtype.ext h⟩
  rw [heq]
  exact (he.isOpenMap _ hV).preimage continuous_subtype_val

private def sBlockLogNormOneEquiv (S : Finset (Place F)) :
    sBlockInNormOne F S ≃ₜ* ((ideleNorm F).comp (sIdeleBlock F S).subtype).ker where
  toFun a := ⟨⟨a.val.val, a.property⟩, a.val.property⟩
  invFun a := ⟨⟨a.val.val, a.property⟩, a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def sBlockNormOneQuotient (S : Finset (Place F)) :
    sBlockInNormOne F S →* sNormOneClass F S :=
  ((QuotientGroup.mk' (sPrincipal F S).range).comp
    (((ideleNorm F).comp (sIdeleBlock F S).subtype).ker.subtype.comp
      (sBlockLogNormOneEquiv F S).toMonoidHom)).codRestrict _
      (fun a => a.val.property)

theorem sBlockNormOneQuotient_open (S : Finset (Place F)) :
    IsOpenQuotientMap (sBlockNormOneQuotient F S) := by
  let q := QuotientGroup.mk' (sPrincipal F S).range
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  exact (hq.restrictPreimage (sNormOneClass F S : Set (SIdeleClass F S))).comp
    ⟨(sBlockLogNormOneEquiv F S).surjective, (sBlockLogNormOneEquiv F S).continuous,
      (sBlockLogNormOneEquiv F S).toHomeomorph.isOpenMap⟩

/-- The norm-one boxes in the global idele group, its extended S-block,
and their two quotients. The finite coordinates can be any open
neighborhood basis with compact bounds and uniformly bounded translates. -/
theorem globalNormOneDoubling (S : Finset (Place F))
    {V : ℕ → Set (IntegralFiniteUnits F)} (hV : OpenTranslateBasis V)
    {c : ℝ} (hc : 0 < c) :
    let U := fun k => archDoublingBox F c k ×ˢ V k
    let W := fun k => normOneIntegralEmbedHom F '' U k
    let W' := fun k => normOneIntegralEmbedInS F S '' U k
    OpenTranslateBasis W ∧ OpenTranslateBasis W' ∧
      OpenTranslateBasis (fun k => normOneIdelesToClasses F '' W k) ∧
      OpenTranslateBasis (fun k => sBlockNormOneQuotient F S '' W' k) := by
  let e := normOneIntegralEmbedHom F
  let e' := normOneIntegralEmbedInS F S
  have hA : OpenTranslateBasis (archDoublingBox F c) :=
    groupBox_translateBasis (archBoxHom F) (archBoxHom_continuous F) (archBoxHom_open F) hc
  have he : IsOpenEmbedding e := normOneIntegralEmbed_open F
  have he' := normOneIntegralEmbedInS_open F S
  have h := (hA.prod hV).image e he.continuous he.isOpenMap
  have h' := (hA.prod hV).image e' he'.continuous he'.isOpenMap
  have H := normOneIdelesToClasses_openQuotient F
  have H' := sBlockNormOneQuotient_open F S
  exact ⟨h, h', h.image _ H.continuous H.isOpenMap, h'.image _ H'.continuous H'.isOpenMap⟩

/-- Extend a global norm-one open doubling basis by a logarithmic
modulus interval, and pass it to the global idele classes. -/
theorem globalFullDoubling (τ : Multiplicative ℝ →* Idele F) (hτ : Continuous τ)
    (hτnorm : ∀ t, ideleNorm F (τ t) = Real.exp t.toAdd)
    {U : ℕ → Set (NormOneIdeles F)} (hU : OpenTranslateBasis U)
    {c : ℝ} (hc : 0 < c) :
    let W := fun k => {a : Idele F | ∃ t ∈ modulusBox c k, ∃ b ∈ U k, a = τ t * b.val}
    OpenTranslateBasis W ∧ OpenTranslateBasis (fun k => ideleClassMap F '' W k) := by
  have h := openTranslateBasis_norm_split (ideleNorm F) (ideleNorm_pos F) (ideleNorm_continuous F)
    τ hτ hτnorm hU hc
  have hq : IsOpenQuotientMap (ideleClassMap F) := QuotientGroup.isOpenQuotientMap_mk
  exact ⟨h, h.image _ hq.continuous hq.isOpenMap⟩

/-- Extend the norm-one basis in an extended S-block by any modulus
section landing in the block, and pass it to the extended S-classes. -/
theorem sBlockFullDoubling (S : Finset (Place F)) (τ : Multiplicative ℝ →* sIdeleBlock F S)
    (hτ : Continuous τ) (hτnorm : ∀ t, ideleNorm F (τ t).val = Real.exp t.toAdd)
    {U : ℕ → Set (sBlockInNormOne F S)} (hU : OpenTranslateBasis U) {c : ℝ} (hc : 0 < c) :
    let W := fun k => {a : sIdeleBlock F S | ∃ t ∈ modulusBox c k, ∃ b ∈ U k,
      a.val = (τ t).val * b.val.val}
    OpenTranslateBasis W ∧ OpenTranslateBasis
      (fun k => QuotientGroup.mk' (sPrincipal F S).range '' W k) := by
  let N := (ideleNorm F).comp (sIdeleBlock F S).subtype
  let e := sBlockLogNormOneEquiv F S
  have he := hU.image e.toMonoidHom e.continuous e.toHomeomorph.isOpenMap
  have h := openTranslateBasis_norm_split N (fun a => ideleNorm_pos F a.val)
    ((ideleNorm_continuous F).comp continuous_subtype_val) τ hτ hτnorm he hc
  have hW : OpenTranslateBasis (fun k => {a : sIdeleBlock F S | ∃ t ∈ modulusBox c k, ∃ b ∈ U k,
      a.val = (τ t).val * b.val.val}) := by
    have eq (k : ℕ) :
        {a : sIdeleBlock F S | ∃ t ∈ modulusBox c k, ∃ b ∈ U k,
          a.val = (τ t).val * b.val.val} =
        {a : sIdeleBlock F S | ∃ t ∈ modulusBox c k, ∃ b ∈ e.toMonoidHom '' U k,
          a = τ t * (b.val : sIdeleBlock F S)} := by
      ext a
      constructor
      · rintro ⟨t, ht, b, hb, ha⟩
        exact ⟨t, ht, e b, ⟨b, hb, rfl⟩, Subtype.ext ha⟩
      · rintro ⟨t, ht, _, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨t, ht, b, hb, rfl⟩
    rw [funext eq]
    exact h
  let q := QuotientGroup.mk' (sPrincipal F S).range
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  exact ⟨hW, hW.image q hq.continuous hq.isOpenMap⟩


/-- The pure S-local construction also works for arbitrary compact open
subgroup bases after inserting bounded-cover intermediate stages. -/
theorem sLocalNormOneDoubling_refined (S : Finset (Place F)) {c : ℝ} (hc : 0 < c)
    (K : ℕ → Subgroup (sFiniteIntegralUnits F S))
    (hKo : ∀ k, IsOpen (K k : Set (sFiniteIntegralUnits F S)))
    (hKc : ∀ k, IsCompact (K k : Set (sFiniteIntegralUnits F S)))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set (sFiniteIntegralUnits F S)))) :
    ∃ V : ℕ → Set (sFiniteIntegralUnits F S), (∀ k, ∃ j, V j = (K k : Set (sFiniteIntegralUnits F S))) ∧
      let W := fun k => sLocalIntegralEmbed F S '' (archDoublingBox F c k ×ˢ V k)
      OpenTranslateBasis W ∧ OpenTranslateBasis (fun k => sLocalNormOneQuotient F S '' W k) := by
  obtain ⟨V, hV, hKV⟩ := refinedCompactOpenBasis K hKo hKc hdec hcof
  have hA : OpenTranslateBasis (archDoublingBox F c) :=
    groupBox_translateBasis (archBoxHom F) (archBoxHom_continuous F) (archBoxHom_open F) hc
  have h := (hA.prod hV).image (sLocalIntegralEmbed F S)
    (sLocalIntegralEmbed_open F S).continuous (sLocalIntegralEmbed_open F S).isOpenMap
  have hq := sLocalNormOneQuotient_open F S
  exact ⟨V, hKV, h, h.image _ hq.continuous hq.isOpenMap⟩

/-- A.5.2.16 with refinement of an arbitrary finite-place subgroup basis. -/
theorem globalNormOneDoubling_refined (S : Finset (Place F)) {c : ℝ} (hc : 0 < c)
    (K : ℕ → Subgroup (IntegralFiniteUnits F))
    (hKo : ∀ k, IsOpen (K k : Set (IntegralFiniteUnits F)))
    (hKc : ∀ k, IsCompact (K k : Set (IntegralFiniteUnits F)))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set (IntegralFiniteUnits F)))) :
    ∃ V : ℕ → Set (IntegralFiniteUnits F), (∀ k, ∃ j, V j = (K k : Set (IntegralFiniteUnits F))) ∧
      let U := fun k => archDoublingBox F c k ×ˢ V k
      let W := fun k => normOneIntegralEmbedHom F '' U k
      let W' := fun k => normOneIntegralEmbedInS F S '' U k
      OpenTranslateBasis W ∧ OpenTranslateBasis W' ∧
        OpenTranslateBasis (fun k => normOneIdelesToClasses F '' W k) ∧
        OpenTranslateBasis (fun k => sBlockNormOneQuotient F S '' W' k) := by
  obtain ⟨V, hV, hKV⟩ := refinedCompactOpenBasis K hKo hKc hdec hcof
  exact ⟨V, hKV, globalNormOneDoubling F S hV hc⟩

/-- A.5.2.17 with refinement and logarithmic modulus intervals. The same
refined finite basis works for every normalizing section, including the
sections landing in the extended S-block. -/
theorem globalFullDoubling_refined (S : Finset (Place F)) {c : ℝ} (hc : 0 < c)
    (K : ℕ → Subgroup (IntegralFiniteUnits F))
    (hKo : ∀ k, IsOpen (K k : Set (IntegralFiniteUnits F)))
    (hKc : ∀ k, IsCompact (K k : Set (IntegralFiniteUnits F)))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set (IntegralFiniteUnits F)))) :
    ∃ V : ℕ → Set (IntegralFiniteUnits F), (∀ k, ∃ j, V j = (K k : Set (IntegralFiniteUnits F))) ∧
      let U := fun k => archDoublingBox F c k ×ˢ V k
      let W := fun k => normOneIntegralEmbedHom F '' U k
      let W' := fun k => normOneIntegralEmbedInS F S '' U k
      (∀ (τ : Multiplicative ℝ →* Idele F), Continuous τ →
        (∀ t, ideleNorm F (τ t) = Real.exp t.toAdd) →
        let Q := fun k => {a : Idele F | ∃ t ∈ modulusBox c k, ∃ b ∈ W k, a = τ t * b.val}
        OpenTranslateBasis Q ∧ OpenTranslateBasis (fun k => ideleClassMap F '' Q k)) ∧
      (∀ (τ : Multiplicative ℝ →* sIdeleBlock F S), Continuous τ →
        (∀ t, ideleNorm F (τ t).val = Real.exp t.toAdd) →
        let Q := fun k => {a : sIdeleBlock F S | ∃ t ∈ modulusBox c k, ∃ b ∈ W' k,
          a.val = (τ t).val * b.val.val}
        OpenTranslateBasis Q ∧ OpenTranslateBasis
          (fun k => QuotientGroup.mk' (sPrincipal F S).range '' Q k)) := by
  obtain ⟨V, hKV, hW, hW', _, _⟩ := globalNormOneDoubling_refined F S hc K hKo hKc hdec hcof
  exact ⟨V, hKV, fun τ hτ hn => globalFullDoubling F τ hτ hn hW hc,
    fun τ hτ hn => sBlockFullDoubling F S τ hτ hn hW' hc⟩


end

end Masullo
