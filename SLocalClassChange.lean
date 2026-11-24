import SUnitRank

open Function IsDedekindDomain NumberField Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

private def localIntegralUnits (v : Place F) : Subgroup (v.adicCompletion F)ˣ :=
  (v.adicCompletionIntegers F).toSubring.toSubmonoid.units

private def localOrder (v : Place F) : (v.adicCompletion F)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (-WithZero.log (Valued.v x.val))
  map_one' := by change -WithZero.log (Valued.v (1 : v.adicCompletion F)) = 0; simp
  map_mul' x y := by
    change -WithZero.log (Valued.v (x.val * y.val)) = -WithZero.log (Valued.v x.val) + -WithZero.log (Valued.v y.val)
    rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.ne_zero), neg_add]

private theorem localOrder_surjective (v : Place F) : Surjective (localOrder F v) := by
  intro n
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-n.toAdd))
  have hne : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  refine ⟨Units.mk0 x hne, ?_⟩
  change -WithZero.log (Valued.v x) = n.toAdd
  rw [hx, WithZero.log_exp, neg_neg]

private theorem localOrder_ker (v : Place F) :
    (localOrder F v).ker = localIntegralUnits F v := by
  ext x
  have hprod : Valued.v x.val * Valued.v x.inv = 1 := by rw [← map_mul, x.val_inv, map_one]
  have hone : x ∈ (localOrder F v).ker ↔ Valued.v x.val = 1 := by
    change -WithZero.log (Valued.v x.val) = 0 ↔ _
    rw [neg_eq_zero]
    constructor
    · intro h
      have he := WithZero.exp_log ((Valuation.ne_zero_iff _).mpr x.ne_zero : Valued.v x.val ≠ 0)
      rw [h, WithZero.exp_zero] at he
      exact he.symm
    · intro h
      rw [h, WithZero.log_one]
  rw [hone]
  change Valued.v x.val = 1 ↔
    x.val ∈ v.adicCompletionIntegers F ∧ x.inv ∈ v.adicCompletionIntegers F
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hprod
    exact ⟨h.le, hprod.le⟩
  · rintro ⟨hx, hy⟩
    exact le_antisymm hx (hprod.symm.trans_le (mul_le_of_le_one_right zero_le hy))

/-- The finite local multiplicative group modulo units is its integer valuation. -/
def localFieldUnitsModIntegers (v : Place F) :
    ((v.adicCompletion F)ˣ ⧸ localIntegralUnits F v) ≃* Multiplicative ℤ :=
  (QuotientGroup.quotientMulEquivOfEq (localOrder_ker F v).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (localOrder_surjective F v))

def localFieldUnitQuotientProduct (U : Finset (Place F)) :
    ((v : U) → (v.val.adicCompletion F)ˣ ⧸ localIntegralUnits F v.val) ≃*
      Multiplicative (U → ℤ) where
  toFun a := Multiplicative.ofAdd fun v => (localFieldUnitsModIntegers F v.val (a v)).toAdd
  invFun k v := (localFieldUnitsModIntegers F v.val).symm (Multiplicative.ofAdd (k.toAdd v))
  left_inv a := funext fun v => (localFieldUnitsModIntegers F v.val).symm_apply_apply (a v)
  right_inv k := Multiplicative.toAdd.injective (funext fun v =>
    congrArg Multiplicative.toAdd ((localFieldUnitsModIntegers F v.val).apply_symm_apply
      (Multiplicative.ofAdd (k.toAdd v))))
  map_mul' a b := Multiplicative.toAdd.injective (funext fun v =>
    congrArg Multiplicative.toAdd (map_mul (localFieldUnitsModIntegers F v.val) (a v) (b v)))

private def sClassOfDivisor (S : Finset (Place F)) :
    Multiplicative (Place F →₀ ℤ) →* SPicardGroup F S :=
  (QuotientGroup.mk' (sInvertedIdealClasses F S)).comp (divisorClassMap F)

theorem sInvertedIdealClasses_mono {S T : Finset (Place F)} (h : S ⊆ T) :
    sInvertedIdealClasses F S ≤ sInvertedIdealClasses F T := by
  intro c hc
  obtain ⟨d, hd, he⟩ := (sInvertedIdealClasses_divisors F S c).mp hc
  exact (sInvertedIdealClasses_divisors F T c).mpr ⟨d, hd.trans h, he⟩

def sClassTransition {S T : Finset (Place F)} (h : S ⊆ T) :
    SPicardGroup F S →* SPicardGroup F T :=
  QuotientGroup.lift _ (QuotientGroup.mk' (sInvertedIdealClasses F T))
    (fun _ hc => (QuotientGroup.eq_one_iff _).mpr (sInvertedIdealClasses_mono F h hc))

theorem sClassTransition_surjective {S T : Finset (Place F)} (h : S ⊆ T) :
    Surjective (sClassTransition F h) := by
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨QuotientGroup.mk x, rfl⟩

private def supportedDivisor (U : Finset (Place F)) : (U → ℤ) →+ (Place F →₀ ℤ) where
  toFun k := Finsupp.onFinset U (fun v => if hv : v ∈ U then k ⟨v, hv⟩ else 0)
    (fun v hv => by by_contra hn; exact hv (by simp [hn]))
  map_zero' := by ext v; simp
  map_add' := by intro a b; ext v; by_cases hv : v ∈ U <;> simp [hv]

omit [NumberField F] in
private theorem supportedDivisor_apply_pos (U : Finset (Place F)) (k : U → ℤ)
    (v : Place F) (hv : v ∈ U) : supportedDivisor F U k v = k ⟨v, hv⟩ := by
  simp [supportedDivisor, hv]

omit [NumberField F] in
private theorem supportedDivisor_apply_neg (U : Finset (Place F)) (k : U → ℤ)
    (v : Place F) (hv : v ∉ U) : supportedDivisor F U k v = 0 := by
  simp [supportedDivisor, hv]

omit [NumberField F] in
private theorem supportedDivisor_support (U : Finset (Place F)) (k : U → ℤ) :
    (supportedDivisor F U k).support ⊆ U := by
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (supportedDivisor_apply_neg F U k v hn)

/-- Classes of divisors at newly inverted places. Each factor is the
valuation coordinate of a local multiplicative group modulo its units. -/
def sNewPrimeClasses (S T : Finset (Place F)) :
    Multiplicative ((T \ S : Finset (Place F)) → ℤ) →* SPicardGroup F S :=
  (sClassOfDivisor F S).comp (supportedDivisor F (T \ S)).toMultiplicative

private theorem sClassOfDivisor_eq_one (S : Finset (Place F)) (d : Place F →₀ ℤ)
    (hd : d.support ⊆ S) : sClassOfDivisor F S (Multiplicative.ofAdd d) = 1 := by
  exact (QuotientGroup.eq_one_iff _).mpr
    ((sInvertedIdealClasses_divisors F S _).mpr ⟨d, hd, rfl⟩)

theorem sNewPrimeClasses_range {S T : Finset (Place F)} (h : S ⊆ T) :
    (sNewPrimeClasses F S T).range = (sClassTransition F h).ker := by
  ext c
  constructor
  · rintro ⟨k, rfl⟩
    exact sClassOfDivisor_eq_one F T (supportedDivisor F (T \ S) k.toAdd)
      ((supportedDivisor_support F _ _).trans Finset.sdiff_subset)
  · intro hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hx : x ∈ sInvertedIdealClasses F T := (QuotientGroup.eq_one_iff _).mp hc
    obtain ⟨d, hd, hdx⟩ := (sInvertedIdealClasses_divisors F T x).mp hx
    let k : (T \ S : Finset (Place F)) → ℤ := fun v => d v
    let e := supportedDivisor F (T \ S) k
    have hdS : (d - e).support ⊆ S := by
      intro v hv
      by_contra hns
      apply (Finsupp.mem_support_iff.mp hv)
      change d v - e v = 0
      by_cases hvt : v ∈ T
      · have he : e v = d v := supportedDivisor_apply_pos F _ k v
          (Finset.mem_sdiff.mpr ⟨hvt, hns⟩)
        rw [he, sub_self]
      · have he := supportedDivisor_apply_neg F _ k v
          (fun he => hvt (Finset.mem_sdiff.mp he).1)
        rw [he, Finsupp.notMem_support_iff.mp (fun hs => hvt (hd hs)), sub_zero]
    have he : sClassOfDivisor F S (Multiplicative.ofAdd (d - e)) = 1 :=
      sClassOfDivisor_eq_one F S _ hdS
    change sClassOfDivisor F S (Multiplicative.ofAdd d / Multiplicative.ofAdd e) = 1 at he
    rw [map_div, div_eq_one] at he
    refine ⟨Multiplicative.ofAdd k, he.symm.trans ?_⟩
    exact congrArg (QuotientGroup.mk' (sInvertedIdealClasses F S)) hdx

/-- The newly inverted valuations of an S'-unit. -/
def sUnitNewPrimeValuation (S T : Finset (Place F)) :
    (sIntegerRing F T)ˣ →* Multiplicative ((T \ S : Finset (Place F)) → ℤ) :=
  ((AddMonoidHom.toIntLinearMap {
    toFun := fun k : T → ℤ => fun v : (T \ S : Finset (Place F)) =>
      k ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩
    map_zero' := rfl
    map_add' := fun _ _ => rfl }).comp (sUnitValuation F T)).toAddMonoidHom.toMultiplicative

private theorem divisorClassMap_eq_ideleIdealClass (a : Idele F) :
    divisorClassMap F (ideleDivisor F a) = ideleIdealClass F a := rfl

theorem sNewPrimeClasses_ker {S T : Finset (Place F)} (h : S ⊆ T) :
    (sNewPrimeClasses F S T).ker = (sUnitNewPrimeValuation F S T).range := by
  ext k
  constructor
  · intro hk
    let d := supportedDivisor F (T \ S) k.toAdd
    have hc : divisorClassMap F (Multiplicative.ofAdd d) ∈ sInvertedIdealClasses F S :=
      (QuotientGroup.eq_one_iff _).mp hk
    obtain ⟨e, he, hed⟩ := (sInvertedIdealClasses_divisors F S _).mp hc
    obtain ⟨a, ha⟩ := ideleDivisor_surjective F (Multiplicative.ofAdd (d - e))
    have ha' : ideleIdealClass F a = 1 := by
      rw [← divisorClassMap_eq_ideleIdealClass, ha]
      change divisorClassMap F (Multiplicative.ofAdd d / Multiplicative.ofAdd e) = 1
      rw [map_div, hed, div_self']
    obtain ⟨t, b, hb⟩ := (ideleIdealClass_ker_iff F a).mp ha'
    have hg : ideleDivisor F (principalIdele F t) = Multiplicative.ofAdd (d - e) := by
      have hg := congrArg (ideleDivisor F) hb
      rw [ha, map_mul, show ideleDivisor F b.val = 1 from b.property, mul_one] at hg
      exact hg.symm
    have hval (v : Place F) : ideleOrder F (principalIdele F t) v = d v - e v :=
      congrArg (fun c : Multiplicative (Place F →₀ ℤ) => c.toAdd v) hg
    have ht : principalIdele F t ∈ sIdeleBlock F T := by
      apply (sIdeleBlock_mem_iff F T _).mpr
      intro v hv
      rw [hval, supportedDivisor_apply_neg F _ _ _ (fun hd => hv (Finset.mem_sdiff.mp hd).1),
        Finsupp.notMem_support_iff.mp (fun hs => hv (h (he hs))), sub_zero]
    obtain ⟨u, hu⟩ := (principalIdele_mem_sBlock F T t).mp ht
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    funext v
    change ideleOrder F (principalIdele F (sUnitToField F T u)) v = k.toAdd v
    rw [hu, hval, supportedDivisor_apply_pos F _ _ _ v.property,
      Finsupp.notMem_support_iff.mp (fun hs => (Finset.mem_sdiff.mp v.property).2 (he hs)), sub_zero]
  · rintro ⟨u, rfl⟩
    let t := sUnitToField F T u
    let c : Place F →₀ ℤ := (ideleDivisor F (principalIdele F t)).toAdd
    let d := supportedDivisor F (T \ S) (sUnitNewPrimeValuation F S T u).toAdd
    have hblock : principalIdele F t ∈ sIdeleBlock F T := (sPrincipal F T u).property
    have he : (d - c).support ⊆ S := by
      intro v hv
      by_contra hns
      apply Finsupp.mem_support_iff.mp hv
      change d v - c v = 0
      by_cases hvt : v ∈ T
      · have he : d v = c v := supportedDivisor_apply_pos F _ _ _
          (Finset.mem_sdiff.mpr ⟨hvt, hns⟩)
        rw [he, sub_self]
      · rw [supportedDivisor_apply_neg F _ _ _ (fun h => hvt (Finset.mem_sdiff.mp h).1)]
        change 0 - ideleOrder F (principalIdele F t) v = 0
        rw [(sIdeleBlock_mem_iff F T _).mp hblock v hvt, sub_zero]
    have hzero := sClassOfDivisor_eq_one F S (d - c) he
    change sClassOfDivisor F S (Multiplicative.ofAdd d / Multiplicative.ofAdd c) = 1 at hzero
    have hc : sClassOfDivisor F S (Multiplicative.ofAdd c) = 1 := by
      change QuotientGroup.mk' _ (ideleIdealClass F (principalIdele F t)) = 1
      have h := (ideleIdealClass_ker_iff F (principalIdele F t)).mpr ⟨t, 1, by simp⟩
      rw [show ideleIdealClass F (principalIdele F t) = 1 from h, map_one]
    rw [map_div, hc, div_one] at hzero
    exact hzero

theorem sPicard_eventually_subsingleton :
    ∃ S : Finset (Place F), ∀ T : Finset (Place F), S ⊆ T → Subsingleton (SPicardGroup F T) := by
  obtain ⟨S, hS⟩ := sIdeleClass_eventually_surjective F
  refine ⟨S, fun T hST => ⟨fun c d => ?_⟩⟩
  have h (x : SPicardGroup F T) : x = 1 := by
    obtain ⟨a, rfl⟩ := sLocalizedIdeleClassMap_surjective F T x
    obtain ⟨b, hb⟩ := hS T hST a
    have hm : a ∈ (sIdeleClassInclusion F T).range := ⟨b, hb⟩
    rw [← sLocalizedIdeleClassMap_ker] at hm
    exact hm
  exact (h c).trans (h d).symm

/-- If the enlarged class group is trivial, newly inverted valuations
modulo valuations of enlarged S-units recover the original S-class group. -/
def sNewPrimeClasses_quotientEquiv {S T : Finset (Place F)} (h : S ⊆ T)
    [Subsingleton (SPicardGroup F T)] :
    (Multiplicative ((T \ S : Finset (Place F)) → ℤ) ⧸
      (sUnitNewPrimeValuation F S T).range) ≃* SPicardGroup F S := by
  have hs : Surjective (sNewPrimeClasses F S T) := by
    intro x
    have hx : x ∈ (sClassTransition F h).ker := Subsingleton.elim (sClassTransition F h x) 1
    rw [← sNewPrimeClasses_range F h] at hx
    exact hx
  exact (QuotientGroup.quotientMulEquivOfEq (sNewPrimeClasses_ker F h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)

private theorem sInvertedIdealClasses_empty :
    sInvertedIdealClasses F ∅ = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  obtain ⟨d, hd, hdc⟩ := (sInvertedIdealClasses_divisors F ∅ c).mp hc
  have he : d = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hd)
  rw [he, show Multiplicative.ofAdd (0 : Place F →₀ ℤ) = 1 from rfl, map_one] at hdc
  exact hdc.symm

def sPicard_empty_equiv : SPicardGroup F ∅ ≃* ClassGroup (𝓞 F) :=
  (QuotientGroup.quotientMulEquivOfEq (sInvertedIdealClasses_empty F)).trans
    QuotientGroup.quotientBot

theorem sPicard_empty_ideleClass (a : Idele F) :
    sPicard_empty_equiv F (sLocalizedIdeleClassMap F ∅ (ideleClassMap F a)) =
      ideleIdealClass F a := by
  change QuotientGroup.quotientBot
    (QuotientGroup.quotientMulEquivOfEq (sInvertedIdealClasses_empty F)
      (QuotientGroup.mk (ideleIdealClass F a))) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

def extendNewPrimeOrders (S : Finset (Place F)) {T U : Finset (Place F)} :
    Multiplicative ((T \ S : Finset (Place F)) → ℤ) →*
      Multiplicative ((U \ S : Finset (Place F)) → ℤ) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun k v => if hv : v.val ∈ T \ S then k ⟨v.val, hv⟩ else 0
      map_zero' := by funext v; simp
      map_add' := by
        intro a b
        funext v
        simp only [Pi.add_apply]
        split <;> simp_all }

theorem sNewPrimeClasses_enlarge (S : Finset (Place F)) {T U : Finset (Place F)} (h : T ⊆ U)
    (k : Multiplicative ((T \ S : Finset (Place F)) → ℤ)) :
    sNewPrimeClasses F S U (extendNewPrimeOrders F S (U := U) k) = sNewPrimeClasses F S T k := by
  change sClassOfDivisor F S (Multiplicative.ofAdd (supportedDivisor F (U \ S) _)) =
    sClassOfDivisor F S (Multiplicative.ofAdd (supportedDivisor F (T \ S) k.toAdd))
  congr 2
  apply Finsupp.ext
  intro v
  by_cases hv : v ∈ T \ S
  · have hv' : v ∈ U \ S := Finset.mem_sdiff.mpr ⟨h (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
    rw [supportedDivisor_apply_pos F _ _ _ hv, supportedDivisor_apply_pos F _ _ _ hv']
    change (if p : v ∈ T \ S then k.toAdd ⟨v, p⟩ else 0) = _
    rw [dite_eq_left hv]
  · rw [supportedDivisor_apply_neg F _ _ _ hv]
    by_cases hv' : v ∈ U \ S
    · rw [supportedDivisor_apply_pos F _ _ _ hv']
      change (if p : v ∈ T \ S then k.toAdd ⟨v, p⟩ else 0) = 0
      rw [dite_eq_right hv]
    · exact supportedDivisor_apply_neg F _ _ _ hv'

end

end Masullo
