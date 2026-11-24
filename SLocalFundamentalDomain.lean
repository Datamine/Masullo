import SLocalOrbitComparison
import NormOneExact
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

private abbrev SValuationQuotient (S : Finset (Place F)) :=
  Multiplicative ((S → ℤ) ⧸ LinearMap.range (sUnitValuation F S))

private theorem sValuationQuotient_finite (S : Finset (Place F)) :
    Finite (SValuationQuotient F S) := by
  have hf : Module.finrank ℤ (LinearMap.range (sUnitValuation F S)) =
      Module.finrank ℤ (S → ℤ) := by
    rw [sUnitValuation_range_finrank, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  exact Submodule.finiteQuotientOfFreeOfRankEq _ hf

private def sIdeleOrders (S : Finset (Place F)) : Idele F →* Multiplicative (S → ℤ) where
  toFun a := Multiplicative.ofAdd fun v => ideleOrder F a v
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext v
    exact (ideleOrder_eq_zero_iff F 1 v).mpr (map_one _)
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext v
    exact ideleOrder_mul F a b v

private def sValuationClasses (S : Finset (Place F)) : Idele F →* SValuationQuotient F S :=
  (LinearMap.range (sUnitValuation F S)).mkQ.toAddMonoidHom.toMultiplicative.comp (sIdeleOrders F S)

private theorem sValuationClasses_eq_one (S : Finset (Place F)) (a : Idele F) :
    sValuationClasses F S a = 1 ↔
      ∃ u : (sIntegerRing F S)ˣ, sIdeleOrders F S (principalIdele F (sUnitToField F S u)) =
        sIdeleOrders F S a := by
  change Submodule.Quotient.mk (p := LinearMap.range (sUnitValuation F S))
    (sIdeleOrders F S a).toAdd = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

private theorem ideleDivisor_eq_one_of_orders (a : Idele F) (h : ∀ w : Place F, ideleOrder F a w = 0) :
    ideleDivisor F a = 1 :=
  Finsupp.ext h

private theorem ideleDivisor_eq_one_order (a : Idele F) (h : ideleDivisor F a = 1) (w : Place F) :
    ideleOrder F a w = 0 :=
  congrArg (fun c : Multiplicative (Place F →₀ ℤ) => c.toAdd w) h

private theorem sIdeleOrders_normOne_surjective (S : Finset (Place F)) (k : Multiplicative (S → ℤ)) :
    ∃ a : NormOneIdeles F, a.val ∈ sIdeleBlock F S ∧ sIdeleOrders F S a.val = k := by
  let d : Place F →₀ ℤ := Finsupp.onFinset S (fun w => if hw : w ∈ S then k.toAdd ⟨w, hw⟩ else 0)
    (fun w h => by by_contra h'; exact h (dite_eq_right h'))
  obtain ⟨b, hb⟩ := ideleDivisor_surjective F (Multiplicative.ofAdd d)
  have hl (w : Place F) : ideleOrder F b w = d w :=
    congrArg (fun c : Multiplicative (Place F →₀ ℤ) => c.toAdd w) hb
  let t := Multiplicative.ofAdd (Real.log (ideleNorm F b))
  let z := ideleExpSection F t
  have hz : ideleNorm F z = ideleNorm F b :=
    (ideleNorm_expSection F t).trans (Real.exp_log (ideleNorm_pos F b))
  have hzv (w : Place F) : ideleOrder F z w = 0 := by
    apply (ideleOrder_eq_zero_iff F z w).mpr
    change Valued.v ((ideleExpSection F t).val.2 w) = 1
    rw [(ideleExpSection_components F t).2]
    exact map_one _
  have he (w : Place F) : ideleOrder F (b / z) w = d w := by
    have h₁ : ideleOrder F ((b / z) * z) w = ideleOrder F (b / z) w := by
      rw [ideleOrder_mul, hzv, add_zero]
    rw [div_mul_cancel, hl] at h₁
    exact h₁.symm
  refine ⟨⟨b / z, by change ideleNorm F (b / z) = 1; rw [map_div, hz, div_self (ideleNorm_pos F b).ne']⟩,
    (sIdeleBlock_mem_iff F S _).mpr (fun w hw => by rw [he]; exact dite_eq_right hw), ?_⟩
  apply Multiplicative.toAdd.injective
  funext w
  exact (he w.val).trans (dite_eq_left w.property)

private theorem sValuationClasses_normOne_representatives (S : Finset (Place F)) :
    ∃ r : SValuationQuotient F S → NormOneIdeles F,
      ∀ c, (r c).val ∈ sIdeleBlock F S ∧ sValuationClasses F S (r c).val = c := by
  have hh (c : SValuationQuotient F S) :
      ∃ r : NormOneIdeles F, r.val ∈ sIdeleBlock F S ∧ sValuationClasses F S r.val = c := by
    obtain ⟨k, hk⟩ := (LinearMap.range (sUnitValuation F S)).mkQ_surjective c.toAdd
    obtain ⟨r, hr, hr'⟩ := sIdeleOrders_normOne_surjective F S (Multiplicative.ofAdd k)
    exact ⟨r, hr, (congrArg (fun x : Multiplicative (S → ℤ) =>
      Multiplicative.ofAdd ((LinearMap.range (sUnitValuation F S)).mkQ x.toAdd)) hr').trans hk⟩
  choose r hr using hh
  exact ⟨r, hr⟩

/-- A corrected S-local region. The finite translates are indexed by
valuation cosets modulo S-units. The integral cell retains the original
Archimedean sector and the full compact finite unit product. -/
def sIdelicDomain (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F) : Set (NormOneIdeles F) :=
  ⋃ c, (Homeomorph.mulLeft (r c)) '' ideleFundamentalCell F v

private theorem sIdelicDomain_mem_iff (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F)
    (hr : ∀ c, (r c).val ∈ sIdeleBlock F S ∧ sValuationClasses F S (r c).val = c)
    (a : NormOneIdeles F) :
    a ∈ sIdelicDomain F S v r ↔ (r (sValuationClasses F S a.val))⁻¹ * a ∈ ideleFundamentalCell F v := by
  constructor
  · intro h
    obtain ⟨c, b, hb, he⟩ := mem_iUnion.mp h
    change r c * b = a at he
    have hb' : sIdeleOrders F S b.val = 1 := Multiplicative.toAdd.injective
      (funext fun w => ideleDivisor_eq_one_order F b.val (ideleFundamentalCell_divisor_zero F v hb) w)
    have hq : sValuationClasses F S b.val = 1 := by
      change (LinearMap.range (sUnitValuation F S)).mkQ.toAddMonoidHom.toMultiplicative
        (sIdeleOrders F S b.val) = 1
      rw [hb', map_one]
    have hc : sValuationClasses F S a.val = c := by
      rw [← he]
      change sValuationClasses F S ((r c).val * b.val) = c
      rw [map_mul, (hr c).2, hq, mul_one]
    rwa [hc, ← he, inv_mul_cancel_left]
  · intro h
    exact mem_iUnion.mpr ⟨sValuationClasses F S a.val, ⟨_, h, mul_inv_cancel_left _ _⟩⟩

theorem sIdelicDomain_topology (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F) :
    IsCompact (closure (sIdelicDomain F S v r)) ∧ (interior (sIdelicDomain F S v r)).Nonempty := by
  letI := ideles_hausdorff (F := F)
  letI := sValuationQuotient_finite F S
  obtain ⟨K, hK, hcell⟩ := ideleFundamentalCell_containedCompact F v
  let D := ⋃ c, (Homeomorph.mulLeft (r c)) '' K
  have hD : IsCompact D := isCompact_iUnion fun c => hK.image (Homeomorph.mulLeft (r c)).continuous
  constructor
  · exact hD.closure_of_subset (iUnion_mono fun _ => image_mono hcell)
  · obtain ⟨a, ha⟩ := ideleFundamentalCell_interior F v
    let e := Homeomorph.mulLeft (r 1)
    have hopen : IsOpen (e '' interior (ideleFundamentalCell F v)) := e.isOpenMap _ isOpen_interior
    have hg : e '' ideleFundamentalCell F v ⊆ sIdelicDomain F S v r :=
      subset_iUnion (fun c => (Homeomorph.mulLeft (r c)) '' ideleFundamentalCell F v) 1
    exact ⟨e a, interior_maximal ((image_mono interior_subset).trans hg) hopen ⟨a, ha, rfl⟩⟩

private theorem sIdelicDomain_subset_cell (v : InfinitePlace F) (S : Finset (Place F))
    {a : NormOneIdeles F} (h : a ∈ ideleFundamentalCell F v) : a.val ∈ sIdeleBlock F S :=
  (sIdeleBlock_mem_iff F S _).mpr fun w _ =>
    ideleDivisor_eq_one_order F a.val (ideleFundamentalCell_divisor_zero F v h) w

theorem sIdelicDomain_subset (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F)
    (hr : ∀ c, (r c).val ∈ sIdeleBlock F S ∧ sValuationClasses F S (r c).val = c) :
    ∀ a ∈ sIdelicDomain F S v r, a.val ∈ sIdeleBlock F S := by
  intro a ha
  obtain ⟨c, b, hb, rfl⟩ := mem_iUnion.mp ha
  exact (sIdeleBlock F S).mul_mem (hr c).1 (sIdelicDomain_subset_cell F v S hb)

private def sPrincipalNormOne (S : Finset (Place F)) :
    (sIntegerRing F S)ˣ →* NormOneIdeles F :=
  (principalNormOne F).comp (sUnitToField F S)

private theorem sPrincipalNormOne_class_one (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ) :
    sValuationClasses F S (sPrincipalNormOne F S u).val = 1 :=
  (sValuationClasses_eq_one F S _).mpr ⟨u, rfl⟩

theorem sIdelicDomain_unique (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F)
    (hr : ∀ c, (r c).val ∈ sIdeleBlock F S ∧ sValuationClasses F S (r c).val = c)
    (a : NormOneIdeles F) (ha : a.val ∈ sIdeleBlock F S) :
    ∃! u : (sIntegerRing F S)ˣ, sPrincipalNormOne F S u * a ∈ sIdelicDomain F S v r := by
  let q := sValuationClasses F S
  let d := r (q a.val)
  let b := d⁻¹ * a
  have hb : b.val ∈ sIdeleBlock F S := (sIdeleBlock F S).mul_mem
    ((sIdeleBlock F S).inv_mem (hr (q a.val)).1) ha
  have hqb : q b.val = 1 := by
    change q (d.val⁻¹ * a.val) = 1
    rw [map_mul, map_inv, (hr (q a.val)).2, inv_mul_cancel]
  obtain ⟨u₀, h₀⟩ := (sValuationClasses_eq_one F S b.val).mp hqb
  let p := sPrincipalNormOne F S
  let c := (p u₀)⁻¹ * b
  have hc : c.val ∈ sIdeleBlock F S := (sIdeleBlock F S).mul_mem
    ((sIdeleBlock F S).inv_mem (sPrincipal F S u₀).property) hb
  have hdiv : ideleDivisor F c.val = 1 := by
    apply ideleDivisor_eq_one_of_orders
    intro w
    by_cases hw : w ∈ S
    · have ho : sIdeleOrders F S c.val = 1 := by
        change sIdeleOrders F S ((principalIdele F (sUnitToField F S u₀))⁻¹ * b.val) = 1
        rw [map_mul, map_inv, h₀, inv_mul_cancel]
      exact congrArg (fun x : Multiplicative (S → ℤ) => x.toAdd ⟨w, hw⟩) ho
    · exact (sIdeleBlock_mem_iff F S _).mp hc w hw
  have hcl : normOneIdealClass F c = 1 := by
    change ClassGroup.mk F (divisorFractionalIdeal F (ideleDivisor F c.val)) = 1
    rw [hdiv, map_one, map_one]
  obtain ⟨t, ht, _⟩ := ideleFundamentalCell_unique F v c hcl
  have htB : principalIdele F t ∈ sIdeleBlock F S := by
    have h := (sIdeleBlock F S).mul_mem
      (sIdelicDomain_subset_cell F v S ht) ((sIdeleBlock F S).inv_mem hc)
    change (principalIdele F t * c.val) * c.val⁻¹ ∈ _ at h
    rwa [mul_inv_cancel_right] at h
  obtain ⟨u₁, hu₁⟩ := (principalIdele_mem_sBlock F S t).mp htB
  let u := u₁ / u₀
  have hclass (w : (sIntegerRing F S)ˣ) : q (p w * a).val = q a.val := by
    change q ((p w).val * a.val) = _
    rw [map_mul, sPrincipalNormOne_class_one F S w, one_mul]
  have hout : d⁻¹ * (p u * a) ∈ ideleFundamentalCell F v := by
    have h : d⁻¹ * (p u * a) = principalNormOne F t * c := by
      change d⁻¹ * (p (u₁ / u₀) * a) = principalNormOne F t * ((p u₀)⁻¹ * (d⁻¹ * a))
      rw [map_div, ← hu₁]
      change d⁻¹ * (p u₁ / p u₀ * a) = p u₁ * ((p u₀)⁻¹ * (d⁻¹ * a))
      rw [div_eq_mul_inv, mul_assoc]
      exact (mul_left_comm d⁻¹ (p u₁) ((p u₀)⁻¹ * a)).trans
        (congrArg (p u₁ * ·) (mul_left_comm d⁻¹ (p u₀)⁻¹ a))
    rwa [h]
  refine ⟨u, (sIdelicDomain_mem_iff F S v r hr _).mpr (by rw [hclass]; exact hout), ?_⟩
  intro w hw
  have hw' := (sIdelicDomain_mem_iff F S v r hr _).mp hw
  rw [hclass] at hw'
  have hmove :
      principalNormOne F (sUnitToField F S (w / u)) * (d⁻¹ * (p u * a)) =
        d⁻¹ * (p w * a) := by
    change p (w / u) * (d⁻¹ * (p u * a)) = _
    rw [map_div, div_eq_mul_inv]
    calc
      _ = d⁻¹ * ((p w * (p u)⁻¹) * (p u * a)) := mul_left_comm _ _ _
      _ = _ := by
        rw [mul_assoc (p w), ← mul_assoc ((p u)⁻¹) (p u) a, inv_mul_cancel, one_mul]
  have he : sUnitToField F S (w / u) = 1 :=
    ideleFundamentalCell_no_translate F v _ hout _ (hmove.symm ▸ hw')
  have hwu : w / u = 1 := sUnitToField_injective F S (he.trans (map_one _).symm)
  exact div_eq_one.mp hwu

theorem sIdelicDomain_finite_translates (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F)
    {K : Set (NormOneIdeles F)} (hK : IsCompact K) :
    {u : (sIntegerRing F S)ˣ | ∃ a ∈ closure (sIdelicDomain F S v r),
      sPrincipalNormOne F S u * a ∈ K}.Finite := by
  let val : NormOneIdeles F → Idele F := Subtype.val
  have hD := (sIdelicDomain_topology F S v r).1
  refine ((principalIdele_finite_translates F (hK.image (f := val) continuous_subtype_val)
    (hD.image (f := val) continuous_subtype_val)).preimage (sUnitToField_injective F S).injOn).subset ?_
  rintro u ⟨a, ha, hu⟩
  exact ⟨a.val, ⟨a, ha, rfl⟩, ⟨sPrincipalNormOne F S u * a, hu, rfl⟩⟩

def sBlockUnitProduct (S : Finset (Place F)) :
    sIdeleBlock F S ≃ₜ* (SAdeles F S)ˣ × (SIntegralTail F S)ˣ :=
  (sIdeleBlockHomeomorph F S).trans
    { toMulEquiv := MulEquiv.prodUnits
      continuous_toFun := Homeomorph.prodUnits.continuous
      continuous_invFun := Homeomorph.prodUnits.symm.continuous }

/-- Insert an S-local idele with unit coordinates off S. -/
def sLocalEmbed (S : Finset (Place F)) : (SAdeles F S)ˣ →* sIdeleBlock F S :=
  (sBlockUnitProduct F S).symm.toMonoidHom.comp (MonoidHom.inl _ _)

def sTailEmbed (S : Finset (Place F)) : (SIntegralTail F S)ˣ →* sIdeleBlock F S :=
  (sBlockUnitProduct F S).symm.toMonoidHom.comp (MonoidHom.inr _ _)

theorem sLocalEmbed_project (S : Finset (Place F)) (a : (SAdeles F S)ˣ) :
    sAdelesProjection F S (sLocalEmbed F S a).val.val = a.val :=
  congrArg (fun p : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => p.1.val)
    ((sBlockUnitProduct F S).apply_symm_apply (a, 1))

private theorem sBlockUnitProduct_local_arch (S : Finset (Place F)) (a : sIdeleBlock F S) :
    (sBlockUnitProduct F S a).1.val.1 = a.val.val.1 := rfl

private theorem sBlockUnitProduct_local_finite (S : Finset (Place F)) (a : sIdeleBlock F S) (v : S) :
    (sBlockUnitProduct F S a).1.val.2 v = a.val.val.2 v := rfl

private theorem sTailEmbed_arch_one (S : Finset (Place F)) (b : (SIntegralTail F S)ˣ) :
    (sTailEmbed F S b).val.val.1 = 1 := by
  rw [← sBlockUnitProduct_local_arch F S]
  have h : sBlockUnitProduct F S (sTailEmbed F S b) = (1, b) :=
    (sBlockUnitProduct F S).apply_symm_apply (1, b)
  rw [h]
  rfl

private theorem sTailEmbed_divisor_one (S : Finset (Place F)) (b : (SIntegralTail F S)ˣ) :
    ideleDivisor F (sTailEmbed F S b).val = 1 := by
  apply ideleDivisor_eq_one_of_orders
  intro v
  by_cases hv : v ∈ S
  · have h : sBlockUnitProduct F S (sTailEmbed F S b) = (1, b) :=
      (sBlockUnitProduct F S).apply_symm_apply (1, b)
    have he : (sTailEmbed F S b).val.val.2 v = 1 := by
      rw [← sBlockUnitProduct_local_finite F S _ ⟨v, hv⟩, h]
      rfl
    apply (ideleOrder_eq_zero_iff F _ v).mpr
    rw [he, map_one]
  · exact (sIdeleBlock_mem_iff F S _).mp (sTailEmbed F S b).property v hv

theorem sTailEmbed_norm_one (S : Finset (Place F)) (b : (SIntegralTail F S)ˣ) :
    ideleNorm F (sTailEmbed F S b).val = 1 := by
  rw [ideleNorm_eq_arch_of_finite_integral F _ (sTailEmbed_divisor_one F S b),
    sTailEmbed_arch_one]
  rw [InfiniteAdeleRing.norm_def]
  change (∏ v : InfinitePlace F, ‖(1 : v.Completion)‖ ^ v.mult) = 1
  simp

/-- The norm on the S-ideles with no tail, obtained by inserting unit tail
coordinates. All other integral-unit tails give the same norm. -/
def sLocalIdeleNorm (S : Finset (Place F)) : (SAdeles F S)ˣ →* ℝ :=
  (ideleNorm F).comp ((sIdeleBlock F S).subtype.comp (sLocalEmbed F S))

theorem sBlock_norm_eq (S : Finset (Place F)) (a : sIdeleBlock F S) :
    sLocalIdeleNorm F S (sBlockUnitProduct F S a).1 = ideleNorm F a.val := by
  let p := sBlockUnitProduct F S a
  have h : sLocalEmbed F S p.1 * sTailEmbed F S p.2 = a := by
    apply (sBlockUnitProduct F S).injective
    rw [map_mul]
    change sBlockUnitProduct F S ((sBlockUnitProduct F S).symm (p.1, 1)) *
      sBlockUnitProduct F S ((sBlockUnitProduct F S).symm (1, p.2)) = p
    rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
    exact Prod.ext (mul_one _) (one_mul _)
  have he := congrArg (fun a : sIdeleBlock F S => ideleNorm F a.val) h
  change ideleNorm F ((sLocalEmbed F S p.1).val * (sTailEmbed F S p.2).val) =
    ideleNorm F a.val at he
  rw [map_mul, sTailEmbed_norm_one, mul_one] at he
  exact he

def sBlockInNormOne (S : Finset (Place F)) : Subgroup (NormOneIdeles F) :=
  (sIdeleBlock F S).comap (ideleNorm F).ker.subtype

abbrev SLocalNormOne (S : Finset (Place F)) := (sLocalIdeleNorm F S).ker

def sNormOneBlockProduct (S : Finset (Place F)) :
    sBlockInNormOne F S ≃ₜ* SLocalNormOne F S × (SIntegralTail F S)ˣ where
  toFun a :=
    let p := sBlockUnitProduct F S ⟨a.val.val, a.property⟩
    (⟨p.1, (sBlock_norm_eq F S _).trans a.val.property⟩, p.2)
  invFun p :=
    let b := (sBlockUnitProduct F S).symm (p.1.val, p.2)
    ⟨⟨b.val, by
      have e := sBlock_norm_eq F S b
      change sLocalIdeleNorm F S ((sBlockUnitProduct F S) ((sBlockUnitProduct F S).symm _)).1 =
        ideleNorm F b.val at e
      rw [ContinuousMulEquiv.apply_symm_apply] at e
      exact e.symm.trans p.1.property⟩, b.property⟩
  left_inv a := Subtype.ext (Subtype.ext (congrArg (fun b : sIdeleBlock F S => b.val)
    ((sBlockUnitProduct F S).symm_apply_apply ⟨a.val.val, a.property⟩)))
  right_inv p := by
    have e := (sBlockUnitProduct F S).apply_symm_apply (p.1.val, p.2)
    exact Prod.ext
      (Subtype.ext (congrArg (fun a : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => a.1) e))
      (congrArg (fun a : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => a.2) e)
  map_mul' a b := by
    have e := map_mul (sBlockUnitProduct F S) ⟨a.val.val, a.property⟩ ⟨b.val.val, b.property⟩
    exact Prod.ext
      (Subtype.ext (congrArg (fun a : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => a.1) e))
      (congrArg (fun a : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => a.2) e)
  continuous_toFun := by
    let g (a : sBlockInNormOne F S) : sIdeleBlock F S := ⟨a.val.val, a.property⟩
    have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
    have h := (sBlockUnitProduct F S).continuous_toFun.comp hg
    exact h.fst.subtype_mk _ |>.prodMk h.snd
  continuous_invFun := by
    have hc : Continuous (fun p : SLocalNormOne F S × (SIntegralTail F S)ˣ =>
        (sBlockUnitProduct F S).symm (p.1.val, p.2)) :=
      (sBlockUnitProduct F S).symm.continuous_toFun.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact ((continuous_subtype_val.comp hc).subtype_mk _).subtype_mk _

def sPrincipalInBlock (S : Finset (Place F)) :
    (sIntegerRing F S)ˣ →* sBlockInNormOne F S :=
  (sPrincipalNormOne F S).codRestrict _ (fun u => (sPrincipal F S u).property)

def sPrincipalLocalNormOne (S : Finset (Place F)) :
    (sIntegerRing F S)ˣ →* SLocalNormOne F S :=
  (MonoidHom.fst _ _).comp ((sNormOneBlockProduct F S).toMonoidHom.comp (sPrincipalInBlock F S))

theorem sLocalEmbed_arch (S : Finset (Place F)) (a : (SAdeles F S)ˣ) :
    (sLocalEmbed F S a).val.val.1 = a.val.1 := by
  have h := (sBlockUnitProduct F S).apply_symm_apply (a, 1)
  rw [← sBlockUnitProduct_local_arch F S]
  exact congrArg (fun x : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => x.1.val.1) h

theorem sLocalEmbed_finite (S : Finset (Place F)) (a : (SAdeles F S)ˣ) (v : S) :
    (sLocalEmbed F S a).val.val.2 v = a.val.2 v := by
  have h := (sBlockUnitProduct F S).apply_symm_apply (a, 1)
  rw [← sBlockUnitProduct_local_finite F S _ v]
  exact congrArg (fun x : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ => x.1.val.2 v) h

theorem sPrincipalLocalNormOne_arch (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ) :
    (sPrincipalLocalNormOne F S u).val.val.1 = (principalIdele F (sUnitToField F S u)).val.1 :=
  rfl

theorem sPrincipalLocalNormOne_finite (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ) (v : S) :
    (sPrincipalLocalNormOne F S u).val.val.2 v = (principalIdele F (sUnitToField F S u)).val.2 v :=
  rfl

private theorem sIdelicDomain_mul_integral_arch_one (S : Finset (Place F)) (v : InfinitePlace F)
    (r : SValuationQuotient F S → NormOneIdeles F)
    (hr : ∀ c, (r c).val ∈ sIdeleBlock F S ∧ sValuationClasses F S (r c).val = c)
    (a b : NormOneIdeles F) (hb : ideleDivisor F b.val = 1) (hbArch : b.val.val.1 = 1) :
    a * b ∈ sIdelicDomain F S v r ↔ a ∈ sIdelicDomain F S v r := by
  have hb₀ : sIdeleOrders F S b.val = 1 := Multiplicative.toAdd.injective
    (funext fun w => ideleDivisor_eq_one_order F b.val hb w)
  have hb₁ : sValuationClasses F S b.val = 1 := by
    change (LinearMap.range (sUnitValuation F S)).mkQ.toAddMonoidHom.toMultiplicative
      (sIdeleOrders F S b.val) = 1
    rw [hb₀, map_one]
  have h : sValuationClasses F S (a * b).val = sValuationClasses F S a.val := by
    change sValuationClasses F S (a.val * b.val) = _
    rw [map_mul, hb₁, mul_one]
  rw [sIdelicDomain_mem_iff F S v r hr, sIdelicDomain_mem_iff F S v r hr, h, ← mul_assoc]
  exact ideleFundamentalCell_mul_integral_arch_one F v _ b hb hbArch

/-- The corrected S-local domain and its exact relationship to the
domain in the global block with its compact integral tail. -/
theorem sLocalNormOne_fundamentalDomain (S : Finset (Place F)) (v : InfinitePlace F) :
    ∃ (r : SValuationQuotient F S → NormOneIdeles F) (D : Set (SLocalNormOne F S)),
      (∀ c, (r c).val ∈ sIdeleBlock F S ∧ sValuationClasses F S (r c).val = c) ∧
      IsCompact (closure D) ∧ (interior D).Nonempty ∧
      (∀ a : SLocalNormOne F S, ∃! u : (sIntegerRing F S)ˣ,
        sPrincipalLocalNormOne F S u * a ∈ D) ∧
      (∀ K : Set (SLocalNormOne F S), IsCompact K →
        {u : (sIntegerRing F S)ˣ | ∃ a ∈ closure D, sPrincipalLocalNormOne F S u * a ∈ K}.Finite) ∧
      sNormOneBlockProduct F S '' ((Subtype.val : sBlockInNormOne F S → NormOneIdeles F) ⁻¹'
        sIdelicDomain F S v r) = D ×ˢ univ := by
  obtain ⟨r, hr⟩ := sValuationClasses_normOne_representatives F S
  let B := sBlockInNormOne F S
  let val : B → NormOneIdeles F := Subtype.val
  let e := sNormOneBlockProduct F S
  let E := sIdelicDomain F S v r
  let E' := e '' (val ⁻¹' E)
  let D := Prod.fst '' E'
  have he (x : SLocalNormOne F S × (SIntegralTail F S)ˣ) :
      x ∈ E' ↔ val (e.symm x) ∈ E := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [ContinuousMulEquiv.symm_apply_apply]
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have htail (x : SLocalNormOne F S) (y : (SIntegralTail F S)ˣ) :
      (x, y) ∈ E' ↔ (x, 1) ∈ E' := by
    let b : NormOneIdeles F := val (e.symm (1, y))
    have hb : ideleDivisor F b.val = 1 := sTailEmbed_divisor_one F S y
    have hb' : b.val.val.1 = 1 := sTailEmbed_arch_one F S y
    rw [he, he]
    have hh : e.symm (x, y) = e.symm (x, 1) * e.symm (1, y) := by
      rw [← map_mul]
      exact congrArg e.symm (Prod.ext (mul_one x).symm (one_mul y).symm)
    rw [hh]
    exact sIdelicDomain_mul_integral_arch_one F S v r hr _ _ hb hb'
  have hprod : E' = D ×ˢ (univ : Set ((SIntegralTail F S)ˣ)) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨p, hp, rfl⟩, mem_univ _⟩
    · rintro ⟨⟨q, hq, hq'⟩, _⟩
      exact (htail p.1 p.2).mpr (hq' ▸ (htail q.1 q.2).mp hq)
  have hB : IsOpen (B : Set (NormOneIdeles F)) := (sIdeleBlock_open F S).preimage continuous_subtype_val
  have hB' : IsClosed (B : Set (NormOneIdeles F)) := B.isClosed_of_isOpen hB
  have hC : IsCompact (closure E) := (sIdelicDomain_topology F S v r).1
  have hV : closure E' = e '' (val ⁻¹' closure E) := by
    have hv : IsOpenMap val := hB.isOpenEmbedding_subtypeVal.isOpenMap
    rw [hv.preimage_closure_eq_closure_preimage continuous_subtype_val]
    exact (e.toHomeomorph.image_closure (val ⁻¹' E)).symm
  have hCP : IsCompact (closure E') :=
    hV ▸ (hB'.isClosedEmbedding_subtypeVal.isCompact_preimage hC).image e.continuous_toFun
  have hclosure : closure E' = closure D ×ˢ (univ : Set ((SIntegralTail F S)ˣ)) := by
    rw [hprod, closure_prod_eq, closure_univ]
  refine ⟨r, D, hr, ?_, ?_, ?_, ?_, hprod⟩
  · have hf : Prod.fst '' closure E' = closure D := by
      rw [hclosure, fst_image_prod _ univ_nonempty]
    exact hf ▸ hCP.image continuous_fst
  · obtain ⟨a, ha⟩ := (sIdelicDomain_topology F S v r).2
    let z : B := ⟨a, sIdelicDomain_subset F S v r hr a (interior_subset ha)⟩
    have hop : IsOpen (e '' (val ⁻¹' interior E)) :=
      e.toHomeomorph.isOpenMap _ (isOpen_interior.preimage continuous_subtype_val)
    have hsub : e '' (val ⁻¹' interior E) ⊆ E' := image_mono (preimage_mono interior_subset)
    have hi := interior_maximal hsub hop (show e z ∈ e '' (val ⁻¹' interior E) from ⟨z, ha, rfl⟩)
    rw [hprod, interior_prod_eq] at hi
    exact ⟨(e z).1, hi.1⟩
  · intro a
    let z := e.symm (a, 1)
    have hz := sIdelicDomain_unique F S v r hr z.val z.property
    refine (existsUnique_congr fun u => ?_).mp hz
    let j := sPrincipalInBlock F S
    have hp : e (j u * z) = e (j u) * (a, 1) := by
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
    have hmem : e (j u * z) ∈ E' ↔ sPrincipalNormOne F S u * z.val ∈ E := by
      rw [he, ContinuousMulEquiv.symm_apply_apply]
      rfl
    rw [← hmem, hp, hprod]
    exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩
  · intro K hK
    letI (i : {w : Place F // w ∉ S}) : CompactSpace (i.val.adicCompletionIntegers F) :=
      compactSpace_adicIntegers i.val
    let K' := val '' (e.symm '' (K ×ˢ (univ : Set ((SIntegralTail F S)ˣ))))
    have hf : IsCompact K' := ((hK.prod isCompact_univ).image
      e.symm.continuous_toFun).image continuous_subtype_val
    refine (sIdelicDomain_finite_translates F S v r hf).subset ?_
    rintro u ⟨x, hx, hu⟩
    let z := e.symm (x, 1)
    have hz' : (x, (1 : (SIntegralTail F S)ˣ)) ∈ closure E' := by
      rw [hclosure]
      exact ⟨hx, mem_univ _⟩
    have hz : z.val ∈ closure E := by
      rw [hV] at hz'
      obtain ⟨w, hw, heq⟩ := hz'
      have e₁ : w = z := e.injective (heq.trans (e.apply_symm_apply (x, 1)).symm)
      exact e₁ ▸ hw
    let j := sPrincipalInBlock F S
    have hju : e (j u * z) ∈ K ×ˢ (univ : Set ((SIntegralTail F S)ˣ)) := by
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
      exact ⟨hu, mem_univ _⟩
    exact ⟨z.val, hz, ⟨j u * z, ⟨e (j u * z), hju, e.symm_apply_apply _⟩, rfl⟩⟩

end

end Masullo
