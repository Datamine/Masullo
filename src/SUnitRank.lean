import SLocalIdelic
import NormOneClassCompact
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

def sNormOneClass (S : Finset (Place F)) : Subgroup (SIdeleClass F S) :=
  ((ideleClassNorm F).comp (sIdeleClassInclusion F S)).ker

theorem sNormOneClass_compact_hausdorff (S : Finset (Place F)) :
    CompactSpace (sNormOneClass F S) ∧ T2Space (sNormOneClass F S) := by
  let i := sIdeleClassInclusion F S
  let j : sNormOneClass F S → normOneIdeleClass F := fun x => ⟨i x.val, x.property⟩
  letI := normOneIdeleClass_compact (F := F)
  letI := ideleClasses_hausdorff (F := F)
  have hi := sIdeleClassInclusion_openEmbedding F S
  have hj : IsEmbedding j := by
    have hval : IsEmbedding (Subtype.val : normOneIdeleClass F → IdeleClass F) := IsEmbedding.subtypeVal
    apply (hval.of_comp_iff (f := j)).mp
    exact hi.isEmbedding.comp IsEmbedding.subtypeVal
  have hr : Set.range j = Subtype.val ⁻¹' (i.range : Set (IdeleClass F)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, rfl⟩
    · rintro ⟨y, hy⟩
      have hyn : y ∈ sNormOneClass F S := by
        change ideleClassNorm F (i y) = 1
        rw [hy]
        exact x.property
      exact ⟨⟨y, hyn⟩, Subtype.ext hy⟩
  have hclosed : IsClosed (Set.range j) := by
    rw [hr]
    exact (i.range.isClosed_of_isOpen hi.isOpen_range).preimage continuous_subtype_val
  have hj' : IsClosedEmbedding j := ⟨hj, hclosed⟩
  exact ⟨hj'.compactSpace, hj.t2Space⟩

private def integralToS (S : Finset (Place F)) : (𝓞 F) →+* sIntegerRing F S :=
  (algebraMap (𝓞 F) F).codRestrict _ fun x v _ =>
    HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v x

def integralUnitToS (S : Finset (Place F)) : (𝓞 F)ˣ →* (sIntegerRing F S)ˣ :=
  Units.map (integralToS F S)

theorem sUnitToField_injective (S : Finset (Place F)) : Injective (sUnitToField F S) := by
  intro a b h
  exact Units.ext (Subtype.ext (congrArg Units.val h))

private theorem integralUnitToS_injective (S : Finset (Place F)) :
    Injective (integralUnitToS F S) := by
  intro a b h
  apply Units.ext
  exact (IsFractionRing.injective (𝓞 F) F)
    (congrArg (fun u : (sIntegerRing F S)ˣ => (u.val : F)) h)

/-- Valuations at the inverted primes. -/
def sUnitValuation (S : Finset (Place F)) :
    Additive (sIntegerRing F S)ˣ →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun u v => ideleOrder F (principalIdele F (sUnitToField F S u.toMul)) v
      map_zero' := by
        funext v
        change ideleOrder F (principalIdele F (sUnitToField F S 1)) v = 0
        rw [map_one, map_one]
        exact (ideleOrder_eq_zero_iff F 1 v).mpr (map_one _)
      map_add' := by
        intro a b
        funext v
        change ideleOrder F (principalIdele F (sUnitToField F S (a.toMul * b.toMul))) v = _
        rw [map_mul, map_mul, ideleOrder_mul]
        rfl }

private theorem divisor_ker_of_orders (a : Idele F) (h : ∀ v : Place F, ideleOrder F a v = 0) :
    a ∈ (ideleDivisor F).ker := by
  change ideleDivisor F a = 1
  exact Finsupp.ext h

def sUnitValuation_ker (S : Finset (Place F)) :
    (sUnitValuation F S).ker ≃ₗ[ℤ] Additive (𝓞 F)ˣ := by
  let j : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sIntegerRing F S)ˣ :=
    (integralUnitToS F S).toAdditive.toIntLinearMap
  have hj : LinearMap.range j = (sUnitValuation F S).ker := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      have hb := (principalIdele_integral_iff F (integralUnitToField F b.toMul)).mpr ⟨b.toMul, rfl⟩
      change ideleDivisor F (principalIdele F (integralUnitToField F b.toMul)) = 1 at hb
      apply LinearMap.mem_ker.mpr
      funext v
      exact congrArg (fun d : Multiplicative (Place F →₀ ℤ) => d.toAdd v.val) hb
    · intro ha
      let t := sUnitToField F S a.toMul
      have hblock : principalIdele F t ∈ sIdeleBlock F S :=
        (principalIdele_mem_sBlock F S t).mpr ⟨a.toMul, rfl⟩
      have hzero (v : Place F) : ideleOrder F (principalIdele F t) v = 0 := by
        by_cases hv : v ∈ S
        · exact congrFun (LinearMap.mem_ker.mp ha) ⟨v, hv⟩
        · exact (sIdeleBlock_mem_iff F S _).mp hblock v hv
      obtain ⟨b, hb⟩ := (principalIdele_integral_iff F t).mp (divisor_ker_of_orders F _ hzero)
      refine ⟨Additive.ofMul b, ?_⟩
      exact sUnitToField_injective F S hb
  exact ((LinearEquiv.ofInjective j (integralUnitToS_injective F S)).trans
    (LinearEquiv.ofEq _ _ hj)).symm

/-- The class number annihilates the cokernel of the S-unit valuation map. -/
theorem sUnitValuation_classNumber (S : Finset (Place F)) (k : S → ℤ) :
    (Nat.card (ClassGroup (𝓞 F))) • k ∈ LinearMap.range (sUnitValuation F S) := by
  let h := Nat.card (ClassGroup (𝓞 F))
  let d : Place F →₀ ℤ := Finsupp.onFinset S (fun v => if hv : v ∈ S then k ⟨v, hv⟩ else 0)
    (fun v hv => by by_contra hn; exact hv (by simp [hn]))
  obtain ⟨a, ha⟩ := ideleDivisor_surjective F (Multiplicative.ofAdd d)
  have ha' : ideleIdealClass F (a ^ h) = 1 := by rw [map_pow, pow_card_eq_one']
  obtain ⟨t, b, hb⟩ := (ideleIdealClass_ker_iff F (a ^ h)).mp ha'
  have hdiv : ideleDivisor F (principalIdele F t) = Multiplicative.ofAdd (h • d) := by
    have e := congrArg (ideleDivisor F) hb
    have hb' : ideleDivisor F b.val = 1 := b.property
    rw [map_pow, map_mul, ha, hb'] at e
    rw [mul_one] at e
    exact e.symm
  have hval (v : Place F) : ideleOrder F (principalIdele F t) v = h • d v :=
    congrArg (fun x : Multiplicative (Place F →₀ ℤ) => x.toAdd v) hdiv
  have ht : principalIdele F t ∈ sIdeleBlock F S :=
    (sIdeleBlock_mem_iff F S _).mpr fun v hv => by rw [hval]; simp [d, hv]
  obtain ⟨u, hu⟩ := (principalIdele_mem_sBlock F S t).mp ht
  refine ⟨Additive.ofMul u, ?_⟩
  funext v
  change ideleOrder F (principalIdele F (sUnitToField F S u)) v.val = h • k v
  rw [hu, hval]
  simp [d, v.property]

theorem sUnitValuation_range_finrank (S : Finset (Place F)) :
    Module.finrank ℤ (LinearMap.range (sUnitValuation F S)) = S.card := by
  let R := LinearMap.range (sUnitValuation F S)
  let h := Nat.card (ClassGroup (𝓞 F))
  let f : (S → ℤ) →ₗ[ℤ] R :=
    (h • (LinearMap.id : (S → ℤ) →ₗ[ℤ] (S → ℤ))).codRestrict R
      (sUnitValuation_classNumber F S)
  have hf : Injective f := by
    intro k l e
    funext v
    have hv : (h : ℤ) * k v = (h : ℤ) * l v :=
      congrArg (fun q : R => (q.val : S → ℤ) v) e
    have hh : (h : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr Nat.card_pos.ne'
    exact mul_left_cancel₀ hh hv
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  have hge := LinearMap.finrank_le_finrank_of_injective R.injective_subtype
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle hge
  exact le_antisymm hge hle

theorem sUnits_finite (S : Finset (Place F)) : Module.Finite ℤ (Additive (sIntegerRing F S)ˣ) := by
  let f := sUnitValuation F S
  have hk : Module.Finite ℤ f.ker := Module.Finite.equiv (sUnitValuation_ker F S).symm
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
  · rw [Submodule.map_top]
    exact Submodule.FG.of_finite
  · simpa only [top_inf_eq] using (Module.Finite.iff_fg.mp hk)

theorem sUnits_finrank (S : Finset (Place F)) :
    Module.finrank ℤ (Additive (sIntegerRing F S)ˣ) = Fintype.card (InfinitePlace F) + S.card - 1 := by
  letI := sUnits_finite F S
  let f := sUnitValuation F S
  have hk : Module.Finite ℤ f.ker := Module.Finite.equiv (sUnitValuation_ker F S).symm
  have he : Module.finrank ℤ f.ker = Fintype.card (InfinitePlace F) - 1 :=
    (sUnitValuation_ker F S).finrank_eq.trans (NumberField.Units.finrank_eq F)
  have hr := f.rank_range_add_rank_ker
  replace hr := congrArg Cardinal.toNat hr
  rw [Cardinal.toNat_add (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _)] at hr
  change Module.finrank ℤ (LinearMap.range (sUnitValuation F S)) + Module.finrank ℤ f.ker =
    Module.finrank ℤ (Additive (sIntegerRing F S)ˣ) at hr
  rw [sUnitValuation_range_finrank, he] at hr
  have hp : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

/-- The norm-one S-class group, the maximal free S-unit quotient, and the S-class number. -/
theorem sClass_arithmetic_finiteness (S : Finset (Place F)) :
    CompactSpace (sNormOneClass F S) ∧ T2Space (sNormOneClass F S) ∧
      Monoid.FG (sIntegerRing F S)ˣ ∧ Finite (SPicardGroup F S) ∧
      Nonempty ((Additive (sIntegerRing F S)ˣ ⧸ Submodule.torsion ℤ (Additive (sIntegerRing F S)ˣ)) ≃ₗ[ℤ]
        (Fin (Fintype.card (InfinitePlace F) + S.card - 1) →₀ ℤ)) := by
  letI := sUnits_finite F S
  let M := Additive (sIntegerRing F S)ˣ
  obtain ⟨hc, ht⟩ := sNormOneClass_compact_hausdorff F S
  refine ⟨hc, ht, ?_, sIdeleClass_finiteCokernel F S, ?_⟩
  · rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
    infer_instance
  · let Q := M ⧸ Submodule.torsion ℤ M
    let b := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Q)
    have hq : Module.finrank ℤ Q = Module.finrank ℤ M :=
      finrank_quotient_eq_of_le_torsion le_rfl
    have hn : b.1 = Fintype.card (InfinitePlace F) + S.card - 1 := by
      rw [← sUnits_finrank, ← hq, Module.finrank_eq_card_basis b.2, Fintype.card_fin]
    exact ⟨b.2.repr.trans (Finsupp.domLCongr (finCongr hn))⟩

end

end Masullo
