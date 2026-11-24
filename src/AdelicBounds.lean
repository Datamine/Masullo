import AdelicTheta
import RestrictedProducts
import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.Valued.LocallyCompact

open Filter Function IsDedekindDomain NumberField Set
open scoped NumberField RestrictedProduct Classical SchwartzMap

noncomputable section

namespace Masullo

variable {F : Type*} [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

/-- Lemma A.1.1.2(5). A box in a cofinite restricted product is open when
only finitely many factors use arbitrary open sets. -/
theorem restrictedProduct_open_box {ι : Type*} {R : ι → Type*}
    [∀ i, TopologicalSpace (R i)] (B U : ∀ i, Set (R i)) (S : Finset ι)
    (hB : ∀ i, IsOpen (B i)) (hU : ∀ i ∈ S, IsOpen (U i)) :
    IsOpen {x : Πʳ i, [R i, B i] |
      (∀ i ∉ S, x.1 i ∈ B i) ∧ (∀ i ∈ S, x.1 i ∈ U i)} :=
  restrictedProductBoxOpen B U S (fun i _ => hB i) hU

private def integralOutside (S : Finset (Place (F := F))) : Set (FinAdeles (F := F)) :=
  {a | ∀ v ∉ S, a v ∈ v.adicCompletionIntegers F}

private theorem integralOutside_open (S : Finset (Place (F := F))) :
    IsOpen (integralOutside S) := by
  change IsOpen {a : Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F] |
    ∀ v, v ∉ S → a.1 v ∈ v.adicCompletionIntegers F}
  exact RestrictedProduct.isOpen_forall_imp_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- A compact set of finite adeles is integral outside a single finite set of
places. The finite exceptional set is uniform over the compact set. -/
theorem compact_finiteAdeles_integralOutside {K : Set (FinAdeles (F := F))} (hK : IsCompact K) :
    ∃ S : Finset (Place (F := F)), ∀ a ∈ K, ∀ v ∉ S, a v ∈ v.adicCompletionIntegers F :=
  compact_restrictedProduct_one_stage _ (fun _ => Valued.isOpen_valuationSubring _) hK

private theorem integral_iff_norm_le_one (v : Place (F := F)) (x : v.adicCompletion F) :
    x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff (val := inferInstance)).symm

private theorem diagonal_integer_integral (d : 𝓞 F) (v : Place (F := F)) :
    ((algebraMap F (FinAdeles (F := F)) (algebraMap (𝓞 F) F d)) v) ∈
      v.adicCompletionIntegers F := by
  rw [integral_iff_norm_le_one]
  exact FinitePlace.norm_le_one F v d

private theorem continuous_finite_coordinate (v : Place (F := F)) :
    Continuous (fun a : FinAdeles (F := F) => a v) :=
  RestrictedProduct.continuous_eval v

private theorem clear_one_place {K : Set (FinAdeles (F := F))} (hK : IsCompact K)
    (v : Place (F := F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K,
      ((algebraMap F (FinAdeles (F := F)) (algebraMap (𝓞 F) F d)) v) * a v ∈
        v.adicCompletionIntegers F := by
  obtain ⟨a, ha, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    ((hK.image (continuous_finite_coordinate v)).isBounded)
  let R := max M 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hlt : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 :=
    (FinitePlace.norm_lt_one_iff_mem F v a).mpr ha
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hR) hlt
  refine ⟨a ^ m, pow_ne_zero _ ha₀, fun b hb => ?_⟩
  rw [integral_iff_norm_le_one]
  have hbR : ‖b v‖ ≤ R := (hM _ ⟨b, hb, rfl⟩).trans (le_max_left _ _)
  change ‖FinitePlace.embedding v (algebraMap (𝓞 F) F (a ^ m)) * b v‖ ≤ 1
  rw [map_pow, map_pow, norm_mul, norm_pow]
  calc
    _ ≤ ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ ^ m * R :=
      mul_le_mul_of_nonneg_left hbR (by positivity)
    _ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_right hm.le hR.le
    _ = 1 := inv_mul_cancel₀ hR.ne'

/-- One nonzero integer of the number field clears all finite denominators
on a compact set. Multiplying by another integer preserves integrality. -/
theorem compact_finiteAdeles_common_denominator {K : Set (FinAdeles (F := F))} (hK : IsCompact K) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K, ∀ v : Place (F := F),
      ((algebraMap F (FinAdeles (F := F)) (algebraMap (𝓞 F) F d)) v) * a v ∈
        v.adicCompletionIntegers F := by
  classical
  obtain ⟨S, hS⟩ := compact_finiteAdeles_integralOutside hK
  have hclear (T : Finset (Place (F := F))) :
      ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K, ∀ v ∈ T,
        ((algebraMap F (FinAdeles (F := F)) (algebraMap (𝓞 F) F d)) v) * a v ∈
          v.adicCompletionIntegers F := by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert v T hv ih =>
      obtain ⟨d, hd, hT⟩ := ih
      obtain ⟨e, he, hE⟩ := clear_one_place hK v
      refine ⟨d * e, mul_ne_zero hd he, fun a ha w hw => ?_⟩
      change (FinitePlace.embedding w (algebraMap (𝓞 F) F (d * e))) * a w ∈ _
      rw [map_mul, map_mul]
      rcases Finset.mem_insert.mp hw with rfl | hwT
      · rw [mul_assoc]
        exact mul_mem (diagonal_integer_integral d w) (hE a ha)
      · rw [mul_comm (FinitePlace.embedding w (algebraMap (𝓞 F) F d)), mul_assoc]
        exact mul_mem (diagonal_integer_integral e w) (hT a ha w hwT)
  obtain ⟨d, hd, hdS⟩ := hclear S
  refine ⟨d, hd, fun a ha v => ?_⟩
  by_cases hv : v ∈ S
  · exact hdS a ha v hv
  · exact mul_mem (diagonal_integer_integral d v) (hS a ha v hv)

/-- For a diagonal element, integrality at every finite place is equivalent
to being a global algebraic integer. -/
theorem diagonal_finiteAdeles_integral_iff (x : F) :
    (∀ v : Place (F := F),
      (algebraMap F (FinAdeles (F := F)) x) v ∈ v.adicCompletionIntegers F) ↔
      x ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h v)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x]
    exact hv
  · rintro ⟨d, rfl⟩
    exact diagonal_integer_integral d

private theorem adic_integer_value (v : Place (F := F)) (m : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m)) =
      v.intValuation m := by
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F m)).trans
    (v.valuation_of_algebraMap m)

private theorem local_integer_approximation (v : Place (F := F))
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) (d : 𝓞 F) (hd : d ≠ 0) :
    ∃ m : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m)) ≤
      v.intValuation d := by
  let L := v.adicCompletion F
  let j : F →+* L := algebraMap F L
  let D := j (algebraMap (𝓞 F) F d)
  have hdv : Valued.v D = v.intValuation d := adic_integer_value v d
  have hD : D ≠ 0 := fun h => (v.intValuation_ne_zero d hd) (by rw [← hdv, h, map_zero])
  obtain ⟨q, hq⟩ := Metric.denseRange_iff.mp (v.denseRange_algebraMap (K := F)) x ‖D‖
    (norm_pos_iff.mpr hD)
  change dist x (j q) < ‖D‖ at hq
  rw [dist_eq_norm, Valued.toNormedField.norm_lt_iff (val := inferInstance), hdv] at hq
  have hxv : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx
  have hqv : v.valuation F q ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change Valued.v (j q) ≤ 1
    rw [show j q = x - (x - j q) by abel]
    exact (Valued.v : Valuation L _).map_sub_le hxv (hq.le.trans (v.intValuation_le_one d))
  obtain ⟨m, hm⟩ := v.exists_valuation_sub_lt_of_integer hqv
    (Units.mk0 (v.intValuation d) (v.intValuation_ne_zero d hd))
  change v.valuation F (algebraMap (𝓞 F) F m - q) < v.intValuation d at hm
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hm
  change Valued.v (j (algebraMap (𝓞 F) F m - q)) < v.intValuation d at hm
  rw [map_sub j, (Valued.v : Valuation L _).map_sub_swap] at hm
  refine ⟨m, ?_⟩
  change Valued.v (x - j (algebraMap (𝓞 F) F m)) ≤ _
  rw [show x - j (algebraMap (𝓞 F) F m) =
    (x - j q) + (j q - j (algebraMap (𝓞 F) F m)) by abel]
  exact (Valued.v : Valuation L _).map_add_le hq.le hm.le

/-- Every finite adele differs from a diagonal element by an integral adele. -/
theorem finiteAdeles_exists_integral_sub_diagonal (a : FinAdeles (F := F)) :
    ∃ q : F, ∀ v : Place (F := F),
      a v - (algebraMap F (FinAdeles (F := F)) q) v ∈ v.adicCompletionIntegers F := by
  classical
  obtain ⟨d, hd, hclear⟩ := compact_finiteAdeles_common_denominator (F := F) (isCompact_singleton (x := a))
  let j (v : Place (F := F)) := algebraMap F (v.adicCompletion F)
  let D := algebraMap (𝓞 F) F d
  have hD : D ≠ 0 := fun h => hd (IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm))
  have hvD (v : Place (F := F)) : Valued.v (j v D) = v.intValuation d := adic_integer_value v d
  let n (v : Place (F := F)) := multiplicity v.asIdeal (Ideal.span ({d} : Set (𝓞 F)))
  have hvn (v : Place (F := F)) : v.intValuation d = WithZero.exp (-(n v : ℤ)) :=
    v.intValuation_eq_exp_neg_multiplicity hd
  let ainv := algebraMap F (FinAdeles (F := F)) D⁻¹
  have hfinite : {v : Place (F := F) | ¬ ainv v ∈ v.adicCompletionIntegers F}.Finite :=
    eventually_cofinite.mp ainv.2
  let S := hfinite.toFinset
  have hS (v : Place (F := F)) : v ∈ S ↔ v.intValuation d < 1 := by
    change v ∈ hfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    change (¬ (j v D⁻¹) ∈ v.adicCompletionIntegers F) ↔ _
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hvD, not_le,
      one_lt_inv₀ (pos_iff_ne_zero.mpr (v.intValuation_ne_zero d hd))]
  have hx (v : Place (F := F)) : j v D * a v ∈ v.adicCompletionIntegers F :=
    hclear a (mem_singleton _) v
  choose m hm using fun v : S => local_integer_approximation v.1 _ (hx v.1) d hd
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := S) (fun v => v.asIdeal) n (fun v _ => v.prime)
    (fun v _ w _ h => mt HeightOneSpectrum.ext h) m
  refine ⟨algebraMap (𝓞 F) F b / D, fun v => ?_⟩
  have hv₀ : 0 < v.intValuation d := pos_iff_ne_zero.mpr (v.intValuation_ne_zero d hd)
  have happrox : Valued.v (j v D * a v - j v (algebraMap (𝓞 F) F b)) ≤ v.intValuation d := by
    by_cases hv : v ∈ S
    · have hbv : v.intValuation (b - m ⟨v, hv⟩) ≤ v.intValuation d := by
        rw [hvn v, v.intValuation_le_pow_iff_mem]
        exact hb v hv
      rw [← adic_integer_value v, map_sub, map_sub,
        (Valued.v : Valuation (v.adicCompletion F) _).map_sub_swap] at hbv
      rw [show j v D * a v - j v (algebraMap (𝓞 F) F b) =
        (j v D * a v - j v (algebraMap (𝓞 F) F (m ⟨v, hv⟩))) +
          (j v (algebraMap (𝓞 F) F (m ⟨v, hv⟩)) - j v (algebraMap (𝓞 F) F b)) by abel]
      exact (Valued.v : Valuation (v.adicCompletion F) _).map_add_le (hm ⟨v, hv⟩) hbv
    · have heq : v.intValuation d = 1 :=
        le_antisymm (v.intValuation_le_one d) (le_of_not_gt (mt (hS v).2 hv))
      rw [heq, ← HeightOneSpectrum.mem_adicCompletionIntegers]
      exact sub_mem (hx v) (diagonal_integer_integral b v)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply]
  change Valued.v (a v - j v (algebraMap (𝓞 F) F b / D)) ≤ 1
  have hdv : j v D ≠ 0 := fun h => hD ((j v).injective (h.trans (map_zero _).symm))
  rw [map_div₀, ← mul_div_cancel_left₀ (a v) hdv, ← sub_div, map_div₀, hvD, div_le_one₀ hv₀]
  exact happrox

/-- Reduction identifies the residue field at a finite place with the
quotient of the global integers by its prime ideal. -/
def finitePlaceResidueEquiv (v : Place (F := F)) :
    ((𝓞 F) ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) := by
  let L := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let j : 𝓞 F →+* O := algebraMap (𝓞 F) O
  let r := IsLocalRing.residue O
  have hzero (b : 𝓞 F) : r (j b) = 0 ↔ b ∈ v.asIdeal := by
    rw [IsLocalRing.residue_eq_zero_iff]
    refine ((Valued.v : Valuation L _).mem_maximalIdeal_iff).trans ?_
    change Valued.v ((j b : O) : L) < 1 ↔ b ∈ v.asIdeal
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    change Valued.v (algebraMap F L (algebraMap (𝓞 F) F b)) < 1 ↔ b ∈ v.asIdeal
    rw [adic_integer_value v b, v.intValuation_lt_one_iff_mem]
  let rbar := Ideal.Quotient.lift v.asIdeal (r.comp j) (fun b hb => (hzero b).mpr hb)
  have hr : Function.Surjective rbar := by
    intro c
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
    obtain ⟨d, hd, hd₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    obtain ⟨m, hm⟩ := local_integer_approximation v (x : L) x.property d hd₀
    refine ⟨Ideal.Quotient.mk _ m, ?_⟩
    change r (j m) = r x
    rw [← sub_eq_zero, ← map_sub]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply ((Valued.v : Valuation L _).mem_maximalIdeal_iff).mpr
    change Valued.v (((j m : O) : L) - (x : L)) < 1
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      (Valued.v : Valuation L _).map_sub_swap]
    exact hm.trans_lt ((v.intValuation_lt_one_iff_mem d).mpr hd)
  have hinj : Injective rbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hzero b).mp hx)
  exact RingEquiv.ofBijective rbar ⟨hinj, hr⟩

theorem finitePlaceResidue_card (v : Place (F := F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal :=
  (Nat.card_congr (finitePlaceResidueEquiv v).toEquiv).symm

theorem compactSpace_adicIntegers (v : Place (F := F)) :
    CompactSpace (v.adicCompletionIntegers F) := by
  let L := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  letI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Finite (IsLocalRing.ResidueField O) := Finite.of_equiv _ (finitePlaceResidueEquiv v).toEquiv
  have hclosed : IsClosed (O : Set L) := Valued.isClosed_valuationSubring L
  letI : CompleteSpace O := hclosed.completeSpace_coe
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨inferInstanceAs (CompleteSpace O), inferInstanceAs (IsDiscreteValuationRing O),
      inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩

private theorem integralFiniteAdeles_compact : IsCompact (integralOutside (F := F) ∅) := by
  let A (v : Place (F := F)) := v.adicCompletionIntegers F
  let i : (∀ v, A v) → FinAdeles (F := F) :=
    RestrictedProduct.inclusion _ _ le_top ∘ (RestrictedProduct.homeoTop :
      (∀ v, A v) ≃ₜ (Πʳ v, [v.adicCompletion F, A v]_[⊤]))
  letI (v : Place (F := F)) : CompactSpace (A v) := compactSpace_adicIntegers v
  have hi : Continuous i :=
    (RestrictedProduct.continuous_inclusion le_top).comp RestrictedProduct.homeoTop.continuous
  have heq : Set.range i = integralOutside (F := F) ∅ := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩ v _
      exact (b v).property
    · intro ha
      refine ⟨fun v => ⟨a v, ha v (Finset.notMem_empty _)⟩, ?_⟩
      exact DFunLike.ext _ _ (fun _ => rfl)
  rw [← heq]
  exact isCompact_range hi

/-- The preferred finite adelic block is a compact open neighborhood of one. -/
theorem finiteAdeles_exists_compactClopen_one :
    ∃ S : Set (FinAdeles (F := F)), IsCompact S ∧ IsClopen S ∧ (1 : FinAdeles (F := F)) ∈ S := by
  letI : T2Space (FinAdeles (F := F)) :=
    inferInstanceAs (T2Space (Πʳ v : Place (F := F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  refine ⟨integralOutside ∅, integralFiniteAdeles_compact,
    ⟨integralFiniteAdeles_compact.isClosed, integralOutside_open ∅⟩, ?_⟩
  intro v _
  exact one_mem _

/-- The finite integral block as a multiplicative submonoid of the
finite adele ring. -/
def finiteIntegralSubmonoid (F : Type*) [Field F] [NumberField F] :
    Submonoid (FiniteAdeleRing (𝓞 F) F) where
  carrier := integralOutside (F := F) ∅
  one_mem' := fun _ _ => one_mem _
  mul_mem' hf hg v hv := mul_mem (hf v hv) (hg v hv)

theorem finiteIntegralUnits_compact :
    IsCompact ((finiteIntegralSubmonoid F).units : Set (FinAdeles (F := F))ˣ) := by
  letI : T2Space (FinAdeles (F := F)) :=
    inferInstanceAs (T2Space (Πʳ v : Place (F := F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  exact Submonoid.units_isCompact (S := finiteIntegralSubmonoid F)
    (integralFiniteAdeles_compact (F := F))

theorem finiteAdeles_locallyCompact : LocallyCompactSpace (FinAdeles (F := F)) := by
  letI : Fact (∀ v : Place (F := F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
  letI (v : Place (F := F)) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicIntegers v
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : Place (F := F), [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem ideles_locallyCompact : LocallyCompactSpace (Idele F) := by
  letI : LocallyCompactSpace (FinAdeles (F := F)) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FinAdeles (F := F)))
  letI : T1Space (FinAdeles (F := F)) :=
    inferInstanceAs (T1Space (Πʳ v : Place (F := F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  letI : T1Space (InfiniteAdeleRing F) := inferInstanceAs (T1Space ((v : InfinitePlace F) → v.Completion))
  letI : T1Space (Adeles F) := inferInstanceAs (T1Space (InfiniteAdeleRing F × FinAdeles (F := F)))
  infer_instance

private abbrev localUnitSubgroup (v : Place (F := F)) : Subgroup (v.adicCompletion F)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers F)).units

/-- The restricted product of the multiplicative groups of the finite completions. -/
abbrev FiniteIdeleRestricted :=
  Πʳ v : Place (F := F), [(v.adicCompletion F)ˣ, localUnitSubgroup v]

private theorem isOpen_localUnitSubgroup (v : Place (F := F)) :
    IsOpen (localUnitSubgroup v : Set (v.adicCompletion F)ˣ) := by
  have h := Valued.isOpen_valuationSubring (v.adicCompletion F)
  exact (h.preimage Units.continuous_val).inter (h.preimage Units.continuous_coe_inv)

/-- The coordinatewise units equivalence has the restricted-product topology. -/
def finiteIdelesHomeomorph : (FinAdeles (F := F))ˣ ≃ₜ FiniteIdeleRestricted (F := F) := by
  let e : (FinAdeles (F := F))ˣ ≃* FiniteIdeleRestricted (F := F) :=
    RestrictedProduct.unitsEquiv (fun (v : Place (F := F)) => v.adicCompletion F)
  letI : Fact (∀ v : Place (F := F), IsOpen (localUnitSubgroup v : Set (v.adicCompletion F)ˣ)) :=
    ⟨isOpen_localUnitSubgroup⟩
  refine ⟨e.toEquiv, ?_, ?_⟩
  · apply continuous_of_continuousAt_one e
    let I := integralOutside (F := F) ∅
    let U : Set (FinAdeles (F := F))ˣ := Units.val ⁻¹' I ∩ (fun x => x.inv) ⁻¹' I
    have hI : IsOpen I := integralOutside_open ∅
    have hU : IsOpen U :=
      (hI.preimage Units.continuous_val).inter (hI.preimage Units.continuous_coe_inv)
    have h1 : (1 : (FinAdeles (F := F))ˣ) ∈ U :=
      ⟨fun _ _ => one_mem _, fun _ _ => one_mem _⟩
    let lift (u : U) : Πʳ v : Place (F := F), [(v.adicCompletion F)ˣ, localUnitSubgroup v]_[⊤] :=
      ⟨fun v => e u.val v, fun v => ⟨u.property.1 v (Finset.notMem_empty _),
        u.property.2 v (Finset.notMem_empty _)⟩⟩
    have hlift : Continuous lift := RestrictedProduct.continuous_rng_of_top.mpr (continuous_pi fun v => by
      let ev : (FinAdeles (F := F)) →* v.adicCompletion F :=
        (RestrictedProduct.evalRingHom (fun (v : Place (F := F)) => v.adicCompletion F)
          (B := fun v => v.adicCompletionIntegers F) v).toMonoidHom
      have hev : Continuous ev := continuous_finite_coordinate v
      exact (hev.units_map ev).comp continuous_subtype_val)
    have hc : Continuous fun u : U => e u.val :=
      (RestrictedProduct.continuous_inclusion (le_top : cofinite ≤ ⊤)).comp hlift
    exact ((continuousWithinAt_iff_continuousAt_domRestrict e h1).mpr hc.continuousAt).continuousAt
      (hU.mem_nhds h1)
  · apply Units.continuous_iff.mpr
    let j (v : Place (F := F)) := v.adicCompletion F
    have hid : Tendsto (id : Place (F := F) → Place (F := F)) cofinite cofinite := tendsto_id
    have hvalmem : ∀ᶠ v : Place (F := F) in cofinite,
        MapsTo (fun x : (j v)ˣ => x.val) (localUnitSubgroup v : Set (j v)ˣ)
          (v.adicCompletionIntegers F : Set (j v)) :=
      Filter.Eventually.of_forall fun _ _ hi => hi.1
    have hinvmem : ∀ᶠ v : Place (F := F) in cofinite,
        MapsTo (fun x : (j v)ˣ => x.inv) (localUnitSubgroup v : Set (j v)ˣ)
          (v.adicCompletionIntegers F : Set (j v)) :=
      Filter.Eventually.of_forall fun _ _ hi => hi.2
    have hval := RestrictedProduct.mapAlong_continuous (R₁ := fun v : Place (F := F) => (j v)ˣ)
      (A₁ := fun v => (localUnitSubgroup v : Set (j v)ˣ))
      (A₂ := fun v => (v.adicCompletionIntegers F : Set (j v)))
      (R₂ := j) id hid (fun v => @Units.val (j v) _) hvalmem (fun _ => Units.continuous_val)
    have hinv := RestrictedProduct.mapAlong_continuous (R₁ := fun v : Place (F := F) => (j v)ˣ)
      (A₁ := fun v => (localUnitSubgroup v : Set (j v)ˣ))
      (A₂ := fun v => (v.adicCompletionIntegers F : Set (j v)))
      (R₂ := j) id hid (fun _ x => x.inv) hinvmem (fun _ => Units.continuous_coe_inv)
    exact ⟨hval, hinv⟩

/-- The restricted-product description of the full idele group in Lemma A.1.3.3.
The archimedean factors are an ordinary finite product. -/
def idelesRestrictedHomeomorph : Idele F ≃ₜ
    ((v : InfinitePlace F) → v.Completionˣ) × FiniteIdeleRestricted (F := F) :=
  Homeomorph.prodUnits.trans
    (ContinuousMulEquiv.piUnits.toHomeomorph.prodCongr finiteIdelesHomeomorph)

theorem idelesRestrictedHomeomorph_mul (a b : Idele F) :
    idelesRestrictedHomeomorph (a * b) = idelesRestrictedHomeomorph a * idelesRestrictedHomeomorph b :=
  rfl

theorem ideles_hausdorff : T2Space (Idele F) := by
  letI : T2Space (FinAdeles (F := F)) :=
    inferInstanceAs (T2Space (Πʳ v : Place (F := F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  letI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI : T2Space (Adeles F) := inferInstanceAs (T2Space (InfiniteAdeleRing F × FinAdeles (F := F)))
  infer_instance

/-- The common-denominator estimate also applies simultaneously to a compact
family of ideles and a compact finite-place support. This is the finite-place
reduction in the proof of Lemma 2.2.2.1. -/
theorem compact_idele_support_common_denominator
    {G : Set (Idele F)} (hG : IsCompact G)
    {K : Set (FinAdeles (F := F))} (hK : IsCompact K) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ g ∈ G, ∀ ξ : Fˣ,
      ((principalIdele F ξ * g).val.2) ∈ K →
        (algebraMap (𝓞 F) F d * (ξ : F)) ∈ (algebraMap (𝓞 F) F).range := by
  let S := (fun p : FinAdeles (F := F) × Idele F => p.1 * p.2.inv.2) '' (K ×ˢ G)
  have hi : Continuous (fun a : Idele F => a.inv.2) :=
    continuous_snd.comp Units.continuous_coe_inv
  have hS : IsCompact S := (hK.prod hG).image (continuous_fst.mul (hi.comp continuous_snd))
  obtain ⟨d, hd, hclear⟩ := compact_finiteAdeles_common_denominator hS
  refine ⟨d, hd, fun g hg ξ hξ => (diagonal_finiteAdeles_integral_iff _).mp ?_⟩
  have hdiag : (algebraMap F (FinAdeles (F := F)) (ξ : F)) ∈ S := by
    refine ⟨((principalIdele F ξ * g).val.2, g), ⟨hξ, hg⟩, ?_⟩
    have hinv : g.val.2 * g.inv.2 = 1 := congrArg Prod.snd g.val_inv
    change ((algebraMap F (FinAdeles (F := F)) (ξ : F)) * g.val.2) * g.inv.2 = _
    rw [mul_assoc, hinv, mul_one]
  intro v
  rw [map_mul]
  exact hclear _ hdiag v

/-- A compact family of additive shifts can be included in the finite-place
support reduction for Lemma 2.2.2.1. -/
theorem compact_idele_shifted_support_common_denominator
    {P : Set (Idele F × Adeles F)} (hP : IsCompact P)
    {K : Set (FinAdeles (F := F))} (hK : IsCompact K) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ p ∈ P, ∀ ξ : F,
      (p.1.val * (algebraMap F (Adeles F) ξ + p.2)).2 ∈ K →
        (algebraMap (𝓞 F) F d * ξ) ∈ (algebraMap (𝓞 F) F).range := by
  let S := (fun w : FinAdeles (F := F) × (Idele F × Adeles F) =>
    w.1 * w.2.1.inv.2 - w.2.2.2) '' (K ×ˢ P)
  have hi : Continuous (fun g : Idele F => g.inv.2) :=
    continuous_snd.comp Units.continuous_coe_inv
  have hS : IsCompact S := (hK.prod hP).image
    ((continuous_fst.mul (hi.comp (continuous_fst.comp continuous_snd))).sub
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨d, hd, hclear⟩ := compact_finiteAdeles_common_denominator hS
  refine ⟨d, hd, fun p hp ξ hξ => (diagonal_finiteAdeles_integral_iff _).mp ?_⟩
  have hdiag : algebraMap F (FinAdeles (F := F)) ξ ∈ S := by
    refine ⟨((p.1.val * (algebraMap F (Adeles F) ξ + p.2)).2, p), ⟨hξ, hp⟩, ?_⟩
    have hinv : p.1.val.2 * p.1.inv.2 = 1 := congrArg Prod.snd p.1.val_inv
    change p.1.val.2 * (algebraMap F (FinAdeles (F := F)) ξ + p.2.2) * p.1.inv.2 -
      p.2.2 = _
    rw [mul_right_comm, hinv, one_mul, add_sub_cancel_right]
  intro v
  rw [map_mul]
  exact hclear _ hdiag v

private abbrev Mixed := mixedEmbedding.mixedSpace F

/-- The archimedean projection of the adeles in mixed real and complex coordinates. -/
def mixedArch : Adeles F →+* Mixed (F := F) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp {
    toFun := fun a : Adeles F => a.1
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

theorem mixedArch_on_diagonal (a : F) :
    mixedArch (algebraMap F (Adeles F) a) = mixedEmbedding F a :=
  (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := a)).symm

/-- The signed archimedean cube times the integral finite adeles. -/
def signedAdelicDomain : Set (Adeles F) :=
  {a | mixedArch a ∈ signedMixedDomain F ∧ ∀ v, a.2 v ∈ v.adicCompletionIntegers F}

/-- Every adelic class has a unique representative in the corrected domain of
Definition A.2.1.1. This also proves the covering assertion in Lemma A.2.1.2(1). -/
theorem signedAdelicDomain_existsUnique (a : Adeles F) :
    ∃! q : F, a - algebraMap F (Adeles F) q ∈ signedAdelicDomain := by
  classical
  let j := algebraMap F (Adeles F)
  obtain ⟨q, hq⟩ := finiteAdeles_exists_integral_sub_diagonal a.2
  let x := mixedArch (a - j q)
  obtain ⟨u, hu, hunique⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    (mixedEmbedding.latticeBasis F) x
  have hul : (u : Mixed (F := F)) ∈ mixedEmbedding.integerLattice F :=
    (mixedEmbedding.mem_span_latticeBasis F).mp u.property
  obtain ⟨z, hz⟩ := hul
  change mixedEmbedding F (algebraMap (𝓞 F) F z) = (u : Mixed (F := F)) at hz
  let r := q - algebraMap (𝓞 F) F z
  have har : a - j r = (a - j q) + j (algebraMap (𝓞 F) F z) := by
    dsimp [r]
    rw [map_sub]
    abel
  have hr : a - j r ∈ signedAdelicDomain := by
    refine ⟨?_, ?_⟩
    · rw [har, map_add, mixedArch_on_diagonal, hz, add_comm]
      exact hu
    · intro v
      rw [har]
      exact add_mem (hq v) (diagonal_integer_integral z v)
  refine ⟨r, hr, fun p hp => ?_⟩
  have hdiff : j (q - p) = (a - j p) - (a - j q) := by rw [map_sub]; abel
  obtain ⟨t, ht⟩ := (diagonal_finiteAdeles_integral_iff (q - p)).mp (fun v => by
    change (j (q - p)).2 v ∈ v.adicCompletionIntegers F
    rw [hdiff]
    exact sub_mem (hp.2 v) (hq v))
  let w : Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) :=
    ⟨mixedEmbedding F (q - p), (mixedEmbedding.mem_span_latticeBasis F).mpr
      ⟨t, congrArg (mixedEmbedding F) ht⟩⟩
  have hw : w +ᵥ x ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) := by
    change mixedEmbedding F (q - p) + mixedArch (a - j q) ∈ signedMixedDomain F
    rw [← mixedArch_on_diagonal, ← map_add, hdiff, sub_add_cancel]
    exact hp.1
  have heq := congrArg Subtype.val (hunique w hw)
  change mixedEmbedding F (q - p) = (u : Mixed (F := F)) at heq
  have hqp := (mixedEmbedding_injective F) (heq.trans hz.symm)
  dsimp [r]
  rw [← hqp, sub_sub_cancel]

omit [NumberField F] in
private theorem mixedToInfiniteAdele_continuous :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  classical
  change Continuous (fun z : Mixed (F := F) => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z)
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hv
    have he (z : Mixed (F := F)) : ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) v =
        e.symm (z.1 ⟨v, hv⟩) := by
      apply e.injective
      rw [e.apply_symm_apply]
      have heq := congrArg (fun y : Mixed (F := F) => y.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z)
      exact heq
    simp_rw [he]
    exact e.symm.continuous.comp ((continuous_apply
      (⟨v, hv⟩ : {w : InfinitePlace F // InfinitePlace.IsReal w})).comp continuous_fst)
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have he (z : Mixed (F := F)) : ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) v =
        e.symm (z.2 ⟨v, hc⟩) := by
      apply e.injective
      rw [e.apply_symm_apply]
      have heq := congrArg (fun y : Mixed (F := F) => y.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z)
      exact heq
    simp_rw [he]
    exact e.symm.continuous.comp ((continuous_apply
      (⟨v, hc⟩ : {w : InfinitePlace F // InfinitePlace.IsComplex w})).comp continuous_snd)

/-- The corrected adelic fundamental domain has compact closure. -/
theorem signedAdelicDomain_isCompact_closure :
    IsCompact (closure (signedAdelicDomain (F := F))) := by
  letI : T2Space (FinAdeles (F := F)) :=
    inferInstanceAs (T2Space (Πʳ v : Place (F := F), [v.adicCompletion F, v.adicCompletionIntegers F]))
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI : T2Space (Adeles F) := inferInstanceAs (T2Space (InfiniteAdeleRing F × FinAdeles (F := F)))
  have hArch : IsCompact (closure (signedMixedDomain F)) :=
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).isCompact_closure
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hbox : IsCompact ((e.symm '' closure (signedMixedDomain F)) ×ˢ integralOutside ∅) :=
    (hArch.image (mixedToInfiniteAdele_continuous (F := F))).prod
      (integralFiniteAdeles_compact (F := F))
  refine hbox.of_isClosed_subset isClosed_closure (closure_minimal ?_ hbox.isClosed)
  intro a ha
  exact ⟨⟨e a.1, subset_closure ha.1, e.symm_apply_apply a.1⟩, fun v _ => ha.2 v⟩

private def mixedUnitMul (u : (Mixed (F := F))ˣ) :
    Mixed (F := F) ≃L[ℝ] Mixed (F := F) :=
  let e : Mixed (F := F) ≃ₗ[ℝ] Mixed (F := F) :=
    { toFun := fun x => u.val * x
      invFun := fun x => u.inv * x
      left_inv := fun x => by
        change u.inv * (u.val * x) = x
        rw [← mul_assoc, u.inv_val, one_mul]
      right_inv := fun x => by
        change u.val * (u.inv * x) = x
        rw [← mul_assoc, u.val_inv, one_mul]
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  e.toContinuousLinearEquiv

theorem norm_finiteBruhat_bounded (ψ : FiniteBruhat F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a, ‖ψ.toLocallyConstant a‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    ((ψ.compactSupport.image ψ.toLocallyConstant.continuous).isBounded)
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : ψ.toLocallyConstant y = 0
  · simp [hy]
  · exact (hM (ψ.toLocallyConstant y) ⟨y, subset_closure hy, rfl⟩).trans (le_max_left _ _)

/-- The shifted summand in (2.2.2.1). -/
def shiftedThetaSummand (f : Adeles F → ℂ) (ξ : Fˣ) (p : Idele F × Adeles F) : ℂ :=
  f (p.1.val * (algebraMap F (Adeles F) (ξ : F) + p.2))

@[simp] theorem shiftedThetaSummand_zero (f : Adeles F → ℂ) (ξ : Fˣ) (g : Idele F) :
    shiftedThetaSummand f ξ (g, 0) = thetaSummand F f g ξ := by
  simp only [shiftedThetaSummand, thetaSummand, add_zero]
  congr 1
  exact mul_comm _ _

set_option maxHeartbeats 2000000 in
/-- The finite-place denominator and a uniform archimedean lower bound
give one summable majorant on each compact set of ideles and shifts. -/
theorem pure_shiftedTheta_uniform (φ : 𝓢(Mixed (F := F), ℂ))
    (ψ : FiniteBruhat F) {P : Set (Idele F × Adeles F)} (hP : IsCompact P) :
    ∃ m : Fˣ → ℝ, Summable m ∧ ∀ ξ p, p ∈ P →
      ‖shiftedThetaSummand (bruhatTensor F φ ψ) ξ p‖ ≤ m ξ := by
  classical
  obtain ⟨d, hd, hclear⟩ := compact_idele_shifted_support_common_denominator hP ψ.compactSupport
  let dF := algebraMap (𝓞 F) F d
  have hdF : dF ≠ 0 := (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr hd
  let arch := mixedArch (F := F)
  have hcArch : Continuous arch :=
    (infiniteAdele_toMixed_continuous F).comp continuous_fst
  have hcI : Continuous (fun p : Idele F × Adeles F => arch p.1.inv) :=
    hcArch.comp (Units.continuous_coe_inv.comp continuous_fst)
  obtain ⟨Rg, hRg, hRgP⟩ := (hP.image hcI).isBounded.exists_pos_norm_le
  obtain ⟨Rx, hRx, hRxP⟩ :=
    (hP.image (hcArch.comp continuous_snd)).isBounded.exists_pos_norm_le
  let L := mixedEmbedding.integerLattice F
  let active : Set Fˣ := {ξ | ∃ p ∈ P, ψ.toLocallyConstant
    (p.1.val * (algebraMap F (Adeles F) (ξ : F) + p.2)).2 ≠ 0}
  have hintegral (ξ : active) : dF * (ξ.val : F) ∈ (algebraMap (𝓞 F) F).range := by
    obtain ⟨p, hp, hn⟩ := ξ.property
    exact hclear p hp ξ.val (subset_closure hn)
  let j (ξ : active) : L := ⟨mixedEmbedding F (dF * (ξ.val : F)), by
    obtain ⟨a, ha⟩ := hintegral ξ
    exact ⟨a, congrArg (mixedEmbedding F) ha⟩⟩
  have hj : Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact mul_left_cancel₀ hdF (mixedEmbedding_injective F (congrArg Subtype.val hab))
  have hj₀ (ξ : active) : 0 < ‖j ξ‖ := by
    rw [norm_pos_iff]
    intro h
    have hz : mixedEmbedding F (dF * (ξ.val : F)) = 0 := congrArg Subtype.val h
    exact (mul_ne_zero hdF ξ.val.ne_zero) (map_eq_zero_iff _ (mixedEmbedding_injective F) |>.mp hz)
  obtain ⟨M, hM, hψ⟩ := norm_finiteBruhat_bounded ψ
  let k := Module.finrank ℤ L + 1
  let A := max 1 (‖mixedEmbedding F dF‖ * (Rg + Rx))
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left ..)
  let C := SchwartzMap.seminorm ℝ k 0 φ + SchwartzMap.seminorm ℝ 0 0 φ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let weight (ξ : active) := (M * C * A ^ k) * (max 1 ‖j ξ‖)⁻¹ ^ k
  have hweight : Summable weight := by
    have hs := (ZLattice.summable_norm_pow_inv L k (Nat.lt_succ_self _)).comp_injective hj
    refine (hs.mul_left (M * C * A ^ k)).of_nonneg_of_le (fun ξ => by
      dsimp [weight]; positivity) ?_
    intro ξ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (inv_anti₀ (hj₀ ξ) (le_max_right (1 : ℝ) ‖j ξ‖)) _
  let m : Fˣ → ℝ := fun ξ => if h : ξ ∈ active then weight ⟨ξ, h⟩ else 0
  have hm : Summable m := by
    apply (summable_subtype_iff_indicator (s := active) (f := m)).mp
      (hweight.congr (fun ξ => by simp [m, ξ.property])) |>.congr
    intro ξ
    by_cases h : ξ ∈ active <;> simp [m, h]
  refine ⟨m, hm, fun ξ p hp => ?_⟩
  by_cases hξ : ξ ∈ active
  · let u := arch (p.1.val * (algebraMap F (Adeles F) (ξ : F) + p.2))
    have hu : mixedEmbedding F (ξ : F) = arch p.1.inv * u - arch p.2 := by
      dsimp [u]
      have hi : ((↑(p.1⁻¹) : Adeles F) * (p.1 : Adeles F)) = 1 := p.1.inv_val
      rw [← map_mul, ← mul_assoc, hi, one_mul, map_add, add_sub_cancel_right]
      exact (mixedArch_on_diagonal (ξ : F)).symm
    have hg := hRgP (arch p.1.inv) ⟨p, hp, rfl⟩
    have hx := hRxP (arch p.2) ⟨p, hp, rfl⟩
    have hv : ‖mixedEmbedding F (ξ : F)‖ ≤ (Rg + Rx) * max 1 ‖u‖ := by
      rw [hu]
      calc
        _ ≤ ‖arch p.1.inv * u‖ + ‖arch p.2‖ := norm_sub_le _ _
        _ ≤ Rg * max 1 ‖u‖ + Rx * max 1 ‖u‖ := add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul hg (le_max_right _ _) (norm_nonneg _) hRg.le))
          (hx.trans (le_mul_of_one_le_right hRx.le (le_max_left _ _)))
        _ = _ := (add_mul _ _ _).symm
    have hjbound : max 1 ‖j ⟨ξ, hξ⟩‖ ≤ A * max 1 ‖u‖ := by
      apply max_le
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
      · change ‖mixedEmbedding F (dF * (ξ : F))‖ ≤ _
        rw [map_mul]
        refine (norm_mul_le _ _).trans ?_
        calc
          _ ≤ ‖mixedEmbedding F dF‖ * ((Rg + Rx) * max 1 ‖u‖) :=
            mul_le_mul_of_nonneg_left hv (norm_nonneg _)
          _ = ‖mixedEmbedding F dF‖ * (Rg + Rx) * max 1 ‖u‖ := by rw [mul_assoc]
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hφ : ‖φ u‖ * (max 1 ‖u‖) ^ k ≤ C := by
      rcases le_total ‖u‖ 1 with h | h
      · rw [max_eq_left h, one_pow, mul_one]
        exact (SchwartzMap.norm_le_seminorm ℝ φ u).trans
          (le_add_of_nonneg_left (apply_nonneg _ _))
      · rw [max_eq_right h, mul_comm]
        exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ φ k u).trans
          (le_add_of_nonneg_right (apply_nonneg _ _))
    have hfactor : ‖φ u‖ * (max 1 ‖j ⟨ξ, hξ⟩‖) ^ k ≤ C * A ^ k := by
      calc
        _ ≤ ‖φ u‖ * (A * max 1 ‖u‖) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjbound _) (norm_nonneg _)
        _ = (‖φ u‖ * (max 1 ‖u‖) ^ k) * A ^ k := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hφ (by positivity)
    change ‖φ u * ψ.toLocallyConstant _‖ ≤ m ξ
    rw [norm_mul, show m ξ = weight ⟨ξ, hξ⟩ by simp [m, hξ]]
    dsimp only [weight]
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = ‖ψ.toLocallyConstant _‖ * (‖φ u‖ * (max 1 ‖j ⟨ξ, hξ⟩‖) ^ k) := by ring
      _ ≤ M * (C * A ^ k) := mul_le_mul (hψ _) hfactor (by positivity) hM
      _ = _ := by ring
  · have hz : ψ.toLocallyConstant (p.1.val * (algebraMap F (Adeles F) (ξ : F) + p.2)).2 = 0 := by
      by_contra hn
      exact hξ ⟨p, hp, hn⟩
    simp [shiftedThetaSummand, bruhatTensor, hz, m, hξ]

theorem bruhat_shiftedTheta_majorant {f : Adeles F → ℂ}
    (hf : f ∈ bruhatSubmodule F) {P : Set (Idele F × Adeles F)} (hP : IsCompact P) :
    ∃ m : Fˣ → ℝ, Summable m ∧ ∀ ξ p, p ∈ P → ‖shiftedThetaSummand f ξ p‖ ≤ m ξ := by
  apply Submodule.span_induction (p := fun f _ =>
    ∃ m : Fˣ → ℝ, Summable m ∧ ∀ ξ p, p ∈ P → ‖shiftedThetaSummand f ξ p‖ ≤ m ξ) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩
    exact pure_shiftedTheta_uniform φ ψ hP
  · exact ⟨0, summable_zero, fun ξ p hp => by simp [shiftedThetaSummand]⟩
  · rintro f g _ _ ⟨m, hm, hfm⟩ ⟨n, hn, hgn⟩
    refine ⟨fun ξ => m ξ + n ξ, hm.add hn, fun ξ p hp => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hfm ξ p hp) (hgn ξ p hp))
  · rintro c f _ ⟨m, hm, hfm⟩
    refine ⟨fun ξ => ‖c‖ * m ξ, hm.mul_left ‖c‖, fun ξ p hp => ?_⟩
    change ‖c * shiftedThetaSummand f ξ p‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hfm ξ p hp) (norm_nonneg _)

/-- Uniform absolute convergence of the shifted theta sum on compact sets,
as asserted in Lemma 2.2.2.1. -/
theorem bruhat_shiftedTheta_norm_uniform {f : Adeles F → ℂ}
    (hf : f ∈ bruhatSubmodule F) {P : Set (Idele F × Adeles F)} (hP : IsCompact P) :
    HasSumUniformlyOn (fun ξ p => ‖shiftedThetaSummand f ξ p‖)
      (fun p => ∑' ξ, ‖shiftedThetaSummand f ξ p‖) P := by
  obtain ⟨m, hm, h⟩ := bruhat_shiftedTheta_majorant hf hP
  apply HasSumUniformlyOn.of_norm_le_summable hm
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h

/-- The shifted theta sum is continuous on ideles times adeles. -/
theorem bruhat_shiftedTheta_continuous {f : Adeles F → ℂ}
    (hf : f ∈ bruhatSubmodule F) :
    Continuous (fun p => ∑' ξ, shiftedThetaSummand f ξ p) := by
  letI : LocallyCompactSpace (FinAdeles (F := F)) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FinAdeles (F := F)))
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨P, hP, hp⟩ := exists_compact_mem_nhds p
  obtain ⟨m, hm, h⟩ := bruhat_shiftedTheta_majorant hf hP
  have hu := HasSumUniformlyOn.of_norm_le_summable hm h
  apply ContinuousOn.continuousAt _ hp
  apply (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp hu).continuousOn
  exact Frequently.of_forall fun s => (continuous_finsetSum s fun ξ _ =>
    (bruhat_continuous F hf).comp
      ((Units.continuous_val.comp continuous_fst).mul (continuous_const.add continuous_snd))).continuousOn

/-- The absolute shifted lattice sum is summable, including the zero term. -/
theorem full_shiftedTheta_norm_summable {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) (x : Adeles F) :
    Summable (fun ξ : F => ‖f (g.val * (algebraMap F (Adeles F) ξ + x))‖) := by
  let u (ξ : F) := ‖f (g.val * (algebraMap F (Adeles F) ξ + x))‖
  change Summable u
  let S : Set F := {ξ | ξ ≠ 0}
  have hs := ((bruhat_shiftedTheta_norm_uniform hf (isCompact_singleton (x := (g, x)))).hasSum
    (mem_singleton _)).summable
  have hsub : Summable (u ∘ (Subtype.val : S → F)) :=
    unitsEquivNeZero.summable_iff.mp hs
  have hsingle : HasSum (fun ξ : F => if ξ = 0 then u 0 else 0) (u 0) := by
    simpa using hasSum_single (f := fun ξ : F => if ξ = 0 then u 0 else 0)
      0 (fun ξ hξ => by simp [hξ])
  refine ((summable_subtype_iff_indicator.mp hsub).add hsingle.summable).congr fun ξ => ?_
  by_cases hξ : ξ = 0 <;> simp [S, hξ]

/-- Splitting the full shifted lattice sum into the nonzero terms and the zero term. -/
theorem full_shiftedTheta_eq {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) (x : Adeles F) :
    (∑' ξ : F, f (g.val * (algebraMap F (Adeles F) ξ + x))) =
      (∑' ξ, shiftedThetaSummand f ξ (g, x)) + f (g.val * x) := by
  let u (ξ : F) := f (g.val * (algebraMap F (Adeles F) ξ + x))
  let S : Set F := {ξ | ξ ≠ 0}
  have hu : Summable u := (full_shiftedTheta_norm_summable hf g x).of_norm
  have he : (fun ξ : F => if ξ = 0 then 0 else u ξ) = S.indicator u := by
    funext ξ
    by_cases hξ : ξ = 0 <;> simp [S, hξ]
  change (∑' ξ, u ξ) = _
  rw [hu.tsum_eq_add_tsum_ite 0, he, ← tsum_subtype, add_comm]
  congr 1
  · exact (unitsEquivNeZero.tsum_eq (u ∘ (Subtype.val : S → F))).symm
  · simp [u]

/-- The invariance clause of Lemma 2.2.2.1(1), with the term at zero included. -/
theorem bruhat_shiftedTheta_add_diagonal {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (g : Idele F) (x : Adeles F) (a : F) :
    (∑' ξ, shiftedThetaSummand f ξ (g, x + algebraMap F (Adeles F) a)) +
        f (g.val * (x + algebraMap F (Adeles F) a)) =
      (∑' ξ, shiftedThetaSummand f ξ (g, x)) + f (g.val * x) := by
  rw [← full_shiftedTheta_eq hf, ← full_shiftedTheta_eq hf]
  simpa only [Equiv.coe_addRight, map_add, add_right_comm, add_assoc] using
    (Equiv.addRight a).tsum_eq (fun ξ => f (g.val * (algebraMap F (Adeles F) ξ + x)))

/-- At zero shift this sum is the continuous, principal-invariant theta
function of Lemma 2.2.2.1(2). -/
theorem bruhat_theta_continuous_and_invariant {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Continuous (thetaOnIdeles F f) ∧
    ∀ (g : Idele F) (a : Fˣ),
      thetaOnIdeles F f (principalIdele F a * g) = thetaOnIdeles F f g := by
  refine ⟨?_, fun g a => thetaOnIdeles_principal_mul F f g a⟩
  have hc : Continuous (fun g : Idele F => ∑' ξ, shiftedThetaSummand f ξ (g, (0 : Adeles F))) :=
    (bruhat_shiftedTheta_continuous hf).comp (continuous_id.prodMk continuous_const)
  change Continuous (fun g : Idele F => ∑' ξ, thetaSummand F f g ξ)
  simpa only [shiftedThetaSummand_zero] using hc

set_option maxHeartbeats 2000000 in
/-- Corrected Lemma 2.2.2.1(3). A compact set of possible finite inverse
components gives a single fractional ideal for the bound. The archimedean
component may vary freely. A finite indicator factor satisfies the norm
hypothesis. -/
theorem pure_theta_fractionalIdeal_bound (φ : 𝓢(Mixed (F := F), ℂ)) (ψ : FiniteBruhat F)
    (hψ : ∀ y, ‖ψ.toLocallyConstant y‖ ≤ 1)
    {K : Set (FinAdeles (F := F))} (hK : IsCompact K) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F, ∀ g : Idele F, g.inv.2 ∈ K →
      let inner (ξ : {ξ : Fˣ // (ξ : F) ∈ I}) :=
        ‖φ (mixedArch g.val * mixedEmbedding F (ξ.val : F))‖
      Summable inner ∧
        (∑' ξ, ‖thetaSummand F (bruhatTensor F φ ψ) g ξ‖) ≤ ∑' ξ, inner ξ := by
  let E := FinAdeles (F := F)
  let Z := (fun p : E × E => p.1 * p.2) '' (tsupport ψ.toLocallyConstant ×ˢ K)
  have hZ : IsCompact Z := (ψ.compactSupport.prod hK).image (continuous_fst.mul continuous_snd)
  obtain ⟨d, hd, hclear⟩ := compact_finiteAdeles_common_denominator hZ
  let dF := algebraMap (𝓞 F) F d
  have hdF : dF ≠ 0 := (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr hd
  let I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F := FractionalIdeal.spanSingleton _ dF⁻¹
  have hI (ξ : F) : ξ ∈ I ↔ dF * ξ ∈ (algebraMap (𝓞 F) F).range := by
    rw [show ξ ∈ I ↔ ∃ a : 𝓞 F, a • dF⁻¹ = ξ from FractionalIdeal.mem_spanSingleton _]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [Algebra.smul_def]; field_simp⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [Algebra.smul_def, ha]
      field_simp
  refine ⟨I, fun g hg => ?_⟩
  let S : Set Fˣ := {ξ | (ξ : F) ∈ I}
  let L := mixedEmbedding.integerLattice F
  let j (ξ : S) : L := ⟨mixedEmbedding F (dF * (ξ.val : F)), by
    obtain ⟨a, ha⟩ := (hI (ξ.val : F)).mp ξ.property
    exact ⟨a, congrArg (mixedEmbedding F) ha⟩⟩
  have hj : Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact mul_left_cancel₀ hdF (mixedEmbedding_injective F (congrArg Subtype.val hab))
  let du := Units.map (mixedEmbedding F).toMonoidHom (Units.mk0 dF hdF)
  let gu := Units.map (mixedArch : Adeles F →+* Mixed (F := F)).toMonoidHom g
  let scaled := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedUnitMul (gu * du⁻¹)) φ
  have hscale (ξ : S) :
      scaled ((j ξ : L) : Mixed (F := F)) = φ (mixedArch g.val * mixedEmbedding F (ξ.val : F)) := by
    change φ ((gu.val * du.inv) * mixedEmbedding F (dF * (ξ.val : F))) = _
    congr 1
    rw [map_mul, mul_assoc]
    have hdu : du.val = mixedEmbedding F dF := rfl
    rw [← hdu, ← mul_assoc du.inv, du.inv_val, one_mul]
    rfl
  let v (ξ : Fˣ) := ‖φ (mixedArch g.val * mixedEmbedding F (ξ : F))‖
  have hs : Summable (v ∘ (Subtype.val : S → Fˣ)) := by
    refine ((schwartz_summable_on_lattice L scaled 0).comp_injective hj).congr fun ξ => ?_
    simpa only [Function.comp_apply, sub_zero] using congrArg norm (hscale ξ)
  refine ⟨hs, ?_⟩
  change _ ≤ ∑' ξ : S, v ξ.val
  rw [tsum_subtype]
  have hl := ((bruhat_shiftedTheta_norm_uniform (bruhatTensor_mem F φ ψ)
    (isCompact_singleton (x := (g, (0 : Adeles F))))).hasSum (mem_singleton _)).summable
  have hleft : Summable (fun ξ => ‖thetaSummand F (bruhatTensor F φ ψ) g ξ‖) :=
    by simpa using hl
  refine hleft.tsum_le_tsum (fun ξ => ?_) (summable_subtype_iff_indicator.mp hs)
  let y := ((principalIdele F ξ * g).val.2)
  by_cases hξ : ψ.toLocallyConstant y = 0
  · simp only [thetaSummand, bruhatTensor, show ((principalIdele F ξ * g).val.2) = y from rfl,
      hξ, mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  · have hdiag : algebraMap F E (ξ : F) ∈ Z := by
      refine ⟨(y, g.inv.2), ⟨subset_closure hξ, hg⟩, ?_⟩
      have hinv : g.val.2 * g.inv.2 = 1 := congrArg Prod.snd g.val_inv
      change (algebraMap F E (ξ : F) * g.val.2) * g.inv.2 = _
      rw [mul_assoc, hinv, mul_one]
    have hmem : ξ ∈ S := (hI (ξ : F)).mpr ((diagonal_finiteAdeles_integral_iff _).mp
      (fun v => by rw [map_mul]; exact hclear _ hdiag v))
    rw [indicator_of_mem hmem]
    have harch : mixedArch (principalIdele F ξ * g).val =
        mixedArch g.val * mixedEmbedding F (ξ : F) := by
      change mixedArch (algebraMap F (Adeles F) (ξ : F) * g.val) = _
      rw [map_mul, mixedArch_on_diagonal, mul_comm]
    change ‖φ (mixedArch (principalIdele F ξ * g).val) * ψ.toLocallyConstant y‖ ≤ v ξ
    rw [norm_mul, harch]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ y)

/-- Absolute summability of a pure tensor's theta series at a fixed idele. -/
theorem pure_theta_absolutely_summable (φ : 𝓢(Mixed (F := F), ℂ))
    (ψ : FiniteBruhat F) (g : Idele F) :
    Summable (fun ξ : Fˣ => ‖thetaSummand F (bruhatTensor F φ ψ) g ξ‖) := by
  have hu := bruhat_shiftedTheta_norm_uniform (bruhatTensor_mem F φ ψ)
    (isCompact_singleton (x := (g, (0 : Adeles F))))
  simpa only [shiftedThetaSummand_zero] using (hu.hasSum (mem_singleton _)).summable

/-- Pointwise summability for the entire algebraic Schwartz–Bruhat space. -/
theorem bruhat_theta_summable {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    thetaSummable F f := by
  apply Submodule.span_induction (p := fun f _ => thetaSummable F f) _ _ _ _ hf
  · rintro _ ⟨φ, ψ, rfl⟩ g
    exact (pure_theta_absolutely_summable φ ψ g).of_norm
  · intro g
    change Summable (fun _ : Fˣ => (0 : ℂ))
    exact summable_zero
  · intro a b _ _ ha hb g
    change Summable (fun ξ => thetaSummand F a g ξ + thetaSummand F b g ξ)
    exact (ha g).add (hb g)
  · intro c a _ ha g
    change Summable (fun ξ => c * thetaSummand F a g ξ)
    exact (ha g).mul_left c

/-- Lemma A.1.2.1(1). The diagonal additive subgroup of a number field is
discrete in the adelic topology. -/
theorem principalAdeles_discrete :
    DiscreteTopology (NumberField.AdeleRing.principalSubgroup (𝓞 F) F) := by
  let L := mixedEmbedding.integerLattice F
  obtain ⟨V, hV, hLV⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({0} : Set L))
  have hV₀ : (0 : Mixed (F := F)) ∈ V := by
    have hz : (0 : L) ∈ ({0} : Set L) := mem_singleton _
    rw [← hLV] at hz
    exact hz
  let P := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let U := {a : Adeles F | mixedArch a ∈ V ∧ a.2 ∈ integralOutside ∅}
  have hmixed : Continuous (mixedArch : Adeles F → Mixed (F := F)) :=
    (infiniteAdele_toMixed_continuous F).comp continuous_fst
  have hU : IsOpen U := (hV.preimage hmixed).inter ((integralOutside_open ∅).preimage continuous_snd)
  have heq : ((↑) : P → Adeles F) ⁻¹' U = ({0} : Set P) := by
    ext x
    constructor
    · intro hx
      rcases x.property with ⟨a, ha⟩
      have hfin : ∀ v : Place (F := F),
          (algebraMap F (FinAdeles (F := F)) a) v ∈ v.adicCompletionIntegers F := by
        intro v
        change mixedArch (x : Adeles F) ∈ V ∧ (x : Adeles F).2 ∈ integralOutside ∅ at hx
        exact (show (algebraMap F (FinAdeles (F := F)) a) v =
          (x : Adeles F).2 v from congrArg (fun t : Adeles F => t.2 v) ha).symm ▸
          hx.2 v (Finset.notMem_empty _)
      obtain ⟨b, hb⟩ := (diagonal_finiteAdeles_integral_iff a).mp hfin
      let z : L := ⟨mixedEmbedding F a, ⟨b, congrArg (mixedEmbedding F) hb⟩⟩
      have hzm : z.val ∈ V := by
        have hz0 : mixedArch (x : Adeles F) = z.val := by
          rw [← ha, mixedArch_on_diagonal]
        exact hz0 ▸ hx.1
      have hz : z = 0 := by
        have : z ∈ ((↑) : L → Mixed (F := F)) ⁻¹' V := hzm
        rw [hLV] at this
        exact mem_singleton_iff.mp this
      have he : mixedEmbedding F a = (0 : Mixed (F := F)) :=
        congrArg (fun y : L => (y : Mixed (F := F))) hz
      have ha₀ : a = 0 := mixedEmbedding_injective F (he.trans (map_zero _).symm)
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← ha, ha₀, map_zero, AddSubgroup.coe_zero]
    · rintro rfl
      exact ⟨by simpa using hV₀, fun v _ => zero_mem (v.adicCompletionIntegers F)⟩
  apply discreteTopology_of_isOpen_singleton_zero
  rw [← heq]
  exact hU.preimage continuous_subtype_val

/-- The other topological conclusion in (A.1.2.1) that follows from
discreteness alone. Compactness of the quotient also needs approximation. -/
theorem principalAdeles_closed :
    IsClosed (NumberField.AdeleRing.principalSubgroup (𝓞 F) F : Set (Adeles F)) := by
  letI : T2Space (FinAdeles (F := F)) :=
    inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI : T2Space (Adeles F) := inferInstanceAs (T2Space (InfiniteAdeleRing F × FinAdeles (F := F)))
  letI := principalAdeles_discrete (F := F)
  exact AddSubgroup.isClosed_of_discrete

/-- Only finitely many translates of the closed corrected domain meet a compact set,
as required in Lemma A.2.1.2(2). -/
theorem signedAdelicDomain_finite_translates {K : Set (Adeles F)} (hK : IsCompact K) :
    {q : F | ∃ x ∈ K, x - algebraMap F (Adeles F) q ∈ closure signedAdelicDomain}.Finite := by
  let P := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let D := closure (signedAdelicDomain (F := F))
  let C := (fun z : Adeles F × Adeles F => z.1 - z.2) '' (K ×ˢ D)
  have hC : IsCompact C := (hK.prod signedAdelicDomain_isCompact_closure).image
    (continuous_fst.sub continuous_snd)
  letI : DiscreteTopology P := principalAdeles_discrete
  have hfinite : ((↑) ⁻¹' C : Set P).Finite :=
    (principalAdeles_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hC).finite_of_discrete
  let j : F → P := fun q => ⟨algebraMap F (Adeles F) q, ⟨q, rfl⟩⟩
  have hj : Function.Injective j := fun _ _ h =>
    NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
  refine (hfinite.preimage hj.injOn).subset ?_
  rintro q ⟨x, hx, hq⟩
  exact ⟨(x, x - algebraMap F (Adeles F) q), ⟨hx, hq⟩, sub_sub_cancel _ _⟩

/-- The adelic additive quotient is compact, as in Lemma A.1.2.1(2). -/
theorem principalAdeles_quotient_compact :
    CompactSpace (Adeles F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F) := by
  let P := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let π := QuotientAddGroup.mk' P
  have h : π '' closure (signedAdelicDomain (F := F)) = univ := by
    apply eq_univ_of_forall
    intro a
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨q, hq, _⟩ := signedAdelicDomain_existsUnique x
    refine ⟨x - algebraMap F (Adeles F) q, subset_closure hq, ?_⟩
    rw [map_sub, show π (algebraMap F (Adeles F) q) = 0 from
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨q, rfl⟩, sub_zero]
    rfl
  exact ⟨h ▸ signedAdelicDomain_isCompact_closure.image continuous_quot_mk⟩

theorem principalAdeles_quotient_hausdorff :
    T2Space (Adeles F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F) := by
  letI := principalAdeles_closed (F := F)
  infer_instance

/-- The additive adelic class group is uniquely divisible, as required by A.1.2.1(3). -/
theorem principalAdeles_quotient_uniquelyDivisible (n : ℕ) (hn : n ≠ 0) :
    Bijective (fun a : Adeles F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F => n • a) := by
  let W := (Algebra.linearMap F (Adeles F)).range
  change Bijective (fun a : Adeles F ⧸ W => n • a)
  have h : IsUnit (n : F) := (Nat.cast_ne_zero.mpr hn).isUnit
  simpa only [Nat.cast_smul_eq_nsmul F] using
    (h.smul_bijective : Bijective (fun a : Adeles F ⧸ W => (n : F) • a))

private theorem principalIdele_value_mem (a : Idele F) :
    a ∈ principalIdeles F ↔ a.val ∈ NumberField.AdeleRing.principalSubgroup (𝓞 F) F := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : F), rfl⟩
  · rintro ⟨x, hx⟩
    have hx₀ : x ≠ 0 := by
      intro h
      have hzero : (0 : Adeles F) = a.val := by simpa [h] using hx
      have hinv := a.val_inv
      rw [← hzero, zero_mul] at hinv
      have hone : algebraMap F (Adeles F) 0 = algebraMap F (Adeles F) 1 := by simpa using hinv
      exact zero_ne_one (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F hone)
    refine ⟨Units.mk0 x hx₀, ?_⟩
    exact Units.ext hx

/-- The multiplicative principal subgroup is discrete in the idelic topology,
as in Lemma A.1.3.4(1). -/
theorem principalIdeles_discrete :
    DiscreteTopology (principalIdeles F) := by
  letI := principalAdeles_discrete (F := F)
  let f (a : principalIdeles F) : NumberField.AdeleRing.principalSubgroup (𝓞 F) F :=
    ⟨a.val.val, (principalIdele_value_mem a.val).mp a.property⟩
  have hcont : Continuous f :=
    (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
  apply DiscreteTopology.of_continuous_injective hcont
  intro a b hab
  exact Subtype.ext (Units.ext (congrArg Subtype.val hab))

theorem principalIdeles_closed : IsClosed (principalIdeles F : Set (Idele F)) := by
  have heq : (principalIdeles F : Set (Idele F)) =
      Units.val ⁻¹' (NumberField.AdeleRing.principalSubgroup (𝓞 F) F : Set (Adeles F)) :=
    Set.ext principalIdele_value_mem
  rw [heq]
  exact principalAdeles_closed.preimage Units.continuous_val

theorem ideleClasses_locallyCompact : LocallyCompactSpace (IdeleClass F) := by
  letI := ideles_locallyCompact (F := F)
  infer_instance

theorem ideleClasses_hausdorff : T2Space (IdeleClass F) := by
  letI := principalIdeles_closed (F := F)
  infer_instance

end Masullo
