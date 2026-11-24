import SLocalLogarithm

open Function IsDedekindDomain NumberField NumberField.Units Set Topology
open NumberField.Units.dirichletUnitTheorem
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

abbrev ReducedSLogIndex (S : Finset (Place F)) :=
  {v : InfinitePlace F // v ≠ w₀} ⊕ S

def reducedLogIndexEmbed (S : Finset (Place F)) :
    ReducedSLogIndex F S → SLogIndex F S :=
  Sum.map Subtype.val id

theorem card_reducedSLogIndex (S : Finset (Place F)) :
    Fintype.card (ReducedSLogIndex F S) = Fintype.card (SLogIndex F S) - 1 := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_coe,
    Fintype.card_subtype_compl (fun v : InfinitePlace F => v = w₀),
    Fintype.card_subtype_eq]
  have hr : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

/-- S-unit logarithms after deleting the distinguished infinite place. -/
def sUnitReducedLog (S : Finset (Place F)) :
    Additive (sIntegerRing F S)ˣ →ₗ[ℤ] (ReducedSLogIndex F S → ℝ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun u v => sLogVector F S (principalIdele F (sUnitToField F S u.toMul))
        (reducedLogIndexEmbed F S v)
      map_zero' := by
        funext v
        change sLogVector F S (principalIdele F (sUnitToField F S 1)) _ = 0
        rw [map_one, map_one]
        cases v with
        | inl v =>
          change (v.val.mult : ℝ) * Real.log ‖(1 : v.val.Completion)‖ = 0
          simp
        | inr v =>
          change Real.log ‖(1 : v.val.adicCompletion F)‖ = 0
          rw [norm_one, Real.log_one]
      map_add' := by
        intro a b
        funext v
        change sLogVector F S (principalIdele F (sUnitToField F S (a.toMul * b.toMul))) _ = _
        rw [map_mul, map_mul, sLogVector_mul]
        rfl }

private def reducedArchProjection (S : Finset (Place F)) :
    (ReducedSLogIndex F S → ℝ) → logSpace F :=
  fun x v => x (Sum.inl v)

private theorem reducedArchProjection_continuous (S : Finset (Place F)) :
    Continuous (reducedArchProjection F S) :=
  continuous_pi fun v => continuous_apply (Sum.inl v)

private theorem integralUnit_reducedLog (S : Finset (Place F)) (u : (𝓞 F)ˣ) :
    reducedArchProjection F S (sUnitReducedLog F S (Additive.ofMul (integralUnitToS F S u))) =
      logEmbedding F (Additive.ofMul u) := by
  obtain ⟨a, ha, he⟩ := fullArchLog_unit F u
  funext v
  have h := congrFun he v
  change a.val v = _ at h
  rw [ha] at h
  exact h

private theorem sUnit_of_finite_orders_zero (S : Finset (Place F))
    (u : (sIntegerRing F S)ˣ)
    (h : ∀ v : S, ideleOrder F (principalIdele F (sUnitToField F S u)) v = 0) :
    ∃ b : (𝓞 F)ˣ, integralUnitToS F S b = u := by
  let t := sUnitToField F S u
  have hblock : principalIdele F t ∈ sIdeleBlock F S := (sPrincipal F S u).property
  have hdiv : principalIdele F t ∈ (ideleDivisor F).ker := by
    change ideleDivisor F (principalIdele F t) = 1
    apply Finsupp.ext
    intro v
    by_cases hv : v ∈ S
    · exact h ⟨v, hv⟩
    · exact (sIdeleBlock_mem_iff F S _).mp hblock v hv
  obtain ⟨b, hb⟩ := (principalIdele_integral_iff F t).mp hdiv
  exact ⟨b, sUnitToField_injective F S hb⟩

private theorem abs_sLogVector_finite_lt_implies_order_zero (S : Finset (Place F)) (a : Idele F) (v : S)
    (h : |sLogVector F S a (Sum.inr v)| < Real.log (Ideal.absNorm v.val.asIdeal)) :
    ideleOrder F a v = 0 := by
  have hp : 0 < Real.log (Ideal.absNorm v.val.asIdeal) :=
    Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
  rw [sLogVector_finite_order, abs_mul, abs_neg, abs_of_pos hp] at h
  have hi : |(ideleOrder F a v : ℝ)| < 1 := by
    by_contra! hh
    have hw := mul_le_mul_of_nonneg_right hh hp.le
    rw [one_mul] at hw
    linarith
  exact Int.abs_lt_one_iff.mp (by exact_mod_cast hi)

theorem sUnitReducedLog_zero_iff (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ) :
    sUnitReducedLog F S (Additive.ofMul u) = 0 ↔
      ∃ t : torsion F, integralUnitToS F S t.val = u := by
  constructor
  · intro hu
    have h (v : S) : |sLogVector F S (principalIdele F (sUnitToField F S u)) (Sum.inr v)| <
        Real.log (Ideal.absNorm v.val.asIdeal) := by
      have he : sLogVector F S (principalIdele F (sUnitToField F S u)) (Sum.inr v) = 0 :=
        congrFun hu (Sum.inr v)
      rw [he, abs_zero]
      exact Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
    obtain ⟨b, rfl⟩ := sUnit_of_finite_orders_zero F S u (fun v =>
      abs_sLogVector_finite_lt_implies_order_zero F S _ v (h v))
    have hb : logEmbedding F (Additive.ofMul b) = 0 := by
      rw [← integralUnit_reducedLog F S b, hu]
      rfl
    exact ⟨⟨b, (logEmbedding_eq_zero_iff (K := F)).mp hb⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    funext v
    cases v with
    | inl v =>
      have he := congrFun (integralUnit_reducedLog F S t.val) v
      rw [(logEmbedding_eq_zero_iff (K := F)).mpr t.property] at he
      exact he
    | inr v =>
      let a := principalIdele F (sUnitToField F S (integralUnitToS F S t.val))
      have he : ideleDivisor F a = 1 := (principalIdele_integral_iff F _).mpr ⟨t.val, rfl⟩
      have hn : ideleOrder F a v = 0 :=
        congrArg (fun d : Multiplicative (Place F →₀ ℤ) => d.toAdd v.val) he
      change sLogVector F S (principalIdele F (sUnitToField F S (integralUnitToS F S t.val))) (Sum.inr v) = _
      rw [sLogVector_finite_order, hn, Int.cast_zero, neg_zero, zero_mul]
      rfl

theorem sUnitReducedLog_ker_finite (S : Finset (Place F)) :
    Set.Finite {u : (sIntegerRing F S)ˣ | sUnitReducedLog F S (Additive.ofMul u) = 0} := by
  let j : torsion F → (sIntegerRing F S)ˣ := fun t => integralUnitToS F S t.val
  refine (finite_range j).subset ?_
  intro u hu
  exact (sUnitReducedLog_zero_iff F S u).mp hu

theorem sUnitReducedLog_image_discrete (S : Finset (Place F)) :
    DiscreteTopology (LinearMap.range (sUnitReducedLog F S)) := by
  let R := LinearMap.range (sUnitReducedLog F S)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_singleton_iff.mp
    (isOpen_discrete ({0} : Set (unitLattice F)))
  let U : Set (ReducedSLogIndex F S → ℝ) :=
    {x | ‖reducedArchProjection F S x‖ < δ} ∩
      ⋂ v : S, {x | |x (Sum.inr v)| < Real.log (Ideal.absNorm v.val.asIdeal)}
  have hU : IsOpen U := by
    refine (isOpen_lt (reducedArchProjection_continuous F S).norm continuous_const).inter
      (isOpen_iInter_of_finite fun v => ?_)
    exact isOpen_lt (continuous_apply (Sum.inr v)).abs continuous_const
  apply discreteTopology_of_isOpen_singleton_zero
  have he : ({0} : Set R) = (Subtype.val : R → (ReducedSLogIndex F S → ℝ)) ⁻¹' U := by
    ext x
    constructor
    · rintro (rfl : x = 0)
      refine ⟨?_, mem_iInter.mpr fun v => ?_⟩
      · change ‖(0 : logSpace F)‖ < δ
        simpa using hδ
      · change |(0 : ℝ)| < Real.log (Ideal.absNorm v.val.asIdeal)
        rw [abs_zero]
        exact Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
    · rintro ⟨ha, hv⟩
      obtain ⟨u, hu⟩ := x.property
      have hz (v : S) : ideleOrder F (principalIdele F (sUnitToField F S u.toMul)) v = 0 :=
        abs_sLogVector_finite_lt_implies_order_zero F S _ v (by
          have hh := mem_iInter.mp hv v
          change |x.val (Sum.inr v)| < Real.log (Ideal.absNorm v.val.asIdeal) at hh
          rw [← hu] at hh
          exact hh)
      obtain ⟨b, hb⟩ := sUnit_of_finite_orders_zero F S u.toMul hz
      have hb' : x.val = sUnitReducedLog F S (Additive.ofMul (integralUnitToS F S b)) :=
        hu.symm.trans (congrArg (sUnitReducedLog F S) (congrArg Additive.ofMul hb.symm))
      have ha' : reducedArchProjection F S x.val = logEmbedding F (Additive.ofMul b) :=
        (congrArg (reducedArchProjection F S) hb').trans (integralUnit_reducedLog F S b)
      have hmem : logEmbedding F (Additive.ofMul b) ∈ unitLattice F :=
        ⟨Additive.ofMul b, Submodule.mem_top, rfl⟩
      have hlog : logEmbedding F (Additive.ofMul b) = 0 := by
        let y : unitLattice F := ⟨logEmbedding F (Additive.ofMul b), hmem⟩
        have hsmall : y ∈ Metric.ball 0 δ := by
          rw [Metric.mem_ball, dist_zero_right]
          change ‖logEmbedding F (Additive.ofMul b)‖ < δ
          rw [← ha']
          exact ha
        exact congrArg Subtype.val (hball y hsmall : y = 0)
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      funext v
      cases v with
      | inl v =>
        exact congrFun (ha'.trans hlog) v
      | inr v =>
        change x.val (Sum.inr v) = 0
        rw [← hu]
        change sLogVector F S (principalIdele F (sUnitToField F S u.toMul)) (Sum.inr v) = 0
        rw [sLogVector_finite_order, hz v, Int.cast_zero, neg_zero, zero_mul]
  rw [he]
  exact hU.preimage continuous_subtype_val

instance (S : Finset (Place F)) : DiscreteTopology (LinearMap.range (sUnitReducedLog F S)) :=
  sUnitReducedLog_image_discrete F S


end

end Masullo
