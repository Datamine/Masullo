import AdelicThetaTranslations
import SLocalFourierIntegral
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NNReal NumberField RestrictedProduct WithZero

namespace Masullo

noncomputable section

/- The summation lemmas and kernel comparison use the arguments from
   mccorvie/riemann-masullo at aa9116c71f4e89934426327b503d6db2ecad0a4b,
   under Apache-2.0. See External/PROVENANCE.md. -/

/-- An absolutely convergent sum over a group can be regrouped
over cosets of an injectively parametrized subgroup. -/
private theorem hasSum_cosets {E G H : Type*} [NormedAddCommGroup E] [CompleteSpace E] [CommGroup G] [Group H]
    (d : H →* G) (hd : Injective d) {a : G → E} (ha : Summable a)
    {b : G ⧸ d.range → E} (hb : ∀ g, b (QuotientGroup.mk g) = ∑' h, a (g * d h)) :
    HasSum b (∑' g, a g) := by
  let π : G →* G ⧸ d.range := QuotientGroup.mk' _
  refine (ha.hasSum.tsum_fiberwise π).congr_fun fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    let e (h : H) : π ⁻¹' {π g} := ⟨g * d h, by
      change π (g * d h) = π g
      rw [map_mul, show π (d h) = 1 from (QuotientGroup.eq_one_iff _).mpr ⟨h, rfl⟩, mul_one]⟩
    have he : Bijective e := by
      refine ⟨fun x y h ↦ hd (mul_left_cancel (congrArg Subtype.val h)), ?_⟩
      rintro ⟨x, hx⟩
      have hx' : QuotientGroup.mk g = (QuotientGroup.mk x : G ⧸ d.range) := (show π x = π g from hx).symm
      obtain ⟨y, hy⟩ := QuotientGroup.eq.mp hx'
      exact ⟨y, Subtype.ext (by change g * d y = x; rw [hy, mul_inv_cancel_left])⟩
    exact (hb g).trans ((Equiv.ofBijective e he).tsum_eq (fun x ↦ a x.val))

/-- Regroup an absolutely convergent sum using any choice of coset representatives. -/
theorem hasSum_cosets_of_representatives {E G H : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] [CommGroup G] [Group H]
    (d : H →* G) (hd : Injective d) {a : G → E} (ha : Summable a)
    (r : G ⧸ d.range → G) (hr : ∀ q, QuotientGroup.mk (r q) = q)
    {b : G ⧸ d.range → E} (hb : ∀ q, b q = ∑' h, a (r q * d h)) :
    HasSum b (∑' g, a g) := by
  refine hasSum_cosets d hd ha fun t ↦ ?_
  rw [hb]
  obtain ⟨u,hu⟩ := QuotientGroup.eq.mp (hr (QuotientGroup.mk t)).symm
  have he : t * d u = r (QuotientGroup.mk t) := by rw [hu,mul_inv_cancel_left]
  rw [← he]
  have hsum := (Equiv.mulLeft u).tsum_eq (fun x ↦ a (t * d x))
  change (∑' x, a (t * d (u*x))) = _ at hsum
  simpa only [map_mul,mul_assoc] using hsum

/-- Finite inclusion–exclusion works simultaneously for a family of absolutely
convergent sums. If the sums on all intersections belong to an additive subgroup
of the function space, so do the sums avoiding a finite list of predicates. -/
private theorem tsum_avoiding_finset_mem {ι α X E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (L : AddSubgroup (X → E)) (a : X → α → E) (ha : ∀ x, Summable (fun t ↦ ‖a x t‖))
    (P : ι → α → Prop) [∀ i t, Decidable (P i t)]
    (h : ∀ B : Finset ι, open Classical in
      (fun x ↦ ∑' t, if ∀ i ∈ B, P i t then a x t else 0) ∈ L) (C : Finset ι) :
    open Classical in (fun x ↦ ∑' t, if ∀ i ∈ C, ¬ P i t then a x t else 0) ∈ L := by
  classical
  let term (C B : Finset ι) (x : X) (t : α) :=
    if (∀ i ∈ B, P i t) ∧ (∀ i ∈ C, ¬ P i t) then a x t else 0
  have hsum C B x : Summable (term C B x) := by
    apply (ha x).of_norm_bounded
    intro t
    change ‖ite _ _ _‖ ≤ _
    split_ifs <;> simp
  have hm (C B : Finset ι) : (fun x ↦ ∑' t, term C B x t) ∈ L := by
    induction C using Finset.induction_on generalizing B with
    | empty => simpa [term] using h B
    | insert i C _ ih =>
      have hd (x t) : term (insert i C) B x t = term C B x t - term C (insert i B) x t := by
        by_cases hp : P i t <;> simp [term, hp]
      have heq : (fun x ↦ ∑' t, term (insert i C) B x t) =
          (fun x ↦ ∑' t, term C B x t) - fun x ↦ ∑' t, term C (insert i B) x t :=
        funext fun x ↦ (tsum_congr (hd x)).trans ((hsum C B x).tsum_sub (hsum C (insert i B) x))
      exact heq ▸ L.sub_mem (ih B) (ih (insert i B))
  simpa [term] using hm C ∅

/-- If an absolutely summable family sums to zero on every finite intersection of predicates,
then it also sums to zero on the set where none of the predicates hold. -/
private theorem tsum_avoiding_of_tsum_intersections {ι α E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (a : α → E)
    (P : ι → α → Prop) [∀ i x, Decidable (P i x)] (ha : Summable (fun x ↦ ‖a x‖))
    (hz : ∀ B : Finset ι, open Classical in (∑' x, if ∀ v ∈ B, P v x then a x else 0) = 0) :
    open Classical in (∑' x, if ∀ v, ¬ P v x then a x else 0) = 0 := by
  classical
  let term (B C : Finset ι) (x : α) :=
    if (∀ v ∈ B, P v x) ∧ (∀ v ∈ C, ¬ P v x) then a x else 0
  have bound (B C : Finset ι) (x : α) : ‖term B C x‖ ≤ ‖a x‖ := by
    unfold term
    split_ifs <;> simp
  have hzero (C : Finset ι) : ∑' x, term ∅ C x = 0 := by
    have h := tsum_avoiding_finset_mem (ι := ι) (⊥ : AddSubgroup (Unit → E))
      (fun _ ↦ a) (fun _ ↦ ha) P (fun B ↦ funext (fun _ ↦ hz B)) C
    simpa [term] using congrFun (show _ = (0 : Unit → E) from h) ()

  -- Finite exclusions eventually decide each term.
  have ht (x : α) : Tendsto (fun C ↦ term ∅ C x) atTop
      (𝓝 (if ∀ v, ¬ P v x then a x else 0)) := by
    by_cases h : ∀ v, ¬ P v x
    · simp [term, h]
    · obtain ⟨v, hv⟩ := not_forall.mp h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({v} : Finset ι)] with C hC
      have hc : ¬ ∀ w ∈ C, ¬ P w x := fun hh ↦ hv (hh v (hC (Finset.mem_singleton_self v)))
      simp [term, hc, h]
  have ht' := tendsto_tsum_of_dominated_convergence ha ht
    (Eventually.of_forall (fun C x ↦ bound ∅ C x))
  simpa only [hzero] using (tendsto_nhds_unique ht' (by simpa only [hzero] using
    (tendsto_const_nhds (f := atTop (α := Finset ι)) (x := (0 : E)))))

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev A := Adeles F
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S

/-- The theta contribution of one principal coset is a local theta value
when the translated argument is integral outside the selected places. -/
def globalThetaPaddingCosetTerm (S : Finset (Place F)) (f : E F S)
    (g : Idele F) (t : Fˣ) : ℂ :=
  let y := principalIdele F t * g
  let p := Units.map (sAdelesProjection F S).toMonoidHom y
  if y.val ∈ globalIntegralSubring F S then
    sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) p
  else 0

theorem globalThetaPaddingCosetTerm_eq (S : Finset (Place F)) (f : E F S)
    (g : Idele F) (t : Fˣ) :
    globalThetaPaddingCosetTerm F S f g t =
      ∑' u : (sIntegerRing F S)ˣ,
        thetaSummand F (GlobalBruhat.algebraicEquiv F f.val).val g (t * sUnitToField F S u) := by
  let d := sUnitToField F S
  let b := (GlobalBruhat.algebraicEquiv F f.val).val
  let y := principalIdele F t * g
  let R := globalIntegralSubring F S
  let p := Units.map (sAdelesProjection F S).toMonoidHom y
  have hterm (u : (sIntegerRing F S)ˣ) :
      thetaSummand F b g (t * d u) =
        if y.val ∈ R then sLocalBruhatRestriction F S f.val (sIntegerDiagonal F S u.val * p.val)
        else 0 := by
    let a := principalIdele F (d u)
    have hu : a ∈ sIdeleBlock F S := (principalIdele_mem_sBlock F S _).mpr ⟨u, rfl⟩
    have he : principalIdele F (t * d u) * g = a * y := by
      rw [map_mul, mul_assoc, mul_left_comm (principalIdele F t)]
    have hr : (a * y).val ∈ R ↔ y.val ∈ R := by
      change a.val * y.val ∈ R ↔ y.val ∈ R
      constructor
      · intro h
        have h' := R.mul_mem hu.2 h
        change a.inv * (a.val * y.val) ∈ R at h'
        rwa [← mul_assoc, a.inv_val, one_mul] at h'
      · exact fun h ↦ R.mul_mem hu.1 h
    have hp : sAdelesProjection F S (a * y).val =
        sIntegerDiagonal F S u.val * p.val := map_mul (sAdelesProjection F S) _ _
    unfold thetaSummand
    rw [he]
    change GlobalBruhat.evaluation F (a * y).val f.val = _
    rw [sLocalBruhatRestriction_reconstruct]
    change _ * (if (a * y).val ∈ R then 1 else 0) = _
    rw [hr, hp]
    split_ifs <;> simp
  rw [tsum_congr hterm]
  change (if y.val ∈ R then sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) p else 0) = _
  by_cases hy : y.val ∈ R
  · simp only [ite_eq_left hy]
    exact ((Additive.toMul : Additive (sIntegerRing F S)ˣ ≃ (sIntegerRing F S)ˣ).tsum_eq
      (fun u ↦ sLocalBruhatRestriction F S f.val (sIntegerDiagonal F S u.val * p.val)))
  · simp [hy]

/-- The global padding map is represented by an absolutely convergent
sum of the local theta contributions over the principal cosets. -/
theorem hasSum_globalThetaPaddingCosets (S : Finset (Place F)) (f : E F S) (g : Idele F)
    (r : (Fˣ ⧸ (sUnitToField F S).range) → Fˣ)
    (hr : ∀ q, QuotientGroup.mk (r q) = q) :
    HasSum (fun q ↦ globalThetaPaddingCosetTerm F S f g (r q))
      (globalThetaOperator F f.val (ideleClassMap F g)) := by
  let d := sUnitToField F S
  let b := (GlobalBruhat.algebraicEquiv F f.val).val
  change HasSum _ (thetaOnIdeles F b g)
  apply hasSum_cosets_of_representatives d (sUnitToField_injective F S)
    (adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F f.val).property g).of_norm r hr
  intro q
  exact globalThetaPaddingCosetTerm_eq F S f g (r q)

theorem summable_norm_globalThetaPaddingCosets (S : Finset (Place F)) (f : E F S) (g : Idele F)
    (r : (Fˣ ⧸ (sUnitToField F S).range) → Fˣ)
    (hr : ∀ q, QuotientGroup.mk (r q) = q) :
    Summable (fun q ↦ ‖globalThetaPaddingCosetTerm F S f g (r q)‖) :=
  (hasSum_globalThetaPaddingCosets F S f g r hr).summable.norm

private theorem sLocalThetaKernel_global_zero (S : Finset (Place F))
    (f : E F S) (hf : f ∈ (sLocalThetaOperator F S).ker) :
    f.val ∈ (globalThetaOperator F).ker := by
  apply LinearMap.mem_ker.mpr
  funext q
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
  let r (q : Fˣ ⧸ (sUnitToField F S).range) := (QuotientGroup.mk_surjective q).choose
  have hs := hasSum_globalThetaPaddingCosets F S f g r
    (fun q ↦ (QuotientGroup.mk_surjective q).choose_spec)
  have hz (q : Fˣ ⧸ (sUnitToField F S).range) :
      globalThetaPaddingCosetTerm F S f g (r q) = 0 := by
    dsimp only [globalThetaPaddingCosetTerm]
    split_ifs
    · exact congrFun (LinearMap.mem_ker.mp hf) (QuotientGroup.mk _)
    · rfl
  exact hs.tsum_eq.symm.trans (by simp [hz])

/-- Insertion of a local idele uses the coordinate one outside its stage. -/
theorem sLocalEmbed_outside_one (S : Finset (Place F)) (g : (SAdeles F S)ˣ)
    (v : Place F) (hv : v ∉ S) : (sLocalEmbed F S g).val.val.2 v = 1 := by
  have h := (sBlockUnitProduct F S).apply_symm_apply (g, 1)
  exact congrArg (fun z : (SAdeles F S)ˣ × (SIntegralTail F S)ˣ =>
    (z.2.val ⟨v, hv⟩).val) h

/-- The inverse uniformizer cuts the local unit ball down to its maximal ideal. -/
theorem finitePlace_mul_inverseUniformizer_integral_iff (v : Place F) (t : Fˣ) :
    algebraMap F (v.adicCompletion F) t.val *
        ((chosenFiniteUniformizer F v)⁻¹ : (v.adicCompletion F)ˣ).val ∈
      v.adicCompletionIntegers F ↔ v.valuation F t.val < 1 := by
  let V : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  change V (algebraMap F (v.adicCompletion F) t.val *
      ((chosenFiniteUniformizer F v)⁻¹ : (v.adicCompletion F)ˣ).val) ≤ 1 ↔ _
  have hval : V (algebraMap F (v.adicCompletion F) t.val) = v.valuation F t.val :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) t.val
  have hπ : V (chosenFiniteUniformizer F v).val = WithZero.exp (-1 : ℤ) :=
    (chosenFiniteUniformizer_spec F v).trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (HeightOneSpectrum.valuedAdicCompletion_surjective F v)))
  have hpos : 0 < WithZero.exp (-1 : ℤ) := pos_iff_ne_zero.mpr (by simp)
  rw [map_mul, hval, Units.val_inv_eq_inv_val, map_inv₀, hπ,
    ← le_div_iff₀ (inv_pos.mpr hpos), div_inv_eq_mul, one_mul]
  have h := WithZero.lt_mul_exp_iff_le (x := v.valuation F t.val)
    (y := WithZero.exp (-1 : ℤ)) (by simp)
  simpa only [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] using h.symm

private theorem exists_thetaCutIdele (S : Finset (Place F)) (g : (SAdeles F S)ˣ)
    (B : Finset {v : Place F // v ∉ S}) :
    ∃ z : Idele F, sAdelesProjection F S z.val = g.val ∧
      ∀ (v : Place F) (hv : v ∉ S) (t : Fˣ),
        ((principalIdele F t * z).val.2 v ∈ v.adicCompletionIntegers F) ↔
          if (⟨v, hv⟩ : {v : Place F // v ∉ S}) ∈ B then v.valuation F t.val < 1
          else v.valuation F t.val ≤ 1 := by
  let C := B.map ⟨Subtype.val, Subtype.val_injective⟩
  let e (w : Place F) := singleFiniteIdele F w (chosenFiniteUniformizer F w)⁻¹
  let c := ∏ w ∈ C, e w
  have hC (w : Place F) (hw : w ∈ C) : w ∉ S := by
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hw
    exact u.property
  have hcA : c.val.1 = 1 := by
    let π : Idele F →* InfiniteAdeleRing F :=
      (RingHom.fst _ _).toMonoidHom.comp (Units.coeHom _)
    change π (∏ w ∈ C, e w) = 1
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ ↦ rfl
  have hc (w : Place F) : c.val.2 w =
      if w ∈ C then ((chosenFiniteUniformizer F w)⁻¹ : (w.adicCompletion F)ˣ).val else 1 := by
    let eval : FiniteAdeleRing (𝓞 F) F →+* w.adicCompletion F :=
      RestrictedProduct.evalRingHom (fun w : Place F ↦ w.adicCompletion F) w
    let π : Idele F →* w.adicCompletion F :=
      eval.toMonoidHom.comp ((RingHom.snd _ _).toMonoidHom.comp (Units.coeHom _))
    change π (∏ t ∈ C, e t) = _
    rw [map_prod]
    have hSingle (t : Place F) : π (e t) =
        Function.update (fun u : Place F ↦ (1 : u.adicCompletion F)) t
          ((chosenFiniteUniformizer F t)⁻¹ : (t.adicCompletion F)ˣ).val w := rfl
    by_cases hw : w ∈ C
    · rw [ite_eq_left hw, Finset.prod_eq_single_of_mem w hw, hSingle, Function.update_self]
      intro t _ htw
      rw [hSingle, Function.update_of_ne htw.symm]
    · rw [ite_eq_right hw]
      apply Finset.prod_eq_one
      intro t ht
      rw [hSingle, Function.update_of_ne (show w ≠ t from fun h ↦ hw (by rwa [h]))]
  let i := (sLocalEmbed F S g).val
  refine ⟨i * c, ?_, fun w hw t ↦ ?_⟩
  · have hproj : sAdelesProjection F S c.val = 1 := by
      apply Prod.ext hcA
      funext w
      change c.val.2 w = 1
      rw [hc, ite_eq_right (fun h ↦ hC w h w.property)]
    change sAdelesProjection F S (i.val * c.val) = g.val
    rw [map_mul, show sAdelesProjection F S i.val = g.val from sLocalEmbed_project F S g,
      hproj, mul_one]
  · let V : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    change V ((algebraMap F (w.adicCompletion F) t.val) * (i.val.2 w * c.val.2 w)) ≤ 1 ↔ _
    rw [show i.val.2 w = 1 from sLocalEmbed_outside_one F S g w hw,
      one_mul, hc]
    have hmem : w ∈ C ↔ (⟨w, hw⟩ : {v : Place F // v ∉ S}) ∈ B := by
      constructor
      · intro ht
        obtain ⟨x, hx, he⟩ := Finset.mem_map.mp ht
        exact (Subtype.ext he : x = ⟨w, hw⟩) ▸ hx
      · exact Finset.mem_map_of_mem _
    by_cases h : (⟨w, hw⟩ : {v : Place F // v ∉ S}) ∈ B
    · rw [ite_eq_left (hmem.mpr h), ite_eq_left h]
      exact finitePlace_mul_inverseUniformizer_integral_iff F w t
    · rw [ite_eq_right (mt hmem.mp h), ite_eq_right h, mul_one]
      have hval : V (algebraMap F (w.adicCompletion F) t.val) = w.valuation F t.val :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) t.val
      rw [hval]

private theorem sLocalThetaKernel_of_global_zero (S : Finset (Place F))
    (f : E F S) (hf : f.val ∈ (globalThetaOperator F).ker) :
    f ∈ (sLocalThetaOperator F S).ker := by
  apply LinearMap.mem_ker.mpr
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g = 0
  let W := {w : Place F // w ∉ S}
  let ok (t : Fˣ) := ∀ w : W, w.val.valuation F t.val ≤ 1
  let P (w : W) (t : Fˣ) := w.val.valuation F t.val < 1
  let b (t : Fˣ) := sLocalBruhatRestriction F S f.val
    (sAdelesProjection F S (principalIdele F t).val * g.val)
  let a (t : Fˣ) := if ok t then b t else 0
  let r := (GlobalBruhat.algebraicEquiv F f.val).val
  have hz (B : Finset W) : ∃ z : Idele F, ∀ t : Fˣ,
      thetaSummand F r z t = if ∀ w ∈ B, P w t then a t else 0 := by
    obtain ⟨z, hz, hcut⟩ := exists_thetaCutIdele F S g B
    refine ⟨z, fun t ↦ ?_⟩
    have hcW (w : W) :
        (principalIdele F t * z).val.2 w.val ∈ w.val.adicCompletionIntegers F ↔
          (if w ∈ B then P w t else w.val.valuation F t.val ≤ 1) := by
      rcases w with ⟨w, hw⟩
      exact hcut w hw t
    have hcond : (∀ w ∉ S, (principalIdele F t * z).val.2 w ∈ w.adicCompletionIntegers F) ↔
        ok t ∧ ∀ w ∈ B, P w t := by
      constructor
      · intro h
        refine ⟨fun w ↦ ?_, fun w hw ↦ ?_⟩
        · have H := (hcW w).mp (h w.val w.property)
          by_cases hw : w ∈ B
          · exact (show P w t from by simpa only [ite_eq_left hw] using H).le
          · simpa only [ite_eq_right hw] using H
        · simpa only [ite_eq_left hw] using (hcW w).mp (h w.val w.property)
      · rintro ⟨h₁, h₂⟩ w hw
        apply (hcut w hw t).mpr
        by_cases hwB : (⟨w, hw⟩ : W) ∈ B
        · rw [ite_eq_left hwB]
          exact h₂ ⟨w, hw⟩ hwB
        · rw [ite_eq_right hwB]
          exact h₁ ⟨w, hw⟩
    change GlobalBruhat.evaluation F _ f.val = _
    rw [sLocalBruhatRestriction_reconstruct, hcond, Units.val_mul, map_mul, hz]
    by_cases h₁ : ok t <;> by_cases h₂ : ∀ w ∈ B, P w t <;> simp [a, b, h₁, h₂]
  obtain ⟨z₀, hz₀⟩ := hz ∅
  have ha : Summable (fun t ↦ ‖a t‖) :=
    (adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F f.val).property z₀).congr
      (fun t ↦ congrArg norm (by simpa only [Finset.notMem_empty, IsEmpty.forall_iff,
        false_implies, implies_true, ite_true] using hz₀ t))
  have hzero (B : Finset W) : (∑' t, if ∀ w ∈ B, P w t then a t else 0) = 0 := by
    obtain ⟨z, hzB⟩ := hz B
    exact (tsum_congr hzB).symm.trans (congrFun (LinearMap.mem_ker.mp hf) (ideleClassMap F z))
  have hex := tsum_avoiding_of_tsum_intersections a P ha hzero
  let d := sUnitToField F S
  have hunit (t : Fˣ) : t ∈ d.range ↔ ok t ∧ ∀ w, ¬ P w t := by
    have he : t ∈ d.range ↔ principalIdele F t ∈ sIdeleBlock F S :=
      (principalIdele_mem_sBlock F S t).symm
    rw [he, sIdeleBlock_mem_iff]
    have hv (w : W) : ideleOrder F (principalIdele F t) w.val = 0 ↔
        w.val.valuation F t.val = 1 := by
      rw [ideleOrder_eq_zero_iff]
      have he : Valued.v ((principalIdele F t).val.2 w.val) = w.val.valuation F t.val :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w.val) t.val
      rw [he]
    constructor
    · intro h
      exact ⟨fun w ↦ ((hv w).mp (h w.val w.property)).le,
        fun w ↦ ((hv w).mp (h w.val w.property)).not_lt⟩
    · rintro ⟨h₁, h₂⟩ w hw
      exact (hv ⟨w, hw⟩).mpr (le_antisymm (h₁ ⟨w, hw⟩) (not_lt.mp (h₂ ⟨w, hw⟩)))
  have hsel (t : Fˣ) : (if ∀ w, ¬ P w t then a t else 0) =
      (d.range : Set Fˣ).indicator b t := by
    by_cases ht : t ∈ (d.range : Set Fˣ)
    · obtain ⟨h₁, h₂⟩ := (hunit t).mp ht
      rw [indicator_of_mem ht]
      simp [a, h₁, h₂]
    · rw [indicator_of_notMem ht]
      by_cases h₁ : ok t <;> by_cases h₂ : ∀ w, ¬ P w t
      · exact (ht ((hunit t).mpr ⟨h₁, h₂⟩)).elim
      all_goals simp [a, h₁, h₂]
  rw [tsum_congr hsel, ← tsum_subtype] at hex
  let u : Additive (sIntegerRing F S)ˣ → d.range := fun x ↦ ⟨d x.toMul, ⟨x.toMul, rfl⟩⟩
  have hu : Bijective u := by
    constructor
    · intro x y h
      exact Additive.toMul.injective (sUnitToField_injective F S (congrArg Subtype.val h))
    · rintro ⟨y, x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩
  exact ((Equiv.ofBijective u hu).tsum_eq (fun t ↦ b t.val)).trans hex

/-- An S-local test has zero theta exactly when its global insertion has
zero theta. -/
theorem sLocalThetaKernel_iff_global (S : Finset (Place F)) (f : E F S) :
    f ∈ (sLocalThetaOperator F S).ker ↔ f.val ∈ (globalThetaOperator F).ker :=
  ⟨sLocalThetaKernel_global_zero F S f, sLocalThetaKernel_of_global_zero F S f⟩

/-- Global insertion descends continuously to the ordinary theta quotients. -/
def sLocalThetaToGlobal (S : Finset (Place F)) :
    SLocalThetaQuotient F S →L[ℂ] GlobalThetaQuotient F := by
  let P := (sLocalThetaOperator F S).ker
  let Q := (globalThetaOperator F).ker
  refine P.liftQL (Q.mkQL.comp (E F S).subtypeL) ?_
  intro f hf
  exact (Submodule.Quotient.mk_eq_zero Q).mpr ((sLocalThetaKernel_iff_global F S f).mp hf)

@[simp] theorem sLocalThetaToGlobal_mk (S : Finset (Place F)) (f : E F S) :
    sLocalThetaToGlobal F S (Submodule.Quotient.mk f) = Submodule.Quotient.mk f.val := rfl

theorem sLocalThetaToGlobal_injective (S : Finset (Place F)) :
    Injective (sLocalThetaToGlobal F S) := by
  rw [injective_iff_map_eq_zero]
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [sLocalThetaToGlobal_mk, Submodule.Quotient.mk_eq_zero]
  exact (sLocalThetaKernel_iff_global F S f).mpr

/-- Stage inclusions descend to the ordinary theta quotients. -/
def sLocalThetaTransition {S T : Finset (Place F)} (hST : S ⊆ T) :
    SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F T := by
  let P := (sLocalThetaOperator F S).ker
  let Q := (sLocalThetaOperator F T).ker
  refine P.liftQL (Q.mkQL.comp (sLocalBruhatTransition F hST)) ?_
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero Q).mpr
  apply (sLocalThetaKernel_iff_global F T (sLocalBruhatTransition F hST f)).mpr
  exact (sLocalThetaKernel_iff_global F S f).mp hf

@[simp] theorem sLocalThetaTransition_mk {S T : Finset (Place F)} (hST : S ⊆ T) (f : E F S) :
    sLocalThetaTransition F hST (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalBruhatTransition F hST f) := rfl

theorem sLocalThetaToGlobal_transition {S T : Finset (Place F)} (hST : S ⊆ T)
    (q : SLocalThetaQuotient F S) :
    sLocalThetaToGlobal F T (sLocalThetaTransition F hST q) = sLocalThetaToGlobal F S q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

theorem sLocalThetaTransition_injective {S T : Finset (Place F)} (hST : S ⊆ T) :
    Injective (sLocalThetaTransition F hST) := by
  intro q r h
  apply sLocalThetaToGlobal_injective F S
  rw [← sLocalThetaToGlobal_transition F hST q, ← sLocalThetaToGlobal_transition F hST r, h]

/-- The stages containing the different are cofinal and exhaust the
global theta quotient. -/
theorem globalThetaQuotient_exhausted_by_different_stages (T : Finset (Place F))
    (q : GlobalThetaQuotient F) :
    ∃ S : Finset (Place F), T ⊆ S ∧
      (∀ w : Place F, w.asIdeal ∣ differentIdeal ℤ (𝓞 F) → w ∈ S) ∧
      q ∈ Set.range (sLocalThetaToGlobal F S) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨U, hU⟩ := sLocalBruhat_bounded_subset F {f} (Bornology.isVonNBounded_singleton f)
  let D := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  let S := T ∪ (U ∪ D)
  have hUS : U ⊆ S := Finset.subset_union_left.trans Finset.subset_union_right
  refine ⟨S, Finset.subset_union_left, fun w hw ↦ ?_, ?_⟩
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ (by simpa [D] using hw))
  · let fS : E F S := ⟨f, sLocalBruhatImage_mono F hUS (hU (mem_singleton f))⟩
    exact ⟨Submodule.Quotient.mk fS, rfl⟩

variable (S : Finset (Place F))
variable (hS : ∀ w : Place F, w.asIdeal ∣ differentIdeal ℤ (𝓞 F) → w ∈ S)

/-- A stage containing the different has a descended Fourier operator on
its ordinary theta quotient. -/
def sLocalThetaFourier : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S := by
  let P := (sLocalThetaOperator F S).ker
  let T := sLocalStageFourier F S (sLocalFourier_preserves_stage_of_different F S hS)
  refine P.liftQL (P.mkQL.comp T) ?_
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero P).mpr
  apply (sLocalThetaKernel_iff_global F S (T f)).mpr
  apply (Submodule.Quotient.mk_eq_zero (globalThetaOperator F).ker).mp
  change (Submodule.Quotient.mk (GlobalBruhat.fourier F f.val) : GlobalThetaQuotient F) = 0
  rw [← globalThetaFourier_mk,
    (Submodule.Quotient.mk_eq_zero _).mpr ((sLocalThetaKernel_iff_global F S f).mp hf), map_zero]

@[simp] theorem sLocalThetaFourier_mk (f : E F S) :
    sLocalThetaFourier F S hS (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalStageFourier F S
        (sLocalFourier_preserves_stage_of_different F S hS) f) := rfl

theorem sLocalThetaFourier_toGlobal (q : SLocalThetaQuotient F S) :
    sLocalThetaToGlobal F S (sLocalThetaFourier F S hS q) =
      globalThetaFourier F (sLocalThetaToGlobal F S q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

theorem sLocalThetaFourier_involutive : Involutive (sLocalThetaFourier F S hS) := by
  intro q
  apply sLocalThetaToGlobal_injective F S
  rw [sLocalThetaFourier_toGlobal, sLocalThetaFourier_toGlobal, globalThetaFourier_involutive]

/-- On a stage containing the different, Fourier is a continuous
involutive linear equivalence on the ordinary theta quotient. -/
def sLocalThetaFourierEquiv : SLocalThetaQuotient F S ≃L[ℂ] SLocalThetaQuotient F S :=
  ContinuousLinearEquiv.equivOfInverse (sLocalThetaFourier F S hS) (sLocalThetaFourier F S hS)
    (sLocalThetaFourier_involutive F S hS) (sLocalThetaFourier_involutive F S hS)

theorem sLocalThetaFourier_unique (T : SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S)
    (hT : ∀ f : E F S, T (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalStageFourier F S
        (sLocalFourier_preserves_stage_of_different F S hS) f)) :
    T = sLocalThetaFourier F S hS := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact hT f

theorem sLocalThetaFourier_transition {T : Finset (Place F)} (hST : S ⊆ T)
    (hT : ∀ w : Place F, w.asIdeal ∣ differentIdeal ℤ (𝓞 F) → w ∈ T)
    (q : SLocalThetaQuotient F S) :
    sLocalThetaTransition F hST (sLocalThetaFourier F S hS q) =
      sLocalThetaFourier F T hT (sLocalThetaTransition F hST q) := by
  apply sLocalThetaToGlobal_injective F T
  rw [sLocalThetaToGlobal_transition, sLocalThetaFourier_toGlobal, sLocalThetaFourier_toGlobal,
    sLocalThetaToGlobal_transition]

omit S hS in
/-- Fourier intertwines norm-one translations with inverse translations on
the global theta quotient. -/
theorem globalThetaFourier_translate_normOne (g : Idele F) (hg : ideleNorm F g = 1)
    (q : GlobalThetaQuotient F) :
    globalThetaFourier F (globalThetaTranslateIdeles F g q) =
      globalThetaTranslateIdeles F g⁻¹ (globalThetaFourier F q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [globalThetaTranslateIdeles_mk, globalThetaFourier_mk, globalThetaFourier_mk,
    globalThetaTranslateIdeles_mk]
  congr 1
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext a
  letI : MeasurableSpace (A F) := borel _
  letI : BorelSpace (A F) := ⟨rfl⟩
  let ν := adelicHaarUnitDomain F
  letI : ν.IsAddHaarMeasure := adelicHaarUnitDomain_isHaar F
  let b := (GlobalBruhat.algebraicEquiv F f).val
  have hb : Measurable b := (bruhat_continuous F (GlobalBruhat.algebraicEquiv F f).property).measurable
  change GlobalBruhat.evaluation F a
      (GlobalBruhat.fourier F (GlobalBruhat.leftTranslate F g f)) =
    GlobalBruhat.evaluation F a (GlobalBruhat.leftTranslate F g⁻¹ (GlobalBruhat.fourier F f))
  rw [GlobalBruhat.leftTranslate_apply]
  change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F (GlobalBruhat.leftTranslate F g f))).val a =
    (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val (g⁻¹⁻¹.val * a)
  rw [GlobalBruhat.fourier_apply, GlobalBruhat.fourier_apply]
  change adelicFourierIntegral F ν (standardAdelicCharacter F) (fun x ↦ b (g⁻¹.val * x)) a =
    adelicFourierIntegral F ν (standardAdelicCharacter F) b (g⁻¹⁻¹.val * a)
  rw [adelicFourier_mul_argument F ν _ (standardAdelicCharacter_continuous F) b hb g⁻¹ a,
    map_inv (ideleNorm F), hg, inv_one, inv_one, one_smul]
  rfl

private theorem sLocalBruhat_leftTranslate_mem (g : (SAdeles F S)ˣ) (f : E F S) :
    GlobalBruhat.leftTranslate F (sLocalEmbed F S g).val f.val ∈ E F S := by
  let i := sLocalEmbed F S g
  have hi (w : Place F) (hw : w ∉ S) : i.val.inv.2 w = 1 := by
    change ((sLocalEmbed F S g).val⁻¹).val.2 w = 1
    rw [← Subgroup.coe_inv, ← map_inv]
    exact sLocalEmbed_outside_one F S g⁻¹ w hw
  obtain ⟨hs, ht⟩ := (sLocalBruhatImage_iff_support_tail_invariant F S _).mp f.property
  apply (sLocalBruhatImage_iff_support_tail_invariant F S _).mpr
  constructor
  · rintro a ⟨w, hw, hnon⟩
    rw [GlobalBruhat.leftTranslate_apply]
    apply hs
    refine ⟨w, hw, ?_⟩
    change i.val.inv.2 w * a.2 w ∉ w.adicCompletionIntegers F
    rwa [hi w hw, one_mul]
  · intro u hu a
    rw [GlobalBruhat.leftTranslate_apply, GlobalBruhat.leftTranslate_apply, mul_add]
    have hprod : i.val.inv * finiteAdelicTranslation F u = finiteAdelicTranslation F u := by
      apply Prod.ext (mul_zero _)
      apply RestrictedProduct.ext
      intro w
      change i.val.inv.2 w * u w = u w
      by_cases hw : w ∈ S
      · rw [hu.1 w hw, mul_zero]
      · rw [hi w hw, one_mul]
    change GlobalBruhat.evaluation F (i.val.inv * a + i.val.inv * finiteAdelicTranslation F u)
      f.val = GlobalBruhat.evaluation F (i.val.inv * a) f.val
    rw [hprod]
    exact ht u hu _

/-- Left translation on the embedded S-local Bruhat test space. -/
def sLocalBruhatLeftTranslate (g : (SAdeles F S)ˣ) : E F S →L[ℂ] E F S :=
  ((GlobalBruhat.leftTranslate F (sLocalEmbed F S g).val).comp (E F S).subtypeL).codRestrict _
    (sLocalBruhat_leftTranslate_mem F S g)

theorem sLocalBruhatLeftTranslate_restrict (g : (SAdeles F S)ˣ) (f : E F S)
    (x : SAdeles F S) :
    sLocalBruhatRestriction F S (sLocalBruhatLeftTranslate F S g f).val x =
      sLocalBruhatRestriction F S f.val (g.inv * x) := by
  change GlobalBruhat.evaluation F (sLocalBruhatPad F S x)
      (GlobalBruhat.leftTranslate F (sLocalEmbed F S g).val f.val) = _
  rw [GlobalBruhat.leftTranslate_apply, ← sLocalBruhatPad_mul_project]
  have h : sAdelesProjection F S ((sLocalEmbed F S g).val⁻¹).val = g.inv := by
    rw [← Subgroup.coe_inv, ← map_inv]
    exact sLocalEmbed_project F S g⁻¹
  rw [h]
  rfl

theorem sLocalThetaOperator_leftTranslate (g : (SAdeles F S)ˣ)
    (f : E F S) (c : SIdeleQuotient F S) :
    sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S g f) c =
      sLocalThetaOperator F S f ((QuotientGroup.mk g : SIdeleQuotient F S)⁻¹ * c) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective c
  let π := QuotientGroup.mk' (sUnitImage F S)
  change sLocalThetaOperator F S _ (π k) = sLocalThetaOperator F S f ((π g)⁻¹ * π k)
  rw [← map_inv, ← map_mul]
  change sLocalThetaOnIdeles F S _ k = sLocalThetaOnIdeles F S _ (g⁻¹ * k)
  unfold sLocalThetaOnIdeles
  apply tsum_congr
  intro u
  rw [sLocalBruhatLeftTranslate_restrict]
  apply congrArg (sLocalBruhatRestriction F S f.val)
  change g.inv * (sIntegerDiagonal F S u.toMul.val * k.val) =
    sIntegerDiagonal F S u.toMul.val * (g.inv * k.val)
  ac_rfl

/-- Translation by a local idele descends to its action on the ordinary
theta quotient. -/
def sLocalThetaTranslateIdeles (g : (SAdeles F S)ˣ) :
    SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S := by
  let P := (sLocalThetaOperator F S).ker
  let T := sLocalBruhatLeftTranslate F S g
  refine P.liftQL (P.mkQL.comp T) ?_
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero P).mpr
  apply (sLocalThetaKernel_iff_global F S (T f)).mpr
  apply (Submodule.Quotient.mk_eq_zero (globalThetaOperator F).ker).mp
  change (Submodule.Quotient.mk (GlobalBruhat.leftTranslate F (sLocalEmbed F S g).val f.val) :
    GlobalThetaQuotient F) = 0
  rw [← globalThetaTranslateIdeles_mk,
    (Submodule.Quotient.mk_eq_zero _).mpr ((sLocalThetaKernel_iff_global F S f).mp hf), map_zero]

@[simp] theorem sLocalThetaTranslateIdeles_mk (g : (SAdeles F S)ˣ) (f : E F S) :
    sLocalThetaTranslateIdeles F S g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S g f) := rfl

private theorem sLocalThetaTranslateIdeles_eq_of_class_eq {g k : (SAdeles F S)ˣ}
    (he : (QuotientGroup.mk g : SIdeleQuotient F S) = QuotientGroup.mk k) :
    sLocalThetaTranslateIdeles F S g = sLocalThetaTranslateIdeles F S k := by
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [sLocalThetaTranslateIdeles_mk, sLocalThetaTranslateIdeles_mk, Submodule.Quotient.eq]
  apply LinearMap.mem_ker.mpr
  rw [map_sub, sub_eq_zero]
  funext c
  rw [sLocalThetaOperator_leftTranslate, sLocalThetaOperator_leftTranslate, he]

/-- Translation by a class of S-ideles on the ordinary theta quotient. -/
def sLocalThetaTranslate (c : SIdeleQuotient F S) :
    SLocalThetaQuotient F S →L[ℂ] SLocalThetaQuotient F S :=
  Quotient.lift (sLocalThetaTranslateIdeles F S)
    (fun _ _ h ↦ sLocalThetaTranslateIdeles_eq_of_class_eq F S (Quotient.sound h)) c

theorem sLocalThetaToGlobal_translate (g : (SAdeles F S)ˣ) (q : SLocalThetaQuotient F S) :
    sLocalThetaToGlobal F S (sLocalThetaTranslateIdeles F S g q) =
      globalThetaTranslateIdeles F (sLocalEmbed F S g).val (sLocalThetaToGlobal F S q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

theorem sLocalThetaToGlobal_translate_class (g : (SAdeles F S)ˣ) (q : SLocalThetaQuotient F S) :
    sLocalThetaToGlobal F S (sLocalThetaTranslate F S (QuotientGroup.mk g) q) =
      globalThetaTranslate F (ideleClassMap F (sLocalEmbed F S g).val) (sLocalThetaToGlobal F S q) :=
  sLocalThetaToGlobal_translate F S g q

omit S hS in
/-- Enlarging the stage preserves the action of a class represented by a
local idele, using the same global idele as a representative in both stages. -/
theorem sLocalThetaTransition_translate {S T : Finset (Place F)} (hST : S ⊆ T)
    (g : (SAdeles F S)ˣ) (q : SLocalThetaQuotient F S) :
    let k := Units.map (sAdelesProjection F T).toMonoidHom (sLocalEmbed F S g).val
    sLocalThetaTransition F hST (sLocalThetaTranslate F S (QuotientGroup.mk g) q) =
      sLocalThetaTranslate F T (QuotientGroup.mk k) (sLocalThetaTransition F hST q) := by
  intro k
  have he : (sLocalEmbed F T k).val = (sLocalEmbed F S g).val := by
    apply Units.ext
    apply Prod.ext (sLocalEmbed_arch F T k)
    apply RestrictedProduct.ext
    intro w
    by_cases hw : w ∈ T
    · exact sLocalEmbed_finite F T k ⟨w, hw⟩
    · exact (sLocalEmbed_outside_one F T k w hw).trans
        (sLocalEmbed_outside_one F S g w (fun h ↦ hw (hST h))).symm
  apply sLocalThetaToGlobal_injective F T
  rw [sLocalThetaToGlobal_transition, sLocalThetaToGlobal_translate_class,
    sLocalThetaToGlobal_translate_class, sLocalThetaToGlobal_transition, he]

theorem sLocalThetaFourier_translate_normOne (g : (SAdeles F S)ˣ)
    (hg : sLocalIdeleNorm F S g = 1) (q : SLocalThetaQuotient F S) :
    sLocalThetaFourier F S hS (sLocalThetaTranslateIdeles F S g q) =
      sLocalThetaTranslateIdeles F S g⁻¹ (sLocalThetaFourier F S hS q) := by
  apply sLocalThetaToGlobal_injective F S
  have hnorm : ideleNorm F (sLocalEmbed F S g).val = 1 := hg
  rw [sLocalThetaFourier_toGlobal, sLocalThetaToGlobal_translate, sLocalThetaToGlobal_translate,
    sLocalThetaFourier_toGlobal, globalThetaFourier_translate_normOne F (sLocalEmbed F S g).val hnorm]
  rw [map_inv]
  rfl

theorem sLocalThetaFourier_translate_normOne_class (c : SLocalThetaNormOne F S)
    (q : SLocalThetaQuotient F S) :
    sLocalThetaFourier F S hS (sLocalThetaTranslate F S c.val q) =
      sLocalThetaTranslate F S c.val⁻¹ (sLocalThetaFourier F S hS q) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective c.val
  have hn : sLocalIdeleNorm F S g = 1 := by
    have h := c.property
    change sQuotientNorm F S c.val = 1 at h
    rw [← hg] at h
    exact congrArg (fun a : ℝ≥0ˣ => (a.val : ℝ)) h
  rw [← hg]
  change sLocalThetaFourier F S hS (sLocalThetaTranslateIdeles F S g q) =
    sLocalThetaTranslate F S ((QuotientGroup.mk' (sUnitImage F S)) g)⁻¹
      (sLocalThetaFourier F S hS q)
  rw [← map_inv]
  exact sLocalThetaFourier_translate_normOne F S hS g hn q

omit S hS in
theorem globalThetaFourier_translate_normOne_class (c : normOneIdeleClass F)
    (q : GlobalThetaQuotient F) :
    globalThetaFourier F (globalThetaTranslate F c.val q) =
      globalThetaTranslate F c.val⁻¹ (globalThetaFourier F q) := by
  obtain ⟨g, hg⟩ := ideleClassMap_surjective F c.val
  have hn : ideleNorm F g = 1 := by
    have h := c.property
    change ideleClassNorm F c.val = 1 at h
    rw [← hg, ideleClassNorm_mk] at h
    exact h
  rw [← hg, ← map_inv, globalThetaTranslate_class, globalThetaTranslate_class]
  exact globalThetaFourier_translate_normOne F g hn q

omit S hS in
/-- Fourier takes the global norm-one isotype of a character to the
isotype of its inverse. -/
theorem globalThetaFourier_isotype (ω : PontryaginDual (normOneIdeleClass F))
    (q : GlobalThetaQuotient F)
    (h : ∀ c : normOneIdeleClass F, globalThetaTranslate F c.val q = (↑(ω c) : ℂ) • q)
    (c : normOneIdeleClass F) :
    globalThetaTranslate F c.val (globalThetaFourier F q) =
      (↑(ω⁻¹ c) : ℂ) • globalThetaFourier F q := by
  have he := globalThetaFourier_translate_normOne_class F c⁻¹ q
  rw [h c⁻¹, map_smul, show (c⁻¹).val⁻¹ = c.val from inv_inv c.val] at he
  have hω : ω⁻¹ c = ω c⁻¹ := by
    change (ω c)⁻¹ = ω c⁻¹
    exact (map_inv ω c).symm
  rw [hω]
  exact he.symm

/-- Fourier takes the S-local norm-one isotype of a character to the
isotype of its inverse on each preserved stage. -/
theorem sLocalThetaFourier_isotype (ω : PontryaginDual (SLocalThetaNormOne F S))
    (q : SLocalThetaQuotient F S)
    (h : ∀ c : SLocalThetaNormOne F S, sLocalThetaTranslate F S c.val q = (↑(ω c) : ℂ) • q)
    (c : SLocalThetaNormOne F S) :
    sLocalThetaTranslate F S c.val (sLocalThetaFourier F S hS q) =
      (↑(ω⁻¹ c) : ℂ) • sLocalThetaFourier F S hS q := by
  have he := sLocalThetaFourier_translate_normOne_class F S hS c⁻¹ q
  rw [h c⁻¹, map_smul, show (c⁻¹).val⁻¹ = c.val from inv_inv c.val] at he
  have hω : ω⁻¹ c = ω c⁻¹ := by
    change (ω c)⁻¹ = ω c⁻¹
    exact (map_inv ω c).symm
  rw [hω]
  exact he.symm

omit S hS in
theorem globalThetaFourier_isotype_iff (ω : PontryaginDual (normOneIdeleClass F))
    (q : GlobalThetaQuotient F) :
    (∀ c : normOneIdeleClass F, globalThetaTranslate F c.val q = (↑(ω c) : ℂ) • q) ↔
    (∀ c : normOneIdeleClass F, globalThetaTranslate F c.val (globalThetaFourier F q) =
      (↑(ω⁻¹ c) : ℂ) • globalThetaFourier F q) := by
  refine ⟨globalThetaFourier_isotype F ω q, fun h c ↦ ?_⟩
  have he := globalThetaFourier_isotype F ω⁻¹ (globalThetaFourier F q) h c
  rwa [globalThetaFourier_involutive, inv_inv] at he

theorem sLocalThetaFourier_isotype_iff (ω : PontryaginDual (SLocalThetaNormOne F S))
    (q : SLocalThetaQuotient F S) :
    (∀ c : SLocalThetaNormOne F S, sLocalThetaTranslate F S c.val q = (↑(ω c) : ℂ) • q) ↔
    (∀ c : SLocalThetaNormOne F S, sLocalThetaTranslate F S c.val (sLocalThetaFourier F S hS q) =
      (↑(ω⁻¹ c) : ℂ) • sLocalThetaFourier F S hS q) := by
  refine ⟨sLocalThetaFourier_isotype F S hS ω q, fun h c ↦ ?_⟩
  have he := sLocalThetaFourier_isotype F S hS ω⁻¹ (sLocalThetaFourier F S hS q) h c
  rwa [sLocalThetaFourier_involutive, inv_inv] at he

end

end Masullo
