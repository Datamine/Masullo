import SLocalThetaFourier
import LocallyConstantProduct

open Filter Function IsDedekindDomain NumberField Set
open scoped Classical NumberField WithZero

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- Projection of a global idele onto the larger stage. -/
private def projectUnits (T : Finset (Place F)) : Idele F →* (SAdeles F T)ˣ :=
  Units.map (sAdelesProjection F T).toMonoidHom

private theorem singleFiniteIdele_outside (v w : Place F) (h : w ≠ v)
    (a : (v.adicCompletion F)ˣ) : (singleFiniteIdele F v a).val.2 w = 1 := by
  change Function.update (fun u : Place F ↦ (1 : u.adicCompletion F)) v a.val w = 1
  rw [Function.update_of_ne h]

private theorem singleFiniteIdele_at (v : Place F) (a : (v.adicCompletion F)ˣ) :
    (singleFiniteIdele F v a).val.2 v = a.val := by
  change Function.update (fun u : Place F ↦ (1 : u.adicCompletion F)) v a.val v = a.val
  rw [Function.update_self]

private theorem valuation_one_iff_order_zero (v : Place F) (t : Fˣ) :
    v.valuation F t.val = 1 ↔ ideleOrder F (principalIdele F t) v = 0 := by
  rw [ideleOrder_eq_zero_iff]
  rw [show Valued.v ((principalIdele F t).val.2 v) = v.valuation F t.val from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) t.val]

/-- The inclusion on units associated with an enlargement of the finite stage. -/
def sUnitInclusion {S T : Finset (Place F)} (h : S ⊆ T) :
    (sIntegerRing F S)ˣ →* (sIntegerRing F T)ˣ :=
  let hs : sIntegerRing F S ≤ sIntegerRing F T :=
    fun _ hx w hw ↦ hx w (fun hm ↦ hw (h hm))
  Units.map (Subring.inclusion hs)

@[simp] theorem sUnitInclusion_toField {S T : Finset (Place F)} (h : S ⊆ T)
    (u : (sIntegerRing F S)ˣ) :
    sUnitToField F T (sUnitInclusion F h u) = sUnitToField F S u := rfl

/-- The finite-stage transition is represented by summation over the
quotient of the larger S-unit group by the smaller one. The global coset
term reduces to the local theta value and the new-place integer tests. -/
theorem hasSum_sLocalThetaPaddingCosets {S T : Finset (Place F)} (hST : S ⊆ T)
    (f : sLocalBruhatImage F S) (g : (SAdeles F T)ˣ)
    (r : ((sIntegerRing F T)ˣ ⧸ (sUnitInclusion F hST).range) → (sIntegerRing F T)ˣ)
    (hr : ∀ q, QuotientGroup.mk (r q) = q) :
    HasSum (fun q ↦ globalThetaPaddingCosetTerm F S f (sLocalEmbed F T g).val (sUnitToField F T (r q)))
      (sLocalThetaOperator F T (sLocalBruhatTransition F hST f) (QuotientGroup.mk g)) := by
  let j := sUnitInclusion F hST
  let G := (sLocalEmbed F T g).val
  let d := sUnitToField F T
  let fT := sLocalBruhatTransition F hST f
  let a (u : (sIntegerRing F T)ˣ) :=
    sLocalBruhatRestriction F T f.val (sIntegerDiagonal F T u.val * g.val)
  have hsum : Summable a := Additive.toMul.summable_iff.mp
    (sLocalTheta_restriction_summable F T f.val g).of_norm
  have hA : (∑' u, a u) = sLocalThetaOperator F T fT (QuotientGroup.mk g) :=
    (Additive.toMul.tsum_eq a).symm
  have ht (u : (sIntegerRing F T)ˣ) :
      thetaSummand F (GlobalBruhat.algebraicEquiv F f.val).val G (d u) = a u := by
    let b := principalIdele F (d u)
    have hb : b ∈ sIdeleBlock F T := (principalIdele_mem_sBlock F T _).mpr ⟨u,rfl⟩
    have hG : G ∈ sIdeleBlock F T := (sLocalEmbed F T g).property
    have hBG : ∀ w ∉ T, (b * G).val.2 w ∈ w.adicCompletionIntegers F :=
      ((sIdeleBlock F T).mul_mem hb hG).1
    change GlobalBruhat.evaluation F (b * G).val fT.val = _
    rw [sLocalBruhatRestriction_reconstruct F T fT, ite_eq_left hBG, mul_one]
    change sLocalBruhatRestriction F T f.val (sAdelesProjection F T (b * G).val) = a u
    rw [Units.val_mul, map_mul, show sAdelesProjection F T G.val = g.val from sLocalEmbed_project F T g]
    rfl
  have hj : Injective j := fun u v h ↦ sUnitToField_injective F S (congrArg d h)
  rw [← hA]
  refine hasSum_cosets_of_representatives j hj hsum r hr fun q ↦ ?_
  rw [globalThetaPaddingCosetTerm_eq]
  refine tsum_congr fun u ↦ ?_
  rw [← ht, map_mul]
  rfl

theorem summable_norm_sLocalThetaPaddingCosets {S T : Finset (Place F)} (hST : S ⊆ T)
    (f : sLocalBruhatImage F S) (g : (SAdeles F T)ˣ)
    (r : ((sIntegerRing F T)ˣ ⧸ (sUnitInclusion F hST).range) → (sIntegerRing F T)ˣ)
    (hr : ∀ q, QuotientGroup.mk (r q) = q) :
    Summable (fun q ↦ ‖globalThetaPaddingCosetTerm F S f (sLocalEmbed F T g).val (sUnitToField F T (r q))‖) :=
  (hasSum_sLocalThetaPaddingCosets F hST f g r hr).summable.norm

private theorem sUnitFieldRange_insert_iff (S : Finset (Place F)) (v : Place F) (hv : v ∉ S)
    (t : Fˣ) (ht : t ∈ (sUnitToField F (insert v S)).range) :
    t ∈ (sUnitToField F S).range ↔ v.valuation F t.val = 1 := by
  have hb := (principalIdele_mem_sBlock F (insert v S) t).mpr ht
  rw [valuation_one_iff_order_zero, show t ∈ (sUnitToField F S).range ↔
    principalIdele F t ∈ sIdeleBlock F S from (principalIdele_mem_sBlock F S t).symm,
    sIdeleBlock_mem_iff]
  refine ⟨fun h ↦ h v hv, fun h w hw ↦ ?_⟩
  by_cases he : w = v
  · exact he.symm ▸ h
  · exact (sIdeleBlock_mem_iff F (insert v S) _).mp hb w
      (by simpa only [Finset.mem_insert, not_or] using And.intro he hw)

/-- Multiplication by a representative identifies the S-units with the fiber
of its new-place valuation in the larger unit group. -/
def sUnitOnePlaceValuationFiber (S : Finset (Place F)) (v : Place F) (hv : v ∉ S)
    (a : (sIntegerRing F (insert v S))ˣ) :
    (sIntegerRing F S)ˣ ≃
      {b : (sIntegerRing F (insert v S))ˣ //
        v.valuation F (sUnitToField F (insert v S) b).val =
          v.valuation F (sUnitToField F (insert v S) a).val} := by
  let T := insert v S
  let d := sUnitToField F T
  let D := sUnitToField F S
  let j := sUnitInclusion F (Finset.subset_insert v S)
  let P := {b : (sIntegerRing F T)ˣ | v.valuation F (d b).val = v.valuation F (d a).val}
  have hval (u : (sIntegerRing F S)ˣ) : v.valuation F (D u).val = 1 :=
    (sUnitFieldRange_insert_iff F S v hv _ ⟨j u, rfl⟩).mp ⟨u, rfl⟩
  let b (u : (sIntegerRing F S)ˣ) : P := ⟨a * j u, by
    change v.valuation F (d (a * j u)).val = _
    rw [map_mul, Units.val_mul, map_mul, show d (j u) = D u from rfl, hval, mul_one]⟩
  refine Equiv.ofBijective b ⟨?_, ?_⟩
  · intro u w h
    have h' : j u = j w := mul_left_cancel (congrArg Subtype.val h)
    exact sUnitToField_injective F S (congrArg d h')
  · rintro ⟨x, hx⟩
    have hz : v.valuation F (d (x / a)).val = 1 := by
      have hn : v.valuation F (d a).val ≠ 0 :=
        (v.valuation F).ne_zero_iff.mpr (Units.ne_zero _)
      rw [map_div, Units.val_div_eq_div_val, map_div₀, show v.valuation F (d x).val =
        v.valuation F (d a).val from hx, div_self hn]
    obtain ⟨u, hu⟩ := (sUnitFieldRange_insert_iff F S v hv _ ⟨x / a, rfl⟩).mpr hz
    refine ⟨u, Subtype.ext ?_⟩
    change a * j u = x
    have he : j u = x / a := sUnitToField_injective F T hu
    rw [he, mul_comm, div_mul_cancel]

@[simp] theorem sUnitOnePlaceValuationFiber_apply
    (S : Finset (Place F)) (v : Place F) (hv : v ∉ S) (a : (sIntegerRing F (insert v S))ˣ)
    (u : (sIntegerRing F S)ˣ) :
    (sUnitOnePlaceValuationFiber F S v hv a u).val =
      a * sUnitInclusion F (Finset.subset_insert v S) u := rfl

/-- A summable series over the larger unit group can be grouped by the new-place
valuation. Each inner sum is indexed by the smaller unit group. -/
theorem sUnitOnePlace_tsum (S : Finset (Place F)) (v : Place F) (hv : v ∉ S)
    (a : (sIntegerRing F (insert v S))ˣ → ℂ) (ha : Summable a)
    (r : range (fun u : (sIntegerRing F (insert v S))ˣ ↦
      v.valuation F (sUnitToField F (insert v S) u).val) → (sIntegerRing F (insert v S))ˣ)
    (hr : ∀ k, v.valuation F (sUnitToField F (insert v S) (r k)).val = k.val) :
    (∑' u, a u) = ∑' k, ∑' u, a (r k * sUnitInclusion F (Finset.subset_insert v S) u) := by
  let val (u : (sIntegerRing F (insert v S))ˣ) :=
    v.valuation F (sUnitToField F (insert v S) u).val
  let index (u : (sIntegerRing F (insert v S))ˣ) : range val :=
    ⟨val u, mem_range_self u⟩
  rw [← (ha.hasSum.tsum_fiberwise index).tsum_eq]
  apply tsum_congr
  intro k
  let e : index ⁻¹' {k} ≃ {b // val b = val (r k)} :=
    Equiv.subtypeEquivRight (fun u ↦ by
      change index u = k ↔ val u = val (r k)
      rw [show val (r k) = k.val from hr k]
      exact ⟨congrArg Subtype.val, fun h ↦ Subtype.ext (show (index u).val = k.val from h)⟩)
  rw [← ((sUnitOnePlaceValuationFiber F S v hv (r k)).trans e.symm).tsum_eq]
  rfl

/-- At a stage obtained by adjoining one finite place, the difference of the two
theta evaluations at the inserted idele and its inverse-uniformizer shift recovers
the original stage's theta evaluation. -/
theorem sLocalTheta_onePlace_probe (S : Finset (Place F)) (v : Place F) (hv : v ∉ S)
    (f : sLocalBruhatImage F S) (g : (SAdeles F S)ˣ) :
    let T := insert v S
    let z := (sLocalEmbed F S g).val
    let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
    sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T f.val)
        (Units.map (sAdelesProjection F T).toMonoidHom z) -
      sLocalThetaOnIdeles F T (sLocalBruhatRestriction F T f.val)
        (Units.map (sAdelesProjection F T).toMonoidHom (z * c)) =
      sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g := by
  classical
  dsimp only
  let T := insert v S
  let z := (sLocalEmbed F S g).val
  let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
  let d := sUnitToField F T
  let D := sUnitToField F S
  let U := Additive (sIntegerRing F T)ˣ
  let b (t : Fˣ) := sLocalBruhatRestriction F S f.val
    (sAdelesProjection F S (principalIdele F t).val * g.val)
  let a (y : Idele F) (u : U) :=
    sLocalBruhatRestriction F T f.val (sIntegerDiagonal F T u.toMul.val *
      (projectUnits F T y).val)
  change (∑' u, a z u) - (∑' u, a (z * c) u) = _
  have hST : S ⊆ T := Finset.subset_insert _ _
  let fT := sLocalBruhatTransition F hST f
  have hproj_c : sAdelesProjection F S c.val = 1 := by
    apply Prod.ext (by rfl)
    funext w
    exact singleFiniteIdele_outside F v w.val (ne_of_mem_of_not_mem w.property hv) _
  have hcut (e : Bool) (u : U) :
      a (if e then z * c else z) u =
        b (d u.toMul) * (if (if e then v.valuation F (d u.toMul).val < 1
                                  else v.valuation F (d u.toMul).val ≤ 1)
                        then 1 else 0) := by
    let t := d u.toMul
    let y := if e then z * c else z
    let x := principalIdele F t * y
    have hu : ∀ w ∉ T, ideleOrder F (principalIdele F t) w = 0 :=
      (sIdeleBlock_mem_iff F T _).mp (sPrincipal F T u.toMul).property
    have hy (w : Place F) (hw : w ≠ v) (hws : w ∉ S) : y.val.2 w = 1 := by
      have hz := sLocalEmbed_outside_one F S g w hws
      have hc := singleFiniteIdele_outside F v w hw (chosenFiniteUniformizer F v)⁻¹
      cases e
      · exact hz
      · change z.val.2 w * c.val.2 w = 1
        rw [hz, show c.val.2 w = 1 from hc, mul_one]
    have hx (w : Place F) (hw : w ∉ T) :
        x.val.2 w ∈ w.adicCompletionIntegers F := by
      have hws : w ∉ S := fun h ↦ hw (hST h)
      have hwv : w ≠ v := fun h ↦ hw (h ▸ Finset.mem_insert_self v S)
      change Valued.v ((principalIdele F t).val.2 w * y.val.2 w) ≤ 1
      rw [hy w hwv hws, mul_one, (ideleOrder_eq_zero_iff F _ w).mp (hu w hw)]
    have hxv : x.val.2 v ∈ v.adicCompletionIntegers F ↔
        (if e then v.valuation F t.val < 1 else v.valuation F t.val ≤ 1) := by
      have hz := sLocalEmbed_outside_one F S g v hv
      cases e
      · change Valued.v (algebraMap F (v.adicCompletion F) t.val * z.val.2 v) ≤ 1 ↔
          v.valuation F t.val ≤ 1
        have he : Valued.v (algebraMap F (v.adicCompletion F) t.val) = v.valuation F t.val :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) t.val
        rw [hz, mul_one, he]
      · change algebraMap F (v.adicCompletion F) t.val * (z.val.2 v * c.val.2 v) ∈
          v.adicCompletionIntegers F ↔ _
        rw [hz, one_mul, show c.val.2 v = _ from singleFiniteIdele_at F v _]
        exact finitePlace_mul_inverseUniformizer_integral_iff F v t
    have hxs : (∀ w ∉ S, x.val.2 w ∈ w.adicCompletionIntegers F) ↔
        x.val.2 v ∈ v.adicCompletionIntegers F := by
      refine ⟨fun h ↦ h v hv, fun h w hws ↦ ?_⟩
      by_cases he : w = v
      · exact he.symm ▸ h
      · exact hx w (by simpa only [T, Finset.mem_insert, not_or] using And.intro he hws)
    have hproj : sAdelesProjection F S y.val = g.val := by
      cases e
      · exact sLocalEmbed_project F S g
      · change sAdelesProjection F S (z.val * c.val) = g.val
        rw [map_mul, hproj_c, mul_one]
        exact sLocalEmbed_project F S g
    have h₁ := sLocalBruhatRestriction_reconstruct F T fT x.val
    have h₂ := sLocalBruhatRestriction_reconstruct F S f x.val
    change sLocalBruhatRestriction F T f.val (sAdelesProjection F T x.val) = _
    change GlobalBruhat.evaluation F x.val f.val =
      sLocalBruhatRestriction F T f.val (sAdelesProjection F T x.val) *
        (if ∀ w ∉ T, x.val.2 w ∈ w.adicCompletionIntegers F then 1 else 0) at h₁
    rw [ite_eq_left hx, mul_one] at h₁
    rw [← h₁, h₂, hxs, hxv, show x.val = (principalIdele F t).val * y.val from rfl,
      map_mul, hproj]
    split_ifs <;> rfl
  have hsub (u : U) : a z u - a (z * c) u =
      ({u : U | v.valuation F (d u.toMul).val = 1} : Set U).indicator
        (fun u ↦ b (d u.toMul)) u := by
    have h₀ := hcut false u
    have h₁ := hcut true u
    simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
    rw [h₀, h₁]
    rcases lt_trichotomy (v.valuation F (d u.toMul).val) 1 with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [h.not_ge, h.not_gt, h.ne']
  have hsum (y : Idele F) : Summable (a y) :=
    (sLocalTheta_restriction_summable F T f.val (projectUnits F T y)).of_norm
  rw [← (hsum z).tsum_sub (hsum (z * c)), tsum_congr hsub, ← tsum_subtype]
  let P := {u : U | v.valuation F (d u.toMul).val = 1}
  let j := sUnitInclusion F hST
  let i (u : Additive (sIntegerRing F S)ˣ) : P :=
    ⟨Additive.ofMul (j u.toMul), by
      change v.valuation F (D u.toMul).val = 1
      exact (sUnitFieldRange_insert_iff F S v hv _ ⟨j u.toMul, rfl⟩).mp ⟨u.toMul, rfl⟩⟩
  have hi (u) : d (i u).val.toMul = D u.toMul := rfl
  have hib : Bijective i := by
    refine ⟨fun u w h ↦ Additive.toMul.injective (sUnitToField_injective F S
      ((hi u).symm.trans ((congrArg (fun x : P ↦ d x.val.toMul) h).trans (hi w)))), ?_⟩
    intro w
    obtain ⟨u, hu⟩ := (sUnitFieldRange_insert_iff F S v hv _ ⟨w.val.toMul, rfl⟩).mpr w.property
    exact ⟨Additive.ofMul u, Subtype.ext (Additive.toMul.injective
      (sUnitToField_injective F T ((hi (Additive.ofMul u)).trans hu)))⟩
  rw [← (Equiv.ofBijective i hib).tsum_eq]
  exact tsum_congr (fun u ↦ by change b (d (i u).val.toMul) = _; rw [hi]; rfl)

/-- Point evaluation is continuous on the actual S-local theta quotient. -/
def sLocalThetaQuotientEval (S : Finset (Place F)) (g : (SAdeles F S)ˣ) :
    SLocalThetaQuotient F S →L[ℂ] ℂ := by
  let P := (sLocalThetaOperator F S).ker
  let A := (sLocalThetaEval F S g).comp (sLocalBruhatImage F S).subtype
  have hA : Continuous A := by
    obtain ⟨p, hp, hb⟩ := sLocalTheta_log_seminorm F S
    let w := (1 + |Real.log (sLocalIdeleNorm F S g)|) ^ (Fintype.card (SLogIndex F S) - 1)
    let c : NNReal := ⟨w, by dsimp [w]; positivity⟩
    refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp A fun _ ↦
      Seminorm.continuous_of_le (q := c • p) (continuous_const.mul hp) ?_
    intro f
    change ‖A f‖ ≤ w * p f
    rw [mul_comm]
    exact hb f g
  refine P.liftQL ⟨A, hA⟩ (fun f hf ↦ ?_)
  exact LinearMap.mem_ker.mpr (congrFun (LinearMap.mem_ker.mp hf) (QuotientGroup.mk g))

@[simp] theorem sLocalThetaQuotientEval_mk (S : Finset (Place F)) (g : (SAdeles F S)ˣ)
    (f : sLocalBruhatImage F S) :
    sLocalThetaQuotientEval F S g (Submodule.Quotient.mk f) =
      sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g := rfl

/-- Each point evaluation on the smaller quotient extends continuously to the
one-place enlargement by the difference of its two shifted evaluations. -/
theorem sLocalThetaQuotientEval_extend_onePlace
    (S : Finset (Place F)) (v : Place F) (hv : v ∉ S) (g : (SAdeles F S)ˣ) :
    let T := insert v S
    let z := (sLocalEmbed F S g).val
    let c := singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹
    (sLocalThetaQuotientEval F T (projectUnits F T z) -
      sLocalThetaQuotientEval F T (projectUnits F T (z * c))).comp
        (sLocalThetaTransition F (Finset.subset_insert v S)) =
      sLocalThetaQuotientEval F S g := by
  dsimp only
  ext q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact sLocalTheta_onePlace_probe F S v hv f g

/-- For a compactly supported locally constant test on a product, the difference of
two slices related by a fixed nonzero dilation is supported in a bounded interval
of integer valuation indices. The interval is independent of the other coordinates. -/
theorem locallyConstantTestSection_sub_support_finite
    {X K I : Type*} [TopologicalSpace X] [NormedField K]
    (f : locallyConstantTests (X × K)) (c : K) (hc : c ≠ 0)
    (i : I → ℤ) (hi : Injective i) (e : I → K) (p : ℝ) (hp : 1 < p)
    (he : ∀ k, ‖e k‖ = p ^ i k) :
    (support fun k ↦ locallyConstantTestSection f (e k) -
      locallyConstantTestSection f (e k * c)).Finite := by
  let sec := locallyConstantTestSection f
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((locallyConstantTestSection_locallyConstant f).eventually_eq 0)
  have hnear (z : K) (hz : ‖z‖ < ε) : sec z = sec 0 :=
    hsmall (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  obtain ⟨R, hR⟩ := f.property.2.bddAbove_image (f := fun a : X × K ↦ ‖a.2‖)
    continuous_snd.norm.continuousOn
  have hfar (z : K) (hz : R < ‖z‖) : sec z = 0 := by
    apply Subtype.ext
    funext x
    change f.val (x, z) = 0
    exact image_eq_zero_of_notMem_tsupport fun hx ↦
      hz.not_ge (hR ⟨(x, z), hx, rfl⟩)
  have hc₀ : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max R (R / ‖c‖)) hp
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max ε⁻¹ (‖c‖ / ε)) hp
  have hlo : p ^ (-(n : ℤ)) < min ε (ε / ‖c‖) := by
    rw [zpow_neg, zpow_natCast, lt_min_iff]
    refine ⟨?_, ?_⟩
    · exact (inv_lt_comm₀ (by positivity) hε).mpr ((le_max_left _ _).trans_lt hn)
    · exact (inv_lt_comm₀ (by positivity) (div_pos hε hc₀)).mpr
        (by rw [inv_div]; exact (le_max_right _ _).trans_lt hn)
  refine ((Set.finite_Icc (-(n : ℤ)) (m : ℤ)).preimage hi.injOn).subset ?_
  intro k hk
  by_contra h
  have h' : ¬ (-(n : ℤ) ≤ i k ∧ i k ≤ (m : ℤ)) := h
  push Not at h'
  apply hk
  change sec (e k) - sec (e k * c) = 0
  by_cases hl : (-(n : ℤ)) ≤ i k
  · have hr := (zpow_lt_zpow_iff_right₀ hp).mpr (h' hl)
    rw [zpow_natCast] at hr
    have h₁ : R < ‖e k‖ := by
      rw [he]
      exact (le_max_left _ _).trans_lt (hm.trans hr)
    have h₂ : R < ‖e k * c‖ := by
      rw [norm_mul, ← div_lt_iff₀ hc₀, he]
      exact (le_max_right _ _).trans_lt (hm.trans hr)
    rw [hfar _ h₁, hfar _ h₂, sub_self]
  · have hlt := ((zpow_le_zpow_iff_right₀ hp).mpr (le_of_not_ge hl)).trans_lt hlo
    have h₁ : ‖e k‖ < ε := (he k).symm ▸ hlt.trans_le (min_le_left _ _)
    have h₂ : ‖e k * c‖ < ε := by
      rw [norm_mul, ← lt_div_iff₀ hc₀, he]
      exact hlt.trans_le (min_le_right _ _)
    rw [hnear _ h₁, hnear _ h₂, sub_self]

/-- The same finite support bound applies to arbitrary representatives of
valuation indices in a finite completion, with the inverse uniformizer shift. -/
theorem finitePlace_section_sub_support_finite
    {X I : Type*} [TopologicalSpace X] (v : Place F)
    (f : locallyConstantTests (X × v.adicCompletion F))
    (i : I → ℤ) (hi : Injective i) (e : I → v.adicCompletion F)
    (he : ∀ k, Valued.v (e k) = WithZero.exp (i k)) :
    (support fun k ↦ locallyConstantTestSection f (e k) -
      locallyConstantTestSection f (e k *
        ((chosenFiniteUniformizer F v)⁻¹ : (v.adicCompletion F)ˣ).val)).Finite := by
  let q : ℝ := Ideal.absNorm v.asIdeal
  refine locallyConstantTestSection_sub_support_finite f _ (Units.ne_zero _) i hi e q
    (by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v) ?_
  intro k
  rw [FinitePlace.norm_def, he,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  norm_cast


/-- The signed slices can be summed over the valuation image of the enlarged
unit group. For any choice of representatives, only finitely many slices contribute. -/
theorem sUnitOnePlace_section_sub_support_finite {X : Type*} [TopologicalSpace X]
    (S : Finset (Place F)) (v : Place F) (f : locallyConstantTests (X × v.adicCompletion F))
    (r : range (fun u : (sIntegerRing F (insert v S))ˣ ↦
      v.valuation F (sUnitToField F (insert v S) u).val) → (sIntegerRing F (insert v S))ˣ)
    (hr : ∀ k, v.valuation F (sUnitToField F (insert v S) (r k)).val = k.val) :
    let e k := algebraMap F (v.adicCompletion F) (sUnitToField F (insert v S) (r k)).val
    (support fun k ↦ locallyConstantTestSection f (e k) -
      locallyConstantTestSection f (e k *
        ((chosenFiniteUniformizer F v)⁻¹ : (v.adicCompletion F)ˣ).val)).Finite := by
  let I := range (fun u : (sIntegerRing F (insert v S))ˣ ↦
    v.valuation F (sUnitToField F (insert v S) u).val)
  have hn (k : I) : k.val ≠ 0 := by
    rcases k.property with ⟨u, hu⟩
    rw [← hu]
    exact (v.valuation F).ne_zero_iff.mpr (Units.ne_zero _)
  let i (k : I) : ℤ := (WithZero.unzero (hn k)).toAdd
  have hi (k : I) : WithZero.exp (i k) = k.val := WithZero.coe_unzero (hn k)
  refine finitePlace_section_sub_support_finite F v f i ?_ _ ?_
  · intro k j h
    apply Subtype.ext
    rw [← hi k, ← hi j, h]
  · intro k
    rw [show Valued.v (algebraMap F (v.adicCompletion F) (sUnitToField F (insert v S) (r k)).val) =
      v.valuation F (sUnitToField F (insert v S) (r k)).val from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) _, hr, hi]


end

end Masullo
