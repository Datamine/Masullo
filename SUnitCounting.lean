import SUnitLogLattice
import LatticeEstimates

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private theorem finite_preimage_card_le_of_finite_ker
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hker : (f.ker : Set A).Finite)
    {T : Set B} (hT : T.Finite) :
    (f ⁻¹' T).Finite ∧ (f ⁻¹' T).ncard ≤ T.ncard * (f.ker : Set A).ncard := by
  let r : f.range → A := fun c => c.property.choose
  have hr (c : f.range) : f (r c) = c.val := c.property.choose_spec
  let k (x : A) : f.range := ⟨f x, ⟨x, rfl⟩⟩
  let e (x : (f ⁻¹' T : Set A)) : T × f.ker :=
    ⟨⟨f x.val, x.property⟩, ⟨x.val - r (k x.val), by
      change f (x.val - r (k x.val)) = 0
      rw [map_sub, hr]
      exact sub_self _⟩⟩
  have he : Injective e := by
    intro x y h
    have h₁ : k x.val = k y.val := Subtype.ext (congrArg (fun p : T × f.ker => p.1.val) h)
    have h₂ : x.val - r (k x.val) = y.val - r (k y.val) :=
      congrArg (fun p : T × f.ker => p.2.val) h
    rw [h₁] at h₂
    exact Subtype.ext (sub_left_inj.mp h₂)
  letI : Fintype T := hT.fintype
  letI : Fintype (f.ker : Set A) := hker.fintype
  letI : Finite (f ⁻¹' T : Set A) := Finite.of_injective e he
  letI : Fintype (f ⁻¹' T : Set A) := Fintype.ofFinite _
  refine ⟨Set.toFinite _, ?_⟩
  have h := Fintype.card_le_of_injective e he
  change Fintype.card (f ⁻¹' T : Set A) ≤ Fintype.card (T × (f.ker : Set A)) at h
  simpa only [Fintype.card_prod, Set.fintypeCard_eq_ncard] using h

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)

def sUnitSmallSet (S : Finset (Place F)) (g : Idele F) : Set (Additive (sIntegerRing F S)ˣ) :=
  {u | ∀ v, sLogVector F S (principalIdele F (sUnitToField F S u.toMul) * g) v ≤ 0}

/-- The translated S-units with every normalized logarithm at most the cutoff. -/
def sUnitLogBox (S : Finset (Place F)) (g : Idele F) (r : ℝ) :
    Set (Additive (sIntegerRing F S)ˣ) :=
  {u | ∀ v, sLogVector F S (principalIdele F (sUnitToField F S u.toMul) * g) v ≤ r}

/-- All translates of the S-unit lattice satisfy the same dimension-power bound.
The logarithmic product formula bounds the omitted coordinate. -/
theorem sUnitLogBox_count (S : Finset (Place F)) :
    ∃ C : ℝ, C > 0 ∧ ∀ g : Idele F, g ∈ sIdeleBlock F S → ∀ r : ℝ, 0 ≤ r →
      (sUnitLogBox F S g r).Finite ∧
      ((sUnitLogBox F S g r).ncard : ℝ) ≤ C *
        (1 + |Real.log (ideleNorm F g)| + ((Fintype.card (SLogIndex F S) : ℝ) + 1) * r) ^
          (Fintype.card (SLogIndex F S) - 1) := by
  let f := sUnitReducedLog F S
  let L := LinearMap.range f
  letI : DiscreteTopology L := sUnitReducedLog_image_discrete F S
  have hker : (f.toAddMonoidHom.ker : Set (Additive (sIntegerRing F S)ˣ)).Finite :=
    (sUnitReducedLog_ker_finite F S).image Additive.ofMul |>.subset (by
      intro u hu
      exact ⟨u.toMul, hu, rfl⟩)
  obtain ⟨D, hD, hball⟩ := lattice_closedBall_count L
  let multiplicity := (f.toAddMonoidHom.ker : Set (Additive (sIntegerRing F S)ˣ)).ncard
  refine ⟨D * (multiplicity + 1), by positivity, ?_⟩
  intro g hg r hr
  let U := sUnitLogBox F S g r
  let t := Real.log (ideleNorm F g)
  let n := Fintype.card (SLogIndex F S)
  let R := 1 + |t| + ((n : ℝ) + 1) * r
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg t, mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) hr]
  have hlower (u : U) (v : SLogIndex F S) :
      t - (n : ℝ) * r ≤ sLogVector F S
        (principalIdele F (sUnitToField F S u.val.toMul) * g) v := by
    let a := principalIdele F (sUnitToField F S u.val.toMul) * g
    have hb : a ∈ sIdeleBlock F S :=
      (sIdeleBlock F S).mul_mem (sPrincipal F S u.val.toMul).property hg
    have he : ∑ w, sLogVector F S a w = t := by
      rw [sLogVector_sum F S a hb]
      change Real.log (ideleNorm F (principalIdele F (sUnitToField F S u.val.toMul) * g)) = _
      rw [map_mul, ideleNorm_principal, one_mul]
    have hs : ∑ w ∈ Finset.univ.erase v, sLogVector F S a w ≤ (n : ℝ) * r := calc
      _ ≤ ∑ _w ∈ Finset.univ.erase v, r :=
        Finset.sum_le_sum fun w _ => u.property w
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hr
    have hv := (Finset.sum_erase_add Finset.univ (sLogVector F S a) (Finset.mem_univ v)).trans he
    change _ ≤ sLogVector F S a v
    linarith
  by_cases hU : U.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hU
    let T := Metric.closedBall 0 R ∩ (L : Set (ReducedSLogIndex F S → ℝ))
    have hp := hball R hR
    have hF := finite_preimage_card_le_of_finite_ker f.toAddMonoidHom hker hp.1
    have hU' : ∀ u ∈ U, u - u₀ ∈ f.toAddMonoidHom ⁻¹' T := by
      intro u hu
      refine ⟨?_, ⟨u - u₀, rfl⟩⟩
      change dist (f (u - u₀)) 0 ≤ R
      rw [dist_zero_right, pi_norm_le_iff_of_nonneg (zero_le_one.trans hR)]
      intro v
      let i := reducedLogIndexEmbed F S v
      have ha := hlower ⟨u, hu⟩ i
      have ha₀ := hlower ⟨u₀, hu₀⟩ i
      have hb := hu i
      have hb₀ := hu₀ i
      rw [map_sub, Pi.sub_apply, Real.norm_eq_abs, abs_le]
      change -R ≤ sLogVector F S (principalIdele F (sUnitToField F S u.toMul)) i -
          sLogVector F S (principalIdele F (sUnitToField F S u₀.toMul)) i ∧
        sLogVector F S (principalIdele F (sUnitToField F S u.toMul)) i -
          sLogVector F S (principalIdele F (sUnitToField F S u₀.toMul)) i ≤ R
      have h₁ : sLogVector F S (principalIdele F (sUnitToField F S u.toMul) * g) i =
          sLogVector F S (principalIdele F (sUnitToField F S u.toMul)) i + sLogVector F S g i :=
        congrFun (sLogVector_mul F S _ _) i
      have h₂ : sLogVector F S (principalIdele F (sUnitToField F S u₀.toMul) * g) i =
          sLogVector F S (principalIdele F (sUnitToField F S u₀.toMul)) i + sLogVector F S g i :=
        congrFun (sLogVector_mul F S _ _) i
      rw [h₁] at ha hb
      rw [h₂] at ha₀ hb₀
      dsimp [R]
      constructor <;> linarith [neg_abs_le t]
    have hshift : Injective (fun u : Additive (sIntegerRing F S)ˣ => u - u₀) :=
      fun _ _ h => sub_left_inj.mp h
    have hfin : U.Finite := (hF.1.preimage hshift.injOn).subset hU'
    refine ⟨hfin, ?_⟩
    have hUcard : U.ncard ≤ (f.toAddMonoidHom ⁻¹' T).ncard :=
      Set.ncard_le_ncard_of_injOn (fun u => u - u₀) hU' hshift.injOn hF.1
    have hcard : (U.ncard : ℝ) ≤ (T.ncard : ℝ) * multiplicity := by
      exact_mod_cast hUcard.trans hF.2
    rw [← card_reducedSLogIndex F S]
    calc
      _ ≤ (T.ncard : ℝ) * multiplicity := hcard
      _ ≤ (D * R ^ Fintype.card (ReducedSLogIndex F S)) * multiplicity :=
        mul_le_mul_of_nonneg_right hp.2 (Nat.cast_nonneg _)
      _ ≤ D * (multiplicity + 1) * R ^ Fintype.card (ReducedSLogIndex F S) := by
        have hn : (multiplicity : ℝ) ≤ multiplicity + 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ D * R ^ Fintype.card (ReducedSLogIndex F S) by positivity)]
  · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hU
    have hfin : U.Finite := he.symm ▸ finite_empty
    refine ⟨hfin, ?_⟩
    change (U.ncard : ℝ) ≤ _
    rw [he, ncard_empty, Nat.cast_zero]
    positivity

/-- The unit cutoff count for moduli below `exp (-1)`. -/
theorem sUnitSmall_count (S : Finset (Place F)) :
    ∃ C : ℝ, C > 0 ∧ ∀ g : Idele F, g ∈ sIdeleBlock F S →
      ideleNorm F g < Real.exp (-1) →
      (sUnitSmallSet F S g).Finite ∧
      ((sUnitSmallSet F S g).ncard : ℝ) ≤ C *
        |Real.log (ideleNorm F g)| ^ (Fintype.card (SLogIndex F S) - 1) := by
  obtain ⟨C, hC, h⟩ := sUnitLogBox_count F S
  let d := Fintype.card (SLogIndex F S) - 1
  refine ⟨C * 2 ^ d, by positivity, fun g hg hmod => ?_⟩
  obtain ⟨hfin, hbound⟩ := h g hg 0 le_rfl
  have ht : Real.log (ideleNorm F g) < -1 := by
    rw [← Real.log_exp (-1)]
    exact Real.log_lt_log (ideleNorm_pos F g) hmod
  have ha : 1 ≤ |Real.log (ideleNorm F g)| :=
    (show 1 ≤ -Real.log (ideleNorm F g) by linarith).trans (neg_le_abs _)
  refine ⟨hfin, hbound.trans ?_⟩
  simp only [mul_zero, add_zero]
  rw [mul_assoc, ← mul_pow]
  gcongr
  linarith

/-- The additive cutoff from (A.4.1.2). The Archimedean conditions use
ordinary norms, which give the same unit box as the normalized norms. -/
def sAdelicUnitBox (S : Finset (Place F)) : Set (SAdeles F S) :=
  {x | (∀ v : InfinitePlace F, ‖x.1 v‖ ≤ 1) ∧
    ∀ v : S, x.2 v ∈ v.val.adicCompletionIntegers F}

def sUnitCutoff (S : Finset (Place F)) (x : SAdeles F S) : ℝ :=
  if x ∈ sAdelicUnitBox F S then 1 else 0

theorem sAdelicUnitBox_compact (S : Finset (Place F)) : IsCompact (sAdelicUnitBox F S) := by
  have ha (v : InfinitePlace F) : IsCompact {x : v.Completion | ‖x‖ ≤ 1} := by
    let e := InfinitePlace.Completion.extensionEmbedding v
    have he := InfinitePlace.Completion.isometry_extensionEmbedding v
    have hpre : {x : v.Completion | ‖x‖ ≤ 1} = e ⁻¹' Metric.closedBall 0 1 := by
      ext x
      exact (show ‖x‖ ≤ 1 ↔ dist (e x) 0 ≤ 1 from by
        rw [← map_zero e, he.dist_eq, dist_zero_right])
    rw [hpre]
    exact he.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)
  have hb (v : S) : IsCompact (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)) :=
    finitePlaceIntegral_compact F v.val
  have h : sAdelicUnitBox F S =
      (Set.pi univ (fun v : InfinitePlace F => {x : v.Completion | ‖x‖ ≤ 1})) ×ˢ
        Set.pi univ (fun v : S => (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F))) := by
    ext x
    exact and_congr Set.mem_univ_pi.symm Set.mem_univ_pi.symm
  rw [h]
  exact (isCompact_univ_pi ha).prod (isCompact_univ_pi hb)

theorem sAdelicUnitBox_interior (S : Finset (Place F)) :
    (interior (sAdelicUnitBox F S)).Nonempty := by
  let A := Set.pi univ (fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1)
  let B := Set.pi univ (fun v : S => (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)))
  have ho : IsOpen (A ×ˢ B) :=
    (isOpen_set_pi finite_univ (fun _ _ => Metric.isOpen_ball)).prod
      (isOpen_set_pi finite_univ (fun v _ => Valued.isOpen_valuationSubring (v.val.adicCompletion F)))
  have hsub : A ×ˢ B ⊆ sAdelicUnitBox F S := by
    rintro x ⟨ha, hb⟩
    refine ⟨fun v => ?_, Set.mem_univ_pi.mp hb⟩
    have h : dist (x.1 v) 0 < 1 := Set.mem_univ_pi.mp ha v
    rw [dist_zero_right] at h
    exact h.le
  refine ⟨0, interior_maximal hsub ho ⟨?_, ?_⟩⟩
  · exact Set.mem_univ_pi.mpr fun v => Metric.mem_ball_self zero_lt_one
  · exact Set.mem_univ_pi.mpr fun v => zero_mem (v.val.adicCompletionIntegers F)

theorem sUnitCutoff_properties (S : Finset (Place F)) :
    HasCompactSupport (sUnitCutoff F S) ∧ (∀ x, 0 ≤ sUnitCutoff F S x ∧ sUnitCutoff F S x ≤ 1) ∧
      ContinuousOn (sUnitCutoff F S) (sAdelicUnitBox F S) ∧
      ContinuousOn (sUnitCutoff F S) (sAdelicUnitBox F S)ᶜ := by
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  have h : Function.support (sUnitCutoff F S) = sAdelicUnitBox F S := by
    ext x
    by_cases hx : x ∈ sAdelicUnitBox F S <;> simp [sUnitCutoff, hx]
  refine ⟨?_, fun x => ?_, ?_, ?_⟩
  · change IsCompact (closure (Function.support (sUnitCutoff F S)))
    rw [h, (sAdelicUnitBox_compact F S).isClosed.closure_eq]
    exact sAdelicUnitBox_compact F S
  · by_cases hx : x ∈ sAdelicUnitBox F S <;> simp [sUnitCutoff, hx]
  · have h₁ : ContinuousOn (fun _ : SAdeles F S => (1 : ℝ)) (sAdelicUnitBox F S) :=
      continuous_const.continuousOn
    exact h₁.congr fun _ hx => by rw [sUnitCutoff, ite_eq_left hx]
  · have h₀ : ContinuousOn (fun _ : SAdeles F S => (0 : ℝ)) (sAdelicUnitBox F S)ᶜ :=
      continuous_const.continuousOn
    exact h₀.congr fun x hx => by
      have hnot : x ∉ sAdelicUnitBox F S := hx
      rw [sUnitCutoff, ite_eq_right hnot]

private theorem sLogVector_nonpos_iff_box (S : Finset (Place F)) (a : Idele F) :
    (∀ v, sLogVector F S a v ≤ 0) ↔
      sAdelesProjection F S a.val ∈ sAdelicUnitBox F S := by
  have har (v : InfinitePlace F) :
      sLogVector F S a (Sum.inl v) ≤ 0 ↔ ‖a.val.1 v‖ ≤ 1 := by
    change (v.mult : ℝ) * Real.log ‖a.val.1 v‖ ≤ 0 ↔ _
    have hvm : 0 < (v.mult : ℝ) := Nat.cast_pos.mpr InfinitePlace.mult_pos
    have hpos : 0 < ‖a.val.1 v‖ := by
      have he := congrArg (fun x : Adeles F => x.1 v) a.val_inv
      exact norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one he)
    have h : (v.mult : ℝ) * Real.log ‖a.val.1 v‖ ≤ 0 ↔ Real.log ‖a.val.1 v‖ ≤ 0 := by
      constructor
      · intro hn
        exact le_of_not_gt fun hp => not_lt_of_ge hn (mul_pos hvm hp)
      · exact mul_nonpos_of_nonneg_of_nonpos hvm.le
    exact h.trans (Real.log_nonpos_iff hpos.le)
  have hfin (v : S) :
      sLogVector F S a (Sum.inr v) ≤ 0 ↔ a.val.2 v ∈ v.val.adicCompletionIntegers F := by
    change Real.log ‖a.val.2 v‖ ≤ 0 ↔ _
    have hpos : 0 < ‖a.val.2 v‖ := by
      have he := congrArg (fun x : Adeles F => x.2 v) a.val_inv
      exact norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one he)
    rw [Real.log_nonpos_iff hpos.le, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff
  constructor
  · intro h
    exact ⟨fun v => (har v).mp (h (Sum.inl v)), fun v => (hfin v).mp (h (Sum.inr v))⟩
  · rintro ⟨ha, hf⟩ v
    cases v with
    | inl v => exact (har v).mpr (ha v)
    | inr v => exact (hfin v).mpr (hf v)

/-- The actual S-unit sum in (A.4.1.3), with a uniform constant for
all S-local ideles of sufficiently small modulus. -/
theorem sUnitCutoff_sum_bound (S : Finset (Place F)) :
    ∃ C : ℝ, C > 0 ∧ ∀ g : (SAdeles F S)ˣ, sLocalIdeleNorm F S g < Real.exp (-1) →
      (∑' u : Additive (sIntegerRing F S)ˣ,
        sUnitCutoff F S (sIntegerDiagonal F S u.toMul.val * g.val)) ≤
        C * |Real.log (sLocalIdeleNorm F S g)| ^ (Fintype.card (SLogIndex F S) - 1) := by
  obtain ⟨C, hC, h⟩ := sUnitSmall_count F S
  refine ⟨C, hC, fun g hg => ?_⟩
  let a := (sLocalEmbed F S g).val
  let U := sUnitSmallSet F S a
  have ha : ideleNorm F a = sLocalIdeleNorm F S g := rfl
  obtain ⟨hU, hbound⟩ := h a (sLocalEmbed F S g).property (ha.symm ▸ hg)
  have he (u : Additive (sIntegerRing F S)ˣ) :
      sUnitCutoff F S (sIntegerDiagonal F S u.toMul.val * g.val) =
        if u ∈ U then 1 else 0 := by
    have hbox := sLogVector_nonpos_iff_box F S (principalIdele F (sUnitToField F S u.toMul) * a)
    have he :
        sAdelesProjection F S ((principalIdele F (sUnitToField F S u.toMul) * a).val) =
          sIntegerDiagonal F S u.toMul.val * g.val := by
      change sAdelesProjection F S ((principalIdele F (sUnitToField F S u.toMul)).val * a.val) = _
      rw [map_mul, show sAdelesProjection F S a.val = g.val from sLocalEmbed_project F S g]
      rfl
    rw [he] at hbox
    change (if _ ∈ sAdelicUnitBox F S then (1 : ℝ) else 0) = _
    rw [← hbox]
    rfl
  have hs : ∑' u : Additive (sIntegerRing F S)ˣ, (if u ∈ U then (1 : ℝ) else 0) = U.ncard := by
    rw [tsum_eq_sum (s := hU.toFinset)]
    · rw [Set.ncard_eq_toFinset_card U hU]
      calc
        _ = ∑ _ ∈ hU.toFinset, (1 : ℝ) := Finset.sum_congr rfl fun u hu => by
          rw [ite_eq_left (hU.mem_toFinset.mp hu)]
        _ = _ := by simp
    · intro u hu
      rw [ite_eq_right (fun hx => hu (hU.mem_toFinset.mpr hx))]
  simp_rw [he]
  rw [hs]
  exact ha ▸ hbound

end

end Masullo
