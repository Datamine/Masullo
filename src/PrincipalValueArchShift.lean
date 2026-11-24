import PrincipalValueStageEmbedding

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E (S : Finset (Place F)) := SLocalThetaQuotient F S

private abbrev project (S : Finset (Place F)) : Idele F →* (SAdeles F S)ˣ :=
  Units.map (sAdelesProjection F S).toMonoidHom

private theorem ideleOrder_one (v : Place F) : ideleOrder F 1 v = 0 :=
  (ideleOrder_eq_zero_iff F 1 v).mpr (show Valued.v (1 : v.adicCompletion F) = 1 from map_one _)

private theorem ideleOrder_pow (g : Idele F) (v : Place F) (n : ℕ) :
    ideleOrder F (g^n) v = (n : ℤ) * ideleOrder F g v := by
  induction n with
  | zero => simp [ideleOrder_one]
  | succ n ih =>
    rw [pow_succ,ideleOrder_mul,ih,Nat.cast_succ,add_mul,one_mul]

private theorem ideleOrder_div (g h : Idele F) (v : Place F) :
    ideleOrder F (g/h) v = ideleOrder F g v - ideleOrder F h v := by
  have hi : ideleOrder F h⁻¹ v = -ideleOrder F h v := by
    have hz : ideleOrder F (h⁻¹ * h) v = 0 := by
      rw [inv_mul_cancel,ideleOrder_one]
    rw [ideleOrder_mul] at hz
    exact eq_neg_of_add_eq_zero_left hz
  rw [div_eq_mul_inv,ideleOrder_mul,hi,sub_eq_add_neg]

private theorem exists_pow_mem_of_open_unitSubgroup (v : Place F)
    (H : Subgroup (v.adicCompletion F)ˣ) (hH : IsOpen (H : Set (v.adicCompletion F)ˣ))
    (u : (v.adicCompletion F)ˣ) (hu : ‖u.val‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ u^n ∈ H := by
  let U := principalIntegralUnits F v
  let J := H.comap U.subtype
  letI : CompactSpace U := principalIntegralUnits_compactSpace F v
  have hJ : IsOpen (J : Set U) := hH.preimage continuous_subtype_val
  letI : DiscreteTopology (U ⧸ J) := QuotientGroup.discreteTopology hJ
  letI : Finite (U ⧸ J) := finite_of_compact_of_discrete
  let q := QuotientGroup.mk' J
  refine ⟨Nat.card (U ⧸ J), Nat.card_pos, ?_⟩
  let x : U := ⟨u,hu⟩
  have hx : q (x ^ Nat.card (U ⧸ J)) = 1 := by rw [map_pow,pow_card_eq_one']
  change x ^ Nat.card (U ⧸ J) ∈ J
  exact (QuotientGroup.eq_one_iff _).mp hx

private abbrev projectClass (S : Finset (Place F)) :
    Idele F →* SIdeleQuotient F S :=
  (QuotientGroup.mk' (sUnitImage F S)).comp (project F S)

private theorem exists_idele_with_zero_local_orders (S : Finset (Place F)) (g : Idele F) :
    ∃ h : ℕ, 0 < h ∧ ∃ z : Idele F, (∀ j : S, ideleOrder F z j.val = 0) ∧
      projectClass F S z = projectClass F S g ^ h := by
  let h := Nat.card (ClassGroup (𝓞 F))
  let k : S → ℤ := fun j ↦ ideleOrder F g j.val
  obtain ⟨u, hu⟩ := sUnitValuation_classNumber F S k
  let t := principalIdele F (sUnitToField F S u.toMul)
  refine ⟨h, Nat.card_pos, g^h / t, ?_, ?_⟩
  · intro j
    have he := congrFun hu j
    change ideleOrder F t j.val = h • k j at he
    have hx : ideleOrder F t j.val = (h : ℤ) * ideleOrder F g j.val := by
      simpa only [k, nsmul_eq_mul] using he
    rw [ideleOrder_div, ideleOrder_pow, hx, sub_self]
  · have ht : projectClass F S t = 1 := by
      change (QuotientGroup.mk' (sUnitImage F S)) (project F S t) = 1
      exact (QuotientGroup.eq_one_iff _).mpr ⟨u.toMul, rfl⟩
    rw [map_div (projectClass F S), map_pow (projectClass F S), ht, div_one]

private theorem zetaIdeleCoordinates_finite_val (S : Finset (Place F))
    (d : (SAdeles F S)ˣ) (j : S) :
    (((sLocalZetaIdeleCoordinates F S d).2 j).val) = d.val.2 j := rfl

private theorem angularLocalIdele_eq_coordinates (S : Finset (Place F))
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ) (b : ∀ j : S, H j) :
    angularLocalIdele F S H b = (sLocalZetaIdeleCoordinates F S).symm (1, fun j ↦ (b j).val) := by
  apply Units.ext
  rfl

private theorem exists_common_unit_power (S : Finset (Place F))
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (b : ∀ j : S, (j.val.adicCompletion F)ˣ) (hb : ∀ j, ‖(b j).val‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ j, b j ^ m ∈ H j := by
  have hex (j : S) : ∃ n : ℕ, 0 < n ∧ b j ^ n ∈ H j :=
    exists_pow_mem_of_open_unitSubgroup F j.val (H j) (hH j) (b j) (hb j)
  choose n hn hmem using hex
  let m := ∏ j : S, n j
  refine ⟨m, Finset.prod_pos (fun j _ ↦ hn j), fun j ↦ ?_⟩
  obtain ⟨l, hl⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ j)
  rw [show m = n j * l from hl, pow_mul]
  exact (H j).pow_mem (hmem j) _

private theorem split_idele_at_level (S : Finset (Place F))
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (d : (SAdeles F S)ˣ) (m : ℕ)
    (hm : ∀ j : S, ((sLocalZetaIdeleCoordinates F S d).2 j)^m ∈ H j) :
    d^m = sLocalArchZetaInsert F S ((sLocalZetaIdeleCoordinates F S d).1^m) *
      angularLocalIdele F S H (fun j ↦ ⟨((sLocalZetaIdeleCoordinates F S d).2 j)^m, hm j⟩) := by
  let e := sLocalZetaIdeleCoordinates F S
  apply e.injective
  rw [map_pow e, map_mul e, sLocalArchZetaInsert, angularLocalIdele_eq_coordinates]
  change (e d)^m = e (e.symm ((e d).1^m,1)) *
    e (e.symm (1,fun j ↦ ((e d).2 j)^m))
  rw [e.apply_symm_apply, e.apply_symm_apply]
  change ((e d).1^m,(e d).2^m) = ((e d).1^m * 1,1 * (fun j ↦ ((e d).2 j)^m))
  rw [mul_one, one_mul]
  rfl

private theorem exists_power_archAngular (S : Finset (Place F))
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (d : (SAdeles F S)ˣ) (hd : ∀ j : S, ‖d.val.2 j‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : (InfiniteAdeleRing F)ˣ, ∃ b : ∀ j : S, H j,
      d^m = sLocalArchZetaInsert F S a * angularLocalIdele F S H b := by
  let p := sLocalZetaIdeleCoordinates F S d
  have hp (j : S) : ‖(p.2 j).val‖ = 1 :=
    (congrArg (fun x ↦ ‖x‖) (zetaIdeleCoordinates_finite_val F S d j)).trans (hd j)
  obtain ⟨m, hm, hb⟩ := exists_common_unit_power F S H hH p.2 hp
  exact ⟨m, hm, p.1^m, fun j ↦ ⟨(p.2 j)^m, hb j⟩, split_idele_at_level F S H d m hb⟩

/-- Modulo every open integral-unit level, a positive power of the selected
uniformizer class can be represented using only archimedean coordinates.
The class number first removes the finite valuations. The finite quotients
of the integral units then remove the remaining angular components. -/
theorem thetaPrincipalUniformizerClass_power_archAngular (S : Finset (Place F)) (w : S)
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ)) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : (InfiniteAdeleRing F)ˣ, ∃ b : ∀ j : S, H j,
      thetaPrincipalUniformizerClass F S w ^ n =
        (QuotientGroup.mk (sLocalArchZetaInsert F S a) : SIdeleQuotient F S) *
          QuotientGroup.mk (angularLocalIdele F S H b) := by
  let g := singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val)
  let q := QuotientGroup.mk' (sUnitImage F S)
  obtain ⟨h, hh, z, hz, hc⟩ := exists_idele_with_zero_local_orders F S g
  let d := project F S z
  have hd (j : S) : ‖d.val.2 j‖ = 1 := by
    have hnorm := (finiteCompletion_norm_eq_one_iff F j.val
      ((sLocalZetaIdeleCoordinates F S d).2 j)).mpr
    rw [zetaIdeleCoordinates_finite_val] at hnorm
    exact hnorm ((ideleOrder_eq_zero_iff F z j.val).mp (hz j))
  obtain ⟨m, hm, a, b, hab⟩ := exists_power_archAngular F S H hH d hd
  have hq : q d = thetaPrincipalUniformizerClass F S w ^ h := hc
  refine ⟨h*m, Nat.mul_pos hh hm, a, b, ?_⟩
  change thetaPrincipalUniformizerClass F S w ^ (h*m) =
    q (sLocalArchZetaInsert F S a) * q (angularLocalIdele F S H b)
  rw [← map_mul q, ← hab, map_pow q, hq, pow_mul]

private theorem localUniformizer_norm_lt_one (S : Finset (Place F)) (w : S) :
    sLocalIdeleNorm F S (project F S (singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val))) < 1 := by
  unfold sLocalIdeleNorm
  change ideleNorm F (sLocalEmbed F S (project F S
    (singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val)))).val < 1
  rw [singleFiniteIdele_embedded_of_mem F w.val w.property, singleFiniteIdele_norm,
    norm_finiteUniformizer F w.val _ (chosenFiniteUniformizer_spec F w.val)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.val)

private theorem angularLocalIdele_norm_one (S : Finset (Place F))
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hU : ∀ j (u : H j), ‖u.val.val‖ = 1) (b : ∀ j : S, H j) :
    sLocalIdeleNorm F S (angularLocalIdele F S H b) = 1 := by
  rw [angularLocalIdele_eq_coordinates, sLocalZetaIdeleCoordinates_norm]
  simp only [hU, Finset.prod_const_one, mul_one]
  apply Finset.prod_eq_one
  intro j _
  change ‖(1 : j.Completion)‖ ^ j.mult = 1
  simp

/-- On classes fixed by the chosen angular level, the power of the
uniformizer acts exactly as the resulting archimedean translation. -/
theorem thetaPrincipalUniformizerClass_power_translate_of_angularFixed
    (S : Finset (Place F)) (w : S)
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (hU : ∀ j (u : H j), ‖u.val.val‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : (InfiniteAdeleRing F)ˣ,
      sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) < 1 ∧ ∀ x : E F S,
      (∀ u : ∀ j : S, H j,
        sLocalThetaTranslate F S (QuotientGroup.mk (angularLocalIdele F S H u)) x = x) →
      sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w ^ n) x =
        sLocalThetaTranslate F S (QuotientGroup.mk (sLocalArchZetaInsert F S a)) x := by
  obtain ⟨n,hn,a,b,h⟩ := thetaPrincipalUniformizerClass_power_archAngular F S w H hH
  let r : SIdeleQuotient F S →* ℝ := NNReal.toRealHom.toMonoidHom.comp
    ((Units.coeHom _).comp (sQuotientNorm F S))
  let v := project F S (singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val))
  have hr := congrArg r h
  rw [map_pow r, map_mul r] at hr
  change sLocalIdeleNorm F S v ^ n =
    sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) *
      sLocalIdeleNorm F S (angularLocalIdele F S H b) at hr
  rw [angularLocalIdele_norm_one F S H hU b, mul_one] at hr
  have hvpos : 0 < sLocalIdeleNorm F S v := ideleNorm_pos F (sLocalEmbed F S v)
  have ha : sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) < 1 :=
    hr ▸ pow_lt_one₀ hvpos.le (localUniformizer_norm_lt_one F S w) hn.ne'
  exact ⟨n, hn, a, ha, fun x hx ↦ by rw [h, sLocalThetaTranslate_mul, hx b]⟩

/-- For a strict modulus contraction, the geometric sum is injective.
The difference range is the inverse image of the power-difference range,
with the same test domain on both sides. -/
theorem sLocalThetaTranslate_difference_image_eq_preimage_power
    (S : Finset (Place F)) (a : (SAdeles F S)ˣ) (ha : sLocalIdeleNorm F S a < 1)
    {n : ℕ} (hn : 0 < n) (X : Set (E F S)) :
    let T := sLocalThetaTranslate F S (QuotientGroup.mk a)
    let C : E F S →L[ℂ] E F S := ∑ i ∈ Finset.range n, T^i
    (fun x ↦ x - T x) '' X =
      C ⁻¹' ((fun x ↦ x - sLocalThetaTranslate F S (QuotientGroup.mk (a^n)) x) '' X) := by
  intro T C
  have hpow (k : ℕ) (x : E F S) :
      (T^k) x = sLocalThetaTranslate F S (QuotientGroup.mk (a^k)) x := by
    let π := QuotientGroup.mk' (sUnitImage F S)
    induction k generalizing x with
    | zero =>
      change x = sLocalThetaTranslate F S (π (a^0)) x
      rw [pow_zero,map_one,sLocalThetaTranslate_one]
    | succ k ih =>
      rw [pow_succ']
      change T ((T^k) x) = sLocalThetaTranslate F S (π (a^(k+1))) x
      rw [ih, pow_succ',map_mul,sLocalThetaTranslate_mul]
      rfl
  have hleft : C * (1 - T) = 1 - T^n := geom_sum_mul_neg T n
  have hright : (1 - T) * C = 1 - T^n := mul_neg_geom_sum T n
  have hInject : Injective C := by
    apply (injective_iff_map_eq_zero C).mpr
    intro x hx
    have h := DFunLike.congr_fun hright x
    change (1 - T) (C x) = x - (T^n) x at h
    rw [hx,map_zero,hpow] at h
    have hnorm : sLocalIdeleNorm F S (a^n) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ (ideleNorm_pos F (sLocalEmbed F S a)).le ha hn.ne'
    exact sLocalThetaTranslate_eq_zero_of_fixed_of_norm_lt_one F S (a^n) hnorm x
      (sub_eq_zero.mp h.symm).symm
  have hstep (x : E F S) :
      C (x - T x) = x - sLocalThetaTranslate F S (QuotientGroup.mk (a^n)) x := by
    have h := DFunLike.congr_fun hleft x
    change C (x - T x) = x - (T^n) x at h
    rw [hpow] at h
    exact h
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(hstep x).symm⟩
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,hInject ((hstep x).trans hxy)⟩

/-- On each open angular level, closedness of the archimedean-difference
image is enough for closedness of the uniformizer-difference image, with
either image taken on the same subset of fixed classes. -/
theorem sLocalThetaUniformizerDifference_closed_of_archDifference
    (S : Finset (Place F)) (w : S)
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (hU : ∀ j (u : H j), ‖u.val.val‖ = 1) :
    ∃ a : (InfiniteAdeleRing F)ˣ,
      sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) < 1 ∧ ∀ X : Set (E F S),
      (∀ x ∈ X, ∀ u : ∀ j : S, H j,
        sLocalThetaTranslate F S (QuotientGroup.mk (angularLocalIdele F S H u)) x = x) →
      IsClosed ((fun x ↦ x - sLocalThetaTranslate F S (QuotientGroup.mk (sLocalArchZetaInsert F S a)) x) '' X) →
      IsClosed ((fun x ↦ x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x) '' X) := by
  obtain ⟨n, hn, a, ha, harch⟩ := thetaPrincipalUniformizerClass_power_translate_of_angularFixed F S w H hH hU
  let v := project F S (singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val))
  let π := QuotientGroup.mk' (sUnitImage F S)
  refine ⟨a, ha, fun X hX hClosed ↦ ?_⟩
  have he : (fun x ↦ x - sLocalThetaTranslate F S (π (v^n)) x) '' X =
      (fun x ↦ x - sLocalThetaTranslate F S (QuotientGroup.mk (sLocalArchZetaInsert F S a)) x) '' X := by
    apply Set.image_congr
    intro x hx
    rw [map_pow]
    exact congrArg (x - ·) (harch x (hX x hx))
  have h := sLocalThetaTranslate_difference_image_eq_preimage_power F S v
    (localUniformizer_norm_lt_one F S w) hn X
  dsimp only at h
  change IsClosed ((fun x ↦ x - sLocalThetaTranslate F S (π v) x) '' X)
  change (fun x ↦ x - sLocalThetaTranslate F S (π v) x) '' X = _ at h
  rw [h]
  change IsClosed ((⇑(∑ i ∈ Finset.range n, sLocalThetaTranslate F S (π v) ^ i)) ⁻¹'
    ((fun x ↦ x - sLocalThetaTranslate F S (π (v^n)) x) '' X))
  rw [he]
  exact hClosed.preimage (ContinuousLinearMap.continuous _)

private theorem uniformizerDifference_injective (S : Finset (Place F)) (w : S) :
    Injective (fun x : E F S ↦ x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x) := by
  let D := ContinuousLinearMap.id ℂ (E F S) - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)
  change Injective D
  apply (injective_iff_map_eq_zero D).mpr
  intro x hx
  change x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x = 0 at hx
  exact sLocalThetaTranslate_eq_zero_of_fixed_of_norm_lt_one F S _
    (localUniformizer_norm_lt_one F S w) x (sub_eq_zero.mp hx).symm

private theorem uniformizerDifference_translate (S : Finset (Place F)) (w : S)
    (c : SIdeleQuotient F S) (q : E F S) :
    let T := sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)
    let R := sLocalThetaTranslate F S c
    R (q - T q) = R q - T (R q) := by
  dsimp only
  rw [map_sub, ← sLocalThetaTranslate_mul, ← sLocalThetaTranslate_mul]
  exact congrArg (fun d : SIdeleQuotient F S ↦
    sLocalThetaTranslate F S c q - sLocalThetaTranslate F S d q)
    (mul_comm c (thetaPrincipalUniformizerClass F S w))

/-- At a fixed angular level, the principal-value range is detected by the
uniformizer-difference image of the classes fixed by the full units at the
selected place. The preimage map is the normalized unit average. -/
theorem sLocalThetaPrincipalValue_angular_preimage_range
    (S : Finset (Place F)) (w : S)
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (hn : ∀ j (u : H j), ‖u.val.val‖ = 1) :
    let W := sLocalThetaInvariantTestSpan F S H
    let A := sLocalThetaPrincipalUnitAverage F S w
    let X := (W : Set (E F S)) ∩ sLocalPrincipalUnitFixed F S w
    W.subtypeL ⁻¹' range (sLocalThetaPrincipalValues F S {w}) =
      (A.comp W.subtypeL) ⁻¹'
        ((fun x ↦ x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x) '' X) := by
  intro W A X
  let D (x : E F S) := x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x
  have hi : Injective D := uniformizerDifference_injective F S w
  ext x
  change x.val ∈ range (sLocalThetaPrincipalValues F S {w}) ↔ A x.val ∈ D '' X
  rw [sLocalThetaPrincipalValue_mem_range_iff_unitDifference]
  change A x.val ∈ range (fun y : sLocalPrincipalUnitFixed F S w ↦ D y.val) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    have hyW : y.val ∈ W := by
      apply mem_sLocalThetaInvariantTestSpan_of_fixed F S H hH hn
      intro u
      let c : SIdeleQuotient F S := QuotientGroup.mk (angularLocalIdele F S H u)
      let R := sLocalThetaTranslate F S c
      change R y.val = y.val
      apply hi
      calc
        D (R y.val) = R (D y.val) := (uniformizerDifference_translate F S w c y.val).symm
        _ = R (A x.val) := congrArg R hy
        _ = A x.val := by
          rw [← sLocalThetaPrincipalUnitAverage_translate]
          exact congrArg A (sLocalThetaInvariantTestSpan_fixed F S H x.val x.property u)
        _ = D y.val := hy.symm
    exact ⟨y.val, ⟨hyW, y.property⟩, hy⟩
  · rintro ⟨y, ⟨_, hy⟩, he⟩
    exact ⟨⟨y, hy⟩, he⟩

/-- On each open integral-unit level, closedness of the principal-value
range is equivalent to closedness of the uniformizer-difference image
on the classes fixed by both the level and the selected local units. -/
theorem sLocalThetaPrincipalValue_angular_isClosed_iff_unitDifference
    (S : Finset (Place F)) (w : S)
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (hn : ∀ j (u : H j), ‖u.val.val‖ = 1) :
    let W := sLocalThetaInvariantTestSpan F S H
    let X := (W : Set (E F S)) ∩ sLocalPrincipalUnitFixed F S w
    IsClosed (W.subtypeL ⁻¹' range (sLocalThetaPrincipalValues F S {w})) ↔
      IsClosed ((fun x ↦ x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x) '' X) := by
  intro W X
  letI : T2Space (E F S) := sLocalThetaQuotient_t2Space F S
  let A := sLocalThetaPrincipalUnitAverage F S w
  let D (x : E F S) := x - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) x
  let P := sLocalThetaPrincipalValues F S {w}
  have hW : IsClosedEmbedding W.subtypeL :=
    (sLocalThetaInvariantTestSpan_isFrechet F S H hH hn).isClosedEmbedding _
      IsEmbedding.subtypeVal
  have hfix {x : E F S} : x ∈ sLocalPrincipalUnitFixed F S w ↔ A x = x := by
    constructor
    · exact sLocalThetaPrincipalUnitAverage_eq_of_fixed F S w x
    · intro hx u
      rw [← hx]
      exact sLocalThetaPrincipalUnitAverage_fixed F S w x u
  have he : D '' X = W.subtypeL '' (W.subtypeL ⁻¹' range P) ∩ {x | A x = x} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyW, hyU⟩, rfl⟩
      have hyP : P y = D y := by
        rw [sLocalThetaPrincipalValue_eq_sub_average]
        change y - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) (A y) = D y
        rw [hfix.mp hyU]
      have hyD : D y ∈ W := by
        apply mem_sLocalThetaInvariantTestSpan_of_fixed F S H hH hn
        intro u
        let c : SIdeleQuotient F S := QuotientGroup.mk (angularLocalIdele F S H u)
        change sLocalThetaTranslate F S c (D y) = D y
        exact (uniformizerDifference_translate F S w c y).trans
          (congrArg D (sLocalThetaInvariantTestSpan_fixed F S H y hyW u))
      refine ⟨⟨⟨D y, hyD⟩, ⟨y, hyP⟩, rfl⟩, hfix.mp ?_⟩
      intro u
      exact (uniformizerDifference_translate F S w (thetaPrincipalUnitClass F S w u) y).trans
        (congrArg D (hyU u))
    · rintro ⟨⟨x, hx, rfl⟩, hAx⟩
      have hx' : x ∈ W.subtypeL ⁻¹' range P := hx
      rw [sLocalThetaPrincipalValue_angular_preimage_range F S w H hH hn] at hx'
      change A x.val ∈ D '' X at hx'
      change A x.val = x.val at hAx
      rwa [hAx] at hx'
  constructor
  · intro h
    rw [he]
    exact (hW.isClosedMap _ h).inter (isClosed_eq A.continuous continuous_id)
  · intro h
    rw [sLocalThetaPrincipalValue_angular_preimage_range F S w H hH hn]
    exact h.preimage (A.comp W.subtypeL).continuous

/-- For the single-place closed embedding it suffices, at each open angular
level, to establish closedness of the archimedean-difference image on the
classes also fixed by the full units at the selected place. -/
theorem sLocalThetaPrincipalValue_closedEmbedding_of_archDifferences
    (S : Finset (Place F)) (w : S)
    (h : ∀ (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ),
      (∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ)) →
      (∀ j (u : H j), ‖u.val.val‖ = 1) →
      ∀ a : (InfiniteAdeleRing F)ˣ, sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) < 1 →
        IsClosed ((fun x ↦ x - sLocalThetaTranslate F S (QuotientGroup.mk (sLocalArchZetaInsert F S a)) x) ''
          ((sLocalThetaInvariantTestSpan F S H : Set (E F S)) ∩ sLocalPrincipalUnitFixed F S w))) :
    IsClosedEmbedding (sLocalThetaPrincipalValues F S {w}) := by
  apply (sLocalThetaPrincipalValues_closedEmbedding_iff_angular F S {w}).mpr
  intro H hH hn
  let W := sLocalThetaInvariantTestSpan F S H
  let X := (W : Set (E F S)) ∩ sLocalPrincipalUnitFixed F S w
  obtain ⟨a, ha, hdiff⟩ := sLocalThetaUniformizerDifference_closed_of_archDifference F S w H hH hn
  have hfix (x : E F S) (hx : x ∈ X) (u : ∀ j : S, H j) :
      sLocalThetaTranslate F S (QuotientGroup.mk (angularLocalIdele F S H u)) x = x :=
    sLocalThetaInvariantTestSpan_fixed F S H x hx.1 u
  have hClosed := hdiff X hfix (h H hH hn a ha)
  rw [sLocalThetaPrincipalValue_angular_preimage_range F S w H hH hn]
  exact hClosed.preimage (ContinuousLinearMap.continuous _)

end
end Masullo
