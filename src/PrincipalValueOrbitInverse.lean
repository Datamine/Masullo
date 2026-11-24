import PrincipalValueArchShift

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Q (S : Finset (Place F)) := SLocalThetaQuotient F S
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S

/-- Translation of a theta class shifts the argument of its evaluation. -/
theorem sLocalThetaQuotientEval_translate (S : Finset (Place F)) (a g : (SAdeles F S)ˣ)
    (q : Q F S) :
    sLocalThetaQuotientEval F S g (sLocalThetaTranslate F S (QuotientGroup.mk a) q) =
      sLocalThetaQuotientEval F S (a⁻¹ * g) q := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change sLocalThetaQuotientEval F S g (sLocalThetaTranslateIdeles F S a (Submodule.Quotient.mk f)) = _
  rw [sLocalThetaTranslateIdeles_mk]
  let π := QuotientGroup.mk' (sUnitImage F S)
  change sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S a f) (π g) =
    sLocalThetaOperator F S f (π (a⁻¹ * g))
  rw [sLocalThetaOperator_leftTranslate]
  change sLocalThetaOperator F S f ((π a)⁻¹ * π g) = _
  rw [map_mul π, map_inv π]

private def orbitEvaluation (S : Finset (Place F)) (a g : (SAdeles F S)ˣ) (n : ℕ) :
    Test F S →L[ℂ] ℂ :=
  (sLocalThetaQuotientEval F S (a⁻¹ ^ n * g)).comp (sLocalThetaOperator F S).ker.mkQL

private theorem orbitEvaluation_majorant (S : Finset (Place F)) (a g : (SAdeles F S)ˣ)
    (ha : sLocalIdeleNorm F S a < 1) :
    ∃ p : Seminorm ℂ (Test F S), Continuous p ∧ ∃ C : ℕ → ℝ,
      Summable C ∧ (∀ n, 0 ≤ C n) ∧ ∀ n f, ‖orbitEvaluation F S a g n f‖ ≤ C n * p f := by
  let r := sLocalIdeleNorm F S
  let L := orbitEvaluation F S a g
  have hpos (b : (SAdeles F S)ˣ) : 0 < r b := ideleNorm_pos F (sLocalEmbed F S b)
  have hr : 1 < (r a)⁻¹ := (one_lt_inv₀ (hpos a)).mpr ha
  have ht : Tendsto (fun n : ℕ ↦ r (a⁻¹ ^ n * g)) atTop atTop := by
    simpa only [map_mul, map_pow, map_inv] using
      (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const (hpos g)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 1))
  obtain ⟨p,hp,hbound⟩ := sLocalTheta_largeNorm_seminorm F S 1
  let phead : Seminorm ℂ (Test F S) :=
    ∑ n ∈ Finset.range N, (normSeminorm ℂ ℂ).comp (L n).toLinearMap
  have hhead (f : Test F S) : phead f = ∑ n ∈ Finset.range N, ‖L n f‖ := by
    let e : Seminorm ℂ (Test F S) →+ (Test F S → ℝ) := FunLike.coeAddMonoidHom _ _ _
    change e (∑ n ∈ Finset.range N, (normSeminorm ℂ ℂ).comp (L n).toLinearMap) f = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have hc : Continuous phead := by
    change Continuous (fun f : Test F S ↦ phead f)
    simp only [hhead]
    exact continuous_finsetSum _ fun n _ ↦ (L n).continuous.norm
  let C (n : ℕ) := Set.indicator (Finset.range N : Set ℕ) (fun _ ↦ (1 : ℝ)) n +
    (r g)⁻¹ * (r a)^n
  have hC : Summable C := by
    apply Summable.add
    · exact summable_of_ne_finset_zero (s := Finset.range N) fun n hn ↦
        Set.indicator_of_notMem hn _
    · exact (summable_geometric_of_lt_one (hpos a).le ha).mul_left _
  have hc0 (n : ℕ) : 0 ≤ C n := add_nonneg
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    (mul_nonneg (inv_nonneg.mpr (hpos g).le) (pow_nonneg (hpos a).le _))
  refine ⟨phead + p, hc.add hp, C, hC, hc0, fun n f ↦ ?_⟩
  have hn0 : 0 ≤ (r g)⁻¹ * (r a)^n := mul_nonneg (inv_nonneg.mpr (hpos g).le) (pow_nonneg (hpos a).le _)
  change ‖L n f‖ ≤ C n * (phead f + p f)
  by_cases hn : n < N
  · have hm : n ∈ Finset.range N := Finset.mem_range.mpr hn
    have hf : ‖L n f‖ ≤ phead f + p f := by
      rw [hhead]
      exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg (L i f)) hm).trans
        (le_add_of_nonneg_right (apply_nonneg p f))
    have hC1 : 1 ≤ C n := by
      change 1 ≤ Set.indicator (Finset.range N : Set ℕ) _ n + _
      rw [Set.indicator_of_mem (show n ∈ (Finset.range N : Set ℕ) from hm)]
      exact le_add_of_nonneg_right hn0
    exact hf.trans (le_mul_of_one_le_left (by positivity) hC1)
  · have hm : n ∉ (Finset.range N : Set ℕ) := by simpa using hn
    have hb := hbound f (a⁻¹ ^ n * g) (hN n (Nat.le_of_not_gt hn))
    change r (a⁻¹ ^ n * g)^1 * ‖L n f‖ ≤ p f at hb
    rw [pow_one, mul_comm] at hb
    have hi := (le_div_iff₀ (hpos (a⁻¹ ^ n * g))).mpr hb
    rw [div_eq_mul_inv, map_mul r, map_pow r, map_inv r, mul_inv_rev, inv_pow, inv_inv] at hi
    change ‖L n f‖ ≤ (Set.indicator (Finset.range N : Set ℕ) _ n + _) * _
    rw [Set.indicator_of_notMem hm, zero_add]
    exact (hi.trans_eq (mul_comm _ _)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (apply_nonneg phead f)) hn0)

/-- Evaluations along a strictly expanding orbit are absolutely summable on
the ordinary theta quotient. -/
theorem sLocalThetaQuotientEval_orbit_summable_norm (S : Finset (Place F))
    (a g : (SAdeles F S)ˣ) (ha : sLocalIdeleNorm F S a < 1) (q : Q F S) :
    Summable (fun n : ℕ ↦ ‖sLocalThetaQuotientEval F S (a⁻¹ ^ n * g) q‖) := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨p,_,C,hC,_,hb⟩ := orbitEvaluation_majorant F S a g ha
  exact (hC.mul_right (p f)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ hb n f)

/-- The inverse-orbit sum is a continuous linear functional on the ordinary
theta quotient, for each initial idele. -/
def sLocalThetaOrbitInverse (S : Finset (Place F)) (a g : (SAdeles F S)ˣ)
    (ha : sLocalIdeleNorm F S a < 1) : Q F S →L[ℂ] ℂ := by
  let K := (sLocalThetaOperator F S).ker
  let L := orbitEvaluation F S a g
  have hs (f : Test F S) : Summable (fun n : ℕ ↦ ‖L n f‖) :=
    sLocalThetaQuotientEval_orbit_summable_norm F S a g ha (K.mkQL f)
  let A : Test F S →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∑' n, L n f
      map_add' := fun f b ↦ by
        simp only [map_add, (hs f).of_norm.tsum_add (hs b).of_norm]
      map_smul' := fun c f ↦ by
        simp only [map_smul, smul_eq_mul, tsum_mul_left, RingHom.id_apply] }
  have hA : Continuous A := by
    obtain ⟨p,hp,C,hC,hC0,hb⟩ := orbitEvaluation_majorant F S a g ha
    let c : NNReal := ⟨∑' n, C n, tsum_nonneg hC0⟩
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp A
    intro _
    apply Seminorm.continuous_of_le (q := c • p) (hp.const_smul c)
    intro f
    change ‖∑' n, L n f‖ ≤ (∑' n, C n) * p f
    calc
      ‖∑' n, L n f‖ ≤ ∑' n, ‖L n f‖ := norm_tsum_le_tsum_norm (hs f)
      _ ≤ ∑' n, C n * p f := (hs f).tsum_le_tsum (fun n ↦ hb n f) (hC.mul_right _)
      _ = _ := hC.tsum_mul_right _
  refine K.liftQL ⟨A,hA⟩ (fun f hf ↦ ?_)
  have hz : K.mkQL f = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hf
  change (∑' n, sLocalThetaQuotientEval F S (a⁻¹ ^ n * g) (K.mkQL f)) = 0
  simp [hz]

@[simp] theorem sLocalThetaOrbitInverse_apply (S : Finset (Place F)) (a g : (SAdeles F S)ˣ)
    (ha : sLocalIdeleNorm F S a < 1) (q : Q F S) :
    sLocalThetaOrbitInverse F S a g ha q =
      ∑' n : ℕ, sLocalThetaQuotientEval F S (a⁻¹ ^ n * g) q := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- The inverse orbit profile satisfies the difference equation at every
idele, whether or not the profile has a theta representative. -/
theorem sLocalThetaOrbitInverse_sub_shift (S : Finset (Place F)) (a g : (SAdeles F S)ˣ)
    (ha : sLocalIdeleNorm F S a < 1) (q : Q F S) :
    sLocalThetaOrbitInverse F S a g ha q -
      sLocalThetaOrbitInverse F S a (a⁻¹ * g) ha q = sLocalThetaQuotientEval F S g q := by
  let f (n : ℕ) := sLocalThetaQuotientEval F S (a⁻¹ ^ n * g) q
  have hs : Summable f := (sLocalThetaQuotientEval_orbit_summable_norm F S a g ha q).of_norm
  have ht : (∑' n : ℕ, sLocalThetaQuotientEval F S (a⁻¹ ^ n * (a⁻¹ * g)) q) =
      ∑' n : ℕ, f (n+1) := by
    apply tsum_congr
    intro n
    dsimp only [f]
    rw [pow_succ, mul_assoc]
  rw [sLocalThetaOrbitInverse_apply, sLocalThetaOrbitInverse_apply, ht]
  change (∑' n, f n) - (∑' n, f (n+1)) = sLocalThetaQuotientEval F S g q
  rw [← hs.sum_add_tsum_nat_add 1, add_sub_cancel_right, Finset.sum_range_one]
  simp [f]

/-- On a translation difference, the inverse orbit sum recovers the original
theta class at every evaluation idele. -/
theorem sLocalThetaOrbitInverse_difference (S : Finset (Place F)) (a g : (SAdeles F S)ˣ)
    (ha : sLocalIdeleNorm F S a < 1) (q : Q F S) :
    sLocalThetaOrbitInverse F S a g ha (q - sLocalThetaTranslate F S (QuotientGroup.mk a) q) =
      sLocalThetaQuotientEval F S g q := by
  rw [map_sub]
  have hshift : sLocalThetaOrbitInverse F S a g ha (sLocalThetaTranslate F S (QuotientGroup.mk a) q) =
      sLocalThetaOrbitInverse F S a (a⁻¹ * g) ha q := by
    simp only [sLocalThetaOrbitInverse_apply]
    apply tsum_congr
    intro n
    rw [sLocalThetaQuotientEval_translate]
    have he : a⁻¹ * (a⁻¹ ^ n * g) = a⁻¹ ^ n * (a⁻¹ * g) := by ac_rfl
    rw [he]
  rw [hshift, sLocalThetaOrbitInverse_sub_shift]

private theorem quotientEval_ext (S : Finset (Place F)) {x y : Q F S}
    (h : ∀ g, sLocalThetaQuotientEval F S g x = sLocalThetaQuotientEval F S g y) : x = y := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective _ y
  apply (Submodule.Quotient.eq (sLocalThetaOperator F S).ker).mpr
  apply LinearMap.mem_ker.mpr
  funext c
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective c
  have hg := h g
  change sLocalThetaOperator F S f (QuotientGroup.mk g) =
    sLocalThetaOperator F S b (QuotientGroup.mk g) at hg
  rw [map_sub, Pi.sub_apply, hg, sub_self, Pi.zero_apply]

/-- The exact remaining range question is whether the pointwise inverse orbit
profile is itself a theta class from the specified domain. -/
theorem sLocalTheta_mem_difference_image_iff_orbitInverse
    (S : Finset (Place F)) (a : (SAdeles F S)ˣ) (ha : sLocalIdeleNorm F S a < 1)
    (X : Set (Q F S)) (q : Q F S) :
    q ∈ (fun x ↦ x - sLocalThetaTranslate F S (QuotientGroup.mk a) x) '' X ↔
      ∃ x ∈ X, ∀ g, sLocalThetaQuotientEval F S g x = sLocalThetaOrbitInverse F S a g ha q := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,fun g ↦ (sLocalThetaOrbitInverse_difference F S a g ha x).symm⟩
  · rintro ⟨x,hx,he⟩
    refine ⟨x,hx,quotientEval_ext F S fun g ↦ ?_⟩
    rw [map_sub, sLocalThetaQuotientEval_translate, he, he, sLocalThetaOrbitInverse_sub_shift]

/-- At large modulus, all positive power weights of the inverse orbit
profile are controlled by continuous seminorms of the original quotient. -/
theorem sLocalThetaOrbitInverse_largeNorm_seminorm (S : Finset (Place F))
    (a : (SAdeles F S)ˣ) (ha : sLocalIdeleNorm F S a < 1) (N : ℕ) :
    ∃ p : Seminorm ℂ (Q F S), Continuous p ∧ ∀ q g, 1 ≤ sLocalIdeleNorm F S g →
      sLocalIdeleNorm F S g ^ N * ‖sLocalThetaOrbitInverse F S a g ha q‖ ≤ p q := by
  let r := sLocalIdeleNorm F S
  let K := (sLocalThetaOperator F S).ker
  have hpos (g : (SAdeles F S)ˣ) : 0 < r g := ideleNorm_pos F (sLocalEmbed F S g)
  let R (g : (SAdeles F S)ˣ) : NNReal := ⟨r g ^ (N+1), pow_nonneg (hpos g).le _⟩
  let I := {g : (SAdeles F S)ˣ // 1 ≤ r g}
  letI : Nonempty I := ⟨⟨1, by rw [map_one]⟩⟩
  let B (g : I) : Seminorm ℂ (Q F S) :=
    R g.val • (normSeminorm ℂ ℂ).comp (sLocalThetaOrbitInverse F S a g.val ha).toLinearMap
  let C (n : ℕ) := (r a ^ (N+1))^n
  have hC0 (n : ℕ) : 0 ≤ C n := pow_nonneg (pow_nonneg (hpos a).le _) _
  have hC : Summable C := summable_geometric_of_lt_one
    (pow_nonneg (hpos a).le _) (pow_lt_one₀ (hpos a).le ha (Nat.succ_ne_zero _))
  let c : NNReal := ⟨∑' n, C n, tsum_nonneg hC0⟩
  obtain ⟨p,hp,hb⟩ := sLocalTheta_largeNorm_seminorm F S (N+1)
  have hbound (f : Test F S) (g : I) : B g (K.mkQL f) ≤ (c • p) f := by
    let e (n : ℕ) := sLocalThetaQuotientEval F S (a⁻¹ ^ n * g.val) (K.mkQL f)
    have hs : Summable (fun n ↦ ‖e n‖) :=
      sLocalThetaQuotientEval_orbit_summable_norm F S a g.val ha (K.mkQL f)
    have hterm (n : ℕ) : (R g.val : ℝ) * ‖e n‖ ≤ C n * p f := by
      let b := a⁻¹ ^ n * g.val
      have hbg : 1 ≤ r b := by
        change 1 ≤ r (a⁻¹ ^ n * g.val)
        rw [map_mul r, map_pow r, map_inv r]
        exact one_le_mul_of_one_le_of_one_le
          (one_le_pow₀ ((one_lt_inv₀ (hpos a)).mpr ha).le) g.property
      have h := hb f b hbg
      change r b ^ (N+1) * ‖e n‖ ≤ p f at h
      have he : C n * r b ^ (N+1) = (R g.val : ℝ) := by
        have hcancel : r a ^ n * (r a)⁻¹ ^ n = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (hpos a).ne', one_pow]
        change (r a ^ (N+1))^n * (r (a⁻¹ ^ n * g.val)) ^ (N+1) = r g.val ^ (N+1)
        rw [map_mul r, map_pow r, map_inv r, mul_pow, ← mul_assoc,
          pow_right_comm (r a) (N+1) n, ← mul_pow, hcancel, one_pow, one_mul]
      rw [← he, mul_assoc]
      exact mul_le_mul_of_nonneg_left h (hC0 n)
    change (R g.val : ℝ) * ‖sLocalThetaOrbitInverse F S a g.val ha (K.mkQL f)‖ ≤ (c : ℝ) * p f
    rw [sLocalThetaOrbitInverse_apply]
    calc
      (R g.val : ℝ) * ‖∑' n, e n‖ ≤ (R g.val : ℝ) * ∑' n, ‖e n‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (R g.val).coe_nonneg
      _ = ∑' n, (R g.val : ℝ) * ‖e n‖ := (hs.tsum_mul_left _).symm
      _ ≤ ∑' n, C n * p f := (hs.mul_left _).tsum_le_tsum hterm (hC.mul_right _)
      _ = _ := hC.tsum_mul_right _
  have hB : BddAbove (range B) := Seminorm.bddAbove_range_iff.mpr fun q ↦ by
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective K q
    exact ⟨(c • p) f, Set.forall_mem_range.mpr fun g ↦ hbound f g⟩
  let U : Seminorm ℂ (Q F S) := ⨆ g : I, B g
  have hU : Continuous U := by
    apply K.isQuotientMap_mkQL.continuous_iff.mpr
    change Continuous (U.comp K.mkQL.toLinearMap)
    apply Seminorm.continuous_of_le (q := c • p) (hp.const_smul c)
    intro f
    exact (Seminorm.iSup_apply hB).trans_le (ciSup_le (hbound f))
  refine ⟨U, hU, fun q g hg ↦ ?_⟩
  have h := (le_ciSup hB (⟨g,hg⟩ : I)) q
  change r g ^ (N+1) * ‖sLocalThetaOrbitInverse F S a g ha q‖ ≤ U q at h
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hg (Nat.le_succ _)) (norm_nonneg _)).trans h

/-- At a fixed angular level, closedness reduces to finding any ordinary
theta representative of each inverse orbit profile in the closure. The
representative's class automatically has the required finite invariances. -/
theorem sLocalThetaArchDifference_isClosed_iff_orbitRealization
    (S : Finset (Place F)) (w : S)
    (H : ∀ j : S, Subgroup (j.val.adicCompletion F)ˣ)
    (hH : ∀ j, IsOpen (H j : Set (j.val.adicCompletion F)ˣ))
    (hU : ∀ j (u : H j), ‖u.val.val‖ = 1)
    (a : (InfiniteAdeleRing F)ˣ)
    (ha : sLocalIdeleNorm F S (sLocalArchZetaInsert F S a) < 1) :
    let W := sLocalThetaInvariantTestSpan F S H
    let X := (W : Set (Q F S)) ∩ sLocalPrincipalUnitFixed F S w
    let b := sLocalArchZetaInsert F S a
    let Y := (fun x ↦ x - sLocalThetaTranslate F S (QuotientGroup.mk b) x) '' X
    IsClosed Y ↔ ∀ q ∈ closure Y, ∃ f : Test F S, ∀ g,
      sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g =
        sLocalThetaOrbitInverse F S b g ha q := by
  intro W X b Y
  let c : SIdeleQuotient F S := QuotientGroup.mk b
  let T := sLocalThetaTranslate F S c
  let D := ContinuousLinearMap.id ℂ (Q F S) - T
  letI : T2Space (Q F S) := sLocalThetaQuotient_t2Space F S
  have hi : Injective D := (injective_iff_map_eq_zero D).mpr fun x hx ↦ by
    change x - T x = 0 at hx
    exact sLocalThetaTranslate_eq_zero_of_fixed_of_norm_lt_one F S b ha x (sub_eq_zero.mp hx).symm
  have hcomm (e : SIdeleQuotient F S) (x : Q F S) :
      sLocalThetaTranslate F S e (D x) = D (sLocalThetaTranslate F S e x) := by
    change sLocalThetaTranslate F S e (x - T x) =
      sLocalThetaTranslate F S e x - T (sLocalThetaTranslate F S e x)
    rw [map_sub]
    change sLocalThetaTranslate F S e x - sLocalThetaTranslate F S e (sLocalThetaTranslate F S c x) = _
    rw [← sLocalThetaTranslate_mul]
    change _ = sLocalThetaTranslate F S e x - sLocalThetaTranslate F S c (sLocalThetaTranslate F S e x)
    rw [← sLocalThetaTranslate_mul]
    exact congrArg (fun r : SIdeleQuotient F S ↦
      sLocalThetaTranslate F S e x - sLocalThetaTranslate F S r x) (mul_comm e c)
  have hX (y : Q F S) : y ∈ X ↔
      (∀ u : ∀ j : S, H j,
        sLocalThetaTranslate F S (QuotientGroup.mk (angularLocalIdele F S H u)) y = y) ∧
      ∀ u : principalIntegralUnits F w.val, sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) y = y :=
    ⟨fun hy ↦ ⟨sLocalThetaInvariantTestSpan_fixed F S H y hy.1, hy.2⟩,
      fun hy ↦ ⟨mem_sLocalThetaInvariantTestSpan_of_fixed F S H hH hU y hy.1, hy.2⟩⟩
  have hClosedX : IsClosed X := by
    have he : X = (⋂ u : ∀ j : S, H j,
        {y | sLocalThetaTranslate F S (QuotientGroup.mk (angularLocalIdele F S H u)) y = y}) ∩
        ⋂ u : principalIntegralUnits F w.val,
          {y | sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) y = y} := by
      ext y
      simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] using hX y
    rw [he]
    exact (isClosed_iInter fun _ ↦ isClosed_eq (ContinuousLinearMap.continuous _) continuous_id).inter
      (isClosed_iInter fun _ ↦ isClosed_eq (ContinuousLinearMap.continuous _) continuous_id)
  have hY : closure Y ⊆ X := by
    apply closure_minimal _ hClosedX
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨hxH,hxU⟩ := (hX x).mp hx
    apply (hX (D x)).mpr
    exact ⟨fun u ↦ (hcomm _ x).trans (congrArg D (hxH u)),
      fun u ↦ (hcomm _ x).trans (congrArg D (hxU u))⟩
  constructor
  · intro h q hq
    rw [h.closure_eq] at hq
    obtain ⟨x, _, hx⟩ := (sLocalTheta_mem_difference_image_iff_orbitInverse F S b ha X q).mp hq
    obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨f, hx⟩
  · intro h
    apply isClosed_of_closure_subset
    intro q hq
    obtain ⟨f,hf⟩ := h q hq
    let x : Q F S := Submodule.Quotient.mk f
    have he : D x = q := by
      apply quotientEval_ext F S
      intro g
      change sLocalThetaQuotientEval F S g
        (x - sLocalThetaTranslate F S (QuotientGroup.mk b) x) = _
      change ∀ g, sLocalThetaQuotientEval F S g x = sLocalThetaOrbitInverse F S b g ha q at hf
      rw [map_sub, sLocalThetaQuotientEval_translate, hf, hf, sLocalThetaOrbitInverse_sub_shift]
    have hx : x ∈ X := by
      obtain ⟨hqH,hqU⟩ := (hX q).mp (hY hq)
      apply (hX x).mpr
      have key (e : SIdeleQuotient F S) (hfix : sLocalThetaTranslate F S e q = q) :
          sLocalThetaTranslate F S e x = x := hi (by rw [← hcomm, he, hfix])
      exact ⟨fun u ↦ key _ (hqH u), fun u ↦ key _ (hqU u)⟩
    exact ⟨x,hx,he⟩

end
end Masullo
