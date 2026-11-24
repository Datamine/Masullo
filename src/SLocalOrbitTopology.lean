import FiniteCoordinateOrbitTopology
import FiniteAdelicOrbits
import SLocalZetaUnfolding
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.EMetricSpace.Paracompact

open Filter Function IsDedekindDomain NumberField Set Topology TopologicalSpace
open scoped Classical NumberField RestrictedProduct

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
variable (S : Finset (Place F))

private abbrev OrbitIndex := InfinitePlace F ⊕ S
private abbrev OrbitField : OrbitIndex F S → Type _
  | .inl v => v.Completion
  | .inr v => v.val.adicCompletion F

private instance (i : OrbitIndex F S) : NormedField (OrbitField F S i) := by
  cases i with
  | inl v => exact inferInstanceAs (NormedField v.Completion)
  | inr v => exact inferInstanceAs (NormedField (v.val.adicCompletion F))

private def orbitWeight : OrbitIndex F S → ℕ
  | .inl v => v.mult
  | .inr _ => 1

omit [NumberField F] in
private theorem orbitWeight_pos (i : OrbitIndex F S) : 0 < orbitWeight F S i := by
  cases i with
  | inl v => exact Nat.pos_of_ne_zero InfinitePlace.mult_ne_zero
  | inr v => exact Nat.zero_lt_one

private def orbitProductEquiv : SAdeles F S ≃+* ((i : OrbitIndex F S) → OrbitField F S i) where
  toFun x
    | .inl v => x.1 v
    | .inr v => x.2 v
  invFun x := (fun v ↦ x (.inl v), fun v ↦ x (.inr v))
  left_inv x := rfl
  right_inv x := funext fun i ↦ by cases i <;> rfl
  map_mul' x y := funext fun i ↦ by cases i <;> rfl
  map_add' x y := funext fun i ↦ by cases i <;> rfl

private def orbitProductHomeomorph : SAdeles F S ≃ₜ ((i : OrbitIndex F S) → OrbitField F S i) where
  toEquiv := (orbitProductEquiv F S).toEquiv
  continuous_toFun := continuous_pi fun i ↦ by
    cases i with
    | inl v => exact (continuous_apply v).comp continuous_fst
    | inr v => exact (continuous_apply v).comp continuous_snd
  continuous_invFun := (continuous_pi fun v ↦ continuous_apply (Sum.inl v)).prodMk
    (continuous_pi fun v ↦ continuous_apply (Sum.inr v))

private def orbitUnitsEquiv : (SAdeles F S)ˣ ≃ₜ* ((i : OrbitIndex F S) → (OrbitField F S i)ˣ) :=
  (Units.mapContinuousMulEquiv
    { toMulEquiv := (orbitProductEquiv F S).toMulEquiv
      continuous_toFun := (orbitProductHomeomorph F S).continuous
      continuous_invFun := (orbitProductHomeomorph F S).symm.continuous }).trans
    ContinuousMulEquiv.piUnits

private theorem orbitUnitsEquiv_val (a : (SAdeles F S)ˣ) (i : OrbitIndex F S) :
    (orbitUnitsEquiv F S a i).val = orbitProductEquiv F S a.val i := rfl

/-- The S-idelic modulus is the product of the normalized absolute values of the selected coordinates. -/
theorem sLocalIdeleNorm_eq_coordinateProduct (a : (SAdeles F S)ˣ) :
    sLocalIdeleNorm F S a =
      (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) * ∏ v : S, ‖a.val.2 v‖ := by
  let b := sLocalEmbed F S a
  change (∏ v : InfinitePlace F, ‖b.val.val.1 v‖ ^ v.mult) *
    (∏ᶠ v : Place F, ‖b.val.val.2 v‖) = _
  rw [show b.val.val.1 = a.val.1 from sLocalEmbed_arch F S a]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra h
    have hord := (sIdeleBlock_mem_iff F S b.val).mp b.property v h
    have hone : ‖b.val.val.2 v‖ = 1 := by
      rw [FinitePlace.norm_def, (ideleOrder_eq_zero_iff F b.val v).mp hord]
      simp
    exact hv hone), ← Finset.prod_attach S (fun v ↦ ‖b.val.val.2 v‖)]
  congr 1
  exact Finset.prod_congr rfl (fun v _ => congrArg norm (sLocalEmbed_finite F S a v))

private theorem orbitUnitNorm_eq (a : (SAdeles F S)ˣ) :
    finiteCoordinateUnitNorm (OrbitField F S) (orbitWeight F S) (orbitUnitsEquiv F S a) =
      sLocalIdeleNorm F S a := by
  change (∏ i, ‖(orbitUnitsEquiv F S a i).val‖ ^ orbitWeight F S i) = _
  rw [sLocalIdeleNorm_eq_coordinateProduct, Fintype.prod_sum_type]
  change (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) *
    (∏ v : S, ‖a.val.2 v‖ ^ (1 : ℕ)) = _
  simp only [pow_one]

private theorem archNorm_hasLocalSection (v : InfinitePlace F) (u : v.Completionˣ) :
    ∃ s : ℝ → v.Completionˣ,
      s (‖u.val‖ ^ v.mult) = u ∧ ContinuousAt s (‖u.val‖ ^ v.mult) ∧
      ∀ᶠ r in 𝓝 (‖u.val‖ ^ v.mult), (∃ a : v.Completionˣ, ‖a.val‖ ^ v.mult = r) →
        ‖(s r).val‖ ^ v.mult = r := by
  let q := ‖u.val‖ ^ v.mult
  have hq : 0 < q := pow_pos (norm_pos_iff.mpr u.ne_zero) _
  have hv : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
  let f (r : ℝ) := Real.exp (Real.log (r / q) / (v.mult : ℝ))
  let e := infinitePlaceRealEmbedding F v
  let s (r : ℝ) : v.Completionˣ :=
    u * Units.mk0 (e (f r)) (fun h ↦ (Real.exp_pos _).ne'
      ((infinitePlaceRealEmbedding_isometry F v).injective (h.trans (map_zero e).symm)))
  have he (r : ℝ) : ‖e (f r)‖ = f r :=
    ((infinitePlaceRealEmbedding_isometry F v).norm_map_of_map_zero (map_zero e) _).trans
      (Real.norm_of_nonneg (Real.exp_pos _).le)
  have hf : ContinuousAt f q := by
    have hdiv : ContinuousAt (fun r : ℝ ↦ r / q) q := (continuous_id.div_const q).continuousAt
    have hlog := (Real.continuousAt_log (x := (fun r : ℝ ↦ r / q) q)
      (div_ne_zero hq.ne' hq.ne')).comp (f := fun r : ℝ ↦ r / q) hdiv
    exact Real.continuous_exp.continuousAt.comp (hlog.div_const _)
  refine ⟨s, Units.ext ?_, ?_, ?_⟩
  · change u.val * e (f q) = u.val
    simp [f, div_self hq.ne', e]
  · apply Units.isEmbedding_val₀.isInducing.continuousAt_iff.mpr
    exact continuousAt_const.mul ((infinitePlaceRealEmbedding_isometry F v).continuous.continuousAt.comp hf)
  · refine Eventually.of_forall fun r ⟨a, ha⟩ ↦ ?_
    have hr : 0 < r := ha ▸ pow_pos (norm_pos_iff.mpr a.ne_zero) _
    change ‖u.val * e (f r)‖ ^ v.mult = r
    have hpow : f r ^ v.mult = r / q := by
      unfold f
      rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hv, Real.exp_log (div_pos hr hq)]
    rw [norm_mul, mul_pow, he, hpow]
    calc
      _ = q * (r / q) := rfl
      _ = r := by field_simp

private theorem finiteNorm_hasLocalSection (v : Place F) (u : (v.adicCompletion F)ˣ) :
    ∃ s : ℝ → (v.adicCompletion F)ˣ,
      s ‖u.val‖ = u ∧ ContinuousAt s ‖u.val‖ ∧
      ∀ᶠ r in 𝓝 ‖u.val‖, (∃ a : (v.adicCompletion F)ˣ, ‖a.val‖ = r) → ‖(s r).val‖ = r := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let π := chosenFiniteUniformizer F v
  have hπ := chosenFiniteUniformizer_spec F v
  have ho (a : (v.adicCompletion F)ˣ) : ∃ n : ℤ, ‖a.val‖ = q ^ n := by
    obtain ⟨n, hn⟩ := finiteCompletion_norm_zpow F v π hπ a.val a.ne_zero
    refine ⟨-n, ?_⟩
    rw [hn, norm_finiteUniformizer F v _ hπ, zpow_neg, inv_zpow]
  obtain ⟨n, hn⟩ := ho u
  refine ⟨fun _ ↦ u, rfl, continuousAt_const, ?_⟩
  have he : Ioo (q ^ (n - 1)) (q ^ (n + 1)) ∈ 𝓝 ‖u.val‖ :=
    Ioo_mem_nhds (hn ▸ zpow_lt_zpow_right₀ hq (by omega)) (hn ▸ zpow_lt_zpow_right₀ hq (by omega))
  filter_upwards [he] with r hr
  rintro ⟨a, ha⟩
  obtain ⟨m, hm⟩ := ho a
  have hrm : r = q ^ m := ha.symm.trans hm
  rw [hrm] at hr ⊢
  have hlt : StrictMono (fun k : ℤ ↦ q ^ k) := fun _ _ h ↦ zpow_lt_zpow_right₀ hq h
  have hm₁ : n - 1 < m := hlt.lt_iff_lt.mp hr.1
  have hm₂ : m < n + 1 := hlt.lt_iff_lt.mp hr.2
  rw [show m = n by omega, ← hn]

private theorem orbitNorm_hasLocalSection (i : OrbitIndex F S) (u : (OrbitField F S i)ˣ) :
    ∃ s : ℝ → (OrbitField F S i)ˣ,
      s (‖u.val‖ ^ orbitWeight F S i) = u ∧ ContinuousAt s (‖u.val‖ ^ orbitWeight F S i) ∧
        ∀ᶠ r in 𝓝 (‖u.val‖ ^ orbitWeight F S i),
          (∃ a : (OrbitField F S i)ˣ, ‖a.val‖ ^ orbitWeight F S i = r) →
          ‖(s r).val‖ ^ orbitWeight F S i = r := by
  cases i with
  | inl v => exact archNorm_hasLocalSection F v u
  | inr v => simpa only [orbitWeight, pow_one] using finiteNorm_hasLocalSection F v.val u


private def sOrbitLabel : Option (OrbitIndex F S) → SAdeles F S
  | none => 1
  | some v => sAdelicCoordinatePoint F S v

/-- The label space of the S-local action, with its inherited topology. -/
def sAdelicOrbitLabels : Set (SAdeles F S) := Set.range (sOrbitLabel F S)

theorem sAdelicOrbitLabels_eq :
    sAdelicOrbitLabels F S = {1} ∪ Set.range (sAdelicCoordinatePoint F S) := by
  ext x
  constructor
  · rintro ⟨(_ | v), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (mem_range_self v)
  · rintro (h | ⟨v, hv⟩)
    · exact ⟨none, mem_singleton_iff.mp h |>.symm⟩
    · exact ⟨some v, hv⟩

private theorem orbitProductEquiv_label (o : Option (OrbitIndex F S)) :
    orbitProductEquiv F S (sOrbitLabel F S o) = finiteCoordinateLabel (OrbitField F S) o := by
  funext i
  cases o with
  | none => simp [sOrbitLabel, finiteCoordinateLabel]
  | some j =>
    cases i with
    | inl v =>
      cases j with
      | inl w =>
        simp only [finiteCoordinateLabel, Option.some.injEq, Sum.inl.injEq]
        change archimedeanCoordinateLine F w 0 v = if w = v then 0 else 1
        by_cases h : v = w
        · subst w; simp [archimedeanCoordinateLine]
        · simp [archimedeanCoordinateLine, h, Ne.symm h]
      | inr w => simp [finiteCoordinateLabel]; rfl
    | inr v =>
      cases j with
      | inl w => simp [finiteCoordinateLabel]; rfl
      | inr w =>
        simp only [finiteCoordinateLabel, Option.some.injEq, Sum.inr.injEq]
        change Function.update (1 : (j : S) → j.val.adicCompletion F) w 0 v =
          if w = v then 0 else 1
        by_cases h : v = w
        · subst w; simp
        · simp [Function.update_of_ne h, Ne.symm h]

private theorem sOrbitLabel_injective : Injective (sOrbitLabel F S) := by
  intro a b h
  have he := (orbitProductEquiv_label F S a).symm.trans
    ((congrArg (orbitProductEquiv F S) h).trans (orbitProductEquiv_label F S b))
  have ha (i : OrbitIndex F S) : a = some i ↔ b = some i := by
    have hcoord := congrArg (fun x ↦ x i) he
    by_cases ha : a = some i <;> by_cases hb : b = some i <;>
      simp_all [finiteCoordinateLabel]
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some i => exact (ha i).mpr rfl
  | some i => exact ((ha i).mp rfl).symm

private local instance : TopologicalSpace (Option (OrbitIndex F S)) := ⊥
private local instance : DiscreteTopology (Option (OrbitIndex F S)) := ⟨rfl⟩

private theorem sOrbitAdeles_hausdorff : T2Space (SAdeles F S) :=
  (orbitProductHomeomorph F S).isEmbedding.t2Space

private def sOrbitLabelHomeomorph : Option (OrbitIndex F S) ≃ₜ sAdelicOrbitLabels F S := by
  letI := sOrbitAdeles_hausdorff F S
  let f (o : Option (OrbitIndex F S)) : sAdelicOrbitLabels F S :=
    ⟨sOrbitLabel F S o, mem_range_self o⟩
  have h : IsHomeomorph f := isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_of_discreteTopology, fun _ _ h ↦ sOrbitLabel_injective F S (congrArg Subtype.val h),
      fun ⟨_, o, ho⟩ ↦ ⟨o, Subtype.ext ho⟩⟩
  exact (Equiv.ofBijective f h.bijective).toHomeomorphOfContinuousOpen h.continuous h.isOpenMap

private abbrev LocalG := (sLocalIdeleNorm F S).ker
private abbrev ModelG := (finiteCoordinateUnitNorm (OrbitField F S) (orbitWeight F S)).ker

private def orbitNormOneHomeo : LocalG F S ≃ₜ ModelG F S :=
  (orbitUnitsEquiv F S).toHomeomorph.subtype fun a ↦ by
    change sLocalIdeleNorm F S a = 1 ↔
      finiteCoordinateUnitNorm (OrbitField F S) (orbitWeight F S) (orbitUnitsEquiv F S a) = 1
    rw [orbitUnitNorm_eq]

/-- The S-local norm-one union of orbits, with the topology inherited from the S-adeles. -/
def sAdelicNormOneOrbitSpace : Set (SAdeles F S) :=
  range (fun p : LocalG F S × sAdelicOrbitLabels F S ↦ p.1.val.val * p.2.val)

def sAdelicNormOneOrbitMap (p : LocalG F S × sAdelicOrbitLabels F S) :
    sAdelicNormOneOrbitSpace F S := ⟨_, mem_range_self p⟩

private theorem orbitProductEquiv_orbitValue (a : LocalG F S) (o : Option (OrbitIndex F S)) :
    orbitProductEquiv F S (a.val.val * sOrbitLabel F S o) =
      finiteCoordinateOrbitValue (OrbitField F S) (orbitWeight F S) (orbitNormOneHomeo F S a) o := by
  rw [map_mul, orbitProductEquiv_label]
  rfl

private abbrev ModelX := finiteCoordinateOrbitSpace (OrbitField F S) (orbitWeight F S)

private def sOrbitTargetHomeo : sAdelicNormOneOrbitSpace F S ≃ₜ ModelX F S :=
  (orbitProductHomeomorph F S).subtype fun x ↦ by
    constructor
    · rintro ⟨⟨a, z⟩, hz⟩
      obtain ⟨o, ho⟩ := z.property
      exact ⟨((orbitNormOneHomeo F S) a, o),
        (orbitProductEquiv_orbitValue F S a o).symm.trans
          (congrArg (orbitProductEquiv F S) ((congrArg (a.val.val * ·) ho).trans hz))⟩
    · rintro ⟨⟨a, o⟩, h⟩
      let b := (orbitNormOneHomeo F S).symm a
      have hb := (orbitNormOneHomeo F S).apply_symm_apply a
      refine ⟨(b, ⟨_, mem_range_self o⟩), (orbitProductEquiv F S).injective ?_⟩
      rw [orbitProductEquiv_orbitValue, hb]
      exact h

set_option maxHeartbeats 800000 in
/-- The S-local action map of Lemma 8.2.0.3(1) is an open quotient. -/
theorem sAdelicNormOneOrbitMap_openQuotient :
    IsOpenQuotientMap (sAdelicNormOneOrbitMap F S) := by
  let source := (orbitNormOneHomeo F S).prodCongr (sOrbitLabelHomeomorph F S).symm
  have he : sAdelicNormOneOrbitMap F S =
      (sOrbitTargetHomeo F S).symm ∘
        (finiteCoordinateOrbitMap (OrbitField F S) (orbitWeight F S) ∘ source) := by
    funext p
    apply (sOrbitTargetHomeo F S).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    apply Subtype.ext
    have hs := (sOrbitLabelHomeomorph F S).apply_symm_apply p.2
    change orbitProductEquiv F S (p.1.val.val * p.2.val) =
      finiteCoordinateOrbitValue (OrbitField F S) (orbitWeight F S)
        (orbitNormOneHomeo F S p.1) ((sOrbitLabelHomeomorph F S).symm p.2)
    refine (congrArg (fun z : SAdeles F S ↦ orbitProductEquiv F S (p.1.val.val * z))
      (congrArg Subtype.val hs).symm).trans ?_
    exact orbitProductEquiv_orbitValue F S _ _
  rw [he]
  exact (sOrbitTargetHomeo F S).symm.isOpenQuotientMap.comp
    ((finiteCoordinateOrbitMap_openQuotient _ _ (orbitWeight_pos F S)
      (orbitNorm_hasLocalSection F S)).comp source.isOpenQuotientMap)

/-- The S-local orbit space has all the topological properties asserted in Lemma 8.2.0.3. -/
theorem sAdelicNormOneOrbitSpace_topology_properties :
    T2Space (sAdelicNormOneOrbitSpace F S) ∧
    SecondCountableTopology (sAdelicNormOneOrbitSpace F S) ∧
    MetrizableSpace (sAdelicNormOneOrbitSpace F S) ∧
    PerfectlyNormalSpace (sAdelicNormOneOrbitSpace F S) ∧
    SeparableSpace (sAdelicNormOneOrbitSpace F S) ∧
    LocallyCompactSpace (sAdelicNormOneOrbitSpace F S) ∧
    SigmaCompactSpace (sAdelicNormOneOrbitSpace F S) ∧
    ParacompactSpace (sAdelicNormOneOrbitSpace F S) := by
  letI := sOrbitAdeles_hausdorff F S
  letI : SecondCountableTopology ((SAdeles F S)ˣ) := sLocalIdeles_secondCountable F S
  letI : SecondCountableTopology (LocalG F S) := IsEmbedding.subtypeVal.secondCountableTopology
  letI := sLocalIdeles_locallyCompact F S
  letI : SecondCountableTopology (sAdelicOrbitLabels F S) :=
    (sOrbitLabelHomeomorph F S).symm.isEmbedding.secondCountableTopology
  letI : LocallyCompactSpace (sAdelicOrbitLabels F S) :=
    (sOrbitLabelHomeomorph F S).symm.isClosedEmbedding.locallyCompactSpace
  have hnorm : Continuous (sLocalIdeleNorm F S) := by
    simp only [show (sLocalIdeleNorm F S : (SAdeles F S)ˣ → ℝ) =
      (finiteCoordinateNorm (OrbitField F S) (orbitWeight F S)) ∘
        (orbitProductHomeomorph F S) ∘ Units.val from funext fun a ↦ (orbitUnitNorm_eq F S a).symm]
    exact (finiteCoordinateNorm_continuous _ _).comp
      ((orbitProductHomeomorph F S).continuous.comp Units.continuous_val)
  letI : LocallyCompactSpace (LocalG F S) := (isClosed_eq hnorm continuous_const).locallyCompactSpace
  have h := sAdelicNormOneOrbitMap_openQuotient F S
  letI := h.isQuotientMap.secondCountableTopology h.isOpenMap
  letI := h.locallyCompactSpace
  letI : MetricSpace (sAdelicNormOneOrbitSpace F S) := metrizableSpaceMetric _
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

end Masullo
