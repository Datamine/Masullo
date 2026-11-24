import NormOneOrbitTopology
import FiniteAdelicOrbits
import AdelicArchimedeanOrbits
import AdelicHaarScaling
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.EMetricSpace.Paracompact

open Filter Function IsDedekindDomain NumberField Set Topology TopologicalSpace
open scoped Classical NumberField RestrictedProduct

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev G := (ideleNorm F).ker

/-- The labels (Z_F), with the subspace topology from the global adeles. -/
def adelicOrbitLabels : Set (Adeles F) :=
  {1} ∪ range (adelicCoordinatePoint F)

/-- The map from the product of the norm-one ideles with the coordinate labels in Lemma 8.2.0.3. -/
def adelicNormOneOrbitMap (p : G F × adelicOrbitLabels F) : adelicNormOneOrbitSpace F :=
  ⟨p.1.val.val * p.2.val, by
    rcases p.2.property with h | ⟨v, hv⟩
    · exact Or.inl (mem_range.mpr ⟨p.1, by rw [mem_singleton_iff.mp h, mul_one]⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨v, mem_range.mpr ⟨p.1, by rw [hv]⟩⟩)⟩

theorem adelicNormOneOrbitMap_continuous : Continuous (adelicNormOneOrbitMap F) := by
  apply Continuous.subtype_mk
  exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem adelicNormOneOrbitMap_surjective : Surjective (adelicNormOneOrbitMap F) := by
  intro y
  rcases y.property with ⟨g, hg⟩ | hy
  · refine ⟨(g, ⟨1, Or.inl rfl⟩), Subtype.ext ?_⟩
    change g.val.val * 1 = y.val
    simpa using hg
  · obtain ⟨v, g, hg⟩ := mem_iUnion.mp hy
    exact ⟨(g, ⟨_, Or.inr (mem_range_self v)⟩), Subtype.ext hg⟩

private def returnNorm (v : Place F) : ℝ := (v.asIdeal.absNorm : ℝ)

private theorem one_lt_returnNorm (v : Place F) : 1 < returnNorm F v := by
  unfold returnNorm
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

private def returnParameter (v : Place F) : Multiplicative ℝ :=
  Multiplicative.ofAdd (-(Real.log (returnNorm F v)))

private def markedIdele (w : InfinitePlace F) (v : Place F) : Idele F :=
  onePlaceExpSection F w (returnParameter F v) *
    singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹

private theorem markedIdele_norm (w : InfinitePlace F) (v : Place F) :
    ideleNorm F (markedIdele F w v) = 1 := by
  have hv := zero_lt_one.trans (one_lt_returnNorm F v)
  rw [markedIdele, map_mul, ideleNorm_onePlaceExpSection, singleFiniteIdele_norm]
  change Real.exp (-Real.log (returnNorm F v)) * ‖(↑(chosenFiniteUniformizer F v)⁻¹ :
    v.adicCompletion F)‖ = 1
  rw [Real.exp_neg, Real.exp_log hv, Units.val_inv_eq_inv_val, norm_inv,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_inv]
  exact inv_mul_cancel₀ hv.ne'

private def markedPoint (w : InfinitePlace F) (v : Place F) : adelicNormOneOrbitSpace F :=
  ⟨(markedIdele F w v).val * adelicCoordinatePoint F (.inr v), Or.inr
    (mem_iUnion.mpr ⟨Sum.inr v, mem_range.mpr ⟨⟨markedIdele F w v, markedIdele_norm F w v⟩, rfl⟩⟩)⟩

private theorem markedPoint_formula (w : InfinitePlace F) (v : Place F) :
    (markedPoint F w v).val = ((onePlaceExpSection F w (returnParameter F v)).val.1,
      (adelicCoordinatePoint F (.inr v)).2) := by
  have hf : (singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹).val *
      adelicCoordinatePoint F (.inr v) = adelicCoordinatePoint F (.inr v) :=
    (adelic_finite_coordinate_stabilizer F v _).mpr ⟨_, rfl⟩
  change ((onePlaceExpSection F w (returnParameter F v) *
    singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹).val * _) = _
  rw [Units.val_mul, mul_assoc, hf]
  refine Prod.ext ?_ ?_
  · change (onePlaceExpSection F w (returnParameter F v)).val.1 * 1 = _
    simp
  · change (onePlaceExpSection F w (returnParameter F v)).val.2 * _ = _
    rw [show (onePlaceExpSection F w (returnParameter F v)).val.2 = 1 from rfl, one_mul]

private theorem finite_label_coordinate (v u : Place F) :
    (adelicCoordinatePoint F (.inr v)).2 u = if u = v then 0 else 1 := rfl

private theorem markedIdele_finite_norm (w : InfinitePlace F) (v : Place F) :
    ‖(markedIdele F w v).val.2 v‖ = returnNorm F v := by
  change ‖(onePlaceExpSection F w (returnParameter F v)).val.2 v *
    (singleFiniteIdele F v (chosenFiniteUniformizer F v)⁻¹).val.2 v‖ = _
  rw [show (onePlaceExpSection F w (returnParameter F v)).val.2 = 1 from rfl]
  change ‖(1 : v.adicCompletion F) * Function.update (fun j : Place F ↦
    (1 : j.adicCompletion F)) v ((chosenFiniteUniformizer F v)⁻¹).val v‖ = _
  rw [Function.update_self, one_mul, Units.val_inv_eq_inv_val, norm_inv,
    norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v), inv_inv]
  rfl

private theorem finite_coord_ne_zero (a : Idele F) (v : Place F) : a.val.2 v ≠ 0 := by
  have h := congrArg (fun b : Adeles F ↦ b.2 v) a.val_inv
  change a.val.2 v * a.inv.2 v = 1 at h
  intro e
  simp [e] at h

private theorem label_eq_of_finite_coord_zero (z : adelicOrbitLabels F) (v : Place F)
    (h : z.val.2 v = 0) : z.val = adelicCoordinatePoint F (.inr v) := by
  rcases z.property with h1 | ⟨i, hi⟩
  · have he : z.val = 1 := mem_singleton_iff.mp h1
    rw [he] at h
    exact (one_ne_zero h).elim
  · rw [← hi] at h ⊢
    cases i with
    | inl w => exact (one_ne_zero h).elim
    | inr u =>
      rw [finite_label_coordinate] at h
      by_cases hu : v = u
      · subst u
        rfl
      · simp [hu] at h

private theorem markedPoint_preimage_finite_norm (w : InfinitePlace F) (v : Place F)
    (p : G F × adelicOrbitLabels F) (hp : adelicNormOneOrbitMap F p = markedPoint F w v) :
    ‖p.1.val.val.2 v‖ = returnNorm F v := by
  have hz : p.2.val.2 v = 0 := by
    have hg := congrArg (fun x : adelicNormOneOrbitSpace F ↦ x.val.2 v) hp
    change p.1.val.val.2 v * p.2.val.2 v = (markedPoint F w v).val.2 v at hg
    rw [markedPoint_formula, finite_label_coordinate, ite_eq_left rfl] at hg
    exact (mul_eq_zero.mp hg).resolve_left (finite_coord_ne_zero F p.1.val v)
  have h := congrArg Subtype.val hp
  change p.1.val.val * p.2.val = (markedIdele F w v).val * adelicCoordinatePoint F (.inr v) at h
  rw [label_eq_of_finite_coord_zero F p.2 v hz] at h
  let c : Idele F := p.1.val / markedIdele F w v
  have hc : c * markedIdele F w v = p.1.val := div_mul_cancel _ _
  have hfix : c.val * adelicCoordinatePoint F (.inr v) = adelicCoordinatePoint F (.inr v) := by
    apply (markedIdele F w v).isUnit.mul_right_inj.mp
    rw [← mul_assoc, mul_comm (markedIdele F w v).val c.val, ← Units.val_mul, hc, h]
  have hn : ideleNorm F c = 1 := by
    change ideleNorm F (p.1.val / markedIdele F w v) = 1
    rw [map_div, markedIdele_norm, p.1.property, div_one]
  obtain ⟨u, hu⟩ := (adelic_finite_coordinate_stabilizer F v c).mp hfix
  rw [← hu, singleFiniteIdele_norm] at hn
  have hcv : c.val.2 v = u.val := by
    rw [← hu]
    change Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v u.val v = _
    rw [Function.update_self]
  have hpv := congrArg (fun a : Idele F ↦ a.val.2 v) hc
  change c.val.2 v * (markedIdele F w v).val.2 v = _ at hpv
  rw [← hpv, norm_mul, hcv, hn, one_mul, markedIdele_finite_norm]

private theorem returnNorm_tendsto_atTop : Tendsto (returnNorm F) cofinite atTop := by
  have h : Tendsto (fun v : Place F ↦ v.asIdeal.absNorm) cofinite atTop := by
    apply tendsto_atTop.mpr
    intro n
    apply eventually_cofinite.mpr
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).preimage
      (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h)).subset ?_
    intro v hv
    exact (lt_of_not_ge hv).le
  exact tendsto_natCast_atTop_atTop.comp h

private theorem markedPoint_tendsto_archimedean (w : InfinitePlace F) :
    Tendsto (fun v ↦ (markedPoint F w v).val) cofinite
      (𝓝 (adelicCoordinatePoint F (.inl w))) := by
  have ht : Tendsto (fun v ↦ (returnParameter F v).toAdd) cofinite atBot :=
    tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.comp (returnNorm_tendsto_atTop F))
  have hw : 0 < (w.mult : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero InfinitePlace.mult_ne_zero))
  have hR : Tendsto (fun v ↦ Real.exp ((returnParameter F v).toAdd * (w.mult : ℝ)⁻¹))
      cofinite (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_pos hw).mpr ht)
  have ha : Tendsto (fun v ↦ (onePlaceExpSection F w (returnParameter F v)).val.1)
      cofinite (𝓝 (archimedeanCoordinateLine F w 0)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases he : j = w
    · subst j
      simpa [Function.comp_def, onePlaceExpSection, (archimedeanExpSection_components F _ _).1,
        archimedeanCoordinateLine] using
        ((infinitePlaceRealEmbedding_isometry F w).continuous.tendsto 0).comp hR
    · simpa [onePlaceExpSection, (archimedeanExpSection_components F _ _).1,
        archimedeanCoordinateLine, he] using
        (tendsto_const_nhds : Tendsto (fun _ : Place F ↦ (1 : j.Completion)) cofinite (𝓝 1))
  have hf : Tendsto (fun v : Place F ↦ (adelicCoordinatePoint F (.inr v)).2) cofinite (𝓝 1) :=
    continuous_snd.continuousAt.tendsto.comp (adelic_finite_coordinate_points_tendsto_one F)
  exact (ha.prodMk_nhds hf).congr' (Eventually.of_forall fun v ↦
    (markedPoint_formula F w v).symm)

private def archimedeanLimitPoint (w : InfinitePlace F) : adelicNormOneOrbitSpace F :=
  ⟨adelicCoordinatePoint F (.inl w), Or.inr (mem_iUnion.mpr ⟨Sum.inl w,
    mem_range.mpr ⟨1, by simp⟩⟩)⟩

private theorem archimedeanLimitPoint_not_marked (w : InfinitePlace F) (v : Place F) :
    archimedeanLimitPoint F w ≠ markedPoint F w v := by
  intro h
  have he := congrArg (fun x : adelicNormOneOrbitSpace F ↦ x.val.2 v) h
  change (1 : v.adicCompletion F) = (markedPoint F w v).val.2 v at he
  rw [markedPoint_formula, finite_label_coordinate, ite_eq_left rfl] at he
  exact one_ne_zero he

private theorem markedPoint_preimage_forces_place
    (w : InfinitePlace F) (v : Place F) (S : Finset (Place F))
    (p : G F × adelicOrbitLabels F) (hp : adelicNormOneOrbitMap F p = markedPoint F w v)
    (hS : p.1.val ∈ sIdeleBlock F S) : v ∈ S := by
  by_contra hv
  have he := (sIdeleBlock_mem_iff F S p.1.val).mp hS v hv
  have hN : ‖p.1.val.val.2 v‖ = 1 := by
    rw [FinitePlace.norm_def, (ideleOrder_eq_zero_iff F p.1.val v).mp he, map_one, NNReal.coe_one]
  rw [markedPoint_preimage_finite_norm F w v p hp] at hN
  exact (one_lt_returnNorm F v).ne' hN

private theorem orbitAdeles_hausdorff : T2Space (Adeles F) := by
  letI : T2Space (FiniteAdeleRing (𝓞 F) F) := T2Space.of_injective_continuous
    (f := fun a : FiniteAdeleRing (𝓞 F) F ↦ (a : (j : Place F) → j.adicCompletion F))
    DFunLike.coe_injective RestrictedProduct.continuous_coe
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  change T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  infer_instance

private theorem markedPoint_preimage_closed (w : InfinitePlace F) :
    IsClosed (adelicNormOneOrbitMap F ⁻¹' range (markedPoint F w)) := by
  letI := orbitAdeles_hausdorff F
  let M := adelicNormOneOrbitMap F
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  let S := (ideleOrder_finite_support F p.1.val).toFinset
  have hS : p.1.val ∈ sIdeleBlock F S := by
    apply (sIdeleBlock_mem_iff F S p.1.val).mpr
    intro v hv
    by_contra he
    exact hv ((ideleOrder_finite_support F p.1.val).mem_toFinset.mpr he)
  let C : Set (adelicNormOneOrbitSpace F) := markedPoint F w '' (↑S : Set (Place F))
  have hC : IsClosed C := (S.finite_toSet.image _).isClosed
  have huv : (fun p : G F × adelicOrbitLabels F ↦ p.1.val) ⁻¹'
      (sIdeleBlock F S : Set (Idele F)) ∈ 𝓝 p :=
    ((sIdeleBlock_open F S).preimage (continuous_subtype_val.comp continuous_fst)).mem_nhds hS
  have hcv : (M ⁻¹' C)ᶜ ∈ 𝓝 p := ((hC.preimage (adelicNormOneOrbitMap_continuous F)).isOpen_compl).mem_nhds
    (fun he ↦ hp (mem_range.mpr (Exists.imp (fun _ h ↦ h.2) he)))
  refine mem_of_superset (inter_mem huv hcv) ?_
  rintro a ⟨ha, hb⟩ ⟨v, hv⟩
  exact hb ⟨v, markedPoint_preimage_forces_place F w v S a hv.symm ha, hv⟩

/-- The global map in Lemma 8.2.0.3(2) is a continuous surjection whose quotient
topology is strictly finer than the inherited adelic topology. -/
theorem adelicNormOneOrbitMap_not_isQuotientMap (w : InfinitePlace F) :
    ¬ IsQuotientMap (adelicNormOneOrbitMap F) := by
  letI := finitePlaces_infinite F
  intro h
  have hclosed := (h.isClosed_preimage).mp (markedPoint_preimage_closed F w)
  have hlim : Tendsto (markedPoint F w) cofinite (𝓝 (archimedeanLimitPoint F w)) :=
    tendsto_subtype_rng.mpr (markedPoint_tendsto_archimedean F w)
  obtain ⟨v, hv⟩ : archimedeanLimitPoint F w ∈ range (markedPoint F w) :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun v ↦ mem_range_self v)
  exact archimedeanLimitPoint_not_marked F w v hv.symm

private abbrev IntegralChart := Πʳ v : Place F,
  [v.adicCompletion F, v.adicCompletionIntegers F]_[⊤]

private def integralChartUpdate (v : Place F) (a : v.adicCompletion F)
    (ha : a ∈ v.adicCompletionIntegers F) : IntegralChart F :=
  ⟨Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v a,
    Eventually.of_forall fun j ↦ by
      by_cases hj : j = v
      · subst j
        rw [Function.update_self]
        exact ha
      · rw [Function.update_of_ne hj]
        exact one_mem _⟩

private def integralChartAtArchZero (w : InfinitePlace F) (a : IntegralChart F) : Adeles F :=
  (archimedeanCoordinateLine F w 0, RestrictedProduct.inclusion _ _ le_top a)

private theorem integralChartAtArchZero_continuous (w : InfinitePlace F) :
    Continuous (integralChartAtArchZero F w) :=
  continuous_const.prodMk (RestrictedProduct.continuous_inclusion le_top)

private theorem integralChart_escaping_updates (a : ∀ v : Place F, v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v ↦ integralChartUpdate F v (a v) (ha v)) cofinite (𝓝 1) := by
  apply RestrictedProduct.isEmbedding_coe_of_top.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_const_nhds.congr'
  have h : ∀ᶠ v : Place F in cofinite, j ≠ v := by simp [eventually_cofinite]
  filter_upwards [h] with v hv
  change (1 : j.adicCompletion F) =
    Function.update (fun k : Place F ↦ (1 : k.adicCompletion F)) v (a v) j
  rw [Function.update_of_ne hv]

private theorem integralChart_update_nbhd (w : InfinitePlace F)
    {U : Set (Adeles F)} (hU : U ∈ 𝓝 (adelicCoordinatePoint F (.inl w))) :
    ∃ v : Place F, ∀ (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F),
      integralChartAtArchZero F w (integralChartUpdate F v a ha) ∈ U := by
  letI := finitePlaces_infinite F
  by_contra! h
  choose a ha hb using h
  have H := (integralChartAtArchZero_continuous F w).tendsto 1 |>.comp
    (integralChart_escaping_updates F a ha)
  obtain ⟨v, hv⟩ := (H.eventually hU).exists
  exact hb v hv

private theorem integralChart_nonzero_update_mem (w : InfinitePlace F) (v : Place F)
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) (ha₀ : a ≠ 0) :
    integralChartAtArchZero F w (integralChartUpdate F v a ha) ∈ adelicNormOneOrbitSpace F := by
  apply Or.inr
  apply mem_iUnion.mpr
  refine ⟨Sum.inl w, ?_⟩
  change _ ∈ range (fun g : (ideleNorm F).ker ↦
    g.val.val * adelicCoordinatePoint F (.inl w))
  rw [adelic_archimedean_normOne_orbit]
  refine ⟨singleFiniteIdele F v (Units.mk0 a ha₀), Prod.ext ?_ ?_⟩
  · change (1 : InfiniteAdeleRing F) * archimedeanCoordinateLine F w 0 = _
    rw [one_mul]
    rfl
  · change (singleFiniteIdele F v (Units.mk0 a ha₀)).val.2 * 1 = _
    rw [mul_one]
    rfl

private theorem integralChart_zero_update_not_mem (w : InfinitePlace F) (v : Place F) :
    integralChartAtArchZero F w (integralChartUpdate F v 0 (zero_mem _)) ∉
      adelicNormOneOrbitSpace F := by
  intro h
  let b : adelicNormOneOrbitSpace F := ⟨_, h⟩
  obtain ⟨p, hp⟩ := adelicNormOneOrbitMap_surjective F b
  have h₁ := congrArg (fun x : adelicNormOneOrbitSpace F ↦ x.val.2 v) hp
  change p.1.val.val.2 v * p.2.val.2 v =
    Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v 0 v at h₁
  rw [Function.update_self] at h₁
  have he := label_eq_of_finite_coord_zero F p.2 v
    ((mul_eq_zero.mp h₁).resolve_left (finite_coord_ne_zero F p.1.val v))
  have h₂ := congrArg Subtype.val hp
  change p.1.val.val * p.2.val = b.val at h₂
  rw [he] at h₂
  have h₃ := congrArg (fun x : Adeles F ↦ x.1 w) h₂
  change p.1.val.val.1 w * 1 = archimedeanCoordinateLine F w 0 w at h₃
  simp [archimedeanCoordinateLine] at h₃
  exact (left_ne_zero_of_mul_eq_one
    (congrArg (fun x : Adeles F ↦ x.1 w) p.1.val.val_inv)) h₃

/-- The other failure in Lemma 8.2.0.3(2). The inherited topology is not
locally compact at any of the infinite coordinate points. -/
theorem adelicNormOneOrbitSpace_no_compact_nbhd (w : InfinitePlace F) :
    ¬ ∃ K : Set (adelicNormOneOrbitSpace F),
      IsCompact K ∧ K ∈ 𝓝 (archimedeanLimitPoint F w) := by
  letI := orbitAdeles_hausdorff F
  rintro ⟨K, hK, hKn⟩
  rw [nhds_subtype_eq_comap] at hKn
  obtain ⟨U, hU, hUK⟩ := Filter.mem_comap.mp hKn
  obtain ⟨v, hv⟩ := integralChart_update_nbhd F w hU
  let π := (chosenFiniteUniformizer F v).val
  have hπ : π ∈ v.adicCompletionIntegers F := by
    change π ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    rw [← finiteCompletion_closedBall F v, Metric.mem_closedBall, dist_zero_right]
    exact (finiteCompletion_uniformizer_contracts F v _ (chosenFiniteUniformizer_spec F v)).le
  let f (n : ℕ) := integralChartUpdate F v (π ^ n) (pow_mem hπ n)
  have hπlim : Tendsto (fun n : ℕ ↦ π ^ n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [norm_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π)
      (finiteCompletion_uniformizer_contracts F v _ (chosenFiniteUniformizer_spec F v))
  have hf : Tendsto f atTop (𝓝 (integralChartUpdate F v 0 (zero_mem _))) := by
    apply RestrictedProduct.isEmbedding_coe_of_top.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hj : j = v
    · subst j
      change Tendsto (fun n ↦ Function.update (fun k : Place F ↦ (1 : k.adicCompletion F))
          v (π ^ n) v) atTop
        (𝓝 (Function.update (fun k : Place F ↦ (1 : k.adicCompletion F)) v 0 v))
      simp only [Function.update_self]
      exact hπlim
    · change Tendsto (fun n ↦ Function.update (fun k : Place F ↦ (1 : k.adicCompletion F))
          v (π ^ n) j) atTop
        (𝓝 (Function.update (fun k : Place F ↦ (1 : k.adicCompletion F)) v 0 j))
      simp only [Function.update_of_ne hj]
      exact tendsto_const_nhds
  have hmem (n : ℕ) : integralChartAtArchZero F w (f n) ∈
      (Subtype.val : adelicNormOneOrbitSpace F → Adeles F) '' K := by
    have hD := integralChart_nonzero_update_mem F w v (π ^ n) (pow_mem hπ n)
      (pow_ne_zero _ (chosenFiniteUniformizer F v).ne_zero)
    exact ⟨⟨_, hD⟩, hUK (hv _ _), rfl⟩
  obtain ⟨y, _, hy⟩ := (hK.image continuous_subtype_val).isClosed.mem_of_tendsto
    (((integralChartAtArchZero_continuous F w).tendsto _).comp hf) (Eventually.of_forall hmem)
  exact integralChart_zero_update_not_mem F w v (hy ▸ y.property)

theorem adelicNormOneOrbitSpace_not_locallyCompact (w : InfinitePlace F) :
    ¬ LocallyCompactSpace (adelicNormOneOrbitSpace F) := by
  intro h
  letI := h
  exact adelicNormOneOrbitSpace_no_compact_nbhd F w (exists_compact_mem_nhds _)

/-- The remaining separation, countability and compact exhaustion properties
of the inherited global topology in Lemma 8.2.0.3. -/
theorem adelicNormOneOrbitSpace_topology_properties :
    T2Space (adelicNormOneOrbitSpace F) ∧
    SecondCountableTopology (adelicNormOneOrbitSpace F) ∧
    MetrizableSpace (adelicNormOneOrbitSpace F) ∧
    PerfectlyNormalSpace (adelicNormOneOrbitSpace F) ∧
    SeparableSpace (adelicNormOneOrbitSpace F) ∧
    SigmaCompactSpace (adelicNormOneOrbitSpace F) ∧
    ParacompactSpace (adelicNormOneOrbitSpace F) := by
  letI := orbitAdeles_hausdorff F
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  letI : SecondCountableTopology (Adeles F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Adeles F)).symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (Idele F) :=
    (Units.isEmbedding_embedProduct (M := Adeles F)).secondCountableTopology
  letI : SecondCountableTopology (G F) := IsEmbedding.subtypeVal.secondCountableTopology
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  letI : LocallyCompactSpace (G F) := (ideles_normOne_isClosed (F := F)).locallyCompactSpace
  have hv : Continuous (fun g : G F ↦ g.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  letI : SigmaCompactSpace (G F) := inferInstance
  letI := finitePlaces_countable F
  let L : Option (InfinitePlace F ⊕ Place F) → Set (Adeles F)
    | none => range (fun g : G F ↦ g.val.val)
    | some v => adelicNormOneCoordinateOrbit F v
  have hL : ∀ a, IsSigmaCompact (L a)
    | none => isSigmaCompact_range hv
    | some v => isSigmaCompact_range (hv.mul continuous_const)
  have heq : adelicNormOneOrbitSpace F = ⋃ a, L a := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨none, hx⟩
      · obtain ⟨v, hv⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨some v, hv⟩
    · intro hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      cases a with
      | none => exact Or.inl ha
      | some v => exact Or.inr (mem_iUnion.mpr ⟨v, ha⟩)
  letI : SigmaCompactSpace (adelicNormOneOrbitSpace F) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (heq.symm ▸ isSigmaCompact_iUnion L hL)
  letI : MetrizableSpace (Adeles F) := inferInstance
  letI : MetricSpace (adelicNormOneOrbitSpace F) :=
    TopologicalSpace.metrizableSpaceMetric _
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end Masullo
