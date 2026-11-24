import FinitePlaceHaar
import ArchimedeanLogarithms
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Filter Function IsDedekindDomain MeasureTheory MeasureTheory.Measure NumberField Set Topology TopologicalSpace
open scoped Classical ENNReal NNReal NumberField Pointwise RestrictedProduct

namespace Masullo

noncomputable section

private theorem secondCountable_restrictedProduct {ι : Type*} [Countable ι]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, SecondCountableTopology (A i)]
    (K : ∀ i, Set (A i)) (hK : ∀ i, IsOpen (K i)) :
    SecondCountableTopology (Πʳ i, [A i, K i]) := by
  have hS (S : Finset ι) : Filter.cofinite ≤ 𝓟 (↑S : Set ι)ᶜ := by
    rw [le_principal_iff]
    exact S.finite_toSet.compl_mem_cofinite
  let U : Finset ι → Set (Πʳ i, [A i, K i]) :=
    fun S => range (RestrictedProduct.inclusion A K (hS S))
  letI (S : Finset ι) : SecondCountableTopology (Πʳ i, [A i, K i]_[𝓟 (↑S : Set ι)ᶜ]) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  letI (S : Finset ι) : SecondCountableTopology (U S) := by
    let e := (RestrictedProduct.isOpenEmbedding_inclusion_principal hK (hS S)).isEmbedding.toHomeomorph
    exact e.symm.isEmbedding.secondCountableTopology
  apply secondCountableTopology_of_countable_cover
    (fun S => (RestrictedProduct.isOpenEmbedding_inclusion_principal hK (hS S)).isOpen_range)
  apply eq_univ_of_forall
  intro x
  have hf : {i | x i ∉ K i}.Finite := eventually_cofinite.mp x.property
  refine mem_iUnion.mpr ⟨hf.toFinset, ⟨⟨fun i => x i, ?_⟩, ?_⟩⟩
  · rw [eventually_principal]
    intro i hi
    exact not_not.mp (fun h => hi (hf.mem_toFinset.mpr h))
  · exact RestrictedProduct.ext _ _ fun _ => rfl

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F
private abbrev L (v : Place F) := v.adicCompletion F
private abbrev O (v : Place F) : Subring (L F v) := (v.adicCompletionIntegers F).toSubring

theorem finitePlaces_countable : Countable (Place F) := by
  letI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  letI : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  let s (t : Finset (𝓞 F)) := Ideal.span (t : Set (𝓞 F))
  have h : Surjective s := by
    intro I
    obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (R := 𝓞 F) I)
    exact ⟨t, ht⟩
  letI : Countable (Ideal (𝓞 F)) := h.countable
  exact HeightOneSpectrum.asIdeal_injective.countable

theorem finiteAdeles_secondCountable : SecondCountableTopology (FinAdeles F) := by
  letI : Countable (Place F) := finitePlaces_countable F
  letI (v : Place F) : SecondCountableTopology (L F v) := finitePlace_secondCountable F v
  exact secondCountable_restrictedProduct (fun v => (O F v : Set (L F v)))
    (fun v => Valued.isOpen_valuationSubring (L F v))

private abbrev RPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev CPlaces := {v : InfinitePlace F // v.IsComplex}
private abbrev Mixed := (RPlaces F → ℝ) × (CPlaces F → ℂ)

theorem adeles_secondCountable : SecondCountableTopology (Adeles F) := by
  letI : SecondCountableTopology (FinAdeles F) := finiteAdeles_secondCountable F
  letI : SecondCountableTopology (InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FinAdeles F))

private abbrev Tail (S : Finset (Place F)) :=
  Πʳ v : {v : Place F // v ∉ S}, [L F v.val, O F v.val]

private abbrev FinCoordinates (S : Finset (Place F)) := (v : S) → L F v.val

def finiteCoordinateSplit (S : Finset (Place F)) :
    FinCoordinates F S × Tail F S ≃ₜ+ FinAdeles F := by
  let e := restrictedProductSplitOpenTail (fun v => (O F v : Set (L F v))) S
    (fun v _ => Valued.isOpen_valuationSubring (L F v))
  refine { toHomeomorph := e, map_add' := ?_ }
  intro x y
  apply RestrictedProduct.ext
  intro v
  let f (p : FinCoordinates F S × Tail F S) : L F v :=
    if h : v ∈ S then p.1 ⟨v, h⟩ else p.2 ⟨v, h⟩
  change f (x + y) = f x + f y
  unfold f
  by_cases h : v ∈ S <;> simp only [h, dite_true, dite_false] <;> rfl

private def tailIntegralBlock (S : Finset (Place F)) : Set (Tail F S) :=
  {x | ∀ v, x v ∈ O F v.val}

private theorem tailIntegralBlock_open (S : Finset (Place F)) :
    IsOpen (tailIntegralBlock F S) :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring (L F v.val))

private theorem tailIntegralBlock_compact (S : Finset (Place F)) :
    IsCompact (tailIntegralBlock F S) := by
  letI (v : {v : Place F // v ∉ S}) : CompactSpace (O F v.val) := compactSpace_adicIntegers v.val
  let j : ((v : {v : Place F // v ∉ S}) → O F v.val) → Tail F S :=
    RestrictedProduct.inclusion _ _ le_top ∘ RestrictedProduct.homeoTop
  have hj : Continuous j :=
    (RestrictedProduct.continuous_inclusion le_top).comp RestrictedProduct.homeoTop.continuous
  have h : range j = tailIntegralBlock F S := RestrictedProduct.range_structureMap
    (fun v : {v : Place F // v ∉ S} => L F v.val)
    (fun v : {v : Place F // v ∉ S} => (O F v.val : Set (L F v.val)))
  exact h ▸ isCompact_range hj

private theorem tail_locallyCompact (S : Finset (Place F)) :
    LocallyCompactSpace (Tail F S) := by
  let ι := {v : Place F // v ∉ S}
  letI : Fact (∀ v : ι, IsOpen (O F v.val : Set (L F v.val))) :=
    ⟨fun v => Valued.isOpen_valuationSubring (L F v.val)⟩
  letI (v : ι) : LocallyCompactSpace (L F v.val) := finitePlace_locallyCompact F v.val
  letI (v : ι) : CompactSpace (O F v.val) := compactSpace_adicIntegers v.val
  exact inferInstanceAs (LocallyCompactSpace (Πʳ v : ι, [L F v.val, O F v.val]))

private theorem tail_secondCountable (S : Finset (Place F)) :
    SecondCountableTopology (Tail F S) := by
  let ι := {v : Place F // v ∉ S}
  letI : Countable (Place F) := finitePlaces_countable F
  letI : Countable ι := inferInstanceAs (Countable {v : Place F // v ∉ S})
  letI (v : ι) : SecondCountableTopology (L F v.val) := finitePlace_secondCountable F v.val
  exact secondCountable_restrictedProduct (ι := ι) (A := fun v => L F v.val)
    (fun v => (O F v.val : Set (L F v.val)))
    (fun v => Valued.isOpen_valuationSubring (L F v.val))


private def fullCoordinateSplit (S : Finset (Place F)) :
    Mixed F × (FinCoordinates F S × Tail F S) ≃ₜ+ Adeles F where
  toHomeomorph := (infiniteAdeleMixedHomeomorph F).symm.prodCongr
    (finiteCoordinateSplit F S).toHomeomorph
  map_add' _ _ := Prod.ext
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _)
    ((finiteCoordinateSplit F S).map_add _ _)

theorem finiteCoordinateSplit_apply (S : Finset (Place F))
    (p : FinCoordinates F S × Tail F S) (v : Place F) :
    (finiteCoordinateSplit F S p) v = if h : v ∈ S then p.1 ⟨v, h⟩ else p.2 ⟨v, h⟩ := by
  exact restrictedProductSplitOpenTail_apply (fun v => (O F v : Set (L F v))) S
    (fun v _ => Valued.isOpen_valuationSubring (L F v)) p v

private theorem fullCoordinateSplit_mul (S : Finset (Place F))
    (p q : Mixed F × (FinCoordinates F S × Tail F S)) :
    fullCoordinateSplit F S (p * q) = fullCoordinateSplit F S p * fullCoordinateSplit F S q := by
  apply Prod.ext
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_mul _ _
  · apply RestrictedProduct.ext
    intro v
    change finiteCoordinateSplit F S (p.2 * q.2) v =
      finiteCoordinateSplit F S p.2 v * finiteCoordinateSplit F S q.2 v
    rw [finiteCoordinateSplit_apply, finiteCoordinateSplit_apply, finiteCoordinateSplit_apply]
    by_cases h : v ∈ S <;> simp only [h, dite_true, dite_false] <;> rfl

private def fullCoordinateRingEquiv (S : Finset (Place F)) :
    Mixed F × (FinCoordinates F S × Tail F S) ≃+* Adeles F where
  toEquiv := (fullCoordinateSplit F S).toEquiv
  map_add' := (fullCoordinateSplit F S).map_add
  map_mul' := fullCoordinateSplit_mul F S

private theorem localIntegral_iff_norm (v : Place F) (x : L F v) :
    x ∈ O F v ↔ ‖x‖ ≤ 1 := by
  have hq : (1 : ℝ≥0) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  change x ∈ v.adicCompletionIntegers F ↔ _
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def]
  exact (WithZeroMulInt.toNNReal_le_one_iff hq).symm

private theorem closedBall_units_smul {K : Type*} [NormedDivisionRing K] [NormMulClass K]
    (u : Kˣ) : u • Metric.closedBall (0 : K) 1 = Metric.closedBall 0 ‖u.val‖ := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem, Metric.mem_closedBall, Metric.mem_closedBall,
    dist_zero_right, dist_zero_right]
  change ‖u.inv * x‖ ≤ 1 ↔ ‖x‖ ≤ ‖u.val‖
  rw [norm_mul, u.inv_eq_val_inv, Units.val_inv_eq_inv_val, norm_inv,
    inv_mul_le_iff₀ (norm_pos_iff.mpr u.ne_zero), mul_one]

private theorem archBall_measure_scaling {K : Type*} [NormedDivisionRing K] [NormMulClass K]
    [NormedSpace ℝ K] [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (u : Kˣ) :
    μ (u • Metric.closedBall (0 : K) 1) =
      (‖u.val‖₊ : ℝ≥0∞) ^ Module.finrank ℝ K * μ (Metric.closedBall 0 1) := by
  rw [closedBall_units_smul]
  have h := addHaar_closedBall_mul_of_pos μ 0 (norm_pos_iff.mpr u.ne_zero) 1
  simpa only [mul_one, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm] using h


private theorem unit_smul_prod {A B : Type*} [Monoid A] [Monoid B] (u : (A × B)ˣ)
    (X : Set A) (Y : Set B) :
    u • (X ×ˢ Y) = ((MulEquiv.prodUnits u).1 • X) ×ˢ ((MulEquiv.prodUnits u).2 • Y) := by
  ext a
  simp only [mem_smul_set_iff_inv_smul_mem, mem_prod]
  rfl

private theorem unit_smul_pi {ι : Type*} {A : ι → Type*} [∀ i, Monoid (A i)]
    (u : (∀ i, A i)ˣ) (B : ∀ i, Set (A i)) :
    u • Set.pi univ B = Set.pi univ (fun i => (MulEquiv.piUnits u) i • B i) := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_univ_pi]
  rfl

private theorem finiteCoordinateSplit_tail_unit (S : Finset (Place F))
    (g : Idele F) (v : {v : Place F // v ∉ S}) :
    let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
    (MulEquiv.prodUnits (MulEquiv.prodUnits w).2).2.val v = g.val.2 v.val := by
  let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
  have hw : fullCoordinateSplit F S w.val = g.val :=
    (fullCoordinateRingEquiv F S).apply_symm_apply g.val
  have h := congrArg (fun a : Adeles F => a.2 v.val) hw
  change finiteCoordinateSplit F S w.val.2 v.val = g.val.2 v.val at h
  rwa [finiteCoordinateSplit_apply, dite_eq_right v.property] at h

private theorem finiteCoordinateSplit_selected_unit (S : Finset (Place F))
    (g : Idele F) (v : S) :
    let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
    ((MulEquiv.piUnits (MulEquiv.prodUnits (MulEquiv.prodUnits w).2).1) v).val = g.val.2 v.val := by
  let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
  have hw : fullCoordinateSplit F S w.val = g.val :=
    (fullCoordinateRingEquiv F S).apply_symm_apply g.val
  have h := congrArg (fun a : Adeles F => a.2 v.val) hw
  change finiteCoordinateSplit F S w.val.2 v.val = g.val.2 v.val at h
  rwa [finiteCoordinateSplit_apply, dite_eq_left v.property] at h

private theorem tailIntegralBlock_invariant (S : Finset (Place F)) (g : Idele F)
    (hg : ∀ v ∉ S, ‖g.val.2 v‖ = 1) :
    let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
    (MulEquiv.prodUnits (MulEquiv.prodUnits w).2).2 • tailIntegralBlock F S =
      tailIntegralBlock F S := by
  let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
  let t := (MulEquiv.prodUnits (MulEquiv.prodUnits w).2).2
  have ht (v : {v : Place F // v ∉ S}) : ‖t.val v‖ = 1 :=
    (congrArg norm (finiteCoordinateSplit_tail_unit F S g v)).trans (hg v.val v.property)
  have hi (v : {v : Place F // v ∉ S}) : ‖t.inv v‖ = 1 := by
    have he := congrArg (fun a : Tail F S => a v) t.val_inv
    change t.val v * t.inv v = 1 at he
    have h := congrArg norm he
    rw [norm_mul, ht, one_mul, norm_one] at h
    exact h
  change t • tailIntegralBlock F S = tailIntegralBlock F S
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change (∀ v : {v : Place F // v ∉ S}, t.inv v * x v ∈ O F v.val) ↔ _
  change (∀ v : {v : Place F // v ∉ S}, t.inv v * x v ∈ O F v.val) ↔
    ∀ v : {v : Place F // v ∉ S}, x v ∈ O F v.val
  simp only [localIntegral_iff_norm, norm_mul, hi, one_mul]


private theorem piMeasure_smul_units {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Monoid (A i)] [∀ i, MeasurableSpace (A i)]
    (μ : ∀ i, Measure (A i)) [∀ i, SigmaFinite (μ i)] (u : (∀ i, A i)ˣ)
    (B : ∀ i, Set (A i)) (w : ι → ℝ≥0∞)
    (hw : ∀ i, μ i ((MulEquiv.piUnits u) i • B i) = w i * μ i (B i)) :
    (Measure.pi μ) (u • Set.pi univ B) =
      (∏ i, w i) * (Measure.pi μ) (Set.pi univ B) := by
  rw [unit_smul_pi, Measure.pi_pi, Measure.pi_pi]
  simp_rw [hw]
  exact Finset.prod_mul_distrib

private theorem ringEquiv_scaled_set {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B)
    (g : Bˣ) (X : Set A) : (g • (e '' X)) = e '' ((Units.map e.symm.toRingHom.toMonoidHom g) • X) := by
  simp only [← Set.image_smul, ← Set.image_comp]
  congr 1
  funext x
  change g.val * e x = e (e.symm g.val * x)
  rw [map_mul, RingEquiv.apply_symm_apply]

private theorem adele_factor_eq (S : Finset (Place F)) (g : Idele F)
    (hg : ∀ v ∉ S, ‖g.val.2 v‖ = 1) :
    let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
      Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
    let a := w.val.1
    (∏ v : RPlaces F, (‖a.1 v‖₊ : ℝ≥0∞)) *
      (∏ v : CPlaces F, (‖a.2 v‖₊ : ℝ≥0∞) ^ 2) *
      (∏ v : S, (‖g.val.2 v.val‖₊ : ℝ≥0∞)) = ENNReal.ofReal (ideleNorm F g) := by
  intro w a
  have ha : a = InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1 := rfl
  have hS : (fun v : Place F => ‖g.val.2 v‖).mulSupport ⊆ (S : Set (Place F)) :=
    fun v hv => not_not.mp fun h => hv (hg v h)
  change _ = ENNReal.ofReal (‖g.val.1‖ * ∏ᶠ v : Place F, ‖g.val.2 v‖)
  rw [finprod_eq_prod_of_mulSupport_subset _ hS, ← Finset.prod_coe_sort S,
    ← archModulus_of_infiniteAdele F, ← ha]
  rw [ENNReal.ofReal_mul (by unfold archModulus; positivity)]
  unfold archModulus
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
  simp only [ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _),
    ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

set_option maxHeartbeats 1600000 in
private theorem adele_haar_scale_test (g : Idele F)
    [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)] :
    ∃ (μ : Measure (Adeles F)) (D : Set (Adeles F)),
      μ.IsAddHaarMeasure ∧ μ D ≠ 0 ∧ μ D ≠ ∞ ∧
        μ (g • D) = ENNReal.ofReal (ideleNorm F g) * μ D := by
  let S := (finiteIdeleNorm_hasFiniteMulSupport F g).toFinset
  have hg (v : Place F) (hv : v ∉ S) : ‖g.val.2 v‖ = 1 :=
    not_not.mp fun h => hv ((finiteIdeleNorm_hasFiniteMulSupport F g).mem_toFinset.mpr h)
  letI : Countable (Place F) := finitePlaces_countable F
  letI (v : Place F) : SecondCountableTopology (L F v) := finitePlace_secondCountable F v
  letI (v : Place F) : LocallyCompactSpace (L F v) := finitePlace_locallyCompact F v
  letI : SecondCountableTopology (Tail F S) := tail_secondCountable F S
  letI : LocallyCompactSpace (Tail F S) := tail_locallyCompact F S
  let PlacesOutside := {v : Place F // v ∉ S}
  letI : Fact (∀ v : PlacesOutside, IsOpen (O F v.val : Set (L F v.val))) :=
    ⟨fun v => Valued.isOpen_valuationSubring (L F v.val)⟩
  letI : IsTopologicalRing (Tail F S) :=
    inferInstanceAs (IsTopologicalRing (Πʳ v : PlacesOutside, [L F v.val, O F v.val]))
  letI : T2Space (FinAdeles F) :=
    inferInstanceAs (T2Space (Πʳ v : Place F, [L F v, v.adicCompletionIntegers F]))
  letI : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  letI : T2Space (Adeles F) := inferInstanceAs (T2Space (InfiniteAdeleRing F × FinAdeles F))
  letI (v : Place F) : MeasurableSpace (L F v) := borel _
  letI (v : Place F) : BorelSpace (L F v) := ⟨rfl⟩
  letI : MeasurableSpace (Tail F S) := borel _
  letI : BorelSpace (Tail F S) := ⟨rfl⟩
  let μR : RPlaces F → Measure ℝ := fun _ => volume
  let μC : CPlaces F → Measure ℂ := fun _ => volume
  let μS (v : S) : Measure (L F v.val) := addHaar
  let μT : Measure (Tail F S) := addHaar
  letI : μT.IsAddHaarMeasure := inferInstanceAs (addHaar (G := Tail F S)).IsAddHaarMeasure
  letI (v : RPlaces F) : (μR v).IsAddHaarMeasure := inferInstanceAs (volume : Measure ℝ).IsAddHaarMeasure
  letI (v : CPlaces F) : (μC v).IsAddHaarMeasure := inferInstanceAs (volume : Measure ℂ).IsAddHaarMeasure
  letI (v : S) : (μS v).IsAddHaarMeasure := inferInstanceAs (addHaar (G := L F v.val)).IsAddHaarMeasure
  let ρ := ((Measure.pi μR).prod (Measure.pi μC)).prod ((Measure.pi μS).prod μT)
  letI : (Measure.pi μR).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  letI : (Measure.pi μC).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  letI : (Measure.pi μS).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  letI : ((Measure.pi μR).prod (Measure.pi μC)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  letI : ((Measure.pi μS).prod μT).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  haveI : ρ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let e := fullCoordinateSplit F S
  let μ : Measure (Adeles F) := ρ.map e.toHomeomorph
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map ρ
  let BR : RPlaces F → Set ℝ := fun _ => Metric.closedBall 0 1
  let BC : CPlaces F → Set ℂ := fun _ => Metric.closedBall 0 1
  let BS (v : S) : Set (L F v.val) := O F v.val
  let B := (Set.pi univ BR ×ˢ Set.pi univ BC) ×ˢ (Set.pi univ BS ×ˢ tailIntegralBlock F S)
  have hBc : IsCompact B :=
    ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)).prod
        ((isCompact_univ_pi fun v => finitePlaceIntegral_compact F v.val).prod (tailIntegralBlock_compact F S))
  have hB₀ : ρ B ≠ 0 := by
    dsimp only [ρ, B]
    rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Measure.pi_pi]
    have hR (v : RPlaces F) : μR v (BR v) ≠ 0 := by
      apply ne_of_gt
      apply lt_of_lt_of_le ((Metric.isOpen_ball (x := (0 : ℝ)) (ε := 1)).measure_pos (μR v) ?_)
        (measure_mono Metric.ball_subset_closedBall)
      exact ⟨0, Metric.mem_ball_self zero_lt_one⟩
    have hC (v : CPlaces F) : μC v (BC v) ≠ 0 := by
      apply ne_of_gt
      apply lt_of_lt_of_le ((Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1)).measure_pos (μC v) ?_)
        (measure_mono Metric.ball_subset_closedBall)
      exact ⟨0, Metric.mem_ball_self zero_lt_one⟩
    have hS (v : S) : μS v (BS v) ≠ 0 :=
      (Valued.isOpen_valuationSubring (L F v.val)).measure_ne_zero (μS v) ⟨0, zero_mem _⟩
    have hT₀ : μT (tailIntegralBlock F S) ≠ 0 :=
      (tailIntegralBlock_open F S).measure_ne_zero μT ⟨0, fun v => zero_mem (O F v.val)⟩
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hR v)
      (Finset.prod_ne_zero_iff.mpr fun v _ => hC v))
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hS v) hT₀)
  let D := e.toHomeomorph '' B
  have hD : μ D = ρ B := by
    change (ρ.map e.toHomeomorph) (e.toHomeomorph '' B) = _
    rw [Measure.map_apply e.continuous.measurable (hBc.image e.continuous).measurableSet,
      e.toHomeomorph.injective.preimage_image]
  refine ⟨μ, D, inferInstance, hD.symm ▸ hB₀, (hBc.image e.continuous).measure_lt_top.ne, ?_⟩
  let w : (Mixed F × (FinCoordinates F S × Tail F S))ˣ :=
    Units.map (fullCoordinateRingEquiv F S).symm.toRingHom g
  have he : g • D = e.toHomeomorph '' (w • B) := ringEquiv_scaled_set (fullCoordinateRingEquiv F S) g B
  have hWB : IsCompact (w • B) := hBc.image (continuous_const_smul w)
  rw [he, hD]
  change (ρ.map e.toHomeomorph) (e.toHomeomorph '' (w • B)) = _
  rw [Measure.map_apply e.continuous.measurable (hWB.image e.continuous).measurableSet,
    e.toHomeomorph.injective.preimage_image]
  let wR := (MulEquiv.prodUnits (MulEquiv.prodUnits w).1).1
  let wC := (MulEquiv.prodUnits (MulEquiv.prodUnits w).1).2
  let wS := (MulEquiv.prodUnits (MulEquiv.prodUnits w).2).1
  let r (v : RPlaces F) : ℝ≥0∞ := ‖(MulEquiv.piUnits wR v).val‖₊
  let c (v : CPlaces F) : ℝ≥0∞ := (‖(MulEquiv.piUnits wC v).val‖₊ : ℝ≥0∞) ^ 2
  let d (v : S) : ℝ≥0∞ := ‖g.val.2 v.val‖₊
  have hR (v : RPlaces F) : μR v (MulEquiv.piUnits wR v • BR v) = r v * μR v (BR v) := by
    simpa only [Module.finrank_self, pow_one] using archBall_measure_scaling (μR v) (MulEquiv.piUnits wR v)
  have hC (v : CPlaces F) : μC v (MulEquiv.piUnits wC v • BC v) = c v * μC v (BC v) := by
    simpa only [Complex.finrank_real_complex] using archBall_measure_scaling (μC v) (MulEquiv.piUnits wC v)
  have hS (v : S) : μS v (MulEquiv.piUnits wS v • BS v) = d v * μS v (BS v) := by
    rw [finitePlace_addHaar_smul F v.val (μS v), finiteCoordinateSplit_selected_unit F S g v]
  have ht := tailIntegralBlock_invariant F S g hg
  have hfactor : (∏ v, r v) * (∏ v, c v) * (∏ v, d v) = ENNReal.ofReal (ideleNorm F g) :=
    adele_factor_eq F S g hg
  simp only [B, ρ, unit_smul_prod, Measure.prod_prod]
  let wT := (MulEquiv.prodUnits (MulEquiv.prodUnits w).2).2
  change wT • tailIntegralBlock F S = tailIntegralBlock F S at ht
  change ((Measure.pi μR) (wR • Set.pi univ BR) * (Measure.pi μC) (wC • Set.pi univ BC)) *
      ((Measure.pi μS) (wS • Set.pi univ BS) * μT (wT • tailIntegralBlock F S)) = _
  rw [ht, piMeasure_smul_units μR wR BR r hR, piMeasure_smul_units μC wC BC c hC,
    piMeasure_smul_units μS wS BS d hS, ← hfactor]
  ac_rfl

/-- Lemma A.3.1.4. Multiplying an adelic set by an idele scales every
additive Haar measure by its actual normalized idelic norm. -/
theorem adelicHaar_smul (g : Idele F)
    [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]
    (μ : Measure (Adeles F)) [μ.IsAddHaarMeasure] (B : Set (Adeles F)) :
    μ (g • B) = ENNReal.ofReal (ideleNorm F g) * μ B := by
  letI : LocallyCompactSpace (FinAdeles F) := finiteAdeles_locallyCompact
  letI : LocallyCompactSpace (Adeles F) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FinAdeles F))
  letI : SecondCountableTopology (Adeles F) := adeles_secondCountable F
  obtain ⟨μ₀, D, hH, hD₀, hDtop, he⟩ := adele_haar_scale_test F g
  letI : μ₀.IsAddHaarMeasure := hH
  let r := (ideleNorm F g).toNNReal
  have hr : (r : ℝ≥0∞) = ENNReal.ofReal (ideleNorm F g) := rfl
  have hc := distribHaarChar_eq_of_measure_smul_eq_mul hD₀ hDtop (r := r) (hr.symm ▸ he)
  rw [← distribHaarChar_mul μ, hc, hr]

end

end Masullo
