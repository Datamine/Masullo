import SLocalFundamentalDomain
import Mathlib.Topology.MetricSpace.ProperSpace.Real

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

noncomputable section

namespace Masullo

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- Replace one infinite adele coordinate by the real scalar x. -/
def archimedeanCoordinateLine (v : InfinitePlace F) (x : ℝ) : InfiniteAdeleRing F :=
  fun w ↦ if h : w = v then h.symm ▸ infinitePlaceRealEmbedding F v x else 1

/-- The adele with precisely the indicated coordinate zero and all others one. -/
def adelicCoordinatePoint : InfinitePlace F ⊕ Place F → Adeles F
  | .inl v => (archimedeanCoordinateLine F v 0, 1)
  | .inr v => (1, ⟨fun w ↦ if w = v then 0 else 1,
      Eventually.of_forall fun w ↦ by
        change (if w = v then 0 else 1) ∈ w.adicCompletionIntegers F
        by_cases h : w = v <;> simp [h]⟩)

/-- The selected coordinate points in the S-adeles. -/
def sAdelicCoordinatePoint (S : Finset (Place F)) :
    InfinitePlace F ⊕ S → SAdeles F S
  | .inl v => (archimedeanCoordinateLine F v 0, 1)
  | .inr v => (1, Function.update 1 v 0)

private def unitAndCoordinateOrbits {R I : Type*} [Monoid R] (z : I → R) : Set R :=
  Set.range (Units.val : Rˣ → R) ∪ ⋃ i : I, Set.range (fun g : Rˣ ↦ g.val * z i)

private theorem coordinatePoint_mem_orbits {R I : Type*} [Monoid R]
    (z : I → R) (i : I) : z i ∈ unitAndCoordinateOrbits z :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨(1 : Rˣ), by simp⟩⟩)

/-- The global space D_F of Definition 8.2.0.1. -/
def adelicOrbitSpace : Set (Adeles F) := unitAndCoordinateOrbits (adelicCoordinatePoint F)

/-- The S-local space D_{F,S} of Definition 8.2.0.1. -/
def sAdelicOrbitSpace (S : Finset (Place F)) : Set (SAdeles F S) :=
  unitAndCoordinateOrbits (sAdelicCoordinatePoint F S)

def sOnePlaceExpSection (S : Finset (Place F)) (v : InfinitePlace F) :
    Multiplicative ℝ →* (SAdeles F S)ˣ :=
  (Units.map (sAdelesProjection F S)).comp (onePlaceExpSection F v)

theorem sOnePlaceExpSection_continuous (S : Finset (Place F)) (v : InfinitePlace F) :
    Continuous (sOnePlaceExpSection F S v) := by
  apply Units.continuous_iff.mpr
  exact ⟨(sAdelesProjection_continuous F S).comp
      (Units.continuous_val.comp (onePlaceExpSection_continuous F v)),
    (sAdelesProjection_continuous F S).comp
      (Units.continuous_coe_inv.comp (onePlaceExpSection_continuous F v))⟩

theorem sLocalIdeleNorm_sOnePlaceExpSection (S : Finset (Place F)) (v : InfinitePlace F)
    (t : Multiplicative ℝ) :
    sLocalIdeleNorm F S (sOnePlaceExpSection F S v t) = Real.exp t.toAdd := by
  let a := onePlaceExpSection F v t
  have ha : a ∈ sIdeleBlock F S := by
    apply (sIdeleBlock_mem_iff F S a).mpr
    intro w _
    apply (ideleOrder_eq_zero_iff F a w).mpr
    have he : a.val.2 = 1 := (archimedeanExpSection_components F _ t).2
    rw [he]
    exact map_one _
  exact (sBlock_norm_eq F S ⟨a, ha⟩).trans (ideleNorm_onePlaceExpSection F v t)

private theorem onePlaceExpSection_realLine (v : InfinitePlace F) (t : Multiplicative ℝ) :
    (onePlaceExpSection F v t).val =
      (archimedeanCoordinateLine F v (Real.exp (t.toAdd * (v.mult : ℝ)⁻¹)), 1) := by
  classical
  refine Prod.ext ?_ (archimedeanExpSection_components F _ t).2
  funext w
  rw [onePlaceExpSection, (archimedeanExpSection_components F _ _).1]
  by_cases hw : w = v
  · subst w
    simp [archimedeanCoordinateLine]
  · simp [archimedeanCoordinateLine, hw]

omit [NumberField F] in
private theorem exp_coordinate_range (v : InfinitePlace F) :
    Set.range (fun t : Multiplicative ℝ ↦ Real.exp (t.toAdd * (v.mult : ℝ)⁻¹)) = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact Real.exp_pos _
  · intro hx
    have hv : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
    refine ⟨Multiplicative.ofAdd (Real.log x * (v.mult : ℝ)), ?_⟩
    change Real.exp (Real.log x * (v.mult : ℝ) * (v.mult : ℝ)⁻¹) = x
    rw [mul_assoc, mul_inv_cancel₀ hv, mul_one, Real.exp_log hx]

private theorem coordinateLine_image_closed {B : Type*} [TopologicalSpace B] [T2Space B]
    (b : B) (v : InfinitePlace F) (C : Set ℝ) (hC : IsClosed C) :
    IsClosed ((fun x ↦ (archimedeanCoordinateLine F v x, b)) '' C) := by
  classical
  let W := (infinitePlaceRealEmbedding F v) '' C
  have hW : IsClosed W := (infinitePlaceRealEmbedding_isometry F v).isClosedEmbedding.isClosedMap _ hC
  have hEq :
      (fun x ↦ (archimedeanCoordinateLine F v x, b)) '' C =
        ((fun p : InfiniteAdeleRing F × B ↦ p.1 v) ⁻¹' W) ∩
          ((⋂ w : {w : InfinitePlace F // w ≠ v},
            (fun p : InfiniteAdeleRing F × B ↦ p.1 w.val) ⁻¹' {(1 : w.val.Completion)}) ∩
           Prod.snd ⁻¹' {b}) := by
    ext p
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff, W, mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx, by simp [archimedeanCoordinateLine]⟩,
        fun w ↦ by simp [archimedeanCoordinateLine, w.property], rfl⟩
    · rintro ⟨⟨x, hx, hxv⟩, hw, hb⟩
      refine ⟨x, hx, Prod.ext ?_ hb.symm⟩
      funext w
      by_cases h : w = v
      · subst w
        simpa [archimedeanCoordinateLine] using hxv
      · simpa [archimedeanCoordinateLine, h] using (hw ⟨w, h⟩).symm
  rw [hEq]
  exact (hW.preimage ((continuous_apply v).comp continuous_fst)).inter
    ((isClosed_iInter fun (w : {w : InfinitePlace F // w ≠ v}) ↦ isClosed_singleton.preimage
      ((continuous_apply w.val).comp continuous_fst)).inter (isClosed_singleton.preimage continuous_snd))

private theorem coordinateLine_positive_closure {B : Type*} [TopologicalSpace B] [T2Space B]
    (b : B) (v : InfinitePlace F) :
    closure ((fun x ↦ (archimedeanCoordinateLine F v x, b)) '' Ioi 0) =
      ((fun x ↦ (archimedeanCoordinateLine F v x, b)) '' Ioi 0) ∪
        {(archimedeanCoordinateLine F v 0, b)} := by
  classical
  let j := fun x ↦ (archimedeanCoordinateLine F v x, b)
  have hj : Continuous j := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro w
    by_cases h : w = v
    · subst w
      simpa [archimedeanCoordinateLine] using (infinitePlaceRealEmbedding_isometry F v).continuous
    · simp [archimedeanCoordinateLine, h, continuous_const]
  have he : closure (j '' Ioi 0) = j '' Ici 0 := by
    apply le_antisymm
    · exact closure_minimal (image_mono Ioi_subset_Ici_self) (coordinateLine_image_closed F b v _ isClosed_Ici)
    · rw [← closure_Ioi]
      exact image_closure_subset_closure_image hj
  rw [show Ici (0 : ℝ) = Ioi 0 ∪ {0} by ext x; simp [le_iff_lt_or_eq, eq_comm, or_comm],
    image_union, image_singleton] at he
  exact he

private theorem relative_closure_of_ambient {R : Type*} [TopologicalSpace R]
    {A D : Set R} {z : R} (hA : A ⊆ D) (hz : z ∈ D)
    (h : closure A = A ∪ {z}) :
    closure (Subtype.val ⁻¹' A : Set D) =
      (Subtype.val ⁻¹' A : Set D) ∪ {⟨z, hz⟩} := by
  ext x
  rw [closure_subtype, image_preimage_eq_inter_range, Subtype.range_val,
    inter_eq_left.mpr hA, h]
  simp [Subtype.ext_iff]

/-- Lemma 8.2.0.6(2), including the stronger closure calculation in the ambient adeles. -/
theorem adelic_onePlaceExpSection_closure (v : InfinitePlace F) :
    let A := Set.range (fun t ↦ (onePlaceExpSection F v t).val)
    let z := adelicCoordinatePoint F (.inl v)
    (closure A = A ∪ {z}) ∧
      ∃ hz : z ∈ adelicOrbitSpace F,
        closure (Subtype.val ⁻¹' A : Set (adelicOrbitSpace F)) =
          (Subtype.val ⁻¹' A : Set (adelicOrbitSpace F)) ∪ {⟨z, hz⟩} := by
  dsimp only
  have hr : Set.range (fun t ↦ (onePlaceExpSection F v t).val) =
      (fun x ↦ (archimedeanCoordinateLine F v x, (1 : FiniteAdeleRing (𝓞 F) F))) '' Ioi 0 := by
    rw [← exp_coordinate_range F v, ← range_comp]
    exact congrArg Set.range (funext (onePlaceExpSection_realLine F v))
  letI : T2Space (FiniteAdeleRing (𝓞 F) F) := T2Space.of_injective_continuous
    (f := fun a : FiniteAdeleRing (𝓞 F) F => (a : (w : Place F) → w.adicCompletion F))
    DFunLike.coe_injective RestrictedProduct.continuous_coe
  have hc := coordinateLine_positive_closure F (1 : FiniteAdeleRing (𝓞 F) F) v
  rw [← hr] at hc
  refine ⟨hc, ?_⟩
  have hz : adelicCoordinatePoint F (.inl v) ∈ adelicOrbitSpace F :=
    coordinatePoint_mem_orbits _ (Sum.inl v)
  refine ⟨hz, relative_closure_of_ambient ?_ hz hc⟩
  rintro _ ⟨t, rfl⟩
  exact Or.inl (Set.mem_range_self _)

/-- Lemma 8.2.0.6(1), including the stronger closure calculation in the ambient S-adeles. -/
theorem sAdelic_onePlaceExpSection_closure (S : Finset (Place F)) (v : InfinitePlace F) :
    let A := Set.range (fun t ↦ (sOnePlaceExpSection F S v t).val)
    let z := sAdelicCoordinatePoint F S (.inl v)
    (closure A = A ∪ {z}) ∧
      ∃ hz : z ∈ sAdelicOrbitSpace F S,
        closure (Subtype.val ⁻¹' A : Set (sAdelicOrbitSpace F S)) =
          (Subtype.val ⁻¹' A : Set (sAdelicOrbitSpace F S)) ∪ {⟨z, hz⟩} := by
  dsimp only
  have hr : Set.range (fun t ↦ (sOnePlaceExpSection F S v t).val) =
      (fun x ↦ (archimedeanCoordinateLine F v x, (1 : (w : S) → w.val.adicCompletion F))) '' Ioi 0 := by
    rw [← exp_coordinate_range F v, ← range_comp]
    apply congrArg Set.range
    funext t
    change sAdelesProjection F S (onePlaceExpSection F v t).val = _
    rw [onePlaceExpSection_realLine]
    rfl
  have hc := coordinateLine_positive_closure F (1 : (w : S) → w.val.adicCompletion F) v
  rw [← hr] at hc
  refine ⟨hc, ?_⟩
  have hz : sAdelicCoordinatePoint F S (.inl v) ∈ sAdelicOrbitSpace F S :=
    coordinatePoint_mem_orbits _ (Sum.inl v)
  refine ⟨hz, relative_closure_of_ambient ?_ hz hc⟩
  rintro _ ⟨t, rfl⟩
  exact Or.inl (Set.mem_range_self _)

private theorem inverse_transporters_distinct_norms {R : Type*} [Monoid R]
    (N : Rˣ →* ℝ) (s : Multiplicative ℝ →* Rˣ)
    (hs : ∀ t, N (s t) = Real.exp t.toAdd) (z : R) {q : ℝ} (hq : 1 < q) :
    let A := (fun t ↦ (s t).val * z) '' {t | Real.exp t.toAdd ∈ Ico 1 q}
    ∃ a b : Rˣ, N a ≠ N b ∧ a⁻¹.val * z ∈ A ∧ b⁻¹.val * z ∈ A := by
  let r : ℝ := (1 + q) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrq : r < q := by dsimp [r]; linarith
  let t := Multiplicative.ofAdd (Real.log r)
  have ht : Real.exp t.toAdd = r := Real.exp_log (zero_lt_one.trans hr)
  refine ⟨1, (s t)⁻¹, ?_, ?_, ?_⟩
  · rw [map_one, map_inv, hs, ht]
    exact (inv_lt_one_of_one_lt₀ hr).ne'
  · exact ⟨1, ⟨by simp, by simpa using hq⟩, by simp⟩
  · refine ⟨t, ?_, by simp⟩
    change Real.exp t.toAdd ∈ Ico 1 q
    rw [ht]
    exact ⟨hr.le, hrq⟩

/-- For the global claim in Proposition 8.2.0.4, two transporters of the finite
coordinate point into the indicated interval can have different moduli. -/
theorem adelic_finite_strip_transporters_distinct_norms (w : InfinitePlace F) (v : Place F) :
    let z := adelicCoordinatePoint F (.inr v)
    let A := (fun t ↦ (onePlaceExpSection F w t).val * z) ''
      {t | Real.exp t.toAdd ∈ Ico 1 (v.asIdeal.absNorm : ℝ)}
    ∃ a b : Idele F, ideleNorm F a ≠ ideleNorm F b ∧
      a⁻¹.val * z ∈ A ∧ b⁻¹.val * z ∈ A :=
  inverse_transporters_distinct_norms (ideleNorm F) (onePlaceExpSection F w)
    (ideleNorm_onePlaceExpSection F w) _ (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)

/-- The same nonuniqueness holds for the S-local claim in Proposition 8.2.0.4. -/
theorem sAdelic_finite_strip_transporters_distinct_norms (S : Finset (Place F))
    (w : InfinitePlace F) (v : S) :
    let z := sAdelicCoordinatePoint F S (.inr v)
    let A := (fun t ↦ (sOnePlaceExpSection F S w t).val * z) ''
      {t | Real.exp t.toAdd ∈ Ico 1 (v.val.asIdeal.absNorm : ℝ)}
    ∃ a b : (SAdeles F S)ˣ, sLocalIdeleNorm F S a ≠ sLocalIdeleNorm F S b ∧
      a⁻¹.val * z ∈ A ∧ b⁻¹.val * z ∈ A :=
  inverse_transporters_distinct_norms (sLocalIdeleNorm F S) (sOnePlaceExpSection F S w)
    (sLocalIdeleNorm_sOnePlaceExpSection F S w) _
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)

end Masullo
