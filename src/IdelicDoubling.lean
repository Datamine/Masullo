import ArchimedeanFundamentalDomain
import OpenBoxDoubling
import IdelicDoublingObstruction
import Mathlib.Topology.Bases
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Filter Function MeasureTheory NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem Set Topology
open scoped Classical ENNReal NNReal NumberField Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}
private abbrev RegulatorIndex := Fin (NumberField.Units.rank F)
private abbrev Signs := RealPlaces F → Metric.sphere (0 : ℝ) 1

/-- The real logarithmic and complex angular coordinates of the small boxes. -/
abbrev ArchBoxIndex := RegulatorIndex F ⊕ ComplexPlaces F

private def archBoxParameters (t : Multiplicative (ArchBoxIndex F → ℝ)) :
    Multiplicative (logSpace F) × (Signs F × (ComplexPlaces F → Circle)) :=
  (Multiplicative.ofAdd ((regulatorBasis F).equivFunL.symm (fun i => t.toAdd (Sum.inl i))),
    1, fun v => Circle.exp (t.toAdd (Sum.inr v)))

/-- Parameterization of the identity component, in regulator coordinates
and real lifts of the angular coordinates at all complex places. -/
def archBoxHom : Multiplicative (ArchBoxIndex F → ℝ) →* archNormOne F where
  toFun t := archNormOnePolar F (archBoxParameters F t)
  map_one' := by
    have h : archBoxParameters F 1 = 1 := by
      apply Prod.ext
      · change Multiplicative.ofAdd ((regulatorBasis F).equivFunL.symm 0) = 1
        rw [map_zero]
        rfl
      · change ((1 : Signs F), fun _ : ComplexPlaces F => Circle.exp 0) = (1, 1)
        apply Prod.ext
        · rfl
        · funext v
          exact Circle.exp_zero
    rw [h, map_one]
  map_mul' s t := by
    rw [← map_mul]
    congr 1
    apply Prod.ext
    · change Multiplicative.ofAdd ((regulatorBasis F).equivFunL.symm
          ((fun i => s.toAdd (Sum.inl i)) + (fun i => t.toAdd (Sum.inl i)))) = _
      rw [map_add]
      rfl
    · apply Prod.ext
      · exact (one_mul (1 : Signs F)).symm
      · funext v
        exact Circle.exp_add _ _

theorem archBoxHom_continuous : Continuous (archBoxHom F) := by
  apply (archNormOnePolar F).continuous.comp
  have hl : Continuous (fun t : Multiplicative (ArchBoxIndex F → ℝ) => (archBoxParameters F t).1) :=
    continuous_ofAdd.comp ((regulatorBasis F).equivFunL.symm.continuous.comp
      (continuous_pi fun i => (continuous_apply (Sum.inl i)).comp continuous_toAdd))
  exact hl.prodMk (continuous_const.prodMk
    (continuous_pi fun v => Circle.exp.continuous.comp ((continuous_apply (Sum.inr v)).comp continuous_toAdd)))

private theorem signs_one_open : IsOpen ({1} : Set (Signs F)) := by
  have h : ({1} : Set (Signs F)) = Set.univ.pi (fun _ => ({1} : Set (Metric.sphere (0 : ℝ) 1))) := by
    ext x
    simp only [mem_singleton_iff, Set.mem_pi, mem_univ, forall_const]
    exact ⟨congrFun, funext⟩
  rw [h]
  refine isOpen_set_pi finite_univ fun v _ => ?_
  have he : ({1} : Set (Metric.sphere (0 : ℝ) 1)) =
      {x : Metric.sphere (0 : ℝ) 1 | 0 < (x : ℝ)} := by
    apply Set.ext
    intro x
    rw [mem_singleton_iff]
    change x = 1 ↔ 0 < (x : ℝ)
    rcases realSigns_eq_one_or_neg_one x with h | h
    · have eq : x = 1 := Subtype.ext h
      rw [eq]
      exact iff_of_true rfl (by exact one_pos)
    · refine iff_of_false (fun k => ?_) (by rw [h]; norm_num)
      have h' : (x : ℝ) = 1 := congrArg Subtype.val k
      linarith
  rw [he]
  exact isOpen_lt continuous_const continuous_subtype_val

private theorem circle_exp_pi_open {J : Type*} :
    IsOpenMap (fun x : J → ℝ => fun j => Circle.exp (x j)) := by
  apply (isTopologicalBasis_pi fun _ => TopologicalSpace.isTopologicalBasis_opens).isOpenMap_iff.mpr
  rintro _ ⟨U, s, hU, rfl⟩
  rw [show (fun x : J → ℝ => fun j => Circle.exp (x j)) =
      Pi.map (fun _ : J => Circle.exp) from rfl, piMap_image_pi (fun _ _ => Circle.exp_surjective)]
  exact isOpen_set_pi s.finite_toSet fun j hj => isLocalHomeomorph_circleExp.isOpenMap _ (hU j hj)

theorem archBoxHom_open : IsOpenMap (archBoxHom F) := by
  let E := Homeomorph.sumPiEquivProdPi (RegulatorIndex F) (ComplexPlaces F) (fun _ => ℝ)
  let l : (RegulatorIndex F → ℝ) → Multiplicative (logSpace F) :=
    Multiplicative.ofAdd ∘ (regulatorBasis F).equivFunL.symm
  have hl : IsOpenMap l := isOpenMap_ofAdd.comp (regulatorBasis F).equivFunL.symm.toHomeomorph.isOpenMap
  let k : (ComplexPlaces F → Circle) → Signs F × (ComplexPlaces F → Circle) := fun p => (1, p)
  have hk : IsOpenMap k := by
    intro S hS
    have he : k '' S = ({1} : Set (Signs F)) ×ˢ S := by
      ext ⟨x, p⟩
      constructor
      · rintro ⟨z, hz, eq⟩
        rw [← eq]
        exact ⟨mem_singleton 1, hz⟩
      · rintro ⟨hx, hp⟩
        exact ⟨p, hp, Prod.ext (mem_singleton_iff.mp hx).symm rfl⟩
    rw [he]
    exact (signs_one_open F).prod hS
  have h := (archNormOnePolar F).toHomeomorph.isOpenMap.comp
    ((hl.prodMap (hk.comp (circle_exp_pi_open (J := ComplexPlaces F)))).comp
      (E.isOpenMap.comp isOpenMap_toAdd))
  convert h using 1
  rfl

/-- Symmetric open boxes in the actual Archimedean norm-one group.
Their radii control both every regulator coordinate and every angle. -/
def archDoublingBox (c : ℝ) (k : ℕ) : Set (archNormOne F) :=
  groupBox (archBoxHom F) (c / ((k : ℝ) + 1))

theorem archDoublingBox_properties [MeasurableSpace (archNormOne F)] [BorelSpace (archNormOne F)]
    (μ : Measure (archNormOne F)) [μ.IsHaarMeasure] {c : ℝ} (hc : 0 < c) :
    DoublingSequence μ (archDoublingBox F c) ∧ CofinalAtOne (archDoublingBox F c) ∧
      (∀ k, IsOpen (archDoublingBox F c k) ∧ (archDoublingBox F c k)⁻¹ = archDoublingBox F c k) ∧
      ∃ C : ℝ≥0, ∀ k, MeasurableSet (archDoublingBox F (c / 4) k) ∧
        archDoublingBox F (c / 4) (k + 1) * archDoublingBox F (c / 4) k ⊆ archDoublingBox F c (k + 1) ∧
        μ (archDoublingBox F c k) ≤ C * μ (archDoublingBox F (c / 4) k) := by
  have eq (k : ℕ) : c / 4 / ((k : ℝ) + 1) = c / ((k : ℝ) + 1) / 4 := by ring
  have eq' : archDoublingBox F (c / 4) = fun k => groupBox (archBoxHom F) (boxRadius c k / 4) :=
    funext fun k => congrArg (groupBox (archBoxHom F)) (eq k)
  rw [eq']
  exact groupBox_doubling μ (archBoxHom F) (archBoxHom_continuous F) (archBoxHom_open F) hc


def normOnePhase (v : InfinitePlace F) : archNormOne F →* Circle :=
  (infiniteIdelePhase F v).comp (archNormOne F).subtype

private theorem normOnePhase_continuous (v : InfinitePlace F) : Continuous (normOnePhase F v) :=
  (infiniteIdelePhase_continuous F v).comp continuous_subtype_val

private theorem normOnePhase_open {v : InfinitePlace F} (hv : v.IsComplex) :
    IsOpenMap (normOnePhase F v) := by
  let e := archNormOnePolar F
  letI : SigmaCompactSpace (archNormOne F) := isSigmaCompact_univ_iff.mp
    (e.surjective.range_eq ▸ isSigmaCompact_range e.continuous)
  apply (normOnePhase F v).isOpenMap_of_sigmaCompact _ (normOnePhase_continuous F v)
  intro z
  obtain ⟨a, ha, _⟩ := complex_place_with_phase F hv 1 z
  exact ⟨a, ha⟩

private theorem centeredPhaseHalfOpen_arg {r : ℝ} (hr : r < Real.pi) (z : Circle) :
    z ∈ centeredPhaseHalfOpen r ↔ Complex.arg (z : ℂ) ∈ Ico (-r) r := by
  refine ⟨?_, fun h => ⟨_, h, Circle.exp_arg z⟩⟩
  rintro ⟨a, ha, rfl⟩
  rw [Circle.arg_exp (by linarith [ha.1]) (ha.2.le.trans hr.le)]
  exact ha

private theorem interior_centeredPhaseHalfOpen {r : ℝ} (hr : r < Real.pi) :
    interior (centeredPhaseHalfOpen r) = Circle.centeredArc r := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := interior_subset hz
    let W := Circle.exp ⁻¹' interior (centeredPhaseHalfOpen r) ∩ Ioo (-Real.pi) Real.pi
    have hW : IsOpen W := (isOpen_interior.preimage Circle.exp.continuous).inter isOpen_Ioo
    have hs : W ⊆ Ico (-r) r := by
      rintro y ⟨hy, hyπ⟩
      have h := (centeredPhaseHalfOpen_arg hr (Circle.exp y)).mp (interior_subset hy)
      rw [Circle.arg_exp hyπ.1 hyπ.2.le] at h
      exact h
    have hmem : x ∈ W := by
      refine ⟨hz, ?_, ?_⟩
      · linarith [hx.1]
      · linarith [hx.2]
    have hxy := interior_maximal hs hW hmem
    rw [interior_Ico] at hxy
    exact ⟨x, abs_lt.mpr hxy, rfl⟩
  · apply interior_maximal _ (Circle.isOpen_centeredArc r)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, Ioo_subset_Ico_self (abs_lt.mp ha), rfl⟩

private theorem phase_preimage_interior (v : InfinitePlace F) {r : ℝ}
    (hpos : 0 < r) (hr : r < Real.pi) :
    interior (normOnePhase F v ⁻¹' centeredPhaseHalfOpen r) =
      normOnePhase F v ⁻¹' Circle.centeredArc r := by
  by_cases hv : v.IsReal
  · have h : normOnePhase F v ⁻¹' centeredPhaseHalfOpen r =
        normOnePhase F v ⁻¹' Circle.centeredArc r := by
      ext a
      change normOnePhase F v a ∈ centeredPhaseHalfOpen r ↔ normOnePhase F v a ∈ Circle.centeredArc r
      rw [centeredPhaseHalfOpen_arg hr, Circle.mem_centeredArc hr.le]
      rcases archPhase_of_real_eq_one_or_neg_one F hv a.val with h | h
      · change normOnePhase F v a = 1 at h
        rw [h]
        change Complex.arg (1 : ℂ) ∈ Ico (-r) r ↔ |Complex.arg (1 : ℂ)| < r
        rw [Complex.arg_one, abs_zero]
        exact iff_of_true ⟨by linarith, hpos⟩ hpos
      · change normOnePhase F v a = -1 at h
        rw [h]
        change Complex.arg (-1 : ℂ) ∈ Ico (-r) r ↔ |Complex.arg (-1 : ℂ)| < r
        rw [Complex.arg_neg_one, abs_of_pos Real.pi_pos]
        exact iff_of_false (fun h => hr.not_ge h.2.le) hr.not_gt
    rw [h, ((Circle.isOpen_centeredArc r).preimage (normOnePhase_continuous F v)).interior_eq]
  · have ho := normOnePhase_open F (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    rw [← ho.preimage_interior_eq_interior_preimage (normOnePhase_continuous F v),
      interior_centeredPhaseHalfOpen hr]

def archRegulatorCoordinate (i : RegulatorIndex F) (a : archNormOne F) : ℝ :=
  (regulatorBasis F).equivFunL (archRegulatorLog F a).toAdd i

private theorem archRegulatorCoordinate_continuous (i : RegulatorIndex F) :
    Continuous (archRegulatorCoordinate F i) :=
  (continuous_apply i).comp ((regulatorBasis F).equivFunL.continuous.comp
    (continuous_toAdd.comp (archRegulatorLog_continuous F)))

private theorem archRegulatorCoordinate_open (i : RegulatorIndex F) :
    IsOpenMap (archRegulatorCoordinate F i) :=
  (isOpenMap_eval i).comp ((regulatorBasis F).equivFunL.toHomeomorph.isOpenMap.comp
    (isOpenMap_toAdd.comp (archRegulatorLog_open F)))

private theorem archRegulatorCoordinate_inv (i : RegulatorIndex F) (a : archNormOne F) :
    archRegulatorCoordinate F i a⁻¹ = -archRegulatorCoordinate F i a := by
  unfold archRegulatorCoordinate
  rw [map_inv]
  change (regulatorBasis F).equivFunL (-(archRegulatorLog F a).toAdd) i =
    -((regulatorBasis F).equivFunL (archRegulatorLog F a).toAdd i)
  rw [map_neg]
  rfl

def archBalancedLogCell : Set (archNormOne F) :=
  ⋂ i : RegulatorIndex F, archRegulatorCoordinate F i ⁻¹' Ico (-(1 / 2 : ℝ)) (1 / 2)

def archBalancedAngleRadius : ℝ :=
  Real.pi / (torsionOrder F : ℝ)

private theorem archBalancedAngleRadius_pos : 0 < archBalancedAngleRadius F :=
  div_pos Real.pi_pos (Nat.cast_pos.mpr (torsionOrder_pos F))

private theorem archBalancedAngleRadius_lt_pi : archBalancedAngleRadius F < Real.pi := by
  obtain ⟨k, hk⟩ := even_torsionOrder F
  have hp := torsionOrder_pos F
  have ht : 1 < torsionOrder F := by omega
  exact div_lt_self Real.pi_pos (by exact_mod_cast ht)

/-- The balanced half-open Archimedean region E1, with its signed angle
written in the interval centered at zero. -/
def archBalancedCell (v : InfinitePlace F) : Set (archNormOne F) :=
  archBalancedLogCell F ∩ normOnePhase F v ⁻¹' centeredPhaseHalfOpen (archBalancedAngleRadius F)

theorem archBalancedCell_interior (v : InfinitePlace F) :
    interior (archBalancedCell F v) =
      (⋂ i : RegulatorIndex F, archRegulatorCoordinate F i ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∩
        normOnePhase F v ⁻¹' Circle.centeredArc (archBalancedAngleRadius F) := by
  rw [archBalancedCell, interior_inter, archBalancedLogCell, interior_iInter_of_finite,
    phase_preimage_interior F v (archBalancedAngleRadius_pos F) (archBalancedAngleRadius_lt_pi F)]
  congr 1
  apply iInter_congr
  intro i
  rw [← (archRegulatorCoordinate_open F i).preimage_interior_eq_interior_preimage
    (archRegulatorCoordinate_continuous F i), interior_Ico]

/-- A.5.2.13(1), with the identity included in the symmetric angular arc. -/
theorem archBalancedCell_interior_nhds (v : InfinitePlace F) :
    interior (archBalancedCell F v) ∈ 𝓝 (1 : archNormOne F) ∧
      (interior (archBalancedCell F v))⁻¹ = interior (archBalancedCell F v) := by
  constructor
  · apply isOpen_interior.mem_nhds
    rw [archBalancedCell_interior]
    refine ⟨mem_iInter.mpr (fun i => ?_), ?_⟩
    · change archRegulatorCoordinate F i 1 ∈ Ioo _ _
      have h : archRegulatorCoordinate F i 1 = 0 := by
        unfold archRegulatorCoordinate
        rw [map_one]
        change (regulatorBasis F).equivFunL 0 i = 0
        rw [map_zero]
        rfl
      rw [h]
      norm_num
    · change normOnePhase F v 1 ∈ Circle.centeredArc _
      rw [map_one]
      exact ⟨0, by simpa using archBalancedAngleRadius_pos F, Circle.exp_zero⟩
  · have h {a : archNormOne F} (ha : a ∈ interior (archBalancedCell F v)) :
        a⁻¹ ∈ interior (archBalancedCell F v) := by
      rw [archBalancedCell_interior] at ha ⊢
      refine ⟨mem_iInter.mpr (fun i => ?_), ?_⟩
      · have hi : archRegulatorCoordinate F i a ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := mem_iInter.mp ha.1 i
        change archRegulatorCoordinate F i a⁻¹ ∈ Ioo _ _
        rw [archRegulatorCoordinate_inv]
        exact ⟨by linarith [hi.2], by linarith [hi.1]⟩
      · change normOnePhase F v a⁻¹ ∈ Circle.centeredArc _
        rw [map_inv]
        obtain ⟨t, ht, e⟩ := ha.2
        refine ⟨-t, ?_, ?_⟩
        · change |-t| < archBalancedAngleRadius F
          rw [abs_neg]
          exact ht
        · rw [Circle.exp_neg, e]
    ext a
    exact ⟨fun ha => inv_inv a ▸ h ha, h⟩

end

end Masullo
