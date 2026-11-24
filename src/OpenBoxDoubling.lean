import DoublingSequences
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Pi

open Filter Function MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

universe u v

noncomputable section

variable {I : Type u} [Fintype I]
variable {G : Type v} [Group G]

/-- A box in additive coordinates, mapped into a multiplicative group. -/
def groupBox (p : Multiplicative (I → ℝ) →* G) (r : ℝ) : Set G :=
  (fun x : I → ℝ => p (Multiplicative.ofAdd x)) '' Metric.ball 0 r

theorem groupBox_mono (p : Multiplicative (I → ℝ) →* G) {r s : ℝ} (h : r ≤ s) :
    groupBox p r ⊆ groupBox p s :=
  image_mono (ball_subset_ball h)

theorem groupBox_one (p : Multiplicative (I → ℝ) →* G) {r : ℝ} (hr : 0 < r) :
    1 ∈ groupBox p r :=
  ⟨0, mem_ball_self hr, p.map_one⟩

theorem groupBox_isOpen [TopologicalSpace G] (p : Multiplicative (I → ℝ) →* G)
    (ho : IsOpenMap p) (r : ℝ) : IsOpen (groupBox p r) :=
  (ho.comp isOpenMap_ofAdd) _ isOpen_ball

theorem groupBox_inv (p : Multiplicative (I → ℝ) →* G) (r : ℝ) :
    (groupBox p r)⁻¹ = groupBox p r := by
  have h {x : G} : x ∈ groupBox p r → x⁻¹ ∈ groupBox p r := by
    rintro ⟨v, hv, rfl⟩
    refine ⟨-v, ?_, p.map_inv (Multiplicative.ofAdd v)⟩
    simpa only [mem_ball, dist_zero_right, norm_neg] using hv
  ext x
  exact ⟨fun hx => inv_inv x ▸ h hx, h⟩

theorem groupBox_mul_subset (p : Multiplicative (I → ℝ) →* G) (r s : ℝ) :
    groupBox p r * groupBox p s ⊆ groupBox p (r + s) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨x + y, ?_, p.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)⟩
  simp only [mem_ball, dist_zero_right] at hx hy ⊢
  exact (norm_add_le x y).trans_lt (add_lt_add hx hy)

abbrev BoxShift (I : Type u) := I → Set.Icc (-4 : ℤ) 4

noncomputable instance : Fintype (BoxShift I) := by
  classical
  exact inferInstanceAs (Fintype (I → Set.Icc (-4 : ℤ) 4))

def boxCenter (r : ℝ) (z : BoxShift I) : I → ℝ := fun i => (z i).val * r

theorem groupBox_grid_subset (p : Multiplicative (I → ℝ) →* G) {r : ℝ} (hr : 0 < r) :
    groupBox p (4 * r) ⊆ ⋃ z : BoxShift I, p (Multiplicative.ofAdd (boxCenter r z)) • groupBox p r := by
  rintro _ ⟨x, hx, rfl⟩
  let k (i : I) : ℤ := ⌊x i / r⌋
  have pointwise (i : I) : |x i| < 4 * r :=
    (pi_norm_lt_iff (by positivity : 0 < 4 * r)).mp (by simpa using hx) i
  have hk (i : I) : k i ∈ Set.Icc (-4 : ℤ) 4 := by
    obtain ⟨h₁, h₂⟩ := abs_lt.mp (pointwise i)
    constructor
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hr).mpr
      norm_num
      linarith
    · apply Int.floor_le_iff.mpr
      apply (div_lt_iff₀ hr).mpr
      norm_num
      linarith
  let z : BoxShift I := fun i => ⟨k i, hk i⟩
  let y : I → ℝ := x - boxCenter r z
  have hy : y ∈ Metric.ball 0 r := by
    simp only [mem_ball, dist_zero_right]
    apply (pi_norm_lt_iff hr).mpr
    intro i
    have h₁ : (k i : ℝ) * r ≤ x i := (le_div_iff₀ hr).mp (Int.floor_le _)
    have h₂ : x i < ((k i : ℝ) + 1) * r := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one _)
    change |x i - (k i : ℝ) * r| < r
    apply abs_lt.mpr
    constructor <;> linarith
  apply mem_iUnion.mpr
  refine ⟨z, ⟨p (Multiplicative.ofAdd y), ⟨y, hy, rfl⟩, ?_⟩⟩
  change p (Multiplicative.ofAdd (boxCenter r z)) * p (Multiplicative.ofAdd y) = _
  rw [← p.map_mul]
  congr 1
  change boxCenter r z + (x - boxCenter r z) = x
  abel

theorem groupBox_measure_compare [MeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (p : Multiplicative (I → ℝ) →* G) {r : ℝ} (hr : 0 < r) :
    μ (groupBox p (4 * r)) ≤ (Fintype.card (BoxShift I) : ℝ≥0) * μ (groupBox p r) := by
  calc
    _ ≤ μ (⋃ z : BoxShift I, p (Multiplicative.ofAdd (boxCenter r z)) • groupBox p r) :=
      measure_mono (groupBox_grid_subset p hr)
    _ ≤ ∑ z : BoxShift I, μ (p (Multiplicative.ofAdd (boxCenter r z)) • groupBox p r) :=
      measure_iUnion_fintype_le _ _
    _ = _ := by simp [measure_smul, nsmul_eq_mul]

def boxRadius (c : ℝ) (k : ℕ) : ℝ := c / ((k : ℝ) + 1)

theorem boxRadius_pos {c : ℝ} (hc : 0 < c) (k : ℕ) : 0 < boxRadius c k :=
  div_pos hc (by positivity)

private theorem boxRadius_decreasing {c : ℝ} (hc : 0 < c) : Antitone (boxRadius c) := by
  intro m n h
  apply div_le_div_of_nonneg_left hc.le (by positivity)
  exact add_le_add_left (by exact_mod_cast h : (m : ℝ) ≤ (n : ℝ)) 1

theorem boxRadius_adjacent {c : ℝ} (hc : 0 < c) (k : ℕ) :
    boxRadius c (k + 1) + boxRadius c k ≤ 4 * boxRadius c (k + 1) := by
  have hp : 0 < (k : ℝ) + 1 := by positivity
  have hq : 0 < (k : ℝ) + 1 + 1 := by positivity
  have h : boxRadius c k ≤ 2 * boxRadius c (k + 1) := by
    unfold boxRadius
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hp hq).mpr
    nlinarith [mul_nonneg hc.le (Nat.cast_nonneg k : 0 ≤ (k : ℝ))]
  linarith [boxRadius_pos hc (k + 1)]

/-- The images of shrinking boxes under an open continuous homomorphism
form a symmetric D′-sequence for every Haar measure. The quarter-radius
boxes give the adjacent-product and measure bounds of a D′′-sequence. -/
theorem groupBox_doubling [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (p : Multiplicative (I → ℝ) →* G) (hp : Continuous p) (hop : IsOpenMap p)
    {c : ℝ} (hc : 0 < c) :
    let U := fun k => groupBox p (boxRadius c k)
    let V := fun k => groupBox p (boxRadius c k / 4)
    DoublingSequence μ U ∧ CofinalAtOne U ∧
      (∀ k, IsOpen (U k) ∧ (U k)⁻¹ = U k) ∧
      ∃ C : ℝ≥0, ∀ k, MeasurableSet (V k) ∧
        V (k + 1) * V k ⊆ U (k + 1) ∧ μ (U k) ≤ C * μ (V k) := by
  let U := fun k => groupBox p (boxRadius c k)
  let V := fun k => groupBox p (boxRadius c k / 4)
  let D : ℝ≥0 := Fintype.card (BoxShift I)
  have hpos (k : ℕ) : 0 < μ (U k) :=
    (groupBox_isOpen p hop _).measure_pos μ ⟨1, groupBox_one p (boxRadius_pos hc k)⟩
  have hfinite (k : ℕ) : μ (U k) < ⊤ := by
    have hK := (isCompact_closedBall (0 : I → ℝ) (boxRadius c k)).image (hp.comp continuous_ofAdd)
    exact (measure_mono (image_mono ball_subset_closedBall)).trans_lt hK.measure_lt_top
  refine ⟨⟨fun k => groupBox_one p (boxRadius_pos hc k),
    fun k => (groupBox_isOpen p hop _).measurableSet, hpos, hfinite,
    fun _ _ h => groupBox_mono p (boxRadius_decreasing hc h), ?_⟩, ?_,
    fun k => ⟨groupBox_isOpen p hop _, groupBox_inv p _⟩, D, ?_⟩
  · refine ⟨D + 1, by positivity, fun k => ⟨?_, ?_⟩⟩
    · apply (hpos (k + 1)).trans_le (measure_mono ?_)
      intro x hx
      exact ⟨x, hx, 1, groupBox_one p (boxRadius_pos hc k), mul_one x⟩
    · have hsubset := (groupBox_mul_subset p _ _).trans
          (groupBox_mono p (boxRadius_adjacent hc k))
      refine ((measure_mono hsubset).trans (groupBox_measure_compare μ p (boxRadius_pos hc _))).trans_lt ?_
      exact ENNReal.mul_lt_mul_left (hpos _).ne' (hfinite _).ne
        (ENNReal.coe_lt_coe.mpr (lt_add_one D))
  · intro S hS
    have h := (hp.comp continuous_ofAdd).continuousAt.preimage_mem_nhds
      (show S ∈ 𝓝 (p (Multiplicative.ofAdd (0 : I → ℝ))) by
        change S ∈ 𝓝 (p 1)
        rwa [map_one])
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
    obtain ⟨k, hk⟩ := exists_nat_gt (c / ε)
    use k
    have hkr : boxRadius c k < ε := by
      unfold boxRadius
      apply (div_lt_iff₀ (by positivity)).mpr
      have h := (div_lt_iff₀ hε).mp hk
      nlinarith
    rintro _ ⟨x, hx, rfl⟩
    exact hball (ball_subset_ball hkr.le hx)
  · intro k
    refine ⟨(groupBox_isOpen p hop _).measurableSet, ?_, ?_⟩
    · apply (groupBox_mul_subset p _ _).trans (groupBox_mono p ?_)
      linarith [boxRadius_adjacent hc k]
    · have hm := groupBox_measure_compare μ p
        (show 0 < boxRadius c k / 4 from by positivity [boxRadius_pos hc k])
      have eq : (4 : ℝ) * (boxRadius c k / 4) = boxRadius c k := by ring
      rw [eq] at hm
      exact hm

end

end Masullo
