import DoublingSequences
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable (μ : Measure G) [μ.IsMulLeftInvariant]
variable {U : ℕ → Set G}

/-- The maximal limsup of the normalized integrals of a nonnegative function. -/
def densityMaximal (U : ℕ → Set G) (f : G → ℝ≥0∞) : G → ℝ≥0∞ :=
  doublingMaximal μ (μ.withDensity f) U

omit [MeasurableMul G] [MeasurableInv G] [μ.IsMulLeftInvariant] in
theorem densityMaximal_congr_ae {f g : G → ℝ≥0∞} (h : f =ᵐ[μ] g) :
    densityMaximal μ U f = densityMaximal μ U g := by
  unfold densityMaximal
  rw [withDensity_congr_ae h]

omit [MeasurableMul G] [MeasurableInv G] in
theorem densityMaximal_const_one (hU : DoublingSequence μ U) (x : G) :
    densityMaximal μ U (fun _ => 1) x = 1 := by
  unfold densityMaximal doublingMaximal
  change limsup (fun k => (μ.withDensity 1) (x • U k) / μ (U k)) atTop = 1
  rw [withDensity_one]
  have he (k : ℕ) : μ (x • U k) / μ (U k) = 1 := by
    rw [measure_smul, ENNReal.div_self (hU.positive k).ne' (hU.finite k).ne]
  simp only [he, limsup_const]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
theorem measurable_densityMaximal [SFinite μ] [MeasurableMul₂ G]
    (hU : ∀ k, MeasurableSet (U k)) (f : G → ℝ≥0∞) :
    Measurable (densityMaximal μ U f) :=
  measurable_doublingMaximal μ (μ.withDensity f) hU

omit [MeasurableInv G] in
private theorem densityWindow_le_truncation_add (hU : DoublingSequence μ U)
    (f : G → ℝ≥0∞) (hf : Measurable f) (t : ℝ≥0∞) (x : G) :
    ∀ k, μ.withDensity f (x • U k) / μ (U k) ≤
      μ.withDensity ({y | t < f y}.indicator f) (x • U k) / μ (U k) + t := by
  let F := {y | t < f y}.indicator f
  have hm : Measurable F := hf.indicator (measurableSet_lt measurable_const hf)
  have hF (y : G) : f y ≤ F y + t := by
    by_cases hy : y ∈ {y | t < f y}
    · rw [show F y = f y from Set.indicator_of_mem hy f]
      exact le_self_add
    · simpa only [F, Set.indicator_of_notMem hy f, zero_add] using (not_lt.mp hy)
  intro k
  have hmeas : MeasurableSet (x • U k) := (hU.measurable k).const_smul x
  change _ ≤ μ.withDensity F (x • U k) / μ (U k) + t
  rw [withDensity_apply f hmeas, withDensity_apply F hmeas]
  have h := lintegral_mono (μ := μ.restrict (x • U k)) hF
  rw [lintegral_add_left hm, setLIntegral_const, measure_smul] at h
  refine (ENNReal.div_le_div_right h _).trans_eq ?_
  rw [ENNReal.add_div, ENNReal.mul_div_cancel_right (hU.positive k).ne' (hU.finite k).ne]

omit [MeasurableInv G] in
theorem densityMaximal_le_truncation_add (hU : DoublingSequence μ U)
    (f : G → ℝ≥0∞) (hf : Measurable f) (t : ℝ≥0∞) (x : G) :
    densityMaximal μ U f x ≤ densityMaximal μ U ({y | t < f y}.indicator f) x + t := by
  unfold densityMaximal doublingMaximal
  refine (limsup_le_limsup (Eventually.of_forall (densityWindow_le_truncation_add μ hU f hf t x))).trans_eq ?_
  exact limsup_add_const atTop _ t (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    (isCoboundedUnder_le_of_le atTop (x := 0) (fun _ => zero_le))

omit [MeasurableInv G] in
/-- Corrected local weak bound in A.5.3.6(1). The integral truncates the
original function at the threshold, as in the manuscript's proof. -/
theorem densityMaximal_weak_truncation (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {B : Set G} (hB : μ (B * U 0) < ⊤) (hmB : MeasurableSet (B * U 0))
    {f : G → ℝ≥0∞} (hf : Measurable f) {a t b : ℝ≥0∞}
    (ha : a = b + t) (hb : 0 < b) (hb' : b ≠ ⊤) :
    μ (B ∩ {x | a < densityMaximal μ U f x}) ≤
      (C : ℝ≥0∞) / b * ∫⁻ x in (B * U 0) ∩ {y | t < f y}, f x ∂μ := by
  let F := {y | t < f y}.indicator f
  let E := B ∩ {x | b < densityMaximal μ U F x}
  have hE : B ∩ {x | a < densityMaximal μ U f x} ⊆ E := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change b < densityMaximal μ U F x
    apply lt_of_not_ge
    intro h
    exact (not_lt_of_ge
      ((densityMaximal_le_truncation_add μ hU f hf t x).trans (ha ▸ add_le_add h le_rfl))) hx.2
  have hweak := (doublingMaximal_measure_bound μ (μ.withDensity F) hU hC hDiff hB hb hb').1
  refine (measure_mono hE).trans (hweak.trans ?_)
  apply mul_le_mul_of_nonneg_left _ zero_le
  refine (measure_mono (Set.mul_subset_mul (show E ⊆ B from inter_subset_left) Subset.rfl)).trans_eq ?_
  rw [withDensity_apply _ hmB, lintegral_indicator (measurableSet_lt measurable_const hf), Measure.restrict_restrict
    (measurableSet_lt measurable_const hf), Set.inter_comm]

section LayerCake

private theorem setLIntegral_rpow_Ioo {q L : ℝ} (hq : -1 < q) (hL : 0 ≤ L) :
    (∫⁻ a in Ioo (0 : ℝ) L, ENNReal.ofReal (a ^ q)) =
      ENNReal.ofReal (L ^ (q + 1) / (q + 1)) := by
  have hi : IntegrableOn (fun a : ℝ => a ^ q) (Ioc 0 L) volume :=
    (intervalIntegral.intervalIntegrable_rpow' hq).1
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hi,
    ← intervalIntegral.integral_of_le hL, integral_rpow (Or.inl hq)]
  · rw [Real.zero_rpow (by linarith : q + 1 ≠ 0), sub_zero]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    exact Real.rpow_nonneg ha.1.le _

variable {X : Type*} [MeasurableSpace X]
variable (ρ ν : Measure X) [SFinite ρ]
variable {M f : X → ℝ}

/-- The power-integral estimate from a truncated weak bound, with its
dependence on the truncation parameter. -/
theorem lintegral_rpow_le_of_truncated_weak_bound
    (hm : Measurable M) (hf : Measurable f) (hM : ∀ x, 0 ≤ M x) (hF : ∀ x, 0 ≤ f x)
    {p θ K : ℝ}
    (hp : 1 < p) (hθ : 0 < θ) (hK : 0 ≤ K)
    (hweak : ∀ a : ℝ, 0 < a →
      ν {x | a < M x} ≤ ENNReal.ofReal (K / a) *
        ∫⁻ x in {x | θ * a < f x}, ENNReal.ofReal (f x) ∂ρ) :
    (∫⁻ x, ENNReal.ofReal (M x ^ p) ∂ν) ≤
      ENNReal.ofReal (p * K / ((p - 1) * θ ^ (p - 1))) *
        ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂ρ := by
  let Q := volume.restrict (Ioi (0 : ℝ))
  let w (a : ℝ) (x : X) :=
    (if θ * a < f x then ENNReal.ofReal (f x) else 0) * ENNReal.ofReal (a ^ (p - 2))
  have hw : Measurable (Function.uncurry w) := by
    have ht : MeasurableSet {z : ℝ × X | θ * z.1 < f z.2} :=
      measurableSet_lt (measurable_const.mul measurable_fst) (hf.comp measurable_snd)
    exact (Measurable.piecewise ht (hf.comp measurable_snd).ennreal_ofReal measurable_const).mul
      (measurable_fst.pow_const _).ennreal_ofReal
  have hwInner : Measurable (fun a => ∫⁻ x, w a x ∂ρ) :=
    Measurable.lintegral_prod_right hw
  have hpoint (a : ℝ) (ha : 0 < a) :
      ν {x | a < M x} * ENNReal.ofReal (a ^ (p - 1)) ≤
        ENNReal.ofReal K * ∫⁻ x, w a x ∂ρ := by
    have hfi : Measurable (fun x => if θ * a < f x then ENNReal.ofReal (f x) else 0) :=
      Measurable.piecewise (measurableSet_lt measurable_const hf) hf.ennreal_ofReal measurable_const
    calc
      _ ≤ (ENNReal.ofReal (K / a) * ∫⁻ x in {x | θ * a < f x}, ENNReal.ofReal (f x) ∂ρ) *
          ENNReal.ofReal (a ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right (hweak a ha) zero_le
      _ = ENNReal.ofReal ((K / a) * a ^ (p - 1)) *
          ∫⁻ x in {x | θ * a < f x}, ENNReal.ofReal (f x) ∂ρ := by
        rw [ENNReal.ofReal_mul (div_nonneg hK ha.le)]
        ac_rfl
      _ = ENNReal.ofReal K * ∫⁻ x, w a x ∂ρ := by
        have he : K / a * a ^ (p - 1) = K * a ^ (p - 2) := by
          have hpow : a ^ (p - 2) = a ^ (p - 1) / a := by
            rw [show p - 2 = (p - 1) - 1 by ring, Real.rpow_sub ha (p - 1) 1, Real.rpow_one]
          rw [hpow]
          ring
        rw [he, ENNReal.ofReal_mul hK, mul_assoc, mul_comm (ENNReal.ofReal (a ^ (p - 2)))]
        congr 1
        simp only [w, lintegral_mul_const _ hfi]
        rw [← lintegral_indicator (measurableSet_lt measurable_const hf)]
        rfl
  have hscaled (x : X) :
      (∫⁻ a, w a x ∂Q) =
        ENNReal.ofReal ((θ ^ (p - 1) * (p - 1))⁻¹) * ENNReal.ofReal (f x ^ p) := by
    have hset : {a : ℝ | θ * a < f x} = Iio (f x / θ) := by
      ext a
      change θ * a < f x ↔ a < f x / θ
      rw [lt_div_iff₀ hθ, mul_comm]
    have hcut : (fun a => if θ * a < f x then ENNReal.ofReal (f x) else 0) =
        (Iio (f x / θ)).indicator (fun _ : ℝ => ENNReal.ofReal (f x)) := by
      funext a
      have he : θ * a < f x ↔ a ∈ Iio (f x / θ) :=
        show a ∈ {a : ℝ | θ * a < f x} ↔ _ by rw [hset]
      by_cases ha : θ * a < f x
      · simp [ha, Set.indicator_of_mem (he.mp ha)]
      · simp [ha, Set.indicator_of_notMem (he.not.mp ha)]
    have hwcut : (fun a => w a x) = (Iio (f x / θ)).indicator
        (fun a : ℝ => ENNReal.ofReal (f x) * ENNReal.ofReal (a ^ (p - 2))) := by
      funext a
      change (if θ * a < f x then ENNReal.ofReal (f x) else 0) * _ = _
      rw [congrFun hcut a]
      by_cases ha : a ∈ Iio (f x / θ) <;> simp [ha]
    have hmeas : Measurable (fun a : ℝ => ENNReal.ofReal (a ^ (p - 2))) :=
      (measurable_id.pow_const _).ennreal_ofReal
    change (∫⁻ a, w a x ∂volume.restrict (Ioi 0)) = _
    rw [hwcut, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi, lintegral_const_mul _ hmeas,
      setLIntegral_rpow_Ioo (by linarith) (div_nonneg (hF x) hθ.le),
      ← ENNReal.ofReal_mul (hF x), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show p - 2 + 1 = p - 1 by ring, Real.div_rpow (hF x) hθ.le]
    have hpow : f x * f x ^ (p - 1) = f x ^ p := by
      calc
        f x * f x ^ (p - 1) = f x ^ (1 : ℝ) * f x ^ (p - 1) := by rw [Real.rpow_one]
        _ = f x ^ (1 + (p - 1)) := (Real.rpow_add' (hF x) (by linarith)).symm
        _ = f x ^ p := by congr 1; ring
    calc
      f x * (f x ^ (p - 1) / θ ^ (p - 1) / (p - 1)) =
          (f x * f x ^ (p - 1)) / (θ ^ (p - 1) * (p - 1)) := by
        rw [← div_div, ← mul_div_assoc, ← mul_div_assoc]
      _ = _ := by rw [hpow, div_eq_mul_inv, mul_comm]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul ν (Eventually.of_forall hM) hm.aemeasurable
    (zero_lt_one.trans hp)]
  have hle :
      (∫⁻ a, ν {x | a < M x} * ENNReal.ofReal (a ^ (p - 1)) ∂Q) ≤
        ENNReal.ofReal K * ∫⁻ a, ∫⁻ x, w a x ∂ρ ∂Q := by
    rw [← lintegral_const_mul _ hwInner]
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    exact hpoint a ha
  refine (mul_le_mul_of_nonneg_left hle zero_le).trans_eq ?_
  rw [lintegral_lintegral_swap hw.aemeasurable, lintegral_congr hscaled,
    lintegral_const_mul _ (hf.pow_const _).ennreal_ofReal,
    ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by linarith : 0 ≤ p),
    ← ENNReal.ofReal_mul (mul_nonneg (by linarith : 0 ≤ p) hK)]
  congr 2
  ring

private theorem setLIntegral_inv_Ioo (L : ℝ) (hNonneg : 0 ≤ L) :
    (∫⁻ a in Ioo (1 : ℝ) L, ENNReal.ofReal (a⁻¹)) = ENNReal.ofReal (max 0 (Real.log L)) := by
  by_cases hL : 1 < L
  · have hpos : 0 < L := zero_lt_one.trans hL
    have hi : IntegrableOn (fun a : ℝ => a⁻¹) (Ioc 1 L) volume :=
      (intervalIntegral.intervalIntegrable_inv
        (fun a ha => by
          rw [uIcc_of_le hL.le] at ha
          exact (zero_lt_one.trans_le ha.1).ne') continuous_id.continuousOn :
        IntervalIntegrable (fun a : ℝ => a⁻¹) volume 1 L).1
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hi,
      ← intervalIntegral.integral_of_le hL.le, integral_inv_of_pos zero_lt_one hpos, div_one,
      max_eq_right (Real.log_nonneg hL.le)]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    exact inv_nonneg.mpr (zero_le_one.trans ha.1.le)
  · have he : Ioo (1 : ℝ) L = ∅ := Ioo_eq_empty hL
    rw [he]
    simp only [Measure.restrict_empty, lintegral_zero_measure]
    rw [max_eq_left (Real.log_nonpos hNonneg (not_lt.mp hL)), ENNReal.ofReal_zero]

/-- The locally integrable logarithmic bound, with a unit-level cutoff and
the corresponding logarithmic argument. -/
theorem lintegral_le_of_truncated_weak_bound
    (hm : Measurable M) (hf : Measurable f) (hM : ∀ x, 0 ≤ M x) (hF : ∀ x, 0 ≤ f x)
    {θ K : ℝ} (hθ : 0 < θ) (hK : 0 ≤ K)
    (hweak : ∀ a : ℝ, 0 < a →
      ν {x | a < M x} ≤ ENNReal.ofReal (K / a) *
        ∫⁻ x in {x | θ * a < f x}, ENNReal.ofReal (f x) ∂ρ) :
    (∫⁻ x, ENNReal.ofReal (M x) ∂ν) ≤ ν univ + ENNReal.ofReal K *
      ∫⁻ x, ENNReal.ofReal (f x * max 0 (Real.log (f x / θ))) ∂ρ := by
  let Q := volume.restrict (Ioi (1 : ℝ))
  let w (a : ℝ) (x : X) :=
    (if θ * a < f x then ENNReal.ofReal (f x) else 0) * ENNReal.ofReal a⁻¹
  have hw : Measurable (Function.uncurry w) := by
    have ht : MeasurableSet {z : ℝ × X | θ * z.1 < f z.2} :=
      measurableSet_lt (measurable_const.mul measurable_fst) (hf.comp measurable_snd)
    exact (Measurable.piecewise ht (hf.comp measurable_snd).ennreal_ofReal measurable_const).mul
      measurable_fst.inv.ennreal_ofReal
  have hwInner : Measurable (fun a => ∫⁻ x, w a x ∂ρ) :=
    Measurable.lintegral_prod_right hw
  have hpoint (a : ℝ) (ha : 1 < a) :
      ν {x | a < M x} ≤ ENNReal.ofReal K * ∫⁻ x, w a x ∂ρ := by
    have hfi : Measurable (fun x => if θ * a < f x then ENNReal.ofReal (f x) else 0) :=
      Measurable.piecewise (measurableSet_lt measurable_const hf) hf.ennreal_ofReal measurable_const
    refine (hweak a (zero_lt_one.trans ha)).trans_eq ?_
    rw [div_eq_mul_inv, ENNReal.ofReal_mul hK, mul_assoc, mul_comm (ENNReal.ofReal a⁻¹)]
    congr 1
    simp only [w, lintegral_mul_const _ hfi]
    rw [← lintegral_indicator (measurableSet_lt measurable_const hf)]
    rfl
  have hvalue (x : X) :
      (∫⁻ a, w a x ∂Q) = ENNReal.ofReal (f x * max 0 (Real.log (f x / θ))) := by
    have hwcut : (fun a => w a x) = (Iio (f x / θ)).indicator
        (fun a : ℝ => ENNReal.ofReal (f x) * ENNReal.ofReal a⁻¹) := by
      funext a
      have he : θ * a < f x ↔ a ∈ Iio (f x / θ) := by
        change θ * a < f x ↔ a < f x / θ
        rw [lt_div_iff₀ hθ, mul_comm]
      by_cases ha : θ * a < f x
      · simp [w, ha, Set.indicator_of_mem (he.mp ha)]
      · simp [w, ha, Set.indicator_of_notMem (he.not.mp ha)]
    have hmeas : Measurable (fun a : ℝ => ENNReal.ofReal a⁻¹) :=
      measurable_id.inv.ennreal_ofReal
    change (∫⁻ a, w a x ∂volume.restrict (Ioi 1)) = _
    rw [hwcut, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Iio_inter_Ioi, lintegral_const_mul _ hmeas, setLIntegral_inv_Ioo _ (div_nonneg (hF x) hθ.le),
      ENNReal.ofReal_mul (hF x)]
  rw [lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hM) hm.aemeasurable]
  have hset : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext a
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ha
      rcases le_or_gt a 1 with h | h
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr h
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr fun _ ha hb => (not_lt_of_ge ha.2) hb
  rw [hset, lintegral_union measurableSet_Ioi hdis]
  apply add_le_add
  · exact (lintegral_mono (fun _ => measure_mono (subset_univ _))).trans_eq (by
      rw [setLIntegral_const, Real.volume_Ioc]; simp)
  · have hle : (∫⁻ a, ν {x | a < M x} ∂Q) ≤
        ENNReal.ofReal K * ∫⁻ a, ∫⁻ x, w a x ∂ρ ∂Q := by
      rw [← lintegral_const_mul _ hwInner]
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
      exact hpoint a ha
    refine hle.trans_eq ?_
    rw [lintegral_lintegral_swap hw.aemeasurable, lintegral_congr hvalue]

end LayerCake

section RealDensity

variable [SFinite μ] [MeasurableMul₂ G]

/-- A measurable real representative whenever the maximal limsup is finite almost everywhere. -/
def realDensityMaximal (U : ℕ → Set G) (f : G → ℝ) (x : G) : ℝ :=
  (densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x).toReal

private theorem realDensityMaximal_weak (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {B : Set G} (hB : μ (B * U 0) < ⊤) (hmB : MeasurableSet (B * U 0))
    {f : G → ℝ} (hf : Measurable f) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (a : ℝ) (ha : 0 < a) :
    (μ.restrict B) {x | a < realDensityMaximal μ U f x} ≤
      ENNReal.ofReal (((C : ℝ) / (1 - θ)) / a) *
        ∫⁻ x in {x | θ * a < f x}, ENNReal.ofReal (f x) ∂μ.restrict (B * U 0) := by
  have hM : Measurable (realDensityMaximal μ U f) :=
    (measurable_densityMaximal μ hU.measurable _).ennreal_toReal
  have hBθ : 0 < (1 - θ) * a := mul_pos (sub_pos.mpr hθ1) ha
  have htθ : 0 < θ * a := mul_pos hθ ha
  rw [Measure.restrict_apply (measurableSet_lt measurable_const hM), Set.inter_comm]
  have he : B ∩ {x | a < realDensityMaximal μ U f x} ⊆
      B ∩ {x | ENNReal.ofReal a < densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxm : a < (densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x).toReal := hx.2
    change ENNReal.ofReal a < densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).2 hxm |>.trans_le ENNReal.ofReal_toReal_le
  refine (measure_mono he).trans ?_
  have hadd : ENNReal.ofReal a = ENNReal.ofReal ((1 - θ) * a) + ENNReal.ofReal (θ * a) := by
    rw [← ENNReal.ofReal_add hBθ.le htθ.le]
    congr 1
    ring
  have hweak := densityMaximal_weak_truncation μ hU hC hDiff hB hmB hf.ennreal_ofReal
    hadd (ENNReal.ofReal_pos.mpr hBθ) ENNReal.ofReal_ne_top
  refine hweak.trans_eq ?_
  rw [Measure.restrict_restrict (measurableSet_lt measurable_const hf), Set.inter_comm (B * U 0)]
  congr 1
  · rw [div_div, ENNReal.ofReal_div_of_pos hBθ, ENNReal.ofReal_coe_nnreal]
  · have hset : {y | ENNReal.ofReal (θ * a) < ENNReal.ofReal (f y)} = {x | θ * a < f x} := by
      ext x
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg htθ.le
    rw [hset]

/-- A.5.3.6(2). The optimized local power bound with the manuscript's constant. -/
theorem densityMaximal_local_rpow (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {B : Set G} (hB : μ (B * U 0) < ⊤) (hmB : MeasurableSet (B * U 0))
    {f : G → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x in B, ENNReal.ofReal (realDensityMaximal μ U f x ^ p) ∂μ) ≤
      ENNReal.ofReal ((C : ℝ) * p ^ (p + 1) / (p - 1) ^ p) *
        ∫⁻ x in B * U 0, ENNReal.ofReal (f x ^ p) ∂μ := by
  let θ := (p - 1) / p
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hθ : 0 < θ := div_pos (sub_pos.mpr hp) hp0
  have hθ1 : θ < 1 := (div_lt_one hp0).mpr (by linarith)
  have hM : Measurable (realDensityMaximal μ U f) :=
    (measurable_densityMaximal μ hU.measurable _).ennreal_toReal
  have h := lintegral_rpow_le_of_truncated_weak_bound (μ.restrict (B * U 0)) (μ.restrict B)
    hM hf (fun _ => ENNReal.toReal_nonneg) hn hp hθ
    (div_nonneg C.coe_nonneg (sub_nonneg.mpr hθ1.le))
    (realDensityMaximal_weak μ hU hC hDiff hB hmB hf hθ hθ1)
  refine h.trans_eq ?_
  congr 2
  have hden : 1 - θ = 1 / p := by dsimp [θ]; field_simp [hp0.ne']; ring
  rw [hden, div_div_eq_mul_div, div_one]
  dsimp [θ]
  rw [Real.div_rpow (sub_nonneg.mpr hp.le) hp0.le]
  have hpPow : p ^ (p + 1) = p ^ (p - 1) * p * p := by
    calc
      p ^ (p + 1) = p ^ ((p - 1) + 1 + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hp0 ((p - 1) + 1) 1, Real.rpow_add hp0 (p - 1) 1, Real.rpow_one]
  have hmPow : (p - 1) ^ p = (p - 1) * (p - 1) ^ (p - 1) := by
    calc
      (p - 1) ^ p = (p - 1) ^ ((1 : ℝ) + (p - 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (sub_pos.mpr hp), Real.rpow_one]
  rw [hpPow, hmPow]
  have hz : p ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  have hdiv : ((p - 1) * ((p - 1) ^ (p - 1) / p ^ (p - 1))) =
      ((p - 1) * (p - 1) ^ (p - 1)) / p ^ (p - 1) := by rw [mul_div_assoc]
  rw [hdiv, div_div_eq_mul_div]
  ring

/-- Corrected estimate (A.5.3.11) from the weak estimate with truncation level a/2. -/
theorem densityMaximal_local_log (hU : DoublingSequence μ U)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {B : Set G} (hB : μ (B * U 0) < ⊤) (hmB : MeasurableSet (B * U 0))
    {f : G → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x in B, ENNReal.ofReal (realDensityMaximal μ U f x) ∂μ) ≤
      μ B + (2 * (C : ℝ≥0∞)) *
        ∫⁻ x in B * U 0, ENNReal.ofReal (f x * max 0 (Real.log (2 * f x))) ∂μ := by
  have hM : Measurable (realDensityMaximal μ U f) :=
    (measurable_densityMaximal μ hU.measurable _).ennreal_toReal
  have h := lintegral_le_of_truncated_weak_bound (μ.restrict (B * U 0)) (μ.restrict B)
    hM hf (fun _ => ENNReal.toReal_nonneg) hn (by norm_num : 0 < (1 : ℝ) / 2)
    (div_nonneg C.coe_nonneg (by norm_num : 0 ≤ 1 - (1 : ℝ) / 2))
    (realDensityMaximal_weak μ hU hC hDiff hB hmB hf (by norm_num) (by norm_num))
  have hc : (C : ℝ) / (1 - 1 / 2) = 2 * (C : ℝ) := by ring
  have hf2 (x : G) : f x / (1 / 2) = 2 * f x := by ring
  simpa only [Measure.restrict_apply_univ, hc, hf2, ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat] using h

end RealDensity

section CompactStages

variable [TopologicalSpace G] [T2Space G] [ContinuousMul G] [SigmaCompactSpace G]
variable [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

omit [MeasurableInv G] in
theorem densityMaximal_ae_finite (hU : DoublingSequence μ U) (hU₀ : IsCompact (U 0))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℝ≥0∞} (hInt : ∀ K : Set G, IsCompact K → (∫⁻ x in K, f x ∂μ) < ⊤) :
    ∀ᵐ x ∂μ, densityMaximal μ U f x < ⊤ := by
  letI : IsFiniteMeasureOnCompacts (μ.withDensity f) :=
    ⟨fun K hK => by rw [withDensity_apply _ hK.measurableSet]; exact hInt K hK⟩
  exact doublingMaximal_ae_lt_top μ (μ.withDensity f) hU hU₀ hC hDiff


/-- Local logarithmic integrability in the corrected A.5.3.6. The original
locally integrable term absorbs the change from log⁺ f to log⁺ (2 f). -/
theorem densityMaximal_local_integrable [MeasurableMul₂ G] (hU : DoublingSequence μ U) (hU₀ : IsCompact (U 0))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hInt : ∀ K : Set G, IsCompact K → (∫⁻ x in K, ENNReal.ofReal (f x) ∂μ) < ⊤)
    (hLog : ∀ K : Set G, IsCompact K →
      (∫⁻ x in K, ENNReal.ofReal (f x * max 0 (Real.log (f x))) ∂μ) < ⊤) :
    (∀ᵐ x ∂μ, densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x < ⊤) ∧
    (∀ K : Set G, IsCompact K →
      (∫⁻ x in K, ENNReal.ofReal (realDensityMaximal μ U f x) ∂μ) < ⊤) := by
  refine ⟨densityMaximal_ae_finite μ hU hU₀ hC hDiff hInt, fun K hK => ?_⟩
  have hKU : IsCompact (K * U 0) := hK.mul hU₀
  refine (densityMaximal_local_log μ hU hC hDiff hKU.measure_lt_top hKU.measurableSet hf hn).trans_lt ?_
  apply ENNReal.add_lt_top.mpr
  refine ⟨hK.measure_lt_top, ENNReal.mul_lt_top (by finiteness) ?_⟩
  have hid : ∀ x, f x * max 0 (Real.log (2 * f x)) ≤
      f x * max 0 (Real.log (f x)) + (Real.log 2) * f x := by
    intro x
    by_cases h : f x = 0
    · simp [h]
    · rw [Real.log_mul (by norm_num) h]
      have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog : max 0 (Real.log 2 + Real.log (f x)) ≤ max 0 (Real.log (f x)) + Real.log 2 := by
        apply max_le
        · exact add_nonneg (le_max_left _ _) hp
        · linarith [le_max_right 0 (Real.log (f x))]
      nlinarith [mul_le_mul_of_nonneg_left hlog (hn x)]
  have hle := lintegral_mono (μ := μ.restrict (K * U 0)) fun x => ENNReal.ofReal_le_ofReal (hid x)
  have hEq (x : G) :
      ENNReal.ofReal (f x * max 0 (Real.log (f x)) + Real.log 2 * f x) =
        ENNReal.ofReal (f x * max 0 (Real.log (f x))) +
          ENNReal.ofReal (Real.log 2) * ENNReal.ofReal (f x) := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [ENNReal.ofReal_add (mul_nonneg (hn x) (le_max_left _ _)) (mul_nonneg hlog (hn x)),
      ENNReal.ofReal_mul hlog]
  rw [lintegral_congr hEq] at hle
  refine hle.trans_lt ?_
  have hm : Measurable (fun x => ENNReal.ofReal (f x * max 0 (Real.log (f x)))) :=
    (hf.mul (measurable_const.max (Real.measurable_log.comp hf))).ennreal_ofReal
  rw [lintegral_add_left hm, lintegral_const_mul _ hf.ennreal_ofReal]
  exact ENNReal.add_lt_top.mpr ⟨hLog _ hKU, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hInt _ hKU)⟩

omit [MeasurableInv G] [T2Space G] [BorelSpace G] in
private theorem densityMaximal_global_weak_of_threshold
    (hU : DoublingSequence μ U) {K : Set G} (hK : IsCompact K) (hU₀ : U 0 ⊆ K)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (f : G → ℝ≥0∞) {a : ℝ≥0∞} (ha : 0 < a) (ha' : a ≠ ⊤)
    (M : G → ℝ≥0∞)
    (hM : ∀ x, a < M x → ∃ k, a < μ.withDensity f (x • U k) / μ (U k)) :
    μ {x | a < M x} ≤ (C : ℝ≥0∞) / a * ∫⁻ x, f x ∂μ := by
  let E := {x | a < M x}
  have hE : ⋃ n, compactCovering G n ∩ E = E := by
    rw [← Set.iUnion_inter, iUnion_compactCovering G, Set.univ_inter]
  change μ E ≤ _
  rw [← hE, Monotone.measure_iUnion (fun _ _ h => inter_subset_inter_left E (compactCovering_subset G h))]
  refine iSup_le fun n => ?_
  have hfin : μ (compactCovering G n * U 0) < ⊤ :=
    (measure_mono (Set.mul_subset_mul Subset.rfl hU₀)).trans_lt
      ((isCompact_compactCovering G n).mul hK).measure_lt_top
  have h := (doublingSequence_measure_bound_of_exists μ (μ.withDensity f) hU hC hDiff
    (E := compactCovering G n ∩ E)
    ((measure_mono (Set.mul_subset_mul inter_subset_left Subset.rfl)).trans_lt hfin)
    ha ha' (fun x hx => hM x hx.2)).1
  exact h.trans (mul_le_mul_of_nonneg_left (by
    have hfin : (μ.withDensity f) univ = ∫⁻ x, f x ∂μ := by
      rw [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]
    rw [← hfin]
    exact measure_mono (subset_univ _)) zero_le)

omit [MeasurableInv G] [T2Space G] [BorelSpace G] in
/-- Global weak type, with the improved constant C from the untruncated estimate. -/
theorem densityMaximal_global_weak_of_subset_compact
    (hU : DoublingSequence μ U) {K : Set G} (hK : IsCompact K) (hU₀ : U 0 ⊆ K)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (f : G → ℝ≥0∞) {a : ℝ≥0∞} (ha : 0 < a) (ha' : a ≠ ⊤) :
    μ {x | a < densityMaximal μ U f x} ≤ (C : ℝ≥0∞) / a * ∫⁻ x, f x ∂μ :=
  densityMaximal_global_weak_of_threshold μ hU hK hU₀ hC hDiff f ha ha' _
    fun _ hx => lt_iSup_iff.mp (hx.trans_le limsup_le_iSup)

omit [MeasurableInv G] [T2Space G] [BorelSpace G] in
theorem densityMaximal_global_weak (hU : DoublingSequence μ U) (hU₀ : IsCompact (U 0))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    (f : G → ℝ≥0∞) {a : ℝ≥0∞} (ha : 0 < a) (ha' : a ≠ ⊤) :
    μ {x | a < densityMaximal μ U f x} ≤ (C : ℝ≥0∞) / a * ∫⁻ x, f x ∂μ :=
  densityMaximal_global_weak_of_subset_compact μ hU hU₀ Subset.rfl hC hDiff f ha ha'

/-- Global strong type, with the same constant as A.5.3.6(2). -/
theorem densityMaximal_global_rpow [MeasurableMul₂ G] (hU : DoublingSequence μ U) (hU₀ : IsCompact (U 0))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal (realDensityMaximal μ U f x ^ p) ∂μ) ≤
      ENNReal.ofReal ((C : ℝ) * p ^ (p + 1) / (p - 1) ^ p) *
        ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (realDensityMaximal μ U f x ^ p))
  have hρ : ρ univ = ∫⁻ x, ENNReal.ofReal (realDensityMaximal μ U f x ^ p) ∂μ := by
    simp only [ρ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← hρ]
  have hu : ρ univ = ⨆ n, ρ (compactCovering G n) := by
    rw [← iUnion_compactCovering G, Monotone.measure_iUnion (fun _ _ h => compactCovering_subset G h)]
  rw [hu]
  refine iSup_le fun n => ?_
  have hCpt : IsCompact (compactCovering G n * U 0) := (isCompact_compactCovering G n).mul hU₀
  simp only [ρ]
  rw [withDensity_apply _ (isCompact_compactCovering G n).measurableSet]
  exact (densityMaximal_local_rpow μ hU hC hDiff hCpt.measure_lt_top hCpt.measurableSet hf hn hp).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := μ) (f := fun x => ENNReal.ofReal (f x ^ p))
          (subset_univ (compactCovering G n * U 0)))) zero_le)


/-- In the global strong estimate the real representative agrees almost
everywhere with the actual maximal limsup. -/
theorem densityMaximal_global_memLp [MeasurableMul₂ G]
    (hU : DoublingSequence μ U) (hU₀ : IsCompact (U 0))
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p)
    (hfp : (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) < ⊤) :
    (∫⁻ x, (densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x) ^ p ∂μ) ≤
      ENNReal.ofReal ((C : ℝ) * p ^ (p + 1) / (p - 1) ^ p) *
        ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hloc (K : Set G) (hK : IsCompact K) : (∫⁻ x in K, ENNReal.ofReal (f x) ∂μ) < ⊤ := by
    have hle (x : G) : ENNReal.ofReal (f x) ≤ 1 + ENNReal.ofReal (f x ^ p) := by
      by_cases hx : f x ≤ 1
      · exact ((ENNReal.ofReal_le_ofReal hx).trans_eq ENNReal.ofReal_one).trans le_self_add
      · have hxp : f x ≤ f x ^ p := by
          nth_rewrite 1 [← Real.rpow_one (f x)]
          exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hp.le
        exact (ENNReal.ofReal_le_ofReal hxp).trans le_add_self
    refine (lintegral_mono hle).trans_lt ?_
    have hpK :
        (∫⁻ x in K, ENNReal.ofReal (f x ^ p) ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := μ) (f := fun x => ENNReal.ofReal (f x ^ p)) (subset_univ K))
    rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hpK.trans_lt hfp⟩
  have hEq : ∀ᵐ x ∂μ, (densityMaximal μ U (fun y => ENNReal.ofReal (f y)) x) ^ p =
      ENNReal.ofReal (realDensityMaximal μ U f x ^ p) := by
    filter_upwards [densityMaximal_ae_finite μ hU hU₀ hC hDiff hloc] with x hx
    simp only [realDensityMaximal]
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0, ENNReal.ofReal_toReal hx.ne]
  rw [lintegral_congr_ae hEq]
  exact densityMaximal_global_rpow μ hU hU₀ hC hDiff hf hn hp

/-- The supremum of the normalized nonnegative integrals over all stages. -/
def densityWindowSup (U : ℕ → Set G) (f : G → ℝ≥0∞) (x : G) : ℝ≥0∞ :=
  ⨆ k, μ.withDensity f (x • U k) / μ (U k)

/-- Uniform square-integral bound over every averaging stage. -/
theorem densityWindowSup_sq [MeasurableMul₂ G]
    (hU : DoublingSequence μ U) {K : Set G} (hK : IsCompact K) (hU₀ : U 0 ⊆ K)
    {C : ℝ≥0} (hC : 0 < C) (hDiff : ∀ k, μ (U k * (U k)⁻¹) < C * μ (U k))
    {f : G → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hfp : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) < ⊤) :
    (∫⁻ x, densityWindowSup μ U (fun y => ENNReal.ofReal (f y)) x ^ 2 ∂μ) ≤
      8 * (C : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  let F : G → ℝ≥0∞ := fun y => ENNReal.ofReal (f y)
  let M : G → ℝ≥0∞ := densityWindowSup μ U F
  have hM : Measurable M := Measurable.iSup fun k =>
    measurable_translated_measure_div μ (μ.withDensity F) (hU.measurable k)
  letI : IsFiniteMeasureOnCompacts (μ.withDensity F) := ⟨fun L hL => by
    rw [withDensity_apply _ hL.measurableSet]
    have hle (x : G) : F x ≤ 1 + ENNReal.ofReal (f x ^ 2) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f x - 1)])
    refine (lintegral_mono hle).trans_lt ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    exact ENNReal.add_lt_top.mpr ⟨hL.measure_lt_top,
      (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hfp⟩⟩
  have hfinite : ∀ᵐ x ∂μ, M x < ⊤ :=
    doublingSequence_ae_lt_top_of_threshold μ (μ.withDensity F) hU hK hU₀ hC hDiff
      M fun _ _ => lt_iSup_iff.mp
  have hweak (a : ℝ) (ha : 0 < a) :
      μ {x | a < (M x).toReal} ≤ ENNReal.ofReal ((2 * (C : ℝ)) / a) *
        ∫⁻ x in {x | (1 / 2 : ℝ) * a < f x}, ENNReal.ofReal (f x) ∂μ := by
    let t := ENNReal.ofReal (a / 2)
    let T := {x | t < F x}
    let Ft := T.indicator F
    have ht : 0 < a / 2 := half_pos ha
    have hsplit : t + t = ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_add ht.le ht.le, add_halves]
    have hsub : {x | a < (M x).toReal} ⊆ {x | t < densityWindowSup μ U Ft x} := by
      intro x hx
      have hx' := ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).2 hx).trans_le
        (ENNReal.ofReal_toReal_le (a := M x))
      have hle : M x ≤ densityWindowSup μ U Ft x + t := iSup_le fun k =>
        (densityWindow_le_truncation_add μ hU F hf.ennreal_ofReal t x k).trans
          (add_le_add_left (le_iSup (fun j => μ.withDensity Ft (x • U j) / μ (U j)) k) t)
      exact lt_of_not_ge fun hxle => hx'.not_ge (hle.trans ((add_le_add_left hxle t).trans_eq hsplit))
    refine (measure_mono hsub).trans ((densityMaximal_global_weak_of_threshold μ hU hK hU₀
      hC hDiff Ft (ENNReal.ofReal_pos.mpr ht) ENNReal.ofReal_ne_top _
      (fun _ hx => lt_iSup_iff.mp hx)).trans_eq ?_)
    have hT : T = {x | (1 / 2 : ℝ) * a < f x} := by
      ext x
      change ENNReal.ofReal (a / 2) < ENNReal.ofReal (f x) ↔ _
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le, div_eq_mul_inv, mul_comm a]
      norm_num
    have hTm : MeasurableSet T := measurableSet_lt measurable_const hf.ennreal_ofReal
    have hcoeff : (C : ℝ≥0∞) / t = ENNReal.ofReal ((2 * (C : ℝ)) / a) := by
      have hreal : 2 * (C : ℝ) / a = (C : ℝ) / (a / 2) := by field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_coe_nnreal]
    rw [lintegral_indicator hTm, hT, hcoeff]
  have hsq := lintegral_rpow_le_of_truncated_weak_bound μ μ hM.ennreal_toReal hf
    (fun _ => ENNReal.toReal_nonneg) hn (p := 2) (θ := 1 / 2) (K := 2 * (C : ℝ))
    (by norm_num) (by norm_num) (mul_nonneg (by norm_num) C.2) hweak
  have hEq : (fun x => M x ^ 2) =ᵐ[μ] fun x => ENNReal.ofReal ((M x).toReal ^ 2) := by
    filter_upwards [hfinite] with x hx
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [lintegral_congr_ae hEq]
  have hcoeff : (2 : ℝ) * (2 * (C : ℝ)) / ((2 - 1) * (1 / 2 : ℝ) ^ ((2 : ℝ) - 1)) =
      8 * (C : ℝ) := by norm_num; ring
  rw [hcoeff, ENNReal.ofReal_mul (by norm_num : 0 ≤ (8 : ℝ)), ENNReal.ofReal_coe_nnreal] at hsq
  simpa [Real.rpow_two] using hsq

end CompactStages



omit [MeasurableMul G] [MeasurableInv G] in
/-- For a positive finite-measure set the constant input 1 already contradicts
(A.5.3.11), whose logarithmic term vanishes on that input. -/
theorem densityMaximal_constant_log_obstruction (hU : DoublingSequence μ U)
    {K : Set G} (hK : 0 < μ K) (hK' : μ K < ⊤) :
    μ K / 2 < ∫⁻ x in K, densityMaximal μ U (fun _ => 1) x ∂μ := by
  simp only [densityMaximal_const_one μ hU, setLIntegral_const, one_mul]
  have h := ENNReal.toReal_pos hK.ne' hK'.ne
  have h₁ : (μ K / 2).toReal < (μ K).toReal := by
    rw [ENNReal.toReal_div]
    norm_num
    linarith
  exact (ENNReal.toReal_lt_toReal (ENNReal.div_lt_top hK'.ne (by norm_num)).ne hK'.ne).mp h₁

end

end Masullo
