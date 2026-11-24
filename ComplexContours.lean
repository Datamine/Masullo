import PettisBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Topology.MetricSpace.Thickening

/-!
Scalar contour integrals for Appendix C. Adapted from Apache-2.0 RiemannMasullo
commit 4f78774 and its supporting rectangle and density integral lemmas.
-/

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

noncomputable section

namespace MeasureTheory.VectorMeasure

/-- Integrating against a complex density measure multiplies the integrand by the density. -/
theorem integral_withDensityᵥ_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℂ} (hg : Integrable g μ) (hgm : Measurable g)
    (hf : (μ.withDensityᵥ g).Integrable f) :
    (μ.withDensityᵥ g).integral f (ContinuousLinearMap.mul ℝ ℂ) = ∫ x, f x * g x ∂μ := by
  let ν := (μ.withDensityᵥ g).variation
  have hν : ν = μ.withDensity (fun x ↦ (‖g x‖₊ : ℝ≥0∞)) := μ.variation_withDensityᵥ hg
  let u (x : X) : ℂ := ‖g x‖⁻¹ • g x
  have hu : Measurable u := hgm.norm.inv.smul hgm
  have hbound (x : X) : ‖u x‖ ≤ 1 := by
    by_cases hx : g x = 0
    · simp [u, hx]
    · simp [u, norm_ne_zero_iff.mpr hx]
  have hscale (v : X → ℂ) (x : X) : ‖g x‖₊ • (v x * u x) = v x * g x := by
    by_cases hx : g x = 0
    · simp [hx]
    · simp only [u, NNReal.smul_def, coe_nnnorm]
      rw [← mul_smul_comm, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]
  have hconvert (v : X → ℂ) : (∫ x, v x * u x ∂ν) = ∫ x, v x * g x ∂μ := by
    rw [hν, integral_withDensity_eq_integral_smul hgm.nnnorm]
    simp_rw [hscale]
  rw [← hconvert]
  have hmul {v : X → ℂ} (hv : Integrable v ν) : Integrable (fun x ↦ v x * u x) ν :=
    hv.mul_bdd hu.aestronglyMeasurable (ae_of_all _ hbound)
  refine Integrable.induction
    (μ := ν) (P := fun v ↦ (μ.withDensityᵥ g).integral v (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ x, v x * u x ∂ν) ?_ ?_ ?_ ?_ hf
  · intro c s hs hsν
    have : IsFiniteMeasure (ν.restrict s) := ⟨by simpa [Measure.restrict_apply' hs] using hsν⟩
    rw [integral_indicator_const c hs, withDensityᵥ_apply hg hs, hconvert]
    simp_rw [← Set.indicator_mul_left, MeasureTheory.integral_indicator hs]
    exact (integral_const_mul c g).symm
  · intro v w _ hv hw hv' hw'
    simp only [Pi.add_apply, add_mul]
    rw [VectorMeasure.integral_add hv hw, MeasureTheory.integral_add (hmul hv) (hmul hw), hv', hw']
  · refine isClosed_eq VectorMeasure.continuous_integral ?_
    apply (show LipschitzWith 1 (fun v : X →₁[ν] ℂ ↦ ∫ x, v x * u x ∂ν) from ?_).continuous
    intro v w
    rw [ENNReal.coe_one, one_mul, Lp.edist_def,
      eLpNorm_one_eq_lintegral_enorm]
    refine (MeasureTheory.edist_integral_le_lintegral_edist
      (hmul (L1.integrable_coeFn v)) (hmul (L1.integrable_coeFn w))).trans ?_
    apply lintegral_mono
    intro x
    simp only [edist_eq_enorm_sub, ← sub_mul, enorm_mul, Pi.sub_apply]
    exact mul_le_of_le_one_right' (by simpa using ENNReal.ofReal_le_ofReal (hbound x))
  · intro v w hvw _ hv
    rw [← VectorMeasure.integral_congr_ae hvw, hv]
    exact MeasureTheory.integral_congr_ae (hvw.mono fun x hx ↦ congrArg (· * u x) hx)

end MeasureTheory.VectorMeasure

namespace Masullo

/-- Paper: Arc convention before Theorem C.5.2.4, p. 738. A contour is a closed,
continuous path with finitely many continuously differentiable pieces.
Deviation: The parameter interval is normalized to `[0, 1]` and the parametrization
is extended continuously to the real line. -/
structure ComplexContour where
  toContinuousMap : C(ℝ, ℂ)
  closed : toContinuousMap 1 = toContinuousMap 0
  piecewiseContDiff : ∃ (n : ℕ) (t : Fin (n + 1) → ℝ),
    StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContDiffOn ℝ 1 toContinuousMap (Icc (t i.castSucc) (t i.succ))

/-- Paper: Arc convention before Theorem C.5.2.4, p. 738. The trace is the image of
the parameter interval. -/
def ComplexContour.trace (γ : ComplexContour) : Set ℂ :=
  γ.toContinuousMap '' Icc 0 1

/-- Paper: Remark C.5.2.5, p. 738. The contour measure is the pushforward of
Lebesgue measure weighted by the complex velocity on the parameter interval. -/
def ComplexContour.measure (γ : ComplexContour) : VectorMeasure ℂ ℂ :=
  ((volume.restrict (Icc (0 : ℝ) 1)).withDensityᵥ
    (deriv (fun t ↦ γ.toContinuousMap t))).map γ.toContinuousMap

/-- Paper: Winding number notation in Theorem C.5.4.1, p. 741. The winding number
off the trace is expressed by its normalized scalar contour integral.
Deviation: It is represented by its value in `ℂ`. -/
def ComplexContour.index (γ : ComplexContour) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    complexMeasureIntegral γ.measure (fun w ↦ (w - z)⁻¹)

/-- Paper: Contours in Theorem C.5.2.4, p. 738. A positively oriented simple
contour is injective before the repeated endpoint and has index zero or one off its trace. -/
def PositiveSimpleContour :=
  { γ : ComplexContour // InjOn γ.toContinuousMap (Ico 0 1) ∧
    ∀ z ∉ γ.trace, γ.index z = 0 ∨ γ.index z = 1 }

/-- Paper: Contour interior in Theorem C.5.2.4, p. 738. The interior of a positively
oriented simple contour consists of points off the trace with index one. -/
def PositiveSimpleContour.interior (γ : PositiveSimpleContour) : Set ℂ :=
  {z | z ∉ γ.val.trace ∧ γ.val.index z = 1}

section ContourIntegral

open Complex intervalIntegral Metric

private lemma ComplexContour.partition_nonempty
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) :
    0 < n := by
  cases n with
  | zero =>
    have : (0 : ℝ) = 1 := by simpa [Fin.last_zero, ht0] using ht1
    exact absurd this zero_ne_one
  | succ n => exact Nat.succ_pos n

private lemma ComplexContour.exists_piece
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t) (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin n, s ∈ Icc (t i.castSucc) (t i.succ) := by
  have hn := ComplexContour.partition_nonempty ht0 ht1
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => s ≤ t i)
  have hne : S.Nonempty := by
    refine ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [ht1]
    exact hs.2
  have hmem := Finset.min'_mem S hne
  have hle : s ≤ t (S.min' hne) := (Finset.mem_filter.mp hmem).2
  have hpred (j : Fin (n + 1)) (hj : j < S.min' hne) : ¬ s ≤ t j := by
    intro hjs
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjs⟩
    exact (Finset.min'_le S j hjS).not_gt hj
  cases hmin : S.min' hne using Fin.cases with
  | zero =>
    have hs0 : s = 0 := le_antisymm (by simpa [hmin, ht0] using hle) hs.1
    refine ⟨⟨0, hn⟩, ?_, ?_⟩
    · simp [hs0, ht0]
    · have : t 0 ≤ t (Fin.succ (⟨0, hn⟩ : Fin n)) :=
        ht.monotone (Fin.zero_le _)
      simpa [hs0, ht0] using this
  | succ k =>
    refine ⟨k, ?_, ?_⟩
    · have hlt : k.castSucc < S.min' hne := by simpa [hmin] using k.castSucc_lt_succ
      exact (lt_of_not_ge (hpred k.castSucc hlt)).le
    · simpa [hmin] using hle

/-- The velocity of a piecewise `C¹` contour is integrable on the parameter interval. -/
lemma ComplexContour.integrable_deriv (g : ComplexContour) :
    Integrable (fun t : ℝ => deriv g.toContinuousMap t) (volume.restrict (Icc (0 : ℝ) 1)) := by
  obtain ⟨n, t, ht, ht0, ht1, hcd⟩ := g.piecewiseContDiff
  have hpiece (i : Fin n) :
      IntegrableOn (fun s : ℝ => deriv g.toContinuousMap s)
        (Icc (t i.castSucc) (t i.succ)) := by
    have hab : t i.castSucc < t i.succ := ht i.castSucc_lt_succ
    have hu : UniqueDiffOn ℝ (Icc (t i.castSucc) (t i.succ)) := uniqueDiffOn_Icc hab
    have hcont : ContinuousOn (derivWithin g.toContinuousMap (Icc (t i.castSucc) (t i.succ)))
        (Icc (t i.castSucc) (t i.succ)) :=
      (hcd i).continuousOn_derivWithin hu le_rfl
    have hint : IntegrableOn (derivWithin g.toContinuousMap (Icc (t i.castSucc) (t i.succ)))
        (Icc (t i.castSucc) (t i.succ)) :=
      hcont.integrableOn_compact isCompact_Icc
    have heq : EqOn (deriv g.toContinuousMap)
        (derivWithin g.toContinuousMap (Icc (t i.castSucc) (t i.succ)))
        (Ioo (t i.castSucc) (t i.succ)) := by
      intro s hs
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)).symm
    have hioo : IntegrableOn (deriv g.toContinuousMap) (Ioo (t i.castSucc) (t i.succ)) :=
      (hint.mono_set Ioo_subset_Icc_self).congr_fun heq.symm measurableSet_Ioo
    exact (integrableOn_congr_set_ae (Ioo_ae_eq_Icc (a := t i.castSucc)
      (b := t i.succ))).1 hioo
  have hunion : IntegrableOn (fun s : ℝ => deriv g.toContinuousMap s)
      (⋃ i : Fin n, Icc (t i.castSucc) (t i.succ)) :=
    (integrableOn_finite_iUnion).2 hpiece
  refine hunion.mono_set ?_
  intro s hs
  obtain ⟨i, hi⟩ := ComplexContour.exists_piece ht ht0 ht1 hs
  exact mem_iUnion.2 ⟨i, hi⟩

/-- The contour variation is supported on the trace. -/
lemma ComplexContour.variation_compl_trace (g : ComplexContour) :
    g.measure.variation (g.trace)ᶜ = 0 := by
  let p : ℝ → ℂ := g.toContinuousMap
  let m : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let n : VectorMeasure ℝ ℂ := m.withDensityᵥ (deriv p)
  have hvel : Integrable (deriv p) m := g.integrable_deriv
  have hvar : n.variation = m.withDensity (fun t => ‖deriv p t‖ₑ) :=
    Measure.variation_withDensityᵥ hvel
  have htrace : IsClosed g.trace :=
    (isCompact_Icc.image g.toContinuousMap.continuous).isClosed
  let pre : Set ℝ := Set.preimage p (g.traceᶜ)
  have hpre : MeasurableSet pre :=
    g.toContinuousMap.continuous.measurable (htrace.measurableSet.compl)
  have hzero_m : m pre = 0 := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    convert measure_empty (μ := volume)
    ext t
    simp only [pre, mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    intro ht htI
    exact ht ⟨t, htI, rfl⟩
  have hzero_n : n.variation pre = 0 := by
    rw [hvar, withDensity_apply (fun t => ‖deriv p t‖ₑ) hpre]
    exact setLIntegral_measure_zero _ _ hzero_m
  have hmap : (n.variation.map p) (g.traceᶜ) = 0 := by
    rw [Measure.map_apply g.toContinuousMap.continuous.measurable htrace.measurableSet.compl]
    exact hzero_n
  have hle : (n.map p).variation (g.traceᶜ) ≤ (n.variation.map p) (g.traceᶜ) :=
    VectorMeasure.variation_map_le _
  exact le_antisymm (hle.trans_eq hmap) bot_le

/-- A function continuous on the trace is integrable against the contour variation, and its
scalar integral is the parameter integral against the velocity. -/
lemma ComplexContour.scalarIntegral_eq_intervalIntegral (g : ComplexContour) {f : ℂ → ℂ}
    (hf : ContinuousOn f g.trace) :
    Integrable f g.measure.variation ∧
      complexMeasureIntegral g.measure f =
        ∫ t in (0 : ℝ)..1, f (g.toContinuousMap t) * deriv g.toContinuousMap t := by
  let p : C(ℝ, ℂ) := g.toContinuousMap
  let m : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let n : VectorMeasure ℝ ℂ := m.withDensityᵥ (deriv (p : ℝ → ℂ))
  have hvel : Integrable (deriv (p : ℝ → ℂ)) m := g.integrable_deriv
  have hclosed : IsClosed g.trace :=
    (isCompact_Icc.image p.continuous).isClosed
  let fRes : C(g.trace, ℂ) :=
    ⟨fun z => f z.1, ContinuousOn.comp_continuous hf continuous_subtype_val (fun z => z.2)⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hclosed fRes
  have hagree (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : F (p t) = f (p t) := by
    have hw : p t ∈ g.trace := ⟨t, ht, rfl⟩
    have := congrFun (congrArg ContinuousMap.toFun hF) ⟨p t, hw⟩
    simpa [fRes] using this
  have hcomp : ContinuousOn (fun t : ℝ => F (p t)) (Icc (0 : ℝ) 1) :=
    F.continuous.comp_continuousOn p.continuous.continuousOn
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖F (p t)‖ ≤ C := by
    have hne : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.2 zero_le_one
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcomp.norm
    exact ⟨‖F (p t)‖, norm_nonneg _, fun s hs => hmax hs⟩
  obtain ⟨C, hC0, hC⟩ := hbdd
  have hsmul : Integrable (fun t => ‖deriv (p : ℝ → ℂ) t‖ • F (p t)) m := by
    refine (hvel.norm.const_mul C).mono'
      (((aestronglyMeasurable_deriv (p : ℝ → ℂ) m).norm.smul
        (hcomp.aestronglyMeasurable measurableSet_Icc))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hfi : n.Integrable (F ∘ p) := by
    change Integrable (F ∘ p) n.variation
    rw [Measure.variation_withDensityᵥ hvel]
    exact (integrable_withDensity_iff_integrable_smul (measurable_deriv (p : ℝ → ℂ)).nnnorm).2
      hsmul
  have hfm : AEStronglyMeasurable F ((n.variation).map p) :=
    F.continuous.aestronglyMeasurable
  have hmeasure : g.measure = n.map (p : ℝ → ℂ) := rfl
  have hint : (n.map p).integral F (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ t in (0 : ℝ)..1, F (p t) * deriv (p : ℝ → ℂ) t := by
    rw [VectorMeasure.integral_map p.continuous.measurable hfm hfi]
    have hn : n = m.withDensityᵥ (deriv (p : ℝ → ℂ)) := rfl
    have hmul := VectorMeasure.integral_withDensityᵥ_mul (μ := m) (f := F ∘ (p : ℝ → ℂ))
      (g := deriv (p : ℝ → ℂ)) hvel (measurable_deriv _) hfi
    rw [hn]
    change (m.withDensityᵥ (deriv (p : ℝ → ℂ))).integral (F ∘ (p : ℝ → ℂ))
      (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [hmul]
    change (∫ x in Icc (0 : ℝ) 1, (F ∘ (p : ℝ → ℂ)) x * deriv (p : ℝ → ℂ) x) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rfl
  have hae : f =ᵐ[g.measure.variation] (F : ℂ → ℂ) := by
    have hsupp : ∀ᵐ w ∂g.measure.variation, w ∈ g.trace := by
      rw [ae_iff]
      exact g.variation_compl_trace
    filter_upwards [hsupp] with w hw
    have := congrFun (congrArg ContinuousMap.toFun hF) ⟨w, hw⟩
    simpa [fRes] using this.symm
  refine ⟨?_, ?_⟩
  · exact (hfi.map hfm).congr hae.symm
  · have hcongr := VectorMeasure.integral_congr_ae (μ := g.measure)
      (B := ContinuousLinearMap.mul ℝ ℂ) hae
    rw [complexMeasureIntegral, hcongr, hmeasure, hint]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall ?_)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    rw [hagree t ht']

private lemma sub_eq_mul_intervalIntegral_deriv {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) {w z : ℂ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, w + (t : ℂ) * (z - w) ∈ Ω) :
    g z - g w = (z - w) * ∫ t in (0 : ℝ)..1, deriv g (w + (t : ℂ) * (z - w)) := by
  let p (t : ℝ) : ℂ := w + (t : ℂ) * (z - w)
  have hp (t : ℝ) : HasDerivAt p (z - w) t := by
    have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    simpa [p, one_mul] using (hid.mul_const (z - w)).const_add w
  have hcomp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (g ∘ p) (deriv g (p t) * (z - w)) t := by
    have hgt : HasDerivAt g (deriv g (p t)) (p t) :=
      (hg.differentiableAt (hΩ.mem_nhds (hseg t ht))).hasDerivAt
    simpa using (hgt.complexToReal_fderiv.comp_hasDerivAt t (hp t))
  have hderiv_cont : ContinuousOn (deriv g) Ω :=
    (hg.contDiffOn hΩ).continuousOn_deriv_of_isOpen hΩ le_rfl
  have hpath : ContinuousOn p (Icc (0 : ℝ) 1) := by fun_prop
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hint : IntervalIntegrable (fun t => deriv g (p t) * (z - w)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    exact (hderiv_cont.comp hpath fun t ht => hseg t ht).mul continuousOn_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := g ∘ p) (f' := fun t => deriv g (p t) * (z - w))
    (fun t ht => hcomp t (by simpa [hI] using ht)) hint
  have hends : (g ∘ p) 1 - (g ∘ p) 0 = g z - g w := by simp [p]
  rw [← hends, ← hFTC, intervalIntegral.integral_mul_const, mul_comm]

private lemma norm_dslope_le_on {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) {M : Set ℂ} (hM : IsCompact M) (hMΩ : M ⊆ Ω) :
    ∃ C, ∀ w ∈ M, ∀ z ∈ M, ‖dslope g w z‖ ≤ C := by
  obtain ⟨δ, hδ, hthick⟩ := hM.exists_cthickening_subset_open hΩ hMΩ
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hthick2 : cthickening (δ / 2) M ⊆ Ω :=
    (cthickening_mono (half_le_self hδ.le) M).trans hthick
  have hKc : IsCompact (cthickening (δ / 2) M) := hM.cthickening
  have hderiv_cont : ContinuousOn (fun ξ => ‖deriv g ξ‖) (cthickening (δ / 2) M) :=
    ((hg.contDiffOn hΩ).continuousOn_deriv_of_isOpen hΩ le_rfl).norm.mono hthick2
  have hB : ∃ B, ∀ ξ ∈ cthickening (δ / 2) M, ‖deriv g ξ‖ ≤ B := by
    by_cases hne : (cthickening (δ / 2) M).Nonempty
    · obtain ⟨ξ, hξ, hmax⟩ := hKc.exists_isMaxOn hne hderiv_cont
      exact ⟨‖deriv g ξ‖, fun η hη => hmax hη⟩
    · exact ⟨0, fun ξ hξ => (hne ⟨ξ, hξ⟩).elim⟩
  obtain ⟨B, hB⟩ := hB
  have hg_cont : ContinuousOn (fun ξ => ‖g ξ‖) M := hg.continuousOn.norm.mono hMΩ
  have hG : ∃ G, ∀ ξ ∈ M, ‖g ξ‖ ≤ G := by
    by_cases hne : M.Nonempty
    · obtain ⟨ξ, hξ, hmax⟩ := hM.exists_isMaxOn hne hg_cont
      exact ⟨‖g ξ‖, fun η hη => hmax hη⟩
    · exact ⟨0, fun ξ hξ => (hne ⟨ξ, hξ⟩).elim⟩
  obtain ⟨G, hG⟩ := hG
  refine ⟨max B (4 * G / δ), fun w hw z hz => ?_⟩
  have hmem_seg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hclose : ‖z - w‖ < δ / 2) :
      w + (t : ℂ) * (z - w) ∈ cthickening (δ / 2) M := by
    refine (thickening_subset_cthickening (δ / 2) M) ?_
    rw [mem_thickening_iff]
    refine ⟨w, hw, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have ht1' : |t| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
    calc |t| * ‖z - w‖ ≤ 1 * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right ht1' (norm_nonneg _)
      _ = ‖z - w‖ := by ring
      _ < δ / 2 := hclose
  by_cases hclose : ‖z - w‖ < δ / 2
  · have hseg : ∀ t ∈ Icc (0 : ℝ) 1, w + (t : ℂ) * (z - w) ∈ Ω :=
      fun t ht => hthick2 (hmem_seg ht.1 ht.2 hclose)
    by_cases hzw : z = w
    · rw [hzw, dslope_same]
      exact (hB w (self_subset_cthickening M hw)).trans (le_max_left _ _)
    · have hsub := sub_eq_mul_intervalIntegral_deriv hΩ hg hseg
      have heq : dslope g w z =
          ∫ t in (0 : ℝ)..1, deriv g (w + (t : ℂ) * (z - w)) := by
        rw [dslope_of_ne _ hzw]
        simp only [slope, vsub_eq_sub, smul_eq_mul]
        rw [hsub]
        field_simp [sub_ne_zero.mpr hzw]
      rw [heq]
      have hle_int := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := B) (f := fun t : ℝ => deriv g (w + (t : ℂ) * (z - w))) (fun t ht => ?_)
      · have hB1 : B * |1 - 0| = B := by simp
        exact (hle_int.trans_eq hB1).trans (le_max_left _ _)
      · rw [uIoc_of_le zero_le_one] at ht
        exact hB _ (hmem_seg (le_of_lt ht.1) ht.2 hclose)
  · have hfar : δ / 2 ≤ ‖z - w‖ := le_of_not_gt hclose
    have hzw : z ≠ w := by
      intro h
      subst h
      simp at hfar
      linarith
    rw [dslope_of_ne _ hzw]
    simp only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv]
    rw [← div_eq_inv_mul]
    have hnum : ‖g z - g w‖ ≤ 2 * G := by
      calc ‖g z - g w‖ ≤ ‖g z‖ + ‖g w‖ := norm_sub_le _ _
        _ ≤ G + G := add_le_add (hG z hz) (hG w hw)
        _ = 2 * G := by ring
    have hpos : 0 < ‖z - w‖ := lt_of_lt_of_le hδ2 hfar
    have hG0 : 0 ≤ 2 * G := le_trans (norm_nonneg _) hnum
    calc ‖g z - g w‖ / ‖z - w‖ ≤ (2 * G) / ‖z - w‖ :=
          div_le_div_of_nonneg_right hnum hpos.le
      _ ≤ (2 * G) / (δ / 2) := div_le_div_of_nonneg_left hG0 hδ2 hfar
      _ = 4 * G / δ := by ring
      _ ≤ max B (4 * G / δ) := le_max_right _ _

end ContourIntegral

open Complex Metric intervalIntegral

private theorem ComplexContour.scalarIntegral_eq_integral (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) :
    γ.measure.Integrable g ∧
      complexMeasureIntegral γ.measure g =
        ∫ t in Icc (0 : ℝ) 1, g (γ.toContinuousMap t) *
          deriv (fun s ↦ γ.toContinuousMap s) t := by
  simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    using γ.scalarIntegral_eq_intervalIntegral hg

/-- The boundary integral following the bottom and right edges from `z` to `w`,
then the top and left edges from `w` back to `z`. -/
def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f

/-- The four oriented edge integrals, with real parameters increasing from the
coordinates of `z` to the coordinates of `w`. -/
theorem rectangleIntegral_eq (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I)) := by
  exact Complex.wedgeIntegral_add_wedgeIntegral_eq z w f

/- The logarithm argument for the simple kernel is adapted from
   DedekindResidue.ExplicitFormula.RectangleContour in AINTLIB.
   Copyright (c) 2026 Chris Birkbeck. Released under Apache 2.0. -/

private theorem integral_log_deriv {p : ℝ → ℂ} {a b : ℝ} {v : ℂ}
    (hp : ∀ x ∈ uIcc a b, HasDerivAt p v x)
    (hslit : ∀ x ∈ uIcc a b, p x ∈ Complex.slitPlane) :
    (∫ x in a..b, v * (p x)⁻¹) = Complex.log (p b) - Complex.log (p a) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    simpa only [div_eq_mul_inv] using (hp x hx).clog_real (hslit x hx)
  · have hc : ContinuousOn p (uIcc a b) := fun x hx ↦
      (hp x hx).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul
      (hc.inv₀ fun x hx ↦ Complex.slitPlane_ne_zero (hslit x hx))).intervalIntegrable

private theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast
  ring

private theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + Real.pi * Complex.I := by
  have h := log_neg_of_im_pos (u := -u) (by simpa using neg_pos.mpr hu)
  rw [neg_neg] at h
  linear_combination -h

private theorem hasDerivAt_horizontal (x y : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * Complex.I - ρ) 1 x := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const
    ((y : ℂ) * Complex.I)).sub_const ρ

private theorem hasDerivAt_vertical (x y : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * Complex.I - ρ) Complex.I y := by
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const
    Complex.I).const_add (x : ℂ)).sub_const ρ

/-- The boundary integral of the simple Cauchy kernel is `2πi` when the
pole is strictly inside the rectangle. -/
theorem rectangleIntegral_sub_inv {z w ρ : ℂ}
    (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (fun s ↦ (s - ρ)⁻¹) z w = 2 * (Real.pi : ℂ) * Complex.I := by
  let p (x y : ℝ) := (x : ℂ) + y * Complex.I - ρ
  have hB := integral_log_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x z.im) (fun x _ ↦ hasDerivAt_horizontal x z.im ρ)
    (fun x _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inr (by simpa [p] using (sub_neg.mpr hρ.2.1).ne)))
  have hT := integral_log_deriv (a := z.re) (b := w.re)
    (p := fun x ↦ p x w.im) (fun x _ ↦ hasDerivAt_horizontal x w.im ρ)
    (fun x _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inr (by simpa [p] using (sub_pos.mpr hρ.2.2).ne')))
  have hR := integral_log_deriv (a := z.im) (b := w.im)
    (p := p w.re) (fun y _ ↦ hasDerivAt_vertical w.re y ρ)
    (fun y _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa [p] using sub_pos.mpr hρ.1.2)))
  have hL := integral_log_deriv (a := z.im) (b := w.im)
    (p := fun y ↦ -p z.re y) (fun y _ ↦ (hasDerivAt_vertical z.re y ρ).neg)
    (fun y _ ↦ Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa [p] using neg_pos.mpr (sub_neg.mpr hρ.1.1))))
  have hBL : (p z.re z.im).im < 0 := by simpa [p] using sub_neg.mpr hρ.2.1
  have hTL : 0 < (p z.re w.im).im := by simpa [p] using sub_pos.mpr hρ.2.2
  simp only [one_mul] at hB hT
  simp only [inv_neg, neg_mul_neg] at hL
  rw [intervalIntegral.integral_const_mul] at hL hR
  rw [rectangleIntegral_eq]
  change (∫ x in z.re..w.re, (p x z.im)⁻¹) - (∫ x in z.re..w.re, (p x w.im)⁻¹) +
    Complex.I * (∫ y in z.im..w.im, (p w.re y)⁻¹) -
    Complex.I * (∫ y in z.im..w.im, (p z.re y)⁻¹) = _
  rw [hB, hT, hR, hL, log_neg_of_im_pos hTL, log_neg_of_im_neg hBL]
  ring

/-- A continuous scalar function on the trace gives an integrable velocity-weighted
function on the parameter interval. -/
private theorem ComplexContour.integrableOn_mul_deriv (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) :
    IntegrableOn (fun t ↦ g (γ.toContinuousMap t) * deriv (fun s ↦ γ.toContinuousMap s) t)
      (Icc (0 : ℝ) 1) := by
  have hc := hg.comp γ.toContinuousMap.continuous.continuousOn
    (fun t ht ↦ mem_image_of_mem γ.toContinuousMap ht)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_norm_le
  exact γ.integrable_deriv.bdd_mul (hc.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hC _ (mem_image_of_mem _ ht))

section RectangleContour

attribute [local simp] Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_three

open Complex Metric intervalIntegral

/-- The four affine sides of the counterclockwise unit square, each traversed
in one quarter of the parameter interval. -/
private def squareSide (i : Fin 4) (t : ℝ) : ℂ :=
  ![⟨4 * t, 0⟩, ⟨1, 4 * t - 1⟩, ⟨3 - 4 * t, 1⟩, ⟨0, 4 - 4 * t⟩] i

private def squarePath (t : ℝ) : ℂ :=
  if t ≤ 1 / 4 then squareSide 0 t else if t ≤ 1 / 2 then squareSide 1 t
  else if t ≤ 3 / 4 then squareSide 2 t else squareSide 3 t

@[local fun_prop] private lemma ofReal_contDiff_one : ContDiff ℝ 1 Complex.ofReal :=
  Complex.ofRealCLM.contDiff

private lemma squareSide_smooth (i : Fin 4) : ContDiff ℝ 1 (squareSide i) := by
  change ContDiff ℝ 1 (fun t ↦ squareSide i t)
  unfold squareSide
  fin_cases i <;> simp [Complex.mk_eq_add_mul_I] <;> fun_prop

private lemma squarePath_continuous : Continuous squarePath := by
  unfold squarePath
  refine Continuous.if_le (squareSide_smooth 0).continuous ?_ continuous_id continuous_const
    (fun t ht ↦ by norm_num [show t = 1 / 4 from ht, squareSide])
  refine Continuous.if_le (squareSide_smooth 1).continuous ?_ continuous_id continuous_const
    (fun t ht ↦ by norm_num [show t = 1 / 2 from ht, squareSide])
  exact Continuous.if_le (squareSide_smooth 2).continuous (squareSide_smooth 3).continuous
    continuous_id continuous_const (fun t ht ↦ by norm_num [show t = 3 / 4 from ht, squareSide])

private lemma squarePath_eqOn_side (i : Fin 4) :
    EqOn squarePath (squareSide i) (Icc (i.val / 4 : ℝ) ((i.val + 1) / 4)) := by
  intro t ht
  obtain ⟨hl, hr⟩ := ht
  fin_cases i <;> norm_num at hl hr ⊢ <;> unfold squarePath <;> split_ifs <;>
    first | rfl | exfalso; linarith | apply Complex.ext <;> norm_num [squareSide] <;> linarith

private lemma squarePath_injOn : InjOn squarePath (Ico 0 1) := by
  intro s hs t ht he
  obtain ⟨hs₀, hs₁⟩ := hs
  obtain ⟨ht₀, ht₁⟩ := ht
  unfold squarePath at he
  split_ifs at he <;> obtain ⟨h₁, h₂⟩ := Complex.ext_iff.mp he <;>
    norm_num [squareSide] at h₁ <;> norm_num [squareSide] at h₂ <;> linarith

/-- Stretch the unit square to a rectangle with the specified lower left
and upper right corners. -/
private def stretchSquare (z w u : ℂ) : ℂ :=
  ⟨z.re + (w.re - z.re) * u.re, z.im + (w.im - z.im) * u.im⟩

private lemma stretchSquare_smooth (z w : ℂ) : ContDiff ℝ 1 (stretchSquare z w) := by
  have hre : ContDiff ℝ 1 Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ 1 Complex.im := Complex.imCLM.contDiff
  unfold stretchSquare
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

private lemma stretchSquare_injective {z w : ℂ} (hx : z.re < w.re) (hy : z.im < w.im) :
    Injective (stretchSquare z w) := by
  intro a b h
  have ⟨h₁, h₂⟩ := Complex.ext_iff.mp h
  exact Complex.ext (mul_left_cancel₀ (sub_pos.mpr hx).ne' (add_left_cancel h₁))
    (mul_left_cancel₀ (sub_pos.mpr hy).ne' (add_left_cancel h₂))

private def rectangleContour (z w : ℂ) : ComplexContour where
  toContinuousMap := ⟨stretchSquare z w ∘ squarePath,
    (stretchSquare_smooth z w).continuous.comp squarePath_continuous⟩
  closed := by norm_num [squarePath, squareSide, Function.comp_def]
  piecewiseContDiff := by
    refine ⟨4, fun i ↦ i.val / (4 : ℝ), fun i j hij ↦ ?_, by norm_num, by norm_num, fun i ↦ ?_⟩
    · exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (by norm_num)
    · apply ((stretchSquare_smooth z w).comp (squareSide_smooth i)).contDiffOn.congr
      intro t ht
      exact congrArg (stretchSquare z w) (squarePath_eqOn_side i (by simpa using ht))

private lemma squarePath_trace :
    squarePath '' Icc 0 1 = (Icc 0 1 ×ℂ Icc 0 1) \ (Ioo 0 1 ×ℂ Ioo 0 1) := by
  ext u
  constructor
  · rintro ⟨t, ⟨hl, hr⟩, rfl⟩
    unfold squarePath
    split_ifs <;> simp [squareSide, Complex.mem_reProdIm] <;> constructor <;> linarith
  · rintro ⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, hout⟩
    have boundary : u.im = 0 ∨ u.re = 1 ∨ u.im = 1 ∨ u.re = 0 := by
      by_contra! h
      exact hout ⟨⟨hx.lt_of_ne h.2.2.2.symm, hx'.lt_of_ne h.2.1⟩,
        hy.lt_of_ne h.1.symm, hy'.lt_of_ne h.2.2.1⟩
    rcases boundary with h | h | h | h
    · refine ⟨u.re / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [squarePath_eqOn_side 0 (by norm_num; constructor <;> linarith : u.re / 4 ∈ _)]
      apply Complex.ext <;> simp [squareSide, h]
      ring
    · refine ⟨(u.im + 1) / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [squarePath_eqOn_side 1 (by norm_num; constructor <;> linarith : (u.im + 1) / 4 ∈ _)]
      apply Complex.ext <;> simp [squareSide, h]
      ring
    · refine ⟨(3 - u.re) / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [squarePath_eqOn_side 2 (by norm_num; constructor <;> linarith : (3 - u.re) / 4 ∈ _)]
      apply Complex.ext <;> simp [squareSide, h]
      ring
    · refine ⟨(4 - u.im) / 4, ⟨by linarith, by linarith⟩, ?_⟩
      rw [squarePath_eqOn_side 3 (by norm_num; constructor <;> linarith : (4 - u.im) / 4 ∈ _)]
      apply Complex.ext <;> simp [squareSide, h]
      ring

private lemma rectangleContour_trace {z w : ℂ} (hx : z.re < w.re) (hy : z.im < w.im) :
    (rectangleContour z w).trace = (Complex.Rectangle z w) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im) := by
  change (stretchSquare z w ∘ squarePath) '' Icc 0 1 = _
  rw [image_comp, squarePath_trace]
  have coord (a b u : ℝ) (hab : a < b) :
      (a + (b - a) * u ∈ Icc a b ↔ u ∈ Icc 0 1) ∧
      (a + (b - a) * u ∈ Ioo a b ↔ u ∈ Ioo 0 1) := by
    have hle : a + (b - a) * u ≤ b ↔ u ≤ 1 := by
      calc a + (b - a) * u ≤ b ↔ (b - a) * u ≤ (b - a) * 1 := by constructor <;> intro h <;> linarith
           _ ↔ _ := mul_le_mul_iff_right₀ (sub_pos.mpr hab)
    have hlt : a + (b - a) * u < b ↔ u < 1 := by
      calc a + (b - a) * u < b ↔ (b - a) * u < (b - a) * 1 := by constructor <;> intro h <;> linarith
           _ ↔ _ := mul_lt_mul_iff_right₀ (sub_pos.mpr hab)
    simp [Set.mem_Icc, Set.mem_Ioo, hle, hlt, sub_pos.mpr hab]
  have he (v : ℂ) : stretchSquare z w v ∈ Rectangle z w \ (Ioo z.re w.re ×ℂ Ioo z.im w.im) ↔
      v ∈ (Icc 0 1 ×ℂ Icc 0 1) \ (Ioo 0 1 ×ℂ Ioo 0 1) := by
    simp only [Rectangle, uIcc_of_le hx.le, uIcc_of_le hy.le, Set.mem_sdiff, mem_reProdIm,
      stretchSquare, (coord _ _ _ hx).1, (coord _ _ _ hy).1, (coord _ _ _ hx).2, (coord _ _ _ hy).2]
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact (he v).mpr hv
  · intro u hu
    let v : ℂ := ⟨(u.re - z.re) / (w.re - z.re), (u.im - z.im) / (w.im - z.im)⟩
    have huv : stretchSquare z w v = u := by
      apply Complex.ext <;> dsimp [stretchSquare, v] <;> field_simp [sub_pos.mpr hx |>.ne', sub_pos.mpr hy |>.ne'] <;> ring
    exact ⟨v, (he v).mp (huv ▸ hu), huv⟩

/-- Integrating on an affine reparametrization of a straight side is a real
change of variable. Only the open parameter interval contributes. -/
private lemma integral_affine_side {p l : ℝ → ℂ} {a b m d lo hi : ℝ} {v : ℂ}
    (hab : a ≤ b) (hp : EqOn p (fun t ↦ l (m * t + d)) (Icc a b))
    (hl : ∀ t, HasDerivAt l v t) (hlo : m * a + d = lo) (hhi : m * b + d = hi) (g : ℂ → ℂ) :
    (∫ t in a..b, g (p t) * deriv p t) = (∫ u in lo..hi, g (l u)) * v := by
  calc
    _ = ∫ t in a..b, m • (g (l (m * t + d)) * v) := by
      apply integral_congr_Ioo_of_le hab
      intro t ht
      have hnear := hp.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2)
      have hdt : HasDerivAt (fun t : ℝ ↦ m * t + d) m t := by
        simpa using ((hasDerivAt_id' t).const_mul m).add_const d
      have hvel := ((hl _).scomp t hdt).congr_of_eventuallyEq hnear
      simp [hp (Ioo_subset_Icc_self ht), hvel.deriv, Complex.real_smul, mul_left_comm]
    _ = _ := by
      rw [intervalIntegral.integral_smul, smul_integral_comp_mul_add (fun t ↦ g (l t) * v),
        hlo, hhi, intervalIntegral.integral_mul_const]

private lemma rectangleContour_integral (z w : ℂ) {g : ℂ → ℂ}
    (hg : ContinuousOn g (rectangleContour z w).trace) :
    complexMeasureIntegral (rectangleContour z w).measure g = rectangleIntegral g z w := by
  let p : ℝ → ℂ := (rectangleContour z w).toContinuousMap
  let F (t : ℝ) := g (p t) * deriv p t
  have hside (i : Fin 4) :
      EqOn p (fun t ↦ stretchSquare z w (squareSide i t)) (Icc (i.val / 4 : ℝ) ((i.val + 1) / 4)) :=
    fun _ ht ↦ congrArg (stretchSquare z w) (squarePath_eqOn_side i ht)
  let H (y x : ℝ) := (x : ℂ) + y * I
  let V (x y : ℝ) := (x : ℂ) + y * I
  have hH (y x : ℝ) : HasDerivAt (H y) 1 x := by
    simpa [H] using Complex.ofRealCLM.hasDerivAt.add_const ((y : ℂ) * I) (x := x)
  have hV (x y : ℝ) : HasDerivAt (V x) I y := by
    simpa [V] using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (x : ℂ) (x := y)
  let dx := w.re - z.re
  let dy := w.im - z.im
  have h₀ : (∫ t in (0 : ℝ)..1/4, F t) = (∫ u in z.re..w.re, g (H z.im u)) * 1 := by
    apply integral_affine_side (m := 4 * dx) (d := z.re) (by norm_num) _ (hH _) _ _ g
    · intro t ht
      rw [hside 0 (by simpa using ht)]
      apply Complex.ext <;> simp [stretchSquare, squareSide, H, dx]
      ring
    all_goals dsimp [dx]; ring
  have h₁ : (∫ t in (1/4 : ℝ)..1/2, F t) = (∫ u in z.im..w.im, g (V w.re u)) * I := by
    apply integral_affine_side (m := 4 * dy) (d := z.im - dy) (by norm_num) _ (hV _) _ _ g
    · intro t ht
      rw [hside 1 (by norm_num; exact ht)]
      apply Complex.ext <;> simp [stretchSquare, squareSide, V, dy]
      ring
    all_goals dsimp [dy]; ring
  have h₂ : (∫ t in (1/2 : ℝ)..3/4, F t) = (∫ u in w.re..z.re, g (H w.im u)) * 1 := by
    apply integral_affine_side (m := -(4 * dx)) (d := z.re + 3 * dx) (by norm_num) _ (hH _) _ _ g
    · intro t ht
      rw [hside 2 (by norm_num; exact ht)]
      apply Complex.ext <;> simp [stretchSquare, squareSide, H, dx]
      ring
    all_goals dsimp [dx]; ring
  have h₃ : (∫ t in (3/4 : ℝ)..1, F t) = (∫ u in w.im..z.im, g (V z.re u)) * I := by
    apply integral_affine_side (m := -(4 * dy)) (d := z.im + 4 * dy) (by norm_num) _ (hV _) _ _ g
    · intro t ht
      rw [hside 3 (by norm_num; exact ht)]
      apply Complex.ext <;> simp [stretchSquare, squareSide, V, dy]
      ring
    all_goals dsimp [dy]; ring
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : IntervalIntegrable F volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (((rectangleContour z w).integrableOn_mul_deriv hg).mono_set (Icc_subset_Icc ha hb))
  rw [((rectangleContour z w).scalarIntegral_eq_intervalIntegral hg).2]
  change (∫ t in (0 : ℝ)..1, F t) = _
  rw [← integral_add_adjacent_intervals (hi (by norm_num) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
        (hi (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals (hi (by norm_num) (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num))
        (hi (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals (hi (by norm_num) (by norm_num : (1/2 : ℝ) ≤ 3/4) (by norm_num))
        (hi (by norm_num) (by norm_num) (by norm_num)), h₀, h₁, h₂, h₃]
  simp only [rectangleIntegral, Complex.wedgeIntegral, H, V, smul_eq_mul]
  ring

theorem exists_rectangleContour_ordered {z w : ℂ} (hx : z.re < w.re) (hy : z.im < w.im) :
    ∃ γ : PositiveSimpleContour, γ.val.trace ⊆ Rectangle z w ∧
      γ.interior = Ioo z.re w.re ×ℂ Ioo z.im w.im ∧
      ∀ g : ℂ → ℂ, ContinuousOn g (Rectangle z w) →
        complexMeasureIntegral γ.val.measure g = rectangleIntegral g z w := by
  classical
  let p := rectangleContour z w
  let B := Ioo z.re w.re ×ℂ Ioo z.im w.im
  have ht : p.trace = Rectangle z w \ B := rectangleContour_trace hx hy
  have htR : p.trace ⊆ Rectangle z w := ht ▸ sdiff_subset
  have hindex (u : ℂ) (hu : u ∉ p.trace) :
      p.index u = if u ∈ Rectangle z w then 1 else 0 := by
    have hk : ContinuousOn (fun v ↦ (v - u)⁻¹) p.trace :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun v hv ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hv hu)
    rw [ComplexContour.index, rectangleContour_integral z w hk]
    split_ifs with h
    · have hin : u ∈ B := by by_contra hn; exact hu (ht ▸ ⟨h, hn⟩)
      rw [rectangleIntegral_sub_inv hin, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero])]
    · have hd : DifferentiableOn ℂ (fun v : ℂ ↦ (v - u)⁻¹) (Rectangle z w) :=
        (differentiableOn_id.sub_const u).inv fun v hv ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hv h)
      rw [rectangleIntegral, wedgeIntegral_add_wedgeIntegral_eq,
        integral_boundary_rect_eq_zero_of_differentiableOn _ z w hd, mul_zero]
  have hinj : InjOn p.toContinuousMap (Ico 0 1) :=
    (stretchSquare_injective hx hy).comp_injOn squarePath_injOn
  let γ : PositiveSimpleContour := ⟨p, hinj, fun u hu ↦ by
    rw [hindex u hu]; split <;> simp⟩
  refine ⟨γ, htR, ?_, fun g hg ↦ rectangleContour_integral z w (hg.mono htR)⟩
  have hBR : B ⊆ Rectangle z w := by
    intro u hu
    exact ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hu.1), Icc_subset_uIcc (Ioo_subset_Icc_self hu.2)⟩
  ext u
  change u ∉ p.trace ∧ p.index u = 1 ↔ u ∈ B
  constructor
  · rintro ⟨hnot, hone⟩
    have hmem : u ∈ Rectangle z w := by
      by_contra hu
      rw [hindex u hnot, ite_eq_right hu] at hone
      exact zero_ne_one hone
    by_contra h
    exact hnot (ht ▸ ⟨hmem, h⟩)
  · intro hu
    have hnot : u ∉ p.trace := fun h ↦ (show u ∈ Rectangle z w \ B from ht ▸ h).2 hu
    exact ⟨hnot, by rw [hindex u hnot, ite_eq_left (hBR hu)]⟩

end RectangleContour

/-- A nondegenerate rectangle admits a positively oriented simple boundary contour.
Its scalar integral agrees, up to orientation, with the sum of the two wedge
integrals around the rectangle. -/
theorem exists_positiveSimpleContour_rectangle (z w : ℂ) (hre : z.re ≠ w.re) (him : z.im ≠ w.im) :
    ∃ γ : PositiveSimpleContour, γ.val.trace ⊆ Complex.Rectangle z w ∧
      γ.interior ⊆ Complex.Rectangle z w ∧
      ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        ∀ g : ℂ → ℂ, ContinuousOn g (Complex.Rectangle z w) →
          complexMeasureIntegral γ.val.measure g =
            ε * (Complex.wedgeIntegral z w g + Complex.wedgeIntegral w z g) := by
  wlog hx : z.re < w.re generalizing z w
  · obtain ⟨γ, ht, hi, ε, hε, h⟩ := this w z hre.symm him.symm (lt_of_le_of_ne (le_of_not_gt hx) hre.symm)
    have hR : Complex.Rectangle w z = Complex.Rectangle z w := by
      simp only [Complex.Rectangle, uIcc_comm w.re z.re, uIcc_comm w.im z.im]
    rw [hR] at ht hi h
    exact ⟨γ, ht, hi, ε, hε, fun g hg ↦ (h g hg).trans (by rw [add_comm])⟩
  rcases lt_or_gt_of_ne him with hy | hy
  · obtain ⟨γ, ht, hi, h⟩ := exists_rectangleContour_ordered hx hy
    exact ⟨γ, ht, hi ▸ (fun _ hu ↦ ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hu.1), Icc_subset_uIcc (Ioo_subset_Icc_self hu.2)⟩), 1, Or.inl rfl, fun g hg ↦ by simpa [rectangleIntegral] using h g hg⟩
  · let a : ℂ := ⟨z.re, w.im⟩
    let b : ℂ := ⟨w.re, z.im⟩
    obtain ⟨γ, ht, hi, h⟩ := exists_rectangleContour_ordered (z := a) (w := b) hx hy
    have hR : Complex.Rectangle a b = Complex.Rectangle z w := by
      simp only [a, b, Complex.Rectangle, uIcc_comm w.im z.im]
    have hiR : γ.interior ⊆ Complex.Rectangle a b :=
      hi ▸ (fun _ hu ↦ ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hu.1), Icc_subset_uIcc (Ioo_subset_Icc_self hu.2)⟩)
    rw [hR] at ht hiR h
    refine ⟨γ, ht, hiR, -1, Or.inr rfl, fun g hg ↦ ?_⟩
    rw [h g hg, rectangleIntegral_eq, Complex.wedgeIntegral_add_wedgeIntegral_eq]
    simp only [a, b, intervalIntegral.integral_symm w.im z.im, smul_eq_mul]
    ring

/-- Every point of an open set is inside a positive simple contour whose trace
and interior are both contained in that open set. -/
theorem exists_positiveSimpleContour_mem_nhds {U : Set ℂ} (hU : IsOpen U) {x : ℂ}
    (hx : x ∈ U) : ∃ γ : PositiveSimpleContour, γ.val.trace ⊆ U ∧
      γ.interior ⊆ U ∧ γ.interior ∈ 𝓝 x := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp (hU.mem_nhds hx)
  let d := R / 3
  have hd : 0 < d := by positivity
  let a : ℂ := ⟨x.re - d, x.im - d⟩
  let b : ℂ := ⟨x.re + d, x.im + d⟩
  have hre : a.re < b.re := by change x.re - d < x.re + d; linarith
  have him : a.im < b.im := by change x.im - d < x.im + d; linarith
  have hrect : Complex.Rectangle a b ⊆ Metric.ball x R := by
    intro y hy
    obtain ⟨hyr, hyi⟩ := hy
    rw [uIcc_of_le hre.le] at hyr
    rw [uIcc_of_le him.le] at hyi
    change x.re - d ≤ y.re ∧ y.re ≤ x.re + d at hyr
    change x.im - d ≤ y.im ∧ y.im ≤ x.im + d at hyi
    have hr : |(y - x).re| ≤ d := by
      change |y.re - x.re| ≤ d
      exact abs_le.mpr ⟨by linarith [hyr.1], by linarith [hyr.2]⟩
    have hi : |(y - x).im| ≤ d := by
      change |y.im - x.im| ≤ d
      exact abs_le.mpr ⟨by linarith [hyi.1], by linarith [hyi.2]⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (by dsimp [d] at *; linarith)
  obtain ⟨γ, htr, hint, _⟩ := exists_rectangleContour_ordered hre him
  refine ⟨γ, htr.trans (hrect.trans hball), ?_, ?_⟩
  · rw [hint]
    intro y hy
    exact hball (hrect ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hy.1),
      Icc_subset_uIcc (Ioo_subset_Icc_self hy.2)⟩)
  · rw [hint]
    apply (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds
    exact ⟨⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩,
      ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩⟩

/-- Vanishing scalar integrals on simple contours imply complex differentiability
by the rectangular form of Morera's theorem. -/
theorem differentiableOn_of_scalarIntegral_eq_zero {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : ContinuousOn g U)
    (hzero : ∀ γ : PositiveSimpleContour, γ.val.trace ⊆ U → γ.interior ⊆ U →
      complexMeasureIntegral γ.val.measure g = 0) : DifferentiableOn ℂ g U := by
  refine (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).1 ⟨?_, hg⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg]
  by_cases hre : z.re = w.re
  · rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
    simp [hre]
  by_cases him : z.im = w.im
  · rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
    simp [him]
  obtain ⟨γ, htrace, hinterior, ε, hε, heq⟩ := exists_positiveSimpleContour_rectangle z w hre him
  have h := hzero γ (htrace.trans hrect) (hinterior.trans hrect)
  rw [heq g (hg.mono hrect)] at h
  have hε₀ : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  exact (mul_eq_zero.mp h).resolve_left hε₀
private lemma ComplexContour.compact_trace (γ : ComplexContour) : IsCompact γ.trace :=
  isCompact_Icc.image γ.toContinuousMap.continuous

lemma ComplexContour.ae_mem_trace (γ : ComplexContour) :
    ∀ᵐ w ∂γ.measure.variation, w ∈ γ.trace := by
  rw [ae_iff]
  exact γ.variation_compl_trace

private lemma ComplexContour.scalarIntegral_const_mul (γ : ComplexContour) (c : ℂ) (g : ℂ → ℂ) :
    complexMeasureIntegral γ.measure (fun w ↦ c * g w) =
      c * complexMeasureIntegral γ.measure g := by
  simp only [complexMeasureIntegral, VectorMeasure.integral_eq_setToFun]
  apply setToFun_smul _ _ c g
  intro a s z
  simp [VectorMeasure.transpose, mul_left_comm]

private lemma ComplexContour.scalarIntegral_sub (γ : ComplexContour) {g h : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) (hh : ContinuousOn h γ.trace) :
    complexMeasureIntegral γ.measure (fun w ↦ g w - h w) =
      complexMeasureIntegral γ.measure g -
        complexMeasureIntegral γ.measure h :=
  VectorMeasure.integral_fun_sub (γ.scalarIntegral_eq_intervalIntegral hg).1
    (γ.scalarIntegral_eq_intervalIntegral hh).1

/-- Bounded convergence for kernels continuous on the contour trace. -/
private lemma ComplexContour.tendsto_scalarIntegral (γ : ComplexContour) {l : Filter ℂ}
    [l.IsCountablyGenerated] {K : ℂ → ℂ → ℂ} {k : ℂ → ℂ}
    (hc : ∀ᶠ z in l, ContinuousOn (K z) γ.trace)
    (hb : ∃ C : ℝ, ∀ᶠ z in l, ∀ w ∈ γ.trace, ‖K z w‖ ≤ C)
    (ht : ∀ w ∈ γ.trace, Tendsto (fun z ↦ K z w) l (𝓝 (k w))) :
    Tendsto (fun z ↦ complexMeasureIntegral γ.measure (K z)) l
      (𝓝 (complexMeasureIntegral γ.measure k)) := by
  have : IsFiniteMeasure γ.measure.variation :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℂ) ≠ 0)).mp
      (γ.scalarIntegral_eq_intervalIntegral continuousOn_const).1
  apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
  · exact hc.mono fun z hz ↦ (γ.scalarIntegral_eq_intervalIntegral hz).1.aestronglyMeasurable
  · obtain ⟨C, hC⟩ := hb
    exact ⟨C, hC.mono fun z hz ↦ γ.ae_mem_trace.mono (hz ·)⟩
  · exact γ.ae_mem_trace.mono (ht ·)

/-- A locally uniformly bounded family of holomorphic kernels may be differentiated
under the contour integral. Cauchy's estimate bounds the difference quotients. -/
private lemma ComplexContour.differentiableOn_scalarIntegral (γ : ComplexContour) {U : Set ℂ}
    (hU : IsOpen U) {K : ℂ → ℂ → ℂ} (hc : ∀ z ∈ U, ContinuousOn (K z) γ.trace)
    (hd : ∀ w ∈ γ.trace, DifferentiableOn ℂ (fun z ↦ K z w) U)
    (hb : ∀ M : Set ℂ, IsCompact M → M ⊆ U → ∃ C : ℝ, ∀ z ∈ M, ∀ w ∈ γ.trace, ‖K z w‖ ≤ C) :
    DifferentiableOn ℂ (fun z ↦ complexMeasureIntegral γ.measure (K z)) U := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC⟩ := hb _ (isCompact_closedBall x r) hball
  have hr' := half_pos hr
  have hsmall : ball x (r / 2) ⊆ closedBall x r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))
  have hderiv (w : ℂ) (hw : w ∈ γ.trace) (y : ℂ) (hy : y ∈ ball x (r / 2)) :
      ‖deriv (fun z ↦ K z w) y‖ ≤ C / (r / 2) := by
    have hs : closedBall y (r / 2) ⊆ closedBall x r :=
      closedBall_subset_closedBall' (by have := mem_ball.mp hy; linarith)
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr'
      ((hd w hw).diffContOnCl_ball (hs.trans hball))
    exact fun z hz ↦ hC z (hs (sphere_subset_closedBall hz)) w hw
  let Q (y w : ℂ) := slope (fun z ↦ K z w) x y
  have hnear : ∀ᶠ y in 𝓝[≠] x, y ∈ ball x (r / 2) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr')
  have hQ : Tendsto (fun y ↦ complexMeasureIntegral γ.measure (Q y)) (𝓝[≠] x)
      (𝓝 (complexMeasureIntegral γ.measure (fun w ↦ deriv (fun z ↦ K z w) x))) := by
    apply γ.tendsto_scalarIntegral
    · filter_upwards [hnear] with y hy
      exact continuousOn_const.mul ((hc y (hball (hsmall hy))).sub (hc x hx))
    · refine ⟨C / (r / 2), ?_⟩
      filter_upwards [hnear, self_mem_nhdsWithin] with y hy hyx
      intro w hw
      have hs := (convex_ball x (r / 2)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz ↦ (hd w hw).differentiableAt (hU.mem_nhds (hball (hsmall hz))))
        (hderiv w hw) (mem_ball_self hr') hy
      change ‖slope (fun z ↦ K z w) x y‖ ≤ _
      rw [slope_def_field, norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hyx))).mpr hs
    · exact fun w hw ↦ ((hd w hw).differentiableAt (hU.mem_nhds hx)).hasDerivAt.tendsto_slope
  apply DifferentiableAt.differentiableWithinAt
  apply HasDerivAt.differentiableAt
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hQ.congr'
  filter_upwards [hnear] with y hy
  simp only [Q, slope, vsub_eq_sub, smul_eq_mul]
  rw [γ.scalarIntegral_const_mul, γ.scalarIntegral_sub (hc y (hball (hsmall hy))) (hc x hx)]

lemma ComplexContour.continuousOn_inv_sub (γ : ComplexContour) {z : ℂ} (hz : z ∉ γ.trace) :
    ContinuousOn (fun w ↦ (w - z)⁻¹) γ.trace :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun _ hw ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz)

lemma ComplexContour.differentiableOn_cauchyTransform (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) : DifferentiableOn ℂ
      (fun z ↦ complexMeasureIntegral γ.measure (fun w ↦ (w - z)⁻¹ * g w)) γ.traceᶜ := by
  apply γ.differentiableOn_scalarIntegral γ.compact_trace.isClosed.isOpen_compl
  · exact fun z hz ↦ (γ.continuousOn_inv_sub hz).mul hg
  · intro w hw
    exact ((differentiableOn_const w).sub differentiableOn_id |>.inv fun z hz ↦
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz)).mul (differentiableOn_const (g w))
  · intro M hM hs
    have hc : ContinuousOn (fun p : ℂ × ℂ ↦ (p.2 - p.1)⁻¹ * g p.2) (M ×ˢ γ.trace) :=
      (((continuousOn_snd (s := M ×ˢ γ.trace)).sub continuousOn_fst).inv₀ fun p hp ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hp.2 (hs hp.1))).mul
        (hg.comp continuousOn_snd mapsTo_snd_prod)
    obtain ⟨C, hC⟩ := (hM.prod γ.compact_trace).exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz w hw ↦ hC (z, w) ⟨hz, hw⟩⟩

private lemma ComplexContour.tendsto_cauchyTransform (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) : Tendsto
      (fun z ↦ complexMeasureIntegral γ.measure (fun w ↦ (w - z)⁻¹ * g w))
      (cocompact ℂ) (𝓝 0) := by
  have hzero : complexMeasureIntegral γ.measure (fun _ ↦ 0) = 0 :=
    VectorMeasure.integral_zero
  have : (cocompact ℂ).IsCountablyGenerated := by
    rw [← cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  rw [← hzero]
  apply γ.tendsto_scalarIntegral
  · filter_upwards [γ.compact_trace.compl_mem_cocompact] with z hz
    exact (γ.continuousOn_inv_sub hz).mul hg
  · obtain ⟨R, hR⟩ := γ.compact_trace.exists_bound_of_continuousOn (f := id) continuousOn_id
    obtain ⟨C, hC⟩ := γ.compact_trace.exists_bound_of_continuousOn hg
    refine ⟨C, ?_⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 1)] with z hz
    intro w hw
    have hzw := norm_sub_norm_le z w
    rw [norm_sub_rev] at hzw
    have h1 : 1 ≤ ‖w - z‖ := by have := hR w hw; change ‖w‖ ≤ R at this; linarith
    rw [norm_mul, norm_inv]
    exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ h1) (norm_nonneg (g w))).trans
      ((one_mul _).le.trans (hC w hw))
  · intro w _
    rw [← cobounded_eq_cocompact]
    simpa using ((tendsto_inv₀_cobounded.comp (tendsto_const_sub_cobounded w)).mul_const (g w))

private lemma ComplexContour.differentiableOn_dslopeIntegral (γ : ComplexContour) {U : Set ℂ}
    (hU : IsOpen U) (htr : γ.trace ⊆ U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun z ↦ complexMeasureIntegral γ.measure (dslope g z)) U := by
  have hd (z : ℂ) : DifferentiableOn ℂ (dslope g z) U := by
    by_cases hz : z ∈ U
    · exact (Complex.differentiableOn_dslope (hU.mem_nhds hz)).mpr hg
    · exact (differentiableOn_dslope_of_notMem hz).mpr hg
  apply γ.differentiableOn_scalarIntegral hU
  · exact fun z _ ↦ (hd z).continuousOn.mono htr
  · intro w _
    apply (hd w).congr
    intro z _
    rcases eq_or_ne w z with rfl | hne
    · rfl
    · rw [dslope_of_ne _ hne, dslope_of_ne _ hne.symm, slope_comm]
  · intro M hM hs
    obtain ⟨C, hC⟩ := norm_dslope_le_on hU hg (hM.union γ.compact_trace) (union_subset hs htr)
    exact ⟨C, fun z hz w hw ↦ hC z (.inl hz) w (.inr hw)⟩

private lemma PositiveSimpleContour.continuousAt_index (γ : PositiveSimpleContour) {x : ℂ}
    (hx : x ∉ γ.val.trace) : ContinuousAt γ.val.index x := by
  have hd := γ.val.differentiableOn_cauchyTransform (continuousOn_const (c := (1 : ℂ)))
  change ContinuousAt (fun y ↦ _ * complexMeasureIntegral γ.val.measure (fun w ↦ (w - y)⁻¹)) x
  simpa only [mul_one] using
    (hd.continuousOn.continuousAt (γ.val.compact_trace.isClosed.isOpen_compl.mem_nhds hx)).const_mul
      (2 * (Real.pi : ℂ) * I)⁻¹

/-- The index is locally constant off the trace, since it is continuous there and takes
only two values. -/
lemma PositiveSimpleContour.eventually_index_eq (γ : PositiveSimpleContour) {x : ℂ}
    (hx : x ∉ γ.val.trace) : ∀ᶠ y in 𝓝 x, γ.val.index y = γ.val.index x := by
  have htr := γ.val.compact_trace.isClosed.isOpen_compl.mem_nhds hx
  have hc := γ.continuousAt_index hx
  rcases γ.property.2 x hx with h | h
  · filter_upwards [htr, hc.eventually_ne (h ▸ zero_ne_one)] with y hy hn using
      ((γ.property.2 y hy).resolve_right hn).trans h.symm
  · filter_upwards [htr, hc.eventually_ne (h ▸ one_ne_zero)] with y hy hn using
      ((γ.property.2 y hy).resolve_left hn).trans h.symm

lemma PositiveSimpleContour.eventually_index_zero (γ : PositiveSimpleContour) :
    ∀ᶠ y in cocompact ℂ, γ.val.index y = 0 := by
  have ht : Tendsto γ.val.index (cocompact ℂ) (𝓝 0) := by
    change Tendsto (fun y ↦ _ * complexMeasureIntegral γ.val.measure (fun w ↦ (w - y)⁻¹)) _ _
    simpa only [mul_one, mul_zero] using
      (γ.val.tendsto_cauchyTransform (continuousOn_const (c := (1 : ℂ)))).const_mul
        (2 * (Real.pi : ℂ) * I)⁻¹
  filter_upwards [γ.val.compact_trace.compl_mem_cocompact, ht.eventually_ne zero_ne_one]
    with y hy hn using (γ.property.2 y hy).resolve_right hn

private lemma ComplexContour.scalarIntegral_dslope (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) {x : ℂ} (hx : x ∉ γ.trace) :
    complexMeasureIntegral γ.measure (dslope g x) =
      complexMeasureIntegral γ.measure (fun w ↦ (w - x)⁻¹ * g w) -
        g x * (2 * (Real.pi : ℂ) * I) * γ.index x := by
  have hk := γ.continuousOn_inv_sub hx
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [ComplexContour.index, mul_assoc, mul_inv_cancel_left₀ hc, ← γ.scalarIntegral_const_mul,
    ← γ.scalarIntegral_sub (g := fun w ↦ (w - x)⁻¹ * g w) (h := fun w ↦ g x * (w - x)⁻¹) (hk.mul hg) (continuousOn_const.mul hk)]
  apply VectorMeasure.integral_congr_ae
  filter_upwards [γ.ae_mem_trace] with w hw
  rw [dslope_of_ne g (ne_of_mem_of_not_mem hw hx)]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  ring

/-- Dixon's argument for a finite weighted family. Glue the integral of the divided
difference to the exterior Cauchy transform wherever the total index vanishes. -/
private lemma sum_scalarIntegral_dslope_eq_zero {ι : Type*} (s : Finset ι)
    (γ : ι → PositiveSimpleContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (htr : ∀ i ∈ s, (γ i).val.trace ⊆ U)
    (hind : ∀ x ∉ U, ∑ i ∈ s, c i * (γ i).val.index x = 0)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    ∑ i ∈ s, c i * complexMeasureIntegral (γ i).val.measure (dslope g z) = 0 := by
  classical
  let A (x : ℂ) := ∑ i ∈ s, c i * complexMeasureIntegral (γ i).val.measure
    (fun w ↦ (w - x)⁻¹ * g w)
  let B (x : ℂ) := ∑ i ∈ s, c i * complexMeasureIntegral (γ i).val.measure (dslope g x)
  let J (x : ℂ) := ∑ i ∈ s, c i * (γ i).val.index x
  have hc i (hi : i ∈ s) := hg.continuousOn.mono (htr i hi)
  have hBA (x) (hx : ∀ i ∈ s, x ∉ (γ i).val.trace) (hj : J x = 0) : B x = A x := by
    calc
      B x = A x - (g x * (2 * (Real.pi : ℂ) * I)) * J x := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(γ i).val.scalarIntegral_dslope (hc i hi) (hx i hi)]
        ring
      _ = A x := by rw [hj, mul_zero, sub_zero]
  let F x := if x ∈ U then B x else A x
  have hFA (x) (hx : ∀ i ∈ s, x ∉ (γ i).val.trace) (hj : J x = 0) : F x = A x := by
    simp [F, hBA x hx hj]
  have hd : Differentiable ℂ F := by
    intro x
    by_cases hx : x ∈ U
    · have hdB : DifferentiableOn ℂ B U := DifferentiableOn.fun_sum fun i hi ↦
        ((γ i).val.differentiableOn_dslopeIntegral hU (htr i hi) hg).const_mul _
      apply (hdB.differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy using ite_eq_left hy
    · have hxt (i) (hi : i ∈ s) : x ∉ (γ i).val.trace := fun h ↦ hx (htr i hi h)
      have hdA : DifferentiableAt ℂ A x := DifferentiableAt.fun_sum fun i hi ↦
        (((γ i).val.differentiableOn_cauchyTransform (hc i hi)).differentiableAt
          ((γ i).val.compact_trace.isClosed.isOpen_compl.mem_nhds (hxt i hi))).const_mul _
      apply hdA.congr_of_eventuallyEq
      have ht := (s.eventually_all).mpr fun i hi ↦
        (γ i).val.compact_trace.isClosed.isOpen_compl.mem_nhds (hxt i hi)
      have hj := (s.eventually_all).mpr fun i hi ↦ (γ i).eventually_index_eq (hxt i hi)
      filter_upwards [ht, hj] with y hy hyj
      exact hFA y hy ((Finset.sum_congr rfl fun i hi ↦ congrArg (c i * ·) (hyj i hi)).trans (hind x hx))
  have ht : Tendsto A (cocompact ℂ) (𝓝 0) := by
    simpa [A] using tendsto_finsetSum s fun i hi ↦
      ((γ i).val.tendsto_cauchyTransform (hc i hi)).const_mul (c i)
  have htF : Tendsto F (cocompact ℂ) (𝓝 0) := by
    apply ht.congr'
    have htr' := s.eventually_all.mpr fun i _ ↦ (γ i).val.compact_trace.compl_mem_cocompact
    have hind' := s.eventually_all.mpr fun i _ ↦ (γ i).eventually_index_zero
    filter_upwards [htr', hind'] with x hx hj
    exact (hFA x hx (Finset.sum_eq_zero fun i hi ↦ by rw [hj i hi, mul_zero])).symm
  simpa [F, hz, B] using hd.apply_eq_of_tendsto_cocompact z htF

/-- Cauchy–Goursat for a null-homologous weighted family, obtained by applying the
divided-difference formula to the function `w ↦ (w - z) * g w`. -/
theorem sum_scalarIntegral_eq_zero {ι : Type*} (s : Finset ι)
    (γ : ι → PositiveSimpleContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (htr : ∀ i ∈ s, (γ i).val.trace ⊆ U)
    (hind : ∀ x ∉ U, ∑ i ∈ s, c i * (γ i).val.index x = 0)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    ∑ i ∈ s, c i * complexMeasureIntegral (γ i).val.measure g = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  let z := (γ i).val.toContinuousMap 0
  have hz : z ∈ U := htr i hi ⟨0, by simp, rfl⟩
  let G (w : ℂ) := (w - z) * g w
  have he : dslope G z = g := by
    funext w
    rcases eq_or_ne w z with rfl | hne
    · have h := ((hasDerivAt_id' z).sub_const z).fun_mul (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
      simpa [dslope_same, G] using h.deriv
    · simp [dslope_of_ne _ hne, slope, G, sub_ne_zero.mpr hne, smul_eq_mul]
  rw [← he]
  exact sum_scalarIntegral_dslope_eq_zero s γ c hU htr hind ((differentiableOn_id.sub_const z).mul hg) hz

/-- Paper: Theorem C.5.2.4(1–2), p. 738. Scalar Cauchy–Goursat for a simple contour
of index zero outside the open set of holomorphy.
Deviation: The conclusion uses the parameter integral and the hypothesis uses the
index outside the domain. -/
theorem PositiveSimpleContour.integral_eq_zero_of_index_eq_zero (γ : PositiveSimpleContour)
    {U : Set ℂ} (hU : IsOpen U) (htrace : γ.val.trace ⊆ U)
    (hindex : ∀ z ∉ U, γ.val.index z = 0) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    (∫ t in Icc (0 : ℝ) 1, g (γ.val.toContinuousMap t) *
      deriv (fun s ↦ γ.val.toContinuousMap s) t) = 0 := by
  rw [← (γ.val.scalarIntegral_eq_integral (hg.continuousOn.mono htrace)).2]
  simpa using sum_scalarIntegral_eq_zero ({γ} : Finset PositiveSimpleContour) id (fun _ ↦ 1) hU
    (by simpa using htrace) (by simpa using hindex) hg

theorem PositiveSimpleContour.scalar_cauchy {U : Set ℂ} (hU : IsOpen U)
    (γ : PositiveSimpleContour) (htr : γ.val.trace ⊆ U) (hint : γ.interior ⊆ U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ γ.interior) :
    g z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      complexMeasureIntegral γ.val.measure (fun w ↦ (w - z)⁻¹ * g w) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * I
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero, I_ne_zero]
  have hzero := sum_scalarIntegral_dslope_eq_zero ({γ} : Finset PositiveSimpleContour) id (fun _ ↦ 1) hU
    (by simpa using htr) (by
      intro x hx
      have hxt : x ∉ γ.val.trace := fun h ↦ hx (htr h)
      simpa using (γ.property.2 x hxt).resolve_right (fun h ↦ hx (hint ⟨hxt, h⟩))) hg (hint hz)
  simp only [Finset.sum_singleton, id_eq, one_mul] at hzero
  rw [γ.val.scalarIntegral_dslope (hg.continuousOn.mono htr) hz.1, hz.2, mul_one] at hzero
  rw [sub_eq_zero.mp hzero, mul_comm (g z), inv_mul_cancel_left₀ hc]

/-- The scalar contour integral of a derivative vanishes when its primitive is
defined and differentiable near the trace. -/
private theorem ComplexContour.integral_eq_zero_of_hasDerivAt (γ : ComplexContour) {g g' : ℂ → ℂ}
    (hg : ∀ w ∈ γ.trace, HasDerivAt g (g' w) w) (hg' : ContinuousOn g' γ.trace) :
    (∫ t in Icc (0 : ℝ) 1, g' (γ.toContinuousMap t) *
      deriv (fun s ↦ γ.toContinuousMap s) t) = 0 := by
  obtain ⟨n, t, ht, hstart, hend, hdiff⟩ := γ.piecewiseContDiff
  let p : ℝ → ℂ := γ.toContinuousMap
  let v (s : ℝ) := g' (p s) * deriv p s
  let a (k : ℕ) : ℝ := t ⟨min k n, by omega⟩
  have ha₀ : a 0 = 0 := by simpa [a] using hstart
  have han : a n = 1 := by simpa [a, Fin.last] using hend
  have hpiece (k : ℕ) (hk : k < n) :
      IntervalIntegrable v volume (a k) (a (k + 1)) ∧
        (∫ s in a k..a (k + 1), v s) = g (p (a (k + 1))) - g (p (a k)) := by
    let i : Fin n := ⟨k, hk⟩
    have h₀ : a k = t i.castSucc := by simp [a, i, min_eq_left hk.le]
    have h₁ : a (k + 1) = t i.succ := by simp [a, i, min_eq_left (by omega : k + 1 ≤ n)]
    have hle := (ht i.castSucc_lt_succ).le
    have hsub : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 1 := by
      rw [← hstart, ← hend]
      exact Icc_subset_Icc (ht.monotone (Fin.zero_le _)) (ht.monotone (Fin.le_last _))
    have hmaps : MapsTo p (Icc (t i.castSucc) (t i.succ)) γ.trace :=
      fun _ hs ↦ mem_image_of_mem p (hsub hs)
    rw [h₀, h₁]
    have hint : IntervalIntegrable v volume (t i.castSucc) (t i.succ) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
        ((γ.integrableOn_mul_deriv hg').mono_set hsub)
    refine ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := g ∘ p) hle ?_ ?_ hint⟩
    · have hc : ContinuousOn g γ.trace := fun w hw ↦ (hg w hw).continuousAt.continuousWithinAt
      exact hc.comp γ.toContinuousMap.continuous.continuousOn hmaps
    · intro s hs
      have hp := ((hdiff i).differentiableOn (by simp) s (Ioo_subset_Icc_self hs)).differentiableAt
        (Icc_mem_nhds hs.1 hs.2)
      simpa only [v, smul_eq_mul, mul_comm] using
        (hg (p s) (hmaps (Ioo_subset_Icc_self hs))).scomp s hp.hasDerivAt
  change (∫ s in Icc (0 : ℝ) 1, v s) = 0
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← ha₀, ← han, ← intervalIntegral.sum_integral_adjacent_intervals (fun k hk ↦ (hpiece k hk).1)]
  calc
    _ = ∑ k ∈ Finset.range n, (g (p (a (k + 1))) - g (p (a k))) :=
      Finset.sum_congr rfl fun k hk ↦ (hpiece k (Finset.mem_range.mp hk)).2
    _ = 0 := by
      rw [Finset.sum_range_sub (fun k ↦ g (p (a k))), ha₀, han]
      exact sub_eq_zero.mpr (congrArg g γ.closed)

/-- The scalar Cauchy kernel times a holomorphic function is integrable on the trace.
Its integral is given by Cauchy–Goursat and integration by parts. -/
theorem PositiveSimpleContour.scalarIntegral_cauchy_derivative (γ : PositiveSimpleContour)
    {U : Set ℂ} (hU : IsOpen U) (htrace : γ.val.trace ⊆ U) (hinterior : γ.interior ⊆ U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ γ.interior) (k : ℕ) :
    Integrable (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * g w)
      γ.val.measure.variation ∧
    complexMeasureIntegral γ.val.measure (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * g w) =
      (2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) * iteratedDeriv k g z := by
  let K (n : ℕ) (w : ℂ) := ((w - z) ^ (n + 1))⁻¹
  let J (q : ℂ → ℂ) := ∫ t in Icc (0 : ℝ) 1,
    q (γ.val.toContinuousMap t) * deriv (fun s ↦ γ.val.toContinuousMap s) t
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hz' : z ∉ γ.val.trace := hz.1
  have hne (w : ℂ) (hw : w ∈ γ.val.trace) : w - z ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz')
  have hK (n : ℕ) : ContinuousOn (K n) γ.val.trace :=
    ((continuousOn_id.sub continuousOn_const).pow _).inv₀ fun w hw ↦ pow_ne_zero _ (hne w hw)
  have hJ_add {q r : ℂ → ℂ} (hq : ContinuousOn q γ.val.trace)
      (hr : ContinuousOn r γ.val.trace) : J (fun w ↦ q w + r w) = J q + J r := by
    simp only [J, add_mul]
    exact integral_add (γ.val.integrableOn_mul_deriv hq) (γ.val.integrableOn_mul_deriv hr)
  have hJ_sub {q r : ℂ → ℂ} (hq : ContinuousOn q γ.val.trace)
      (hr : ContinuousOn r γ.val.trace) : J (fun w ↦ q w - r w) = J q - J r := by
    simp only [J, sub_mul]
    exact integral_sub (γ.val.integrableOn_mul_deriv hq) (γ.val.integrableOn_mul_deriv hr)
  have hJ_mul (b : ℂ) (q : ℂ → ℂ) : J (fun w ↦ b * q w) = b * J q := by
    simp only [J, mul_assoc, MeasureTheory.integral_const_mul]
  have hindex : ∀ w ∉ U, γ.val.index w = 0 := by
    intro w hw
    have hwt : w ∉ γ.val.trace := fun h ↦ hw (htrace h)
    exact (γ.property.2 w hwt).resolve_right fun h ↦ hw (hinterior ⟨hwt, h⟩)
  have hJ_zero : J (K 0) = c := by
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hi := hz.2
    change c⁻¹ * complexMeasureIntegral γ.val.measure (fun w ↦ (w - z)⁻¹) = 1 at hi
    have hK₀ : K 0 = fun w ↦ (w - z)⁻¹ := by ext w; simp [K]
    rw [← hK₀, (γ.val.scalarIntegral_eq_integral (hK 0)).2] at hi
    exact (inv_mul_eq_iff_eq_mul₀ hc).mp (show c⁻¹ * J (K 0) = 1 from hi) |>.trans (mul_one c)
  have hformula (n : ℕ) (q : ℂ → ℂ) (hq : DifferentiableOn ℂ q U) :
      J (fun w ↦ K n w * q w) = (c / (n.factorial : ℂ)) * iteratedDeriv n q z := by
    induction n generalizing q with
    | zero =>
      have hds := (Complex.differentiableOn_dslope (hU.mem_nhds (hinterior hz))).2 hq
      have heq : J (fun w ↦ K 0 w * q w) =
          J (fun w ↦ dslope q z w + q z * K 0 w) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have hwt : γ.val.toContinuousMap t ∈ γ.val.trace := mem_image_of_mem _ ht
        have hw := ne_of_mem_of_not_mem hwt hz'
        simp only [K, zero_add, pow_one, dslope_of_ne q hw, slope_def_field, div_eq_mul_inv]
        ring
      have hconst : ContinuousOn (fun w ↦ q z * K 0 w) γ.val.trace :=
        continuousOn_const.mul (hK 0)
      rw [heq, hJ_add (hds.continuousOn.mono htrace) hconst, hJ_mul, hJ_zero]
      rw [show J (dslope q z) = 0 from γ.integral_eq_zero_of_index_eq_zero hU htrace hindex hds]
      simp [mul_comm]
    | succ n ih =>
      have hq' := hq.deriv hU
      have hleft : ContinuousOn (fun w ↦ K n w * deriv q w) γ.val.trace :=
        (hK n).mul (hq'.continuousOn.mono htrace)
      have hright : ContinuousOn (fun w ↦ (n + 1 : ℂ) * (K (n + 1) w * q w)) γ.val.trace :=
        continuousOn_const.mul ((hK (n + 1)).mul (hq.continuousOn.mono htrace))
      have hpart : J (fun w ↦ K n w * deriv q w) =
          (n + 1 : ℂ) * J (fun w ↦ K (n + 1) w * q w) := by
        apply sub_eq_zero.mp
        rw [← hJ_mul (n + 1 : ℂ) (fun w ↦ K (n + 1) w * q w), ← hJ_sub hleft hright]
        apply γ.val.integral_eq_zero_of_hasDerivAt (g := fun w ↦ K n w * q w)
          _ (hleft.sub hright)
        intro w hw
        have hker : HasDerivAt (K n) (-(n + 1 : ℂ) * K (n + 1) w) w := by
          have h := (hasDerivAt_zpow (-((n + 1 : ℕ) : ℤ)) (w - z)
            (.inl (hne w hw))).comp_sub_const w z
          have hexp : -((n + 1 : ℕ) : ℤ) - 1 = -((n + 1 + 1 : ℕ) : ℤ) := by omega
          rw [hexp] at h
          simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at h
          simpa only [K, Nat.cast_add, Nat.cast_one] using h
        change HasDerivAt (fun u ↦ K n u * q u)
          (K n w * deriv q w - (n + 1 : ℂ) * (K (n + 1) w * q w)) w
        have hqAt : HasDerivAt q (deriv q w) w :=
          (hq.differentiableAt (hU.mem_nhds (htrace hw))).hasDerivAt
        have he :
            (-(n + 1 : ℂ) * K (n + 1) w) * q w + K n w * deriv q w =
              K n w * deriv q w - (n + 1 : ℂ) * (K (n + 1) w * q w) := by ring
        exact he ▸ hker.fun_mul hqAt
      rw [ih (deriv q) hq', ← iteratedDeriv_succ'] at hpart
      have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply (mul_left_cancel₀ hn)
      rw [← hpart, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hn, hfact]
  obtain ⟨hi, heq⟩ := γ.val.scalarIntegral_eq_integral (g := fun w ↦ K k w * g w)
    ((hK k).mul (hg.continuousOn.mono htrace))
  exact ⟨hi, heq.trans (hformula k g hg)⟩

end Masullo
