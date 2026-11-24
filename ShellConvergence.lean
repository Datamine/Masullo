import AdelicBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Function MeasureTheory NumberField Set Topology
open scoped ENNReal NumberField

namespace Masullo

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- Lemma 11.1.1.1: the pointwise limit of Schwartz–Bruhat restrictions
to the ideles is Borel measurable. -/
theorem adeleShell_pointwise_measurable [MeasurableSpace (Idele F)] [BorelSpace (Idele F)]
    (f : ℕ → Adeles F → ℂ) (hf : ∀ k, f k ∈ bruhatSubmodule F)
    (l : Idele F → ℂ)
    (hl : ∀ g : Idele F, Tendsto (fun k => f k g.val) atTop (𝓝 (l g))) :
    Measurable l :=
  measurable_of_tendsto_metrizable
    (fun k => ((bruhat_continuous F (hf k)).comp Units.continuous_val).measurable)
    (tendsto_pi_nhds.mpr hl)

/-- The orbit sum on a Borel region, extended by zero outside it. The
limit is only required at every translate of a point of that region. -/
theorem adeleShell_dominated_pointwise [MeasurableSpace (Idele F)] [BorelSpace (Idele F)]
    (f : ℕ → Adeles F → ℂ) (hf : ∀ k, f k ∈ bruhatSubmodule F)
    (l : Idele F → ℂ) (S : Set (Idele F)) (hS : MeasurableSet S)
    (b : Idele F → Fˣ → ℝ)
    (hSum : ∀ g ∈ S, Summable (b g))
    (hlimit : ∀ g ∈ S, ∀ ξ : Fˣ, Tendsto (fun k => thetaSummand F (f k) g ξ) atTop (𝓝 (l (principalIdele F ξ * g))))
    (hbound : ∀ k, ∀ g ∈ S, ∀ ξ, ‖thetaSummand F (f k) g ξ‖ ≤ b g ξ) :
    let L (g : Idele F) := S.indicator (fun x => ∑' ξ : Fˣ, l (principalIdele F ξ * x)) g
    (∀ g ∈ S, Summable fun ξ : Fˣ => ‖l (principalIdele F ξ * g)‖) ∧
    (∀ g, Tendsto (fun k => S.indicator (thetaOnIdeles F (f k)) g) atTop (𝓝 (L g))) ∧
    Measurable L ∧
    (∀ g ∈ S, ‖L g‖ ≤ ∑' ξ, b g ξ) ∧
    (∀ k, ∀ g ∈ S, ‖thetaOnIdeles F (f k) g‖ ≤ ∑' ξ, b g ξ) := by
  let L (g : Idele F) := S.indicator (fun x => ∑' ξ : Fˣ, l (principalIdele F ξ * x)) g
  have hble (g : Idele F) (hg : g ∈ S) (ξ : Fˣ) : ‖l (principalIdele F ξ * g)‖ ≤ b g ξ :=
    le_of_tendsto (tendsto_norm.comp (hlimit g hg ξ))
      (Eventually.of_forall fun k => hbound k g hg ξ)
  have hls (g : Idele F) (hg : g ∈ S) :
      Summable fun ξ : Fˣ => ‖l (principalIdele F ξ * g)‖ :=
    (hSum g hg).of_norm_bounded fun ξ => by simpa only [norm_norm] using hble g hg ξ
  have hfl (k : ℕ) (g : Idele F) (hg : g ∈ S) :
      Summable fun ξ : Fˣ => ‖thetaSummand F (f k) g ξ‖ :=
    (hSum g hg).of_norm_bounded fun ξ => by simpa only [norm_norm] using hbound k g hg ξ
  have htl (g : Idele F) : Tendsto (fun k => S.indicator (thetaOnIdeles F (f k)) g) atTop (𝓝 (L g)) := by
    by_cases hg : g ∈ S
    · simp only [L, indicator_of_mem hg, thetaOnIdeles]
      exact tendsto_tsum_of_dominated_convergence (hSum g hg) (hlimit g hg)
        (Eventually.of_forall fun k ξ => hbound k g hg ξ)
    · simp only [L, indicator_of_notMem hg]
      exact tendsto_const_nhds
  refine ⟨hls, htl, ?_, ?_, ?_⟩
  · apply measurable_of_tendsto_metrizable _ (tendsto_pi_nhds.mpr htl)
    intro k
    exact ((bruhat_theta_continuous_and_invariant (hf k)).1.measurable).indicator hS
  · intro g hg
    change ‖L g‖ ≤ _
    rw [show L g = ∑' ξ : Fˣ, l (principalIdele F ξ * g) by simp [L, hg]]
    exact (norm_tsum_le_tsum_norm (hls g hg)).trans ((hls g hg).tsum_le_tsum (hble g hg) (hSum g hg))
  · intro k g hg
    unfold thetaOnIdeles
    exact (norm_tsum_le_tsum_norm (hfl k g hg)).trans ((hfl k g hg).tsum_le_tsum (hbound k g hg) (hSum g hg))

/-- Proposition 11.1.1.2 with a common summable orbit majorant and
pointwise convergence at all needed translates. The functions are extended
by zero off the region. The last limit is convergence in the (L^r) norm. -/
theorem adeleShell_dominated_Lp [MeasurableSpace (Idele F)] [BorelSpace (Idele F)]
    (f : ℕ → Adeles F → ℂ) (hf : ∀ k, f k ∈ bruhatSubmodule F)
    (l : Idele F → ℂ) (S : Set (Idele F)) (hS : MeasurableSet S)
    (ν : Measure (Idele F)) (r : ℝ≥0∞) (hr : 1 ≤ r) (hrtop : r ≠ ⊤)
    (b : Idele F → Fˣ → ℝ)
    (hSum : ∀ g ∈ S, Summable (b g))
    (hB : MemLp (fun g => ∑' ξ, b g ξ) r (ν.restrict S))
    (hlimit : ∀ g ∈ S, ∀ ξ : Fˣ, Tendsto (fun k => thetaSummand F (f k) g ξ) atTop (𝓝 (l (principalIdele F ξ * g))))
    (hbound : ∀ k, ∀ g ∈ S, ∀ ξ, ‖thetaSummand F (f k) g ξ‖ ≤ b g ξ) :
    let L (g : Idele F) := S.indicator (fun x => ∑' ξ : Fˣ, l (principalIdele F ξ * x)) g
    (∀ g ∈ S, Summable fun ξ : Fˣ => ‖l (principalIdele F ξ * g)‖) ∧
    Measurable L ∧ MemLp L r (ν.restrict S) ∧ (∀ k, MemLp (thetaOnIdeles F (f k)) r (ν.restrict S)) ∧
    Tendsto (fun k => eLpNorm (thetaOnIdeles F (f k) - L) r (ν.restrict S)) atTop (𝓝 0) := by
  obtain ⟨hls, htl, hlm, hlb, hfb⟩ := adeleShell_dominated_pointwise f hf l S hS b hSum hlimit hbound
  let L (g : Idele F) := S.indicator (fun x => ∑' ξ : Fˣ, l (principalIdele F ξ * x)) g
  let H (g : Idele F) := ∑' ξ, b g ξ
  let μ := ν.restrict S
  have hfM (k : ℕ) : Measurable (thetaOnIdeles F (f k)) :=
    (bruhat_theta_continuous_and_invariant (hf k)).1.measurable
  have haS : ∀ᵐ g ∂μ, g ∈ S := ae_restrict_mem hS
  have hLm : MemLp L r μ := hB.of_le hlm.aestronglyMeasurable
    (haS.mono fun g hg => (hlb g hg).trans (le_abs_self _))
  have hFm (k : ℕ) : MemLp (thetaOnIdeles F (f k)) r μ :=
    hB.of_le (hfM k).aestronglyMeasurable
      (haS.mono fun g hg => (hfb k g hg).trans (le_abs_self _))
  refine ⟨hls, hlm, hLm, hFm, ?_⟩
  let W (k : ℕ) (g : Idele F) := thetaOnIdeles F (f k) g - L g
  have hWm (k : ℕ) : Measurable (W k) := (hfM k).sub hlm
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos hr0 hrtop
  have hT : ∀ᵐ g ∂μ, Tendsto (fun k => W k g) atTop (𝓝 0) := haS.mono fun g hg => by
    have hi : Tendsto (fun k => thetaOnIdeles F (f k) g) atTop (𝓝 (L g)) := by
      have ht : Tendsto (fun k => S.indicator (thetaOnIdeles F (f k)) g) atTop (𝓝 (L g)) := htl g
      simpa only [indicator_of_mem hg] using ht
    simpa only [W, sub_self] using hi.sub (tendsto_const_nhds (x := L g))
  have hD : Tendsto (fun k => ∫⁻ g, ‖W k g‖ₑ ^ r.toReal ∂μ) atTop (𝓝 0) := by
    have hB2 : MemLp (H + H) r μ := hB.add hB
    have hd := tendsto_lintegral_of_dominated_convergence'
      (μ := μ) (f := fun _ => 0) (F := fun k g => ‖W k g‖ₑ ^ r.toReal)
      (bound := fun g => ‖(H + H) g‖ₑ ^ r.toReal)
      (fun k => ((hWm k).enorm.pow_const _).aemeasurable)
      (fun k => haS.mono fun g hg => by
        apply ENNReal.rpow_le_rpow ?_ hrpos.le
        rw [← ofReal_norm, ← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        exact (norm_sub_le _ _).trans (((add_le_add (hfb k g hg) (hlb g hg))).trans (le_abs_self _)))
      ((lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hr0 hrtop hB2.2).ne)
      (hT.mono fun x ht => by
        have hw : Tendsto (fun n => ‖W n x‖ₑ ^ r.toReal) atTop (𝓝 (‖(0 : ℂ)‖ₑ ^ r.toReal)) :=
          ((ENNReal.continuous_rpow_const (y := r.toReal)).tendsto (‖(0 : ℂ)‖ₑ)).comp ht.enorm
        simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hrpos] using hw)
    simpa only [lintegral_zero] using hd
  change Tendsto (fun k => eLpNorm (W k) r μ) atTop (𝓝 0)
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop]
  have hp : 0 < 1 / r.toReal := one_div_pos.mpr hrpos
  have hPow : Tendsto (fun k => (∫⁻ g, ‖W k g‖ₑ ^ r.toReal ∂μ) ^ (1 / r.toReal))
      atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / r.toReal))) :=
    ((ENNReal.continuous_rpow_const (y := 1 / r.toReal)).tendsto (0 : ℝ≥0∞)).comp hD
  simpa only [ENNReal.zero_rpow_of_pos hp] using hPow

/-- Orbit reindexing for a function already restricted to the ideles. -/
theorem shellLimit_principal_mul (l : Idele F → ℂ) (g : Idele F) (a : Fˣ) :
    (∑' ξ : Fˣ, l (principalIdele F ξ * (principalIdele F a * g))) =
      ∑' ξ : Fˣ, l (principalIdele F ξ * g) := by
  simpa only [Equiv.coe_mulRight, map_mul, mul_assoc] using
    (Equiv.mulRight a).tsum_eq (fun ξ => l (principalIdele F ξ * g))

/-- The limiting orbit sum as a function on the actual idele class group. -/
def shellLimitClass (l : Idele F → ℂ) : IdeleClass F → ℂ :=
  Quotient.lift (fun g => ∑' ξ : Fˣ, l (principalIdele F ξ * g)) fun x y h => by
    change (QuotientGroup.leftRel (principalIdeles F)).r x y at h
    rw [QuotientGroup.leftRel_apply] at h
    obtain ⟨a, ha⟩ := h
    have hy : y = principalIdele F a * x := by rw [ha, mul_comm (x⁻¹ * y), mul_inv_cancel_left]
    rw [hy, shellLimit_principal_mul]

/-- Corollary 11.1.1.4 with a common summable majorant on each representative's
orbit. Any representative set covering the class group suffices. -/
theorem adeleShell_class_pointwise (f : ℕ → Adeles F → ℂ) (l : Idele F → ℂ)
    (hl : ∀ g : Idele F, Tendsto (fun k => f k g.val) atTop (𝓝 (l g)))
    (S : Set (Idele F)) (hS : SurjOn (ideleClassMap F) S univ)
    (hbound : ∀ g ∈ S, ∃ b : Fˣ → ℝ, Summable b ∧
      ∀ k ξ, ‖thetaSummand F (f k) g ξ‖ ≤ b ξ) :
    (∀ g : Idele F, Summable (fun ξ : Fˣ => ‖l (principalIdele F ξ * g)‖)) ∧
    (∀ c : IdeleClass F, Tendsto (fun k => adelicTheta F (f k) c) atTop (𝓝 (shellLimitClass l c))) := by
  have hAt (g : Idele F) (hg : g ∈ S) :
      Summable (fun ξ : Fˣ => ‖l (principalIdele F ξ * g)‖) ∧
      Tendsto (fun k => thetaOnIdeles F (f k) g) atTop
        (𝓝 (∑' ξ : Fˣ, l (principalIdele F ξ * g))) := by
    obtain ⟨b, hbs, hb⟩ := hbound g hg
    have hL (ξ : Fˣ) := hl (principalIdele F ξ * g)
    refine ⟨hbs.of_norm_bounded (fun ξ => ?_), ?_⟩
    · rw [norm_norm]
      exact le_of_tendsto (tendsto_norm.comp (hL ξ)) (Eventually.of_forall fun k => hb k ξ)
    · exact tendsto_tsum_of_dominated_convergence hbs hL (Eventually.of_forall hb)
  constructor
  · intro g
    obtain ⟨r, hr, hrg⟩ := hS (mem_univ (ideleClassMap F g))
    have hrg' : (r : IdeleClass F) = (g : IdeleClass F) := hrg
    have hrel : (QuotientGroup.leftRel (principalIdeles F)).r r g := Quotient.exact hrg'
    rw [QuotientGroup.leftRel_apply] at hrel
    obtain ⟨a, ha⟩ := hrel
    have hg : g = principalIdele F a * r := by
      rw [ha, mul_comm (r⁻¹ * g), mul_inv_cancel_left]
    rw [hg]
    have he := ((Equiv.mulRight a).summable_iff).2 (hAt r hr).1
    simpa only [Function.comp_def, Equiv.coe_mulRight, map_mul, mul_assoc] using he
  · intro c
    obtain ⟨g, hg, rfl⟩ := hS (mem_univ c)
    exact (hAt g hg).2

end

end Masullo
